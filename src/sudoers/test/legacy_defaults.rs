//! The `Defaults` lines of the unit tests, and misuses that reach every diagnostic of the
//! settings parser, through the parser: the closure-based modifiers of `70fdb56b`
//! (`crate::defaults::legacy`, parsed by the copy of the old `impl Parse` below) against the
//! data-based ones. Same diagnostics (span and message) or the same effect on every base.

use super::super::ast::*;
use super::super::basic_parser::*;
use super::super::tokens::*;
use crate::defaults::{self, legacy};

struct LegacyModifier(legacy::SettingsModifier);

impl Parse for LegacyModifier {
    fn parse(stream: &mut CharStream) -> Parsed<Self> {
        legacy_parse(stream).map(LegacyModifier)
    }
}

impl Many for LegacyModifier {}

// the body of `impl Parse for defaults::SettingsModifier` at 70fdb56b, with `defaults::`
// replaced by `legacy::` for the modifier types and the functions `negate` and `set`
fn legacy_parse(stream: &mut CharStream) -> Parsed<legacy::SettingsModifier> {
    let id_pos = stream.get_pos();

    // Parse multiple entries enclosed in quotes (for list-like Defaults-settings)
    let parse_vars = |stream: &mut CharStream| -> Parsed<Vec<String>> {
        if stream.eat_char('"') {
            let mut result = Vec::new();
            while let Some(EnvVar(name)) = try_nonterminal(stream)? {
                if is_syntax('=', stream)? {
                    let StringParameter(value) = expect_nonterminal(stream)?;
                    result.push(name + "=" + &value);
                } else {
                    result.push(name);
                }
                if result.len() > Identifier::LIMIT {
                    unrecoverable!(stream, "environment variable list too long")
                }
            }
            expect_syntax('"', stream)?;
            if result.is_empty() {
                unrecoverable!(stream, "empty string not allowed");
            }

            make(result)
        } else {
            let EnvVar(name) = expect_nonterminal(stream)?;
            if is_syntax('=', stream)? {
                unrecoverable!(stream, "double quotes are required for VAR=value pairs")
            } else {
                make(vec![name])
            }
        }
    };

    // Parse the remainder of a list variable
    let list_items =
        |mode: defaults::ListMode, name: String, cfg: legacy::SettingKind, stream: &mut _| {
            expect_syntax('=', stream)?;
            let legacy::SettingKind::List(checker) = cfg else {
                unrecoverable!(pos = id_pos, stream, "{name} is not a list parameter");
            };

            make(checker(mode, parse_vars(stream)?))
        };

    // Parse a text parameter
    let text_item = |stream: &mut CharStream| {
        if stream.eat_char('"') {
            let QuotedStringParameter(text) = expect_nonterminal(stream)?;
            expect_syntax('"', stream)?;
            make(text)
        } else {
            let StringParameter(name) = expect_nonterminal(stream)?;
            make(name)
        }
    };

    if is_syntax('!', stream)? {
        let value_pos = stream.get_pos();
        let DefaultName(name) = expect_nonterminal(stream)?;
        let Some(modifier) = legacy::negate(&name) else {
            if legacy::set(&name).is_some() {
                unrecoverable!(
                    pos = value_pos,
                    stream,
                    "'{name}' cannot be used in a boolean context"
                );
            } else {
                unrecoverable!(pos = value_pos, stream, "unknown setting: '{name}'");
            }
        };

        make(modifier)
    } else {
        let DefaultName(name) = try_nonterminal(stream)?;
        let Some(cfg) = legacy::set(&name) else {
            unrecoverable!(pos = id_pos, stream, "unknown setting: '{name}'");
        };

        if is_syntax('+', stream)? {
            list_items(defaults::ListMode::Add, name, cfg, stream)
        } else if is_syntax('-', stream)? {
            list_items(defaults::ListMode::Del, name, cfg, stream)
        } else if is_syntax('=', stream)? {
            let value_pos = stream.get_pos();
            match cfg {
                legacy::SettingKind::Flag(_) => {
                    unrecoverable!(stream, "can't assign to boolean setting '{name}'")
                }
                legacy::SettingKind::Integer(checker) => {
                    let Numeric(denotation) = expect_nonterminal(stream)?;
                    if let Some(modifier) = checker(&denotation) {
                        make(modifier)
                    } else {
                        unrecoverable!(
                            pos = value_pos,
                            stream,
                            "'{denotation}' is not a valid value for {name}"
                        );
                    }
                }
                legacy::SettingKind::List(checker) => {
                    let items = parse_vars(stream)?;

                    make(checker(defaults::ListMode::Set, items))
                }
                legacy::SettingKind::Text(checker) => {
                    let text = text_item(stream)?;
                    let Some(modifier) = checker(&text) else {
                        unrecoverable!(
                            pos = value_pos,
                            stream,
                            "'{text}' is not a valid value for {name}"
                        );
                    };
                    make(modifier)
                }
            }
        } else {
            let legacy::SettingKind::Flag(modifier) = cfg else {
                unrecoverable!(pos = id_pos, stream, "'{name}' is not a boolean setting");
            };

            make(modifier)
        }
    }
}

/// `Defaults` lines of the unit tests (`test/mod.rs`) that parse, split into the directive with
/// its scope and the settings.
const TEST_LINES: &[(&str, &str)] = &[
    ("Defaults ", "env_editor"),
    ("Defaults ", "!use_pty"),
    ("Defaults ", "use_pty"),
    ("Defaults ", "!env_keep"),
    ("Defaults ", "!secure_path"),
    ("Defaults ", "!env_editor"),
    ("Defaults ", "env_keep = \"FOO HUK BAR\""),
    ("Defaults ", "env_keep -= HUK"),
    ("Defaults ", "!env_check"),
    ("Defaults ", "env_check += \"FOO\""),
    ("Defaults ", "env_check += \"XYZZY\""),
    ("Defaults ", "passwd_tries = 5"),
    ("Defaults ", "secure_path = /etc"),
    ("Defaults ", "verifypw = never"),
    ("Defaults ", "runcwd = *"),
    ("Defaults ", "runcwd = /usr/local"),
    ("Defaults ", "!runcwd"),
    (
        "Defaults ",
        "!env_editor, use_pty, env_keep = \"FOO BAR\", env_keep -= BAR, secure_path=/etc",
    ),
    ("Defaults:#1999999999 ", "use_pty"),
    ("Defaults!/bin/bash ", "!use_pty"),
    ("Defaults@host ", "!use_pty"),
    ("Defaults@host", "!use_pty"),
    ("Defaults@host,!host2 ", "!use_pty"),
    ("Defaults@!host,host2", "!use_pty"),
    ("Defaults:user ", "!use_pty"),
    ("Defaults:user", "!use_pty"),
    ("Defaults>user ", "!use_pty"),
    ("Defaults>user", "!use_pty"),
    ("Defaults@ hostname ", "use_pty"),
    ("Defaults@\\\nhost ", "use_pty"),
    ("Defaults:\\\nuser ", "use_pty"),
    ("Defaults>\\\nuser ", "use_pty"),
    ("Defaults!\\\nCMD ", "use_pty"),
    ("Defaults@host ", "env_keep=ALL"),
    ("Defaults!RR ", "use_pty"),
    ("Defaults@host ", "!env_editor"),
    ("Defaults:user ", "use_pty"),
    ("Defaults>runas ", "secure_path=\"/bin\""),
    ("Defaults!/bin/foo ", "!env_keep"),
    ("Defaults:%:DEFBAD ", "passwd_tries=5"),
    ("Defaults:alice ", "passwd_tries=4"),
    ("Defaults!list ", "passwd_tries=7"),
];

/// Settings texts beyond the unit tests: one per diagnostic of the settings parser, the value
/// checkers at their edges, and sequences on one line.
const MORE_SETTINGS: &[&str] = &[
    "verifypw = \"sometimes\"",
    "verifypw = sometimes",
    "!passwd_tries",
    "!editor",
    "!timestamp_type",
    "!nosuch",
    "nosuch",
    "nosuch=1",
    "use_pty=1",
    "use_pty+=X",
    "secure_path-=X",
    "passwd_tries+=1",
    "passwd_tries",
    "secure_path",
    "env_keep",
    "lecture",
    "passwd_tries=0",
    "passwd_tries=1000",
    "passwd_tries=1001",
    "passwd_tries=abc",
    "passwd_tries=1.5",
    "passwd_tries=\"5\"",
    "umask=0777",
    "umask=777",
    "umask=0778",
    "umask=018",
    "umask=0",
    "umask=00",
    "umask=037777777777",
    "umask=040000000000",
    "timestamp_timeout=2.5",
    "timestamp_timeout=.",
    "timestamp_timeout=.5",
    "timestamp_timeout=5.",
    "timestamp_timeout=1.2.3",
    "timestamp_timeout=307445734561825860",
    "timestamp_timeout=307445734561825861",
    "timestamp_timeout=9999999999.9999999",
    "passwd_timeout=0",
    "passwd_timeout=0.0000000000000001",
    "lecture=\"always\"",
    "lecture=once",
    "lecture=Once",
    "timestamp_type=ppid",
    "timestamp_type=kernel",
    "editor=/usr/bin/vim",
    "editor=\"/a b\"",
    "apparmor_profile=foo",
    "mailerpath=/usr/sbin/sendmail",
    "env_keep=\"A=b C\"",
    "env_keep=A=b",
    "env_keep=\"\"",
    "env_keep=\"A",
    "env_delete+=FOO",
    "env_check-=\"TZ TERM\"",
    "env_keep-=\"PATH DISPLAY\"",
    "env_keep=\"A B\", env_keep+=C, env_keep-=A, !env_check, env_check+=D",
    "use_pty, !use_pty, use_pty",
    "secure_path=/a, secure_path=/b, !secure_path",
    "!lecture, lecture=always",
    "umask=0077, !umask",
    "passwd_timeout=1.5, !passwd_timeout",
    "!verifypw, verifypw=any",
    "use_pty, nosuch, !use_pty",
    "use_pty !use_pty",
];

fn apply_old(modifiers: Vec<LegacyModifier>, settings: &mut defaults::Settings) {
    for LegacyModifier(modifier) in modifiers {
        modifier(settings);
    }
}

fn apply_new(modifiers: Vec<defaults::SettingsModifier>, settings: &mut defaults::Settings) {
    for modifier in modifiers {
        modifier.apply(settings);
    }
}

/// Parse `text` as a list of settings with the old and the new parser; compare diagnostics or,
/// when both accept, the effect on every base.
fn compare_settings(text: &str) {
    let old = || parse_string::<Vec<LegacyModifier>>(text);
    let new = || parse_string::<Vec<defaults::SettingsModifier>>(text);
    match (old(), new()) {
        (Err(old), Err(new)) => assert_eq!(old, new, "{text:?}"),
        (Ok(_), Ok(_)) => {
            for (i, base) in legacy::bases().into_iter().enumerate() {
                let mut by_old = base.clone();
                apply_old(old().unwrap(), &mut by_old);
                let mut by_new = base;
                apply_new(new().unwrap(), &mut by_new);
                assert_eq!(by_old, by_new, "{text:?} on base {i}");
            }
        }
        (old, new) => panic!(
            "{text:?}: legacy {}, new {:?}",
            if old.is_ok() { "accepts" } else { "rejects" },
            new.err()
        ),
    }
}

#[test]
fn defaults_lines_old_against_new() {
    for (_, settings) in TEST_LINES {
        compare_settings(settings);
    }
    for settings in MORE_SETTINGS {
        compare_settings(settings);
    }

    let many_vars = format!("env_keep=\"{}\"", vec!["V"; 200].join(" "));
    compare_settings(&many_vars);
    let many_settings = vec!["use_pty"; 200].join(",");
    compare_settings(&many_settings);
}

// the full lines through `Sudo`: the modifiers of the `Defaults` directive have the effect of
// the legacy parse of its settings
#[test]
fn defaults_directives_old_against_new() {
    for (directive, settings) in TEST_LINES {
        let line = format!("{directive}{settings}");
        let Ok(Sudo::Decl(Directive::Defaults(_, _))) = parse_string::<Sudo>(&line) else {
            panic!("{line:?} is not a Defaults directive");
        };
        for (i, base) in legacy::bases().into_iter().enumerate() {
            let Ok(Sudo::Decl(Directive::Defaults(modifiers, _))) = parse_string::<Sudo>(&line)
            else {
                unreachable!()
            };
            let mut by_new = base.clone();
            apply_new(modifiers, &mut by_new);
            let mut by_old = base;
            apply_old(
                parse_string::<Vec<LegacyModifier>>(settings).unwrap(),
                &mut by_old,
            );
            assert_eq!(by_old, by_new, "{line:?} on base {i}");
        }
    }
}
