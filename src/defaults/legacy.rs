//! Test-only oracle: the closure-based `Defaults` DSL as it was at `70fdb56b`, with its own copy
//! of the settings table and of the value parsers, against which the data-based modifiers of
//! `super` are compared.
//!
//! The macros `initializer_of`, `modifier_of`, `has_standard_negator` and `ifdef` are verbatim
//! copies of `src/defaults/settings_dsl.rs` at `70fdb56b`, except that `modifier_of` names
//! `legacy::SettingKind`. `defaults` keeps the original matcher and generates `negate` and `set`
//! verbatim; instead of `enums`, `Settings` and its accessors (which are shared with `super`) it
//! generates `NAMES` and `default_settings`, the struct literal of the original `Default` impl.
//! The table, `octal_mode` and `fractional_minutes` are verbatim copies of
//! `src/defaults/mod.rs` at `70fdb56b`.

use super::{ListMode, SYSTEM_EDITOR, Settings};

pub type SettingsModifier = Box<dyn FnOnce(&mut Settings)>;

#[repr(u32)]
pub enum SettingKind {
    Flag(SettingsModifier) = crate::common::HARDENED_ENUM_VALUE_0,
    Integer(fn(&str) -> Option<SettingsModifier>) = crate::common::HARDENED_ENUM_VALUE_1,
    Text(fn(&str) -> Option<SettingsModifier>) = crate::common::HARDENED_ENUM_VALUE_2,
    List(fn(ListMode, Vec<String>) -> SettingsModifier) = crate::common::HARDENED_ENUM_VALUE_3,
}

macro_rules! initializer_of {
    ($id:ident, true) => { true };
    ($id:ident, false) => { false };
    ($id:ident, [ $($value: expr),* ]) => { [$($value),*].into_iter().map(|s: &str| s.to_string()).collect::<std::collections::HashSet<_>>() };
    ($id:ident, $(=int $check: expr;)+ $value: expr) => { $value };
    ($id:ident, $(=enum $k: ident;)+ $value: ident) => { $crate::defaults::enums::$id::$value };
    ($id:ident, None) => { None };
    ($id:ident, $value: expr) => { $value.into() };
    ($id:ident, $($_: tt)*) => { return None };
}

macro_rules! modifier_of {
    ($id:ident, true) => {
        $crate::defaults::legacy::SettingKind::Flag(Box::new(move |obj: &mut Settings| obj.$id = true))
    };
    ($id:ident, false) => {
        $crate::defaults::legacy::SettingKind::Flag(Box::new(move |obj: &mut Settings| obj.$id = true))
    };
    ($id:ident, [ $($value: expr),* ]) => {
        $crate::defaults::legacy::SettingKind::List(|mode, list| {
            Box::new(move |obj: &mut Settings| match mode {
                ListMode::Set => obj.$id = list.into_iter().collect(),
                ListMode::Add => obj.$id.extend(list),
                ListMode::Del => {
                    for key in list {
                        obj.$id.remove(&key);
                    }
                }
            })
        })
    };
    ($id:ident, =int $first:literal ..= $last: literal $(@ $radix: literal)?; $value: expr) => {
        #[allow(clippy::from_str_radix_10)]
        $crate::defaults::legacy::SettingKind::Integer(|text| {
            u64::from_str_radix(text, 10$(*0 + $radix)?)
                .ok()
                .filter(|val| ($first ..= $last).contains(val))
                .map(|i| {
                    Box::new(move |obj: &mut Settings| obj.$id = i) as SettingsModifier
                })
        })
    };
    ($id:ident, =int $fn: expr; $value: expr) => {
        $crate::defaults::legacy::SettingKind::Integer(|text| {
            $fn(&text).map(|i| {
                Box::new(move |obj: &mut Settings| obj.$id = i) as SettingsModifier
            })
        })
    };
    ($id:ident, $(=int $check: expr;)+ $value: expr) => { compile_error!("bla") };
    ($id:ident, $(=enum $key: ident;)+ $value: ident) => {
        $crate::defaults::legacy::SettingKind::Text(|key| match key {
            $(
            stringify!($key) => {
                Some(Box::new(move |obj: &mut Settings| obj.$id = $crate::defaults::enums::$id::$key))
            },
            )*
            _ => None,
        })
    };
    ($id:ident, None) => {
        $crate::defaults::legacy::SettingKind::Text(|text| {
            let text = text.into();
            Some(Box::new(move |obj: &mut Settings| obj.$id = Some(text)))
        })
    };
    ($id:ident, $value: expr) => {
        $crate::defaults::legacy::SettingKind::Text(|text| {
            let text = text.into();
            Some(Box::new(move |obj: &mut Settings| obj.$id = text))
        })
    };
}

macro_rules! has_standard_negator {
    (true) => {
        true
    };
    (false) => {
        true
    };
    ([$($_: expr),*]) => {
        true
    };
    ($($_: tt)*) => {
        false
    };
}

// this macro allows us to help the compiler generate more efficient code in 'fn negate'
// and enables the way 'fn set' is made
macro_rules! ifdef {
    (; $then: expr; $else: expr) => {
        $else
    };
    ($($_: expr)+; $then: expr; $else: expr) => {
        $then
    };
}

macro_rules! defaults {
    ($($name:ident = $value:tt $((!= $negate:tt))? $([$($key:ident),*])? $([$first:literal ..= $last:literal$(; radix: $radix: expr)?])? $({$fn: expr})? $(#$attribute:ident)?)*) => {
        pub(crate) const NAMES: &[&str] = &[$(stringify!($name)),*];

        pub(crate) fn default_settings() -> Settings {
            Settings {
                $($name: initializer_of!($name, $(=int $fn;)?$(=int $first;)?$($(=enum $key;)*)? $value)),*
            }
        }

        pub(crate) fn negate(name: &str) -> Option<SettingsModifier> {
            match name {
                $(
                stringify!($name) if ifdef!($($negate)?; true; has_standard_negator!($value)) => {
                    let value = ifdef!($($negate)?;
                        // this setting has an explicit negation; use that
                        initializer_of!($name, $(=int $fn;)?$(=int $first;)?$($(=enum $key;)*)? $($negate)?);
                        // for bool and sets, false/empty works (for other types this is dead code)
                        Default::default()
                    );
                    Some(Box::new(move |obj: &mut Settings| obj.$name = value))
                },
                )*
                _ => None
            }
        }

        pub(crate) fn set(name: &str) -> Option<SettingKind> {
            match name {
            $(
                stringify!($name) => Some(modifier_of!($name, $(=int $fn;)?$(=int $first ..= $last $(@ $radix)?;)?$($(=enum $key;)*)? $value)),
            )*
                _ => None,
            }
        }
    };
}

defaults! {
    always_query_group_plugin = false  #ignored
    always_set_home           = false  #ignored
    env_reset                 = true   #ignored
    fqdn                      = false  #ignored
    ignore_dot                = true   #ignored
    lecture                   = never (!= never) [always, once, never] #ignored
    mailerpath                = None (!= None) #ignored
    mail_badpass              = true   #ignored
    match_group_by_gid        = false  #ignored
    use_pty                   = true
    visiblepw                 = false  #ignored
    pwfeedback                = true
    rootpw                    = false
    targetpw                  = false
    noexec                    = false
    noninteractive_auth       = false

    log_allowed               = true
    log_denied                = true #ignored

    insults                   = false  #ignored

    setenv                    = false
    runcwd                    = None (!= None)
    apparmor_profile          = None (!= None)
    umask                     = 0o022 (!= 0o777) {octal_mode}
    umask_override            = false

    passwd_tries              = 3 [0..=1000]

    secure_path               = None (!= None)

    verifypw                  = all (!= never) [all, always, any, never] #ignored

    passwd_timeout            = (5*60) (!= 0) {fractional_minutes}
    timestamp_timeout         = (15*60) (!= 0) {fractional_minutes}
    timestamp_type            = tty [tty, ppid]

    editor                    = SYSTEM_EDITOR
    env_editor                = true

    env_keep                  = ["COLORS", "DISPLAY", "HOSTNAME", "KRB5CCNAME", "LS_COLORS", "PATH",
                                 "PS1", "PS2", "XAUTHORITY", "XAUTHORIZATION", "XDG_CURRENT_DESKTOP"]

    env_check                 = ["COLORTERM", "LANG", "LANGUAGE", "LC_*", "LINGUAS", "TERM", "TZ"]

    env_delete                = ["IFS", "CDPATH", "LOCALDOMAIN", "RES_OPTIONS", "HOSTALIASES",
                                "NLSPATH", "PATH_LOCALE", "LD_*", "_RLD*", "TERMINFO", "TERMINFO_DIRS",
                                "TERMPATH", "TERMCAP", "ENV", "BASH_ENV", "PS4", "GLOBIGNORE",
                                "BASHOPTS", "SHELLOPTS", "JAVA_TOOL_OPTIONS", "PERLIO_DEBUG",
                                "PERLLIB", "PERL5LIB", "PERL5OPT", "PERL5DB", "FPATH", "NULLCMD",
                                "READNULLCMD", "ZDOTDIR", "TMPPREFIX", "PYTHONHOME", "PYTHONPATH",
                                "PYTHONINSPECT", "PYTHONUSERBASE", "RUBYLIB", "RUBYOPT", "*=()*"] #ignored
}

fn octal_mode(input: &str) -> Option<u64> {
    <libc::mode_t>::from_str_radix(input.strip_prefix('0')?, 8)
        .ok()
        .map(Into::into)
}

/// A custom parser to parse seconds as fractional "minutes", the format used by
/// passwd_timeout and timestamp_timeout.
fn fractional_minutes(input: &str) -> Option<u64> {
    if let Some((integral, fractional)) = input.split_once('.') {
        // - 'input' is maximally 18 characters, making fractional.len() at most 17;
        //   1e17 < 2**63, so the definition of 'shift' will not overflow.
        // - for the same reason, if both parses in the definition of 'seconds' succeed,
        //   we will have constructed an integer < 1e17.
        //-  1e17 * 60 = 6e18 < 9e18 < 2**63, so the final line also will not overflow
        let shift = 10u64.pow(fractional.len().try_into().ok()?);
        let seconds = integral.parse::<u64>().ok()? * shift + fractional.parse::<u64>().ok()?;

        Some(seconds * 60 / shift)
    } else {
        input.parse::<u64>().ok()?.checked_mul(60)
    }
}

/// Base settings on which old and new modifiers are compared: the defaults; every setting moved
/// away from its default by legacy modifiers; every negatable setting negated.
pub(crate) fn bases() -> Vec<Settings> {
    let defaults = default_settings();

    let mut moved = default_settings();
    for &name in NAMES {
        let modifier = match set(name).unwrap() {
            SettingKind::Flag(modifier) => {
                if field(&defaults, name) == "true" {
                    negate(name).unwrap()
                } else {
                    modifier
                }
            }
            SettingKind::Integer(check) => ["0", "1", "7", "0077", "2.5"]
                .into_iter()
                .filter_map(check)
                .next()
                .unwrap(),
            SettingKind::Text(check) => {
                let default = field(&defaults, name);
                ["/opt/moved", "always", "once", "any", "ppid"]
                    .into_iter()
                    .filter(|value| !default.contains(value))
                    .find_map(check)
                    .unwrap()
            }
            SettingKind::List(build) => build(
                ListMode::Set,
                vec!["MOVED".to_string(), "PATH".to_string(), "LC_*".to_string()],
            ),
        };
        modifier(&mut moved);
    }
    for &name in NAMES {
        assert_ne!(
            field(&moved, name),
            field(&defaults, name),
            "{name} was not moved"
        );
    }

    let mut negated = default_settings();
    for &name in NAMES {
        if let Some(modifier) = negate(name) {
            modifier(&mut negated);
        }
    }

    vec![defaults, moved, negated]
}

fn field(settings: &Settings, name: &str) -> String {
    let fields = settings.dump_fields();
    let (_, value) = fields.iter().find(|(field, _)| *field == name).unwrap();
    value.clone()
}

/// The legacy modifier and the new one (made afresh for every base) have the same effect on
/// every base; `None` only together.
pub(crate) fn assert_same_effect(
    what: &str,
    old: impl Fn() -> Option<SettingsModifier>,
    new: impl Fn() -> Option<super::SettingsModifier>,
) {
    match (old(), new()) {
        (None, None) => return,
        (Some(_), Some(_)) => {}
        (old, new) => panic!(
            "{what}: legacy gives {}, new gives {new:?}",
            if old.is_some() { "a modifier" } else { "none" }
        ),
    }
    for (i, base) in bases().into_iter().enumerate() {
        let mut by_old = base.clone();
        old().unwrap()(&mut by_old);
        let mut by_new = base;
        new().unwrap().apply(&mut by_new);
        assert_eq!(
            by_old.dump_fields(),
            by_new.dump_fields(),
            "{what} on base {i}"
        );
        assert_eq!(by_old, by_new, "{what} on base {i}");
    }
}

#[cfg(test)]
mod test {
    use super::super::{
        IntegerSetting, ListSetting, SettingKind as NewKind, TextSetting, build_list,
        check_integer, check_text,
    };
    use super::*;

    fn new_names() -> Vec<&'static str> {
        super::super::Settings::default()
            .dump_fields()
            .into_iter()
            .map(|(name, _)| name)
            .collect()
    }

    fn integer_setting(name: &str) -> IntegerSetting {
        let Some(NewKind::Integer(setting)) = super::super::set(name) else {
            panic!("{name} is not an integer setting")
        };
        setting
    }

    fn text_setting(name: &str) -> TextSetting {
        let Some(NewKind::Text(setting)) = super::super::set(name) else {
            panic!("{name} is not a text setting")
        };
        setting
    }

    fn list_setting(name: &str) -> ListSetting {
        let Some(NewKind::List(setting)) = super::super::set(name) else {
            panic!("{name} is not a list setting")
        };
        setting
    }

    // integers in and out of range, signs, radix prefixes, octal digits, fractions, overflow
    // of u64, of mode_t and of the multiplication by 60, the empty string, and whitespace
    const INTEGER_INPUTS: &[&str] = &[
        "",
        "0",
        "00",
        "000",
        "1",
        "3",
        "7",
        "8",
        "10",
        "999",
        "1000",
        "1001",
        "4294967295",
        "4294967296",
        "18446744073709551615",
        "18446744073709551616",
        "99999999999999999999",
        "-1",
        "-0",
        "+5",
        "+0",
        "0x10",
        "0o22",
        "0b1",
        "1e3",
        "abc",
        "A",
        " 1",
        "1 ",
        "022",
        "0022",
        "0077",
        "0777",
        "0778",
        "0779",
        "08",
        "018",
        "07777",
        "077777",
        "0177777",
        "037777777777",
        "040000000000",
        "0+7",
        "0-7",
        "0 7",
        "1.5",
        "25.25",
        ".5",
        "5.",
        "1.",
        ".",
        "..",
        "1.2.3",
        "0.0",
        "0.5",
        "1.05",
        "+1.5",
        "1.+5",
        "-1.5",
        "1.-5",
        "0.0000000000000001",
        "9999999999.9999999",
        "99999999999999999",
        "307445734561825860",
        "307445734561825861",
        "1.00000000000000000",
        "a.5",
        "1.a",
    ];

    // every enum key, keys in another case or with blanks, non-keys, paths, and the empty string
    const TEXT_INPUTS: &[&str] = &[
        "",
        "always",
        "once",
        "never",
        "all",
        "any",
        "tty",
        "ppid",
        "sometimes",
        "kernel",
        "Always",
        "NEVER",
        " never",
        "never ",
        "None",
        "none",
        "/bin",
        "/usr/bin:/bin",
        "*",
        "a b",
        "\"x\"",
        "\u{e9}",
    ];

    const LIST_INPUTS: &[&[&str]] = &[
        &[],
        &["PATH"],
        &["MOVED"],
        &["COLORS", "FOO", "BAR=baz"],
        &["PATH", "PATH"],
        &["LC_*", "XYZZY", "IFS"],
    ];

    #[test]
    fn same_names_and_defaults() {
        assert_eq!(NAMES, new_names().as_slice());
        assert_eq!(default_settings(), super::super::Settings::default());
    }

    #[test]
    fn same_kinds() {
        for name in NAMES
            .iter()
            .copied()
            .chain(["", "notanoption", "Use_pty", "use_pty "])
        {
            let same = matches!(
                (set(name), super::super::set(name)),
                (None, None)
                    | (Some(SettingKind::Flag(_)), Some(NewKind::Flag(_)))
                    | (Some(SettingKind::Integer(_)), Some(NewKind::Integer(_)))
                    | (Some(SettingKind::Text(_)), Some(NewKind::Text(_)))
                    | (Some(SettingKind::List(_)), Some(NewKind::List(_)))
            );
            assert!(same, "kind of {name:?}");
        }
    }

    #[test]
    fn same_negation() {
        for name in NAMES.iter().copied().chain(["", "notanoption", "!use_pty"]) {
            assert_same_effect(
                &format!("!{name}"),
                || negate(name),
                || super::super::negate(name),
            );
        }
    }

    #[test]
    fn same_flags() {
        for &name in NAMES {
            if let Some(SettingKind::Flag(_)) = set(name) {
                assert_same_effect(
                    name,
                    || match set(name) {
                        Some(SettingKind::Flag(modifier)) => Some(modifier),
                        _ => None,
                    },
                    || match super::super::set(name) {
                        Some(NewKind::Flag(modifier)) => Some(modifier),
                        _ => None,
                    },
                );
            }
        }
    }

    #[test]
    fn same_integers() {
        let mut count = 0;
        for &name in NAMES {
            let Some(SettingKind::Integer(old)) = set(name) else {
                continue;
            };
            let new = integer_setting(name);
            for &input in INTEGER_INPUTS {
                assert_same_effect(
                    &format!("{name}={input}"),
                    || old(input),
                    || check_integer(new, input),
                );
            }
            count += 1;
        }
        assert_eq!(count, 4);
    }

    #[test]
    fn same_texts() {
        let mut count = 0;
        for &name in NAMES {
            let Some(SettingKind::Text(old)) = set(name) else {
                continue;
            };
            let new = text_setting(name);
            for &input in TEXT_INPUTS {
                assert_same_effect(
                    &format!("{name}={input}"),
                    || old(input),
                    || check_text(new, input),
                );
            }
            count += 1;
        }
        assert_eq!(count, 8);
    }

    #[test]
    fn same_lists() {
        let mut count = 0;
        for &name in NAMES {
            let Some(SettingKind::List(old)) = set(name) else {
                continue;
            };
            let new = list_setting(name);
            for mode in [ListMode::Set, ListMode::Add, ListMode::Del] {
                for &list in LIST_INPUTS {
                    let items = || list.iter().map(|s| s.to_string()).collect::<Vec<_>>();
                    assert_same_effect(
                        &format!("{name} {mode:?} {list:?}"),
                        || Some(old(mode, items())),
                        || Some(build_list(new, mode, items())),
                    );
                }
            }
            count += 1;
        }
        assert_eq!(count, 3);
    }

    // a sequence of modifiers applied in order: every list operation after every other one,
    // and each after a negation
    #[test]
    fn same_sequences() {
        let modes = [ListMode::Set, ListMode::Add, ListMode::Del];
        for &name in NAMES {
            let Some(SettingKind::List(old)) = set(name) else {
                continue;
            };
            let new = list_setting(name);
            for first in modes {
                for second in modes {
                    for (a, b) in [(&["A", "B"][..], &["B", "C"][..]), (&["PATH"], &["PATH"])] {
                        let a = || a.iter().map(|s| s.to_string()).collect::<Vec<_>>();
                        let b = || b.iter().map(|s| s.to_string()).collect::<Vec<_>>();
                        for base in bases() {
                            let mut by_old = base.clone();
                            negate(name).unwrap()(&mut by_old);
                            old(first, a())(&mut by_old);
                            old(second, b())(&mut by_old);
                            let mut by_new = base;
                            super::super::negate(name).unwrap().apply(&mut by_new);
                            build_list(new, first, a()).apply(&mut by_new);
                            build_list(new, second, b()).apply(&mut by_new);
                            assert_eq!(by_old, by_new, "{name} {first:?} {second:?}");
                        }
                    }
                }
            }
        }
    }

    // no setting of the table has a radix; the generic range check against the expression the
    // legacy DSL generated, for the radixes a table entry could name
    #[test]
    fn same_range_check() {
        for radix in [2, 8, 10, 16, 36] {
            for &input in INTEGER_INPUTS {
                for (first, last) in [(0, 1000), (1, 7), (0, u64::MAX), (5, 5)] {
                    let old = u64::from_str_radix(input, radix)
                        .ok()
                        .filter(|val| (first..=last).contains(val));
                    assert_eq!(
                        old,
                        super::super::integer_in_range(input, radix, first, last),
                        "{input} radix {radix} in {first}..={last}"
                    );
                }
            }
        }
    }
}
