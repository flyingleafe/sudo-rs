//! Canonical text dump of the legacy parser `parse_lines::<Sudo>`.
//!
//! The format, the escaping rule, the two settings bases, the character-class table and the
//! corpus conventions are specified in `proofs/parser/DUMP.md`; keep the two in step. The dump is
//! a contract with the Lean reference parser (which prints the same format) and with the
//! restyled parser (which must produce the same dump as the legacy one).

use std::fmt::Write as _;
use std::io::Write as _;
use std::path::Path;

use super::super::ast::*;
use super::super::basic_parser::{Span, Status, parse_lines};
use super::super::char_stream::CharStream;
use super::super::tokens::*;
use crate::defaults::{self, ListMode, SettingKind, Settings, SettingsModifier};

/// Root of the file-system fixture used by the `fixture` corpus category.
pub(super) const FIXTURE_ROOT: &str = "/tmp/sudo-rs-parser-dump-fixture";

/// Command-path prefix of the generated corpus; it must not exist on the host.
pub(super) const ABSENT_PREFIX: &str = "/sudoers-nx";

/// Quoted string: `"` + escaped characters + `"`. Printable ASCII (U+0020 to U+007E) other than
/// `"` and `\` is written as is; `"` and `\` are written as `\"` and `\\`; every other code point
/// as `\u{h}` with `h` its lowercase hexadecimal value without leading zeros.
pub(super) fn quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            ' '..='~' => out.push(c),
            _ => {
                let _ = write!(out, "\\u{{{:x}}}", c as u32);
            }
        }
    }
    out.push('"');
    out
}

/// Inverse of [quote] on its image: decodes one quoted string at the start of `s` and returns it
/// with the remaining input.
pub(super) fn unquote(s: &str) -> Option<(String, &str)> {
    let mut chars = s.strip_prefix('"')?.char_indices();
    let mut out = String::new();
    let body = &s[1..];
    while let Some((i, c)) = chars.next() {
        match c {
            '"' => return Some((out, &body[i + 1..])),
            '\\' => match chars.next()?.1 {
                '"' => out.push('"'),
                '\\' => out.push('\\'),
                'u' => {
                    if chars.next()?.1 != '{' {
                        return None;
                    }
                    let mut value = 0u32;
                    loop {
                        let d = chars.next()?.1;
                        if d == '}' {
                            break;
                        }
                        value = value.checked_mul(16)?.checked_add(d.to_digit(16)?)?;
                    }
                    out.push(char::from_u32(value)?);
                }
                _ => return None,
            },
            ' '..='~' => out.push(c),
            _ => return None,
        }
    }
    None
}

fn span(s: &Span) -> String {
    format!("{}:{}-{}:{}", s.start.0, s.start.1, s.end.0, s.end.1)
}

fn list<T>(items: &[T], f: impl Fn(&T) -> String) -> String {
    let items: Vec<String> = items.iter().map(f).collect();
    format!("[{}]", items.join(" "))
}

fn spec<T>(s: &Spec<T>, f: impl Fn(&T) -> String) -> String {
    let (tag, meta) = match s {
        Qualified::Allow(m) => ("allow", m),
        Qualified::Forbid(m) => ("forbid", m),
    };
    let meta = match meta {
        Meta::All => "all".to_string(),
        Meta::Alias(name) => format!("(alias {})", quote(name)),
        Meta::Only(x) => format!("(only {})", f(x)),
    };
    format!("({tag} {meta})")
}

fn spec_list<T>(l: &SpecList<T>, f: impl Fn(&T) -> String + Copy) -> String {
    list(l, |s| spec(s, f))
}

fn ident(i: &Identifier) -> String {
    match i {
        Identifier::Name(name) => format!("(name {})", quote(name)),
        Identifier::ID(id) => format!("(id {id})"),
    }
}

fn user(u: &UserSpecifier) -> String {
    match u {
        UserSpecifier::User(i) => format!("(user {})", ident(i)),
        UserSpecifier::Group(i) => format!("(group {})", ident(i)),
        UserSpecifier::NonunixGroup(i) => format!("(nonunix {})", ident(i)),
    }
}

fn host(h: &Hostname) -> String {
    quote(&h.0)
}

fn simple_command(c: &SimpleCommand) -> String {
    quote(c.as_str())
}

fn command(c: &Command) -> String {
    let (pat, args) = c;
    let (kind, args) = match args {
        Args::Prefix(a) => ("prefix", a),
        Args::Exact(a) => ("exact", a),
    };
    let args = list(args, |a| quote(&a.to_string_lossy()));
    format!("(cmd {} ({kind} {args}))", simple_command(pat))
}

fn chdir(c: &ChDir) -> String {
    match c {
        ChDir::Any => "any".to_string(),
        ChDir::Path(p) => format!("(path {})", quote(&p.to_string_lossy())),
    }
}

fn modifier(m: &Modifier) -> String {
    match m {
        Modifier::Passwd => "passwd".to_string(),
        Modifier::Nopasswd => "nopasswd".to_string(),
        Modifier::Setenv => "setenv".to_string(),
        Modifier::Nosetenv => "nosetenv".to_string(),
        Modifier::Exec => "exec".to_string(),
        Modifier::Noexec => "noexec".to_string(),
        Modifier::Cwd(c) => format!("(cwd {})", chdir(c)),
        Modifier::AppArmorProfile(p) => format!("(apparmor {})", quote(p)),
        Modifier::Ignored(s) => format!("(ignored {})", span(s)),
        Modifier::NoOp => "noop".to_string(),
    }
}

fn runas(r: &Option<RunAs>) -> String {
    match r {
        None => "none".to_string(),
        Some(RunAs { users, groups }) => {
            format!("(runas {} {})", spec_list(users, user), spec_list(groups, ident))
        }
    }
}

fn entry((r, CommandSpec(mods, cmd)): &(Option<RunAs>, CommandSpec)) -> String {
    format!(
        "(entry {} {} {})",
        runas(r),
        list(mods, modifier),
        spec(cmd, command)
    )
}

fn perm((hosts, entries): &(SpecList<Hostname>, Vec<(Option<RunAs>, CommandSpec)>)) -> String {
    format!("(perm {} {})", spec_list(hosts, host), list(entries, entry))
}

fn defs<T>(d: &Defs<T>, f: impl Fn(&T) -> String + Copy) -> String {
    list(d, |Def(name, items)| {
        format!("(def {} {})", quote(name), spec_list(items, f))
    })
}

fn scope(s: &ConfigScope) -> String {
    match s {
        ConfigScope::Generic => "generic".to_string(),
        ConfigScope::Host(l) => format!("(host {})", spec_list(l, host)),
        ConfigScope::User(l) => format!("(user {})", spec_list(l, user)),
        ConfigScope::RunAs(l) => format!("(runas {})", spec_list(l, user)),
        ConfigScope::Command(l) => format!("(command {})", spec_list(l, simple_command)),
    }
}

/// How base B sets one field away from its default (see `DUMP.md`, "Settings bases").
enum BaseB {
    Flag,
    Negate,
    Text(&'static str),
    Integer(&'static str),
    List(&'static [&'static str]),
}

/// Base B, in field declaration order: every field differs from `Settings::default()`.
const BASE_B: &[(&str, BaseB)] = &[
    ("always_query_group_plugin", BaseB::Flag),
    ("always_set_home", BaseB::Flag),
    ("env_reset", BaseB::Negate),
    ("fqdn", BaseB::Flag),
    ("ignore_dot", BaseB::Negate),
    ("lecture", BaseB::Text("always")),
    ("mailerpath", BaseB::Text("/b/mailer")),
    ("mail_badpass", BaseB::Negate),
    ("match_group_by_gid", BaseB::Flag),
    ("use_pty", BaseB::Negate),
    ("visiblepw", BaseB::Flag),
    ("pwfeedback", BaseB::Negate),
    ("rootpw", BaseB::Flag),
    ("targetpw", BaseB::Flag),
    ("noexec", BaseB::Flag),
    ("noninteractive_auth", BaseB::Flag),
    ("log_allowed", BaseB::Negate),
    ("log_denied", BaseB::Negate),
    ("insults", BaseB::Flag),
    ("setenv", BaseB::Flag),
    ("runcwd", BaseB::Text("/b/cwd")),
    ("apparmor_profile", BaseB::Text("b_profile")),
    ("umask", BaseB::Integer("077")),
    ("umask_override", BaseB::Flag),
    ("passwd_tries", BaseB::Integer("7")),
    ("secure_path", BaseB::Text("/b/bin")),
    ("verifypw", BaseB::Text("any")),
    ("passwd_timeout", BaseB::Integer("2")),
    ("timestamp_timeout", BaseB::Integer("3")),
    ("timestamp_type", BaseB::Text("ppid")),
    ("editor", BaseB::Text("/b/editor")),
    ("env_editor", BaseB::Negate),
    ("env_keep", BaseB::List(&["B_KEEP"])),
    ("env_check", BaseB::List(&["B_CHECK"])),
    ("env_delete", BaseB::List(&["B_DELETE"])),
];

fn base_b() -> Settings {
    let mut settings = Settings::default();
    for (name, how) in BASE_B {
        let modifier: SettingsModifier = match (how, defaults::set(name)) {
            (BaseB::Negate, _) => defaults::negate(name).expect("negatable"),
            (BaseB::Flag, Some(SettingKind::Flag(f))) => f,
            (BaseB::Text(v), Some(SettingKind::Text(s))) => {
                defaults::check_text(s, v).expect("valid text")
            }
            (BaseB::Integer(v), Some(SettingKind::Integer(s))) => {
                defaults::check_integer(s, v).expect("valid integer")
            }
            (BaseB::List(v), Some(SettingKind::List(s))) => {
                defaults::build_list(s, ListMode::Set, v.iter().map(|s| s.to_string()).collect())
            }
            _ => panic!("base B: wrong kind for {name}"),
        };
        modifier.apply(&mut settings);
    }
    settings
}

fn fields(settings: &Settings) -> String {
    let fields: Vec<String> = settings
        .dump_fields()
        .into_iter()
        .map(|(name, value)| format!("({name} {value})"))
        .collect();
    format!("[{}]", fields.join(" "))
}

/// A settings modifier, by its effect on base A (`Settings::default()`) and on base B.
fn setting(on_a: SettingsModifier, on_b: SettingsModifier) -> String {
    let mut a = Settings::default();
    on_a.apply(&mut a);
    let mut b = base_b();
    on_b.apply(&mut b);
    format!("(setting {} {})", fields(&a), fields(&b))
}

fn sudo(item: Sudo, second: &mut impl Iterator<Item = SettingsModifier>) -> String {
    match item {
        Sudo::Spec(PermissionSpec { users, permissions }) => {
            format!("(spec {} {})", spec_list(&users, user), list(&permissions, perm))
        }
        Sudo::Decl(Directive::UserAlias(d)) => format!("(user_alias {})", defs(&d, user)),
        Sudo::Decl(Directive::HostAlias(d)) => format!("(host_alias {})", defs(&d, host)),
        Sudo::Decl(Directive::CmndAlias(d)) => format!("(cmnd_alias {})", defs(&d, command)),
        Sudo::Decl(Directive::RunasAlias(d)) => format!("(runas_alias {})", defs(&d, user)),
        Sudo::Decl(Directive::Defaults(mods, s)) => {
            let settings: Vec<String> = mods
                .into_iter()
                .map(|m| setting(m, second.next().expect("deterministic parse")))
                .collect();
            format!("(defaults {} [{}])", scope(&s), settings.join(" "))
        }
        Sudo::Include(path, s) => format!("(include {} {})", quote(&path), span(&s)),
        Sudo::IncludeDir(path, s) => format!("(includedir {} {})", quote(&path), span(&s)),
        #[cfg(feature = "unstable-remote-sudoers")]
        Sudo::Remote(path, PeerSpec { user, group }, s) => {
            let group = match group {
                None => "none".to_string(),
                Some(g) => format!("(some {})", ident(&g)),
            };
            format!(
                "(remote {} (peer {} {group}) {})",
                quote(&path),
                ident(&user),
                span(&s)
            )
        }
        Sudo::LineComment => "comment".to_string(),
    }
}

/// Dump of two parses of the same text: everything is taken from `first`, except that each
/// settings modifier of `first` is applied to base A and its counterpart in `second` to base B.
fn dump_items(first: Vec<Result<Sudo, Status>>, second: Vec<Result<Sudo, Status>>) -> String {
    let mut second = second
        .into_iter()
        .flat_map(|item| match item {
            Ok(Sudo::Decl(Directive::Defaults(mods, _))) => mods,
            _ => Vec::new(),
        })
        .collect::<Vec<_>>()
        .into_iter();
    let mut out = String::new();
    for item in first {
        match item {
            Ok(item) => {
                let _ = writeln!(out, "ok {}", sudo(item, &mut second));
            }
            Err(Status::Fatal(s, msg)) => {
                let _ = writeln!(out, "fatal {} {}", span(&s), quote(&msg.to_string()));
            }
            Err(Status::Reject) => out.push_str("reject\n"),
        }
    }
    out
}

/// The dump of `text`: one line per item returned by `parse_lines::<Sudo>`, in order.
pub(super) fn dump(text: &str) -> String {
    CharStream::with_text(text, |cursor| {
        let first = parse_lines::<Sudo>(&mut cursor.clone());
        let second = parse_lines::<Sudo>(cursor);
        dump_items(first, second)
    })
}

/// [dump], with a panic of the parser recorded as the single line `panic <quoted message>`.
pub(super) fn dump_catching(text: &str) -> String {
    match std::panic::catch_unwind(|| dump(text)) {
        Ok(out) => out,
        Err(payload) => {
            let msg = if let Some(s) = payload.downcast_ref::<&str>() {
                s.to_string()
            } else if let Some(s) = payload.downcast_ref::<String>() {
                s.clone()
            } else {
                String::new()
            };
            format!("panic {}\n", quote(&msg))
        }
    }
}

/// Command patterns of the accepted items of `text` that name an existing path outside the
/// fixture root: evidence that `SimpleCommand::construct` canonicalized against the host.
fn host_paths(text: &str) -> Vec<String> {
    let mut patterns = Vec::new();
    let mut push_cmd = |c: &SimpleCommand| patterns.push(c.as_str().to_string());
    let commands = |l: &[Spec<Command>], push: &mut dyn FnMut(&SimpleCommand)| {
        for s in l {
            if let Qualified::Allow(Meta::Only((c, _))) | Qualified::Forbid(Meta::Only((c, _))) = s
            {
                push(c);
            }
        }
    };
    for item in CharStream::with_text(text, parse_lines::<Sudo>)
        .into_iter()
        .flatten()
    {
        match item {
            Sudo::Spec(PermissionSpec { permissions, .. }) => {
                for (_, entries) in &permissions {
                    for (_, CommandSpec(_, cmd)) in entries {
                        commands(std::slice::from_ref(cmd), &mut push_cmd);
                    }
                }
            }
            Sudo::Decl(Directive::CmndAlias(d)) => {
                for Def(_, items) in &d {
                    commands(items, &mut push_cmd);
                }
            }
            Sudo::Decl(Directive::Defaults(_, ConfigScope::Command(l))) => {
                for s in &l {
                    if let Qualified::Allow(Meta::Only(c)) | Qualified::Forbid(Meta::Only(c)) = s {
                        push_cmd(c);
                    }
                }
            }
            _ => {}
        }
    }
    patterns
        .into_iter()
        .filter(|p| {
            let path = p.strip_suffix("/*").unwrap_or(p);
            path.starts_with('/')
                && !path.starts_with(FIXTURE_ROOT)
                && std::fs::metadata(path).is_ok()
        })
        .collect()
}

/// Recreates the fixture directory (layout documented in `DUMP.md`).
pub(super) fn make_fixture() -> std::io::Result<()> {
    use std::os::unix::fs::symlink;
    let root = Path::new(FIXTURE_ROOT);
    if root.symlink_metadata().is_ok() {
        std::fs::remove_dir_all(root)?;
    }
    for dir in ["bin", "sub", "incdir"] {
        std::fs::create_dir_all(root.join(dir))?;
    }
    std::fs::write(root.join("bin/tool"), "")?;
    std::fs::write(root.join("include"), "")?;
    symlink("tool", root.join("bin/alias"))?;
    symlink("bin", root.join("link"))?;
    Ok(())
}

/// Reads a corpus: a directory (one case per regular file, label = file name, in name order) or
/// a file of lines `<label> <quoted text>`.
fn read_corpus(path: &Path) -> Vec<(String, String)> {
    if path.is_dir() {
        let mut names: Vec<_> = std::fs::read_dir(path)
            .expect("corpus directory")
            .map(|e| e.expect("directory entry").path())
            .filter(|p| p.is_file())
            .collect();
        names.sort();
        names
            .into_iter()
            .map(|p| {
                let label = p.file_name().unwrap().to_string_lossy().into_owned();
                let text = std::fs::read_to_string(&p)
                    .unwrap_or_else(|e| panic!("{}: {e}", p.display()));
                (label, text)
            })
            .collect()
    } else {
        let corpus = std::fs::read_to_string(path).expect("corpus file");
        corpus
            .lines()
            .enumerate()
            .map(|(n, line)| {
                let (label, rest) = line
                    .split_once(' ')
                    .unwrap_or_else(|| panic!("corpus line {}: no label", n + 1));
                match unquote(rest) {
                    Some((text, "")) => (label.to_string(), text),
                    _ => panic!("corpus line {}: malformed quoted text", n + 1),
                }
            })
            .collect()
    }
}

/// Writes the dump of a corpus. Does nothing unless `SUDO_PARSER_DUMP_CORPUS` is set.
///
/// - `SUDO_PARSER_DUMP_CORPUS`: corpus file or directory (see [read_corpus]).
/// - `SUDO_PARSER_DUMP_OUT`: output file; per case the line `case <label>`, then its dump.
///   Next to it, `<OUT>.hostdep` lists `<label> <quoted pattern>` for every command pattern that
///   names an existing host path outside the fixture root.
#[test]
fn dump_corpus() {
    let Some(corpus) = std::env::var_os("SUDO_PARSER_DUMP_CORPUS") else {
        return;
    };
    let out = std::env::var_os("SUDO_PARSER_DUMP_OUT").expect("SUDO_PARSER_DUMP_OUT must be set");
    assert!(
        Path::new(ABSENT_PREFIX).symlink_metadata().is_err(),
        "{ABSENT_PREFIX} exists on this host; the corpus convention needs it absent"
    );
    make_fixture().expect("fixture");
    assert_eq!(
        std::fs::canonicalize(FIXTURE_ROOT).expect("fixture root"),
        Path::new(FIXTURE_ROOT),
        "the fixture root must be its own canonical path"
    );
    let cases = read_corpus(Path::new(&corpus));
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut dump_text = String::new();
    let mut hostdep = String::new();
    let mut panics = 0usize;
    for (label, text) in &cases {
        let d = dump_catching(text);
        if d.starts_with("panic ") {
            panics += 1;
        } else {
            for p in host_paths(text) {
                let _ = writeln!(hostdep, "{label} {}", quote(&p));
            }
        }
        let _ = writeln!(dump_text, "case {label}");
        dump_text.push_str(&d);
    }
    std::panic::set_hook(hook);
    std::fs::write(&out, dump_text).expect("write dump");
    let mut hostdep_path = out.clone();
    hostdep_path.push(".hostdep");
    std::fs::write(hostdep_path, hostdep).expect("write hostdep");
    let mut bases_path = out.clone();
    bases_path.push(".bases");
    std::fs::write(
        bases_path,
        format!(
            "a {}\nb {}\n",
            fields(&Settings::default()),
            fields(&base_b())
        ),
    )
    .expect("write bases");
    let _ = writeln!(
        std::io::stderr(),
        "parser dump: {} cases, {panics} panics",
        cases.len()
    );
}

/// The predicates of the character-class table, in table order.
const CHAR_CLASSES: &[(&str, fn(char) -> bool)] = &[
    ("alphanumeric", char::is_alphanumeric),
    ("uppercase", char::is_uppercase),
    ("numeric", char::is_numeric),
    ("control", char::is_control),
    ("whitespace", char::is_whitespace),
];

/// The character-class table: `unicode <version>`, then per predicate its maximal ranges of
/// code points, one line `<predicate> <first> <last>` each (lowercase hexadecimal, inclusive).
pub(super) fn char_table() -> String {
    let (major, minor, update) = char::UNICODE_VERSION;
    let mut out = format!("unicode {major}.{minor}.{update}\n");
    for (name, pred) in CHAR_CLASSES {
        let mut start: Option<u32> = None;
        for cp in 0..=0x11_0000u32 {
            let member = char::from_u32(cp).is_some_and(pred);
            match (member, start) {
                (true, None) => start = Some(cp),
                (false, Some(s)) => {
                    let _ = writeln!(out, "{name} {s:x} {:x}", cp - 1);
                    start = None;
                }
                _ => {}
            }
        }
    }
    out
}

/// Writes the character-class table to `SUDO_PARSER_DUMP_CHARTABLE`; does nothing when unset.
#[test]
fn write_char_table() {
    if let Some(path) = std::env::var_os("SUDO_PARSER_DUMP_CHARTABLE") {
        std::fs::write(path, char_table()).expect("write char table");
    }
}

#[test]
fn char_table_shape() {
    let table = char_table();
    assert!(table.starts_with("unicode "));
    assert!(table.contains("\nalphanumeric 30 39\n"));
    assert!(table.contains("\ncontrol 0 1f\n"));
    assert!(table.contains("\nwhitespace 9 d\n"));
}

#[test]
fn quote_round_trip() {
    for s in ["", "a b", "\"\\", "\u{0}\u{7f}\u{e9}\u{10ffff}\n\t", "\\u{41}"] {
        let q = quote(s);
        assert!(q.bytes().all(|b| (b' '..=b'~').contains(&b)));
        assert_eq!(unquote(&q), Some((s.to_string(), "")));
    }
    assert_eq!(quote("\u{e9}\n\"x\\"), r#""\u{e9}\u{a}\"x\\""#);
}

#[test]
fn base_b_differs_from_default_everywhere() {
    let a = Settings::default().dump_fields();
    let b = base_b().dump_fields();
    assert_eq!(a.len(), BASE_B.len());
    for ((name_a, va), ((name_b, vb), (name, _))) in a.iter().zip(b.iter().zip(BASE_B)) {
        assert_eq!(name_a, name_b);
        assert_eq!(name_a, name);
        assert_ne!(va, vb, "{name} equal in both bases");
    }
}

#[test]
fn dump_is_deterministic() {
    let text = "Defaults env_keep += \"A B\", !use_pty\nalice ALL = (root) NOPASSWD: /bin/x\n";
    assert_eq!(dump(text), dump(text));
}

#[test]
fn dump_defaults_setting_by_effect() {
    let mut a = Settings::default();
    defaults::negate("use_pty").unwrap().apply(&mut a);
    let mut b = base_b();
    defaults::negate("use_pty").unwrap().apply(&mut b);
    assert_eq!(
        dump("Defaults!/sudoers-nx/x !use_pty\n"),
        format!(
            "ok (defaults (command [(allow (only \"/sudoers-nx/x\"))]) [(setting {} {})])\n",
            fields(&a),
            fields(&b)
        )
    );
}

fn assert_dump(text: &str, expected: &[&str]) {
    let mut want = expected.join("\n");
    want.push('\n');
    assert_eq!(dump(text), want, "input {text:?}");
}

const ALICE: &str = "(allow (only (user (name \"alice\"))))";
const BOB: &str = "(allow (only (user (name \"bob\"))))";

/// PLAN.md section 3.3, first table, row by row.
#[test]
fn plan_3_3_recovery_rows() {
    let all = "(entry none [] (allow all))";
    let rule = |user: &str, entries: &str| format!("ok (spec [{user}] [(perm [(allow all)] [{entries}])])");
    let bob_runas_all = rule(BOB, "(entry (runas [(allow all)] []) [] (allow all))");
    // 1: an error inside the list drops the line; the continuation is parsed as a line of its own
    assert_dump(
        "alice ALL = /bin/a, sha224:x \\\nbob ALL = (ALL) ALL\n",
        &[
            "fatal 1:21-1:27 \"digest specifications are not supported\"",
            "ok comment",
            &bob_runas_all,
        ],
    );
    // 2: one rule; the continued line becomes arguments of the second command
    assert_dump(
        "alice ALL = /bin/a, /bin/b \\\nbob ALL = (ALL) ALL\n",
        &[&rule(
            ALICE,
            "(entry none [] (allow (only (cmd \"/bin/a\" (prefix []))))) \
             (entry none [] (allow (only (cmd \"/bin/b\" (exact [\"bob\" \"ALL\" \"=\" \"(ALL)\" \"ALL\"])))))",
        )],
    );
    // 3: no final newline
    assert_dump(
        "alice ALL = ALL",
        &[
            &rule(ALICE, all),
            "fatal 1:16-1:16 \"missing line terminator at end of file\"",
        ],
    );
    // 4: prefix acceptance, then the next line
    assert_dump(
        "alice ALL = ALL ) junk\nbob ALL = ALL\n",
        &[
            &rule(ALICE, all),
            "fatal 1:17-1:17 \"garbage at end of line\"",
            "ok comment",
            &rule(BOB, all),
        ],
    );
    // 5: ALL, then the exclusion
    assert_dump(
        "alice ALL = ALL, !/usr/bin/su\n",
        &[&rule(
            ALICE,
            "(entry none [] (allow all)) \
             (entry none [] (forbid (only (cmd \"/usr/bin/su\" (prefix [])))))",
        )],
    );
    // 6: comma missing: the rule with ALL only, then garbage
    assert_dump(
        "alice ALL = ALL !/usr/bin/su\n",
        &[
            &rule(ALICE, all),
            "fatal 1:17-1:17 \"garbage at end of line\"",
            "ok comment",
        ],
    );
    // 7: an error inside the exclusion drops the line
    assert_dump(
        "alice ALL = ALL, !sha224:x\n",
        &[
            "fatal 1:19-1:25 \"digest specifications are not supported\"",
            "ok comment",
        ],
    );
}

/// PLAN.md finding F-P3: a quoted user whose content is not a user is consumed and then
/// rejected; the callers observed turn this into a fatal error.
#[test]
fn finding_f_p3_quoted_non_user() {
    // first user of a line: `expect_nonterminal` reports the consumed range `"@x`
    assert_dump(
        "\"@x\" ALL = ALL\n",
        &["fatal 1:1-1:4 \"expected elem\"", "ok comment"],
    );
    // later element of a user list
    assert_dump(
        "alice, \"@x\" ALL = ALL\n",
        &["fatal 1:8-1:11 \"expected elem\"", "ok comment"],
    );
    // runas user list: the rejection is discarded, the closing parenthesis is then missing
    assert_dump(
        "alice ALL = (\"@x\") ALL\n",
        &["fatal 1:17-1:17 \"expecting ')' but found '\\\"'\"", "ok comment"],
    );
}

/// PLAN.md finding F-P4: after `#`, any failure of the user id, fatal ones included, makes the
/// line an include or a comment.
#[test]
fn finding_f_p4_hash_identifier() {
    let id_rule = "ok (spec [(allow (only (user (id 1))))] [(perm [(allow all)] [(entry none [] (allow all))])])";
    assert_dump("#1 ALL = ALL\n", &[id_rule]);
    // "value too large" (does not fit u32): comment
    assert_dump("#4294967296 ALL = ALL\n", &["ok comment"]);
    // "token exceeds maximum length" (11 digits): comment
    assert_dump("#12345678901 ALL = ALL\n", &["ok comment"]);
    // no digits at all: include, or comment
    assert_dump(
        "#include /etc/x\n",
        &["ok (include \"/etc/x\" 1:2-1:16)"],
    );
    assert_dump("#x ALL = ALL\n", &["ok comment"]);
}
