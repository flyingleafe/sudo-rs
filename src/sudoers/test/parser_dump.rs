//! Canonical text dump of `parse_lines::<Sudo>`.
//!
//! The format, the escaping rule, the character-class table and the corpus conventions are
//! specified in `proofs/parser/DUMP.md`; keep the Rust and Lean observers in step.

use std::fmt::Write as _;
use std::io::Write as _;
use std::path::Path;

use super::super::ast::*;
use super::super::basic_parser::{Span, Status, parse_lines};
use super::super::char_stream::CharStream;
use super::super::tokens::*;
use crate::defaults::SettingsModifier;

pub(super) use crate::defaults::quote_for_dump as quote;

/// Root of the file-system fixture used by the `fixture` corpus category.
pub(super) const FIXTURE_ROOT: &str = "/tmp/sudo-rs-parser-dump-fixture";

/// Command-path prefix of the generated corpus; it must not exist on the host.
pub(super) const ABSENT_PREFIX: &str = "/sudoers-nx";

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

fn sudo(item: &Sudo) -> String {
    match item {
        Sudo::Spec(PermissionSpec { users, permissions }) => {
            format!(
                "(spec {} {})",
                spec_list(users, user),
                list(permissions, perm)
            )
        }
        Sudo::Decl(Directive::UserAlias(d)) => format!("(user_alias {})", defs(d, user)),
        Sudo::Decl(Directive::HostAlias(d)) => format!("(host_alias {})", defs(d, host)),
        Sudo::Decl(Directive::CmndAlias(d)) => format!("(cmnd_alias {})", defs(d, command)),
        Sudo::Decl(Directive::RunasAlias(d)) => format!("(runas_alias {})", defs(d, user)),
        Sudo::Decl(Directive::Defaults(mods, s)) => {
            format!(
                "(defaults {} {})",
                scope(s),
                list(mods, SettingsModifier::dump_modifier)
            )
        }
        Sudo::Include(path, s) => format!("(include {} {})", quote(path), span(s)),
        Sudo::IncludeDir(path, s) => format!("(includedir {} {})", quote(path), span(s)),
        #[cfg(feature = "unstable-remote-sudoers")]
        Sudo::Remote(path, PeerSpec { user, group }, s) => {
            let group = match group {
                None => "none".to_string(),
                Some(g) => format!("(some {})", ident(g)),
            };
            format!(
                "(remote {} (peer {} {group}) {})",
                quote(path),
                ident(user),
                span(s)
            )
        }
        Sudo::LineComment => "comment".to_string(),
    }
}

fn dump_items(items: &[Result<Sudo, Status>]) -> String {
    let mut out = String::new();
    for item in items {
        match item {
            Ok(item) => {
                let _ = writeln!(out, "ok {}", sudo(item));
            }
            Err(Status::Fatal(s, msg)) => {
                let _ = writeln!(out, "fatal {} {}", span(s), quote(&msg.to_string()));
            }
            Err(Status::Reject) => out.push_str("reject\n"),
        }
    }
    out
}

/// The dump of `text`: one line per item returned by `parse_lines::<Sudo>`, in order.
pub(super) fn dump(text: &str) -> String {
    dump_items(&CharStream::with_text(text, parse_lines::<Sudo>))
}

/// Dump and report host-dependent paths from the same parse, or only a panic record.
fn dump_catching(text: &str, on_host_path: impl FnMut(&str)) -> String {
    match std::panic::catch_unwind(|| {
        let items = CharStream::with_text(text, parse_lines::<Sudo>);
        (dump_items(&items), items)
    }) {
        Ok((out, items)) => {
            host_paths(&items, on_host_path);
            out
        }
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

/// Report command patterns naming an existing path outside the fixture root: evidence that
/// `SimpleCommand::construct` canonicalized against the host.
fn host_paths(items: &[Result<Sudo, Status>], mut on_host_path: impl FnMut(&str)) {
    let mut push_cmd = |c: &SimpleCommand| {
        let pattern = c.as_str();
        let path = pattern.strip_suffix("/*").unwrap_or(pattern);
        if path.starts_with('/')
            && !path.starts_with(FIXTURE_ROOT)
            && std::fs::metadata(path).is_ok()
        {
            on_host_path(pattern);
        }
    };
    let commands = |l: &[Spec<Command>], push: &mut dyn FnMut(&SimpleCommand)| {
        for s in l {
            if let Qualified::Allow(Meta::Only((c, _))) | Qualified::Forbid(Meta::Only((c, _))) = s
            {
                push(c);
            }
        }
    };
    for item in items.iter().filter_map(|item| item.as_ref().ok()) {
        match item {
            Sudo::Spec(PermissionSpec { permissions, .. }) => {
                for (_, entries) in permissions {
                    for (_, CommandSpec(_, cmd)) in entries {
                        commands(std::slice::from_ref(cmd), &mut push_cmd);
                    }
                }
            }
            Sudo::Decl(Directive::CmndAlias(d)) => {
                for Def(_, items) in d {
                    commands(items, &mut push_cmd);
                }
            }
            Sudo::Decl(Directive::Defaults(_, ConfigScope::Command(l))) => {
                for s in l {
                    if let Qualified::Allow(Meta::Only(c)) | Qualified::Forbid(Meta::Only(c)) = s {
                        push_cmd(c);
                    }
                }
            }
            _ => {}
        }
    }
}

/// Create the documented tree once. On reuse, verify its layout without writing into it.
/// Never remove an existing directory at a well-known path on a shared machine.
fn ensure_fixture(root: &Path) -> std::io::Result<()> {
    use std::fs::{self, DirBuilder, File};
    use std::io::{Error, ErrorKind};
    use std::os::unix::fs::{DirBuilderExt, MetadataExt, symlink};

    let dirs = [("bin", 2), ("sub", 0), ("incdir", 0)];
    let files = ["bin/tool", "include"];
    let links = [("bin/alias", "tool"), ("link", "bin")];
    match DirBuilder::new().mode(0o700).create(root) {
        Ok(()) => {
            for (d, _) in dirs {
                DirBuilder::new().mode(0o700).create(root.join(d))?;
            }
            for f in files {
                File::create_new(root.join(f))?;
            }
            for (l, target) in links {
                symlink(target, root.join(l))?;
            }
        }
        Err(e) if e.kind() == ErrorKind::AlreadyExists => {}
        Err(e) => return Err(e),
    }

    let invalid = || Error::new(ErrorKind::InvalidData, "unexpected parser fixture; left untouched");
    let uid = crate::system::User::effective_uid().inner();
    for (d, count) in [("", 5)].into_iter().chain(dirs) {
        let path = root.join(d);
        let meta = fs::symlink_metadata(if d.is_empty() { root } else { &path })?;
        if !meta.is_dir() || meta.uid() != uid || meta.mode() & 0o022 != 0
            || fs::read_dir(&path)?.count() != count
        {
            return Err(invalid());
        }
    }
    for f in files {
        let meta = fs::symlink_metadata(root.join(f))?;
        if !meta.is_file() || meta.len() != 0 || meta.uid() != uid || meta.mode() & 0o022 != 0 {
            return Err(invalid());
        }
    }
    for (l, target) in links {
        if fs::read_link(root.join(l))? != Path::new(target) {
            return Err(invalid());
        }
    }
    Ok(())
}

#[test]
fn fixture_reuse_preserves_unrelated_files() {
    let tmp = std::env::temp_dir().join(format!("sudo-parser-fixture-test-{}", std::process::id()));
    std::fs::create_dir(&tmp).unwrap();
    let root = tmp.join("tree");
    ensure_fixture(&root).unwrap();
    ensure_fixture(&root).unwrap();
    let extra = root.join("do-not-remove");
    std::fs::write(&extra, b"untouched").unwrap();
    assert_eq!(ensure_fixture(&root).unwrap_err().kind(), std::io::ErrorKind::InvalidData);
    assert_eq!(std::fs::read(&extra).unwrap(), b"untouched");
    std::fs::remove_dir_all(tmp).unwrap();
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
/// - `SUDO_PARSER_DUMP_OUT`: versioned output file; per case `case <label>`, then its dump.
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
    ensure_fixture(Path::new(FIXTURE_ROOT)).expect("fixture");
    assert_eq!(
        std::fs::canonicalize(FIXTURE_ROOT).expect("fixture root"),
        Path::new(FIXTURE_ROOT),
        "the fixture root must be its own canonical path"
    );
    let cases = read_corpus(Path::new(&corpus));
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut dump_text = String::from("parser-dump 2\n");
    let mut hostdep = String::new();
    let mut panics = 0usize;
    for (label, text) in &cases {
        let d = dump_catching(text, |p| {
            let _ = writeln!(hostdep, "{label} {}", quote(p));
        });
        if d.starts_with("panic ") {
            panics += 1;
        }
        let _ = writeln!(dump_text, "case {label}");
        dump_text.push_str(&d);
    }
    std::panic::set_hook(hook);
    std::fs::write(&out, dump_text).expect("write dump");
    let mut hostdep_path = out.clone();
    hostdep_path.push(".hostdep");
    std::fs::write(hostdep_path, hostdep).expect("write hostdep");
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
fn dump_is_deterministic() {
    let text = "Defaults env_keep += \"A B\", !use_pty\nalice ALL = (root) NOPASSWD: /bin/x\n";
    assert_eq!(dump(text), dump(text));
}

#[test]
fn dump_defaults_setting_by_payload() {
    // These removals had the same dump in v1: neither name was in either fixed base.
    assert_dump(
        "Defaults env_keep -= DUMP_A\nDefaults env_keep -= DUMP_B\n",
        &[
            r#"ok (defaults generic [(setting env_keep (del ["DUMP_A"]))])"#,
            r#"ok (defaults generic [(setting env_keep (del ["DUMP_B"]))])"#,
        ],
    );
    assert_dump(
        concat!(
            "Defaults env_check = \"B A B\"\n",
            "Defaults env_check += \"B A B\"\n",
            "Defaults env_check += \"A B B\"\n",
            "Defaults !mailerpath, !env_delete\n",
            "Defaults !use_pty, lecture=once, umask=077, editor=\"a b\"\n",
        ),
        &[
            r#"ok (defaults generic [(setting env_check (set ["B" "A" "B"]))])"#,
            r#"ok (defaults generic [(setting env_check (add ["B" "A" "B"]))])"#,
            r#"ok (defaults generic [(setting env_check (add ["A" "B" "B"]))])"#,
            r#"ok (defaults generic [(setting mailerpath none) (setting env_delete (set []))])"#,
            concat!(
                "ok (defaults generic [(setting use_pty false) (setting lecture once) ",
                "(setting umask 63) (setting editor \"a b\")])",
            ),
        ],
    );
    assert_eq!(
        SettingsModifier::mailerpath(Some("".into())).dump_modifier(),
        r#"(setting mailerpath (some ""))"#,
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
