//! Behaviour preservation of the restricted-style `analyze` and `Sudoers::specify_*`: the live
//! code against the copies of the code before the rewrite (`super::legacy_analysis`).
//!
//! For every text both sides analyze the same parsed items; the results are printed and must be
//! equal: the rules, the four alias tables with their processing order, the customisers (scope
//! and modifiers), the settings, and the diagnostics (source, span, message) in order. Then, for
//! several requests, the settings in force after `specify_*` (`Settings::dump_fields`), the
//! decision of `check` / `check_list_permission` / `check_validate_permission` (live) against the
//! legacy `specify_*` followed by the same decision function, and the warnings about ignored
//! user specifiers. A panic is caught and compared by its message.
//!
//! Inputs: the texts of the unit tests and the generated and mutated corpus of
//! `src/sudoers/equiv/corpus.rs`, and texts that include files of a temporary directory tree.
//!
//! Evidence kind: test.

use std::cell::RefCell;
use std::ffi::OsString;
use std::fs::File;
use std::io::{self, Write as _};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

use super::super::*;
use super::{IGNORED, Named, legacy_analysis};

// the corpus of the parser equivalence tests (`super::super::equiv`, where it is private)
#[allow(clippy::duplicate_mod)]
#[path = "../equiv/corpus.rs"]
mod corpus;

// ------------------------------------------------------------------ include fixtures

thread_local! {
    static FIXTURE: RefCell<Option<PathBuf>> = const { RefCell::new(None) };
}

/// `open_sudoers` under test: a file below the fixture directory of this thread is opened
/// without the ownership checks of `audit::secure_open_sudoers` (a test cannot create files
/// owned by root); `None` for every other path.
pub(in crate::sudoers) fn open_fixture(path: &Path) -> Option<io::Result<File>> {
    FIXTURE.with_borrow(|root| match root {
        Some(root) if path.starts_with(root) => Some(File::open(path)),
        _ => None,
    })
}

/// A scratch directory with the given files (relative path, content; a content of `None` makes
/// a directory). While it lives, `open_sudoers` opens its files on this thread (unless created
/// with `relaxed = false`). Removed on drop.
struct Tree(PathBuf);

impl Tree {
    fn new(tag: &str, files: &[(&str, Option<&str>)], relaxed: bool) -> Tree {
        let base = std::env::temp_dir()
            .canonicalize()
            .unwrap()
            .join(format!("sudo-rs-analysis-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(&base).unwrap();
        for (name, content) in files {
            let path = base.join(name);
            match content {
                Some(text) => {
                    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
                    std::fs::write(&path, text.replace("$ROOT", &base.display().to_string()))
                        .unwrap()
                }
                None => std::fs::create_dir_all(&path).unwrap(),
            }
        }
        if relaxed {
            FIXTURE.with_borrow_mut(|root| *root = Some(base.clone()));
        }
        Tree(base)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }

    fn text(&self, name: &str) -> String {
        std::fs::read_to_string(self.path(name)).unwrap()
    }
}

impl Drop for Tree {
    fn drop(&mut self) {
        FIXTURE.with_borrow_mut(|root| *root = None);
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

// ------------------------------------------------------------------ printing

fn specs<T>(items: &[Spec<T>], f: &dyn Fn(&T) -> String) -> String {
    let parts: Vec<String> = items
        .iter()
        .map(|item| {
            let (sign, meta) = match item {
                Qualified::Allow(m) => ("+", m),
                Qualified::Forbid(m) => ("!", m),
            };
            match meta {
                Meta::All => format!("{sign}ALL"),
                Meta::Alias(name) => format!("{sign}alias {name:?}"),
                Meta::Only(x) => format!("{sign}{}", f(x)),
            }
        })
        .collect();
    format!("[{}]", parts.join(", "))
}

fn user(u: &UserSpecifier) -> String {
    format!("{u:?}")
}

fn ident(i: &Identifier) -> String {
    format!("{i:?}")
}

fn host(h: &Hostname) -> String {
    format!("{:?}", h.0)
}

fn command((pattern, args): &Command) -> String {
    match args {
        Args::Prefix(a) => format!("{:?} prefix {a:?}", pattern.as_str()),
        Args::Exact(a) => format!("{:?} exact {a:?}", pattern.as_str()),
    }
}

fn simple_command(pattern: &SimpleCommand) -> String {
    format!("{:?}", pattern.as_str())
}

fn modifier(m: &Modifier) -> String {
    match m {
        Modifier::Passwd => "PASSWD".into(),
        Modifier::Nopasswd => "NOPASSWD".into(),
        Modifier::Setenv => "SETENV".into(),
        Modifier::Nosetenv => "NOSETENV".into(),
        Modifier::Exec => "EXEC".into(),
        Modifier::Noexec => "NOEXEC".into(),
        Modifier::Cwd(dir) => format!("CWD {dir:?}"),
        Modifier::AppArmorProfile(p) => format!("APPARMOR {p:?}"),
        Modifier::Ignored(span) => format!("ignored {span:?}"),
        Modifier::NoOp => "noop".into(),
    }
}

fn rule(rule: &PermissionSpec) -> String {
    let permissions: Vec<String> = rule
        .permissions
        .iter()
        .map(|(hosts, entries)| {
            let entries: Vec<String> = entries
                .iter()
                .map(|(runas, CommandSpec(mods, cmd))| {
                    let runas = match runas {
                        Some(RunAs { users, groups }) => {
                            format!("({} : {})", specs(users, &user), specs(groups, &ident))
                        }
                        None => "-".into(),
                    };
                    let mods: Vec<String> = mods.iter().map(modifier).collect();
                    format!("{runas} {mods:?} {}", specs(std::slice::from_ref(cmd), &command))
                })
                .collect();
            format!("{} = {entries:?}", specs(hosts, &host))
        })
        .collect();
    format!("rule {} {permissions:?}", specs(&rule.users, &user))
}

fn table<T>(name: &str, VecOrd(order, defs): &VecOrd<Def<T>>, f: &dyn Fn(&T) -> String) -> String {
    let defs: Vec<String> = defs
        .iter()
        .map(|Def(id, members)| format!("{id:?} = {}", specs(members, f)))
        .collect();
    format!("{name} order {order:?} defs {defs:?}")
}

fn scope(s: &ConfigScope) -> String {
    match s {
        ConfigScope::Generic => "generic".into(),
        ConfigScope::Host(l) => format!("host {}", specs(l, &host)),
        ConfigScope::User(l) => format!("user {}", specs(l, &user)),
        ConfigScope::RunAs(l) => format!("runas {}", specs(l, &user)),
        ConfigScope::Command(l) => format!("command {}", specs(l, &simple_command)),
    }
}

/// Everything `analyze` produced.
fn show(sudoers: &Sudoers, errors: &[Error], out: &mut Vec<String>) {
    out.extend(sudoers.rules.iter().map(rule));
    out.push(table("user", &sudoers.aliases.user, &user));
    out.push(table("host", &sudoers.aliases.host, &host));
    out.push(table("cmnd", &sudoers.aliases.cmnd, &command));
    out.push(table("runas", &sudoers.aliases.runas, &user));
    for (s, modifiers) in &sudoers.customisers.non_cmnd {
        out.push(format!("defaults {} {modifiers:?}", scope(s)));
    }
    for (s, modifiers) in &sudoers.customisers.cmnd {
        out.push(format!("defaults! {} {modifiers:?}", specs(s, &command)));
    }
    out.push(format!("settings {:?}", sudoers.settings.dump_fields()));
    for e in errors {
        out.push(format!("error {:?} {:?} {:?}", e.source, e.location, e.message));
    }
}

// ------------------------------------------------------------------ comparison

/// The invoking user, the host, the target user (`None`: the request of `sudo -v`; equal to
/// the invoking user: `sudo -l`) and the command line of a request.
type Req = (&'static str, &'static str, Option<&'static str>, &'static str, &'static [&'static str]);

const REQUESTS: &[Req] = &[
    ("alice", "server", Some("root"), "/bin/ls", &["-l"]),
    ("bob", "server.example.com", Some("alice"), "/usr/bin/su", &[]),
    ("wheel", "1.2.3.4", Some("root"), "/bin/echo", &["a", "b"]),
    ("root", "localhost", None, "", &[]),
    ("alice", "SRV_1", Some("alice"), "list", &[]),
    ("bob", "server", Some("alice"), "list", &[]),
];

/// The live or the legacy side on the items of `text` read from `path`: what `analyze` produced,
/// then per request the settings in force and the decision. `Err` with the panic message.
fn run(live: bool, path: &Path, text: &str) -> Result<Vec<String>, String> {
    let chars = char_stream::chars_of(&text.to_string());
    let analyze_side = |items: Vec<basic_parser::Parsed<Sudo>>| {
        if live {
            analyze(path, items)
        } else {
            legacy_analysis::analyze(path, items)
        }
    };
    catch_unwind(AssertUnwindSafe(|| {
        let mut out = Vec::new();
        IGNORED.with_borrow_mut(Vec::clear);
        let (sudoers, errors) = if live {
            analyze_text(path, &chars)
        } else {
            analyze_side(parse_sudoers(&chars))
        };
        show(&sudoers, &errors, &mut out);
        // without rules and customisers every request is denied with the default settings
        let requests = if sudoers.rules.is_empty()
            && sudoers.customisers.non_cmnd.is_empty()
            && sudoers.customisers.cmnd.is_empty()
        {
            &[]
        } else {
            REQUESTS
        };
        for &(user, hostname, target, command, args) in requests {
            let (mut sudoers, _) = analyze_side(parse_sudoers(&chars));
            let user = Named(user);
            let hostname = system::Hostname::fake(hostname);
            let command = Path::new(command);
            let args: Vec<OsString> = args.iter().map(OsString::from).collect();
            let decision = match target {
                None if live => format!("{:?}", sudoers.check_validate_permission(&user, &hostname)),
                None => {
                    legacy_analysis::specify_host_user_runas(&mut sudoers, &hostname, &user, None);
                    match validate_flags(&sudoers.rules, &sudoers.aliases, &user, &hostname) {
                        Some(tag) => format!("{:?}", Authorization::Allowed(sudoers.settings.to_auth(&tag), ())),
                        None => format!("{:?}", Authorization::<()>::Forbidden),
                    }
                }
                Some(target) if command == Path::new("list") => {
                    let target = Named(target);
                    let request = ListRequest {
                        inspected_user: &target,
                        target_user: &target,
                        target_group: &target,
                    };
                    if live {
                        format!("{:?}", sudoers.check_list_permission(&user, &hostname, request))
                    } else {
                        if request.inspected_user != &user {
                            legacy_analysis::specify_host_user_runas(
                                &mut sudoers,
                                &hostname,
                                &user,
                                Some(request.inspected_user),
                            );
                            legacy_analysis::specify_command(&mut sudoers, Path::new("list"), &[]);
                        }
                        match list_flags(&sudoers.rules, &sudoers.aliases, &user, &hostname, request) {
                            Some(tag) => format!("{:?}", Authorization::Allowed(sudoers.settings.to_auth(&tag), ())),
                            None => format!("{:?}", Authorization::<()>::Forbidden),
                        }
                    }
                }
                Some(target) => {
                    let target = Named(target);
                    let request = Request {
                        user: &target,
                        group: &target,
                        command,
                        arguments: &args,
                    };
                    let judgement = if live {
                        sudoers.check(&user, &hostname, request)
                    } else {
                        legacy_analysis::specify_host_user_runas(
                            &mut sudoers,
                            &hostname,
                            &user,
                            Some(request.user),
                        );
                        legacy_analysis::specify_command(&mut sudoers, request.command, request.arguments);
                        let flags = permission_flags(&sudoers.rules, &sudoers.aliases, &user, &hostname, request);
                        Judgement { flags, settings: sudoers.settings.clone() }
                    };
                    format!("{:?} {:?}", judgement.flags, judgement.settings.dump_fields())
                }
            };
            out.push(format!(
                "request {decision} settings {:?} customisers left {} {}",
                sudoers.settings.dump_fields(),
                sudoers.customisers.non_cmnd.len(),
                sudoers.customisers.cmnd.len()
            ));
            // a second call applies nothing
            if live {
                sudoers.specify_host_user_runas(&hostname, &user, Some(&user));
                sudoers.specify_command(command, &args);
            } else {
                legacy_analysis::specify_host_user_runas(&mut sudoers, &hostname, &user, Some(&user));
                legacy_analysis::specify_command(&mut sudoers, command, &args);
            }
            out.push(format!("again {:?}", sudoers.settings.dump_fields()));
        }
        out.push(format!("ignored {:?}", IGNORED.with_borrow(Vec::clone)));
        out
    }))
    .map_err(|payload| {
        if let Some(s) = payload.downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = payload.downcast_ref::<String>() {
            s.clone()
        } else {
            "non-string panic".to_string()
        }
    })
}

/// Live against legacy on `text`; `Err` describes the first difference.
fn compare(path: &Path, text: &str) -> Result<Result<Vec<String>, String>, String> {
    let live = run(true, path, text);
    let legacy = run(false, path, text);
    if live == legacy {
        return Ok(live);
    }
    let detail = match (&live, &legacy) {
        (Ok(a), Ok(b)) => {
            let k = a.iter().zip(b).take_while(|(x, y)| x == y).count();
            format!("first difference at line {k}:\n  live:   {:?}\n  legacy: {:?}", a.get(k), b.get(k))
        }
        _ => format!("live: {live:?}\nlegacy: {legacy:?}"),
    };
    Err(format!("{text:?}\n{detail}"))
}

/// Compare on every text; panics with the first differences. Returns a summary.
fn check_all(path: &Path, texts: &[String]) -> String {
    let mut failures = Vec::new();
    let (mut panics, mut rules, mut defs, mut customisers, mut errors) = (0, 0, 0, 0, 0);
    let mut requests = 0;
    for text in texts {
        match compare(path, text) {
            Err(diff) => failures.push(diff),
            Ok(Err(_)) => panics += 1,
            Ok(Ok(lines)) => {
                for line in &lines {
                    match line.split(' ').next().unwrap_or("") {
                        "rule" => rules += 1,
                        "defaults" | "defaults!" => customisers += 1,
                        "error" => errors += 1,
                        "request" => requests += 1,
                        _ => {}
                    }
                }
                defs += lines
                    .iter()
                    .filter(|l| l.contains(" order ") && !l.ends_with("defs []"))
                    .count();
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} texts differ; the first ones:\n{}",
        failures.len(),
        texts.len(),
        failures[..failures.len().min(5)].join("\n\n")
    );
    format!(
        "{} texts, no difference: {rules} rules, {defs} non-empty alias tables, {customisers} \
         Defaults lines, {errors} diagnostics, {requests} requests, {panics} panicking (on both \
         sides)",
        texts.len(),
    )
}

fn report(what: &str, summary: &str) {
    writeln!(std::io::stdout(), "analysis equivalence, {what}: {summary}").unwrap();
}

const SUDOERS: &str = "/etc/sudoers";

#[test]
fn unit_test_texts() {
    let texts = corpus::unit_test_texts();
    assert!(texts.len() > 500, "only {} texts harvested", texts.len());
    report("unit test texts", &check_all(Path::new(SUDOERS), &texts));
}

#[test]
fn generated_corpus() {
    let (generated, mutated) = corpus::generated(corpus::SEED, 8_000, 16_000);
    report("generated", &check_all(Path::new(SUDOERS), &generated));
    report("mutated", &check_all(Path::new(SUDOERS), &mutated));
}

/// Texts with `Defaults` of every scope, aliases that the scopes use, ignored tags and
/// unsupported specifiers, so that every request above has customisers that match and that
/// do not.
#[test]
fn scoped_defaults() {
    let texts = [
        "Defaults env_keep += \"G\"\nDefaults@server passwd_tries=7\nDefaults@SRV_1 !use_pty\n\
         Defaults:alice env_keep -= PATH\nDefaults:%wheel rootpw\nDefaults:!bob timestamp_timeout=1\n\
         Defaults>root secure_path=\"/r\"\nDefaults>ALL,!root noexec\nDefaults!/bin/ls umask=077\n\
         Defaults!/usr/bin/su, !/bin/ls insults\nDefaults!list passwd_timeout=2.5\nDefaults!CMDS setenv\n\
         Cmnd_Alias CMDS = /bin/echo, !/bin/ls\nHost_Alias HOSTS = server.example.com, 1.2.3.4\n\
         Defaults@HOSTS lecture=always\nUser_Alias ADMINS = alice, %:nonunix\nDefaults:ADMINS umask_override\n\
         Runas_Alias R = alice, %grp\nDefaults>R targetpw\n\
         ALL ALL = (ALL:ALL) LOG_INPUT: MAIL: /bin/ls, NOMAIL: FOLLOW: SETENV: ALL\n\
         alice, %wheel ALL = (root) NOPASSWD: CWD=/tmp /bin/ls, (alice) /usr/bin/su, list\n\
         bob HOSTS = (ALL) CMDS, NOEXEC: /bin/echo\nroot ALL = ALL\n",
        "Defaults:%:nonunix use_pty\nDefaults>%:nonunix !use_pty\nDefaults>%grp rootpw\n\
         alice ALL = ALL\n",
        "Defaults!/bin/echo a b env_keep = \"X\"\nDefaults!/bin/echo env_keep += \"Y\"\n\
         Defaults!sudoedit setenv\nalice ALL = ALL\n",
    ];
    let texts: Vec<String> = texts.iter().map(|t| t.to_string()).collect();
    report("scoped defaults", &check_all(Path::new(SUDOERS), &texts));
}

/// Include directives against a directory tree: `@include` with absolute and relative paths
/// (relative to the including file), `@includedir` (sorted, `~` and `.` names skipped, a
/// directory entry that is itself a directory), a missing file and a missing directory, `%h`,
/// diagnostics inside included files, and the include limit (counted over the whole tree).
#[test]
fn include_tree() {
    let tree = Tree::new(
        "tree",
        &[
            (
                "sudoers",
                Some(
                    "Defaults env_keep += \"MAIN\"\nalice ALL = NOPASSWD: /bin/ls\n\
                     @include sub/a\n@include $ROOT/sub/b\n#include sub/b\n@includedir dir\n\
                     @includedir nodir\n@includedir dir/%h\n@include missing\n@include sub\n\
                     User_Alias U = alice, B\nU ALL = (root) /bin/echo\n",
                ),
            ),
            ("sub/a", Some("Host_Alias H = server\n@include c\nbob H = ALL\nDefaults@H !use_pty\n")),
            (
                "sub/b",
                Some("User_Alias B = bob\nDefaults:B passwd_tries=9\nalice ALL = INTERCEPT /x\n"),
            ),
            (
                "sub/c",
                Some(
                    "Defaults:bob !use_pty\nCmnd_Alias C = /bin/true\nalice ALL = (root) C\n\
                     this is junk\nDefaults!C setenv\n",
                ),
            ),
            ("dir/10", Some("alice ALL = /bin/ten\n@include ../sub/c\n")),
            ("dir/02", Some("Host_Alias H = localhost\n")),
            ("dir/x~", Some("alice ALL = /bin/tilde\n")),
            ("dir/y.conf", Some("alice ALL = /bin/dot\n")),
            ("dir/zz", None),
            ("loop", Some("Defaults env_keep += \"LOOP\"\n@include loop\n")),
            ("loopdir/self", Some("bob ALL = /bin/self\n@includedir .\n")),
            ("wide", Some(&"@include sub/b\n".repeat(140))),
        ],
        true,
    );
    let texts = vec![
        tree.text("sudoers"),
        tree.text("loop"),
        tree.text("loopdir/self"),
        tree.text("wide"),
        "@include sub/a\n@includedir dir\n@include loop\n@include sub/c\n".to_string(),
    ];
    report("include tree", &check_all(&tree.path("sudoers"), &texts));
    report("include tree (as loop)", &check_all(&tree.path("loop"), &texts[1..2]));
    report(
        "include tree (as loopdir/self)",
        &check_all(&tree.path("loopdir/self"), &texts[2..3]),
    );

    // the include limit is reached: the 129th file is refused, and the count covers the tree
    let (sudoers, errors) = analyze_text(&tree.path("loop"), &char_stream::chars_of(&texts[1]));
    let limit: Vec<&Error> = errors
        .iter()
        .filter(|e| e.message.starts_with("include file limit reached"))
        .collect();
    assert_eq!(limit.len(), 1);
    assert_eq!(sudoers.customisers.non_cmnd.len(), 1 + usize::from(INCLUDE_LIMIT));
    // files of `@includedir` are sorted and filtered; diagnostics name the included file
    let (sudoers, errors) = analyze_text(&tree.path("sudoers"), &char_stream::chars_of(&texts[0]));
    let sources: Vec<String> = errors
        .iter()
        .map(|e| format!("{:?} {}", e.source, e.message))
        .collect();
    assert!(sources.iter().any(|s| s.contains("sub/c") && s.contains("expecting")), "{sources:#?}");
    assert!(sources.iter().any(|s| s.contains("nodir")), "{sources:#?}");
    assert!(sources.iter().any(|s| s.contains("percent escape %h")), "{sources:#?}");
    assert!(sources.iter().any(|s| s.contains("cannot open sudoers file") && s.contains("missing")));
    assert!(!format!("{:?}", sudoers.rules.iter().map(rule).collect::<Vec<_>>()).contains("tilde"));
}

/// The same tree opened with the ownership checks of `audit` (the files are not owned by root),
/// and include paths without a parent directory (a panic on both sides).
#[test]
fn include_tree_audited() {
    let tree = Tree::new(
        "audited",
        &[
            ("sudoers", Some("@include sub/a\n@includedir dir\n@include missing\n")),
            ("sub/a", Some("alice ALL = ALL\n")),
            ("dir/f", Some("bob ALL = ALL\n")),
        ],
        false,
    );
    let texts = vec![tree.text("sudoers")];
    report("audited include tree", &check_all(&tree.path("sudoers"), &texts));
    let texts = vec!["@include x\n".to_string(), "@includedir x\n".to_string(), "alice ALL = ALL\n".to_string()];
    report("include from \"\"", &check_all(Path::new(""), &texts));
    report("include from \"/\"", &check_all(Path::new("/"), &texts));
    assert!(run(true, Path::new(""), "@include x\n").is_err());
}

/// An item list without include items never reaches the include oracle: the live analysis of
/// such a text from a path without a parent directory (where resolving an include panics)
/// succeeds.
#[test]
fn no_oracle_without_includes() {
    let text = "Defaults env_keep += \"X\"\nalice ALL = (root) /bin/ls\nUser_Alias A = bob\n\
                Defaults!/bin/ls !use_pty\njunk junk\n";
    let (sudoers, errors) = analyze_text(Path::new(""), &char_stream::chars_of(&text.to_string()));
    assert_eq!(sudoers.rules.len(), 1);
    assert_eq!(errors.len(), 1);
}
