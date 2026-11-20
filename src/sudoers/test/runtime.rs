//! Runtime checks of the real code on the file system and on constructs sudo-rs rejects:
//!
//! * command paths are compared after canonicalisation on both sides: the patterns of the
//!   policy when `Sudoers::read` parses them (`SimpleCommand::construct`), the requested
//!   command when the command line is resolved (`CommandAndArguments::build_from_args`). Both
//!   use `resolve::canonicalize`, which resolves the directories leading up to the file but not
//!   the file itself, and only for paths that exist;
//! * the tags `NOTBEFORE=`, `NOTAFTER=`, `TIMEOUT=`, `CHROOT=`, `INTERCEPT:`, `ROLE=`, `TYPE=`
//!   and digest specifications (`sha224:` …) are parse errors that drop the whole line, so a
//!   rule that uses them grants nothing.

use std::ffi::OsString;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};

use super::super::*;
use super::Named;
use crate::common::command::CommandAndArguments;

/// A scratch directory with `real/x` (a file), `real/y` (a symlink to `x`) and `lnk` (a
/// symlink to `real`); removed on drop.
struct Tree(PathBuf);

impl Tree {
    fn new(tag: &str) -> Tree {
        let base = std::env::temp_dir()
            .canonicalize()
            .unwrap()
            .join(format!("sudo-rs-runtime-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&base);
        std::fs::create_dir_all(base.join("real")).unwrap();
        std::fs::write(base.join("real/x"), "").unwrap();
        symlink("x", base.join("real/y")).unwrap();
        symlink(base.join("real"), base.join("lnk")).unwrap();
        Tree(base)
    }

    /// `self.0` followed by `rest` (which starts with a `/`), as text.
    fn path(&self, rest: &str) -> String {
        format!("{}{rest}", self.0.display())
    }
}

impl Drop for Tree {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Is root, invoked by `user`, allowed to run `command` (resolved as sudo resolves it) under
/// the policy `line`? Also returns the diagnostics of the parse.
fn allowed(line: &str, command: &str) -> (bool, Vec<String>) {
    let (mut sudoers, errors) =
        Sudoers::read(format!("{line}\n").as_bytes(), "/etc/sudoers").unwrap();
    let cmd = CommandAndArguments::build_from_args(None, vec![OsString::from(command)], "/bin");
    let judgement = sudoers.check(
        &Named("user"),
        &system::Hostname::fake("server"),
        Request {
            user: &Named("root"),
            group: &Named("root"),
            command: &cmd.command,
            arguments: &cmd.arguments,
        },
    );
    let messages = errors.into_iter().map(|e| e.message).collect();
    (judgement.flags.is_some(), messages)
}

#[test]
fn command_path_spellings_are_canonicalised() {
    let t = Tree::new("spell");
    let canonical = t.path("/real/x");
    let spellings = [
        t.path("/real/x"),
        t.path("/real/../real/x"),
        t.path("/real/./x"),
        t.path("//real/x"),
        t.path("/lnk/x"),
        t.path("/lnk/../real/x"),
        format!("/{}", t.path("/real/x")),
    ];
    for policy in &spellings {
        for request in &spellings {
            let (ok, errors) = allowed(&format!("user ALL = {policy}"), request);
            assert!(errors.is_empty(), "{policy}: {errors:?}");
            assert!(ok, "policy {policy} should allow {request} (both are {canonical})");
        }
    }
    // a file of another name is another command, also through `..`
    let (ok, _) = allowed(&format!("user ALL = {canonical}"), &t.path("/real/../lnk/z"));
    assert!(!ok);
}

#[test]
fn command_symlink_itself_is_not_followed() {
    // `canonicalize` resolves the directories, not the file: `real/y -> x` is a command of
    // its own (on purpose: multi-call binaries such as busybox)
    let t = Tree::new("link");
    let (ok, _) = allowed(&format!("user ALL = {}", t.path("/real/x")), &t.path("/real/y"));
    assert!(!ok);
    let (ok, _) = allowed(&format!("user ALL = {}", t.path("/real/y")), &t.path("/lnk/y"));
    assert!(ok);
    let (ok, _) = allowed(&format!("user ALL = {}", t.path("/real/y")), &t.path("/real/x"));
    assert!(!ok);
}

#[test]
fn nonexistent_command_paths_are_compared_as_text() {
    // neither side can be canonicalised, so `..` is not removed and the glob pattern is
    // compared with the path as given
    let t = Tree::new("none");
    let (ok, _) = allowed(
        &format!("user ALL = {}", t.path("/real/../real/none")),
        &t.path("/real/none"),
    );
    assert!(!ok);
    let (ok, _) = allowed(
        &format!("user ALL = {}", t.path("/real/none")),
        &t.path("/real/none"),
    );
    assert!(ok);
    assert!(!Path::new(&t.path("/real/none")).exists());
}

#[test]
fn unsupported_tags_are_rejected_at_parse() {
    for (tag, message) in [
        ("NOTBEFORE=20250101000000Z", "NOTBEFORE is not supported by sudo-rs"),
        ("NOTAFTER=20990101000000Z", "NOTAFTER is not supported by sudo-rs"),
        ("TIMEOUT=10", "TIMEOUT is not supported by sudo-rs"),
        ("CHROOT=/", "CHROOT is not supported by sudo-rs"),
        ("INTERCEPT:", "INTERCEPT is not supported by sudo-rs"),
        ("ROLE=unconfined_r", "SELinux role based access control"),
        ("TYPE=unconfined_t", "SELinux role based access control"),
    ] {
        for line in [
            format!("user ALL = (root) {tag} /usr/bin/true"),
            format!("user ALL = (root) NOPASSWD: {tag} /usr/bin/true"),
            format!("user ALL = /usr/bin/false, {tag} /usr/bin/true"),
        ] {
            let (ok, errors) = allowed(&line, "/usr/bin/true");
            assert!(!ok, "{line}");
            assert!(
                errors.iter().any(|e| e.contains(message)),
                "{line}: {errors:?}"
            );
            // the whole line is dropped, not only the entry with the tag
            let (ok, _) = allowed(&line, "/usr/bin/false");
            assert!(!ok, "{line}");
        }
    }
}

#[test]
fn digests_are_rejected_at_parse() {
    for digest in ["sha224", "sha256", "sha384", "sha512"] {
        for line in [
            format!("user ALL = {digest}:0123abcd /usr/bin/true"),
            format!("user ALL = (root) {digest}:0123abcd /usr/bin/true, /usr/bin/false"),
        ] {
            let (ok, errors) = allowed(&line, "/usr/bin/true");
            assert!(!ok, "{line}");
            assert!(
                errors.iter().any(|e| e.contains("digest")),
                "{line}: {errors:?}"
            );
            let (ok, _) = allowed(&line, "/usr/bin/false");
            assert!(!ok, "{line}");
        }
        // in a Cmnd_Alias the definition is dropped and the alias matches nothing
        let policy = format!("Cmnd_Alias C = {digest}:0123abcd /usr/bin/true\nuser ALL = C");
        let (ok, errors) = allowed(&policy, "/usr/bin/true");
        assert!(!ok, "{policy}");
        assert!(errors.iter().any(|e| e.contains("digest")), "{errors:?}");
    }
}
