//! The environment policy: which variable of the invoking user's environment, and which
//! `VAR=value` given on the command line, sudo-rs passes on (`env_keep`, `env_check`, the TZ
//! check, `secure_path`, function values).
//!
//! Only decisions on bytes live here; collecting the environment, the PAM environment and the
//! assembly of the target environment (`environment::get_target_environment`) do not.
//! [should_keep] and [keep_inherited] are extraction roots (`Cargo.toml`,
//! `[package.metadata.charon]`); `proofs/lean/SudoRsProofs/EnvFilter.lean` proves them equal to
//! `SudoersSpec.EnvFilter.shouldKeep` and `keepInherited`. The code is written in the restricted
//! style of `proofs/parser/RESTYLE.md` (index loops ending through a flag, no closures or
//! iterator adapters). The few calls that reach the operating system or `HashSet` iteration go
//! through the thin wrappers [table_iter], [table_next], [path_max] and
//! `crate::system::audit::zoneinfo_path`, which are opaque for Charon and modelled in
//! `proofs/lean/SudoRs/{Types,Funs}External.lean` (rows in `proofs/lean/ASSUMPTIONS.md`).

use std::collections::{HashSet, hash_set};

use crate::sudoers::Restrictions;
use crate::system::{PATH_MAX, audit::zoneinfo_path};

use super::wildcard_match::wildcard_match;

/// A cursor over the entries of an `env_keep`/`env_check` table. It visits every entry of the
/// set exactly once, in the set's iteration order, and borrows the set (no copy).
///
/// Opaque for Charon: `HashSet` iteration has no Aeneas model. `TypesExternal.lean` models the
/// cursor as the list of the entries not visited yet.
struct TableIter<'a> {
    entries: hash_set::Iter<'a, String>,
}

/// The cursor at the first entry of `table`. Opaque for Charon, see [TableIter].
fn table_iter(table: &HashSet<String>) -> TableIter<'_> {
    TableIter {
        entries: table.iter(),
    }
}

/// The bytes of the next entry, or `None` when every entry has been visited. Opaque for
/// Charon, see [TableIter].
fn table_next<'a>(iter: &mut TableIter<'a>) -> Option<&'a [u8]> {
    iter.entries.next().map(|entry| entry.as_bytes())
}

/// `PATH_MAX` as a length. Opaque for Charon: the constant comes from `libc` and depends on the
/// platform.
fn path_max() -> usize {
    PATH_MAX as usize
}

/// `text.starts_with(prefix)`, bytewise.
fn starts_with_bytes(text: &[u8], prefix: &[u8]) -> bool {
    let mut ok = prefix.len() <= text.len();
    let mut i: usize = 0;
    while ok && i < prefix.len() {
        ok = text[i] == prefix[i];
        i += 1;
    }
    ok
}

/// `text == word`, bytewise.
fn equals_bytes(text: &[u8], word: &[u8]) -> bool {
    text.len() == word.len() && starts_with_bytes(text, word)
}

/// The position of the first `=` in `input`, or its length if there is none.
fn find_equals(input: &[u8]) -> usize {
    let mut position = input.len();
    let mut i: usize = 0;
    while i < input.len() && position == input.len() {
        if input[i] == b'=' {
            position = i;
        }
        i += 1;
    }
    position
}

/// Whether `value` contains two consecutive dots.
fn contains_dotdot(value: &[u8]) -> bool {
    let mut found = false;
    let mut i: usize = 1;
    while !found && i < value.len() {
        if value[i - 1] == b'.' && value[i] == b'.' {
            found = true;
        }
        i += 1;
    }
    found
}

/// The byte classes the filter looks for.
#[derive(Clone, Copy)]
enum ByteClass {
    /// Anything but a printable non-space ASCII character (`!` to `~`), i.e. the bytes that are
    /// neither `u8::is_ascii_alphanumeric` nor `u8::is_ascii_punctuation`.
    NotPrintable,
    /// `%` or `/`.
    PercentOrSlash,
}

fn in_class(c: u8, class: ByteClass) -> bool {
    match class {
        ByteClass::NotPrintable => !matches!(c, b'!'..=b'~'),
        ByteClass::PercentOrSlash => c == b'%' || c == b'/',
    }
}

/// Whether some byte of `input` is in `class`.
fn contains_class(input: &[u8], class: ByteClass) -> bool {
    let mut found = false;
    let mut i: usize = 0;
    while !found && i < input.len() {
        if in_class(input[i], class) {
            found = true;
        }
        i += 1;
    }
    found
}

/// The TZ variable is considered unsafe if any of the following are true:
/// It consists of a fully-qualified path name, optionally prefixed with a colon (‘:’), that does not match the location of the zoneinfo directory.
/// It contains a .. path element.
/// It contains white space or non-printable characters.
/// It is longer than the value of PATH_MAX.
///
/// The zoneinfo directory is looked up only for a fully-qualified value. sudo-rs rejects every
/// `..`, not only a `..` path element.
fn is_safe_tz(value: &[u8]) -> bool {
    let check_value = if starts_with_bytes(value, &[b':']) {
        let (_, rest) = value.split_at(1);
        rest
    } else {
        value
    };

    if starts_with_bytes(check_value, &[b'/']) {
        match zoneinfo_path() {
            Some(path_zoneinfo) => {
                let zoneinfo = path_zoneinfo.as_bytes();
                if !starts_with_bytes(check_value, zoneinfo)
                    || check_value.len() <= zoneinfo.len()
                    || check_value[zoneinfo.len()] != b'/'
                {
                    return false;
                }
            }
            None => return false,
        }
    }

    !contains_dotdot(check_value)
        && !contains_class(check_value, ByteClass::NotPrintable)
        && check_value.len() < path_max()
}

/// Whether a variable matches one table entry: an entry `NAME=VALUE` (split at its first `=`)
/// matches the name against `NAME` and the value against `VALUE`; an entry without `=` matches
/// the name only. Both parts may contain `*` wildcards.
fn entry_matches(key: &[u8], value: &[u8], entry: &[u8]) -> bool {
    let separator = find_equals(entry);
    if separator < entry.len() {
        let (key_pattern, rest) = entry.split_at(separator);
        let (_, value_pattern) = rest.split_at(1);
        wildcard_match(key, key_pattern) && wildcard_match(value, value_pattern)
    } else {
        wildcard_match(key, entry)
    }
}

/// Whether a variable matches some entry of `table`. Visits the entries in the set's iteration
/// order and stops at the first match; the result does not depend on that order.
fn in_table(key: &[u8], value: &[u8], table: &HashSet<String>) -> bool {
    let mut entries = table_iter(table);
    let mut found = false;
    let mut more = true;
    while more {
        match table_next(&mut entries) {
            Some(entry) => {
                if entry_matches(key, value, entry) {
                    found = true;
                    more = false;
                }
            }
            None => {
                more = false;
            }
        }
    }
    found
}

/// Whether `key` is `PATH` while `secure_path` (`path`) is set. A `match` on the option passed
/// by value: Aeneas rejects a `matches!` on the field behind `&Restrictions` ("Unreachable").
fn is_secured_path(key: &[u8], path: Option<&str>) -> bool {
    match path {
        Some(_) => equals_bytes(key, &[b'P', b'A', b'T', b'H']),
        None => false,
    }
}

/// Determine whether a specific environment variable should be kept
///
/// In this order: a value starting with `()` is dropped; `PATH` is dropped when `secure_path`
/// is set; `TZ` is kept if it is in `env_keep`, or in `env_check` with a safe value; any other
/// variable in `env_check` is kept iff its value has neither `%` nor `/`; otherwise it is kept
/// iff it is in `env_keep`.
pub(super) fn should_keep(key: &[u8], value: &[u8], cfg: &Restrictions) -> bool {
    if starts_with_bytes(value, &[b'(', b')']) {
        return false;
    }

    if is_secured_path(key, cfg.path) {
        return false;
    }

    if equals_bytes(key, &[b'T', b'Z']) {
        return in_table(key, value, cfg.env_keep)
            || (in_table(key, value, cfg.env_check) && is_safe_tz(value));
    }

    if in_table(key, value, cfg.env_check) {
        return !contains_class(value, ByteClass::PercentOrSlash);
    }

    in_table(key, value, cfg.env_keep)
}

/// The variables a login shell (`sudo -i`) sets for the target user itself.
fn is_login_variable(key: &[u8]) -> bool {
    equals_bytes(key, &[b'H', b'O', b'M', b'E'])
        || equals_bytes(key, &[b'S', b'H', b'E', b'L', b'L'])
        || equals_bytes(key, &[b'U', b'S', b'E', b'R'])
        || equals_bytes(key, &[b'L', b'O', b'G', b'N', b'A', b'M', b'E'])
}

/// Whether a variable of the invoking user's environment is passed on: for a login shell
/// (`login`) never `HOME`, `SHELL`, `USER` or `LOGNAME`; otherwise as [should_keep] decides.
pub(super) fn keep_inherited(key: &[u8], value: &[u8], login: bool, cfg: &Restrictions) -> bool {
    !(login && is_login_variable(key)) && should_keep(key, value, cfg)
}

/// The filter before it was rewritten for extraction (`environment.rs` at `afbada67`); the tests
/// compare both.
#[cfg(test)]
pub(super) mod reference {
    use std::{collections::HashSet, ffi::OsStr, os::unix::prelude::OsStrExt};

    use super::super::wildcard_match::wildcard_match;
    use crate::sudoers::Restrictions;
    use crate::system::{PATH_MAX, audit::zoneinfo_path};

    fn contains_subsequence(haystack: &[u8], needle: &[u8]) -> bool {
        haystack
            .windows(needle.len())
            .any(|window| window == needle)
    }

    fn is_printable(input: &[u8]) -> bool {
        input
            .iter()
            .all(|c| c.is_ascii_alphanumeric() || c.is_ascii_punctuation())
    }

    pub(in super::super) fn is_safe_tz(value: &[u8]) -> bool {
        let check_value = if value.starts_with(b":") {
            &value[1..]
        } else {
            value
        };

        if check_value.starts_with(b"/") {
            if let Some(path_zoneinfo) = zoneinfo_path() {
                if !check_value.starts_with(path_zoneinfo.as_bytes())
                    || check_value.get(path_zoneinfo.len()) != Some(&b'/')
                {
                    return false;
                }
            } else {
                return false;
            }
        }

        !contains_subsequence(check_value, "..".as_bytes())
            && is_printable(check_value)
            && check_value.len() < PATH_MAX as usize
    }

    fn in_table(needle: (&OsStr, &OsStr), haystack: &HashSet<String>) -> bool {
        haystack.iter().any(|pattern| {
            if let Some((key, value)) = pattern.split_once('=') {
                wildcard_match(needle.0.as_bytes(), key.as_bytes())
                    && wildcard_match(needle.1.as_bytes(), value.as_bytes())
            } else {
                wildcard_match(needle.0.as_bytes(), pattern.as_bytes())
            }
        })
    }

    pub(in super::super) fn should_keep(key: &OsStr, value: &OsStr, cfg: &Restrictions) -> bool {
        if value.as_bytes().starts_with("()".as_bytes()) {
            return false;
        }

        if cfg.path.is_some() && key == "PATH" {
            return false;
        }

        if key == "TZ" {
            return in_table((key, value), cfg.env_keep)
                || (in_table((key, value), cfg.env_check) && is_safe_tz(value.as_bytes()));
        }

        if in_table((key, value), cfg.env_check) {
            return !value.as_bytes().iter().any(|c| *c == b'%' || *c == b'/');
        }

        in_table((key, value), cfg.env_keep)
    }

    pub(in super::super) fn keep_inherited(
        key: &OsStr,
        value: &OsStr,
        login: bool,
        cfg: &Restrictions,
    ) -> bool {
        let login_vars: &[_] = if login {
            &["HOME", "SHELL", "USER", "LOGNAME"].map(OsStr::new)
        } else {
            &[]
        };
        !login_vars.contains(&key) && should_keep(key, value, cfg)
    }
}

#[cfg(test)]
mod tests {
    use super::{
        ByteClass, contains_class, contains_dotdot, entry_matches, equals_bytes, find_equals,
        in_class, is_safe_tz, keep_inherited, reference, should_keep, starts_with_bytes,
    };
    use crate::system::audit::zoneinfo_path;
    use std::{
        collections::HashSet,
        ffi::OsStr,
        os::unix::prelude::OsStrExt,
    };

    fn restrictions<'a>(
        keep: &'a HashSet<String>,
        check: &'a HashSet<String>,
        path: Option<&'a str>,
    ) -> crate::sudoers::Restrictions<'a> {
        crate::sudoers::Restrictions {
            env_keep: keep,
            env_check: check,
            path,
            chdir: crate::sudoers::DirChange::Strict(None),
            trust_environment: false,
            use_pty: true,
            umask: crate::exec::Umask::Preserve,
            #[cfg(feature = "apparmor")]
            apparmor_profile: None,
            noexec: false,
            log: crate::sudoers::Logging::Auth,
        }
    }

    #[test]
    fn byte_helpers() {
        assert!(starts_with_bytes(b"abc", b""));
        assert!(starts_with_bytes(b"abc", b"ab"));
        assert!(starts_with_bytes(b"abc", b"abc"));
        assert!(!starts_with_bytes(b"abc", b"abcd"));
        assert!(!starts_with_bytes(b"abc", b"b"));
        assert!(equals_bytes(b"PATH", b"PATH"));
        assert!(!equals_bytes(b"PATH", b"PAT"));
        assert!(!equals_bytes(b"PATHS", b"PATH"));
        assert_eq!(find_equals(b"A=B=C"), 1);
        assert_eq!(find_equals(b"=x"), 0);
        assert_eq!(find_equals(b"ABC"), 3);
        assert_eq!(find_equals(b""), 0);
        assert!(!contains_dotdot(b""));
        assert!(!contains_dotdot(b"."));
        assert!(contains_dotdot(b".."));
        assert!(contains_dotdot(b"a/b..c"));
        assert!(!contains_dotdot(b"a.b.c"));
    }

    /// `in_class` against the `std` predicates the old code used, on every byte.
    #[test]
    fn byte_classes_all_bytes() {
        for c in 0..=u8::MAX {
            assert_eq!(
                in_class(c, ByteClass::NotPrintable),
                !(c.is_ascii_alphanumeric() || c.is_ascii_punctuation()),
                "{c:#04x}"
            );
            assert_eq!(
                in_class(c, ByteClass::PercentOrSlash),
                c == b'%' || c == b'/',
                "{c:#04x}"
            );
            assert_eq!(contains_class(&[c], ByteClass::NotPrintable), in_class(c, ByteClass::NotPrintable));
        }
    }

    #[test]
    fn entry_matching() {
        assert!(entry_matches(b"FOO", b"x", b"FOO"));
        assert!(entry_matches(b"FOO", b"x", b"F*"));
        assert!(!entry_matches(b"FOO", b"x", b"FOO=y"));
        assert!(entry_matches(b"FOO", b"x", b"FOO=x"));
        assert!(entry_matches(b"FOO", b"a=b", b"FOO=a=b"));
        assert!(entry_matches(b"FOO", b"", b"FOO="));
        assert!(entry_matches(b"", b"x", b"=x"));
        assert!(!entry_matches(b"FOO", b"x", b"=x"));
    }

    /// Every pair of byte strings over a small alphabet that contains the separator, the
    /// wildcard and the bytes the filter singles out.
    fn strings(alphabet: &[u8], max_len: usize) -> Vec<Vec<u8>> {
        let mut all = vec![vec![]];
        let mut last = vec![vec![]];
        for _ in 0..max_len {
            let mut next = Vec::new();
            for s in &last {
                for &c in alphabet {
                    let mut t = s.clone();
                    t.push(c);
                    next.push(t);
                }
            }
            all.extend(next.iter().cloned());
            last = next;
        }
        all
    }

    /// The rewritten filter against the previous implementation, on a grid of names, values and
    /// tables (test evidence on these inputs only).
    #[test]
    fn should_keep_equals_reference() {
        let zoneinfo = zoneinfo_path().unwrap_or("/usr/share/zoneinfo");
        let names: Vec<Vec<u8>> = [
            &b"TZ"[..], b"PATH", b"HOME", b"SHELL", b"USER", b"LOGNAME", b"LANG", b"LC_ALL",
            b"A", b"AB", b"", b"T", b"TZZ", b"PAT",
        ]
        .iter()
        .map(|n| n.to_vec())
        .chain(strings(b"AT*", 2))
        .collect();
        let mut values: Vec<Vec<u8>> = strings(b"a/%.:(", 3);
        for v in [
            &b"()"[..], b"() { :; }", b"Europe/Amsterdam", b"../x", b"a..b", b"a b", b"\x7f",
            b"\xff", b"=", b"a=b",
        ] {
            values.push(v.to_vec());
        }
        for v in ["", ":"] {
            values.push(format!("{v}{zoneinfo}/Europe/London").into_bytes());
            values.push(format!("{v}{zoneinfo}").into_bytes());
            values.push(format!("{v}{zoneinfo}x/a").into_bytes());
            values.push(format!("{v}{zoneinfo}/../a").into_bytes());
        }
        values.push(vec![b'a'; 4095]);
        values.push(vec![b'a'; 4096]);
        let tables: Vec<HashSet<String>> = vec![
            HashSet::new(),
            ["TZ", "PATH", "A"].iter().map(|s| s.to_string()).collect(),
            ["*"].iter().map(|s| s.to_string()).collect(),
            ["T*", "A=a*", "LC_*"].iter().map(|s| s.to_string()).collect(),
            ["TZ=a", "*=*/*", "HOME", "LOGNAME"].iter().map(|s| s.to_string()).collect(),
        ];
        let mut count = 0usize;
        for keep in &tables {
            for check in &tables {
                for path in [None, Some("/bin")] {
                    let cfg = restrictions(keep, check, path);
                    for name in &names {
                        for value in &values {
                            let (k, v) = (OsStr::from_bytes(name), OsStr::from_bytes(value));
                            assert_eq!(
                                should_keep(name, value, &cfg),
                                reference::should_keep(k, v, &cfg),
                                "{name:?} {value:?} {keep:?} {check:?} {path:?}"
                            );
                            for login in [false, true] {
                                assert_eq!(
                                    keep_inherited(name, value, login, &cfg),
                                    reference::keep_inherited(k, v, login, &cfg),
                                );
                            }
                            count += 1;
                        }
                    }
                }
            }
        }
        assert!(count > 100_000, "{count}");
    }

    #[test]
    fn is_safe_tz_equals_reference() {
        let zoneinfo = zoneinfo_path().unwrap_or("/usr/share/zoneinfo");
        let mut values = strings(b"a/.: \x01", 4);
        for prefix in ["", ":"] {
            for suffix in ["", "/", "/Europe/London", "x", "x/a", "/../a", "/a..b", "/ a"] {
                values.push(format!("{prefix}{zoneinfo}{suffix}").into_bytes());
            }
        }
        for value in &values {
            assert_eq!(is_safe_tz(value), reference::is_safe_tz(value), "{value:?}");
        }
    }

    // The tests of `environment.rs` at `afbada67`, on bytes.
    #[test]
    fn test_filtering() {
        let mut keep = HashSet::from(["AAP".to_string(), "NOOT".to_string()]);
        let check = HashSet::from(["MIES".to_string(), "TZ".to_string()]);
        let check_should_keep =
            |keep: &HashSet<String>, path: Option<&str>, key: &str, value: &str, expected: bool| {
                assert_eq!(
                    should_keep(key.as_bytes(), value.as_bytes(), &restrictions(keep, &check, path)),
                    expected,
                    "{} should {}",
                    key,
                    if expected { "be kept" } else { "not be kept" }
                );
            };

        check_should_keep(&keep, Some("/bin"), "AAP", "FOO", true);
        check_should_keep(&keep, Some("/bin"), "MIES", "BAR", true);
        check_should_keep(&keep, Some("/bin"), "AAP", "()=foo", false);
        check_should_keep(&keep, Some("/bin"), "TZ", "Europe/Amsterdam", true);
        check_should_keep(&keep, Some("/bin"), "TZ", "../Europe/Berlin", false);
        check_should_keep(&keep, Some("/bin"), "MIES", "FOO/BAR", false);

        keep.insert("PATH".to_string());
        check_should_keep(&keep, Some("/bin"), "PATH", "FOO", false);
        check_should_keep(&keep, None, "PATH", "FOO", true);
    }

    #[allow(clippy::bool_assert_comparison)]
    #[test]
    fn test_tzinfo() {
        let path_zoneinfo = zoneinfo_path().unwrap();
        assert_eq!(is_safe_tz(b"Europe/Amsterdam"), true);
        assert_eq!(
            is_safe_tz(format!("{path_zoneinfo}/Europe/London").as_bytes()),
            true
        );
        assert_eq!(
            is_safe_tz(format!(":{path_zoneinfo}/Europe/Amsterdam").as_bytes()),
            true
        );
        assert_eq!(is_safe_tz(b"/Europe/Amsterdam"), false);
        assert_eq!(is_safe_tz(b"/schaap/Europe/Amsterdam"), false);
        assert_eq!(
            is_safe_tz(format!("{path_zoneinfo}/../Europe/London").as_bytes()),
            false
        );
    }

    /// Hook of `proofs/differential/env/pattern-run.sh`: reads the file named by
    /// `SUDO_ENV_PATTERN_CASES` (lines `ENTRY<TAB>NAME<TAB>VALUE`) and writes `1` or `0` per line,
    /// the result of [entry_matches], to the file named by `SUDO_ENV_PATTERN_OUT`. Without
    /// `SUDO_ENV_PATTERN_CASES` the test does nothing.
    #[test]
    fn env_pattern_cases() {
        let Ok(cases) = std::env::var("SUDO_ENV_PATTERN_CASES") else {
            return;
        };
        let out = std::env::var("SUDO_ENV_PATTERN_OUT")
            .expect("SUDO_ENV_PATTERN_OUT must name the output file");
        let text = std::fs::read(cases).unwrap();
        let mut result = Vec::new();
        for line in text.split(|c| *c == b'\n').filter(|l| !l.is_empty()) {
            let fields: Vec<&[u8]> = line.split(|c| *c == b'\t').collect();
            assert_eq!(fields.len(), 3, "{line:?}");
            let matched = entry_matches(fields[1], fields[2], fields[0]);
            result.extend_from_slice(if matched { b"1\n" } else { b"0\n" });
        }
        std::fs::write(out, result).unwrap();
    }
}
