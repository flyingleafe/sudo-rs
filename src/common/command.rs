use std::{
    ffi::OsString,
    fmt::Display,
    os::unix::ffi::OsStringExt,
    path::{Path, PathBuf},
};

use crate::common::DisplayOsStr;
use crate::system::escape_os_str_lossy;

use super::resolve::{canonicalize, resolve_path};

#[derive(Debug, Default)]
#[cfg_attr(test, derive(PartialEq))]
pub struct CommandAndArguments {
    pub(crate) command: PathBuf,
    pub(crate) arguments: Vec<OsString>,
    pub(crate) resolved: bool,
    pub(crate) arg0: Option<PathBuf>,
}

impl Display for CommandAndArguments {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cmd = escape_os_str_lossy(self.command.as_os_str());
        let args = self
            .arguments
            .iter()
            .map(|a| {
                DisplayOsStr(a)
                    .to_string()
                    .escape_default()
                    .collect::<String>()
            })
            .collect::<Vec<_>>()
            .join(" ");
        write!(f, "{cmd} {args}")
    }
}

// when -i and -s are used, the arguments given to sudo are escaped "except for alphanumerics, underscores, hyphens, and dollar signs."
//
// Written with index loops, without closures or iterator adapters, so that Charon/Aeneas can
// extract it; `proofs/lean/SudoRsProofs/Escape.lean` proves it equal to a specification.
fn escaped(arguments: Vec<OsString>) -> OsString {
    let mut line = Vec::new();
    let mut i = 0;
    while i < arguments.len() {
        if i > 0 {
            line.push(b' ');
        }
        escape_arg_into(arguments[i].as_encoded_bytes(), &mut line);
        i += 1;
    }
    OsString::from_vec(line)
}

/// Bytes that [escaped] passes through without a backslash: ASCII alphanumerics, `_`, `-`, `$`.
fn is_unescaped(c: u8) -> bool {
    matches!(c, b'0'..=b'9' | b'A'..=b'Z' | b'a'..=b'z' | b'_' | b'-' | b'$')
}

/// Appends `arg` to `line`, every byte that is not [is_unescaped] preceded by a backslash.
fn escape_arg_into(arg: &[u8], line: &mut Vec<u8>) {
    let mut i = 0;
    while i < arg.len() {
        let c = arg[i];
        if !is_unescaped(c) {
            line.push(b'\\');
        }
        line.push(c);
        i += 1;
    }
}

/// The implementation of [escaped] before it was rewritten for extraction; the tests compare
/// both.
#[cfg(test)]
fn escaped_reference(arguments: Vec<OsString>) -> OsString {
    arguments
        .into_iter()
        .map(|arg| {
            let mut escaped_arg = Vec::new();
            for c in arg.into_encoded_bytes() {
                match c {
                    b'_' | b'-' | b'$' => escaped_arg.push(c),
                    c if c.is_ascii_alphanumeric() => escaped_arg.push(c),
                    _ => escaped_arg.extend_from_slice(&[b'\\', c]),
                }
            }
            OsString::from_vec(escaped_arg)
        })
        .collect::<Vec<OsString>>()
        .join(std::ffi::OsStr::new(" "))
}

/// Fuzzing entry point for [escaped].
#[cfg(fuzzing)]
pub(crate) fn fuzz_escaped(arguments: Vec<OsString>) -> OsString {
    escaped(arguments)
}

// An unqualified path has exactly one relative component (as normalized by Path).
fn is_qualified(path: impl AsRef<Path>) -> bool {
    path.as_ref().parent() != Some(Path::new(""))
}

/// Replace the path after a successful PATH search or canonicalization. A failed step
/// keeps its input path and clears `resolved`; later steps cannot restore that flag.
fn select_command_path<P>(input: P, replacement: Option<P>, resolved: bool) -> (P, bool) {
    match replacement {
        Some(path) => (path, resolved),
        None => (input, false),
    }
}

impl CommandAndArguments {
    pub fn build_from_args(
        shell: Option<PathBuf>,
        mut arguments: Vec<OsString>,
        path: &str,
    ) -> Self {
        let mut resolved = true;
        let mut command;
        let mut arg0 = None;
        if let Some(chosen_shell) = shell {
            command = chosen_shell;
            if !arguments.is_empty() {
                arguments = vec!["-c".into(), escaped(arguments)]
            }
        } else {
            command = arguments.first().map(|s| s.into()).unwrap_or_default();
            arguments.remove(0);

            // remember the original binary name before resolving symlinks; this is not
            // to be used except for setting the `arg0`
            arg0 = Some(command.clone());

            // resolve the command, remembering errors (but not propagating them)
            if !is_qualified(&command) {
                let found = resolve_path(&command, path);
                (command, resolved) = select_command_path(command, found, resolved);
            }
        }

        // Canonicalize the directories and check existence, retaining the final path component.
        // Failure should not stop the pipeline.
        let canonical = canonicalize(&command).ok();
        (command, resolved) = select_command_path(command, canonical, resolved);

        CommandAndArguments {
            command,
            arguments,
            resolved,
            arg0,
        }
    }
}

#[cfg(kani)]
mod kani_proofs;

#[cfg(test)]
mod test {
    use std::ffi::OsString;
    use std::os::unix::ffi::{OsStrExt, OsStringExt};

    use super::{CommandAndArguments, escaped, escaped_reference};

    fn os(bytes: &[u8]) -> OsString {
        OsString::from_vec(bytes.to_vec())
    }

    fn escaped_bytes(args: &[&[u8]]) -> Vec<u8> {
        escaped(args.iter().map(|a| os(a)).collect()).into_vec()
    }

    #[test]
    fn escaped_argument_lists() {
        assert_eq!(escaped_bytes(&[]), b"");
        assert_eq!(escaped_bytes(&[b""]), b"");
        assert_eq!(escaped_bytes(&[b"", b""]), b" ");
        assert_eq!(escaped_bytes(&[b"a", b"", b"b"]), b"a  b");
        assert_eq!(escaped_bytes(&[b"a", b"", b"", b"b"]), b"a   b");
        assert_eq!(escaped_bytes(&[b"", b"x"]), b" x");
        assert_eq!(escaped_bytes(&[b"x", b""]), b"x ");
        assert_eq!(escaped_bytes(&[b"ls", b"-l", b"$HOME"]), b"ls -l $HOME");
        assert_eq!(
            escaped_bytes(&[b"a b", b"c\\d", b"e\nf"]),
            b"a\\ b c\\\\d e\\\nf"
        );
    }

    #[test]
    fn escaped_byte_classes() {
        let kept: &[u8] = b"_-$09azAZ5mQ";
        let quoted: &[u8] = &[
            b' ', b'\\', b'\t', b'\n', b'\'', b'"', b'`', b';', b'&', b'|', b'*', b'?', b'#',
            b'!', b'(', b')', b'<', b'>', b'=', b'~', b'%', b'^', b'+', b'.', b',',
            // neighbours of the kept ranges
            b'/', b':', b'@', b'[', b'`', b'{',
            // control, non-ASCII and invalid UTF-8 bytes
            0x00, 0x01, 0x1f, 0x7f, 0x80, 0xa0, 0xc3, 0xfe, 0xff,
        ];
        for &c in kept {
            assert_eq!(escaped_bytes(&[&[c]]), [c], "byte {c:#04x}");
        }
        for &c in quoted {
            assert_eq!(escaped_bytes(&[&[c]]), [b'\\', c], "byte {c:#04x}");
        }
        let mut n_kept = 0;
        for c in 0..=u8::MAX {
            let out = escaped_bytes(&[&[c]]);
            if out == [c] {
                n_kept += 1;
            } else {
                assert_eq!(out, [b'\\', c], "byte {c:#04x}");
            }
        }
        // 10 digits, 26 + 26 letters, `_`, `-`, `$`
        assert_eq!(n_kept, 65);
    }

    #[test]
    fn escaped_matches_reference() {
        let same = |args: Vec<OsString>| {
            assert_eq!(escaped(args.clone()), escaped_reference(args.clone()), "{args:?}");
        };
        for a in 0..=u8::MAX {
            same(vec![os(&[a])]);
            for b in 0..=u8::MAX {
                same(vec![os(&[a, b])]);
            }
        }
        same(vec![]);
        same(vec![os(b"")]);
        same(vec![os(b""), os(b"")]);
        same(vec![os(b"a"), os(b""), os(b"b")]);
        same(vec![os(b"echo"), os(b"a b"), os(b"$x"), os(b"\\"), os(b"\xff\x00")]);
        same(vec![os(b"-c"), os(b"rm -rf /"), os(b""), os(b"\"q\"")]);
        let all: Vec<u8> = (0..=u8::MAX).collect();
        same(vec![os(&all), os(&all[..128]), os(&all[128..])]);
        same(all.iter().map(|&c| os(&[c])).collect());
        same(vec![std::ffi::OsStr::from_bytes(b"x y").to_os_string()]);
    }

    #[test]
    fn test_escaped() {
        let test = |src: &[&str], target: &str| {
            assert_eq!(&escaped(src.iter().map(OsString::from).collect()), target);
        };
        test(&["a", "b", "c"], "a b c");
        test(&["a", "b c"], "a b\\ c");
        test(&["a", "b-c"], "a b-c");
        test(&["a", "b#c"], "a b\\#c");
        test(&["1 2 3"], "1\\ 2\\ 3");
        test(&["! @ $"], "\\!\\ \\@\\ $");
    }

    #[test]
    fn test_build_command_and_args() {
        assert_eq!(
            CommandAndArguments::build_from_args(
                None,
                vec!["/usr/bin/fmt".into(), "hello".into()],
                "/bin"
            ),
            CommandAndArguments {
                command: "/usr/bin/fmt".into(),
                arguments: vec!["hello".into()],
                resolved: true,
                arg0: Some("/usr/bin/fmt".into()),
            }
        );

        assert_eq!(
            CommandAndArguments::build_from_args(
                None,
                vec!["fmt".into(), "hello".into()],
                "/tmp:/usr/bin:/bin"
            ),
            CommandAndArguments {
                command: "/usr/bin/fmt".into(),
                arguments: vec!["hello".into()],
                resolved: true,
                arg0: Some("fmt".into()),
            }
        );

        assert_eq!(
            CommandAndArguments::build_from_args(
                None,
                vec!["thisdoesnotexist".into(), "hello".into()],
                ""
            ),
            CommandAndArguments {
                command: "thisdoesnotexist".into(),
                arguments: vec!["hello".into()],
                resolved: false,
                arg0: Some("thisdoesnotexist".into()),
            }
        );

        assert_eq!(
            CommandAndArguments::build_from_args(
                Some("shell".into()),
                vec!["ls".into(), "hello".into()],
                "/bin"
            ),
            CommandAndArguments {
                command: "shell".into(),
                arguments: vec!["-c".into(), "ls hello".into()],
                resolved: false,
                arg0: None,
            }
        );
    }

    #[test]
    fn direct_arguments_keep_their_boundaries_and_bytes() {
        // Construct the command; do not execute it or change credentials.
        let executable = std::env::current_exe().unwrap();
        let tail = vec![os(b"a b"), os(b""), os(b"c\\d"), os(b"\xff")];
        let argv = std::iter::once(executable.clone().into_os_string())
            .chain(tail.iter().cloned())
            .collect();
        let command = CommandAndArguments::build_from_args(None, argv, "");
        assert!(command.resolved);
        assert_eq!(command.arg0, Some(executable));
        assert_eq!(command.arguments, tail);
    }

    #[test]
    fn qualified_paths() {
        use super::is_qualified;
        assert!(is_qualified("foo/bar"));
        assert!(is_qualified("a/b/bar"));
        assert!(is_qualified("a/b//bar"));
        assert!(is_qualified("/bar"));
        assert!(is_qualified("/bar/"));
        assert!(is_qualified("/bar/foo/"));
        assert!(is_qualified("/"));
        assert!(is_qualified("")); // don't try to resolve ""
        assert!(!is_qualified("bar"));
    }
}
