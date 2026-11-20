//! Kani bounded proofs for shell-mode escaping (`escaped`) and for the arguments that
//! `CommandAndArguments::build_from_args` hands to the policy. Built only under `cfg(kani)`.
//!
//! Every harness fixes the number of arguments and the length of each argument; the bytes are
//! arbitrary (all 256 values). Bounds are stated per harness; see proofs/kani/README.md.
// Replacement functions are referenced only from `#[kani::stub]` attributes.
#![allow(dead_code)]

use std::ffi::OsString;
use std::io;
use std::os::unix::ffi::OsStringExt;
use std::path::{Path, PathBuf};

use super::{CommandAndArguments, escaped};

fn os(bytes: &[u8]) -> OsString {
    OsString::from_vec(bytes.to_vec())
}

/// An argument of exactly `N` arbitrary bytes (kept on the stack for the specification).
fn bytes<const N: usize>() -> [u8; N] {
    kani::any()
}

fn arg<const N: usize>() -> OsString {
    os(&bytes::<N>())
}

/// Bytes `escaped` leaves alone, written out by hand: ASCII letters, digits, `_`, `-`, `$`.
fn kept(c: u8) -> bool {
    matches!(c, b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'-' | b'$')
}

/// The specification of `escaped`: walk `out` and check that it is exactly the arguments,
/// each byte kept or prefixed with a backslash, separated by single spaces.
fn is_escaping_of(args: &[&[u8]], out: &[u8]) -> bool {
    let mut j = 0;
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            if out.get(j) != Some(&b' ') {
                return false;
            }
            j += 1;
        }
        for &c in arg.iter() {
            if !kept(c) {
                if out.get(j) != Some(&b'\\') {
                    return false;
                }
                j += 1;
            }
            if out.get(j) != Some(&c) {
                return false;
            }
            j += 1;
        }
    }
    j == out.len()
}

fn check_exact(args: &[&[u8]]) {
    let out = escaped(args.iter().map(|a| os(a)).collect());
    assert!(is_escaping_of(args, out.as_encoded_bytes()));
}

/// A1: zero arguments escape to the empty string; one empty argument too.
#[kani::proof]
fn escaped_no_args() {
    assert!(escaped(Vec::new()).is_empty());
    assert!(escaped(vec![OsString::new()]).is_empty());
}

/// A2: one argument of 1 arbitrary byte, and one of 2 arbitrary bytes.
#[kani::proof]
#[kani::unwind(4)]
fn escaped_exact_1_arg_1_and_2_bytes() {
    check_exact(&[&bytes::<1>()[..]]);
    check_exact(&[&bytes::<2>()[..]]);
}

/// A3: one argument of 3 arbitrary bytes.
#[kani::proof]
#[kani::unwind(5)]
fn escaped_exact_1_arg_3_bytes() {
    check_exact(&[&bytes::<3>()[..]]);
}

/// A3b: one argument of 4 arbitrary bytes.
#[kani::proof]
#[kani::unwind(6)]
fn escaped_exact_1_arg_4_bytes() {
    check_exact(&[&bytes::<4>()[..]]);
}

/// A3c: one argument of 5 arbitrary bytes.
#[kani::proof]
#[kani::unwind(7)]
fn escaped_exact_1_arg_5_bytes() {
    check_exact(&[&bytes::<5>()[..]]);
}

/// A4: two arguments of 2 arbitrary bytes each.
#[kani::proof]
#[kani::unwind(4)]
fn escaped_exact_2_args_2_bytes() {
    check_exact(&[&bytes::<2>()[..], &bytes::<2>()[..]]);
}

/// A5: two arguments, one of them empty: lengths (0, 2) and (2, 0).
#[kani::proof]
#[kani::unwind(4)]
fn escaped_exact_2_args_with_empty() {
    check_exact(&[&bytes::<0>()[..], &bytes::<2>()[..]]);
    check_exact(&[&bytes::<2>()[..], &bytes::<0>()[..]]);
}

fn check_injective(a: &[&[u8]], b: &[&[u8]]) {
    let ea = escaped(a.iter().map(|x| os(x)).collect());
    let eb = escaped(b.iter().map(|x| os(x)).collect());
    if ea == eb {
        assert!(a == b);
    }
}

/// B1: one argument of 2 bytes against two arguments of 1 byte each (the `"a b"` against
/// `"a", "b"` shape): the escaped strings always differ.
#[kani::proof]
#[kani::unwind(4)]
fn escaped_injective_1x2_vs_2x1() {
    check_injective(
        &[&bytes::<2>()[..]],
        &[&bytes::<1>()[..], &bytes::<1>()[..]],
    );
}

/// B1b: one argument of 3 bytes against two arguments of 1 byte each: `"a b"` (one argument
/// whose middle byte may be a space) never escapes to the same string as `"a", "b"`.
#[kani::proof]
#[kani::unwind(5)]
fn escaped_injective_1x3_vs_2x1() {
    check_injective(
        &[&bytes::<3>()[..]],
        &[&bytes::<1>()[..], &bytes::<1>()[..]],
    );
}

/// B1c: as B1b with the middle byte of the 3-byte argument fixed to a space (first and last
/// byte arbitrary): the smaller instance of the same question.
#[kani::proof]
#[kani::unwind(5)]
fn escaped_injective_1x3_space_vs_2x1() {
    let mut a = bytes::<3>();
    a[1] = b' ';
    check_injective(&[&a[..]], &[&bytes::<1>()[..], &bytes::<1>()[..]]);
}

/// B2: two single arguments of 2 bytes: equal escaped strings imply equal arguments.
#[kani::proof]
#[kani::unwind(5)]
fn escaped_injective_1x2_vs_1x2() {
    check_injective(&[&bytes::<2>()[..]], &[&bytes::<2>()[..]]);
}

/// B3: one argument of 1 byte against one argument of 2 bytes, and 2 bytes against two
/// arguments of lengths (1, 0) and (0, 1): the separator space is never confused with an
/// escaped space or a backslash inside an argument.
#[kani::proof]
#[kani::unwind(4)]
fn escaped_injective_mixed_lengths() {
    check_injective(&[&bytes::<1>()[..]], &[&bytes::<2>()[..]]);
    check_injective(
        &[&bytes::<2>()[..]],
        &[&bytes::<1>()[..], &bytes::<0>()[..]],
    );
    check_injective(
        &[&bytes::<2>()[..]],
        &[&bytes::<0>()[..], &bytes::<1>()[..]],
    );
}

/// File-system replacement for `canonicalize`: any outcome the real function could have
/// (the path unchanged, another path, or an error). The properties below do not depend on it.
fn canonicalize_any<P: AsRef<Path>>(path: P) -> io::Result<PathBuf> {
    match kani::any::<u8>() {
        0 => Ok(path.as_ref().to_path_buf()),
        1 => Ok(PathBuf::from("/kani/canonical")),
        _ => Err(io::Error::from(io::ErrorKind::NotFound)),
    }
}

/// File-system replacement for the PATH lookup: found somewhere, or not found.
fn resolve_path_any(command: &Path, _path: &str) -> Option<PathBuf> {
    if kani::any() {
        Some(Path::new("/kani/bin").join(command))
    } else {
        None
    }
}

fn shell_arguments(args: Vec<OsString>) -> Vec<OsString> {
    CommandAndArguments::build_from_args(Some("/bin/sh".into()), args, "").arguments
}

/// B5: shell mode (-s/-i): the one collision of `escaped` itself, `[]` against `[""]`, does
/// not reach the policy, because `build_from_args` only adds `-c <escaped>` for a non-empty
/// list. `canonicalize` is replaced by `canonicalize_any`.
#[kani::proof]
#[kani::stub(crate::common::resolve::canonicalize, canonicalize_any)]
fn shell_empty_list_collision_not_policy_visible() {
    assert_eq!(escaped(Vec::new()), escaped(vec![OsString::new()]));
    assert!(shell_arguments(Vec::new()).is_empty());
    assert_eq!(
        shell_arguments(vec![OsString::new()]),
        vec![OsString::from("-c"), OsString::new()]
    );
}

/// B6: shell mode: the policy sees `["-c", escaped(args)]`; for one argument of 2 bytes against
/// two arguments of 1 byte, equal policy arguments imply equal lists. `canonicalize` replaced.
#[kani::proof]
#[kani::unwind(4)]
#[kani::stub(crate::common::resolve::canonicalize, canonicalize_any)]
fn shell_policy_arguments_injective_1x2_vs_2x1() {
    let a = vec![arg::<2>()];
    let b = vec![arg::<1>(), arg::<1>()];
    let pa = shell_arguments(a.clone());
    let pb = shell_arguments(b.clone());
    assert_eq!(pa.len(), 2);
    assert_eq!(pa[0], OsString::from("-c"));
    if pa == pb {
        assert!(a == b);
    }
}

/// B8: direct mode with an empty argv panics (`Vec::remove(0)`). The callers never pass one:
/// run mode requires a command unless -s/-i (shell branch), and list mode checks for an empty
/// argv first. This harness records that precondition.
#[kani::proof]
#[kani::should_panic]
#[kani::stub(crate::common::resolve::canonicalize, canonicalize_any)]
#[kani::stub(crate::common::resolve::resolve_path, resolve_path_any)]
fn direct_empty_argv_panics() {
    let _ = CommandAndArguments::build_from_args(None, Vec::new(), "");
}
