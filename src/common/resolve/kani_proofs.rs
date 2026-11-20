//! Kani bounded proofs for `NameOrId::parse` (the `-u`/`-g` argument: `#<id>` or a name).
//! Built only under `cfg(kani)`. Bounds are stated per harness; see proofs/kani/README.md.
//!
//! Inputs have a fixed byte length per check (several lengths per harness, each checked
//! separately); the bytes are arbitrary apart from what a `SudoString` must be (valid UTF-8,
//! no NUL). The `String` handed to `SudoString::new` is created with spare capacity; capacity
//! has no influence on the result.

use super::NameOrId;
use crate::common::SudoString;
use crate::system::interface::{GroupId, UserId};

/// `prefix` followed by exactly `N` arbitrary bytes, assumed to form valid UTF-8 without NUL.
fn input<const N: usize>(prefix: &str) -> SudoString {
    let raw: [u8; N] = kani::any();
    kani::assume(!raw.contains(&0));
    let Ok(rest) = std::str::from_utf8(&raw) else {
        kani::assume(false);
        unreachable!()
    };
    let mut s = String::with_capacity(32);
    s.push_str(prefix);
    s.push_str(rest);
    SudoString::new(s).unwrap()
}

/// What Rust's `u32: FromStr` accepts, written out independently: an optional leading `+`
/// (a leading `-` is a digit error for unsigned types), then one or more ASCII digits
/// (leading zeros allowed) whose value is at most `u32::MAX`.
fn spec_u32(s: &[u8]) -> Option<u32> {
    let digits = match s {
        [b'+', rest @ ..] => rest,
        _ => s,
    };
    if digits.is_empty() {
        return None;
    }
    let mut value: u64 = 0;
    for &d in digits {
        if !d.is_ascii_digit() {
            return None;
        }
        value = value * 10 + u64::from(d - b'0');
        if value > u64::from(u32::MAX) {
            return None;
        }
    }
    Some(value as u32)
}

/// `parse` on `#...` agrees with `spec_u32` on the part after `#`.
fn check_hash(input: &SudoString) {
    let expected = spec_u32(&input.as_bytes()[1..]);
    match NameOrId::<u32>::parse(input) {
        None => {
            assert!(expected.is_none());
        }
        Some(NameOrId::Id(v)) => {
            assert_eq!(Some(v), expected);
        }
        Some(NameOrId::Name(_)) => panic!("`#` input parsed as a name"),
    }
}

/// C1: `#` followed by 0, 1, 2, 3 or 4 arbitrary bytes (valid UTF-8, no NUL): `Id(v)` exactly
/// when the rest is an optional `+` and decimal digits of value `v <= u32::MAX`, else `None`.
#[kani::proof]
#[kani::unwind(6)]
fn name_or_id_hash_any_0_to_4_bytes() {
    check_hash(&input::<0>("#"));
    check_hash(&input::<1>("#"));
    check_hash(&input::<2>("#"));
    check_hash(&input::<3>("#"));
    check_hash(&input::<4>("#"));
}

/// `#` followed by exactly `N` bytes from `0-9 + -`.
fn digits_input<const N: usize>() -> SudoString {
    let raw: [u8; N] = kani::any();
    for b in raw {
        kani::assume(b.is_ascii_digit() || b == b'+' || b == b'-');
    }
    let mut s = String::with_capacity(32);
    s.push('#');
    s.push_str(std::str::from_utf8(&raw).unwrap());
    SudoString::new(s).unwrap()
}

/// C2: `#` and exactly 10 bytes over `0-9 + -`: every 10-digit value (overflowing ones included)
/// and every 9-digit value with a sign.
#[kani::proof]
#[kani::unwind(12)]
fn name_or_id_hash_10_digit_bytes() {
    check_hash(&digits_input::<10>());
}

/// C3: `#` and exactly 11 bytes over `0-9 + -`: 11-digit values (all overflow unless leading
/// zeros) and 10-digit values with a sign, i.e. the u32 overflow boundary with `+`.
#[kani::proof]
#[kani::unwind(13)]
fn name_or_id_hash_11_digit_bytes() {
    check_hash(&digits_input::<11>());
}

/// C4: every spelling of zero with 1 to 16 digits, with or without `+`, parses to `Id(0)`, and
/// the documented edge cases, concretely.
#[kani::proof]
#[kani::unwind(19)]
fn name_or_id_zero_spellings_and_edge_cases() {
    let p = |s: &str| match NameOrId::<u32>::parse(&SudoString::new(s.to_string()).unwrap()) {
        None => None,
        Some(NameOrId::Id(v)) => Some(v),
        Some(NameOrId::Name(_)) => panic!("`#` input parsed as a name"),
    };
    let mut plain = String::from("#");
    let mut signed = String::from("#+");
    for _ in 0..16 {
        plain.push('0');
        signed.push('0');
        assert_eq!(p(&plain), Some(0));
        assert_eq!(p(&signed), Some(0));
    }
    assert_eq!(p(""), None);
    assert_eq!(p("#"), None);
    assert_eq!(p("#+"), None);
    assert_eq!(p("#-"), None);
    assert_eq!(p("#-1"), None);
    assert_eq!(p("#-0"), None);
    assert_eq!(p("#007"), Some(7));
    assert_eq!(p("#4294967295"), Some(u32::MAX));
    assert_eq!(p("#+4294967295"), Some(u32::MAX));
    assert_eq!(p("#4294967296"), None);
    assert_eq!(p("# 1"), None);
    assert_eq!(p("#1 "), None);
}

fn check_non_hash(input: &SudoString) {
    if input.starts_with('#') {
        return;
    }
    match NameOrId::<u32>::parse(input) {
        None => {
            assert!(input.is_empty());
        }
        Some(NameOrId::Name(n)) => {
            assert!(!input.is_empty() && std::ptr::eq(n, input));
        }
        Some(NameOrId::Id(_)) => panic!("a name parsed as an id"),
    }
}

/// C5: input not starting with `#`, of 0 to 4 arbitrary bytes (valid UTF-8, no NUL): the empty
/// string gives `None`, anything else is `Name` of the very same string.
#[kani::proof]
#[kani::unwind(6)]
fn name_or_id_non_hash_is_name_0_to_4_bytes() {
    check_non_hash(&input::<0>(""));
    check_non_hash(&input::<1>(""));
    check_non_hash(&input::<2>(""));
    check_non_hash(&input::<3>(""));
    check_non_hash(&input::<4>(""));
}

fn check_ids_like_u32(input: &SudoString) {
    let as_u32 = NameOrId::<u32>::parse(input);
    let as_uid = NameOrId::<UserId>::parse(input);
    let as_gid = NameOrId::<GroupId>::parse(input);
    match as_u32 {
        None => {
            assert!(as_uid.is_none() && as_gid.is_none());
        }
        Some(NameOrId::Name(n)) => {
            assert!(matches!(as_uid, Some(NameOrId::Name(m)) if std::ptr::eq(m, n)));
            assert!(matches!(as_gid, Some(NameOrId::Name(m)) if std::ptr::eq(m, n)));
        }
        Some(NameOrId::Id(v)) => {
            assert!(as_uid == Some(NameOrId::Id(UserId::new(v))));
            assert!(as_gid == Some(NameOrId::Id(GroupId::new(v))));
        }
    }
}

/// C6: the instances used by `resolve_target_user_and_group` (`UserId`, `GroupId`) parse
/// exactly like `u32`, for every input of 0 to 3 arbitrary bytes (valid UTF-8, no NUL).
#[kani::proof]
#[kani::unwind(5)]
fn name_or_id_user_and_group_ids_like_u32_0_to_3_bytes() {
    check_ids_like_u32(&input::<0>(""));
    check_ids_like_u32(&input::<1>(""));
    check_ids_like_u32(&input::<2>(""));
    check_ids_like_u32(&input::<3>(""));
}
