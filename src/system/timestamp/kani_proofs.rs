//! Kani bounded proofs for the session record (timestamp) file: where the per-user file lives,
//! the record encoding, and which account a record stands for. Built only under `cfg(kani)`.
//! Bounds and replaced functions are stated per harness; see proofs/kani/README.md.
// Replacement functions are referenced only from `#[kani::stub]` attributes.
#![allow(dead_code)]

use std::fs::File;
use std::io;
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

use super::{RecordScope, SessionRecord, SessionRecordFile};
use crate::common::resolve::{AuthUser, CurrentUser};
use crate::common::{Error, SudoPath, SudoString};
use crate::system::User;
use crate::system::interface::{DeviceId, GroupId, ProcessId, UserId};
use crate::system::time::{ProcessCreateTime, SystemTime};

/// Whether `b` (at most 3 bytes) is well-formed UTF-8, written out from the table of
/// well-formed byte sequences in the Unicode standard (section 3.9) without loops, so that
/// the harness bound does not have to cover `std::str::from_utf8`'s data-dependent loop.
fn is_utf8_upto_3(b: &[u8]) -> bool {
    let cont = |x: u8| (0x80..=0xBF).contains(&x);
    match *b {
        [] => true,
        [a, ref rest @ ..] if a < 0x80 => is_utf8_upto_3(rest),
        [a, c, ref rest @ ..] if (0xC2..=0xDF).contains(&a) && cont(c) => is_utf8_upto_3(rest),
        [a, c, d] => {
            let second = match a {
                0xE0 => (0xA0..=0xBF).contains(&c),
                0xE1..=0xEC | 0xEE..=0xEF => cont(c),
                0xED => (0x80..=0x9F).contains(&c),
                _ => false,
            };
            second && cont(d)
        }
        _ => false,
    }
}

/// A user with the given uid and gid and a name of exactly `N` <= 3 arbitrary bytes (valid
/// UTF-8, no NUL; for `N` = 2 this includes `..`, `./`, `/x`, `a/`).
fn any_user<const N: usize>(uid: u32, gid: u32) -> User {
    let raw: [u8; N] = kani::any();
    kani::assume(!raw.contains(&0) && is_utf8_upto_3(&raw));
    // SAFETY: well-formed UTF-8 by the assumption above
    let name = unsafe { std::str::from_utf8_unchecked(&raw) }.to_string();
    User {
        uid: UserId::new(uid),
        gid: GroupId::new(gid),
        name: SudoString::new(name).unwrap(),
        home: SudoPath::new(PathBuf::from("/")).unwrap(),
        shell: PathBuf::from("/bin/sh"),
        groups: Vec::new(),
    }
}

/// The uid of the invoking user in E1.
const E1_UID: u32 = 1000;

/// The timestamp directory with its trailing separator, written out for the check below.
const TS_DIR: &[u8] = b"/var/run/sudo-rs/ts/";

/// Replaces `secure_open_cookie_file` (a real `open`). Checks, on the bytes and without
/// `std::path` parsing, the path it is given: it starts with the timestamp directory, its last
/// segment is not `..`, and it is exactly `/var/run/sudo-rs/ts/1000` (which implies the other
/// two). Then it ends the execution (`kani::assume(false)`): what happens after the `open` is
/// not part of E1. The `cover!` shows that the call is reached.
fn open_cookie_file_checked<P: AsRef<Path>>(path: P) -> io::Result<File> {
    let bytes = path.as_ref().as_os_str().as_bytes();
    assert!(
        bytes.len() > TS_DIR.len() && bytes.starts_with(TS_DIR),
        "record path is outside the timestamp directory"
    );
    assert!(
        !(bytes.ends_with(b"/..") || bytes.ends_with(b"/../")),
        "record path ends in a `..` component"
    );
    assert!(
        bytes == b"/var/run/sudo-rs/ts/1000",
        "record path is not <timestamp directory>/<uid>"
    );
    kani::cover!(true, "record file opened");
    kani::assume(false);
    unreachable!()
}

fn check_record_path<const N: usize>() {
    let user = CurrentUser::fake(any_user::<N>(E1_UID, kani::any()));
    let _ = SessionRecordFile::open_for_user(&user, Duration::from_secs(300));
}

/// E1 (CVE-2023-42456 class): for uid 1000 and every user name of 2 bytes,
/// `SessionRecordFile::open_for_user` opens `/var/run/sudo-rs/ts/1000`: inside the timestamp
/// directory, no `..` component, named by the uid alone. The real `open` is replaced by
/// `open_cookie_file_checked`.
#[kani::proof]
#[kani::unwind(26)]
#[kani::stub(
    crate::system::audit::secure_open_cookie_file,
    open_cookie_file_checked
)]
fn record_path_is_uid_entry_name_2_bytes() {
    check_record_path::<2>();
}

/// E1 with user names of 3 bytes (this includes `../`, `/..`, `a/.`).
#[kani::proof]
#[kani::unwind(26)]
#[kani::stub(
    crate::system::audit::secure_open_cookie_file,
    open_cookie_file_checked
)]
fn record_path_is_uid_entry_name_3_bytes() {
    check_record_path::<3>();
}

/// Nanoseconds in the normalised range, as `SystemTime::now` and process start times produce.
fn any_nsecs() -> i64 {
    let n: i64 = kani::any();
    kani::assume((0..1_000_000_000).contains(&n));
    n
}

fn any_init_time() -> ProcessCreateTime {
    ProcessCreateTime::new(kani::any(), any_nsecs())
}

fn any_tty_scope() -> RecordScope {
    RecordScope::Tty {
        tty_device: DeviceId::new(kani::any()),
        session_pid: ProcessId::new(kani::any()),
        init_time: any_init_time(),
    }
}

fn any_ppid_scope() -> RecordScope {
    RecordScope::Ppid {
        group_pid: ProcessId::new(kani::any()),
        session_pid: ProcessId::new(kani::any()),
        init_time: any_init_time(),
    }
}

fn any_scope() -> RecordScope {
    if kani::any() {
        any_tty_scope()
    } else {
        any_ppid_scope()
    }
}

fn check_roundtrip(scope: RecordScope, expected_len: usize) {
    let record = SessionRecord::init(
        scope,
        UserId::new(kani::any()),
        kani::any(),
        SystemTime::new(kani::any(), any_nsecs()),
    );
    let bytes = record.as_bytes().unwrap();
    assert_eq!(bytes.len(), expected_len);
    assert_eq!(SessionRecord::from_bytes(&bytes).unwrap(), record);
}

/// E2 (tty scope): every record with a tty scope (all field values, normalised times) encodes
/// to 50 bytes and decodes back to itself.
#[kani::proof]
#[kani::unwind(4)]
fn record_encode_decode_roundtrip_tty() {
    check_roundtrip(any_tty_scope(), 50);
}

/// E2 (ppid scope): every record with a parent-process scope encodes to 46 bytes and decodes
/// back to itself.
#[kani::proof]
#[kani::unwind(4)]
fn record_encode_decode_roundtrip_ppid() {
    check_roundtrip(any_ppid_scope(), 46);
}

/// Byte layout of an encoded record for one scope tag: offsets of the process start seconds
/// and of the record seconds, the offset of the enabled flag, and the length.
struct Layout {
    tag: u8,
    init_secs: usize,
    ts_secs: usize,
    enabled: usize,
    len: usize,
}

/// tag, tty device (8), session pid (4), start time (16), uid (4), time (16), flag (1)
const TTY: Layout = Layout {
    tag: 1,
    init_secs: 13,
    ts_secs: 33,
    enabled: 49,
    len: 50,
};

/// tag, group pid (4), session pid (4), start time (16), uid (4), time (16), flag (1)
const PPID: Layout = Layout {
    tag: 2,
    init_secs: 9,
    ts_secs: 29,
    enabled: 45,
    len: 46,
};

/// The stored 8-byte field at `at`, if the input is long enough.
fn field(data: &[u8], at: usize) -> Option<i64> {
    data.get(at..at + 8)
        .map(|b| i64::from_ne_bytes(b.try_into().unwrap()))
}

/// `N` >= 1 arbitrary bytes that start with the scope tag of `l`. Precondition of E3: the
/// stored seconds fields that lie inside the input are in [-2^62, 2^62].
fn tagged<const N: usize>(l: &Layout) -> [u8; N] {
    let mut data: [u8; N] = kani::any();
    data[0] = l.tag;
    let in_range = |v: Option<i64>| v.is_none_or(|v| (-(1i64 << 62)..=(1i64 << 62)).contains(&v));
    kani::assume(in_range(field(&data, l.init_secs)) && in_range(field(&data, l.ts_secs)));
    data
}

/// Decoding a full-length input with the tag of `l` reads only inside it, never panics, and
/// succeeds exactly when the enabled flag is 0x00 or 0xFF.
fn check_decode_full<const N: usize>(l: &Layout) {
    assert_eq!(N, l.len);
    let data = tagged::<N>(l);
    assert_eq!(
        SessionRecord::from_bytes(&data).is_ok(),
        matches!(data[l.enabled], 0x00 | 0xFF)
    );
}

/// E3 (tty tag, 50 bytes): every input of 50 bytes starting with tag 1, both stored seconds
/// fields in [-2^62, 2^62], decodes without panic or out-of-bounds read; it is accepted
/// exactly when the enabled flag is 0x00 or 0xFF.
#[kani::proof]
#[kani::unwind(4)]
fn record_decode_tty_50_bytes() {
    check_decode_full::<50>(&TTY);
}

/// E3 (ppid tag, 46 bytes): as for the tty tag.
#[kani::proof]
#[kani::unwind(4)]
fn record_decode_ppid_46_bytes() {
    check_decode_full::<46>(&PPID);
}

fn check_decode_fails<const N: usize>(l: &Layout) {
    assert!(SessionRecord::from_bytes(&tagged::<N>(l)).is_err());
}

/// E3 (tty tag, other lengths): inputs of 1, 13, 45, 46, 47, 49 and 51 bytes starting with
/// tag 1 (same precondition) are rejected without panic.
#[kani::proof]
#[kani::unwind(4)]
fn record_decode_tty_wrong_lengths_fail() {
    check_decode_fails::<1>(&TTY);
    check_decode_fails::<13>(&TTY);
    check_decode_fails::<45>(&TTY);
    check_decode_fails::<46>(&TTY);
    check_decode_fails::<47>(&TTY);
    check_decode_fails::<49>(&TTY);
    check_decode_fails::<51>(&TTY);
}

/// E3 (ppid tag, other lengths): inputs of 1, 13, 45, 47, 49, 50 and 51 bytes starting with
/// tag 2 (same precondition) are rejected without panic.
#[kani::proof]
#[kani::unwind(4)]
fn record_decode_ppid_wrong_lengths_fail() {
    check_decode_fails::<1>(&PPID);
    check_decode_fails::<13>(&PPID);
    check_decode_fails::<45>(&PPID);
    check_decode_fails::<47>(&PPID);
    check_decode_fails::<49>(&PPID);
    check_decode_fails::<50>(&PPID);
    check_decode_fails::<51>(&PPID);
}

/// E4 (CVE-2025-64517 class, record side): a record matches a (scope, authenticating user)
/// pair exactly when both the scope and the uid of the authenticating user are the ones it was
/// written for; the authenticating user built for targetpw or for the invoking user carries
/// that user's uid. 2-byte names, all uids and scopes.
#[kani::proof]
#[kani::unwind(5)]
fn record_matches_exactly_its_scope_and_auth_user() {
    let written_scope = any_scope();
    let written_uid: u32 = kani::any();
    let record = SessionRecord::init(
        written_scope,
        UserId::new(written_uid),
        kani::any(),
        SystemTime::new(kani::any(), any_nsecs()),
    );
    let scope = any_scope();
    let uid: u32 = kani::any();
    let user = any_user::<2>(uid, kani::any());
    let auth = if kani::any() {
        AuthUser::from_user_for_targetpw(user)
    } else {
        AuthUser::from_current_user(CurrentUser::fake(user))
    };
    assert_eq!(auth.uid, UserId::new(uid));
    assert_eq!(
        record.matches(&scope, &auth),
        scope == written_scope && uid == written_uid
    );
}

/// Replaces `SystemTime::now` (`clock_gettime`): any normalised time.
fn now_any() -> io::Result<SystemTime> {
    Ok(SystemTime::new(kani::any(), any_nsecs()))
}

/// Replaces `User::from_uid` (`getpwuid_r`): an entry with the requested uid (the getpwuid_r
/// contract) and arbitrary other fields. The lookup failures (error, no entry) are not
/// modelled: `resolve_root_for_rootpw` returns an error for them and no record is written.
fn from_uid_entry(uid: UserId) -> Result<Option<User>, Error> {
    Ok(Some(any_user::<2>(uid.inner(), kani::any())))
}

/// The record `create` writes for an authenticating user, `SessionRecord::new(scope,
/// auth_user.uid)`, matches that user, no user with another uid, and not the invoking user
/// unless the invoking user has the same uid.
fn check_created_record(auth: &AuthUser, invoking: CurrentUser) {
    let scope = any_scope();
    let record = SessionRecord::new(scope, auth.uid).unwrap();
    assert!(record.matches(&scope, auth));
    let other = AuthUser::from_user_for_targetpw(any_user::<2>(kani::any(), kani::any()));
    if other.uid != auth.uid {
        assert!(!record.matches(&scope, &other));
    }
    if invoking.uid != auth.uid {
        assert!(!record.matches(&scope, &AuthUser::from_current_user(invoking)));
    }
}

fn any_invoking_user() -> CurrentUser {
    CurrentUser::fake(any_user::<2>(kani::any(), kani::any()))
}

/// E5 (CVE-2025-64517 class, creation side), default: the authenticating user is the invoking
/// user; the created record matches it and no user with another uid. All scopes and uids,
/// 2-byte names; `SystemTime::now` replaced by `now_any`.
#[kani::proof]
#[kani::unwind(5)]
#[kani::stub(crate::system::time::SystemTime::now, now_any)]
fn created_record_identifies_invoking_user() {
    let invoking = any_invoking_user();
    let auth = AuthUser::from_current_user(invoking.clone());
    assert_eq!(auth.uid, invoking.uid);
    check_created_record(&auth, invoking);
}

/// E5, targetpw: the authenticating user is the target user; the created record carries the
/// target user's uid, so it matches the target user and neither the invoking user (when the
/// uids differ) nor any user with another uid.
#[kani::proof]
#[kani::unwind(5)]
#[kani::stub(crate::system::time::SystemTime::now, now_any)]
fn created_record_identifies_target_user_targetpw() {
    let invoking = any_invoking_user();
    let target = any_user::<2>(kani::any(), kani::any());
    let target_uid = target.uid;
    let auth = AuthUser::from_user_for_targetpw(target);
    assert_eq!(auth.uid, target_uid);
    check_created_record(&auth, invoking);
}

/// E5, rootpw: the authenticating user comes from `resolve_root_for_rootpw` (`User::from_uid`
/// replaced by `from_uid_entry`); it has uid 0, and the created record matches root and
/// neither the invoking user (when not root) nor any user with another uid.
#[kani::proof]
#[kani::unwind(5)]
#[kani::stub(crate::system::time::SystemTime::now, now_any)]
#[kani::stub(crate::system::User::from_uid, from_uid_entry)]
fn created_record_identifies_root_rootpw() {
    let invoking = any_invoking_user();
    let root = AuthUser::resolve_root_for_rootpw().unwrap();
    assert_eq!(root.uid, UserId::ROOT);
    check_created_record(&root, invoking);
}
