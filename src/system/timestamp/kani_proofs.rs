//! Kani bounded proofs for the session record (timestamp) file: the record encoding and which
//! account a record stands for. Built only under `cfg(kani)`.
//! Bounds and replaced functions are stated per harness; see proofs/kani/README.md.

use std::path::PathBuf;

use super::{RecordScope, SessionRecord};
use crate::common::resolve::{AuthUser, CurrentUser};
use crate::common::{SudoPath, SudoString};
use crate::system::User;
use crate::system::interface::{DeviceId, GroupId, ProcessId, UserId};
use crate::system::time::{ProcessCreateTime, SystemTime};

/// A user with the given uid and gid and a name of exactly `N` arbitrary bytes (valid UTF-8, no
/// NUL; for `N` = 2 this includes `..`, `./`, `/x`, `a/`).
fn any_user<const N: usize>(uid: u32, gid: u32) -> User {
    let raw: [u8; N] = kani::any();
    kani::assume(!raw.contains(&0));
    let Ok(s) = std::str::from_utf8(&raw) else {
        kani::assume(false);
        unreachable!()
    };
    User {
        uid: UserId::new(uid),
        gid: GroupId::new(gid),
        name: SudoString::new(s.to_string()).unwrap(),
        home: SudoPath::new(PathBuf::from("/")).unwrap(),
        shell: PathBuf::from("/bin/sh"),
        groups: Vec::new(),
    }
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
