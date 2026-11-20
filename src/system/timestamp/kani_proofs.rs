//! Kani bounded proofs for the session record (timestamp) file: where the per-user file lives,
//! the record encoding, and which account a record stands for. Built only under `cfg(kani)`.
//! Bounds and replaced functions are stated per harness; see proofs/kani/README.md.
// Replacement functions are referenced only from `#[kani::stub]` attributes.
#![allow(dead_code)]

use std::fs::File;
use std::io;
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::time::Duration;

use super::{RecordScope, SessionRecord, SessionRecordFile};
use crate::common::resolve::{AuthUser, CurrentUser};
use crate::common::{Error, SudoPath, SudoString};
use crate::system::User;
use crate::system::interface::{DeviceId, GroupId, ProcessId, UserId};
use crate::system::time::{ProcessCreateTime, SystemTime};

/// A user with the given uid and gid and a name of exactly 2 arbitrary bytes (valid UTF-8, no
/// NUL; this includes `..`, `./`, `/x`, `a/`).
fn any_user(uid: u32, gid: u32) -> User {
    let raw: [u8; 2] = kani::any();
    kani::assume(!raw.contains(&0));
    let Ok(s) = std::str::from_utf8(&raw) else {
        kani::assume(false);
        unreachable!()
    };
    let mut name = String::with_capacity(8);
    name.push_str(s);
    User {
        uid: UserId::new(uid),
        gid: GroupId::new(gid),
        name: SudoString::new(name).unwrap(),
        home: SudoPath::new(PathBuf::from("/home/u")).unwrap(),
        shell: PathBuf::from("/bin/sh"),
        groups: Vec::new(),
    }
}

static EXPECTED_UID: AtomicU32 = AtomicU32::new(0);
static OPENED: AtomicBool = AtomicBool::new(false);

/// Replaces `secure_open_cookie_file` (a real `open`): checks the path it is given and fails.
/// The path must be `/var/run/sudo-rs/ts/<name>` with `<name>` one normal component that is
/// the canonical decimal spelling of the user's uid.
fn open_cookie_file_checked<P: AsRef<Path>>(path: P) -> io::Result<File> {
    let mut c = path.as_ref().components();
    assert_eq!(c.next(), Some(Component::RootDir));
    for dir in ["var", "run", "sudo-rs", "ts"] {
        assert_eq!(c.next(), Some(Component::Normal(dir.as_ref())));
    }
    let Some(Component::Normal(name)) = c.next() else {
        panic!("record file is not a plain entry of the timestamp directory");
    };
    assert!(c.next().is_none());
    let name = name.as_encoded_bytes();
    assert!(!name.is_empty() && name.iter().all(u8::is_ascii_digit));
    assert!(name.len() == 1 || name[0] != b'0');
    let mut value: u64 = 0;
    for &d in name {
        value = value * 10 + u64::from(d - b'0');
    }
    assert_eq!(value, u64::from(EXPECTED_UID.load(Ordering::SeqCst)));
    OPENED.store(true, Ordering::SeqCst);
    Err(io::Error::from(io::ErrorKind::PermissionDenied))
}

/// E1 (CVE-2023-42456 class): for every uid (all 2^32) and every 2-byte user name,
/// `SessionRecordFile::open_for_user` opens `/var/run/sudo-rs/ts/<uid in decimal>`: one plain
/// entry of the timestamp directory, determined by the uid alone. The real `open` is replaced
/// by `open_cookie_file_checked`.
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(crate::system::audit::secure_open_cookie_file, open_cookie_file_checked)]
fn record_file_path_stays_in_ts_dir_any_user() {
    let uid: u32 = kani::any();
    EXPECTED_UID.store(uid, Ordering::SeqCst);
    let user = CurrentUser::fake(any_user(uid, kani::any()));
    let res = SessionRecordFile::open_for_user(&user, Duration::from_secs(300));
    assert!(res.is_err());
    assert!(OPENED.load(Ordering::SeqCst));
}

/// Nanoseconds in the normalised range, as `SystemTime::now` and process start times produce.
fn any_nsecs() -> i64 {
    let n: i64 = kani::any();
    kani::assume((0..1_000_000_000).contains(&n));
    n
}

fn any_scope() -> RecordScope {
    let init_time = ProcessCreateTime::new(kani::any(), any_nsecs());
    if kani::any() {
        RecordScope::Tty {
            tty_device: DeviceId::new(kani::any()),
            session_pid: ProcessId::new(kani::any()),
            init_time,
        }
    } else {
        RecordScope::Ppid {
            group_pid: ProcessId::new(kani::any()),
            session_pid: ProcessId::new(kani::any()),
            init_time,
        }
    }
}

/// E2: every record (both scope kinds, all field values, normalised times) encodes to 50
/// (tty scope) or 46 (ppid scope) bytes and decodes back to itself.
#[kani::proof]
#[kani::unwind(4)]
fn record_encode_decode_roundtrip() {
    let scope = any_scope();
    let record = SessionRecord::init(
        scope,
        UserId::new(kani::any()),
        kani::any(),
        SystemTime::new(kani::any(), any_nsecs()),
    );
    let bytes = record.as_bytes().unwrap();
    let expected_len = match scope {
        RecordScope::Tty { .. } => 50,
        RecordScope::Ppid { .. } => 46,
    };
    assert_eq!(bytes.len(), expected_len);
    assert_eq!(SessionRecord::from_bytes(&bytes).unwrap(), record);
}

/// Decoding exactly `N` arbitrary bytes, both stored seconds fields in [-2^62, 2^62].
fn check_decode<const N: usize>() {
    let data: [u8; N] = kani::any();
    let secs_in_range = |at: usize| match data.get(at..at + 8) {
        Some(b) => {
            let v = i64::from_ne_bytes(b.try_into().unwrap());
            (-(1i64 << 62)..=(1i64 << 62)).contains(&v)
        }
        None => true,
    };
    // offsets of the process start seconds and of the record seconds, per scope kind
    let (init_at, ts_at) = if data.first() == Some(&1) { (13, 33) } else { (9, 29) };
    kani::assume(secs_in_range(init_at) && secs_in_range(ts_at));
    if let Ok(record) = SessionRecord::from_bytes(&data) {
        assert!(N == 50 || N == 46);
        let again = record.as_bytes().unwrap();
        assert_eq!(SessionRecord::from_bytes(&again).unwrap(), record);
    }
}

/// E3: decoding arbitrary input of 0, 1, 13, 45, 46, 47, 49, 50 or 51 bytes reads only inside
/// the input and never panics; a decoded record has length 50 or 46 and re-encodes to a
/// record that decodes to itself. Bound: both stored seconds fields in [-2^62, 2^62]; inputs
/// outside this range are not covered by E3.
#[kani::proof]
#[kani::unwind(4)]
fn record_decode_arbitrary_bytes() {
    check_decode::<0>();
    check_decode::<1>();
    check_decode::<13>();
    check_decode::<45>();
    check_decode::<46>();
    check_decode::<47>();
    check_decode::<49>();
    check_decode::<50>();
    check_decode::<51>();
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
    let user = any_user(uid, kani::any());
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

/// Replaces `User::from_uid` (`getpwuid_r`): an error, no entry, or an entry with the requested
/// uid (the getpwuid_r contract) and arbitrary other fields.
fn from_uid_any(uid: UserId) -> Result<Option<User>, Error> {
    match kani::any::<u8>() {
        0 => Err(Error::UserNotFound("kani".to_string())),
        1 => Ok(None),
        _ => Ok(Some(any_user(uid.inner(), kani::any()))),
    }
}

/// E5 (CVE-2025-64517 class, creation side): the record `create` writes for an authenticating
/// user, `SessionRecord::new(scope, auth_user.uid)`, matches that user and no user with another
/// uid, for each way the pipeline builds the authenticating user: the invoking user, the
/// target user (targetpw), and root via `resolve_root_for_rootpw` (rootpw, which must yield
/// uid 0). `SystemTime::now` and `User::from_uid` are replaced as stated above.
#[kani::proof]
#[kani::unwind(5)]
#[kani::stub(crate::system::time::SystemTime::now, now_any)]
#[kani::stub(crate::system::User::from_uid, from_uid_any)]
fn created_record_identifies_authenticating_user() {
    let scope = any_scope();
    let invoking = CurrentUser::fake(any_user(kani::any(), kani::any()));
    let target = any_user(kani::any(), kani::any());
    let target_uid = target.uid;
    let auth = match kani::any::<u8>() {
        0 => AuthUser::from_current_user(invoking.clone()),
        1 => AuthUser::from_user_for_targetpw(target),
        _ => match AuthUser::resolve_root_for_rootpw() {
            Ok(root) => {
                assert_eq!(root.uid, UserId::ROOT);
                root
            }
            Err(_) => return,
        },
    };
    let record = SessionRecord::new(scope, auth.uid).unwrap();
    assert!(record.matches(&scope, &auth));
    let other = AuthUser::from_user_for_targetpw(any_user(kani::any(), kani::any()));
    if other.uid != auth.uid {
        assert!(!record.matches(&scope, &other));
    }
    // targetpw: the record is the target user's, not the invoking user's
    if auth.uid == target_uid && target_uid != invoking.uid {
        assert!(!record.matches(&scope, &AuthUser::from_current_user(invoking)));
    }
}
