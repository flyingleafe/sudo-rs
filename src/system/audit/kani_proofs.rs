//! Kani bounded proofs for the ownership and mode policy with which `secure_open_sudoers` and
//! `secure_open_cookie_file` accept a file (`checks`), and for handing out an opened file only
//! after the metadata read from the open handle passed that policy (`checked_handle`). Built
//! only under `cfg(kani)`. See proofs/kani/README.md.
// Replacement functions are referenced only from `#[kani::stub]` attributes.
#![allow(dead_code)]

use std::io::{self, ErrorKind};
use std::path::Path;
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};

use super::{Category, Insecure, Op, OwnerMode, checked_handle, mode};

/// G1: `mode` yields the octal permission bits, and for every uid, gid and mode (all `u32`
/// values) a file is accepted exactly when it is owned by root, is not world-writable, and is
/// group-writable only if its group is root; a refused file gets the first applicable reason
/// in the order owner, group, world.
#[kani::proof]
fn owner_mode_policy_exact() {
    assert_eq!(mode(Category::Owner, Op::Read), 0o400);
    assert_eq!(mode(Category::Owner, Op::Write), 0o200);
    assert_eq!(mode(Category::Owner, Op::Exec), 0o100);
    assert_eq!(mode(Category::Group, Op::Read), 0o040);
    assert_eq!(mode(Category::Group, Op::Write), 0o020);
    assert_eq!(mode(Category::Group, Op::Exec), 0o010);
    assert_eq!(mode(Category::World, Op::Read), 0o004);
    assert_eq!(mode(Category::World, Op::Write), 0o002);
    assert_eq!(mode(Category::World, Op::Exec), 0o001);

    let owner_mode = OwnerMode {
        uid: kani::any(),
        gid: kani::any(),
        mode: kani::any(),
    };
    let (uid, gid, bits) = (owner_mode.uid, owner_mode.gid, owner_mode.mode);
    let root_owned = uid == 0;
    let bad_group_write = gid != 0 && bits & 0o020 != 0;
    let world_write = bits & 0o002 != 0;
    let accepted = root_owned && !bad_group_write && !world_write;

    let verdict = owner_mode.insecurity();
    assert_eq!(verdict.is_none(), accepted);
    match verdict {
        None => {}
        Some(Insecure::NotRootOwned) => assert!(!root_owned),
        Some(Insecure::GroupWritable) => assert!(root_owned && bad_group_write),
        Some(Insecure::WorldWritable) => assert!(root_owned && !bad_group_write && world_write),
    }

    kani::cover!(accepted && gid != 0, "accepted: root-owned, other group");
    kani::cover!(
        accepted && gid == 0 && bits & 0o020 != 0,
        "accepted: group-writable, group root"
    );
    kani::cover!(
        matches!(verdict, Some(Insecure::NotRootOwned)),
        "refused: not owned by root"
    );
    kani::cover!(
        matches!(verdict, Some(Insecure::GroupWritable)),
        "refused: group-writable"
    );
    kani::cover!(
        matches!(verdict, Some(Insecure::WorldWritable)),
        "refused: world-writable"
    );
}

/// How often the handle of G2 was dropped (closed).
static DROPPED: AtomicU32 = AtomicU32::new(0);
/// How often the metadata of the handle of G2 was read.
static READS: AtomicU32 = AtomicU32::new(0);

/// Stands for an opened file in G2: carries an identity and records being dropped.
struct Handle(u8);

impl Drop for Handle {
    fn drop(&mut self) {
        DROPPED.fetch_add(1, SeqCst);
    }
}

/// Replaces `Insecure::message`: the path is not formatted into the message (the formatting
/// machinery is too costly for Kani). Only the text of the error changes; its kind and whether
/// an error is returned stay those of the real code.
fn message_unformatted(_insecure: Insecure, _path: &Path) -> String {
    String::new()
}

/// G2: `checked_handle` reads the owner and mode once, from the handle it was given, while that
/// handle is open; it returns that same handle, still open, exactly when the read succeeded and
/// the policy of G1 accepts the result. Otherwise it returns the read error, or a
/// `PermissionDenied` error for a refused file, and the handle has been dropped (closed) once.
/// Bounds: every owner, group and mode; the read succeeds or fails.
#[kani::proof]
#[kani::stub(super::Insecure::message, message_unformatted)]
fn checked_handle_only_after_passing_check() {
    let id: u8 = kani::any();
    let read_ok: bool = kani::any();
    let owner_mode = OwnerMode {
        uid: kani::any(),
        gid: kani::any(),
        mode: kani::any(),
    };
    let accepted = owner_mode.insecurity().is_none();

    let result = checked_handle(Path::new("/etc/sudoers"), Handle(id), |handle| {
        READS.fetch_add(1, SeqCst);
        assert_eq!(handle.0, id);
        assert_eq!(DROPPED.load(SeqCst), 0);
        if read_ok {
            Ok(owner_mode)
        } else {
            Err(io::Error::from(ErrorKind::Other))
        }
    });

    assert_eq!(READS.load(SeqCst), 1);
    match result {
        Ok(handle) => {
            assert!(read_ok && accepted);
            assert_eq!(handle.0, id);
            assert_eq!(DROPPED.load(SeqCst), 0);
            kani::cover!(owner_mode.gid != 0, "handle returned, group not root");
        }
        Err(error) => {
            assert_eq!(DROPPED.load(SeqCst), 1);
            if read_ok {
                assert!(!accepted);
                assert_eq!(error.kind(), ErrorKind::PermissionDenied);
                kani::cover!(true, "handle refused by the policy");
            } else {
                assert_eq!(error.kind(), ErrorKind::Other);
                kani::cover!(true, "metadata read fails");
            }
        }
    }
}
