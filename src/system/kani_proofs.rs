//! Kani bounded proofs for the conversions of C passwd/group records (`User::from_libc`,
//! `Group::from_libc`): pointer reads stay inside the NUL-terminated strings and the result
//! carries exactly their contents. Built only under `cfg(kani)`. Bounds are stated per
//! harness; see proofs/kani/README.md.
// Replacement functions are referenced only from `#[kani::stub]` attributes.
#![allow(dead_code)]

use std::ffi::{c_char, c_int};
use std::sync::atomic::{AtomicI32, Ordering};

use super::{Group, User};
use crate::system::interface::{GroupId, UserId};

/// `M - 1` symbolic bytes (interior NULs allowed) followed by a NUL.
fn c_buffer<const M: usize>() -> [c_char; M] {
    let mut buf: [c_char; M] = kani::any();
    buf[M - 1] = 0;
    buf
}

fn c_prefix(buf: &[c_char]) -> Vec<u8> {
    buf.iter().take_while(|&&c| c != 0).map(|&c| c as u8).collect()
}

/// G1: `Group::from_libc` on a record whose name has up to 4 arbitrary bytes: the gid is
/// copied and the name is the lossy UTF-8 reading of the bytes before the first NUL.
#[kani::proof]
#[kani::unwind(6)]
fn group_from_libc_exact_4_bytes() {
    let mut name = c_buffer::<5>();
    // SAFETY: an all-zero `group` is a valid value of this plain C struct.
    let mut grp: libc::group = unsafe { std::mem::zeroed() };
    grp.gr_name = name.as_mut_ptr();
    grp.gr_gid = kani::any();
    // SAFETY: `gr_name` points to a NUL-terminated string; `gr_mem` is not read.
    let group = unsafe { Group::from_libc(&grp) };
    assert_eq!(group.gid, GroupId::new(grp.gr_gid));
    let prefix = c_prefix(&name);
    assert_eq!(group.name.as_deref(), Some(String::from_utf8_lossy(&prefix).as_ref()));
}

/// Number of supplementary groups the replaced `getgrouplist` reports (fixed per run).
static NGROUPS: AtomicI32 = AtomicI32::new(-1);

/// Replaces `getgrouplist` (reads the group database) with its contract: a list of `n` groups
/// (`n` = 33 groups, the same on every call; group k is `group + k`); if `*ngroups`
/// is too small, return -1 and store `n` in `*ngroups`, otherwise fill the first `n` entries,
/// store `n` and return it. With n > 32 this forces `dynamic_fill` to grow its buffer.
unsafe fn getgrouplist_model(
    _user: *const c_char,
    group: libc::gid_t,
    groups: *mut libc::gid_t,
    ngroups: *mut c_int,
) -> c_int {
    if NGROUPS.load(Ordering::SeqCst) < 0 {
        let n: i32 = 33;
        NGROUPS.store(n, Ordering::SeqCst);
    }
    let n = NGROUPS.load(Ordering::SeqCst);
    // SAFETY: the caller passes a valid `ngroups` and a `groups` array of `*ngroups` entries.
    unsafe {
        if *ngroups < n {
            *ngroups = n;
            return -1;
        }
        for k in 0..n {
            *groups.add(k as usize) = group.wrapping_add(k as libc::gid_t);
        }
        *ngroups = n;
    }
    n
}

/// G2: `User::from_libc` on a passwd record with name, home and shell of up to 3 arbitrary
/// bytes each, and a group list of 33 entries (`getgrouplist` replaced by
/// `getgrouplist_model`): uid, gid, name (lossy UTF-8), shell (exact bytes) and the group list
/// are copied exactly; the result is an error exactly when the home directory is not UTF-8.
#[kani::proof]
#[kani::unwind(65)]
#[kani::stub(libc::getgrouplist, getgrouplist_model)]
fn user_from_libc_exact_3_bytes_33_groups() {
    let mut name = c_buffer::<4>();
    let mut dir = c_buffer::<4>();
    let mut shell = c_buffer::<4>();
    // SAFETY: an all-zero `passwd` is a valid value of this plain C struct.
    let mut pwd: libc::passwd = unsafe { std::mem::zeroed() };
    pwd.pw_name = name.as_mut_ptr();
    pwd.pw_dir = dir.as_mut_ptr();
    pwd.pw_shell = shell.as_mut_ptr();
    pwd.pw_uid = kani::any();
    pwd.pw_gid = kani::any();
    // SAFETY: the string fields point to NUL-terminated strings; the others are not read.
    let res = unsafe { User::from_libc(&pwd) };
    let dir_bytes = c_prefix(&dir);
    match res {
        Err(_) => {
            assert!(std::str::from_utf8(&dir_bytes).is_err());
        }
        Ok(user) => {
            assert!(std::str::from_utf8(&dir_bytes).is_ok());
            assert_eq!(user.uid, UserId::new(pwd.pw_uid));
            assert_eq!(user.gid, GroupId::new(pwd.pw_gid));
            assert_eq!(user.name.as_str(), String::from_utf8_lossy(&c_prefix(&name)));
            assert_eq!(user.home.as_os_str().as_encoded_bytes(), dir_bytes.as_slice());
            assert_eq!(user.shell.as_os_str().as_encoded_bytes(), c_prefix(&shell).as_slice());
            let n = NGROUPS.load(Ordering::SeqCst);
            assert_eq!(user.groups.len(), n as usize);
            for (k, g) in user.groups.iter().enumerate() {
                assert_eq!(*g, GroupId::new(pwd.pw_gid.wrapping_add(k as libc::gid_t)));
            }
        }
    }
}
