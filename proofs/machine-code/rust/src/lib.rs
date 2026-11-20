//! Harness for the machine-code proof of sudo-rs's `NameOrId::parse` at `T = UserId`.
//!
//! Everything under `../copied/` is copied byte for byte from sudo-rs by
//! `../scripts/copy-source.sh` (`--check` verifies it). This file only supplies the imports
//! those items expect, the `libc::uid_t` type alias, and one monomorphic `extern "C"` entry
//! point, so that the generic function is compiled at the instance sudo-rs uses for `-u #<uid>`
//! (`resolve_from_name_or_id` with `I = UserId`).

#![no_std]

extern crate alloc;

use alloc::string::String;
use core::{fmt, num::ParseIntError, ops, str::FromStr};

/// `libc::uid_t` on `aarch64-unknown-linux-gnu` (libc 0.2: `pub type uid_t = u32;`).
mod libc {
    #[allow(non_camel_case_types)]
    pub type uid_t = u32;
}

include!("../copied/sudo_string.rs");
include!("../copied/sudo_string_deref.rs");
include!("../copied/sudo_string_debug.rs");
include!("../copied/user_id.rs");
include!("../copied/user_id_impl.rs");
include!("../copied/user_id_from_str.rs");
include!("../copied/name_or_id.rs");

/// `NameOrId::<UserId>::parse(input)`, reported through C-compatible out-parameters:
/// - `None`        -> returns 0, writes nothing;
/// - `Name(name)`  -> returns 1, writes `name` to `*name_out`;
/// - `Id(uid)`     -> returns 2, writes `uid.inner()` to `*id_out`.
#[unsafe(no_mangle)]
#[allow(improper_ctypes_definitions)]
pub extern "C" fn sudo_rs_name_or_id_parse_uid(
    input: &SudoString,
    name_out: &mut *const SudoString,
    id_out: &mut u32,
) -> u32 {
    match NameOrId::<UserId>::parse(input) {
        None => 0,
        Some(NameOrId::Name(name)) => {
            *name_out = name;
            1
        }
        Some(NameOrId::Id(id)) => {
            *id_out = id.inner();
            2
        }
    }
}
