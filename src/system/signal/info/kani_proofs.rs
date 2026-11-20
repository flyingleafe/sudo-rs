//! Kani bounded proof for `SignalInfo::signaler_pid`, which reads the `si_pid` member of the
//! `siginfo_t` union. Built only under `cfg(kani)`; see proofs/kani/README.md.

use std::mem::size_of;

use super::SignalInfo;
use crate::system::interface::ProcessId;

/// G4: for every bit pattern of a `siginfo_t` (128 bytes on Linux x86-64): the read stays inside
/// the struct; a user-sent signal (`si_code <= 0`) yields the pid stored at byte offset 16 (the
/// kernel's `si_pid` slot), any other signal yields `None`; `signal()` is `si_signo`.
#[kani::proof]
fn signaler_pid_reads_si_pid() {
    const N: usize = size_of::<libc::siginfo_t>();
    assert_eq!(N, 128);
    let raw: [u8; N] = kani::any();
    // SAFETY: `siginfo_t` is a plain C struct of integers; every bit pattern is a valid value,
    // and `SignalInfo` is `repr(transparent)` over it.
    let info: SignalInfo = unsafe { std::mem::transmute(raw) };
    let code = i32::from_ne_bytes(raw[8..12].try_into().unwrap());
    let pid = i32::from_ne_bytes(raw[16..20].try_into().unwrap());
    let signo = i32::from_ne_bytes(raw[0..4].try_into().unwrap());
    assert_eq!(info.signal(), signo);
    if code <= 0 {
        assert_eq!(info.signaler_pid(), Some(ProcessId::new(pid)));
    } else {
        assert_eq!(info.signaler_pid(), None);
    }
}
