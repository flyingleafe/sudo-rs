//! Kani bounded proofs for `alloc_dynamic`, the over-allocation of the seccomp notification
//! buffers, and for the NOEXEC filter bytecode. Built only under `cfg(kani)`; see
//! proofs/kani/README.md.

use std::alloc::{GlobalAlloc, Layout, System};
use std::mem::{align_of, size_of};

use libc::{seccomp_notif, seccomp_notif_resp};

use super::alloc_dynamic;
use super::filter_model::{
    ARCH_OFFSET, Action, NR_OFFSET, SECCOMP_DATA_SIZE, check_accepted, run, this_target, word,
};
use super::noexec_filter;

fn check<T>(runtime_size: u16) {
    let (ptr, size) = alloc_dynamic::<T>(runtime_size);
    assert!(!ptr.is_null());
    assert_eq!(size, usize::from(runtime_size).max(size_of::<T>()));
    assert!(size >= size_of::<T>());
    assert_eq!(ptr as usize % align_of::<seccomp_notif>(), 0);
    assert_eq!(ptr as usize % align_of::<T>(), 0);
    // every byte of the allocation is zeroed and writable
    let k: usize = kani::any();
    kani::assume(k < size);
    let bytes = ptr.cast::<u8>();
    // SAFETY: `k < size` and the allocation has `size` bytes.
    unsafe {
        assert_eq!(*bytes.add(k), 0);
        *bytes.add(k) = 1;
        let layout = Layout::from_size_align(size, align_of::<seccomp_notif>()).unwrap();
        System.dealloc(ptr.cast(), layout);
    }
}

/// G3: for every kernel-reported size (all u16 values), both seccomp buffers are non-null,
/// aligned, zeroed, at least as large as the Rust type and exactly max(reported, type size).
#[kani::proof]
fn alloc_dynamic_any_kernel_size() {
    check::<seccomp_notif>(kani::any());
    check::<seccomp_notif_resp>(kani::any());
}

/// The NOEXEC filter that `add_noexec_filter` installs, run under the classic BPF semantics of
/// `filter_model` on every `seccomp_data` (all 64 bytes arbitrary), returns the action that the
/// documented dispatch contract of this target prescribes; Allow, Notify and KillProcess are
/// each reached.
#[kani::proof]
#[kani::unwind(20)]
fn noexec_filter_matches_contract_on_any_seccomp_data() {
    let prog = noexec_filter();
    assert!(check_accepted(&prog).is_ok());
    let data: [u8; SECCOMP_DATA_SIZE] = kani::any();
    let got = Action::of_ret(run(&prog, &data));
    let nr = word(&data, NR_OFFSET as usize);
    let arch = word(&data, ARCH_OFFSET as usize);
    if let Some(want) = this_target().expected(arch, nr) {
        assert_eq!(got, want);
    }
    kani::cover!(got == Action::Allow);
    kani::cover!(got == Action::Notify);
    kani::cover!(got == Action::KillProcess);
}
