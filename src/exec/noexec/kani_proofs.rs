//! Kani bounded proof for `alloc_dynamic`, the over-allocation of the seccomp notification
//! buffers. Built only under `cfg(kani)`; see proofs/kani/README.md.

use std::alloc::{GlobalAlloc, Layout, System};
use std::mem::{align_of, size_of};

use libc::{seccomp_notif, seccomp_notif_resp};

use super::alloc_dynamic;

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
