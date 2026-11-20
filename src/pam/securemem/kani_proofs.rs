//! Kani bounded proofs for `PamBuffer`, the fixed-size buffer that holds passwords for PAM.
//! Built only under `cfg(kani)`. Bounds are stated per harness; see proofs/kani/README.md.
// Replacement functions are referenced only from `#[kani::stub]` attributes.
#![allow(dead_code)]

use std::ffi::c_void;

use super::{PamBuffer, SIZE, wipe_memory};

/// F1: a fresh buffer is `SIZE` (512) zeroed bytes of which `SIZE - 1` are reachable through
/// `Deref`/`DerefMut`; a write at any reachable index is read back, every index past the end
/// is refused by the slice, and the last byte (the C terminator) stays NUL after `leak`.
#[kani::proof]
#[kani::unwind(513)]
fn pam_buffer_bounds_and_terminator() {
    assert_eq!(SIZE, 512);
    let mut buf = PamBuffer::default();
    assert_eq!(buf.len(), SIZE - 1);
    assert!(buf.iter().all(|&b| b == 0));
    let i: usize = kani::any();
    let v: u8 = kani::any();
    match buf.get_mut(i) {
        Some(slot) => {
            assert!(i < SIZE - 1);
            *slot = v;
            assert_eq!(buf[i], v);
        }
        None => {
            assert!(i >= SIZE - 1);
        }
    }
    let ptr = buf.leak();
    // SAFETY: `leak` returns the start of the `SIZE`-byte allocation made by `calloc`.
    unsafe {
        assert_eq!(*ptr.as_ptr().add(SIZE - 1), 0);
        libc::free(ptr.as_ptr().cast());
    }
}

/// Replaces `libc::free` while a `PamBuffer` is dropped: checks that all `SIZE` bytes of the
/// allocation were overwritten before it is handed back. (The memory is not released; leaks
/// are not checked.)
unsafe fn free_checked(ptr: *mut c_void) {
    let bytes = ptr.cast::<u8>();
    for i in 0..SIZE {
        // SAFETY: `ptr` is the `SIZE`-byte allocation of the dropped buffer.
        assert_eq!(unsafe { *bytes.add(i) }, 0x55);
    }
}

/// F2: dropping a buffer that holds an arbitrary password (any bytes at any index) wipes every
/// one of its `SIZE` bytes, the terminator included, before `free`.
#[kani::proof]
#[kani::unwind(513)]
#[kani::stub(libc::free, free_checked)]
fn pam_buffer_wiped_on_drop() {
    let mut buf = PamBuffer::default();
    let i: usize = kani::any();
    kani::assume(i < SIZE - 1);
    buf[i] = kani::any();
    buf[0] = kani::any();
    buf[SIZE - 2] = kani::any();
    drop(buf);
}

/// F3: `wipe_memory` overwrites exactly the slice it is given (up to 8 bytes, inside a
/// 10-byte array) and nothing next to it.
#[kani::proof]
#[kani::unwind(11)]
fn wipe_memory_exact_8() {
    let mut mem: [u8; 10] = kani::any();
    let orig = mem;
    let from: usize = kani::any();
    let to: usize = kani::any();
    kani::assume(1 <= from && from <= to && to <= 9);
    wipe_memory(&mut mem[from..to]);
    for k in 0..10 {
        if from <= k && k < to {
            assert_eq!(mem[k], 0x55);
        } else {
            assert_eq!(mem[k], orig[k]);
        }
    }
}
