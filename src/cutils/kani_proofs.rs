//! Kani bounded proofs for the C-string helpers and the pure helpers of `cutils`.
//! Built only under `cfg(kani)`. Bounds are stated per harness; see proofs/kani/README.md.

use std::ffi::c_char;

use super::{cerr, dynamic_fill, os_string_from_ptr, string_from_ptr};

/// A buffer of `M - 1` arbitrary bytes (interior NULs allowed) followed by one NUL, so that the
/// C string it holds has any length 0..=M-1. Any read past the buffer is a Kani failure.
fn c_buffer<const M: usize>() -> [c_char; M] {
    let mut buf: [c_char; M] = kani::any();
    buf[M - 1] = 0;
    buf
}

/// Index of the first NUL.
fn c_len(buf: &[c_char]) -> usize {
    let mut n = 0;
    while buf[n] != 0 {
        n += 1;
    }
    n
}

/// D1: `os_string_from_ptr` on a NUL-terminated buffer of 6 arbitrary bytes plus terminator:
/// no read outside the buffer, and the result is exactly the bytes before the first NUL.
#[kani::proof]
#[kani::unwind(8)]
fn os_string_from_ptr_exact_6_bytes() {
    let buf = c_buffer::<7>();
    // SAFETY: `buf` is a valid NUL-terminated C string.
    let s = unsafe { os_string_from_ptr(buf.as_ptr()) };
    let bytes = s.as_encoded_bytes();
    let n = c_len(&buf);
    assert_eq!(bytes.len(), n);
    for i in 0..n {
        assert_eq!(bytes[i], buf[i] as u8);
    }
}

/// D2: `string_from_ptr` on a NUL-terminated buffer of 3 arbitrary bytes plus terminator: no
/// read outside the buffer; the result is the bytes before the first NUL when those are UTF-8
/// (in particular every ASCII string), and their lossy conversion (each invalid sequence
/// replaced by U+FFFD) otherwise.
#[kani::proof]
#[kani::unwind(5)]
fn string_from_ptr_exact_3_bytes() {
    let buf = c_buffer::<4>();
    // SAFETY: `buf` is a valid NUL-terminated C string.
    let s = unsafe { string_from_ptr(buf.as_ptr()) };
    let n = c_len(&buf);
    let prefix: [u8; 3] = [buf[0] as u8, buf[1] as u8, buf[2] as u8];
    let prefix = &prefix[..n];
    match std::str::from_utf8(prefix) {
        Ok(valid) => assert_eq!(s, valid),
        Err(_) => {
            assert!(s.contains('\u{FFFD}'));
            assert_eq!(s, String::from_utf8_lossy(prefix));
        }
    }
}

/// D3: both helpers map the null pointer to the empty string.
#[kani::proof]
fn from_ptr_null_is_empty() {
    // SAFETY: the null pointer is explicitly allowed by both functions.
    unsafe {
        assert!(string_from_ptr(std::ptr::null()).is_empty());
        assert!(os_string_from_ptr(std::ptr::null()).is_empty());
    }
}

/// D4: `cerr` returns `Err` exactly for -1, and the value itself otherwise, for every i32,
/// i64 and isize value.
#[kani::proof]
fn cerr_only_minus_one_is_error() {
    let a: i32 = kani::any();
    assert_eq!(cerr(a).is_err(), a == -1);
    if let Ok(v) = cerr(a) {
        assert_eq!(v, a);
    }
    let b: i64 = kani::any();
    assert_eq!(cerr(b).is_err(), b == -1);
    let c: isize = kani::any();
    assert_eq!(cerr(c).is_err(), c == -1);
}

/// `dynamic_fill` over `start..end` with a closure that, on every call, nondeterministically
/// fails, asks for a bigger buffer, or reports a used length of at most the buffer length:
/// every buffer offered is longer than the previous one and lies in [start, end], and the
/// result is exactly what the closure reported (`Ok(None)` only once the length reached `end`).
fn check_dynamic_fill(start: usize, end: usize) {
    let mut last_len = 0;
    let mut reported = None;
    let result = dynamic_fill::<u8, ()>(start..end, |buf| {
        assert!(buf.len() >= start && buf.len() <= end);
        assert!(buf.len() > last_len);
        last_len = buf.len();
        match kani::any::<u8>() {
            0 => Err(()),
            1 => Ok(None),
            _ => {
                let used: usize = kani::any();
                kani::assume(used <= buf.len());
                reported = Some(used);
                Ok(Some(used))
            }
        }
    });
    match result {
        Err(()) => {}
        Ok(None) => {
            assert!(last_len >= end);
        }
        Ok(Some(v)) => assert_eq!(Some(v.len()), reported),
    }
}

/// D5: `dynamic_fill` for the ranges 1..16, 3..10, 5..5 and 32..64 (the smallest range the
/// callers use starts at 32): see `check_dynamic_fill`.
#[kani::proof]
#[kani::unwind(66)]
fn dynamic_fill_bounds_and_result() {
    check_dynamic_fill(1, 16);
    check_dynamic_fill(3, 10);
    check_dynamic_fill(5, 5);
    check_dynamic_fill(32, 64);
}

/// D6: a closure reporting more than the buffer length makes `dynamic_fill` panic
/// (documented internal invariant; the callers report at most the length).
#[kani::proof]
#[kani::should_panic]
#[kani::unwind(10)]
fn dynamic_fill_overlong_report_panics() {
    let _ = dynamic_fill::<u8, ()>(4..8, |buf| Ok(Some(buf.len() + 1)));
}
