//! Kani bounded proofs for the C-string helpers and the pure helpers of `cutils`.
//! Built only under `cfg(kani)`. Bounds are stated per harness; see proofs/kani/README.md.

use super::{cerr, dynamic_fill, os_string_from_ptr, string_from_ptr};

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
