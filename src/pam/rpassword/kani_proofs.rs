//! Kani bounded proofs for `read_unbuffered`, the loop that reads a password byte by byte into
//! the fixed-size `PamBuffer`. Built only under `cfg(kani)`. The terminal is replaced: the
//! byte source `TimeoutRead::read_byte` (poll + read) by the stubs below, and the terminal
//! settings by arbitrary control characters. Bounds are stated per harness; see
//! proofs/kani/README.md.
// Replacement functions are referenced only from `#[kani::stub]` attributes.
#![allow(dead_code)]

use std::io;
use std::os::fd::BorrowedFd;
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};

use libc::{VEOF, VERASE, VKILL};

use super::{Hidden, HiddenInput, TimeoutRead, read_unbuffered};
use crate::pam::PamError;
use crate::pam::securemem::PamBuffer;

const SIZE: usize = 512;

fn source() -> TimeoutRead<'static> {
    TimeoutRead {
        timeout_at: None,
        // SAFETY: never used: `read_byte` is replaced in every harness.
        fd: unsafe { BorrowedFd::borrow_raw(0) },
    }
}

/// Byte at `i` of the 512-byte allocation behind the buffer (index 511 is outside the slice
/// that `Deref` exposes: it is the C terminator).
fn raw_byte(buf: PamBuffer, i: usize) -> u8 {
    let ptr = buf.leak();
    // SAFETY: `ptr` is the start of a `SIZE`-byte allocation; `i < SIZE` at every call site.
    unsafe {
        let b = *ptr.as_ptr().add(i);
        libc::free(ptr.as_ptr().cast());
        b
    }
}

/// Replaces `read_byte`: an endless supply of arbitrary bytes other than newline/return.
fn read_byte_never_ends<'a>(_: &mut TimeoutRead<'a>) -> io::Result<Option<u8>>
where
    'a: 'a,
{
    let b: u8 = kani::any();
    kani::assume(b != b'\n' && b != b'\r');
    Ok(Some(b))
}

/// F4: input without end that never contains a line end: after 511 stored bytes the next
/// byte is refused with `IncorrectPasswordAttempt`; nothing is written outside the buffer.
#[kani::proof]
#[kani::unwind(514)]
#[kani::stub(TimeoutRead::read_byte, read_byte_never_ends)]
fn read_password_longer_than_buffer_is_refused() {
    let mut sink = Vec::new();
    let res = read_unbuffered(&mut source(), &mut sink, &Hidden::No);
    assert!(matches!(res, Err(PamError::IncorrectPasswordAttempt)));
    assert!(sink.is_empty());
}

const STEPS: usize = 6;
static CALLS: AtomicUsize = AtomicUsize::new(0);
/// Per call: `EV_EOF`, `EV_TIMEOUT`, `EV_IO_ERROR`, or `EV_BYTE` with the byte in `BYTES`.
static EVENTS: [AtomicU8; STEPS] = [const { AtomicU8::new(EV_EOF) }; STEPS];
static BYTES: [AtomicU8; STEPS] = [const { AtomicU8::new(0) }; STEPS];
const EV_EOF: u8 = 0;
const EV_TIMEOUT: u8 = 1;
const EV_IO_ERROR: u8 = 2;
const EV_BYTE: u8 = 3;

/// Replaces `read_byte`: for `STEPS` calls, nondeterministically end of input, a timeout, another
/// I/O error, or an arbitrary byte (each recorded); end of input afterwards.
fn read_byte_scripted<'a>(_: &mut TimeoutRead<'a>) -> io::Result<Option<u8>>
where
    'a: 'a,
{
    let n = CALLS.fetch_add(1, Ordering::SeqCst);
    if n >= STEPS {
        return Ok(None);
    }
    let ev: u8 = kani::any();
    kani::assume(ev <= EV_BYTE);
    EVENTS[n].store(ev, Ordering::SeqCst);
    match ev {
        EV_EOF => Ok(None),
        EV_TIMEOUT => Err(io::Error::from(io::ErrorKind::TimedOut)),
        EV_IO_ERROR => Err(io::Error::from(io::ErrorKind::BrokenPipe)),
        _ => {
            let b: u8 = kani::any();
            BYTES[n].store(b, Ordering::SeqCst);
            Ok(Some(b))
        }
    }
}

enum Expected {
    Password(Vec<u8>),
    NoPassword,
    TimedOut,
    IoError,
}

/// What reading the recorded events must give with echo on (no line editing): the bytes up to
/// the first newline/return, or up to end of input if at least one byte came.
fn expected_plain() -> Expected {
    let mut stored = Vec::new();
    for n in 0..STEPS {
        let ev = EVENTS[n].load(Ordering::SeqCst);
        let b = BYTES[n].load(Ordering::SeqCst);
        match ev {
            EV_TIMEOUT => return Expected::TimedOut,
            EV_IO_ERROR => return Expected::IoError,
            EV_BYTE if b == b'\n' || b == b'\r' => return Expected::Password(stored),
            EV_BYTE => stored.push(b),
            _ => break,
        }
    }
    if stored.is_empty() {
        Expected::NoPassword
    } else {
        Expected::Password(stored)
    }
}

/// F5: echoing input (askpass, or stdin that is not a terminal), up to 6 events: the result is
/// exactly the bytes before the first newline/return or end of input, followed by NULs
/// (checked up to index 8 and at the terminator 511); end of input before any byte gives
/// `NoPasswordProvided`; a timeout gives `TimedOut`, another read error `IoError`.
#[kani::proof]
#[kani::unwind(10)]
#[kani::stub(TimeoutRead::read_byte, read_byte_scripted)]
fn read_password_plain_exact_6_events() {
    let mut sink = Vec::new();
    let res = read_unbuffered(&mut source(), &mut sink, &Hidden::No);
    match (res, expected_plain()) {
        (Ok(buf), Expected::Password(stored)) => {
            for k in 0..9 {
                let expected = if k < stored.len() { stored[k] } else { 0 };
                assert_eq!(buf[k], expected);
            }
            assert_eq!(raw_byte(buf, SIZE - 1), 0);
        }
        (Err(PamError::NoPasswordProvided), Expected::NoPassword) => {}
        (Err(PamError::TimedOut), Expected::TimedOut) => {}
        (Err(PamError::IoError(_)), Expected::IoError) => {}
        _ => panic!("result differs from the expected one"),
    }
    assert!(sink.is_empty());
}

/// F6: hidden input with line editing (any erase, kill and end-of-file characters, with and
/// without `pwfeedback` bullets), up to 6 events of any kind: no index or arithmetic error,
/// nothing written outside the buffer, and the terminator at 511 stays NUL.
#[kani::proof]
#[kani::unwind(12)]
#[kani::stub(TimeoutRead::read_byte, read_byte_scripted)]
fn read_password_hidden_editing_6_events() {
    // SAFETY: an all-zero termios is a valid value of this plain C struct.
    let mut term: libc::termios = unsafe { std::mem::zeroed() };
    term.c_cc[VEOF] = kani::any();
    term.c_cc[VERASE] = kani::any();
    term.c_cc[VKILL] = kani::any();
    let input = HiddenInput {
        // SAFETY: never used: `read_byte` is replaced and the restoring `Drop` is skipped below.
        tty: unsafe { BorrowedFd::borrow_raw(0) },
        term_orig: term,
    };
    let hidden = if kani::any() {
        Hidden::Yes(input)
    } else {
        Hidden::WithFeedback(input)
    };
    // feedback (bullets, erasures) goes to a sink that discards it
    let res = read_unbuffered(&mut source(), &mut io::sink(), &hidden);
    // `HiddenInput::drop` would call tcsetattr on the (fake) terminal.
    std::mem::forget(hidden);
    if let Ok(buf) = res {
        for k in STEPS..STEPS + 3 {
            assert_eq!(buf[k], 0);
        }
        assert_eq!(raw_byte(buf, SIZE - 1), 0);
    }
}
