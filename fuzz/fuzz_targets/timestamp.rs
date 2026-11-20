//! (g) Timestamp (credential cache) records and files, `src/system/timestamp.rs`.
//!
//! Input byte 0 selects the mode:
//! - even: the rest is one record for `SessionRecord::from_bytes`; a decoded record is
//!   re-encoded with `as_bytes`. Asserts: no panic; the re-encoding has the input's length and
//!   decodes and re-encodes to itself.
//! - odd: byte 1 is the number of operations (at most 8), the next bytes the operations (bits
//!   0-1: touch, create, disable; bits 2-3: one of four scope/user keys), the rest the file
//!   contents. The contents go into a memfd that is opened with `SessionRecordFile::new` (the
//!   header check and repair `sudo` applies to `/var/run/sudo-rs/ts/<uid>`); then the operations
//!   run. Asserts: no panic; right after a successful `create` for a key, `touch` for that key
//!   finds a fresh record (`Updated`); right after a successful `disable` of a scope, `touch`
//!   finds no record for it.
#![no_main]

use std::fs::File;
use std::io::{Seek, Write};
use std::os::fd::FromRawFd;
use std::time::Duration;

use libfuzzer_sys::fuzz_target;
use sudo_rs::fuzz_api::{
    TimestampFile, TimestampKey, TimestampOp, TimestampOutcome, timestamp_record,
};

const KEYS: [TimestampKey; 4] = [
    TimestampKey { tty: true, pid: 0x8801, session: 100, start_secs: 1000, start_nsecs: 5, auth_uid: 1000 },
    TimestampKey { tty: true, pid: 0x8801, session: 100, start_secs: 1000, start_nsecs: 5, auth_uid: 0 },
    TimestampKey { tty: false, pid: 200, session: 100, start_secs: 2000, start_nsecs: 0, auth_uid: 1000 },
    TimestampKey { tty: true, pid: 0x8802, session: 300, start_secs: 3000, start_nsecs: 999_999_999, auth_uid: 1000 },
];

fn memfd(contents: &[u8]) -> File {
    // SAFETY: memfd_create gets a NUL-terminated name; the returned descriptor is owned by
    // the File from here on
    let fd = unsafe { libc::memfd_create(c"timestamp".as_ptr(), libc::MFD_CLOEXEC) };
    assert!(fd >= 0, "memfd_create failed");
    // SAFETY: fd is a fresh descriptor that nothing else owns
    let mut file = unsafe { File::from_raw_fd(fd) };
    file.write_all(contents).expect("writing a memfd");
    // sudo opens the file afresh: start reading at the beginning
    file.rewind().expect("rewinding a memfd");
    file
}

fuzz_target!(|data: &[u8]| {
    let Some((&mode, rest)) = data.split_first() else {
        return;
    };

    if mode % 2 == 0 {
        if let Ok(encoded) = timestamp_record(rest) {
            assert_eq!(encoded.len(), rest.len(), "re-encoding changed the length");
            assert_eq!(
                timestamp_record(&encoded).ok().as_ref(),
                Some(&encoded),
                "re-encoding is not stable"
            );
        }
        return;
    }

    let Some((&count, rest)) = rest.split_first() else {
        return;
    };
    let count = usize::from(count % 9).min(rest.len());
    let (ops, contents) = rest.split_at(count);

    let file = memfd(contents);
    let Ok(mut records) = TimestampFile::open(1000, file, Duration::from_secs(15 * 60)) else {
        return;
    };

    for &op in ops {
        let key = &KEYS[usize::from((op >> 2) & 3)];
        let op = match op & 3 {
            0 => TimestampOp::Touch,
            1 => TimestampOp::Create,
            _ => TimestampOp::Disable,
        };
        let Ok(_) = records.apply(op, key) else {
            break;
        };
        match op {
            TimestampOp::Create => {
                let touched = records.apply(TimestampOp::Touch, key);
                assert_eq!(touched.ok(), Some(TimestampOutcome::Updated), "create then touch");
            }
            TimestampOp::Disable => {
                let touched = records.apply(TimestampOp::Touch, key);
                assert_eq!(touched.ok(), Some(TimestampOutcome::NotFound), "disable then touch");
            }
            TimestampOp::Touch => {}
        }
    }
});
