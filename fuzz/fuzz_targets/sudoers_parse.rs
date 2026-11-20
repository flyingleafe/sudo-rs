//! (a) The sudoers file on arbitrary bytes, on the path the binaries take after opening it:
//! `Sudoers::read` = read as UTF-8, `parse_lines`, `analyze` (aliases, includes, Defaults).
//!
//! Asserts: no panic; invalid UTF-8 is the only read error; every diagnostic location of the
//! fuzzed file satisfies what `sudo::diagnostic::cited_error` computes with it (`line - 1`,
//! `col - 1`, and `end_col - col` when the span stays on one line); reading twice gives the
//! same diagnostics.
#![no_main]

use std::path::Path;

use libfuzzer_sys::fuzz_target;
use sudo_rs::fuzz_api::{SUDOERS_PATH, sudoers_read};

fuzz_target!(|data: &[u8]| {
    let diagnostics = match sudoers_read(data) {
        Ok(diagnostics) => diagnostics,
        Err(_) => {
            assert!(std::str::from_utf8(data).is_err(), "read error on UTF-8 input");
            return;
        }
    };

    for d in &diagnostics {
        if d.source.as_deref() != Some(Path::new(SUDOERS_PATH)) {
            continue;
        }
        if let Some(((line, col), (end_line, end_col))) = d.span {
            assert!(line >= 1 && col >= 1, "position before the start: {d:?}");
            assert!(
                line != end_line || end_col >= col,
                "span ends before it starts: {d:?}"
            );
        }
    }

    assert_eq!(sudoers_read(data).ok(), Some(diagnostics), "reading is not deterministic");
});
