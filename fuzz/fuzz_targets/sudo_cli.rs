//! (d) `sudo`'s command line: `SudoAction::try_parse_from` (option normalisation, parsing,
//! validation into an action). Input: the argument vector, NUL-separated, starting with
//! argv[0] (`sudo`, `sudoedit`, ...); arguments may be any bytes, as on Linux.
//!
//! Asserts: no panic; parsing twice gives the same result; the positional arguments of the
//! action (the command and its arguments, or the files to edit) are a contiguous tail of the
//! argument vector, so option processing never rewrites, reorders or drops any of them.
#![no_main]

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;

use libfuzzer_sys::fuzz_target;
use sudo_rs::fuzz_api::sudo_cli;

fuzz_target!(|data: &[u8]| {
    let args: Vec<OsString> = data
        .split(|&b| b == 0)
        .map(|a| OsString::from_vec(a.to_vec()))
        .collect();

    let result = sudo_cli(&args);
    assert_eq!(sudo_cli(&args), result, "parsing is not deterministic");

    if let Ok((_, positional)) = &result {
        assert!(
            args[1..].ends_with(positional),
            "positional arguments are not a tail of the input: {positional:?}"
        );
    }
});
