//! (f) `visudo`'s command line: `VisudoOptions::parse_arguments`, a parser separate from
//! those of `sudo` and `su`. Input: the argument vector, NUL-separated, starting with argv[0];
//! `visudo` reads its arguments with `std::env::args`, so they are UTF-8 (other inputs are
//! skipped).
//!
//! Asserts: no panic; parsing twice gives the same result.
#![no_main]

use libfuzzer_sys::fuzz_target;
use sudo_rs::fuzz_api::visudo_cli;

fuzz_target!(|data: &[u8]| {
    let Ok(text) = std::str::from_utf8(data) else {
        return;
    };
    let args: Vec<String> = text.split('\0').map(str::to_owned).collect();

    let result = visudo_cli(args.clone());
    assert_eq!(visudo_cli(args), result, "parsing is not deterministic");
});
