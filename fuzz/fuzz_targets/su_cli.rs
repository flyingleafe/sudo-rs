//! (e) `su`'s command line: `SuOptions::parse_arguments` and `validate` (what
//! `SuAction::from_env` runs). Input: the argument vector, NUL-separated, starting with
//! argv[0]; `su` reads its arguments with `std::env::args`, so they are UTF-8 (other inputs
//! are skipped).
//!
//! Asserts: no panic; parsing twice gives the same result; for a run, the target user (unless
//! it is the default `root`) and the arguments for the shell occur in the input in this order.
#![no_main]

use libfuzzer_sys::fuzz_target;
use sudo_rs::fuzz_api::su_cli;

fuzz_target!(|data: &[u8]| {
    let Ok(text) = std::str::from_utf8(data) else {
        return;
    };
    let args: Vec<String> = text.split('\0').map(str::to_owned).collect();

    let result = su_cli(args.clone());
    assert_eq!(su_cli(args.clone()), result, "parsing is not deterministic");

    if let Ok((_, positional)) = &result {
        let mut input = args[1..].iter();
        for (i, p) in positional.iter().enumerate() {
            let found = input.any(|a| a == p);
            assert!(
                found || (i == 0 && p == "root"),
                "positional argument {p:?} is not in the input in order"
            );
        }
    }
});
