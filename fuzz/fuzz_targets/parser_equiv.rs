//! The restricted-style sudoers parser against the legacy parser it replaced, on arbitrary
//! bytes (`fuzz_api::sudoers_parser_equiv`, `src/sudoers/equiv.rs`).
//!
//! Asserts: on every UTF-8 text, both `parse_lines::<Sudo>` give the same items, spans and
//! message texts, and every `Defaults` modifier has the same effect on two base settings.
#![no_main]

use libfuzzer_sys::fuzz_target;
use sudo_rs::fuzz_api::sudoers_parser_equiv;

fuzz_target!(|data: &[u8]| {
    if let Err(difference) = sudoers_parser_equiv(data) {
        panic!("the parsers differ:\n{difference}");
    }
});
