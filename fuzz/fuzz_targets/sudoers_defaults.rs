//! (c) `Defaults` and the settings they produce. The policy text (format: see `common.rs`) is
//! followed by a rule that allows everything, so the decision exposes the settings; the
//! `Defaults` modifiers (generic, `@host`, `:user`, `>runas`, `!command`) are applied by
//! `Sudoers::check`, and the settings are read back the way the binaries read them
//! (`Judgement::authorization`, `Sudoers::search_path`, `visudo_editor_path`).
//!
//! Asserts: no panic; applying the same policy twice gives the same settings; the password
//! attempts stay within the `passwd_tries` range 0..=1000.
#![no_main]

mod common;

use libfuzzer_sys::fuzz_target;
use sudo_rs::fuzz_api::sudoers_settings;

fuzz_target!(|data: &[u8]| {
    let Some(mut input) = common::decision_input(data) else {
        return;
    };
    input.policy.push_str("\nALL ALL=(ALL:ALL) ALL\n");

    let outcome = sudoers_settings(&input);
    assert_eq!(sudoers_settings(&input), outcome, "settings are not deterministic");

    if let Some((auth, _)) = &outcome.decision {
        assert!(auth.allowed_attempts <= 1000, "passwd_tries out of range: {auth:?}");
    }
});
