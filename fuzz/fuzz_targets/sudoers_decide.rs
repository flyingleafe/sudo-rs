//! (b) Policy text plus a request, end to end: `Sudoers::read`, then `Sudoers::check`
//! (`sudo <command>`), `check_validate_permission` (`sudo -v`), `check_list_permission`
//! (`sudo -l`, `sudo -l -U`) and the `sudo -l`/`sudo -ll` listing (`matching_entries`).
//! Input format: see `common.rs`.
//!
//! Asserts: no panic; deciding twice gives the same result; a command that may be run implies
//! that `sudo -v` is allowed; `sudo -l` of one's own permissions is allowed exactly when
//! `sudo -v` is; root, and a user who neither changes user nor leaves their groups, are not
//! asked for a password.
#![no_main]

mod common;

use libfuzzer_sys::fuzz_target;
use sudo_rs::fuzz_api::sudoers_decide;

fuzz_target!(|data: &[u8]| {
    let Some(input) = common::decision_input(data) else {
        return;
    };

    let decision = sudoers_decide(&input);
    assert_eq!(sudoers_decide(&input), decision, "deciding is not deterministic");

    if decision.run.is_some() {
        assert!(decision.validate.is_some(), "may run a command but not `sudo -v`");
    }
    assert_eq!(
        decision.list_self.is_some(),
        decision.validate.is_some(),
        "`sudo -l` and `sudo -v` disagree"
    );

    if let Some((auth, _)) = &decision.run {
        let am = &input.invoking_user;
        let stays = input.target_user == *am && common::in_group(am, &input.target_group);
        if am.uid == 0 || stays {
            assert!(!auth.must_authenticate, "password asked of root or without a switch");
        }
    }
});
