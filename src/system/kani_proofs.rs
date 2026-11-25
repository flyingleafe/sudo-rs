//! The real credential drivers, instantiated with fixed-width errors and a local trace.
//! The native adapter (syscalls, errno, and process state) is outside this model. Group
//! preparation is checked separately, with constant capacity and no symbolic allocation.

use std::cell::Cell;

use super::{
    CredentialOps, Credentials, GroupId, TemporaryCredentialOps, UserId, apply_credentials,
    inject_group, with_temporary_credentials,
};

const SNAPSHOT: u64 = 1;
const PREPARE: u64 = 2;
const GROUPS: u64 = 3;
const GID: u64 = 4;
const UID: u64 = 5;
const OPERATION: u64 = 6;
const READ_ERROR: u8 = 1;
const SWITCH_ERROR: u8 = 2;
const RESTORE_ERROR: u8 = 3;
const NO_FAILURE: u8 = 3;

fn with_group_capacity(groups: &[GroupId]) -> Vec<GroupId> {
    let mut prepared = Vec::with_capacity(3);
    for &gid in groups {
        prepared.push(gid);
    }
    prepared
}

#[kani::proof]
#[kani::unwind(5)]
fn inject_group_empty() {
    let target = GroupId::new(kani::any());
    let mut prepared = with_group_capacity(&[]);
    inject_group(target, &mut prepared);
    assert!(prepared.as_slice() == [target]);
    kani::cover!(prepared.len() == 1, "inserted into empty groups");
}

#[kani::proof]
#[kani::unwind(5)]
fn inject_group_one_entry() {
    let target = GroupId::new(kani::any());
    let existing = GroupId::new(kani::any());
    let mut prepared = with_group_capacity(&[existing]);
    inject_group(target, &mut prepared);
    if existing == target {
        assert!(prepared.as_slice() == [target]);
        kani::cover!(true, "already first");
    } else {
        assert!(prepared.as_slice() == [target, existing]);
        kani::cover!(true, "new target group");
    }
}

#[kani::proof]
#[kani::unwind(5)]
fn inject_group_two_entries() {
    let target = GroupId::new(kani::any());
    let first = GroupId::new(kani::any());
    let second = GroupId::new(kani::any());
    let mut prepared = with_group_capacity(&[first, second]);
    inject_group(target, &mut prepared);
    if first == target {
        assert!(prepared.as_slice() == [first, second]);
        kani::cover!(first == second, "duplicates preserved");
    } else if second == target {
        assert!(prepared.as_slice() == [target, first]);
        kani::cover!(true, "existing target group swapped to front");
    } else {
        assert!(prepared.as_slice() == [target, first, second]);
        kani::cover!(true, "new target group prepended");
    }
}

fn append(trace: &Cell<u64>, event: u64) {
    trace.set((trace.get() << 4) | event);
}

struct Model<'a, F> {
    trace: &'a Cell<u64>,
    target: Credentials<&'a [GroupId]>,
    previous: Credentials<&'a [GroupId]>,
    read_fails: bool,
    /// The first failing switch/restore setter (0..=2), or NO_FAILURE.
    switch_failure: u8,
    restore_failure: u8,
    witness_restore_failure: F,
    calls: u8,
}

impl<'a, F: Fn(u8, u8)> Model<'a, F> {
    fn new(
        trace: &'a Cell<u64>,
        target: Credentials<&'a [GroupId]>,
        previous: Credentials<&'a [GroupId]>,
        witness_restore_failure: F,
    ) -> Self {
        Self {
            trace,
            target,
            previous,
            read_fails: false,
            switch_failure: NO_FAILURE,
            restore_failure: NO_FAILURE,
            witness_restore_failure,
            calls: 0,
        }
    }

    fn switch_calls(&self) -> u8 {
        (self.switch_failure + 1).min(3)
    }

    fn expected(&self) -> &Credentials<&'a [GroupId]> {
        if self.calls < self.switch_calls() {
            &self.target
        } else {
            &self.previous
        }
    }

    fn record(&mut self, event: u64) -> Result<(), u8> {
        kani::assert(self.calls < 6, "too many credential calls");
        append(self.trace, event);
        let call = self.calls;
        self.calls += 1;
        let switch_calls = self.switch_calls();
        if call < switch_calls && call == self.switch_failure {
            Err(SWITCH_ERROR)
        } else if call >= switch_calls && call - switch_calls == self.restore_failure {
            Err(RESTORE_ERROR)
        } else {
            Ok(())
        }
    }

    fn run(&mut self, value: u8) -> Result<u8, u8> {
        let trace = self.trace;
        let target = Credentials {
            uid: self.target.uid,
            gid: self.target.gid,
            groups: self.target.groups,
        };
        let previous = Credentials {
            uid: self.previous.uid,
            gid: self.previous.gid,
            groups: self.previous.groups,
        };
        with_temporary_credentials(
            self,
            |snapshot| {
                kani::assert(trace.get() == 0x1, "prepare after snapshot");
                kani::assert(snapshot.uid == previous.uid, "snapshot uid");
                kani::assert(snapshot.gid == previous.gid, "snapshot gid");
                kani::assert(snapshot.groups == previous.groups, "snapshot groups");
                append(trace, PREPARE);
                Some(target)
            },
            || {
                kani::assert(trace.get() == 0x1_2345, "switch before operation");
                append(trace, OPERATION);
                value
            },
        )
    }

    fn before_restore(&self) -> u64 {
        match self.switch_failure {
            0 => 0x123,
            1 => 0x1234,
            2 => 0x1_2345,
            _ => 0x12_3456,
        }
    }
}

impl<F: Fn(u8, u8)> CredentialOps for Model<'_, F> {
    type Error = u8;

    fn set_groups(&mut self, groups: &[GroupId]) -> Result<(), Self::Error> {
        kani::assert(groups == self.expected().groups, "wrong groups");
        self.record(GROUPS)
    }

    fn set_gid(&mut self, gid: GroupId) -> Result<(), Self::Error> {
        kani::assert(gid == self.expected().gid, "wrong gid");
        self.record(GID)
    }

    fn set_uid(&mut self, uid: UserId) -> Result<(), Self::Error> {
        kani::assert(uid == self.expected().uid, "wrong uid");
        self.record(UID)
    }
}

impl<'a, F: Fn(u8, u8)> TemporaryCredentialOps for Model<'a, F> {
    type Groups = &'a [GroupId];

    fn snapshot(&mut self) -> Result<Credentials<Self::Groups>, Self::Error> {
        append(self.trace, SNAPSHOT);
        if self.read_fails {
            Err(READ_ERROR)
        } else {
            Ok(Credentials {
                uid: self.previous.uid,
                gid: self.previous.gid,
                groups: self.previous.groups,
            })
        }
    }

    fn restore_failed(&mut self, error: Self::Error) -> ! {
        kani::assert(error == RESTORE_ERROR, "wrong restore error");
        let suffix = match self.restore_failure {
            0 => 0x5,
            1 => 0x54,
            _ => 0x543,
        };
        let bits = 4 * (self.restore_failure + 1);
        let expected = (self.before_restore() << bits) | suffix;
        kani::assert(self.trace.get() == expected, "restore did not stop at failure");
        (self.witness_restore_failure)(self.switch_failure, self.restore_failure);
        panic!("restore rejected");
    }
}

fn any_group_buffer() -> [GroupId; 3] {
    [
        GroupId::new(kani::any()),
        GroupId::new(kani::any()),
        GroupId::new(kani::any()),
    ]
}

fn any_credentials(groups: &[GroupId]) -> Credentials<&[GroupId]> {
    let len: usize = kani::any();
    kani::assume(len <= groups.len());
    Credentials {
        uid: UserId::new(kani::any()),
        gid: GroupId::new(kani::any()),
        groups: &groups[..len],
    }
}

fn any_failure_index() -> u8 {
    let choice: u8 = kani::any();
    choice & 0b11
}

/// The pre-exec switch over a prepared list of 0..=3 arbitrary gids, all uid/gid values,
/// and any first failure. Later failures are immaterial because no later call is made.
#[kani::proof]
#[kani::unwind(5)]
fn credential_application_order_and_fail_stop() {
    let trace = Cell::new(0);
    let group_buffer = any_group_buffer();
    let target = any_credentials(&group_buffer);
    let (uid, gid, groups) = (target.uid, target.gid, target.groups);
    let mut ops = Model::new(&trace, target, any_credentials(&[]), |_, _| {});
    ops.switch_failure = any_failure_index();

    let result = apply_credentials(&mut ops, uid, gid, groups);
    let (expected, result_expected) = match ops.switch_failure {
        0 => (0x3, Err(SWITCH_ERROR)),
        1 => (0x34, Err(SWITCH_ERROR)),
        2 => (0x345, Err(SWITCH_ERROR)),
        _ => (0x345, Ok(())),
    };
    assert!(result == result_expected && trace.get() == expected);
    kani::cover!(result.is_ok() && groups.len() == 3, "all three setters succeed");
    kani::cover!(ops.switch_failure == 0, "setgroups fails");
    kani::cover!(ops.switch_failure == 1, "setgid fails");
    kani::cover!(ops.switch_failure == 2, "setuid fails");
}

/// Read, prepare, apply, operate, restore. Bounded to 3 target groups and 2 previous groups,
/// arbitrary ids and operation result, either snapshot failure or success, any first switch
/// failure or none. Restoration succeeds in this harness.
#[kani::proof]
#[kani::unwind(5)]
fn temporary_credentials_switch_and_restore() {
    let trace = Cell::new(0);
    let target_groups = any_group_buffer();
    let previous_groups = any_group_buffer();
    let target = any_credentials(&target_groups);
    let previous = any_credentials(&previous_groups[..2]);
    let value = kani::any();
    let mut ops = Model::new(&trace, target, previous, |_, _| {});
    ops.read_fails = kani::any();
    ops.switch_failure = any_failure_index();

    let result = ops.run(value);
    if ops.read_fails {
        assert!(result == Err(READ_ERROR) && trace.get() == 0x1);
        kani::cover!(true, "snapshot fails, no switch or operation");
    } else {
        let expected = (ops.before_restore() << 12) | 0x543;
        assert!(trace.get() == expected);
        if ops.switch_failure == NO_FAILURE {
            assert!(result == Ok(value));
            kani::cover!(true, "operation runs and credentials restored");
        } else {
            assert!(result == Err(SWITCH_ERROR));
            kani::cover!(ops.switch_failure == 0, "group switch fails, restored");
            kani::cover!(ops.switch_failure == 1, "gid switch fails, restored");
            kani::cover!(ops.switch_failure == 2, "uid switch fails, restored");
        }
    }
}

/// Same bound as the previous harness, with snapshot success and a failure at any restore
/// setter. Checks the exact prefix and error in `restore_failed` and forbids normal return.
/// The model terminates with a panic; it does not model a later Rust stack unwind.
#[kani::proof]
#[kani::should_panic]
#[kani::unwind(5)]
fn temporary_credentials_restore_is_fail_stop() {
    let trace = Cell::new(0);
    let target_groups = any_group_buffer();
    let previous_groups = any_group_buffer();
    let target = any_credentials(&target_groups);
    let previous = any_credentials(&previous_groups[..2]);
    // Keep these covers at the failure path, but only in the harness that permits it.
    let mut ops = Model::new(&trace, target, previous, |switch, restore| {
        kani::cover!(restore == 0, "restore uid fails");
        kani::cover!(restore == 1, "restore gid fails");
        kani::cover!(restore == 2, "restore groups fails");
        kani::cover!(switch == NO_FAILURE, "failure after operation");
        kani::cover!(switch != NO_FAILURE, "failure after failed switch");
    });
    ops.switch_failure = any_failure_index();
    ops.restore_failure = any_failure_index();
    kani::assume(ops.restore_failure != NO_FAILURE);

    let _ = ops.run(0);
    kani::assert(false, "returned after a failed restore");
}
