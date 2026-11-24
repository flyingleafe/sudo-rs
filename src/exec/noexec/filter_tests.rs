//! Checks of the NOEXEC filter that `add_noexec_filter` installs (`super::noexec_filter`, the
//! production bytecode) against its documented dispatch contract for the target these tests are
//! built for, over all 2^64 `(nr, arch)` pairs. Model and assumptions: `filter_model.rs`. No
//! syscall is made and no filter is installed.
//!
//! `cargo test --lib exec::noexec::filter_tests -- --show-output` prints the counts. The
//! exhaustive enumeration is `#[ignore]`d: `cargo test --release --lib
//! exec::noexec::filter_tests -- --ignored --show-output`; `proofs/seccomp/run.sh` runs all.

use std::collections::BTreeMap;
use std::io::Write;
use std::mem::{offset_of, size_of};

use libc::{seccomp_data, sock_filter};

use super::filter_model::{
    ARCH_OFFSET, AUDIT_ARCHES, Action, Constraint, Contract, DOMAIN, NR_OFFSET,
    SECCOMP_RET_USER_NOTIF, TARGETS, check_accepted, count, data_for, paths, run, this_target,
};
use super::noexec_filter;

/// 2^32, the number of values of one 32-bit word.
const WORDS: u128 = 1 << 32;

/// <asm/unistd.h> (x86) `__X32_SYSCALL_BIT`, used here only to pick test points.
const X32_BIT: u32 = 0x4000_0000;

fn contract_name(contract: &Contract) -> &'static str {
    match contract {
        Contract::Known(target) => target.name,
        Contract::Unknown => "unrecognised architecture",
    }
}

/// Whether `(nr, arch)` satisfies `c`.
fn holds(c: &Constraint, nr: u32, arch: u32) -> bool {
    let word = if c.offset == NR_OFFSET { nr } else { arch };
    assert!(c.offset == NR_OFFSET || c.offset == ARCH_OFFSET);
    (word & c.mask == c.value) == c.equal
}

/// The counts the contract implies by arithmetic alone: pairs per prescribed action, and the
/// number of pairs it leaves unconstrained.
fn closed_form(contract: &Contract) -> (BTreeMap<Action, u128>, u128) {
    match contract {
        Contract::Known(target) => {
            let notified: u128 = target
                .abis
                .iter()
                .map(|abi| abi.exec_nrs.len() as u128 * (1u128 << abi.ignored_bits.count_ones()))
                .sum();
            let abis = target.abis.len() as u128;
            let counts = BTreeMap::from([
                (Action::Allow, abis * WORDS - notified),
                (Action::Notify, notified),
                (Action::KillProcess, (WORDS - abis) * WORDS),
            ]);
            (counts, 0)
        }
        Contract::Unknown => (
            BTreeMap::from([(Action::KillProcess, (WORDS - 1) * WORDS)]),
            WORDS,
        ),
    }
}

/// Test points around every constant of `prog` and of the contract tables: each architecture
/// value and syscall number at which a comparison changes its outcome, and neighbours of it.
fn boundary_points(prog: &[sock_filter]) -> (Vec<u32>, Vec<u32>) {
    let program_constants: Vec<u32> = prog.iter().map(|insn| insn.k).collect();
    let mut arch_seeds = program_constants.clone();
    arch_seeds.extend(AUDIT_ARCHES);
    let mut nr_seeds = program_constants;
    for target in &TARGETS {
        for abi in target.abis {
            nr_seeds.extend(abi.exec_nrs);
            nr_seeds.extend(abi.kernel_exec_nrs);
        }
    }
    let mut arches = vec![0, u32::MAX];
    for v in arch_seeds {
        arches.extend([v, v ^ 1]);
    }
    let mut nrs = vec![0, u32::MAX];
    for v in nr_seeds {
        nrs.extend([
            v,
            v ^ 1,
            v | X32_BIT,
            v & !X32_BIT,
            v ^ 0x8000_0000,
            v.wrapping_add(1),
            v.wrapping_sub(1),
        ]);
    }
    for list in [&mut arches, &mut nrs] {
        list.sort_unstable();
        list.dedup();
    }
    (arches, nrs)
}

/// libc's `seccomp_data` and `sock_filter` have the uapi layout the model assumes
/// (<linux/seccomp.h>, <linux/filter.h>).
#[test]
fn uapi_layouts_match_libc() {
    assert_eq!(size_of::<seccomp_data>(), 64);
    assert_eq!(offset_of!(seccomp_data, nr), NR_OFFSET as usize);
    assert_eq!(offset_of!(seccomp_data, arch), ARCH_OFFSET as usize);
    assert_eq!(offset_of!(seccomp_data, instruction_pointer), 8);
    assert_eq!(offset_of!(seccomp_data, args), 16);
    assert_eq!(size_of::<sock_filter>(), 8);
    assert_eq!(offset_of!(sock_filter, code), 0);
    assert_eq!(offset_of!(sock_filter, jt), 2);
    assert_eq!(offset_of!(sock_filter, jf), 3);
    assert_eq!(offset_of!(sock_filter, k), 4);
}

/// The contract tables are well formed for every target, not only this one: distinct
/// architectures, exec numbers free of ignored bits, every syscall number the kernel dispatches
/// to execve/execveat named by the contract, every architecture value non-zero. The regions of
/// every contract partition the 2^64 pairs, give the closed-form counts, and agree with
/// `Contract::expected` on every boundary point.
#[test]
#[cfg_attr(miri, ignore = "target-independent tables; checked in the native run")]
fn contract_tables_are_consistent() {
    let mut sorted = AUDIT_ARCHES.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(sorted.len(), AUDIT_ARCHES.len());
    assert!(!AUDIT_ARCHES.contains(&0));

    let mut contracts: Vec<Contract> = TARGETS.iter().map(Contract::Known).collect();
    contracts.push(Contract::Unknown);
    let (arches, nrs) = boundary_points(&noexec_filter());
    for contract in &contracts {
        let name = contract_name(contract);
        if let Contract::Known(target) = contract {
            for (i, abi) in target.abis.iter().enumerate() {
                assert!(AUDIT_ARCHES.contains(&abi.arch), "{name}: {}", abi.name);
                assert!(target.abis[..i].iter().all(|a| a.arch != abi.arch), "{name}");
                for (j, &nr) in abi.exec_nrs.iter().enumerate() {
                    assert_eq!(nr & abi.ignored_bits, 0, "{name}: {}", abi.name);
                    assert!(!abi.exec_nrs[..j].contains(&nr), "{name}: {}", abi.name);
                }
                for &nr in abi.kernel_exec_nrs {
                    assert_eq!(
                        contract.expected(abi.arch, nr),
                        Some(Action::Notify),
                        "{name}: {} {nr:#x}",
                        abi.name
                    );
                }
            }
        }

        let regions = contract.regions();
        let total: u128 = regions.iter().map(|(cs, _)| count(cs)).sum();
        assert_eq!(total, DOMAIN, "{name}");
        let (expected, unconstrained) = closed_form(contract);
        let mut counts = BTreeMap::new();
        let mut free = 0;
        for (cs, action) in &regions {
            match action {
                Some(action) => *counts.entry(*action).or_insert(0) += count(cs),
                None => free += count(cs),
            }
        }
        assert_eq!(counts, expected, "{name}");
        assert_eq!(free, unconstrained, "{name}");

        for &arch in &arches {
            for &nr in &nrs {
                let containing: Vec<_> = regions
                    .iter()
                    .filter(|(cs, _)| cs.iter().all(|c| holds(c, nr, arch)))
                    .collect();
                assert_eq!(containing.len(), 1, "{name}: arch {arch:#x} nr {nr:#x}");
                assert_eq!(
                    containing[0].1,
                    contract.expected(arch, nr),
                    "{name}: arch {arch:#x} nr {nr:#x}"
                );
            }
        }
    }
}

/// The production filter is a program the kernel accepts, built from the four modelled opcodes.
#[test]
fn filter_is_accepted() {
    let prog = noexec_filter();
    assert_eq!(check_accepted(&prog), Ok(()));
}

/// The syscall numbers the kernel dispatches to execve/execveat, under every architecture the
/// contract accepts for this target, are notified by the production filter.
#[test]
fn kernel_exec_numbers_are_notified() {
    let prog = noexec_filter();
    assert_eq!(check_accepted(&prog), Ok(()));
    if let Contract::Known(target) = this_target() {
        for abi in target.abis {
            for &nr in abi.kernel_exec_nrs {
                assert_eq!(
                    run(&prog, &data_for(abi.arch, nr)),
                    SECCOMP_RET_USER_NOTIF,
                    "{}: {nr:#x}",
                    abi.name
                );
            }
        }
    }
}

/// The symbolic paths of the production filter agree with the concrete interpreter on every
/// boundary point.
#[test]
fn paths_agree_with_interpreter_on_boundary_points() {
    let prog = noexec_filter();
    assert_eq!(check_accepted(&prog), Ok(()));
    let paths = paths(&prog);
    let (arches, nrs) = boundary_points(&prog);
    for &arch in &arches {
        for &nr in &nrs {
            let taking: Vec<_> = paths
                .iter()
                .filter(|p| p.constraints.iter().all(|c| holds(c, nr, arch)))
                .collect();
            assert_eq!(taking.len(), 1, "arch {arch:#x} nr {nr:#x}");
            assert_eq!(
                taking[0].ret,
                run(&prog, &data_for(arch, nr)),
                "arch {arch:#x} nr {nr:#x}"
            );
        }
    }
}

/// Main check: for every `(nr, arch)` pair the production filter returns the action the
/// documented contract prescribes. The filter's paths and the contract's regions each partition
/// the 2^64 pairs; the pairs on which a path and a region with different actions overlap are
/// counted exactly and must be zero. Prints the counts per action and the number of pairs that
/// reach each instruction and take each branch.
#[test]
fn filter_matches_contract_for_every_nr_and_arch() {
    let prog = noexec_filter();
    assert_eq!(check_accepted(&prog), Ok(()));
    let contract = this_target();
    let paths = paths(&prog);
    let regions = contract.regions();

    let on_paths: u128 = paths.iter().map(|p| count(&p.constraints)).sum();
    assert_eq!(on_paths, DOMAIN, "the paths partition the pairs");
    let in_regions: u128 = regions.iter().map(|(cs, _)| count(cs)).sum();
    assert_eq!(in_regions, DOMAIN, "the regions partition the pairs");

    let mut agreed: BTreeMap<Action, u128> = BTreeMap::new();
    let mut unconstrained: BTreeMap<Action, u128> = BTreeMap::new();
    let mut mismatches = Vec::new();
    for path in &paths {
        let got = Action::of_ret(path.ret);
        for (constraints, want) in &regions {
            let both = [path.constraints.as_slice(), constraints.as_slice()].concat();
            let n = count(&both);
            if n == 0 {
                continue;
            }
            match want {
                None => *unconstrained.entry(got).or_insert(0) += n,
                Some(want) if *want == got => *agreed.entry(got).or_insert(0) += n,
                Some(want) => mismatches.push((got, *want, n, both)),
            }
        }
    }

    let mut reached = vec![0u128; prog.len()];
    let mut branches = vec![(0u128, 0u128); prog.len()];
    for path in &paths {
        let n = count(&path.constraints);
        for &pc in &path.trace {
            reached[pc] += n;
        }
        for &(pc, condition) in &path.branches {
            if condition {
                branches[pc].0 += n;
            } else {
                branches[pc].1 += n;
            }
        }
    }

    let mut out = std::io::stdout();
    writeln!(
        out,
        "noexec filter, contract {}: {} instructions, {} paths, {} contract regions",
        contract_name(&contract),
        prog.len(),
        paths.len(),
        regions.len()
    )
    .unwrap();
    for (action, n) in &agreed {
        writeln!(out, "  {action:?}: {n} pairs as prescribed").unwrap();
    }
    for (action, n) in &unconstrained {
        writeln!(out, "  {action:?}: {n} pairs where the contract prescribes nothing").unwrap();
    }
    let mismatching: u128 = mismatches.iter().map(|m| m.2).sum();
    writeln!(out, "  mismatching pairs: {mismatching}").unwrap();
    for (pc, insn) in prog.iter().enumerate() {
        writeln!(
            out,
            "  {pc:2}: code {:#06x} jt {} jf {} k {:#010x}: reached by {} pairs; condition true for {}, false for {}",
            insn.code, insn.jt, insn.jf, insn.k, reached[pc], branches[pc].0, branches[pc].1
        )
        .unwrap();
    }

    assert!(mismatches.is_empty(), "{mismatches:?}");
    let (expected, free) = closed_form(&contract);
    assert_eq!(agreed, expected);
    assert_eq!(unconstrained.values().sum::<u128>(), free);
    assert_eq!(reached[0], DOMAIN);
}

/// Index of an action in the counters of the enumeration.
fn slot(action: Action) -> usize {
    match action {
        Action::Allow => 0,
        Action::Notify => 1,
        Action::KillProcess => 2,
        Action::Other(_) => 3,
    }
}

/// Independent cross-check of the symbolic count: the concrete interpreter on every one of the
/// 2^32 syscall numbers, for every `AUDIT_ARCH_*` value of the contract tables, 0, `u32::MAX`
/// and every constant of the program, against `Contract::expected`.
#[test]
#[ignore = "enumerates 2^32 syscall numbers per architecture value; run in release mode"]
fn filter_matches_contract_for_every_nr_enumerated() {
    let prog = noexec_filter();
    assert_eq!(check_accepted(&prog), Ok(()));
    let contract = this_target();
    let mut arches = AUDIT_ARCHES.to_vec();
    arches.extend([0, u32::MAX]);
    arches.extend(prog.iter().map(|insn| insn.k));
    arches.sort_unstable();
    arches.dedup();
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()) as u64;
    let chunk = (1u64 << 32).div_ceil(threads);
    writeln!(
        std::io::stdout(),
        "noexec filter, contract {}: {} architecture values x 2^32 syscall numbers, {threads} threads",
        contract_name(&contract),
        arches.len()
    )
    .unwrap();
    let mut failures = Vec::new();
    for &arch in &arches {
        let (prog, contract) = (&prog, &contract);
        let parts: Vec<([u64; 4], u64, Option<u32>)> = std::thread::scope(|scope| {
            let workers: Vec<_> = (0..threads)
                .map(|t| {
                    scope.spawn(move || {
                        let mut counts = [0u64; 4];
                        let (mut bad, mut first_bad) = (0u64, None);
                        for nr in t * chunk..((t + 1) * chunk).min(1 << 32) {
                            let nr = nr as u32;
                            let got = Action::of_ret(run(prog, &data_for(arch, nr)));
                            counts[slot(got)] += 1;
                            if contract.expected(arch, nr).is_some_and(|want| want != got) {
                                bad += 1;
                                if first_bad.is_none() {
                                    first_bad = Some(nr);
                                }
                            }
                        }
                        (counts, bad, first_bad)
                    })
                })
                .collect();
            workers.into_iter().map(|w| w.join().unwrap()).collect()
        });
        let mut counts = [0u64; 4];
        let mut bad = 0;
        let mut first_bad = None;
        for (part, part_bad, part_first) in parts {
            for (total, n) in counts.iter_mut().zip(part) {
                *total += n;
            }
            bad += part_bad;
            first_bad = first_bad.or(part_first);
        }
        writeln!(
            std::io::stdout(),
            "  arch {arch:#010x}: allow {} notify {} kill {} other {}; mismatches {bad}",
            counts[0],
            counts[1],
            counts[2],
            counts[3]
        )
        .unwrap();
        assert_eq!(counts.iter().sum::<u64>(), 1 << 32);
        if bad > 0 {
            failures.push((arch, bad, first_bad));
        }
    }
    assert!(failures.is_empty(), "{failures:?}");
}
