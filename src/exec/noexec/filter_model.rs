//! Model of the NOEXEC seccomp filter, used by the unit tests in `filter_tests.rs` and the Kani
//! harnesses in `kani_proofs.rs`; built only under `cfg(test)` or `cfg(kani)`.
//!
//! Nothing here is taken from `super` or from the libc constants the filter is built with. Every
//! number is written out from the Linux uapi headers and syscall tables named next to it:
//!
//! - the classic BPF semantics the kernel gives a seccomp filter (`check_accepted`, `run`),
//!   restricted to the four instructions the model executes;
//! - the documented dispatch contract per target (`Contract`), from the comments on
//!   `HOST_ARCH`, `GUEST_ARCH` and the filter in `noexec.rs`;
//! - a symbolic execution of a program over the 32-bit words it loads (`paths`) and an exact
//!   count of the `(nr, arch)` pairs that satisfy a conjunction of masked comparisons (`count`),
//!   so a check covers all 2^64 pairs without enumerating them.
//!
//! Assumptions (not checked here): the kernel runs the filter as classic BPF on a `seccomp_data`
//! laid out as in <linux/seccomp.h> in native byte order, the accumulator starts at 0, a 32-bit
//! load at offset 0 yields the bit pattern of `nr` and at offset 4 the `arch` value; the action is
//! the return value's upper 16 bits (no other filter is installed); the kernel dispatches a
//! syscall on the same 32-bit number the filter sees; `arch` is never 0 (every `AUDIT_ARCH_*`
//! value contains a non-zero ELF machine number).
#![cfg_attr(kani, allow(dead_code))]

use libc::sock_filter;

// <linux/bpf_common.h>, <linux/filter.h>: the opcodes the model executes. Class: BPF_LD 0x00,
// BPF_ALU 0x04, BPF_JMP 0x05, BPF_RET 0x06; size BPF_W 0x00; mode BPF_ABS 0x20; ALU op BPF_AND
// 0x50; jump op BPF_JEQ 0x10; source BPF_K 0x00.
/// `BPF_LD | BPF_W | BPF_ABS`: A = 32-bit word of `seccomp_data` at offset k.
const LD_W_ABS: u16 = 0x20;
/// `BPF_ALU | BPF_AND | BPF_K`: A &= k.
const ALU_AND_K: u16 = 0x54;
/// `BPF_JMP | BPF_JEQ | BPF_K`: skip jt instructions if A == k, else jf.
const JMP_JEQ_K: u16 = 0x15;
/// `BPF_RET | BPF_K`: return k.
const RET_K: u16 = 0x06;
/// <linux/bpf_common.h> `BPF_MAXINSNS`.
const BPF_MAXINSNS: usize = 4096;

// <linux/seccomp.h>
/// `sizeof(struct seccomp_data)`.
pub const SECCOMP_DATA_SIZE: usize = 64;
/// Offset of `seccomp_data.nr`.
pub const NR_OFFSET: u32 = 0;
/// Offset of `seccomp_data.arch`.
pub const ARCH_OFFSET: u32 = 4;
pub const SECCOMP_RET_KILL_PROCESS: u32 = 0x8000_0000;
pub const SECCOMP_RET_USER_NOTIF: u32 = 0x7fc0_0000;
pub const SECCOMP_RET_ALLOW: u32 = 0x7fff_0000;

/// What the kernel does with a syscall, by the filter's return value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Action {
    Allow,
    Notify,
    KillProcess,
    /// Any other return value (another action, or one of these with data bits set).
    Other(u32),
}

impl Action {
    pub fn of_ret(ret: u32) -> Action {
        match ret {
            SECCOMP_RET_ALLOW => Action::Allow,
            SECCOMP_RET_USER_NOTIF => Action::Notify,
            SECCOMP_RET_KILL_PROCESS => Action::KillProcess,
            other => Action::Other(other),
        }
    }
}

/// Why `check_accepted` refuses a program.
#[derive(Debug, PartialEq, Eq)]
pub enum Reject {
    /// Empty or longer than `BPF_MAXINSNS`.
    Length(usize),
    /// An opcode outside the four the model executes.
    Opcode { pc: usize, code: u16 },
    /// A load that is not 4-byte aligned inside `seccomp_data`.
    LoadOffset { pc: usize, k: u32 },
    /// A jump target at or past the end of the program.
    Jump { pc: usize },
    /// The last instruction is not a return.
    NoFinalReturn,
}

/// The kernel's conditions for accepting a seccomp filter (`bpf_check_classic` and
/// `seccomp_check_filter` in the Linux sources), for programs made of the four opcodes the model
/// executes; any other opcode is refused here as outside the model. An accepted program
/// terminates on every input: every jump goes forward and stays inside the program, which ends
/// with a return.
pub fn check_accepted(prog: &[sock_filter]) -> Result<(), Reject> {
    if prog.is_empty() || prog.len() > BPF_MAXINSNS {
        return Err(Reject::Length(prog.len()));
    }
    for (pc, insn) in prog.iter().enumerate() {
        match insn.code {
            LD_W_ABS => {
                if insn.k as usize >= SECCOMP_DATA_SIZE || insn.k & 3 != 0 {
                    return Err(Reject::LoadOffset { pc, k: insn.k });
                }
            }
            ALU_AND_K | RET_K => {}
            JMP_JEQ_K => {
                if pc + 1 + usize::from(insn.jt.max(insn.jf)) >= prog.len() {
                    return Err(Reject::Jump { pc });
                }
            }
            code => return Err(Reject::Opcode { pc, code }),
        }
    }
    if prog[prog.len() - 1].code != RET_K {
        return Err(Reject::NoFinalReturn);
    }
    Ok(())
}

/// The `seccomp_data` of a syscall `nr` (as its 32-bit pattern) under `arch`; the instruction
/// pointer and arguments are zero.
pub fn data_for(arch: u32, nr: u32) -> [u8; SECCOMP_DATA_SIZE] {
    let mut data = [0u8; SECCOMP_DATA_SIZE];
    data[0..4].copy_from_slice(&nr.to_ne_bytes());
    data[4..8].copy_from_slice(&arch.to_ne_bytes());
    data
}

/// The 32-bit word of `data` at `offset`, in native byte order.
pub fn word(data: &[u8; SECCOMP_DATA_SIZE], offset: usize) -> u32 {
    u32::from_ne_bytes([
        data[offset],
        data[offset + 1],
        data[offset + 2],
        data[offset + 3],
    ])
}

/// The return value of `prog` on `data`. Precondition: `check_accepted(prog)` is `Ok`.
pub fn run(prog: &[sock_filter], data: &[u8; SECCOMP_DATA_SIZE]) -> u32 {
    let mut acc: u32 = 0;
    let mut pc = 0;
    loop {
        let insn = &prog[pc];
        match insn.code {
            LD_W_ABS => acc = word(data, insn.k as usize),
            ALU_AND_K => acc &= insn.k,
            JMP_JEQ_K => pc += usize::from(if acc == insn.k { insn.jt } else { insn.jf }),
            RET_K => return insn.k,
            code => panic!("opcode {code:#x} at {pc} is outside the model"),
        }
        pc += 1;
    }
}

/// `(word at offset & mask) == value` if `equal`, else `!=`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Constraint {
    pub offset: u32,
    pub mask: u32,
    pub value: u32,
    pub equal: bool,
}

impl Constraint {
    fn word_is(offset: u32, mask: u32, value: u32, equal: bool) -> Constraint {
        Constraint {
            offset,
            mask,
            value,
            equal,
        }
    }
}

/// The size of the counted domain: all `(nr, arch)` pairs.
pub const DOMAIN: u128 = 1 << 64;

/// The number of `(nr, arch)` pairs, out of `DOMAIN`, that satisfy every constraint. Panics on
/// a constraint on another word: a program that reads one is outside the checked domain.
pub fn count(constraints: &[Constraint]) -> u128 {
    assert!(
        constraints
            .iter()
            .all(|c| c.offset == NR_OFFSET || c.offset == ARCH_OFFSET),
        "a constraint on a word other than nr and arch: {constraints:?}"
    );
    count_word(constraints, NR_OFFSET) * count_word(constraints, ARCH_OFFSET)
}

/// The number of 32-bit words satisfying the constraints on `offset`: inclusion-exclusion over
/// the disequalities, each term a conjunction of masked equalities.
fn count_word(constraints: &[Constraint], offset: u32) -> u128 {
    let equalities: Vec<&Constraint> = constraints
        .iter()
        .filter(|c| c.offset == offset && c.equal)
        .collect();
    let disequalities: Vec<&Constraint> = constraints
        .iter()
        .filter(|c| c.offset == offset && !c.equal)
        .collect();
    assert!(disequalities.len() <= 20, "too many disequalities to count");
    let mut total: i128 = 0;
    for subset in 0u32..(1 << disequalities.len()) {
        let mut chosen = equalities.clone();
        for (i, &c) in disequalities.iter().enumerate() {
            if subset & (1 << i) != 0 {
                chosen.push(c);
            }
        }
        let n = i128::try_from(solutions(&chosen)).expect("at most 2^32");
        if subset.count_ones() % 2 == 0 {
            total += n;
        } else {
            total -= n;
        }
    }
    u128::try_from(total).expect("inclusion-exclusion yields a count")
}

/// The number of 32-bit words `x` with `x & mask == value` for every given constraint (their
/// `equal` flag is ignored): 0 if two of them disagree on a shared bit or a value has a bit
/// outside its mask, otherwise one per assignment of the bits no mask fixes.
fn solutions(equalities: &[&Constraint]) -> u128 {
    let (mut mask, mut value) = (0u32, 0u32);
    for c in equalities {
        if c.value & !c.mask != 0 || (value ^ c.value) & mask & c.mask != 0 {
            return 0;
        }
        mask |= c.mask;
        value |= c.value;
    }
    1u128 << (32 - mask.count_ones())
}

/// One path through a program: the inputs that take it and what it returns.
#[derive(Clone, Debug)]
pub struct Path {
    pub constraints: Vec<Constraint>,
    pub ret: u32,
    /// The instructions executed, in order.
    pub trace: Vec<usize>,
    /// Each conditional jump executed and whether its condition held.
    pub branches: Vec<(usize, bool)>,
}

/// The accumulator during symbolic execution.
#[derive(Clone, Copy)]
enum Acc {
    Const(u32),
    /// The word at `offset` of the input, masked.
    Word { offset: u32, mask: u32 },
}

/// Every feasible path of an accepted program, by symbolic execution over the loaded words.
/// The paths' constraint sets are pairwise contradictory (they split at a comparison) and an
/// infeasible branch (count 0) is dropped. Precondition: `check_accepted(prog)` is `Ok`.
pub fn paths(prog: &[sock_filter]) -> Vec<Path> {
    let start = Path {
        constraints: Vec::new(),
        ret: 0,
        trace: Vec::new(),
        branches: Vec::new(),
    };
    let mut pending = vec![(0usize, Acc::Const(0), start)];
    let mut done = Vec::new();
    while let Some((mut pc, mut acc, mut path)) = pending.pop() {
        loop {
            path.trace.push(pc);
            let insn = &prog[pc];
            match insn.code {
                LD_W_ABS => {
                    acc = Acc::Word {
                        offset: insn.k,
                        mask: u32::MAX,
                    };
                }
                ALU_AND_K => {
                    acc = match acc {
                        Acc::Const(c) => Acc::Const(c & insn.k),
                        Acc::Word { offset, mask } => Acc::Word {
                            offset,
                            mask: mask & insn.k,
                        },
                    };
                }
                JMP_JEQ_K => match acc {
                    Acc::Const(c) => {
                        let holds = c == insn.k;
                        path.branches.push((pc, holds));
                        pc += usize::from(if holds { insn.jt } else { insn.jf });
                    }
                    Acc::Word { offset, mask } => {
                        let mut taken = path.clone();
                        taken
                            .constraints
                            .push(Constraint::word_is(offset, mask, insn.k, true));
                        taken.branches.push((pc, true));
                        if count(&taken.constraints) > 0 {
                            pending.push((pc + 1 + usize::from(insn.jt), acc, taken));
                        }
                        path.constraints
                            .push(Constraint::word_is(offset, mask, insn.k, false));
                        path.branches.push((pc, false));
                        if count(&path.constraints) == 0 {
                            break;
                        }
                        pc += usize::from(insn.jf);
                    }
                },
                RET_K => {
                    path.ret = insn.k;
                    done.push(path);
                    break;
                }
                code => panic!("opcode {code:#x} at {pc} is outside the model"),
            }
            pc += 1;
        }
    }
    done
}

// <linux/elf-em.h>
const EM_386: u32 = 3;
const EM_MIPS: u32 = 8;
const EM_PPC: u32 = 20;
const EM_PPC64: u32 = 21;
const EM_S390: u32 = 22;
const EM_ARM: u32 = 40;
const EM_X86_64: u32 = 62;
const EM_AARCH64: u32 = 183;
const EM_RISCV: u32 = 243;

// <linux/audit.h>
const ARCH_64BIT: u32 = 0x8000_0000;
const ARCH_LE: u32 = 0x4000_0000;
pub const AUDIT_ARCH_AARCH64: u32 = EM_AARCH64 | ARCH_64BIT | ARCH_LE;
pub const AUDIT_ARCH_ARM: u32 = EM_ARM | ARCH_LE;
pub const AUDIT_ARCH_I386: u32 = EM_386 | ARCH_LE;
pub const AUDIT_ARCH_MIPS: u32 = EM_MIPS;
pub const AUDIT_ARCH_MIPSEL: u32 = EM_MIPS | ARCH_LE;
pub const AUDIT_ARCH_MIPS64: u32 = EM_MIPS | ARCH_64BIT;
pub const AUDIT_ARCH_MIPSEL64: u32 = EM_MIPS | ARCH_64BIT | ARCH_LE;
pub const AUDIT_ARCH_PPC: u32 = EM_PPC;
pub const AUDIT_ARCH_PPC64: u32 = EM_PPC64 | ARCH_64BIT;
pub const AUDIT_ARCH_PPC64LE: u32 = EM_PPC64 | ARCH_64BIT | ARCH_LE;
pub const AUDIT_ARCH_RISCV32: u32 = EM_RISCV | ARCH_LE;
pub const AUDIT_ARCH_RISCV64: u32 = EM_RISCV | ARCH_64BIT | ARCH_LE;
pub const AUDIT_ARCH_S390X: u32 = EM_S390 | ARCH_64BIT;
pub const AUDIT_ARCH_X86_64: u32 = EM_X86_64 | ARCH_64BIT | ARCH_LE;

/// The architecture values above, for checks that try every one.
pub const AUDIT_ARCHES: [u32; 14] = [
    AUDIT_ARCH_AARCH64,
    AUDIT_ARCH_ARM,
    AUDIT_ARCH_I386,
    AUDIT_ARCH_MIPS,
    AUDIT_ARCH_MIPSEL,
    AUDIT_ARCH_MIPS64,
    AUDIT_ARCH_MIPSEL64,
    AUDIT_ARCH_PPC,
    AUDIT_ARCH_PPC64,
    AUDIT_ARCH_PPC64LE,
    AUDIT_ARCH_RISCV32,
    AUDIT_ARCH_RISCV64,
    AUDIT_ARCH_S390X,
    AUDIT_ARCH_X86_64,
];

/// <asm/unistd.h> (x86) `__X32_SYSCALL_BIT`.
const X32_SYSCALL_BIT: u32 = 0x4000_0000;

/// An ABI the filter is documented to recognise: its syscalls are allowed, except execve and
/// execveat, which go to the supervisor.
#[derive(Debug)]
pub struct Abi {
    pub name: &'static str,
    pub arch: u32,
    /// Bits of `nr` the contract ignores (the x32 bit on x86-64).
    pub ignored_bits: u32,
    /// The execve and execveat numbers the contract names (compared after clearing
    /// `ignored_bits`).
    pub exec_nrs: &'static [u32],
    /// The `nr` values (full 32 bits) the kernel's syscall tables dispatch to execve or execveat
    /// for this `arch`.
    pub kernel_exec_nrs: &'static [u32],
}

// arch/x86/entry/syscalls/syscall_64.tbl: execve 59, execveat 322 (64-bit ABI); 520, 545 (x32
// ABI, called with the x32 bit set).
const ABI_X86_64: Abi = Abi {
    name: "x86-64 and x32",
    arch: AUDIT_ARCH_X86_64,
    ignored_bits: X32_SYSCALL_BIT,
    exec_nrs: &[59, 322, 520, 545],
    kernel_exec_nrs: &[59, 322, X32_SYSCALL_BIT | 520, X32_SYSCALL_BIT | 545],
};
// arch/x86/entry/syscalls/syscall_32.tbl
const ABI_I386: Abi = Abi {
    name: "i386",
    arch: AUDIT_ARCH_I386,
    ignored_bits: 0,
    exec_nrs: &[11, 358],
    kernel_exec_nrs: &[11, 358],
};
// arch/arm/tools/syscall.tbl (EABI)
const ABI_ARM: Abi = Abi {
    name: "arm",
    arch: AUDIT_ARCH_ARM,
    ignored_bits: 0,
    exec_nrs: &[11, 387],
    kernel_exec_nrs: &[11, 387],
};
// include/uapi/asm-generic/unistd.h (arm64, riscv)
const ABI_AARCH64: Abi = Abi {
    name: "aarch64",
    arch: AUDIT_ARCH_AARCH64,
    ignored_bits: 0,
    exec_nrs: &[221, 281],
    kernel_exec_nrs: &[221, 281],
};
const ABI_RISCV32: Abi = Abi {
    name: "riscv32",
    arch: AUDIT_ARCH_RISCV32,
    ignored_bits: 0,
    exec_nrs: &[221, 281],
    kernel_exec_nrs: &[221, 281],
};
const ABI_RISCV64: Abi = Abi {
    name: "riscv64",
    arch: AUDIT_ARCH_RISCV64,
    ignored_bits: 0,
    exec_nrs: &[221, 281],
    kernel_exec_nrs: &[221, 281],
};
// arch/mips/kernel/syscalls/syscall_o32.tbl (numbers from 4000)
const ABI_MIPS: Abi = Abi {
    name: "mips o32",
    arch: AUDIT_ARCH_MIPS,
    ignored_bits: 0,
    exec_nrs: &[4011, 4356],
    kernel_exec_nrs: &[4011, 4356],
};
const ABI_MIPSEL: Abi = Abi {
    name: "mipsel o32",
    arch: AUDIT_ARCH_MIPSEL,
    ..ABI_MIPS
};
// arch/mips/kernel/syscalls/syscall_n64.tbl (numbers from 5000)
const ABI_MIPS64: Abi = Abi {
    name: "mips64 n64",
    arch: AUDIT_ARCH_MIPS64,
    ignored_bits: 0,
    exec_nrs: &[5057, 5316],
    kernel_exec_nrs: &[5057, 5316],
};
const ABI_MIPSEL64: Abi = Abi {
    name: "mips64el n64",
    arch: AUDIT_ARCH_MIPSEL64,
    ..ABI_MIPS64
};
// arch/powerpc/kernel/syscalls/syscall.tbl
const ABI_PPC: Abi = Abi {
    name: "powerpc",
    arch: AUDIT_ARCH_PPC,
    ignored_bits: 0,
    exec_nrs: &[11, 362],
    kernel_exec_nrs: &[11, 362],
};
const ABI_PPC64: Abi = Abi {
    name: "powerpc64",
    arch: AUDIT_ARCH_PPC64,
    ..ABI_PPC
};
const ABI_PPC64LE: Abi = Abi {
    name: "powerpc64le",
    arch: AUDIT_ARCH_PPC64LE,
    ..ABI_PPC
};
// arch/s390/kernel/syscalls/syscall.tbl
const ABI_S390X: Abi = Abi {
    name: "s390x",
    arch: AUDIT_ARCH_S390X,
    ignored_bits: 0,
    exec_nrs: &[11, 354],
    kernel_exec_nrs: &[11, 354],
};

/// A target the code recognises and the ABIs its filter accepts: the target's own, and the
/// 32-bit compat ABI where the code documents multi-arch support (x86-64, aarch64, riscv64).
#[derive(Debug)]
pub struct Target {
    pub name: &'static str,
    pub abis: &'static [Abi],
}

pub static TARGETS: [Target; 14] = [
    Target {
        name: "x86_64",
        abis: &[ABI_X86_64, ABI_I386],
    },
    Target {
        name: "x86",
        abis: &[ABI_I386],
    },
    Target {
        name: "aarch64",
        abis: &[ABI_AARCH64, ABI_ARM],
    },
    Target {
        name: "arm",
        abis: &[ABI_ARM],
    },
    Target {
        name: "mips",
        abis: &[ABI_MIPS],
    },
    Target {
        name: "mipsel",
        abis: &[ABI_MIPSEL],
    },
    Target {
        name: "mips64",
        abis: &[ABI_MIPS64],
    },
    Target {
        name: "mips64el",
        abis: &[ABI_MIPSEL64],
    },
    Target {
        name: "powerpc",
        abis: &[ABI_PPC],
    },
    Target {
        name: "powerpc64",
        abis: &[ABI_PPC64],
    },
    Target {
        name: "powerpc64le",
        abis: &[ABI_PPC64LE],
    },
    Target {
        name: "riscv32",
        abis: &[ABI_RISCV32],
    },
    Target {
        name: "riscv64",
        abis: &[ABI_RISCV64, ABI_RISCV32],
    },
    Target {
        name: "s390x",
        abis: &[ABI_S390X],
    },
];

/// The documented dispatch contract of the filter for one build target.
#[derive(Debug)]
pub enum Contract {
    /// A recognised target: a syscall of one of these ABIs is notified if it is execve or
    /// execveat and allowed otherwise; a syscall with any other `arch` kills the process.
    Known(&'static Target),
    /// A target the code does not recognise ("this will filter out all syscalls"): every
    /// syscall kills the process. `arch == 0` is left unconstrained (no kernel architecture
    /// reports it; the filter's fallback treats it as the host architecture).
    Unknown,
}

/// The `name` of the entry of `TARGETS` for this build, `Ok(None)` if the code does not recognise
/// the target architecture, `Err` for a configuration the contract does not cover: x86-64 with
/// 32-bit pointers (x32), big-endian arm or aarch64, little-endian 32-bit powerpc.
fn this_target_name() -> Result<Option<&'static str>, &'static str> {
    let little = cfg!(target_endian = "little");
    let name = if cfg!(target_arch = "x86_64") {
        if !cfg!(target_pointer_width = "64") {
            return Err("x86_64 with 32-bit pointers");
        }
        "x86_64"
    } else if cfg!(target_arch = "x86") {
        "x86"
    } else if cfg!(target_arch = "aarch64") {
        if !little {
            return Err("big-endian aarch64");
        }
        "aarch64"
    } else if cfg!(target_arch = "arm") {
        if !little {
            return Err("big-endian arm");
        }
        "arm"
    } else if cfg!(target_arch = "mips") {
        if little { "mipsel" } else { "mips" }
    } else if cfg!(target_arch = "mips64") {
        if little { "mips64el" } else { "mips64" }
    } else if cfg!(target_arch = "powerpc") {
        if little {
            return Err("little-endian powerpc");
        }
        "powerpc"
    } else if cfg!(target_arch = "powerpc64") {
        if little { "powerpc64le" } else { "powerpc64" }
    } else if cfg!(target_arch = "riscv32") {
        "riscv32"
    } else if cfg!(target_arch = "riscv64") {
        "riscv64"
    } else if cfg!(target_arch = "s390x") {
        "s390x"
    } else {
        return Ok(None);
    };
    Ok(Some(name))
}

/// The contract for the target this crate is built for; panics for a configuration the contract
/// does not cover (see `this_target_name`).
pub fn this_target() -> Contract {
    match this_target_name() {
        Ok(Some(name)) => Contract::Known(
            TARGETS
                .iter()
                .find(|t| t.name == name)
                .expect("every name is in TARGETS"),
        ),
        Ok(None) => Contract::Unknown,
        Err(config) => panic!("no dispatch contract is stated for {config}"),
    }
}

impl Contract {
    /// The action the contract prescribes for `(arch, nr)`; `None` where it prescribes none.
    pub fn expected(&self, arch: u32, nr: u32) -> Option<Action> {
        match self {
            Contract::Known(target) => Some(match target.abis.iter().find(|a| a.arch == arch) {
                Some(abi) if abi.exec_nrs.contains(&(nr & !abi.ignored_bits)) => Action::Notify,
                Some(_) => Action::Allow,
                None => Action::KillProcess,
            }),
            Contract::Unknown => (arch != 0).then_some(Action::KillProcess),
        }
    }

    /// The contract as pairwise disjoint regions of `(nr, arch)` pairs, each with the action
    /// `expected` gives on it.
    pub fn regions(&self) -> Vec<(Vec<Constraint>, Option<Action>)> {
        let arch_is = |arch, equal| Constraint::word_is(ARCH_OFFSET, u32::MAX, arch, equal);
        match self {
            Contract::Known(target) => {
                let mut regions = Vec::new();
                for abi in target.abis {
                    let nr_mask = !abi.ignored_bits;
                    for &nr in abi.exec_nrs {
                        let notified = vec![
                            arch_is(abi.arch, true),
                            Constraint::word_is(NR_OFFSET, nr_mask, nr, true),
                        ];
                        regions.push((notified, Some(Action::Notify)));
                    }
                    let mut allowed = vec![arch_is(abi.arch, true)];
                    allowed.extend(
                        abi.exec_nrs
                            .iter()
                            .map(|&nr| Constraint::word_is(NR_OFFSET, nr_mask, nr, false)),
                    );
                    regions.push((allowed, Some(Action::Allow)));
                }
                let killed = target
                    .abis
                    .iter()
                    .map(|abi| arch_is(abi.arch, false))
                    .collect();
                regions.push((killed, Some(Action::KillProcess)));
                regions
            }
            Contract::Unknown => vec![
                (vec![arch_is(0, true)], None),
                (vec![arch_is(0, false)], Some(Action::KillProcess)),
            ],
        }
    }
}
