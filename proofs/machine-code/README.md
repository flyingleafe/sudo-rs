# Machine-code proof of `NameOrId::<UserId>::parse`

Evidence kind: **kernel-checked proof** (Lean v4.34.0, Google DeepMind `arm64-semantics`
v0.51.2) about the AArch64 machine code that rustc 1.98.1 emits for sudo-rs's
`NameOrId::<UserId>::parse`, for every input length (no bound other than the address space).
Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Target

sudo-rs's `NameOrId::parse` (`src/common/resolve.rs`) at `T = UserId`: it decides whether
`sudo -u <arg>` names a user or a numeric uid (`#<uid>`), the input class of CVE-2019-14287.

- `scripts/copy-source.sh` copies the items byte for byte into `rust/copied/`
  (`NameOrId` + `parse`, `SudoString` + `Deref` + `Debug`, `UserId` + `new`/`inner` + `FromStr`);
  `--check` compares them with the checkout and with commit `bc2fc69e`.
- `rust/src/lib.rs` adds only imports, `libc::uid_t = u32` and the monomorphic wrapper
  `sudo_rs_name_or_id_parse_uid(input, name_out, id_out) -> u32` (0 = `None`, 1 = `Name`,
  2 = `Id`).

## Compile settings

rustc 1.98.1, `aarch64-unknown-linux-gnu`, `opt-level = 3`, `panic = "abort"`, one codegen unit,
LTO off, plus the engine driver's flags (`relocation-model=static`, `target-cpu=generic`, no
vectorisation); see `rust/Cargo.toml`, `rust/translation.toml`, `rust/rust-toolchain.toml`.

Why `opt-level = 3` and not sudo-rs's own `opt-level = "s"`: at `"s"` (and `"z"`) rustc 1.98.1
outlines `str::strip_prefix::<char>` and compares the prefix by calling libc `bcmp`, which the
proof would have to assume instead of check. At `opt-level = 2` and `3` the whole function is one
self-contained block of 86 instructions (identical at 2 and 3) with no call except the
`core::str::slice_error_fail` panic path. So the proved code is sudo-rs's source compiled with
these settings, not the instructions of a shipped sudo-rs binary.

The 86 instructions: the first 81 (`parseUidWords`, `+0x000` to `+0x140`) are proved; the last 5
(`+0x144` to `+0x154`) set up and call `core::str::slice_error_fail` (the panic of
`&self.inner[..num_bytes - 1]` in `SudoString::deref`) and are proved unreachable. The digits are
read by two loops that rustc emits for `u32::from_str`: an unchecked one for fewer than nine
digits (`+0x0a4`) and one with multiplication and addition overflow checks for nine or more
(`+0x0dc`).

## What is proved

`SudoRsMachineCode/Spec.lean` is the whole specification (it imports only the engine's trusted
vocabulary `Arm64`):

- `rustParseU32` is Rust 1.98.1's `<u32 as FromStr>::from_str(..).ok()`: an optional `'+'`, then
  one or more ASCII digits whose value is below `2 ^ 32` (via the engine's trusted
  `parseDecimalU32`); `nameOrIdParseUid` is `NameOrId::<UserId>::parse` on the `SudoString`
  contents (empty → `None`; `'#'` prefix → `Id` of the rest or `None`; otherwise `Name`).
- `parseUidSpec` (a `c_spec`): `input` points to the `String` header (capacity at `+0`, buffer at
  `+8`, length `content.length + 1` at `+16`), whose buffer holds `content ++ [0]`; header and
  buffer are owned read-only (`↦ᵣ`); `*name_out` (8 bytes) and `*id_out` (4 bytes) are owned
  writable; the callee may use the 16 bytes below the stack pointer (`stack16`). Only
  hypothesis on the input: `content.length + 1 < 2 ^ 64`. It does not assume UTF-8 or the absence
  of interior NULs (which `SudoString` guarantees). On return: `w0 = resultCode r` and the two
  outputs hold `nameOutAfter`/`idOutAfter` of `r = nameOrIdParseUid content`; header and buffer
  are unchanged.

`SudoRsMachineCode/SpecExamples.lean` checks the specification on 21 inputs by `decide`, e.g.
`#-1` → `None`, `#+5` → `Id 5`, `#4294967295` → `Id 0xffffffff`, `#4294967296` → `None`.

Main theorems (`SudoRsMachineCode/Proof.lean`, `SudoRsMachineCode/Theorems.lean`):

```lean
theorem parseUid_codeAt_ok (prog : Program) (a : BitVec 64)
    (hc : prog.hasWords a parseUidWords) :
    subroutine_ok prog a parseUidSpec

theorem parseUid_placed_ok :
    sudoRsParseUidLib.subroutineOk "sudo_rs_name_or_id_parse_uid" (fun _ => parseUidSpec)

theorem parseUid_placed_nonvacuous : ∃ pl, sudoRsParseUidLib.Placeable pl

theorem parseUidSpec_no_abnormal_outcome :
    (∀ x s sf, parseUidSpec.onPanic x s sf = ⌜False⌝) ∧
    (∀ x c s sf, parseUidSpec.onExit x c s sf = ⌜False⌝) ∧
    (∀ x s sf, parseUidSpec.onOom x s sf = ⌜False⌝)
```

`sudoRsParseUidLib` is the library `rust-obj2lean` exported from the compiled object (the text
block of the function and its neighbours, with relocations); `PlacedLib.subroutineOk` (engine,
trusted) quantifies over every placement `pl` the linker may choose (`Placeable pl`), and the
generated, kernel-checked canonical placement shows that such placements exist.

Reading of `subroutine_ok` (engine definition, `Arm64/Trusted/Spec/Hoare.lean`): for every ghost
value, every frame `R` and every entry state at the function's address with a 16-byte aligned
stack pointer whose memory satisfies `pre ∗ R`, the machine runs (`Steps`) to a final state that
has returned to the caller with the AAPCS64 calling convention preserved (stack pointer,
callee-saved registers) and memory satisfying `post ∗ R` (panic, exit and out-of-memory
outcomes are excluded since their postconditions are `⌜False⌝`). Hence:

- **Termination**: every run returns (total correctness; the loops are proved with measures).
- **Functional correctness**: return code and outputs equal `nameOrIdParseUid content` for
  every `content` of every length below `2 ^ 64 - 1`.
- **Memory safety**: writes go only to `*name_out`, `*id_out` and the 16-byte frame (the frame
  `R` is arbitrary and preserved, and header and buffer are read-only); reads stay inside the
  header and `content ++ [0]`, because the theorem also covers memories in which nothing else is
  mapped (`R = emp`), where any other access would fault. The panic call at `+0x144` is never
  reached.

The loop invariants (`small_loop_proof`, `checked_loop_proof` in `Proof.lean`) state that after
`i` bytes `x10` holds the value of the first `i` digits (`prefixValue D i`, defined from the
engine's `parseDecimalNatFold`) and that those bytes are digits (`DigitsUpTo D i`);
`ParseLemmas.lean` turns the three loop exits (all digits read, a non-digit, a value `≥ 2 ^ 32`)
into the value of `parseDecimalU32`.

## Trusted base

- The Lean 4 kernel (v4.34.0).
- The engine's trusted files, by the engine's own classification (`arm64-semantics/README.md`),
  pinned to commit `b0f729ac` and checked by `scripts/check-engine.sh` (74 files, SHA-256 equal to
  the pinned blobs and to an independent clone): the ISA model `Arm64/Trusted/ISA/{Syntax,Decode,
  Memory,State,Eval,Semantics,Float}.lean`, the object/placement model
  `Arm64/Trusted/Object/{Reloc,Placed}.lean`, the specification vocabulary
  `Arm64/Trusted/Spec/{SepLogic,Hoare,Placed,AsciiNum,RustAbi}.lean` and the `c_spec` elaborator
  `Arm64/Trusted/Surface/Abi.lean`, plus the `[TCB]` modules of `tools/rust-obj2lean` that
  extract the object file. `ProofLib` (tactics, lemmas) is untrusted: its results are re-checked
  by the kernel.
- The specification `SudoRsMachineCode/Spec.lean` (`rustParseU32`, `nameOrIdParseUid`,
  `parseUidSpec`): that it says what `NameOrId::<UserId>::parse` does is a claim checked by
  reading and by the 21 examples, not by proof.
- The link between the proof and sudo-rs: `scripts/copy-source.sh --check` (copied source equals
  sudo-rs's), `scripts/recheck.sh` step 3 (the generated library is reproduced from a fresh
  compile) and step 4 (`parseUidWords` are the bytes of an object compiled independently by
  rustc, and no relocation falls inside them). rustc itself is not trusted for the statement:
  the theorem is about the machine code it produced.

## Planted bugs: not yet run

Two mutants are prepared in scratch copies outside the repository (`/tmp/mcode-planted-a`: the
u32 parse replaced by a wrapping parse without the overflow check; `/tmp/mcode-planted-b`:
`SudoString::deref` slicing `[..num_bytes]`, an off-by-one that keeps the NUL). Compiling,
exporting and re-running the proof against them has not been done yet, so there is no recorded
outcome. Note that any source mutation changes the instruction words, so the unchanged proof
necessarily stops at the first differing word; the informative part of such a run is that the
mutant is also wrong on concrete inputs (for example `#4294967296` and `""`).

## Reproduce

```sh
cd proofs/machine-code
lake build                     # fetches the engine at b0f729ac, builds it and the proof
scripts/copy-source.sh --check
scripts/check-engine.sh
scripts/recheck.sh             # copy check, engine check, fresh export, object words, clean
                               # Lean rebuild, direct elaboration, axiom audit
scripts/recheck.sh --fresh     # the same from a fresh clone of HEAD, engine built from source
```

`scripts/export.sh` and `recheck.sh` need rustup with the toolchain of `rust/rust-toolchain.toml`
(1.98.1 + `aarch64-unknown-linux-gnu`) and a host C toolchain to build `rust-obj2lean`. On the
shared machine run them under `/tmp/sudo-rs-wt/limited`.

## Measured (this laptop, shared 4-CPU / 10 GiB slice, `LEAN_NUM_THREADS=2`)

- Engine closure (Arm64 + the whole precompiled `ProofLib` library, 757 Lake jobs): built in
  several runs, the last two 39 min (497 jobs, peak 2.3 GiB in the scope) and 7 min (the
  remaining jobs, peak 1.6 GiB); earlier partial runs took about 45 min more. A one-shot build
  from scratch (`recheck.sh --fresh`) has not been timed.
- `scripts/recheck.sh` (engine prebuilt): 8 min 21 s wall, peak 1.6 GiB in the scope (1.3 GiB
  anonymous, at most 2 Lean processes). Inside it: the clean `lake build` of this package
  235 s, peak 2.0 GB RSS for the largest process; direct elaboration of `Proof.lean` 220 s,
  2.0 GB; `Theorems.lean` 2 s, 0.9 GB.
- `scripts/export.sh` including building `rust-obj2lean`: 5 min 13 s, peak 1.3 GiB.
