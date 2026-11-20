# Machine-code proof of `NameOrId::<UserId>::parse` (work in progress)

Status: **not finished.** The specification, the compiled object, its Lean export and the
re-check scripts are in place; the machine-code proof itself is partial and is *not* committed
(it still has open cases). Nothing in this directory is a kernel-checked statement about the
machine code yet, except the specification examples below.

## Target

sudo-rs's `NameOrId::parse` (`src/common/resolve.rs`) at `T = UserId`: it decides whether
`sudo -u <arg>` names a user or a numeric uid (`#<uid>`), the input class of CVE-2019-14287.

- `scripts/copy-source.sh` copies the items byte for byte into `rust/copied/`
  (`NameOrId` + `parse`, `SudoString` + `Deref` + `Debug`, `UserId` + `new`/`inner` + `FromStr`);
  `--check` compares them with the checkout and with commit `bc2fc69e`.
- `rust/src/lib.rs` adds only imports, `libc::uid_t = u32` and the monomorphic wrapper
  `sudo_rs_name_or_id_parse_uid(input, name_out, id_out) -> u32` (0 = `None`, 1 = `Name`,
  2 = `Id`).
- Compiler: rustc 1.98.1, `aarch64-unknown-linux-gnu`, `opt-level = 3`, `panic = "abort"`,
  one codegen unit, LTO off, plus the engine driver's flags (`relocation-model=static`,
  `target-cpu=generic`, no vectorisation). sudo-rs's own profile is `opt-level = "s"`; at `"s"`
  rustc outlines `str::strip_prefix::<char>` and calls libc `bcmp`, which would have to be
  assumed, so the proof targets `opt-level = 3` (identical code at 2). The function is 86
  instructions; the last 5 are the unreachable `core::str::slice_error_fail` call.

## Engine

`arm64-semantics` v0.51.2, i.e. the `arm64-semantics/` tree `bcaf7c1e` of
`google-deepmind/code-verification` commit `b0f729ac` (the commits that pin v0.51.2 pin Lean
`v4.34.0`; the repository's current main pins v0.56.1 and Lean v4.35.0). Lake fetches it
(`lakefile.lean`, `lake-manifest.json`); nothing is vendored. `scripts/check-engine.sh` checks
the commit, the tree id, and the SHA-256 of all trusted files against the pinned blobs and an
independent clone.

## What exists

| Item | Evidence |
|---|---|
| `SudoRsMachineCode/Spec.lean`: `rustParseU32` (Rust 1.98.1 `u32::from_str`, via the engine's trusted `parseDecimalU32`), `nameOrIdParseUid`, and the `c_spec` contract `parseUidSpec` (read-only `String` header and buffer `content ++ [0]`, writable out-parameters, 16-byte stack frame, exact return code and out values) | definitions (trusted, to be reviewed) |
| `SudoRsMachineCode/SpecExamples.lean`: 21 examples, e.g. `#-1` → `None`, `#+5` → `Id 5`, `#4294967295` → `Id 0xffffffff`, `#4294967296` → `None` | kernel-checked (`decide`) |
| `SudoRsMachineCode/Generated/`: `rust-obj2lean` output (placed library, `ExtractedObj` from the `.o` bytes, canonical placement witness) | generated; `scripts/recheck.sh` step 3 regenerates and diffs |
| `scripts/recheck.sh`: copied-source check, engine check, fresh export diff, instruction words vs an independently compiled `.o`, clean Lean build, axiom audit | script; steps 4–5 need the finished proof (`Proof.lean`, `Theorems.lean`) |

The partial proof (`subroutine_ok prog a parseUidSpec` from `prog.hasWords a parseUidWords`,
by `wp_init`/`wp_steps`/`wp_done`) currently closes: empty input, non-`#` names, `#`, `#+`,
`#-`, and one non-digit byte after `#`; the one-digit case reaches the return but its final
`wp_done` is not yet discharged, and the multi-byte digit loops (`len < 9` unchecked loop,
`len ≥ 9` checked loop) are not started. Not done: the placement lift to
`sudoRsParseUidLib.subroutineOk`, the axiom audit, the planted-bug runs, the fresh re-check.

## Reproduce

```sh
cd proofs/machine-code
lake build                     # fetches the engine at b0f729ac and builds what is imported
scripts/copy-source.sh --check
scripts/check-engine.sh
scripts/export.sh              # needs rustup 1.98.1 + aarch64-unknown-linux-gnu and a host cc
```

## Measured (this laptop, shared 4-CPU / 10 GiB slice, `LEAN_NUM_THREADS=2`)

- Engine closure for the proof (Arm64 + the needed ProofLib modules, precompiled): 39 min wall
  for the last ~130 jobs, peak 2.3 GiB (scope), peak 1.9 GiB anonymous with 2 Lean processes;
  earlier partial runs took ~45 min more. Importing ProofLib through Lake requires the whole
  precompiled `ProofLib` library (757 jobs), which was still building at hand-over.
- `scripts/export.sh` including building `rust-obj2lean`: 5 min 13 s, peak 1.3 GiB.
- Elaborating the partial proof file with plain `lean`: 7–60 s, about 1.1 GiB.
