# Formal verification of sudo-rs

This directory holds the verification artefacts of sudo-rs:

| Path | Contents |
|---|---|
| `sudoers.mlw` | Upstream Why3 proof (unchanged). |
| `extract.sh` | Rust → LLBC (Charon) → Lean 4 (Aeneas) extraction. |
| `lean/` | Lake project: generated code (`SudoRs`) and proofs (`SudoRsProofs`). |
| `spec/` | Hand-written Lean specification of the authorization decision. |
| `quint/` | Quint model of the surrounding lifecycle. |

## Prerequisites

Only [Nix](https://nixos.org) with flakes enabled. The repository's `flake.nix` provides a dev shell
with everything pinned:

```sh
nix develop            # or prefix single commands: nix develop -c <cmd>
```

| Tool | Version | Source |
|---|---|---|
| `aeneas` | rev `8f4466db9f0d59267b8e76b54473a21a005cf7be` | flake input `github:AeneasVerif/aeneas/8f4466db…` |
| `charon` | 0.1.321 (rev `61c67516e7752daf6b4dd403a030d90efbb0b8eb`), own toolchain `nightly-2026-09-17` | input of the Aeneas flake |
| Lean | `leanprover/lean4:v4.36.0-rc2` via `elan` (`lean/lean-toolchain`) | same as the Aeneas Lean library |
| Aeneas Lean library | rev `8f4466db…`, `backends/lean` | `lean/lakefile.lean` |
| Mathlib | `v4.36.0-rc2` (required by the Aeneas library) | `lean/lake-manifest.json` |
| `rustc`/`cargo` | 1.99.0 (+ `linux-pam`, `gcc`) | nixpkgs `02c087f3` (followed from the Aeneas flake) |
| `quint` | 0.33.0 | nixpkgs |
| `java` | OpenJDK 21 (for Apalache, which `quint verify` downloads) | nixpkgs |

The dev shell also builds and tests sudo-rs itself (`cargo test --lib`). On upstream commit `81dff9a1`
on a NixOS host: 171 passed, 11 failed; every failure is host-specific (the tests expect a `daemon`
user, `/bin/sleep`, `/bin` as a symlink, a zoneinfo database, a non-world-writable working directory),
none is a build or link problem.

## Workflow

### 1. Extract

```sh
nix develop -c proofs/extract.sh [extra charon args...]
```

- Runs `charon cargo --preset=aeneas [args] --dest-file <tmp>.llbc -- --lib` in the crate root with
  Charon's own Rust toolchain first on `PATH`. Without extra arguments, the items to extract come from
  the `[package.metadata.charon]` section of `Cargo.toml`; extra arguments (e.g.
  `--start-from crate::sudoers::find_item`, `--opaque …`) are appended.
- Runs `aeneas -backend lean -split-files -subdir SudoRs -no-progress-bar $AENEAS_FLAGS -dest <tmp>`
  and installs the result into `lean/SudoRs/`. `AENEAS_FLAGS` defaults to `-loops-to-rec` (every loop
  becomes a `partial_fixpoint` recursive function; the proof support for the default `loop`
  combinator is less mature); `AENEAS_FLAGS=""` passes no extra flag.
- Fails (exit 1, nothing installed, logs kept) on a Charon failure or any Aeneas `[Error]`, and prints
  the errors grouped by kind plus the list of definitions that could not be translated.
- `SUDO_RS_SRC=/path/to/crate` extracts from another checkout (default: this repository's root).

Generated modules in `lean/SudoRs/`, all in Lean namespace `sudo_rs`:

| Module | Kind |
|---|---|
| `SudoRs.Types` | generated: crate types |
| `SudoRs.Funs` | generated: crate functions (imports all of the others) |
| `SudoRs.TypesExternal_Template`, `SudoRs.FunsExternal_Template` | generated: stubs for external (std) types/functions; not built |
| `SudoRs.TypesExternal`, `SudoRs.FunsExternal` | hand-maintained models of the external definitions, imported by `Types`/`Funs` |

#### Hand-maintained external models

`lean/SudoRs/TypesExternal.lean` and `lean/SudoRs/FunsExternal.lean` are **not generated**: they are
source files owned by whoever writes models for the external (std/dependency) definitions the
generated code uses. The `axiom`s seeded into them are trusted assumptions; replacing an axiom with a
definitional model (a `def` with the same name and type) shrinks the trusted base.

- Aeneas only writes `*_Template.lean`; `extract.sh` never overwrites `*External.lean`. It seeds a
  missing one from its template (marked "Hand-maintained", without the Aeneas header).
- When a template changes, the script prints the template diff.
- After every run it compares the names declared in each template with the names the hand-maintained
  file declares (`axiom`/`opaque`/`def`/`abbrev`/`structure`/`inductive`/`class`/`instance`, fully
  qualified, at top level) and prints a `WARNING` listing the missing ones; add them, or `lake build`
  fails.
- Every other file in `lean/SudoRs/` whose first line is the Aeneas header is deleted and regenerated
  on each run; never edit those by hand.

### 2. Build

```sh
cd proofs/lean
nix develop -c lake exe cache get   # first time only: download Mathlib oleans (never build Mathlib)
nix develop -c lake build
```

### 3. Write proofs

Proof files live under `lean/SudoRsProofs/` and are imported from `lean/SudoRsProofs.lean`:

```lean
import SudoRs            -- or `import SudoRs.Funs`
open Aeneas Aeneas.Std Result
open sudo_rs

-- e.g. `sudo_rs.sudoers.find_item`
```

## Baseline extraction results

Upstream code at `81dff9a1`, one `--start-from` per function:

| Item | Result |
|---|---|
| `find_item` | extracts with full body; `HashMap` is an axiom type |
| `match_group`, `match_command`, `match_identifier`, `in_group`, `sanitize_alias_table` | extract; `glob::Pattern::matches_path_with`, `Path`, `OsString` become axioms |
| `get_aliases` | body fails: Aeneas "Internal error" (interp/InterpReduceCollapse.ml:1151) on its `for` loop (mod.rs ~701-709); `Iterator::chain`/`map` have no model in the Aeneas Lean library |
| `match_user` | fails through `auth_warn!`: `log::SudoLogger` holds `Box<dyn Log>` ("Dynamic trait types are not supported yet"); still fatal with `--opaque crate::log` |
| `distribute_tags` | fails: `ast::CommandSpec` holds `Vec<Modifier>` where `Modifier` is a boxed `dyn Fn(&mut Tag)`; the `Iterator::scan` closure body does not translate |
| `check_permission` | fatal, no output: `dyn` in `CommandSpec`, `CustomiserTable`, `SudoLogger`; `str::rsplitn` / `core::str::pattern::Pattern` unimplemented (reached via `tokens.rs` `Token::construct` impls); bodies of `matching_user_specs`, `get_aliases`, `distribute_tags` fail |
| whole `crate::sudoers` | fatal, no output |

The committed `lean/SudoRs/` is the `find_item` smoke extraction, reproducible with:

```sh
git clone https://github.com/trifectatechfoundation/sudo-rs /tmp/fi/src/sudo-rs
git -C /tmp/fi/src/sudo-rs checkout 81dff9a1
SUDO_RS_SRC=/tmp/fi/src/sudo-rs nix develop -c proofs/extract.sh --start-from crate::sudoers::find_item
```
