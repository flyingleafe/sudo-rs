# Formal verification of sudo-rs

**Result.** Lean proves that the extracted `sudoers::check_permission` and
`sudoers::permission_flags` return the same decision and tags as the hand-written spec.
The latter includes the root/self password-tag adjustment from `Sudoers::check`.
The same is proved for the tags behind `sudo -v` and `sudo -l` (`validate_flags`, `list_flags`)
and for the mapping from a decision and the Defaults in force to the terms of execution
(`Judgement::authorization`).
The proofs start with a parsed policy and a resolved request, not an invocation of `sudo`.

## Verification boundary

[`permission_flags_eq`](lean/SudoRsProofs/Permission.lean) says the extracted model
returns `ok r` (rather than an error or divergence) and that `r.map absTag` equals
`SudoersSpec.authorize` on the abstracted inputs. Companion proofs cover the rule
lookup, aliases, matchers, tag accumulation, and the pre-adjustment decision
`check_permission_eq`. The spec separately proves default-deny and last-match
properties.

[`validate_flags_eq` and `list_flags_eq`](lean/SudoRsProofs/ListValidate.lean) make the
same statement for the tags that `sudo -v` and `sudo -l` compute, against
`SudoersSpec.validateFlags` and `SudoersSpec.listFlags`. `list_flags_eq` also assumes
that `UnixUser::group` is a pure function (`GroupOracle`) and that `Path::new("list")`
reads as `list` (`ListPath`); `sudo -v` and listing one's own entries need neither.
The Defaults handling in `check_validate_permission` and `check_list_permission` and
the `sudo -l` printing code are not verified.

[`authorization_eq`](lean/SudoRsProofs/Authorization.lean) proves that the extracted
`Judgement::authorization`, with `Settings::to_auth`, returns `ok` and equals
`SudoersSpec.authorization`: the mapping from the decision and the Defaults values to
`Authorization::{Allowed(Authentication, Restrictions), Forbidden}`. It assumes
`SettingsInRange` (`passwd_tries` fits `u16`, `umask` fits `u32`); two further theorems
show that the function panics outside that range. The Defaults parser appears to keep
both values in range, but that is not proved. `authorization_permission_flags_eq`
composes the result with `permission_flags_eq`. `ChDir::construct`, used for `runcwd`,
is a hand-written model, and the `apparmor` restriction is not covered.

The [proof witnesses](lean/SudoRsProofs/NonVacuity.lean) apply the theorem to a
synthetic policy that permits one user with explicit tags and denies another.
They retain the glob-interface assumption. A separate spec-level negative
control proves that an always-deny decision does not refine the spec.

The decision theorem assumes valid alias-order indices, representable string and
modifier lengths, and agreement of the identity and command-matching interfaces
with their oracles. Host matching is literal. Only explicit tag updates are
representable as Rust modifiers, so no separate modifier invariant is required.
See [the assumptions ledger](lean/ASSUMPTIONS.md) for exact hypotheses and external
models. The axiom audit does not verify the Charon/Aeneas translation or the
faithfulness of hand-written models.

The alias preprocessing proofs
([`SanitizeAliases`](lean/SudoRsProofs/SanitizeAliases.lean),
[`SanitizeOrder`](lean/SudoRsProofs/SanitizeOrder.lean),
[`SanitizeTables`](lean/SudoRsProofs/SanitizeTables.lean),
[`SanitizeTotal`](lean/SudoRsProofs/SanitizeTotal.lean)) cover `sanitize_alias_table`
and `sanitize_alias_tables`, the function `analyze` calls for the four alias tables.
Every returned order has in-range, pairwise distinct indices, which discharges the index
premise of the decision theorem. If a call adds no diagnostic, its order is a permutation
of the definitions with unique names in which every referenced alias comes earlier, so
`SudoersSpec.demonstration` applies: deciding with the precomputed table equals deciding
on the fully expanded items. Both functions always return, given names that fit in memory
and room in the diagnostics vector. These proofs rely on the list model of `HashSet` and
on the model of `alias_diagnostic`. Nothing is proved about which diagnostics are emitted,
about the order when diagnostics are present beyond those index properties, or that a
given sudoers text produces none.

The parser, include processing, Defaults parsing and scoping, real OS identity lookup,
glob matching, credential changes, authentication, command execution, rustc, and the
deployed binary are outside the verified boundary. The Quint lifecycle model is a
separate abstraction, not a proof about the Rust execution path.

The fork changes alias-membership storage from a hash table to a linear list for
extraction. Resolving many dependent aliases can therefore be quadratic. Treat
this branch as a verification PoC, not a production performance replacement.

## Artifacts

| Path | Contents |
|---|---|
| `sudoers.mlw` | Upstream Why3 proof (unchanged). |
| `extract.sh` | Rust → LLBC (Charon) → Lean 4 (Aeneas) extraction. |
| `lean/` | Lake project: generated code (`SudoRs`) and proofs (`SudoRsProofs`). |
| `spec/` | Hand-written Lean specification of the authorization decision. |
| `quint/` | Quint model of the surrounding lifecycle. |
| `check.sh` | Local gate for proof builds, axiom audit, model checks, and sudoers unit tests. |
| `differential/` | Unprivileged comparison of the Lean, Rust and C policy decisions. |
| `compliance/` | Docker comparison of upstream and refactored sudo-rs. |
| `parser/PLAN.md` | Plan and feasibility measurements for a parser proof. Nothing proved yet. |

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

From the repository root:

```sh
nix develop -c proofs/check.sh
nix develop -c proofs/check.sh extract   # independently regenerate the Lean and check for drift
```

The [Verification workflow](../.github/workflows/verification.yml) runs the default
gate on relevant pushes and pull requests. The extraction check is separate:
run it locally as above while the workflow is not on the fork's default branch.
The differential and compliance runs are opt-in.

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
generated code uses. The checked-in files use definitions or opaque constants,
not axioms. A definition still needs a justification as a model of the external Rust operation.

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

These are baseline experiments. The committed `lean/SudoRs/` is now generated from the
roots listed in `Cargo.toml` under `[package.metadata.charon]`. Run the extraction drift
check above to compare it with the current source. `Judgement::authorization` extracted
on the fork once `ChDir::construct` was made opaque: its `str::contains` reaches the
`Pattern` trait, which Aeneas does not translate.
