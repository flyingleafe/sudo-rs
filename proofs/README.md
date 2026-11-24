# Formal verification of sudo-rs

**Result.** Lean proves that the extracted `sudoers::check_permission` and
`sudoers::permission_flags` return the same decision and tags as the hand-written spec.
The latter includes the root/self password-tag adjustment from `Sudoers::check`.
The same is proved for the tags behind `sudo -v` and `sudo -l` (`validate_flags`, `list_flags`)
and for the mapping from a decision and the Defaults in force to the terms of execution
(`Judgement::authorization`).
The policy proofs (P1–P9) start from a parsed policy and a resolved request, not an invocation
of `sudo`. They transfer to the extracted code under the oracle and representation assumptions
below. Alias flattening preserves decisions and tags under the stated conditions, not
unconditionally. Separate proofs cover shell-mode argument escaping for every input and
the compiled AArch64 `-u '#uid'` parser. For stable, include-free sudoers text,
[`text_to_authorization`](lean/SudoRsProofs/Parser/EndToEnd.lean) connects the actual
extracted parser, analyzer, Defaults passes, `check` and `Judgement::authorization` to the
independent specification. It starts **after** the input is read and decoded, and ends at
the returned decision and restrictions, not at OS execution. See the [text proof index](parser/README.md).

## Verification boundary

[`permission_flags_eq`](lean/SudoRsProofs/Permission.lean) says the extracted model
returns `ok r` (rather than an error or divergence) and that `r.map absTag` equals
`SudoersSpec.authorize` on the abstracted inputs. Companion proofs cover the rule
lookup, aliases, matchers, tag accumulation, and the pre-adjustment decision
`check_permission_eq`. The spec separately proves default-deny and last-match
properties.

For the text theorem no policy or settings invariant is assumed: both are derived from the
input. A denial is a successful return of `Forbidden`, not a failed parse. If the analyzer
reports nothing, [`TextAgreement.clean_unique`](lean/SudoRsProofs/Parser/EndToEnd.lean)
also identifies the unique grammar ASTs and end position and proves the alias tables are
in valid dependency order. Exact tag equality after whole-policy alias expansion has two
additional conditions, stated in `clean_expanded_flags`. [Input bounds and primitive model
agreements](lean/ASSUMPTIONS.md#parser-and-analysis-boundaries) still apply.

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
show that the function panics outside that range. [The extracted Defaults producers](lean/SudoRsProofs/Defaults/Range.lean)
keep reachable settings in range; [the reference text parser](spec/SudoersSpec/Settings/FromParser.lean)
establishes that property after scope selection on include-free input. `ChDir::construct`
is extracted and uses modeled path/classification primitives. The `apparmor` restriction is not covered.

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
and room in the diagnostics vector. [`sanitize_alias_tables_exact`](lean/SudoRsProofs/Parser/Analysis/AliasOrder.lean)
also proves the exact order and appended messages, even for non-clean tables. These facts
rely on the list model of `HashSet` and on `alias_diagnostic`. For an include-free stream
of parsed items, [`analyze_refines_of_reference`](lean/SudoRsProofs/Parser/Analysis/Input.lean)
establishes the actual policy, Defaults lists and diagnostics under its input-size, path
and rendering conditions; it does not require the input file to be diagnostic-free.

The [policy-level properties](spec/SudoersSpec/Properties.lean) are kernel-checked for
every oracle, policy and request: an allowed request has a witness line, host group and
deciding entry (P1); a user, host or command that no list mentions is never allowed (P2);
the denial of a matched request comes from a command-side `!` (P3); `!` in user and host
lists only switches a line or host group off (P3b); the last line with a deciding entry
decides (P4); other users' lines are irrelevant (P5); adding a line without a
command-side `!` never revokes (P6); `()` and `(: grp)` only run as oneself (P7); `-g grp`
is justified by membership or the group list (P8); NOPASSWD comes from the root/self
exception or a tag in the deciding host group (P9). Where sudo-rs lacks the documented
property (runas targets without a runas spec, F2; `!` in runas lists, F3 and F5), the exact
sudo-rs rule is proved instead. [`RunasManual.lean`](spec/SudoersSpec/RunasManual.lean)
states the man page's runas rule for lists without `!`; sudo-rs agrees except in F2, F4
and F5. [`Certificates.lean`](spec/SudoersSpec/Certificates.lean) has 22 theorems checked
by `decide` on concrete policies: the findings and one non-vacuity example per property.
[`SudoRsProofs/Properties.lean`](lean/SudoRsProofs/Properties.lean) transfers P1-P3 and
P7-P9 to the extracted `permission_flags`, P2 to `Judgement::authorization`, and P4-P6 to
pairs of Rust rule slices, under the hypotheses of `permission_flags_eq`.

[Alias expansion](spec/SudoersSpec/Expansion.lean): `Policy.expandAliases` flattens every
User, Host, Runas and Cmnd_Alias reference (runas group lists through
`match_group_alias`; a Cmnd_Alias becomes separate entries that inherit runas spec and
tags). For alias tables that `sanitize_alias_tables` accepts without a diagnostic, the
flattened policy decides exactly like the original (`authorize_expandAliases`, and
`permission_flags_expandAliases` for the extracted code) provided expansion empties no
runas user list and no Cmnd_Alias body contains `ALL`; without the second condition the
results differ only by the implicit `SETENV` of a literal `ALL`
(`authorize_expandAliases_rel`). Kernel-checked counterexamples show both conditions are
needed; C sudo 1.9.18 behaves the same on those cases (test).

[Argument escaping](lean/SudoRsProofs/Escape.lean) for `sudo -s`/`-i`: the extracted
`escaped` (`src/common/command.rs`) equals `SudoersSpec.Escape.escapeArgs` for every input
(`escaped_eq`, `escaped_spec`): it succeeds exactly when the line fits in `usize::MAX` bytes,
keeps a byte iff it is ASCII alphanumeric, `_`, `-` or `$`, puts a backslash before every
other byte, and joins arguments with one space. The only two argument lists with the same
line are `[]` and `[""]` (`escaped_injective`; `build_from_args` never passes `[]`), and the
line reads back to its arguments (`escaped_unescape`). `OsString`/`OsStr` are modelled as
their bytes (see the assumptions ledger). The decoder follows the escaping grammar, not a
shell.

[Machine code](machine-code/README.md): a separate Lean project (Lean v4.34.0, Google
DeepMind's `arm64-semantics` v0.51.2) proves that the AArch64 code rustc 1.98.1 emits for
`NameOrId::<UserId>::parse` (the `-u '#uid'` parser; source copied verbatim and checked
byte-identical; `opt-level = 3`) meets its specification under every valid linker placement
(`parseUid_placed_ok`): it always returns normally, reads only the `String` header and
buffer, writes only its two outputs and a 16-byte stack frame, and returns exactly the
result of `NameOrId::parse`, for inputs of any length. `scripts/recheck.sh` rebuilds and
re-checks it (copied source, engine trusted files, fresh export, instruction words against
the object file, clean build, axioms). Trusted: the Lean kernel, the engine's ISA and memory
model and its `parseDecimalU32`, and the specification.

For stable, include-free input, the text proof covers the decoded characters through analysis,
Defaults scoping and the returned authorization. It does not establish that the file was
opened securely, that real identity lookups or glob matching satisfy their contracts, or
that the installed binary authenticates, changes credentials and executes as authorized.
The Quint lifecycle model describes these later steps separately; it is not a refinement
proof of the Rust execution path. The AArch64 result above concerns one compiled parser,
not the compiler or the complete `sudo` binary.

The fork changes alias-membership storage from a hash table to a linear list for
extraction. Resolving many dependent aliases can therefore be quadratic. Treat
this branch as a verification PoC, not a production performance replacement.

## Bounded proofs and tests

Each item says what kind of evidence it is. A test covers only the inputs it ran.

- **Differential test** ([`differential/`](differential/README.md), test): generated
  policies and requests decided by the Lean spec, by sudo-rs (`Sudoers::read` + `check`) and
  by C sudo 1.9.18 (`testsudoers`). The generator covers alias hazards: names spelled like
  aliases, references to undefined aliases, cyclic and duplicate definitions. On 20,000
  cases the spec and sudo-rs agree on every verdict, every tag field and every alias
  diagnostic; a C model agrees with C sudo on all 17,335 cases C sudo accepts, which
  explains every spec/C difference.
- **Property search on the real code** (`differential/`, test): seven properties stated in
  Lean (lines of other users are irrelevant, appending without a command-side `!` never
  revokes, unmentioned users/hosts/commands are never allowed, textual alias expansion,
  earlier lines before a deciding last line, `sudo -l` read back as a policy, `#0`
  spellings), each run on at least 10,000 generated instances that meet its precondition;
  counterexamples are shrunk and confirmed on sudo-rs twice. The README there lists the
  outcome of each property.
- **Runtime unit tests** (`src/sudoers/test/runtime.rs`, test): command paths match after
  canonicalisation (`..`, `//`, `.`, directory symlinks); time windows, `CHROOT`,
  `INTERCEPT`, `ROLE`, `TYPE` and digests are rejected at parse.
- **Sanitizers** ([`sanitizers/`](sanitizers/README.md), test): the 191-test baseline ran in
  debug mode, under AddressSanitizer and under Miri. ASan found no invalid memory access;
  LeakSanitizer reported one leak attributed to the forking test harness. Miri reported no
  undefined behaviour on the paths it ran. The results include host-dependent failures,
  four unsupported-clock failures and 30 Miri skips; they are not 191 clean passes. The
  eight tests added since then pass in all three modes at `f20cfeb7`.
- **Fuzzing** ([`../fuzz/`](../fuzz/README.md), test): nine libFuzzer targets on the real
  code (sudoers parser, decision, Defaults, sudo/su/visudo command lines, timestamp records,
  `NameOrId` and shell-mode argument escaping, and the rewritten sudoers parser against the
  legacy one) through the `cfg(fuzzing)`-only `src/fuzz_api.rs`, with AddressSanitizer, debug
  assertions and property assertions. All runs total 648,651,049 executions. A cluster
  campaign at `58a225fe` ran every target for at least 2,700 seconds (173,633,180
  executions): eight targets saved no failing input, and all 6,981 saved `timestamp` inputs
  reproduce the two corrupt-file defects in the fuzz README; both fail closed.
- **Kani** ([`kani/`](kani/README.md), bounded proof): 36 harnesses on the real functions
  (`#[cfg(kani)]` modules), all passing in one run at `f20cfeb7`. They cover shell-mode
  escaping (exact output up to one 5-byte argument or two 2-byte arguments; injectivity for
  shapes such as [3] vs [1,1]), the arguments the policy sees in shell mode, the timestamp
  record path (CVE-2023-42456 class), record encoding, decoding and matching, the user a new
  record names under default, `targetpw` and `rootpw` authentication (CVE-2025-64517 class),
  `PamBuffer` bounds and wiping, `cutils`, seccomp buffer allocation and `siginfo` reading.
  Four planted bugs (the pre-fix CVE-2023-42456 record path, a space kept by `escaped`, a
  `PamBuffer` one byte too long, record decoding without its seconds precondition) each fail
  a harness that passes on the clean tree.

## Artifacts

| Path | Contents |
|---|---|
| `sudoers.mlw` | Upstream Why3 proof (unchanged). |
| `extract.sh` | Rust → LLBC (Charon) → Lean 4 (Aeneas) extraction. |
| `lean/` | Lake project: generated code (`SudoRs`) and proofs (`SudoRsProofs`). |
| `spec/` | Hand-written Lean specification of the authorization decision. |
| `quint/` | Quint model of the surrounding lifecycle. |
| `check.sh` | Local gate for proof builds, axiom audit, model checks, and sudoers unit tests. |
| `differential/` | Unprivileged comparison of the Lean, Rust and C policy decisions; property search on the real code. |
| `sanitizers/` | Unit suite under debug overflow checks, AddressSanitizer and Miri. |
| `../fuzz/` | libFuzzer targets on the real code and the campaign runner. |
| `kani/` | Runner and results of the Kani bounded proofs (harnesses in `src/**/kani_proofs.rs`). |
| `machine-code/` | AArch64 machine-code proof of `NameOrId::<UserId>::parse` (own Lean project, pinned engine) and its re-check script. |
| `compliance/` | Docker comparison of upstream and refactored sudo-rs. |
| [`parser/`](parser/README.md) | Evidence index for the stable text parser, its grammar, extraction, local analysis, and the [P0–P5 plan](parser/PLAN.md). |

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
