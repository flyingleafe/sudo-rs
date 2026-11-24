# Fuzzing sudo-rs

Evidence kind: **test** (only the inputs the fuzzer generated were tried; nothing here is a
proof). Nine [libFuzzer](https://llvm.org/docs/LibFuzzer.html) targets drive the real sudo-rs
code, built with AddressSanitizer, debug assertions and integer-overflow checks.

## How the targets reach the code

`cargo fuzz` compiles every crate with `--cfg fuzzing`. Under that flag, and only then,
`src/lib.rs` contains `pub mod fuzz_api` (`src/fuzz_api.rs`): thin wrappers that call the same
crate-private functions the `sudo`, `su` and `visudo` binaries call and return their results in
plain types. A few `#[cfg(fuzzing)]` hooks sit next to private items (`su::cli`, `visudo`,
`common::resolve`, `common::command`); `Hostname::fake`, the `SudoAction` re-export, the legacy
sudoers parser (`sudoers::legacy`) and its comparison with the live one (`sudoers::equiv`) are
compiled for `cfg(any(test, fuzzing))`. A normal build contains none of it.

## Targets

| Target | Code under test (entry point) | Input | Properties asserted besides "no crash" |
|---|---|---|---|
| `sudoers_parse` | `Sudoers::read`: UTF-8 read, `parse_lines`, `analyze` (aliases, `Defaults`, `@include`/`@includedir`) | arbitrary bytes | only invalid UTF-8 fails to read; every diagnostic span of the file satisfies what `sudo::diagnostic::cited_error` computes with it; reading twice gives the same diagnostics |
| `sudoers_decide` | `Sudoers::read` + `check` (`sudo cmd`), `check_validate_permission` (`sudo -v`), `check_list_permission` (`sudo -l`, `-l -U`), `matching_entries` with both listing formats | request header + policy text | deciding twice gives the same result; a runnable command implies `sudo -v` is allowed; own `sudo -l` allowed exactly when `sudo -v` is; root, and a user who neither switches user nor leaves their groups, are not asked for a password |
| `sudoers_defaults` | `Defaults` parsing (`SettingsModifier::parse`, the settings DSL), application by scope in `Sudoers::check`, read back via `Judgement::authorization`, `search_path`, `visudo_editor_path` | request header + policy text (+ an allow-all rule) | same settings when applied twice; password attempts within `passwd_tries`' range 0..=1000 |
| `sudo_cli` | `SudoAction::try_parse_from` (normalisation, parsing, validation) | NUL-separated argv, any bytes | parsing twice gives the same result; the action's positional arguments are a contiguous tail of argv |
| `su_cli` | `SuOptions::parse_arguments` + `validate` | NUL-separated argv, UTF-8 | same result twice; the target user and shell arguments occur in argv in order |
| `visudo_cli` | `VisudoOptions::parse_arguments` | NUL-separated argv, UTF-8 | same result twice |
| `timestamp` | `SessionRecord::from_bytes`/`as_bytes`; `SessionRecordFile::new`, `touch`, `create`, `disable` on a memfd | one record, or file contents + up to 8 operations | re-encoding keeps the length and is stable; `touch` right after `create` finds a fresh record; `touch` right after `disable` finds none |
| `name_escape` | `NameOrId::parse` (`-u`/`-g` values); `escaped` and `CommandAndArguments::build_from_args` with a shell (`sudo -s`/`-i`) | a name, or NUL-separated arguments (any bytes) | empty rejected; no `#` → the name unchanged; `#…` never a name, an id exactly when the rest is a `uid_t`, ids print back to themselves; every byte outside `[A-Za-z0-9_$-]` escaped; splitting at unescaped spaces and unescaping returns the arguments (escaping is injective); the shell gets `-c` and that string |
| `parser_equiv` | the restricted-style `parse_lines::<Sudo>` against the legacy parser it replaced (`sudoers::equiv::compare`, `src/sudoers/legacy/`) | arbitrary bytes | on UTF-8 input both parsers give the same items, spans and message texts, and every `Defaults` modifier has the same effect on two base settings (`Settings::dump_fields`) |

The request header of `sudoers_decide`/`sudoers_defaults` is
`invoking-user:target-user:target-group:host`, then a line with the command and its arguments,
then the policy (see `fuzz_targets/common.rs`). Users and groups are synthetic (no lookups in
the host's databases); ids are derived from names as in the sudoers unit tests. Relative
`@include` paths resolve under a directory that does not exist; absolute ones reach the real
file system through the same secure-open checks as in `sudo`.

Seeds (`seeds.py`) come from the unit tests: the string literals and request triples of the
sudoers tests, `docs/sudoers.example`, the argument vectors of the `sudo` and `su` CLI tests,
the `escaped` tests, every setting name in every `Defaults` form and scope, and records encoded
exactly as `SessionRecord::encode` writes them. The three sudoers targets also get a dictionary
of sudoers keywords and setting names.

## Campaign

Run on 2026-11-20 on the shared verification machine: two batches of four, each target in a
scope of its own pinned to one core (`LIMIT_CPUS=<core> LIMIT_MEM=2560M`), from the seeds
alone (no corpus carried over). "Code covered" is the line coverage of the final corpus
(`run.sh coverage`), for the files the target reaches; "edges" is libFuzzer's `cov:`.

| Target | Code covered (lines executed by the final corpus) | Seconds | Executions | Edges | Corpus | Crashes |
|---|---|---:|---:|---:|---:|---:|
| `sudoers_parse` | `sudoers/{ast 96.7 %, basic_parser 96.0 %, tokens 97.4 %, char_stream 100 %, mod 29.1 %}`, `defaults/settings_dsl` 58.5 % | 1855 | 1,142,226 | 4039 | 2162 | 0 |
| `sudoers_decide` | `sudoers/mod` 88.7 %, `sudoers/{entry 96.7 %, entry/verbose 100 %, policy 63.9 %, ast 96.1 %, tokens 98.7 %}` | 1838 | 314,666 | 5302 | 1969 | 0 |
| `sudoers_defaults` | `defaults/{mod, settings_dsl}` 100 %, `sudoers/policy` 87.5 %, `sudoers/mod` 59.8 %, `sudoers/ast` 93.9 % | 1857 | 890,952 | 4801 | 1748 | 0 |
| `sudo_cli` | `sudo/cli/mod` 97.5 % | 1850 | 11,814,244 | 1107 | 775 | 0 |
| `su_cli` | `su/cli` 97.4 % | 1860 | 9,479,760 | 663 | 382 | 0 |
| `visudo_cli` | `visudo/cli` 94.7 % | 1843 | 18,943,703 | 386 | 426 | 0 |
| `timestamp` | `system/timestamp` 85.2 %, `system/time` 86.1 %, `system/file/lock` 95.8 % | 1268 (stopped, see below) | 5,790,440 | 452 | 196 | 1338 inputs, 2 causes |
| `name_escape` | `common/command` 56.9 % (`escaped`, `build_from_args`), `common/resolve` 18.1 % (`NameOrId::parse`) | 1843 | 15,913,811 | 347 | 176 | 0 |

Triage (every saved input replayed against the same build):

- Seven targets: no crash, no timeout (`-timeout=600`), no out-of-memory input. Their only
  artifacts are `slow-unit-*` files (1 to 6 per target, 14 in all); on replay each runs in 0 to
  16 ms. Four of them were written in the same minute by four different targets: stalls of the
  shared machine, not slow inputs.
- `timestamp`: 1338 failing inputs with two causes, both real defects of sudo-rs in reading a
  corrupt timestamp file (root-owned, mode 0600, so only corruption or root can produce one).
  Both fail closed (no credential is accepted that should not be); details and inputs are kept
  outside this repository and are reported separately. The remaining 2 artifacts are slow
  units that replay in under 20 ms.
- `timestamp` did not complete 1800 s: systemd-oomd stopped its scope twice under memory
  pressure of the shared machine (at 1280 s and 1268 s); the table shows the second run. An
  earlier version of the target handed the memfd over at its end, so its file mode never read
  a record; that run was discarded and the target fixed (commit "fuzz: timestamp target reads
  the file from its start").

### Extended runs

The initial campaign contributed 64,289,802 executions. Fifteen additional local runs
contributed 235,116,307: `visudo_cli` 85,233,885; `name_escape` 66,740,624; `su_cli`
39,746,343; `sudo_cli` 32,424,440; `timestamp` 10,971,015. The later local `timestamp` run
completed 3,600 seconds. For interrupted runs the count stops at the last libFuzzer
fork-mode status line.

A separate cluster campaign at `f20cfeb7` ran all eight targets concurrently for 2,700-2,755
seconds each, from seed corpora, on one 8-CPU Slurm node (GCC 11.5, cargo-fuzz 0.13.2):

| Target | Seconds | Executions | Edges | Corpus | Crashes |
|---|---:|---:|---:|---:|---:|
| `sudoers_parse` | 2743 | 8,802,978 | 4349 | 2640 | 0 |
| `sudoers_decide` | 2752 | 824,980 | 5788 | 2607 | 0 |
| `sudoers_defaults` | 2755 | 940,002 | 4922 | 2440 | 0 |
| `sudo_cli` | 2737 | 23,189,656 | 1107 | 801 | 0 |
| `su_cli` | 2731 | 23,269,066 | 663 | 393 | 0 |
| `visudo_cli` | 2731 | 40,421,718 | 388 | 430 | 0 |
| `timestamp` | 2700 | 19,155,335 | 453 | 212 | 5138 crashes, 4980 artifacts |
| `name_escape` | 2723 | 59,008,025 | 322 | 175 | 0 |

The cluster campaign contributed 175,611,760 executions, for 475,017,869 across all runs.
Seven targets reported no crash, timeout or out-of-memory input. The `timestamp` artifacts of
that campaign were not replayed. A second 900-second `timestamp` run at `f20cfeb7` on the cluster
(5,807,309 executions, 3,815 crashes) saved 3,738 crash inputs; every one was replayed. All
of them reproduce one of the two corrupt-file defects described above (3,630 one defect, 108
the other); no other cause appeared. Executions are not distinct inputs.

### Campaign on the rewritten parser

At `58a225fe` (the sources and fuzz targets of the rewritten parser) all nine targets ran
concurrently for 2,700-2,757 seconds each, from seed corpora, on one 10-CPU Slurm node (job
`fuzz-parser-final-07263c`, GCC 11.5, cargo-fuzz 0.13.2):

| Target | Seconds | Executions | Edges | Corpus | Crashes |
|---|---:|---:|---:|---:|---:|
| `sudoers_parse` | 2748 | 741,639 | 4183 | 2187 | 0 |
| `sudoers_decide` | 2706 | 276,021 | 5437 | 2242 | 0 |
| `sudoers_defaults` | 2757 | 426,081 | 4594 | 1903 | 0 |
| `sudo_cli` | 2732 | 25,364,021 | 1107 | 811 | 0 |
| `su_cli` | 2726 | 25,471,943 | 663 | 387 | 0 |
| `visudo_cli` | 2726 | 39,452,238 | 388 | 423 | 0 |
| `timestamp` | 2700 | 18,440,602 | 453 | 204 | 7346 crashes, 6981 saved inputs |
| `name_escape` | 2721 | 63,095,638 | 320 | 185 | 0 |
| `parser_equiv` | 2703 | 364,997 | 6761 | 2275 | 0 |

This campaign contributed 173,633,180 executions, for 648,651,049 across all runs. Eight
targets saved no failing input (no crash, timeout or out-of-memory input); `parser_equiv`
found no text on which the rewritten parser and the legacy parser differ. Every one of the
6,981 saved `timestamp` inputs was replayed against the same build: 6,678 reproduce one of the
two corrupt-file defects described above and 303 the other; no other cause appeared.

The three targets that read sudoers text executed fewer inputs than at `f20cfeb7`
(`sudoers_parse` 741,639 against 8,802,978), mostly because the inputs are longer: the seed
corpus grew with the tests added since (544 seeds, the largest 6,294 bytes, against 443
seeds, the largest 1,498), and libFuzzer derives its length limit from the largest seed. On
identical inputs the `sudoers_parse` build of `58a225fe` took 1.06 to 1.16 times as long as
the build of `f20cfeb7` (job `fuzz-rate-644487`: both builds replayed both seed corpora and
the two corpora that each build evolved in 300 seconds).

## Commands

From the repository root, inside the dev shell (`nix develop`, or `/tmp/sudo-rs-wt/dev` on the
verification machine, which also applies the shared memory and CPU limits):

```sh
fuzz/run.sh build                       # cargo fuzz build -O --debug-assertions (ASan)
fuzz/run.sh campaign                    # 2 batches of 4 targets, 1800 s each, one core each
fuzz/run.sh summary                     # the table above, from $FUZZ_OUT/<target>/fuzz.log
fuzz/run.sh coverage                    # line coverage of each corpus (cargo fuzz coverage + llvm-cov)
FUZZ_SECONDS=60 fuzz/run.sh campaign timestamp   # one target, one minute
```

The campaign above ran each target in its own scope on the verification machine:

```sh
/tmp/sudo-rs-wt/dev fuzz/run.sh build && /tmp/sudo-rs-wt/dev fuzz/run.sh seed
LIMIT_CPUS=4 LIMIT_MEM=2560M FUZZ_PARALLEL=1 /tmp/sudo-rs-wt/dev fuzz/run.sh fuzz sudoers_parse &
# ... likewise sudoers_decide (core 5), sudoers_defaults (6), sudo_cli (7); then the second
# batch su_cli, visudo_cli, timestamp, name_escape on cores 4-7
/tmp/sudo-rs-wt/dev fuzz/run.sh summary; /tmp/sudo-rs-wt/dev fuzz/run.sh coverage
```

Every target runs as

```sh
<target> $FUZZ_OUT/corpus/<target> [-dict=sudoers.dict] -fork=1 -ignore_crashes=1 \
  -ignore_timeouts=1 -ignore_ooms=1 -rss_limit_mb=2048 -timeout=600 -max_total_time=1800 \
  -artifact_prefix=$FUZZ_OUT/<target>/artifacts/
```

Fork mode with one worker keeps a target fuzzing after a crash and saves every failing input.
Tools: rustup toolchain `nightly-2026-11-20` (rustc 1.102.0-nightly 6905905bb, LLVM 23.1.6),
cargo-fuzz 0.13.1, libfuzzer-sys 0.4.13; `run.sh` fetches rustup, cargo-fuzz and python3 from
nixpkgs when they are missing. Failing inputs of real defects are not part of this repository.
