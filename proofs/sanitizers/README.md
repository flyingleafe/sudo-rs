# The unit-test suite under sanitizers and Miri

Evidence kind: **test**. The sudo-rs unit tests (every unit-test target of the crate: the
library and the `sudo`, `su`, `visudo` binaries) run in three modes, one process per test so
that a sanitizer report or a Miri stop is attributed to one test and does not end the run.

| Mode | Build | What it detects |
|---|---|---|
| `debug` | plain `cargo test` debug build: debug assertions and integer-overflow checks on | panics, arithmetic overflow; the baseline for host-dependent failures |
| `asan` | `-Zsanitizer=address`, std rebuilt with it (`-Zbuild-std`), target `x86_64-unknown-linux-gnu`; LeakSanitizer on | out-of-bounds and use-after-free accesses, double frees, leaks in the Rust code and std; the uninstrumented C libraries (glibc, PAM) only through ASan's interceptors (allocation, string and memory functions) |
| `miri` | `cargo miri test`, `MIRIFLAGS=-Zmiri-disable-isolation` | undefined behaviour of the Rust code (invalid pointers, aliasing (Stacked Borrows), uninitialised reads, invalid values, data races), leaks |

Rust has no UndefinedBehaviorSanitizer counterpart to C's: integer overflow is the `debug`
mode's overflow checks, every other kind of undefined behaviour is Miri's job.
MemorySanitizer is not used: it needs every linked library (glibc, PAM) built with it.

## Results

Run of 2026-11-20 (`results/{debug,asan,miri}.tsv` hold every test with its outcome and, for a
failure or a Miri skip, the reason). The suite has 191 tests, all in the library; the three
binaries have none, and the crate's single doctest is marked `ignore`.

| Mode | Tests | Pass | Fail | of which host-dependent | Sanitizer / Miri reports | Miri skips |
|---|---:|---:|---:|---:|---|---:|
| `debug` | 191 | 179 | 12 | 12 | none (no overflow panic) | - |
| `asan` | 191 | 178 | 12 | 12 | 0 memory errors; 1 leak report, a harness artefact (below) | - |
| `miri` | 191 | 152 | 9 | 5 (+4, below) | 0 undefined behaviour, 0 leaks | 30 |

- **Host-dependent failures** (fail identically with and without sanitizers; on this NixOS
  machine there are no fixed test accounts, the file-system layout differs and nothing runs
  setuid): `common::command::test::test_build_command_and_args`,
  `common::context::tests::test_build_run_context`, `common::resolve::test::canonicalization`,
  `common::resolve::tests::test_resolve_path`, `su::context::tests::invalid_shell`,
  `sudo::env::environment::tests::test_tzinfo`, `system::audit::test::secure_open_is_predictable`,
  `system::audit::test::test_traverse_secure_open_positive`, `system::interface::test::test_unix_group`,
  `system::interface::test::test_unix_user`, `system::tests::kill_test`,
  `system::tests::test_get_user_and_group_by_id`.
- **ASan leak report** of `system::tests::mark_fds_as_cloexec`: the test forks, and the child
  ends with `exit` while the parent's test harness still owns its allocations; all 39 leaked
  allocations (3.5 KB) come from libtest's `main` (test list, channel, formatter), none from
  sudo-rs code. Harness artefact, not a finding.
- **Miri**: every `sudoers::` test (51 of 51) and every `miri_test_*`/`miri_*` test (9 of 9)
  passes, with all other tests that stay inside Rust and std (152 in all). The 9 failures: the
  5 host-dependent tests above that Miri can run, plus 4 `system::timestamp` tests that call
  `clock_gettime(CLOCK_BOOTTIME)`, which Miri answers with `EINVAL` (it models only the realtime
  and monotonic clocks); they pass in `debug` and `asan`. Skipped (Miri stopped at an
  operation it does not model; no statement about these tests): 30 tests, by operation:
  `getpwuid_r` 6, `syslog` 5, `posix_spawnattr_init` 4, `getpwnam_r` 3, `fork` 3,
  `sysconf(_SC_GETGR_R_SIZE_MAX)` 2, `sigaction` 2, `openpty` 2, `sysconf(_SC_CLK_TCK)` 1,
  `getppid` 1, `getpgrp` 1 (each test and its operation is in `results/miri.tsv`).

The Miri run was stopped once by systemd-oomd (memory pressure of the shared machine) after 70
tests and continued with `SAN_RESUME=1`; each test runs in its own process, so the recorded
outcomes are unaffected.

## Commands

From the repository root, inside the dev shell (`nix develop`, or `/tmp/sudo-rs-wt/dev` on the
verification machine):

```sh
proofs/sanitizers/run.sh                 # all three modes, then the summary table
proofs/sanitizers/run.sh debug asan      # selected modes
SAN_FILTER=sudoers:: proofs/sanitizers/run.sh miri
```

Per mode the script builds the test binaries, lists their tests (`--list --format terse`) and
runs each as `<test binary> --exact <name> --test-threads=1` (Miri: `cargo miri test --lib --
--exact <name>`), with a time limit (120 s, Miri 1800 s). Results land in
`$SAN_OUT/<mode>/results.tsv` (test, status, detail) with one log per test. Toolchain: rustup
`nightly-2026-11-20` (rustc 1.102.0-nightly 6905905bb, LLVM 23.1.6, miri 0.1.0) with
`rust-src` and `miri`; `llvm-symbolizer` from nixpkgs for symbolised ASan reports. The script
fetches rustup, llvm and jq from nixpkgs when they are missing.
