# Compliance-suite evidence for the Aeneas refactor

Question: did refactoring `src/sudoers/` for Aeneas extraction (commits `a3bb8467`, `8e70b3b6`,
`d9947d3f`, `ccf4489e`, `d3d394fb`, `46d955a1`) change sudo-rs behaviour? We ran the project's own
compliance suite (`test-framework/sudo-compliance-tests`) against sudo-rs built from:

- **A**: upstream baseline `81dff9a1` (pristine clone `/tmp/fi/src/sudo-rs`);
- **B**: the fork at `5002dab6` (`git archive HEAD` export; its `src/` equals `46d955a1`).

`test-framework/` is identical in both trees, so both runs execute the same 863 tests.

## How to run

```
proofs/compliance/run.sh <tree-A> <tree-B> [libtest filter/args...]
# e.g.
git archive HEAD | tar -x -C /tmp/compliance/B
proofs/compliance/run.sh /tmp/fi/src/sudo-rs /tmp/compliance/B
```

For each tree the script deletes the `sudo-test-rs` image, then runs, in `<tree>/test-framework`,

```
env -u CI SUDO_UNDER_TEST=ours CARGO_TARGET_DIR=$OUT/target \
  nix shell nixpkgs#cargo nixpkgs#rustc nixpkgs#gcc -c \
  cargo test --locked -p sudo-compliance-tests -- --test-threads $(nproc)
```

The framework builds the `sudo-test-rs` Docker image from that tree (`ours.linux.Dockerfile`,
features `gettext,pam-login,unstable-remote-sudoers`) and runs each test in a fresh container.
Per-test outcomes go to `$OUT/{A,B}.results` (sorted `name ok|FAILED|ignored`, `OUT` defaults to
`/tmp/compliance`), and the script prints their `diff`; exit 0 means identical outcomes.
Trees run sequentially because the image tag is fixed. No filter was used: the full suite ran.
`#[ignore]`d tests (features sudo-rs does not implement) are not run, as in upstream CI.

## Results (full suite, 863 tests, about 10-20 min per tree on 14 cores)

| Run | Tree | passed | failed | ignored |
|---|---|---|---|---|
| 1 | A `81dff9a1` | 827 | 0 | 36 |
| 1 | B `d3d394fb` (earlier HEAD) | 826 | 1 | 36 |
| 2 | A `81dff9a1` | 826 | 1 | 36 |
| 2 | B `5002dab6` (src = `46d955a1`) | **827** | **0** | 36 |

Each run differed in exactly one test, and in both cases it was a timing flake unrelated to sudoers:

- Run 1, B: `sudo::child_process::signal_handling::no_tty::signal_is_forwarded_to_child` failed with
  `program failed with exit status: 143` (the `kill-sudo.sh` helper was itself killed by SIGTERM,
  a race between `pidof sudo` and the sudo process). Re-run 30 times in isolation: 30/30 pass on A and on B.
- Run 2, A (upstream): `sudo::flag_background::stdin_pipe` hung (the background `sudo -b`
  became defunct and `/tmp/barrier` never appeared); it failed after its container was killed
  by hand 16 minutes later. Re-run 15 times in isolation: 15/15 pass on A and on B.

Neither test reaches policy-dependent behaviour: both use a `ALL ALL=(ALL:ALL) NOPASSWD: ALL`-style sudoers.
Excluding these two flaky tests, the per-test outcome sets of A and B are identical (827 pass, 36 ignored).

### `warn_ignored` ordering

Between `ccf4489e` and `46d955a1` the two `warn_ignored` warnings ("non-unix group ... was ignored",
"ignoring %group syntax in runas_alias ...") could be printed in a different relative order than
upstream; `46d955a1` restores upstream's interleaved evaluation. No compliance test asserts on these
warning strings: the only tests with non-Unix groups (`sudo::flag_list::{short,long}_format::user_non_unix_group*_runas`)
check stdout only and trigger a single warning kind. So the suite does not observe this difference
for either B revision.

## Caveats

- The host sets `CI`, which makes the framework pass `--cache-to=type=local` to `docker buildx`;
  the default `docker` driver rejects it ("Cache export is not supported"), so `run.sh` unsets `CI`.
- The suite is Docker-timing sensitive; a single flake per run is normal. Rerun a suspect test with
  `proofs/compliance/run.sh A B --exact <test-name>`.
- Disk: about 0.4 GB of BuildKit cache (base image, cargo cache mount, layers) plus about 300 MB of
  cargo target and the tree export; all were removed afterwards.
