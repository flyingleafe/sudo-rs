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

Use a dedicated Docker engine with no existing `sudo-test-rs:latest` tag. For each tree
the script starts a fresh BuildKit builder and a fresh Cargo target directory, then runs
the following command from `<tree>/test-framework`:

```
env -u CI SUDO_UNDER_TEST=ours CARGO_TARGET_DIR="$target" BUILDX_BUILDER="$builder" \
  nix shell nixpkgs#cargo nixpkgs#rustc nixpkgs#gcc -c \
  cargo test --locked -p sudo-compliance-tests -- --test-threads $(nproc)
```

`sudo-test` embeds `CARGO_MANIFEST_DIR` when compiled. Sharing a Cargo target can reuse
the first tree's helper and silently build its Docker image twice. The Dockerfile also
has a writable Cargo cache mount; each tree gets an independent builder so that mount
cannot supply the other tree's binaries. The fixed image tag is used sequentially.

The framework builds with `gettext,pam-login,unstable-remote-sudoers` and runs each test
in a fresh container. `$OUT/{A,B}.results` record the per-test outcomes; `.image` records
the image ID and `.sha256` records the installed `sudo`, `su` and `visudo` hashes before
the image tag is removed. Exit 0 means identical completed outcome sets, **not** that
every test passed. Check the outcome counts and the artifact identities for the two
revisions being compared. The default run uses no filter and does not run ignored tests.

## Results (full suite, 863 tests, about 10-20 min per tree on 14 cores)

| Run | Tree | passed | failed | ignored |
|---|---|---|---|---|
| 1 | A `81dff9a1` | 827 | 0 | 36 |
| 1 | B `d3d394fb` (earlier HEAD) | 826 | 1 | 36 |
| 2 | A `81dff9a1` | 826 | 1 | 36 |
| 2 | B `5002dab6` (src = `46d955a1`) | **827** | **0** | 36 |

These are historical libtest counts. Run 1 exported the **same** image configuration
(`584150968c95…`) on both sides, so it is not evidence that the two revisions agreed.
Run 2 logged distinct image configurations (`584150968c95…` and `d893dc284b43…`);
the old driver did not retain installed-binary hashes.

Each pair of logs differed in one per-test outcome:

- Run 1, B: `sudo::child_process::signal_handling::no_tty::signal_is_forwarded_to_child` failed with
  `program failed with exit status: 143` (the `kill-sudo.sh` helper was itself killed by SIGTERM,
  a race between `pidof sudo` and the sudo process). Re-run 30 times in isolation: 30/30 pass on A and on B.
- Run 2, A (upstream): `sudo::flag_background::stdin_pipe` hung (the background `sudo -b`
  became defunct and `/tmp/barrier` never appeared); it failed after its container was killed
  by hand 16 minutes later. Re-run 15 times in isolation: 15/15 pass on A and on B.

Neither test reaches policy-dependent behaviour: both use a `ALL ALL=(ALL:ALL) NOPASSWD: ALL`-style sudoers.
In run 2 all recorded outcomes except `stdin_pipe` matched.

### Run 3: after the list/validate, authorization and alias-table refactors

Later commits changed `src/sudoers/` again: typed tag modifiers, the alias-order helpers, the
pure functions behind `sudo -l` and `sudo -v`, the `runcwd` conversion in `policy.rs`, and
`sanitize_alias_tables`. Only tree B was run, with 8 test threads, and compared with the
stored results above (the test framework is unchanged, so the 863 tests are the same).

| Run | Tree | passed | failed | ignored |
|---|---|---|---|---|
| 3 | B `495048ed` | 827 | 0 | 36 |
| 3 | B `82589e95` | 827 | 0 | 36 |

Both outcome sets equal run 2 B test for test. Against run 2 A they differ only in
`sudo::flag_background::stdin_pipe`, the upstream flake described above.

### Run 4: parser rewrite, isolated builds

The two-vCPU KVM guest ran the default, unfiltered suite on baseline `70fdb56b` and
candidate `58a225fe`. **827 passed, 0 failed, 36 ignored on each tree; zero outcomes
changed across the same 863 test names.** Each helper compiled in its own source
tree. The builders used the same base image (`6f14b2b4b278…`), but the installed
`/usr/bin/sudo` hashes differed: `fbed553b54ae…` on A, `cd38f67be2cb…` on B.

An earlier attempt is excluded: both runs completed but used the same image because
the Cargo target was shared. Neither that attempt nor the ignored tests is counted
as evidence of candidate behavior.

### `warn_ignored` ordering

Between `ccf4489e` and `46d955a1` the two `warn_ignored` warnings ("non-unix group ... was ignored",
"ignoring %group syntax in runas_alias ...") could be printed in a different relative order than
upstream; `46d955a1` restores upstream's interleaved evaluation. No compliance test asserts on these
warning strings: the only tests with non-Unix groups (`sudo::flag_list::{short,long}_format::user_non_unix_group*_runas`)
check stdout only and trigger a single warning kind. So the suite does not observe this difference
for either B revision.

## Caveats

- `run.sh` unsets `CI`; it does not import or export the hosted CI's builder cache.
- The suite is Docker-timing sensitive; a single flake per run is normal. Rerun a suspect test with
  `proofs/compliance/run.sh A B --exact <test-name>`.
- Disk: about 0.4 GB of BuildKit cache (base image, cargo cache mount, layers) plus about 300 MB of
  cargo target and the tree export; all were removed afterwards.
