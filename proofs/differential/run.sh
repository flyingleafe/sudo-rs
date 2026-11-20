#!/usr/bin/env bash
# Three-way differential test of the sudoers decision: the Lean spec (SudoersSpec.authorize),
# sudo-rs (real parser + Sudoers::check) and C sudo (testsudoers).
#
#   cd proofs/differential && nix develop ../.. -c ./run.sh [N] [SEED]
#
# Environment: DIFF_SCRATCH (default /tmp/sudo-differential) holds the cases, the engine
# outputs, the cargo target dir and the testsudoers build (TS_BUILD and CARGO_TARGET_DIR
# override the last two); JOBS (default nproc) parallel testsudoers workers; MINIMIZE
# (default 20) C disagreements minimised per kind.
# Disagreements are written to ./disagreements/ (replaced on every run).
set -euo pipefail

n=${1:-20000}
seed=${2:-1}
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
scratch=${DIFF_SCRATCH:-/tmp/sudo-differential}
jobs=${JOBS:-$(nproc)}
mincap=${MINIMIZE:-20}
mkdir -p "$scratch"

echo "== building testsudoers and the oracle" >&2
ts=$(TS_BUILD="${TS_BUILD:-$scratch/sudo}" "$here/build-testsudoers.sh")
(cd "$here" && lake build oracle >&2)
oracle=$here/.lake/build/bin/oracle

# sudo-rs canonicalises existing command paths and C sudo compares inodes of existing files;
# the generated paths must not exist so that both compare paths as strings.
for p in $("$oracle" paths); do
  if [ -e "$p" ]; then
    echo "error: generated command path $p exists on this machine" >&2
    exit 2
  fi
done

echo "== generating $n cases (seed $seed) with the spec verdicts" >&2
"$oracle" gen "$n" "$seed" > "$scratch/cases.txt"

echo "== sudo-rs" >&2
(cd "$repo" && CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/target}" \
  SUDO_DIFF_CASES="$scratch/cases.txt" \
  SUDO_DIFF_OUT="$scratch/sudo-rs.out" \
  cargo test --quiet --lib differential_cases -- --nocapture >&2)

echo "== testsudoers" >&2
"$oracle" csudo "$n" "$seed" "$ts" "$scratch/work" "$jobs" > "$scratch/c-sudo.out"

"$oracle" coverage "$n" "$seed"

echo "== comparing" >&2
rm -rf "$here/disagreements"
"$oracle" compare "$n" "$seed" "$scratch/sudo-rs.out" "$scratch/c-sudo.out" \
  "$here/disagreements" "$ts" "$scratch/work" "$jobs" "$mincap"
