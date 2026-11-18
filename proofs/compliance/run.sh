#!/usr/bin/env bash
# Run sudo-rs's compliance suite (SUDO_UNDER_TEST=ours) against two source trees
# and print the diff of per-test outcomes.
#
# Usage: proofs/compliance/run.sh <tree-A> <tree-B> [cargo-test filter...]
#   <tree-X>: a sudo-rs source directory (git checkout or `git archive` export).
# Env:  OUT (default /tmp/compliance), THREADS (default: nproc).
# Results: $OUT/<A|B>.log (raw output), $OUT/<A|B>.results (sorted "name outcome").
# Exit status: 0 if outcome sets are identical, 1 otherwise.
set -euo pipefail

[ $# -ge 2 ] || { echo "usage: $0 <tree-A> <tree-B> [filter...]" >&2; exit 2; }
A=$(realpath "$1"); B=$(realpath "$2"); shift 2
OUT=${OUT:-/tmp/compliance}
THREADS=${THREADS:-$(nproc)}
mkdir -p "$OUT"

run_tree() {
  local label=$1 tree=$2
  echo "== $label: $tree" >&2
  # The image tag `sudo-test-rs` is fixed by the framework; trees therefore run
  # sequentially, and each run rebuilds the image from its own tree.
  docker image rm -f sudo-test-rs >/dev/null 2>&1 || true
  shift 2
  (
    cd "$tree/test-framework"
    # CI=... makes the framework pass buildx cache flags the docker driver rejects.
    env -u CI SUDO_UNDER_TEST=ours CARGO_TARGET_DIR="$OUT/target" \
      nix shell nixpkgs#cargo nixpkgs#rustc nixpkgs#gcc -c \
      cargo test --locked -p sudo-compliance-tests -- \
        --test-threads "$THREADS" "$@"
  ) >"$OUT/$label.log" 2>&1 || true
  # libtest lines: "test <name> ... ok|FAILED|ignored"
  sed -nE 's/^test ([^ ]+) \.\.\. (ok|FAILED|ignored).*/\1 \2/p' "$OUT/$label.log" \
    | sort >"$OUT/$label.results"
  printf '%s: passed=%s failed=%s ignored=%s total=%s\n' "$label" \
    "$(grep -c ' ok$' "$OUT/$label.results" || true)" \
    "$(grep -c ' FAILED$' "$OUT/$label.results" || true)" \
    "$(grep -c ' ignored$' "$OUT/$label.results" || true)" \
    "$(wc -l <"$OUT/$label.results")"
}

run_tree A "$A" "$@"
run_tree B "$B" "$@"
docker image rm -f sudo-test-rs >/dev/null 2>&1 || true

echo "== diff A.results B.results"
if diff "$OUT/A.results" "$OUT/B.results" | tee "$OUT/diff.txt"; then
  echo "identical outcomes"
else
  exit 1
fi
