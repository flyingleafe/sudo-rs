#!/usr/bin/env bash
# Run sudo-rs's compliance suite (SUDO_UNDER_TEST=ours) against two source trees
# and print the diff of per-test outcomes.
#
# Usage: proofs/compliance/run.sh <tree-A> <tree-B> [cargo-test filter...]
#   <tree-X>: a sudo-rs source directory (git checkout or `git archive` export).
# Env:  OUT (default /tmp/compliance), THREADS (default: nproc).
# Results per tree: log, sorted results, image ID and installed-binary SHA-256s.
# Use a dedicated Linux Docker engine; the framework requires the tag sudo-test-rs:latest.
# Exit status: 0 for identical completed outcomes, nonzero for differences or setup errors.
set -euo pipefail

[ $# -ge 2 ] || { echo "usage: $0 <tree-A> <tree-B> [filter...]" >&2; exit 2; }
A=$(realpath "$1"); B=$(realpath "$2"); shift 2
outcomes=$(dirname "$(realpath "${BASH_SOURCE[0]}")")/outcomes.awk
OUT=${OUT:-/tmp/compliance}
THREADS=${THREADS:-$(nproc)}
mkdir -p "$OUT"
OUT=$(realpath "$OUT")
tag=sudo-test-rs:latest
existing=$(docker image ls -q --filter "reference=$tag")
[ -z "$existing" ] || { echo "use an isolated engine without an existing $tag image" >&2; exit 1; }

run_tree() (
  local label=$1 tree=$2 status=0 target builder=
  echo "== $label: $tree" >&2
  # sudo-test embeds CARGO_MANIFEST_DIR to locate the Docker build context. A shared
  # target can silently reuse A's helper in B. The Dockerfile also mounts a mutable
  # Cargo target: give each tree its own BuildKit builder as well as its own host target.
  target=$(mktemp -d "${TMPDIR:-/tmp}/sudo-compliance-target.XXXXXXXX")
  cleanup() {
    if [ -n "$builder" ]; then docker buildx rm "$builder" >/dev/null; fi
    rm -rf -- "$target"
  }
  trap cleanup EXIT
  builder=$(docker buildx create --driver docker-container)
  shift 2
  (
    cd "$tree/test-framework"
    env -u CI SUDO_UNDER_TEST=ours CARGO_TARGET_DIR="$target" BUILDX_BUILDER="$builder" \
      nix shell nixpkgs#cargo nixpkgs#rustc nixpkgs#gcc -c \
      cargo test --locked -p sudo-compliance-tests -- \
        --test-threads "$THREADS" "$@"
  ) >"$OUT/$label.log" 2>&1 || status=$?
  awk -v "status=$status" -f "$outcomes" "$OUT/$label.log" | sort >"$OUT/$label.results"
  local image
  image=$(docker image inspect --format '{{.Id}}' "$tag")
  printf '%s\n' "$image" >"$OUT/$label.image"
  docker run --rm --network=none --entrypoint sha256sum "$image" \
    /usr/bin/sudo /usr/bin/su /usr/sbin/visudo >"$OUT/$label.sha256"
  docker image rm "$tag" >/dev/null
  printf '%s: passed=%s failed=%s ignored=%s total=%s\n' "$label" \
    "$(grep -c ' ok$' "$OUT/$label.results" || true)" \
    "$(grep -c ' FAILED$' "$OUT/$label.results" || true)" \
    "$(grep -c ' ignored$' "$OUT/$label.results" || true)" \
    "$(wc -l <"$OUT/$label.results")"
)

run_tree A "$A" "$@"
run_tree B "$B" "$@"

echo "== diff A.results B.results"
if diff "$OUT/A.results" "$OUT/B.results" | tee "$OUT/diff.txt"; then
  echo "identical outcomes"
else
  exit 1
fi
