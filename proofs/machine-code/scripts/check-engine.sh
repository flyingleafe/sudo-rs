#!/usr/bin/env bash
# Check that the engine checkout Lake uses is the pinned commit and that its trusted files are
# unmodified.
#
#   proofs/machine-code/scripts/check-engine.sh [ENGINE_CHECKOUT]
#
# ENGINE_CHECKOUT defaults to Lake's clone, proofs/machine-code/.lake/packages/prooflib.
# Checks:
#  1. HEAD is the pinned commit PIN and no tracked file differs from it (`git status`).
#  2. The `arm64-semantics` tree of PIN is the v0.51.2 tree ENGINE_TREE.
#  3. Every trusted file (the engine's own classification, see arm64-semantics/README.md:
#     `Arm64/Trusted/**` and the `[TCB]` modules of `tools/rust-obj2lean`) hashes (SHA-256) to
#     the blob recorded in PIN, and to the same file in an independent clone of the
#     repository fetched here at PIN from GitHub (into a temporary directory).
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
engine=${1:-$here/.lake/packages/prooflib}
PIN=b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b
ENGINE_TREE=bcaf7c1ee45df5c0c4578ab177b5bcf2784e08d0
URL=https://github.com/google-deepmind/code-verification

fail() { echo "FAIL: $*" >&2; exit 1; }

head=$(git -C "$engine" rev-parse HEAD)
[ "$head" = "$PIN" ] || fail "engine checkout is at $head, expected $PIN"
echo "ok   engine checkout HEAD = $PIN"
dirty=$(git -C "$engine" status --porcelain --untracked-files=no)
[ -z "$dirty" ] || fail "tracked files differ from $PIN:"$'\n'"$dirty"
echo "ok   no tracked file of the checkout differs from $PIN"
tree=$(git -C "$engine" rev-parse "$PIN:arm64-semantics")
[ "$tree" = "$ENGINE_TREE" ] || fail "arm64-semantics tree is $tree, expected $ENGINE_TREE (v0.51.2)"
echo "ok   arm64-semantics tree = $ENGINE_TREE (v0.51.2)"

ref=$(mktemp -d /tmp/mcode-engine-ref.XXXXXX)
trap 'rm -rf "$ref"' EXIT
git -C "$ref" init -q
git -C "$ref" fetch -q --depth 1 "$URL" "$PIN"
git -C "$ref" checkout -q FETCH_HEAD
[ "$(git -C "$ref" rev-parse HEAD)" = "$PIN" ] || fail "independent clone is not at $PIN"

mapfile -t trusted < <(cd "$engine" && git ls-files \
  'arm64-semantics/Arm64/Trusted/**' \
  'arm64-semantics/Arm64/Trusted.lean' \
  'arm64-semantics/Arm64.lean' \
  'arm64-semantics/Arm64/lakefile.toml' \
  'arm64-semantics/tools/rust-obj2lean/src/lib.rs' \
  'arm64-semantics/tools/rust-obj2lean/src/trusted_common/**' \
  'arm64-semantics/tools/rust-obj2lean/src/trusted_extractor/**')
[ "${#trusted[@]}" -gt 0 ] || fail "no trusted files found"
n=0
for f in "${trusted[@]}"; do
  work=$(sha256sum < "$engine/$f" | cut -d' ' -f1)
  blob=$(git -C "$engine" show "$PIN:$f" | sha256sum | cut -d' ' -f1)
  indep=$(sha256sum < "$ref/$f" | cut -d' ' -f1)
  [ "$work" = "$blob" ] || fail "$f differs from its blob in $PIN"
  [ "$work" = "$indep" ] || fail "$f differs from the independent clone"
  n=$((n + 1))
done
echo "ok   $n trusted files: SHA-256 of the checkout = blob at $PIN = independent clone"
