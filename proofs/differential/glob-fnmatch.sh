#!/usr/bin/env bash
# Opt-in conformance check of the sudo-rs command-path matcher (compile_pattern + match_command,
# pinned glob crate) against libc fnmatch(3) with FNM_PATHNAME in the C locale, on a small
# synthetic fixture (src/sudoers/test/glob_fnmatch.rs; scope and untested dialects there).
#
#   ./proofs/differential/glob-fnmatch.sh [OUTDIR]       # default OUTDIR /tmp/glob-fnmatch
#
# Writes OUTDIR/env.txt (versions), test.log and summary.txt. Fails unless exactly one test ran
# and passed. Uses CARGO_TARGET_DIR if set.
set -euo pipefail

out=${1:-${TMPDIR:-/tmp}/glob-fnmatch}
mkdir -p "$out"
out=$(cd "$out" && pwd)
cd "$(dirname "$0")/../.."
export LC_ALL=C

{
  echo "commit $(git rev-parse HEAD 2>/dev/null || echo unknown)"
  rustc --version
  cargo tree --locked -i glob --depth 0
  cargo tree --locked -i libc --depth 0
  ldd --version 2>&1 | head -n 1 || true
} > "$out/env.txt"

status=0
cargo test --locked --lib sudoers::test::glob_fnmatch::glob_fnmatch_conformance \
  -- --exact --ignored --nocapture --test-threads=1 > "$out/test.log" 2>&1 || status=$?
if [ "$status" -ne 0 ] || ! grep -q '^test result: ok. 1 passed;' "$out/test.log"; then
  tail -n 30 "$out/test.log"
  echo "glob-fnmatch: expected exactly one passing test (exit $status)" >&2
  exit 1
fi
# the test prints its summary at the start of a line; compiler diagnostics never start there
grep -E '^glob-fnmatch-summary ' "$out/test.log" > "$out/summary.txt" || true
if [ "$(wc -l < "$out/summary.txt")" -ne 1 ]; then
  echo "glob-fnmatch: expected exactly one summary line in $out/test.log" >&2
  exit 1
fi
cat "$out/env.txt" "$out/summary.txt"
