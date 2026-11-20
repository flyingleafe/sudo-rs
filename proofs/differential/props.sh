#!/usr/bin/env bash
# Property search on the real sudo-rs code: every property of Differential/Props.lean is
# checked on N generated instances (seed SEED) with the sudo-rs unit-test harness
# (src/sudoers/test/differential.rs); failures are shrunk and confirmed (PropRun.lean).
#
#   cd proofs/differential && nix develop ../.. -c ./props.sh [N] [SEED] [PROPS]
#
# PROPS is a list of property letters (default "a b c d e f g"). Environment: PROPS_OUT
# (default /tmp/sudo-props) receives the shrunk failures and the work files and is replaced
# for the properties that run; CARGO_TARGET_DIR as for cargo; CAP (default 5) failures shrunk
# per class. The summary goes to stdout.
set -euo pipefail

n=${1:-10000}
seed=${2:-1}
props=${3:-a b c d e f g}
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
out=${PROPS_OUT:-/tmp/sudo-props}
cap=${CAP:-5}

echo "== building the oracle and the sudo-rs test binary" >&2
(cd "$here" && lake build oracle >&2)
oracle=$here/.lake/build/bin/oracle
bin=$(cd "$repo" && cargo test --lib --no-run 2>&1 |
  sed -n 's/.*Executable unittests src\/lib.rs (\(.*\))$/\1/p' | tail -n 1)
[ -x "$bin" ] || { echo "error: sudo-rs test binary not found" >&2; exit 2; }

# sudo-rs canonicalises command paths that exist; the generated ones must not
for p in $("$oracle" paths); do
  if [ -e "$p" ]; then
    echo "error: generated command path $p exists on this machine" >&2
    exit 2
  fi
done

mkdir -p "$out"
for p in $props; do
  rm -rf "$out/work-$p" "$out"/"$p"-*
  echo "== property $p" >&2
  "$oracle" prop "$p" "$n" "$seed" "$bin" "$out" "$cap"
  rm -rf "$out/work-$p"
done
