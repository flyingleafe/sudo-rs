#!/usr/bin/env bash
# Compile the harness crate (rust/) for aarch64 with the pinned rustc and export the machine
# code to Lean with the engine's own `rust-obj2lean`.
#
#   proofs/machine-code/scripts/export.sh [OUT_DIR]
#
# OUT_DIR defaults to proofs/machine-code (the committed `SudoRsMachineCode/Generated/` files);
# the re-check passes a scratch directory and compares. Requires rustup with the toolchain of
# rust/rust-toolchain.toml (1.98.1 + aarch64-unknown-linux-gnu) and a host C toolchain to
# build `rust-obj2lean`. The engine sources are Lake's checkout at the pinned commit
# (`lake update` / `lake build` fetch it into .lake/packages/prooflib).
#
# Environment: OBJ2LEAN_TARGET_DIR (cargo target dir for rust-obj2lean, default
# /tmp/mcode-obj2lean-target), CARGO_TARGET_DIR (for the harness crate, default a fresh
# temporary directory, so the object is always rebuilt).
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
out=${1:-$here}
engine=${ENGINE_DIR:-$here/.lake/packages/prooflib}
tools=$engine/arm64-semantics/tools
obj2lean_target=${OBJ2LEAN_TARGET_DIR:-/tmp/mcode-obj2lean-target}

[ -f "$tools/Cargo.toml" ] || { echo "engine checkout not found at $engine (run lake update)" >&2; exit 1; }
"$here/scripts/check-engine.sh" "$engine" >/dev/null

# rust-obj2lean, built from the pinned engine sources with their lock file.
(cd "$engine" && cargo build --release --locked --quiet --manifest-path "$tools/Cargo.toml" \
  -p rust-obj2lean --target-dir "$obj2lean_target")
bin=$obj2lean_target/release/rust-obj2lean

tmp_target=
if [ -z "${CARGO_TARGET_DIR:-}" ]; then
  tmp_target=$(mktemp -d /tmp/mcode-harness-target.XXXXXX)
  export CARGO_TARGET_DIR=$tmp_target
fi
trap '[ -n "$tmp_target" ] && rm -rf "$tmp_target"' EXIT

mkdir -p "$out"
(cd "$here/rust" && rustc --version && "$bin" --config "$here/rust/translation.toml" \
  --out-dir "$out")
