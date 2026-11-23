#!/usr/bin/env bash
# Stage P0 of proofs/parser/PLAN.md, Lean side: the parser corpus, dumped by the Rust parser and by
# the Lean reference parser (SudoersSpec.Syntax), compared byte for byte (proofs/parser/DUMP.md,
# proofs/parser/P0.md).
#
#   cd proofs/differential && ./parser-lean-run.sh [N] [SEED...]     # inside the dev shell
#
# N cases per corpus category and per mutation operator (default 200), for each SEED (default 1).
# Environment: PARSER_SCRATCH (default /tmp/sudo-parser-p0-lean) holds, per seed, corpus.txt,
# sudo-rs.dump (+ .hostdep, .bases), chartable.txt, lean.dump, differences.txt, report.md; and the
# cargo target dir (CARGO_TARGET_DIR overrides). Exit status 1 if a case disagrees.
set -euo pipefail

n=${1:-200}
shift || true
seeds=("$@")
[ ${#seeds[@]} -gt 0 ] || seeds=(1)
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
scratch=${PARSER_SCRATCH:-/tmp/sudo-parser-p0-lean}
mkdir -p "$scratch"

echo "== building the generator and the Lean dump" >&2
(cd "$here" && lake build parser >&2)
parser=$here/.lake/build/bin/parser

status=0
for seed in "${seeds[@]}"; do
  out=$scratch/seed-$seed
  mkdir -p "$out"
  echo "== seed $seed: corpus ($n per category)" >&2
  "$parser" corpus "$seed" "$n" > "$out/corpus.txt"
  echo "== seed $seed: sudo-rs dump" >&2
  (cd "$repo" && CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/target}" \
    SUDO_PARSER_DUMP_CORPUS="$out/corpus.txt" \
    SUDO_PARSER_DUMP_OUT="$out/sudo-rs.dump" \
    SUDO_PARSER_DUMP_CHARTABLE="$out/chartable.txt" \
    cargo test --lib sudoers::test::parser_dump::dump_corpus -- --test-threads=1 >&2)
  (cd "$repo" && CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/target}" \
    SUDO_PARSER_DUMP_CHARTABLE="$out/chartable.txt" \
    cargo test --lib sudoers::test::parser_dump::write_char_table -- --test-threads=1 >&2)
  echo "== seed $seed: Lean dump" >&2
  "$parser" lean-dump "$out/corpus.txt" "$out/chartable.txt" > "$out/lean.dump"
  echo "== seed $seed: comparison" >&2
  if ! python3 "$here/parser_lean_compare.py" "$out/sudo-rs.dump" "$out/lean.dump" \
      "$out/differences.txt" | tee "$out/report.md"; then
    status=1
  fi
done
exit $status
