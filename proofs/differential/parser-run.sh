#!/usr/bin/env bash
# Stage P0 of proofs/parser/PLAN.md: generate the parser corpus, dump it with the legacy sudo-rs
# parser, run C sudo 1.9.18 (visudo -c, testsudoers -d, cvtsudoers -f json) on it, and classify
# every difference (proofs/parser/DUMP.md, proofs/parser/C-SUDO.md).
#
#   cd proofs/differential && ./parser-run.sh [N] [SEED]      # inside the dev shell; defaults 200 1
#
# N cases per corpus category and per mutation operator (29 of them, plus 24 fixed inputs).
# Environment: PARSER_SCRATCH (default /tmp/sudo-parser-p0) holds the corpus, the outputs, the
# cargo target dir (CARGO_TARGET_DIR overrides) and the C build (CSUDO_BUILD overrides);
# JOBS (default 4) parallel C workers; SUDO_SRC the sudo 1.9.18 sources (default /tmp/fi/src/sudo).
# Outputs in $PARSER_SCRATCH: corpus.txt, sudo-rs.dump (+ .hostdep), chartable.txt,
# c-sudo.out, differences.tsv, report.md.
set -euo pipefail

n=${1:-200}
seed=${2:-1}
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
scratch=${PARSER_SCRATCH:-/tmp/sudo-parser-p0}
jobs=${JOBS:-4}
mkdir -p "$scratch"

echo "== building the C tools and the generator" >&2
build=$(CSUDO_BUILD="${CSUDO_BUILD:-$scratch/csudo}" JOBS="$jobs" "$here/build-csudo-tools.sh")
(cd "$here" && lake build parser >&2)
parser=$here/.lake/build/bin/parser

echo "== corpus: $n per category, seed $seed" >&2
"$parser" corpus "$seed" "$n" > "$scratch/corpus.txt"
"$parser" categories "$seed" "$n" > "$scratch/categories.txt"

echo "== sudo-rs dump" >&2
(cd "$repo" && CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/target}" \
  SUDO_PARSER_DUMP_CORPUS="$scratch/corpus.txt" \
  SUDO_PARSER_DUMP_OUT="$scratch/sudo-rs.dump" \
  SUDO_PARSER_DUMP_CHARTABLE="$scratch/chartable.txt" \
  cargo test --lib sudoers::test::parser_dump:: -- --test-threads=1 >&2)

echo "== C sudo" >&2
rm -rf "$scratch/work"
"$parser" csudo "$scratch/corpus.txt" "$build" "$scratch/work" "$jobs" > "$scratch/c-sudo.out"

echo "== comparison" >&2
python3 "$here/parser_compare.py" "$scratch/corpus.txt" "$scratch/sudo-rs.dump" \
  "$scratch/c-sudo.out" "$scratch/differences.tsv" | tee "$scratch/report.md"
