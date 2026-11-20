#!/usr/bin/env bash
# Run the Kani bounded proof harnesses of sudo-rs, one Kani process per harness, each in its own
# memory-limited scope, and print a table with result, wall time and peak memory.
#
# Usage (from anywhere):  proofs/kani/run.sh [harness-substring ...]
#   Without arguments every harness is run. An argument selects the harnesses whose
#   fully qualified name contains it.
#
# Requirements: `cargo-kani` (Kani 0.68.0; default location ~/.cargo/bin) after `cargo kani setup`,
# and a C compiler on PATH for the build scripts of dependencies (the pinned dev shell has one:
# `/tmp/sudo-rs-wt/dev proofs/kani/run.sh`).
#
# Harnesses are the `#[kani::proof]` functions in src/**/kani_proofs.rs; their module path is
# derived from the file path.
#
# Environment:
#   KANI_LIMITED     memory/CPU limiter wrapper (default: /tmp/sudo-rs-wt/limited). Each harness
#                    gets a scope of its own; the peak memory column is that scope's peak
#                    (cargo, kani-compiler, CBMC and the SAT solver together). If the wrapper is
#                    missing, harnesses run unwrapped and the column shows the maximum resident
#                    set size of the largest process instead.
#   KANI_LIMIT_MEM   memory limit per harness (default 8G)
#   KANI_LOG_DIR     directory for the per-harness logs and results.tsv (default: fresh temp dir)
#   KANI_TARGET_DIR  cargo target directory (default: ${TMPDIR:-/tmp}/sudo-rs-kani-target)
#   KANI_TIMEOUT     wall-clock limit per harness, as for timeout(1) (default: none)
set -uo pipefail

kani_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$kani_dir/../.." && pwd)
limited=${KANI_LIMITED:-/tmp/sudo-rs-wt/limited}
mem=${KANI_LIMIT_MEM:-8G}
logdir=${KANI_LOG_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/sudo-rs-kani.XXXXXX")}
export CARGO_TARGET_DIR=${KANI_TARGET_DIR:-${TMPDIR:-/tmp}/sudo-rs-kani-target}
mkdir -p "$logdir"

command -v cargo-kani >/dev/null || PATH=$HOME/.cargo/bin:$PATH
command -v cargo-kani >/dev/null || { echo "cargo-kani not found (cargo install --locked kani-verifier)" >&2; exit 2; }
command -v cc >/dev/null || { echo "no C compiler on PATH; run inside the dev shell" >&2; exit 2; }

# Fully qualified harness names, in file order.
harnesses=()
while IFS= read -r f; do
  rel=${f#"$root"/src/}
  rel=${rel%.rs}
  rel=${rel%/mod}
  mod=${rel//\//::}
  while IFS= read -r name; do
    harnesses+=("$mod::$name")
  done < <(awk '/#\[kani::proof\]/ { want = 1; next }
                want && match($0, /fn [A-Za-z0-9_]+/) { print substr($0, RSTART + 3, RLENGTH - 3); want = 0 }' "$f")
done < <(find "$root/src" -name kani_proofs.rs | sort)

selected=()
for h in "${harnesses[@]}"; do
  if [ $# -eq 0 ]; then selected+=("$h"); continue; fi
  for pat in "$@"; do
    case $h in *"$pat"*) selected+=("$h"); break ;; esac
  done
done
[ ${#selected[@]} -gt 0 ] || { echo "no harness matches: $*" >&2; exit 2; }

echo "kani: $(cargo-kani --version 2>/dev/null | head -n 1); ${#selected[@]} harnesses; logs: $logdir"
results=$logdir/results.tsv
printf 'harness\tresult\tseconds\tpeak_MiB\n' > "$results"
failed=0
for h in "${selected[@]}"; do
  log=$logdir/${h//::/__}.log
  start=$(date +%s.%N)
  run=(cargo kani --lib -Z stubbing --exact --harness "$h" --output-format terse)
  [ -z "${KANI_TIMEOUT:-}" ] || run=(timeout "$KANI_TIMEOUT" "${run[@]}")
  if [ -x "$limited" ]; then
    (cd "$root" && env -u SUDO_RS_LIMITED LIMIT_MEM="$mem" "$limited" "${run[@]}") > "$log" 2>&1
  else
    (cd "$root" && command time -f 'maxrss_kib %M' "${run[@]}") > "$log" 2>&1
  fi
  rc=$?
  secs=$(awk -v a="$start" -v b="$(date +%s.%N)" 'BEGIN { printf "%.1f", b - a }')
  peak=$(sed -n 's/^limited: peak memory \([0-9]*\) MiB.*/\1/p' "$log" | tail -n 1)
  [ -n "$peak" ] || peak=$(awk '/^maxrss_kib/ { print int($2 / 1024) }' "$log" | tail -n 1)
  # A harness whose `kani::cover!` is not satisfied verified nothing on that path (vacuous).
  uncovered=$(sed -n 's/^ \*\* \([0-9]*\) of \([0-9]*\) cover properties satisfied.*/\1 \2/p' "$log" |
                awk '$1 != $2' | head -n 1)
  if [ $rc -eq 0 ] && grep -q 'Complete - 1 successfully verified harnesses, 0 failures' "$log" &&
     [ -z "$uncovered" ]; then
    res=PASS
  elif [ $rc -eq 124 ]; then
    res=TIME; failed=1
  elif [ $rc -eq 99 ]; then
    res=OOM; failed=1
  else
    res=FAIL; failed=1
  fi
  printf '%s\t%s\t%s\t%s\n' "$h" "$res" "$secs" "${peak:-?}" >> "$results"
  printf '%-4s %7ss %6s MiB  %s\n' "$res" "$secs" "${peak:-?}" "$h"
done

echo "results: $results"
if [ $failed -ne 0 ]; then
  echo "FAIL"
  exit 1
fi
echo "PASS (${#selected[@]} harnesses)"
