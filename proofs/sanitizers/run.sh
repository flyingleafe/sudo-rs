#!/usr/bin/env bash
# Run the sudo-rs unit-test suite (every unit-test target of the crate: the library and the
# three binaries) in three modes, one process per test, and summarise the outcome per mode.
#
#   debug  plain debug build (overflow checks and debug assertions on): the baseline
#   asan   AddressSanitizer + LeakSanitizer, std rebuilt with the sanitizer (-Zbuild-std)
#   miri   Miri interpreter (undefined behaviour, aliasing, leaks); tests that reach a foreign
#          function or a system call Miri does not model are recorded as skipped, with the
#          operation Miri refused as the reason
#
# Usage (repository root, inside the dev shell, which provides gcc and linux-pam):
#   nix develop -c proofs/sanitizers/run.sh [debug] [asan] [miri]     (default: all three)
#
# Environment:
#   SAN_TOOLCHAIN   rustup toolchain (default nightly-2026-11-20; needs miri and rust-src)
#   SAN_OUT         output directory (default ${TMPDIR:-/tmp}/sudo-rs-sanitizers)
#   SAN_FILTER      only run tests whose name contains this string
#   SAN_TIMEOUT     per-test time limit in seconds (default 120; miri: 1800)
#   SAN_RESUME=1    keep the tests already in <mode>/results.tsv (continue an interrupted run)
#   MIRIFLAGS       default -Zmiri-disable-isolation (tests read files and the clock)
#
# Output: $SAN_OUT/<mode>/results.tsv (test, status, detail), one log per test under
# $SAN_OUT/<mode>/logs, and a summary table on stdout. Statuses:
#   pass, fail (test failed, no sanitizer report), ignored, timeout,
#   asan (AddressSanitizer report), leak (LeakSanitizer report), ub (Miri: undefined
#   behaviour), miri-leak (Miri: memory leaked), skip (Miri: unsupported operation).
# A test that fails in debug mode too is host-dependent (`host` column of the summary).
set -uo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../.." && pwd)
tc=${SAN_TOOLCHAIN:-nightly-2026-11-20}
out=${SAN_OUT:-${TMPDIR:-/tmp}/sudo-rs-sanitizers}
filter=${SAN_FILTER:-}
target=x86_64-unknown-linux-gnu

modes=("$@")
[ ${#modes[@]} -gt 0 ] || modes=(debug asan miri)
for m in "${modes[@]}"; do
  case $m in debug | asan | miri) ;; *) echo "unknown mode: $m (debug, asan, miri)" >&2; exit 2 ;; esac
done

# ------------------------------------------------------------------ tools

nix_bin() { echo "$(nix build --no-link --print-out-paths "nixpkgs#$1")/bin"; }
command -v rustup > /dev/null || PATH="$(nix_bin rustup):$PATH"
command -v llvm-symbolizer > /dev/null || PATH="$(nix_bin llvm):$PATH"
command -v jq > /dev/null || PATH="$(nix_bin jq):$PATH"
export ASAN_SYMBOLIZER_PATH=${ASAN_SYMBOLIZER_PATH:-$(command -v llvm-symbolizer)}
if ! rustup run "$tc" rustc -V > /dev/null 2>&1; then
  rustup toolchain install "$tc" --profile minimal --component miri,rust-src
fi
export RUSTUP_TOOLCHAIN=$tc
# the rustup proxies (cargo, rustc) must shadow the dev shell's pinned cargo
PATH="$(dirname "$(command -v rustup)"):$PATH"

cd "$root" || exit 2
export CARGO_MANIFEST_DIR=$root

# ------------------------------------------------------------------ helpers

# classify <log> <exit status> -> "status<TAB>detail"
classify() {
  local log=$1 st=$2 line
  if line=$(grep -m1 -E '^(==[0-9]+==)?ERROR: AddressSanitizer' "$log"); then
    printf 'asan\t%s' "$(grep -m1 '^SUMMARY: AddressSanitizer' "$log" || echo "$line")"
  elif grep -q -E '^(==[0-9]+==)?ERROR: LeakSanitizer' "$log"; then
    printf 'leak\t%s' "$(grep -m1 '^SUMMARY: AddressSanitizer' "$log")"
  elif line=$(grep -m1 -o -E 'error: Undefined Behavior.*' "$log"); then
    printf 'ub\t%s' "${line#error: }"
  elif line=$(grep -m1 -o -E 'error: unsupported operation.*' "$log"); then
    printf 'skip\t%s' "${line#error: unsupported operation: }"
  elif line=$(grep -m1 -o -E 'error: memory leaked.*' "$log"); then
    printf 'miri-leak\t%s' "${line#error: }"
  elif [ "$st" = 124 ]; then
    printf 'timeout\t'
  elif grep -q -E '^test result: ok\. 0 passed; 0 failed; 1 ignored' "$log"; then
    printf 'ignored\t'
  elif [ "$st" = 0 ] && grep -q -E '^test result: ok\. 1 passed' "$log"; then
    printf 'pass\t'
  else
    line=$(grep -m1 -A1 -E "panicked at" "$log" | tail -1)
    printf 'fail\t%s' "${line:-exit status $st}"
  fi
}

# run_tests <mode> <timeout> <command prefix...>: the prefix gets `--exact <name>` appended
run_tests() {
  local mode=$1 limit=$2
  shift 2
  local dir=$out/$mode name log st res
  mkdir -p "$dir/logs"
  if [ "${SAN_RESUME:-0}" != 1 ] || [ ! -f "$dir/results.tsv" ]; then
    : > "$dir/results.tsv"
  fi
  while read -r name; do
    [ -n "$name" ] || continue
    if cut -f1 "$dir/results.tsv" | grep -q -x -F -- "$name"; then
      continue
    fi
    log=$dir/logs/$name.log
    timeout -k 10 "$limit" "$@" --exact "$name" --test-threads=1 > "$log" 2>&1
    st=$?
    res=$(classify "$log" "$st")
    printf '%s\t%s\n' "$name" "$res" >> "$dir/results.tsv"
    printf '%-9s %s\n' "${res%%$'\t'*}" "$name"
  done < "$dir/tests.txt"
}

# list_tests <binary...>: test names of the given test binaries, filtered by SAN_FILTER
list_tests() {
  "$@" --list --format terse 2>/dev/null | sed -n 's/: test$//p' | grep -F -- "$filter" | sort
}

# native_mode <mode> <target dir> <cargo args...>
native_mode() {
  local mode=$1 tdir=$2
  shift 2
  local dir=$out/$mode bins bin
  mkdir -p "$dir"
  bins=$(CARGO_TARGET_DIR=$tdir cargo test --lib --bins --no-run --message-format=json "$@" \
    2> "$dir/build.log" |
    jq -r 'select(.reason == "compiler-artifact" and .profile.test and .executable != null) | .executable')
  [ -n "$bins" ] || { echo "$mode: build failed, see $dir/build.log" >&2; return 1; }
  : > "$dir/tests.txt"
  : > "$dir/results.tsv.all"
  for bin in $bins; do
    list_tests "$bin" > "$dir/tests.txt"
    run_tests "$mode" "${SAN_TIMEOUT:-120}" "$bin"
    cat "$dir/results.tsv" >> "$dir/results.tsv.all"
  done
  mv "$dir/results.tsv.all" "$dir/results.tsv"
}

# ------------------------------------------------------------------ modes

run_debug() {
  native_mode debug "$out/target-debug"
}

run_asan() {
  RUSTFLAGS="-Zsanitizer=address" RUSTDOCFLAGS="-Zsanitizer=address" \
    ASAN_OPTIONS=${ASAN_OPTIONS:-detect_leaks=1:abort_on_error=0:symbolize=1} \
    native_mode asan "$out/target-asan" -Zbuild-std --target "$target"
}

run_miri() {
  local dir=$out/miri
  mkdir -p "$dir"
  export MIRIFLAGS=${MIRIFLAGS:--Zmiri-disable-isolation}
  CARGO_TARGET_DIR=$out/target-miri cargo miri test --lib --bins -- --list --format terse \
    2> "$dir/build.log" | sed -n 's/: test$//p' | grep -F -- "$filter" | sort > "$dir/tests.txt"
  [ -s "$dir/tests.txt" ] || { echo "miri: no tests listed, see $dir/build.log" >&2; return 1; }
  # the binaries have no unit tests, so only the library target is run per test
  CARGO_TARGET_DIR=$out/target-miri run_tests miri "${SAN_TIMEOUT:-1800}" \
    cargo miri test --lib --
}

for m in "${modes[@]}"; do
  echo "== $m"
  "run_$m"
done

# ------------------------------------------------------------------ summary

host_failures() { [ -s "$out/debug/results.tsv" ] && awk -F'\t' '$2 == "fail" || $2 == "timeout" { print $1 }' "$out/debug/results.tsv"; }

echo
printf '%-6s %6s %6s %6s %8s %6s %6s %6s %6s %6s %6s %6s\n' \
  mode tests pass fail ignored timeout asan leak ub m-leak skip host
for m in "${modes[@]}"; do
  f=$out/$m/results.tsv
  [ -s "$f" ] || continue
  hosts=$(host_failures | sort)
  host=$(awk -F'\t' '$2 == "fail" || $2 == "timeout" { print $1 }' "$f" | sort | comm -12 - <(echo "$hosts") | grep -c . || true)
  awk -F'\t' -v m="$m" -v host="$host" '
    { n++; c[$2]++ }
    END { printf "%-6s %6d %6d %6d %8d %6d %6d %6d %6d %6d %6d %6d\n", m, n, c["pass"], c["fail"],
          c["ignored"], c["timeout"], c["asan"], c["leak"], c["ub"], c["miri-leak"], c["skip"], host }' "$f"
done
echo
echo "per-test results: $out/<mode>/results.tsv; logs: $out/<mode>/logs"
for m in "${modes[@]}"; do
  f=$out/$m/results.tsv
  [ -s "$f" ] || continue
  awk -F'\t' -v m="$m" '$2 != "pass" && $2 != "skip" && $2 != "ignored" { printf "%s: %-9s %s  %s\n", m, $2, $1, $3 }' "$f"
done
