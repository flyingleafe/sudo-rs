#!/usr/bin/env bash
# Build and run the libFuzzer targets of fuzz/ (see fuzz/README.md).
#
#   nix develop -c fuzz/run.sh build                 build every target
#   nix develop -c fuzz/run.sh seed                  write the seed corpora (fuzz/seeds.py)
#   nix develop -c fuzz/run.sh fuzz <target...>      fuzz the named targets (built and seeded)
#   nix develop -c fuzz/run.sh campaign [target...]  build, seed, fuzz every (or the named) target
#   nix develop -c fuzz/run.sh coverage [target...]  line coverage of the corpora
#   nix develop -c fuzz/run.sh summary               table of the last campaign
#
# Run from the repository root; the dev shell provides gcc and linux-pam. The campaign runs the
# targets in batches of FUZZ_PARALLEL processes (one core each), every target for FUZZ_SECONDS,
# in libFuzzer's fork mode with one worker, which keeps fuzzing after a crash, a timeout or an
# out-of-memory input and saves each of them under $FUZZ_OUT/<target>/artifacts/.
#
# Environment:
#   FUZZ_TOOLCHAIN  rustup toolchain (default nightly-2026-11-20)
#   FUZZ_OUT        corpora, logs and artifacts (default ${TMPDIR:-/tmp}/sudo-rs-fuzz)
#   FUZZ_SECONDS    seconds per target (default 1800)
#   FUZZ_PARALLEL   targets fuzzed at the same time (default 4)
#   FUZZ_ARGS       extra libFuzzer arguments
set -uo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(dirname "$here")
tc=${FUZZ_TOOLCHAIN:-nightly-2026-11-20}
out=${FUZZ_OUT:-${TMPDIR:-/tmp}/sudo-rs-fuzz}
seconds=${FUZZ_SECONDS:-1800}
parallel=${FUZZ_PARALLEL:-4}
all_targets=(sudoers_parse sudoers_decide sudoers_defaults sudo_cli su_cli visudo_cli timestamp name_escape)
dict_targets=" sudoers_parse sudoers_decide sudoers_defaults "

nix_bin() { echo "$(nix build --no-link --print-out-paths "nixpkgs#$1")/bin"; }
command -v rustup > /dev/null || PATH="$(nix_bin rustup):$PATH"
command -v cargo-fuzz > /dev/null || PATH="$(nix_bin cargo-fuzz):$PATH"
command -v python3 > /dev/null || PATH="$(nix_bin python3):$PATH"
if ! rustup run "$tc" rustc -V > /dev/null 2>&1; then
  rustup toolchain install "$tc" --profile minimal --component rust-src,llvm-tools
fi
export RUSTUP_TOOLCHAIN=$tc
# the rustup proxies (cargo, rustc) must shadow the dev shell's pinned cargo
PATH="$(dirname "$(command -v rustup)"):$PATH"
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$out/target}
cd "$root" || exit 2

# libFuzzer's defaults: release build with debug assertions and overflow checks, AddressSanitizer
build() {
  cargo fuzz build -O --debug-assertions "$@"
}

binary() { echo "$CARGO_TARGET_DIR/x86_64-unknown-linux-gnu/release/$1"; }

seed() {
  if [ ! -d "$out/seeds" ]; then
    python3 "$here/seeds.py" "$out/seeds"
  fi
  local t
  for t in "${all_targets[@]}"; do
    if [ ! -d "$out/corpus/$t" ]; then
      mkdir -p "$out/corpus/$t"
      cp "$out/seeds/$t"/* "$out/corpus/$t/"
    fi
  done
}

fuzz_one() {
  local t=$1 dir=$out/$t
  mkdir -p "$dir/artifacts"
  local dict=()
  case $dict_targets in *" $t "*) dict=(-dict="$out/seeds/sudoers.dict") ;; esac
  # shellcheck disable=SC2086
  "$(binary "$t")" "$out/corpus/$t" "${dict[@]}" \
    -fork=1 -ignore_crashes=1 -ignore_timeouts=1 -ignore_ooms=1 \
    -rss_limit_mb=2048 -timeout=600 -max_total_time="$seconds" \
    -artifact_prefix="$dir/artifacts/" -print_final_stats=1 ${FUZZ_ARGS:-} \
    > "$dir/fuzz.log" 2>&1
  echo "$t: exit $?"
}

# fuzz <target...>: in batches of $parallel targets fuzzed at the same time
fuzz() {
  local targets=("$@") i
  [ ${#targets[@]} -gt 0 ] || targets=("${all_targets[@]}")
  for ((i = 0; i < ${#targets[@]}; i += parallel)); do
    local batch=("${targets[@]:i:parallel}") t
    echo "batch: ${batch[*]} (${seconds}s)"
    for t in "${batch[@]}"; do
      fuzz_one "$t" &
    done
    wait
  done
}

campaign() {
  build || exit 1
  seed
  fuzz "$@"
  summary "$@"
}

# the last fork-mode status line: "#<execs>: cov: <edges> ft: <features> corp: <inputs> ...
#  oom/timeout/crash: <o>/<t>/<c> time: <s>s job: <j> ..."
summary() {
  local targets=("$@") t
  [ ${#targets[@]} -gt 0 ] || targets=("${all_targets[@]}")
  printf '%-17s %7s %12s %7s %8s %7s %6s %8s %6s %9s\n' \
    target seconds executions cov features corpus crash timeout oom artifacts
  for t in "${targets[@]}"; do
    local log=$out/$t/fuzz.log line
    [ -s "$log" ] || continue
    line=$(grep -E '^#[0-9]+: cov: ' "$log" | tail -1)
    awk -v t="$t" -v arts="$(find "$out/$t/artifacts" -type f 2>/dev/null | wc -l)" '{
      execs = substr($1, 2); sub(":", "", execs)
      for (i = 2; i <= NF; i++) {
        if ($i == "cov:") cov = $(i + 1); if ($i == "ft:") ft = $(i + 1)
        if ($i == "corp:") corp = $(i + 1); if ($i == "time:") time = $(i + 1)
        if ($i == "oom/timeout/crash:") { split($(i + 1), a, "/"); oom = a[1]; to = a[2]; cr = a[3] }
      }
      sub("s$", "", time)
      printf "%-17s %7s %12s %7s %8s %7s %6s %8s %6s %9s\n", t, time, execs, cov, ft, corp, cr, to, oom, arts
    }' <<< "$line"
  done
}

coverage() {
  local targets=("$@") t
  [ ${#targets[@]} -gt 0 ] || targets=("${all_targets[@]}")
  local sysroot llvm
  sysroot=$(rustc --print sysroot)
  llvm=$sysroot/lib/rustlib/x86_64-unknown-linux-gnu/bin
  for t in "${targets[@]}"; do
    cargo fuzz coverage "$t" "$out/corpus/$t" > "$out/$t/coverage.log" 2>&1 || {
      echo "$t: coverage run failed, see $out/$t/coverage.log"
      continue
    }
    "$llvm/llvm-cov" report "$CARGO_TARGET_DIR/x86_64-unknown-linux-gnu/coverage/x86_64-unknown-linux-gnu/release/$t" \
      -instr-profile="$here/coverage/$t/coverage.profdata" \
      -ignore-filename-regex='(\.cargo/registry|rustlib|fuzz/fuzz_targets|src/fuzz_api\.rs)' \
      > "$out/$t/coverage.txt" 2>&1
    echo "== $t"
    grep -E '^(Filename|TOTAL)|src/' "$out/$t/coverage.txt" |
      awk '$1 == "Filename" || $1 == "TOTAL" || $(NF - 2) != "0" { print }' | sed "s|$root/||"
  done
}

cmd=${1:-}
shift || true
case $cmd in
  build) build "$@" ;;
  seed) seed ;;
  fuzz) fuzz "$@" ;;
  campaign) campaign "$@" ;;
  coverage) coverage "$@" ;;
  summary) summary "$@" ;;
  *) sed -n '2,10p' "$0" >&2; exit 2 ;;
esac
