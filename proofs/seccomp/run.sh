#!/usr/bin/env bash
# Checks of the NOEXEC seccomp filter bytecode against its documented dispatch contract
# (src/exec/noexec/filter_model.rs, filter_tests.rs, kani_proofs.rs). No syscall is made and no
# filter is installed: every check runs the bytecode built by the production `noexec_filter()`
# in a model of the kernel's classic BPF semantics.
#
# Usage (from anywhere):  proofs/seccomp/run.sh [host] [enumerate] [miri] [kani]   (default: all)
#   host       `cargo test` of exec::noexec::filter_tests on the build host
#   enumerate  the ignored enumeration of all 2^32 syscall numbers per architecture value
#              (release build, all CPUs; CPU-heavy: cluster only)
#   miri       the same tests except the enumeration, interpreted by Miri for every target in
#              SECCOMP_TARGETS: each target's own bytecode against that target's contract
#   kani       proofs/kani/run.sh on the NOEXEC filter harness (build host target)
#
# Environment:
#   SECCOMP_OUT        log directory (default: fresh temp dir); results.tsv: check, result, seconds
#   SECCOMP_TOOLCHAIN  rustup toolchain with the miri and rust-src components, for `miri`
#                      (default: nightly-2026-11-20)
#   SECCOMP_TARGETS    target triples for `miri` (default: the list below)
#   CARGO_TARGET_DIR   default: ${TMPDIR:-/tmp}/sudo-rs-seccomp-target
#   KANI_*             passed to proofs/kani/run.sh
set -uo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
out=${SECCOMP_OUT:-$(mktemp -d "${TMPDIR:-/tmp}/sudo-rs-seccomp.XXXXXX")}
toolchain=${SECCOMP_TOOLCHAIN:-nightly-2026-11-20}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-${TMPDIR:-/tmp}/sudo-rs-seccomp-target}
# Every architecture the code recognises (14 contracts), then two it does not.
default_targets="x86_64-unknown-linux-gnu i686-unknown-linux-gnu aarch64-unknown-linux-gnu
  armv7-unknown-linux-gnueabihf mips-unknown-linux-gnu mipsel-unknown-linux-gnu
  mips64-unknown-linux-gnuabi64 mips64el-unknown-linux-gnuabi64 powerpc-unknown-linux-gnu
  powerpc64-unknown-linux-gnu powerpc64le-unknown-linux-gnu riscv32gc-unknown-linux-gnu
  riscv64gc-unknown-linux-gnu s390x-unknown-linux-gnu
  loongarch64-unknown-linux-gnu sparc64-unknown-linux-gnu"
read -r -a targets <<< "$(echo ${SECCOMP_TARGETS:-$default_targets})"
mkdir -p "$out"
results=$out/results.tsv
[ -f "$results" ] || printf 'check\tresult\tseconds\n' > "$results"
module=exec::noexec::filter_tests
main_test=$module::filter_matches_contract_for_every_nr_and_arch
enum_test=$module::filter_matches_contract_for_every_nr_enumerated
failed=0

# record <check> <log> <exit status> <start> <test that must have run>
# The tests write straight to stdout (not captured by libtest), so a line of theirs can split
# libtest's "test <name> ... ok" line: require the name line (not "ignored"), exit 0 and an ok
# summary; a failing test would turn the summary into FAILED.
record() {
  local check=$1 log=$2 rc=$3 start=$4 must=$5 res
  if [ "$rc" -eq 0 ] && grep -q "test $must \.\.\. " "$log" &&
     ! grep -q "test $must \.\.\. ignored" "$log" &&
     grep -q '^test result: ok\.' "$log"; then
    res=PASS
  elif grep -q '^test result: FAILED\.' "$log"; then
    res=FAIL; failed=1
  else
    res=ERROR; failed=1   # no verdict: build error or the run stopped
  fi
  local secs=$(( $(date +%s) - start ))
  printf '%s\t%s\t%s\n' "$check" "$res" "$secs" >> "$results"
  printf '%-5s %6ss  %s  (%s)\n' "$res" "$secs" "$check" "$log"
}

run_host() {
  local log=$out/host.log start=$(date +%s)
  (cd "$root" && cargo test --lib "$module" -- --show-output) > "$log" 2>&1
  record host "$log" $? "$start" "$main_test"
}

run_enumerate() {
  local log=$out/enumerate.log start=$(date +%s)
  # Optimised without LTO: the release profile's `opt-level = "s"` and LTO only slow this down.
  (cd "$root" && CARGO_PROFILE_RELEASE_LTO=false CARGO_PROFILE_RELEASE_OPT_LEVEL=3 \
     cargo test --release --lib "$enum_test" -- --ignored --exact --show-output) > "$log" 2>&1
  record enumerate "$log" $? "$start" "$enum_test"
}

run_miri() {
  local t log start
  for t in "${targets[@]}"; do
    log=$out/miri-$t.log
    start=$(date +%s)
    (cd "$root" && cargo "+$toolchain" miri test --lib --target "$t" -- "$module" --show-output) \
      > "$log" 2>&1
    record "miri $t" "$log" $? "$start" "$main_test"
  done
}

run_kani() {
  local log=$out/kani.log start=$(date +%s) rc
  KANI_LOG_DIR=${KANI_LOG_DIR:-$out/kani} \
    "$root/proofs/kani/run.sh" exec::noexec::kani_proofs::noexec_filter > "$log" 2>&1
  rc=$?
  local res=PASS
  if [ $rc -ne 0 ]; then res=$(awk 'NR > 1 { print $1; exit }' "$log"); res=${res:-ERROR}; failed=1; fi
  local secs=$(( $(date +%s) - start ))
  printf '%s\t%s\t%s\n' kani "$res" "$secs" >> "$results"
  printf '%-5s %6ss  %s  (%s)\n' "$res" "$secs" kani "$log"
}

steps=("$@")
[ ${#steps[@]} -gt 0 ] || steps=(host enumerate miri kani)
for s in "${steps[@]}"; do
  case $s in
    host) run_host ;;
    enumerate) run_enumerate ;;
    miri) run_miri ;;
    kani) run_kani ;;
    *) echo "unknown step: $s (host, enumerate, miri, kani)" >&2; exit 2 ;;
  esac
done

echo "results: $results"
if [ $failed -ne 0 ]; then
  echo FAIL
  exit 1
fi
echo PASS
