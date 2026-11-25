#!/usr/bin/env bash
# Pattern-level comparison of env_keep/env_check entries, unprivileged: sudo-rs `entry_matches`
# (through the test hook `env_pattern_cases`) against C sudo 1.9.18 `matches_env_pattern`
# (through C sudo's own regress checker `plugins/sudoers/regress/env_match/check_env_pattern`).
# Compares matching only, not environment filtering or assembly. Never installs or runs sudo.
#
#   proofs/differential/env/pattern-run.sh OUT
#
# SUDO_SRC selects the pinned read-only C tree, defaulting to the uni-cpu cache when set.
# CARGO_TARGET_DIR optionally reuses an existing Rust build. JOBS controls C parallelism.
# All other build and comparison inputs go in a run-specific temporary directory.
# OUT receives summary.txt (aggregate counts only).
set -euo pipefail

out=${1:?usage: pattern-run.sh OUT}
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../../.." && pwd)
src=${SUDO_SRC:-${OMNIRUN_ROOT:+$OMNIRUN_ROOT/cache/sudo-rs-csudo/sudo}}
: "${src:?set SUDO_SRC to the pinned C sudo 1.9.18 source tree}"
src=$(realpath -- "$src")
jobs=${JOBS:-4}
mkdir -p "$out"
scratch=$(mktemp -d "${TMPDIR:-/tmp}/sudo-env-pattern.XXXXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
export LC_ALL=C

echo "== building C sudo 1.9.18 check_env_pattern" >&2
grep -Fxq "PACKAGE_VERSION='1.9.18'" "$src/configure" || { echo "expected C sudo 1.9.18" >&2; exit 1; }
# The matcher and checker at d58e85d868c79ab92860e22fc2d76756cf8f0e2c.
(
  cd "$src"
  printf '%s\n' \
    'bc9de8b637de91a7384986a562347d2ffa3d97aeac580062f509a06a562cff6a  plugins/sudoers/env_pattern.c' \
    '3569c9c5f1e2d45ad80966d2e1748aceb61896fddd69db55778a88fba3783d61  plugins/sudoers/regress/env_match/check_env_pattern.c' |
    sha256sum --check --status
)
cp -r "$src" "$scratch/sudo"
checker=$scratch/sudo/plugins/sudoers/check_env_pattern
(
  cd "$scratch/sudo"
  ./configure --disable-shared --without-pam --disable-nls --without-sendmail \
    --without-lecture --disable-sasl --without-ldap --disable-log-server --disable-log-client \
    --disable-openssl --disable-gcrypt --without-audit --without-selinux --without-apparmor \
    --disable-zlib --with-noexec=no > configure.log 2>&1 &&
    make -C lib/util -j"$jobs" > make-util.log 2>&1 &&
    make -C plugins/sudoers -j"$jobs" check_env_pattern > make-checker.log 2>&1
) || { echo "failed to build the pinned C checker" >&2; exit 1; }

echo "== validating the checker on ordinary control cases" >&2
printf '%s\n' 'A A=B 1' 'A B=B 0' | "$checker" > "$scratch/controls.out" 2> "$scratch/controls.err"
grep -qx '.*: 2 tests run, 0 errors, 100% success rate' "$scratch/controls.out"

echo "== generating the cases" >&2
python3 "$here/env_pattern.py" gen "$scratch/cases" >&2

echo "== sudo-rs" >&2
(cd "$repo" && CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$scratch/target}" \
  SUDO_ENV_PATTERN_CASES="$scratch/cases/rust.tsv" \
  SUDO_ENV_PATTERN_OUT="$scratch/cases/rust.out" \
  cargo test --locked --quiet --lib sudo::env::filter::tests::env_pattern_cases -- --exact >&2)

echo "== C sudo (check_env_pattern)" >&2
# The checker exits with the number of lines whose result differs from `want` (0 here), i.e.
# the number of matches; that is not a failure.
rc=0
"$checker" "$scratch/cases/c.txt" > "$scratch/cases/c.out" 2> "$scratch/cases/c.err" || rc=$?

echo "== comparing" >&2
python3 "$here/env_pattern.py" compare "$scratch/cases" "$out" "$rc"
