#!/usr/bin/env bash
# Re-run sudo-rs and testsudoers on one saved case (a file in disagreements/, or any file of
# case records such as the output of `oracle show SEED I`). The spec verdict is the `spec`
# line of the record.
#
#   cd proofs/differential && nix develop ../.. -c ./repro.sh disagreements/.../case-17.case
set -euo pipefail

file=$(realpath "$1")
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
scratch=${DIFF_SCRATCH:-/tmp/sudo-differential}
ts=$(TS_BUILD="$scratch/sudo" "$here/build-testsudoers.sh")
dir=$(mktemp -d "$scratch/repro.XXXXXX")
trap 'rm -rf "$dir"' EXIT

field() { sed -n "s/^$1 //p" "$file"; }

echo "spec:    $(field spec)"
(cd "$repo" && CARGO_TARGET_DIR="$scratch/target" SUDO_DIFF_CASES="$file" \
  SUDO_DIFF_OUT="$dir/sudo-rs.out" cargo test --quiet --lib differential_cases >/dev/null 2>&1)
echo "sudo-rs: $(cut -d' ' -f2- "$dir/sudo-rs.out")"

field passwd > "$dir/passwd"
field group > "$dir/group"
field sudoers > "$dir/sudoers"
# shellcheck disable=SC2046 # flags and command words are single tokens
set -- -p "$dir/passwd" -P "$dir/group" -h "$(field host)" $(field runas) "$(field user)" $(field command)
echo "testsudoers $*  < sudoers:"
sed 's/^/  | /' "$dir/sudoers"
"$ts" "$@" < "$dir/sudoers" || true
