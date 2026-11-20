#!/usr/bin/env bash
# Copy the sudo-rs source items that the machine-code proof compiles, verbatim, into
# proofs/machine-code/rust/copied/, or (--check) verify that the committed copies are
# byte-identical to sudo-rs's source.
#
#   proofs/machine-code/scripts/copy-source.sh           # (re)write the copies
#   proofs/machine-code/scripts/copy-source.sh --check   # compare, exit 1 on any difference
#
# Each copy is a contiguous line range of one sudo-rs file. --check compares every copy with
# the same range of (a) the file in this checkout and (b) the file at the pinned sudo-rs commit
# PIN below, so a moved or edited item is reported instead of silently drifting.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
repo=$(git -C "$here" rev-parse --show-toplevel)
PIN=bc2fc69e
out=$here/rust/copied

# name  source file  first line  last line  first line's expected text
slices=(
  "name_or_id.rs|src/common/resolve.rs|16|32|#[derive(PartialEq, Debug)]"
  "sudo_string.rs|src/common/string.rs|9|18|const NULL_BYTE: char = '\0';"
  "sudo_string_deref.rs|src/common/string.rs|90|97|impl ops::Deref for SudoString {"
  "sudo_string_debug.rs|src/common/string.rs|99|104|impl fmt::Debug for SudoString {"
  "user_id.rs|src/system/interface.rs|12|14|/// Represents a user ID in the system."
  "user_id_impl.rs|src/system/interface.rs|34|44|impl UserId {"
  "user_id_from_str.rs|src/system/interface.rs|102|108|impl FromStr for UserId {"
)

check=0
[ "${1:-}" = --check ] && check=1
mkdir -p "$out"
status=0
for s in "${slices[@]}"; do
  IFS='|' read -r name file first last anchor <<<"$s"
  cur=$(sed -n "${first},${last}p" "$repo/$file"; echo x)
  pin=$(git -C "$repo" show "$PIN:$file" | sed -n "${first},${last}p"; echo x)
  head_line=$(sed -n "${first}p" "$repo/$file")
  if [ "$head_line" != "$anchor" ]; then
    echo "MISMATCH $file:$first: expected '$anchor', found '$head_line'" >&2
    status=1
    continue
  fi
  if [ "$cur" != "$pin" ]; then
    echo "MISMATCH $file:$first-$last differs between the checkout and $PIN" >&2
    status=1
  fi
  if [ "$check" = 1 ]; then
    if [ "$(cat "$out/$name"; echo x)" = "$cur" ]; then
      echo "identical  rust/copied/$name  =  $file:$first-$last  (checkout and $PIN)"
    else
      echo "MISMATCH rust/copied/$name differs from $file:$first-$last" >&2
      status=1
    fi
  else
    printf '%s' "${cur%x}" > "$out/$name"
    echo "copied     $file:$first-$last  ->  rust/copied/$name"
  fi
done
exit $status
