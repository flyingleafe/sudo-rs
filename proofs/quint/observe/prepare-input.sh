#!/usr/bin/env bash
# Assemble the read-only input directory of the LifecycleTrace guest run.
#   proofs/quint/observe/prepare-input.sh <commit> <input-dir>
# Unprivileged; needs git, curl and sha256sum, and network access to
# static.crates.io. Every file comes from <commit>, so the guest builds and
# runs exactly that revision with exactly its fixture:
#   src.tar          git archive of <commit>
#   crates/*.crate   the registry packages of <commit>'s Cargo.lock, each
#                    checked against the lock file's sha256 checksum
#   guest-run.sh, sudoers, pam.d-sudo, scenarios   from proofs/quint/observe
#   commit           the full commit id
set -euo pipefail
[ $# -eq 2 ] || { echo "usage: $0 <commit> <input-dir>" >&2; exit 2; }
commit=$(git rev-parse --verify "$1^{commit}")
dir=$2
mkdir -p "$dir/crates"
[ -z "$(ls -A "$dir/crates")" ] || { echo "$dir/crates is not empty" >&2; exit 2; }

git archive --format=tar "$commit" > "$dir/src.tar"
git show "$commit:proofs/quint/observe/guest-run.sh" > "$dir/guest-run.sh"
for f in sudoers pam.d-sudo scenarios; do
  git show "$commit:proofs/quint/observe/fixture/$f" > "$dir/$f"
done
printf '%s\n' "$commit" > "$dir/commit"

# name version checksum of every registry package in the lock file
git show "$commit:Cargo.lock" | awk '
  /^\[\[package\]\]/ { if (n != "" && c != "") print n, v, c; n = v = c = "" }
  /^name = /     { n = $3; gsub(/"/, "", n) }
  /^version = /  { v = $3; gsub(/"/, "", v) }
  /^checksum = / { c = $3; gsub(/"/, "", c) }
  END            { if (n != "" && c != "") print n, v, c }
' | while read -r name version sum; do
  out="$dir/crates/$name-$version.crate"
  curl -fsSL --proto '=https' "https://static.crates.io/crates/$name/$name-$version.crate" -o "$out"
  got=$(sha256sum "$out" | cut -d' ' -f1)
  [ "$got" = "$sum" ] || { echo "checksum mismatch for $name $version: $got != $sum" >&2; exit 1; }
  echo "crate $name $version $sum"
done
echo "input for $commit ready in $dir"
