#!/usr/bin/env bash
# Independent re-check of the machine-code proof.
#
#   proofs/machine-code/scripts/recheck.sh [--fresh]
#
# Without --fresh it works in this checkout but rebuilds everything of its own without caches:
#   1. the copied sudo-rs items are byte-identical to sudo-rs's source (copy-source.sh --check);
#   2. the engine checkout is the pinned commit and its trusted files are unmodified
#      (check-engine.sh, which also compares them with an independent clone);
#   3. a fresh compile + export (new cargo target directory) reproduces the committed
#      SudoRsMachineCode/Generated/ files byte for byte;
#   4. an object file compiled here directly with rustc (not through rust-obj2lean) has, in
#      `.text.sudo_rs_name_or_id_parse_uid`, exactly the instruction words the proof is about
#      (`parseUidWords` in SudoRsMachineCode/Proof.lean) followed by the five words of the
#      panic call, and its relocations all lie in that tail;
#   5. the Lean package is rebuilt from an empty build directory (the engine's compiled
#      libraries are reused), the theorem file is elaborated directly with `lean`, and every
#      `#print axioms` line lists only propext, Classical.choice and Quot.sound.
# With --fresh it first copies the committed tree (git HEAD) of proofs/machine-code into a new
# directory under /tmp, lets Lake clone the engine there afresh, and builds the engine from
# source as well, so no compiled artifact of this checkout is reused.
#
# Heavy steps should run under /tmp/sudo-rs-wt/limited on the shared machine.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)

if [ "${1:-}" = --fresh ]; then
  repo=$(git -C "$here" rev-parse --show-toplevel)
  rel=${here#"$repo"/}
  head=$(git -C "$repo" rev-parse HEAD)
  fresh=$(mktemp -d /tmp/mcode-recheck-fresh.XXXXXX)
  git clone -q --no-checkout "$repo" "$fresh/repo"
  git -C "$fresh/repo" checkout -q --detach "$head"
  echo "== fresh clone of $head in $fresh/repo"
  cd "$fresh/repo/$rel"
  echo "== lake: clone the engine and build it from source"
  env time -f "engine build: %e s wall, %M KiB max RSS of the largest process" \
    lake build ProofLib.SepLogic.LoopTactics ProofLib.SepLogic.Entry ProofLib.AsciiNum \
      ProofLib.Placed.Fetch
  exec ./scripts/recheck.sh
fi

cd "$here"
tmp=$(mktemp -d /tmp/mcode-recheck.XXXXXX)
trap 'rm -rf "$tmp"' EXIT

echo "== 1. copied sources"
./scripts/copy-source.sh --check

echo "== 2. engine"
./scripts/check-engine.sh

echo "== 3. fresh compile and export"
./scripts/export.sh "$tmp/out" >/dev/null
diff -r "$tmp/out/SudoRsMachineCode/Generated" SudoRsMachineCode/Generated
echo "ok   regenerated SudoRsMachineCode/Generated/ is identical to the committed files"

echo "== 4. instruction words against an independently compiled object"
sysroot=$(cd rust && rustc --print sysroot)
host=$(cd rust && rustc -vV | sed -n 's/^host: //p')
bin=$sysroot/lib/rustlib/$host/bin
(cd rust && CARGO_TARGET_DIR=$tmp/target \
  RUSTFLAGS="-C codegen-units=1 -C relocation-model=static -C target-cpu=generic -C no-vectorize-slp -C no-vectorize-loops" \
  CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 CARGO_PROFILE_RELEASE_PANIC=abort CARGO_PROFILE_RELEASE_LTO=off \
  cargo rustc --quiet --release --locked --lib --target aarch64-unknown-linux-gnu -- \
    --emit=obj="$tmp/harness.o")
sec=.text.sudo_rs_name_or_id_parse_uid
"$bin/llvm-objcopy" -O binary --only-section="$sec" "$tmp/harness.o" "$tmp/fn.bin"
od -An -tx4 -v "$tmp/fn.bin" | tr -s ' ' '\n' | sed '/^$/d' > "$tmp/obj.words"
sed -n '/^def parseUidWords/,/^]/p' SudoRsMachineCode/Proof.lean | grep -o '0x[0-9a-f]\{8\}#32' |
  sed 's/^0x//; s/#32$//' > "$tmp/lean.words"
nl=$(wc -l < "$tmp/lean.words")
[ "$nl" -gt 0 ] || { echo "FAIL: no words found in Proof.lean" >&2; exit 1; }
head -n "$nl" "$tmp/obj.words" | cmp -s - "$tmp/lean.words" ||
  { echo "FAIL: parseUidWords differs from the object file" >&2; exit 1; }
tail_words=$(( $(wc -l < "$tmp/obj.words") - nl ))
echo "ok   parseUidWords = the first $nl words of $sec in the object file ($tail_words more words follow)"
"$bin/llvm-readobj" --relocations "$tmp/harness.o" |
  awk -v s=".rela$sec" '$0 ~ "Section .*"s" " {on=1; next} on && /}/ {on=0} on && /0x/ {print $1}' > "$tmp/relocs"
while read -r off; do
  [ $((off)) -ge $((4 * nl)) ] || { echo "FAIL: relocation at $off inside the proved words" >&2; exit 1; }
done < "$tmp/relocs"
echo "ok   all $(wc -l < "$tmp/relocs") relocations of $sec are at or after byte $((4 * nl))"

echo "== 5. Lean: clean build, direct elaboration, axioms"
rm -rf .lake/build
lake build 2>&1 | tail -n 3
lake env lean SudoRsMachineCode/Theorems.lean > "$tmp/axioms.txt" 2>&1 || {
  cat "$tmp/axioms.txt"; echo "FAIL: lean SudoRsMachineCode/Theorems.lean" >&2; exit 1; }
grep "depends on axioms" "$tmp/axioms.txt" || { echo "FAIL: no #print axioms output" >&2; exit 1; }
if grep "depends on axioms" "$tmp/axioms.txt" | grep -v "\[propext, Classical.choice, Quot.sound\]"; then
  echo "FAIL: a theorem depends on other axioms" >&2; exit 1
fi
if grep -q "does not depend on any axioms\|sorryAx" "$tmp/axioms.txt"; then
  echo "FAIL: unexpected axiom report" >&2; exit 1
fi
echo "ok   every #print axioms line is [propext, Classical.choice, Quot.sound]"
echo "== all re-checks passed"
