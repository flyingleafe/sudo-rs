#!/usr/bin/env bash
# Verification gate for sudo-rs: runs the named stages, prints a PASS/FAIL table and
# exits non-zero if any stage fails.
#
# Usage (from the repository root):  nix develop -c proofs/check.sh [stage ...]
#
# Stages (default: tokens spec lean axioms quint rust):
#   tokens        no sorry / admit / native_decide / `decide +native` / axiom declaration in
#                 hand-written Lean files under proofs/ (comments and strings ignored;
#                 .lake/ and the generated *_Template.lean files are skipped)
#   spec          lake build in proofs/spec
#   lean          lake build in proofs/lean (fetches the Mathlib cache first if it is missing)
#   axioms        every `#print axioms` result of the spec and lean builds lists only
#                 propext, Classical.choice, Quot.sound; at least one result must be present
#   quint         proofs/quint/check.sh
#   rust          cargo test --lib sudoers::   (the rest of the unit suite is host-dependent)
#   extract       proofs/extract.sh, then no drift in proofs/lean/SudoRs
#   differential  proofs/differential/run.sh $DIFFERENTIAL_ARGS        (slow; not default)
#   compliance    proofs/compliance/run.sh <base tree> <this tree>      (Docker; not default)
#
# Environment:
#   CHECK_LOG_DIR           directory for the per-stage logs (default: a fresh temp dir)
#   CHECK_CARGO_TARGET_DIR  cargo target dir of the rust stage
#                           (default: ${TMPDIR:-/tmp}/sudo-rs-check-target)
#   AXIOMS_LOGS             space-separated build logs for the axioms stage; by default it uses
#                           the spec/lean logs of this run and builds whichever is missing
#   DIFFERENTIAL_ARGS       arguments for proofs/differential/run.sh
#   COMPLIANCE_BASE         git revision compared against the working tree by the compliance
#                           stage (default: merge-base of HEAD and upstream/main)
set -uo pipefail

proofs=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(dirname "$proofs")
all_stages=(tokens spec lean axioms quint rust extract differential compliance)
default_stages=(tokens spec lean axioms quint rust)
allowed_axioms=(propext Classical.choice Quot.sound)

usage() {
  echo "usage: $0 [stage ...]" >&2
  echo "stages: ${all_stages[*]} (default: ${default_stages[*]})" >&2
  exit 2
}

stages=("$@")
[ ${#stages[@]} -gt 0 ] || stages=("${default_stages[@]}")
for s in "${stages[@]}"; do
  case " ${all_stages[*]} " in *" $s "*) ;; *) echo "unknown stage: $s" >&2; usage ;; esac
done

logdir=${CHECK_LOG_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/sudo-rs-check.XXXXXX")}
mkdir -p "$logdir"

# ---------------------------------------------------------------- tokens

# Print a Lean file with comments (`--`, nested `/- -/`) and string literal contents blanked,
# keeping the line numbering.
strip_lean() {
  awk '
    BEGIN { depth = 0; instr = 0 }
    {
      line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        c = substr(line, i, 1); c2 = substr(line, i, 2)
        if (depth > 0) {
          if (c2 == "/-") { depth++; i += 2; continue }
          if (c2 == "-/") { depth--; i += 2; if (depth == 0) out = out " "; continue }
          i++; continue
        }
        if (instr) {
          if (c == "\\") { i += 2; continue }
          if (c == "\"") { instr = 0; out = out c }
          i++; continue
        }
        if (c2 == "--") break
        if (c2 == "/-") { depth = 1; i += 2; continue }
        if (substr(line, i, 3) == "'\''\"'\''") { out = out "'\'' '\''"; i += 3; continue }
        if (c == "\"") { instr = 1; out = out c; i++; continue }
        out = out c; i++
      }
      print out
    }' "$1"
}

stage_tokens() {
  local bad="(^|[^[:alnum:]_.'])(sorry|admit|native_decide)(\$|[^[:alnum:]_!?'])"
  bad+="|(^|[^[:alnum:]_.'])decide[[:space:]]+\+native"
  bad+="|^[[:space:]]*(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable|unsafe|partial)[[:space:]]+)*axiom([[:space:]]|\$)"
  local files=() f hits found=0
  mapfile -d '' files < <(find "$proofs" -name .lake -prune -o -type f -name '*.lean' \
    ! -name '*_Template.lean' -print0 | sort -z)
  [ ${#files[@]} -gt 0 ] || { echo "no Lean files found under $proofs"; return 1; }
  for f in "${files[@]}"; do
    hits=$(strip_lean "$f" | grep -nE "$bad" | cut -d: -f1) || continue
    for n in $hits; do
      printf '%s:%s: %s\n' "${f#"$root"/}" "$n" "$(sed -n "${n}p" "$f")"
      found=1
    done
  done
  echo "scanned ${#files[@]} files"
  [ $found -eq 0 ] || { echo "forbidden tokens found"; return 1; }
}

# ---------------------------------------------------------------- lean builds

stage_spec() {
  (cd "$proofs/spec" && lake build)
}

stage_lean() {
  local mathlib=$proofs/lean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean
  if [ ! -f "$mathlib" ]; then
    echo "Mathlib oleans missing: lake exe cache get"
    (cd "$proofs/lean" && lake exe cache get) || return 1
  fi
  (cd "$proofs/lean" && lake build)
}

# Scan build logs for `#print axioms` results. Lists may wrap over several lines.
scan_axioms() {
  awk -v allowed="${allowed_axioms[*]}" '
    BEGIN { n = split(allowed, a, " "); for (i = 1; i <= n; i++) ok[a[i]] = 1; seen = 0; bad = 0 }
    function check(entry,   list, items, k, m, x) {
      list = entry
      sub(/.*depends on axioms: *\[/, "", list); sub(/\].*/, "", list)
      m = split(list, items, ",")
      for (k = 1; k <= m; k++) {
        x = items[k]; gsub(/[[:space:]]/, "", x)
        if (x != "" && !(x in ok)) { print "forbidden axiom " x ": " entry; bad = 1 }
      }
    }
    pending != "" {
      pending = pending " " $0
      if (index($0, "]")) { check(pending); pending = "" }
      next
    }
    /does not depend on any axioms/ { seen++; next }
    /depends on axioms: *\[/ {
      seen++
      if (index($0, "]")) check($0); else pending = $0
    }
    END {
      if (pending != "") { print "unterminated axiom list: " pending; bad = 1 }
      printf "%d #print axioms results scanned\n", seen
      if (seen == 0) { print "no #print axioms output found"; exit 1 }
      exit bad
    }' "$@"
}

stage_axioms() {
  local logs=() s
  if [ -n "${AXIOMS_LOGS:-}" ]; then
    read -r -a logs <<< "$AXIOMS_LOGS"
  else
    for s in spec lean; do
      if [ ! -f "$logdir/$s.log" ]; then
        echo "building $s for its axiom report"
        "stage_$s" >"$logdir/$s.log" 2>&1 || { echo "$s build failed, see $logdir/$s.log"; return 1; }
      fi
      logs+=("$logdir/$s.log")
    done
  fi
  echo "logs: ${logs[*]}"
  scan_axioms "${logs[@]}"
}

# ---------------------------------------------------------------- other stages

stage_quint() {
  "$proofs/quint/check.sh"
}

stage_rust() {
  (cd "$root" && CARGO_TARGET_DIR=${CHECK_CARGO_TARGET_DIR:-${TMPDIR:-/tmp}/sudo-rs-check-target} \
    cargo test --lib sudoers::)
}

stage_extract() {
  "$proofs/extract.sh" || return 1
  local untracked
  untracked=$(git -C "$root" ls-files --others --exclude-standard -- proofs/lean/SudoRs)
  git -C "$root" --no-pager diff --stat --exit-code -- proofs/lean/SudoRs || {
    echo "extraction drift in proofs/lean/SudoRs"; return 1; }
  [ -z "$untracked" ] || { echo "untracked generated files:"; echo "$untracked"; return 1; }
  echo "no drift"
}

stage_differential() {
  local run=$proofs/differential/run.sh args=()
  [ -x "$run" ] || { echo "SKIP: $run not present"; return 3; }
  read -r -a args <<< "${DIFFERENTIAL_ARGS:-}"
  "$run" "${args[@]}"
}

stage_compliance() {
  local run=$proofs/compliance/run.sh base
  [ -x "$run" ] || { echo "SKIP: $run not present"; return 3; }
  base=${COMPLIANCE_BASE:-$(git -C "$root" merge-base HEAD upstream/main 2>/dev/null)}
  [ -n "$base" ] || { echo "set COMPLIANCE_BASE (no upstream/main remote branch)"; return 1; }
  local tree=$logdir/compliance-base
  rm -rf "$tree" && mkdir -p "$tree"
  git -C "$root" archive "$base" | tar -x -C "$tree" || return 1
  echo "comparing $base with the working tree"
  OUT=$logdir/compliance "$run" "$tree" "$root"
}

# ---------------------------------------------------------------- driver

declare -A result elapsed
failed=0
for s in "${stages[@]}"; do
  echo "==> $s"
  start=$SECONDS
  "stage_$s" >"$logdir/$s.log" 2>&1
  rc=$?
  elapsed[$s]=$((SECONDS - start))
  case $rc in
    0) result[$s]=PASS ;;
    3) result[$s]=SKIP; sed -n 's/^SKIP: /    /p' "$logdir/$s.log" ;;
    *) result[$s]=FAIL; failed=1
       echo "    $s failed (exit $rc); last lines of $logdir/$s.log:"
       tail -n 30 "$logdir/$s.log" | sed 's/^/    | /' ;;
  esac
done

echo
printf '%-13s %-6s %s\n' STAGE RESULT TIME
for s in "${stages[@]}"; do
  printf '%-13s %-6s %ss\n' "$s" "${result[$s]}" "${elapsed[$s]}"
done
echo "logs: $logdir"
if [ $failed -ne 0 ]; then
  echo "FAIL"
  exit 1
fi
echo "PASS"
