#!/usr/bin/env bash
# Check the sudo lifecycle model.
#   nix shell nixpkgs#quint nixpkgs#jdk -c ./check.sh
# 1. typecheck every module;
# 2. clean models (ogsudo, sudors): all invariants under random simulation,
#    plus coverage witnesses; opt-in bounded `quint verify` (Apalache), see
#    VERIFY_STEPS;
# 3. every mutant: the expected invariant must be violated; the counterexample
#    is saved as ITF under traces/.
# Exit status is non-zero on any unexpected outcome.
# Budgets can be overridden through the environment variables below.
set -uo pipefail
cd "$(dirname "$0")"

SAMPLES=${SAMPLES:-100000}               # random runs per clean model
STEPS=${STEPS:-60}                       # steps per random run
MUTANT_SAMPLES=${MUTANT_SAMPLES:-100000} # upper bound of runs per mutant
VERIFY_STEPS=${VERIFY_STEPS:-0}          # Apalache bound; 0 = skip (slow, see README)
SEED=${SEED:-0x5ad0}

INVARIANTS=(inv1_completeMediation inv2_authentication inv3_exactCredentials
            inv4_helperIsolation inv5_trustedInputs inv6_sudoeditFiles)
WITNESSES=(witnessExec witnessExecAsOther witnessTicketReuse witnessSudoeditWrite
           witnessMailer witnessAskpass witnessEditor witnessCredFailure witnessConcurrent)
# module | bug | invariant expected to break
MUTANTS=(
  "mut_cve_2026_35535|CVE-2026-35535|inv4_helperIsolation"
  "mut_cve_2025_32463|CVE-2025-32463|inv5_trustedInputs"
  "mut_cve_2025_32462|CVE-2025-32462|inv1_completeMediation"
  "mut_cve_2019_14287|CVE-2019-14287|inv3_exactCredentials"
  "mut_cve_2026_96512|CVE-2026-96512|inv5_trustedInputs"
  "mut_cve_2023_22809|CVE-2023-22809|inv6_sudoeditFiles"
  "mut_cve_2025_64517|CVE-2025-64517|inv2_authentication"
  "mut_cve_2023_42456|CVE-2023-42456|inv2_authentication"
  "mut_proc_stat_split|PROC-STAT-SPLIT|inv5_trustedInputs"
)

failures=0
fail() { echo "FAIL $*"; failures=$((failures + 1)); }

command -v quint >/dev/null || { echo "quint not on PATH"; exit 2; }

echo "== typecheck"
for f in types.qnt kernel.qnt policy.qnt sudo.qnt instances.qnt; do
  if out=$(quint typecheck "$f" 2>&1); then echo "PASS typecheck $f"
  else echo "$out"; fail "typecheck $f"; fi
done

echo "== clean models: random simulation ($SAMPLES runs x $STEPS steps, seed $SEED)"
for impl in ogsudo sudors; do
  out=$(quint run --main="$impl" instances.qnt --max-samples="$SAMPLES" --max-steps="$STEPS" \
        --seed="$SEED" --invariants "${INVARIANTS[@]}" --witnesses "${WITNESSES[@]}" \
        --verbosity=1 2>&1)
  if grep -q '^\[ok\]' <<<"$out"; then
    for inv in "${INVARIANTS[@]}"; do echo "PASS $impl $inv (simulation)"; done
  else
    echo "$out" | tail -40
    fail "$impl invariants (simulation)"
  fi
  for w in "${WITNESSES[@]}"; do
    n=$(sed -n "s/^$w was witnessed in \([0-9]*\) trace.*/\1/p" <<<"$out")
    if [[ "$impl" == sudors && "$w" == witnessMailer ]]; then
      [[ "$n" == 0 ]] || fail "$impl $w: sudo-rs has no mailer but $n runs used it"
    elif [[ -n "$n" && "$n" -gt 0 ]]; then
      echo "     $impl $w reached in $n/$SAMPLES runs"
    else
      fail "$impl $w never reached (vacuous check)"
    fi
  done
done

if [[ "$VERIFY_STEPS" -eq 0 ]]; then
  echo "== clean models: bounded model checking skipped (set VERIFY_STEPS=N to enable)"
elif command -v java >/dev/null; then
  echo "== clean models: bounded model checking (Apalache, $VERIFY_STEPS steps)"
  for impl in ogsudo sudors; do
    out=$(quint verify --main="$impl" instances.qnt --invariant=allInvariants \
          --max-steps="$VERIFY_STEPS" 2>&1)
    if grep -q '^\[ok\]' <<<"$out"; then
      for inv in "${INVARIANTS[@]}"; do echo "PASS $impl $inv (apalache, $VERIFY_STEPS steps)"; done
    else
      echo "$out" | tail -40
      fail "$impl allInvariants (apalache)"
    fi
  done
else
  echo "SKIP apalache: no java on PATH (run inside nix shell nixpkgs#jdk)"
fi

# One simulator thread plus a fixed seed make the search deterministic; the
# creation time Quint stamps into the ITF header is blanked so that reruns
# reproduce the committed traces byte for byte.
echo "== mutants (up to $MUTANT_SAMPLES runs x $STEPS steps each, 1 thread, seed $SEED)"
mkdir -p traces
for m in "${MUTANTS[@]}"; do
  IFS='|' read -r mod bug inv <<<"$m"
  trace="traces/$mod.itf.json"
  raw=$(mktemp)
  out=$(quint run --main="$mod" instances.qnt --max-samples="$MUTANT_SAMPLES" --max-steps="$STEPS" \
        --seed="$SEED" --n-threads=1 --invariant="$inv" --out-itf="$raw" --verbosity=1 2>&1)
  if grep -q '^\[violation\]' <<<"$out" && [[ -s "$raw" ]]; then
    sed -E 's/"description":"Created by Quint on [^"]*","timestamp":[0-9]+/"description":"Created by Quint","timestamp":0/' \
      "$raw" > "$trace"
    echo "VIOLATED $inv by $mod ($bug), trace $trace"
  else
    echo "$out" | tail -20
    fail "$mod ($bug): expected $inv to be violated"
  fi
  rm -f "$raw"
done

# Scratch directories quint/Apalache leave behind.
rm -rf _apalache-out
rmdir tmp 2>/dev/null

if [[ $failures -eq 0 ]]; then echo "ALL CHECKS PASSED"; else echo "$failures UNEXPECTED OUTCOME(S)"; fi
[[ $failures -eq 0 ]]
