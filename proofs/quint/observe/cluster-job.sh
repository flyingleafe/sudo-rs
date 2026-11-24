#!/usr/bin/env bash
# LifecycleTrace end to end on one uni-cpu node: guest input, capture in the disposable
# guest, record, harness self-test, replay, negative controls.
#   omnirun submit --backend uni-cpu --name lifecycle-trace --cpus 4 --mem 8 --time 1h \
#     --env GUEST_RUN=<path of the guest launcher `guest-run`> \
#     -- bash proofs/quint/observe/cluster-job.sh
# Runs unprivileged in a clean checkout of the commit under test. Needs git, curl,
# python3 >= 3.9, npm (for quint 0.33.0, cached under $OMNIRUN_ROOT/cache/quint-0.33.0),
# /dev/kvm and the guest launcher `guest-run <input_dir> <output_dir> <timeout_s> -- <cmd>`
# (disposable Debian 13 guest, no network, input read-only at /fixture, /out copied back).
# Results in $OMNIRUN_OUTPUT: lifecycle-<commit>.obs.json, guest/ (capture without the
# binary, launcher metadata), summary.
# observe.py runs `quint test --backend=typescript`: the npm Rust evaluator v0.7.0 needs
# glibc 2.39 and does not start on EL9 (glibc 2.34). The rest of check.sh (simulation,
# mutants) uses the Rust evaluator and runs in the nix dev shell instead.
set -euo pipefail
: "${OMNIRUN_OUTPUT:?}" "${GUEST_RUN:?}" "${OMNIRUN_ROOT:?}"
cd "$(git rev-parse --show-toplevel)"
[ -z "$(git status --porcelain)" ] || { echo "checkout is not clean" >&2; exit 2; }
commit=$(git rev-parse HEAD)
mkdir -p "$OMNIRUN_OUTPUT"
summary="$OMNIRUN_OUTPUT/summary"
log() { printf '%s\n' "$*" | tee -a "$summary"; }
work=$(mktemp -d "${TMPDIR:-/tmp}/lifecycle-trace.XXXXXXXX")
trap 'rm -rf "$work"' EXIT

log "commit $commit"
proofs/quint/observe/prepare-input.sh "$commit" "$work/in" | tee -a "$summary"

rc=0
"$GUEST_RUN" "$work/in" "$work/guest" 900 -- sh /fixture/guest-run.sh /fixture /out || rc=$?
rsync -a --exclude /out/bin/ "$work/guest/" "$OMNIRUN_OUTPUT/guest/"
guest_rc=$(cat "$work/guest/meta/rc" 2>/dev/null || echo missing)
log "guest launcher exit $rc, guest command exit $guest_rc"
if [ "$rc" != 0 ] || [ "$guest_rc" != 0 ]; then
  [ -f "$work/guest/out/REFUSED" ] && log "guest refused: $(cat "$work/guest/out/REFUSED")"
  exit 1
fi

obs="$OMNIRUN_OUTPUT/lifecycle-$commit.obs.json"
python3 proofs/quint/observe/observe.py record "$work/guest/out" "$obs" | tee -a "$summary"

q="$OMNIRUN_ROOT/cache/quint-0.33.0"
[ -x "$q/node_modules/.bin/quint" ] || npm install --no-audit --no-fund --prefix "$q" @informalsystems/quint@0.33.0
export QUINT="$q/node_modules/.bin/quint"
status=0
for step in selftest "replay $obs" "controls $obs"; do
  # shellcheck disable=SC2086
  python3 proofs/quint/observe/observe.py $step 2>&1 | tee -a "$summary" || status=1
done
log "exit $status"
exit "$status"
