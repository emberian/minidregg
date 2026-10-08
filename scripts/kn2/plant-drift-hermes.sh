#!/usr/bin/env bash
# Restore old Hermes commitment/manager expectations in separate temp copies.
# Usage: plant-drift-hermes.sh NEW_RESULTS_ROOT
set -euo pipefail
[[ $# == 1 ]] || { echo "usage: $0 NEW_RESULTS_ROOT" >&2; exit 64; }
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
. "$HERE/plant-drift-lib.sh"
drift_setup hermes "$1"

drift_copy host-next native/grain-runtime/hermes-journey.sh
drift_replace '--no-prerotation --dir "$RUN/host-workspace" >/dev/null' \
  '--dir "$RUN/host-workspace" >/dev/null'
grep -Fx '  --dir "$RUN/host-workspace" >/dev/null' "$COPY/$DRIVER"
drift_red
grep -F "mini: refused: subject 8's record commits to no next key, but you hold one:" "$EVIDENCE/hermes.err"
echo "RED host-next: mini: refused: subject 8's record commits to no next key, but you hold one"

drift_copy worker-next native/grain-runtime/hermes-journey.sh
drift_replace '--no-prerotation --dir "$H/state/resource-workspace" >/dev/null' \
  '--dir "$H/state/resource-workspace" >/dev/null'
grep -Fx '  --dir "$H/state/resource-workspace" >/dev/null' "$COPY/$DRIVER"
drift_red
grep -F "mini: refused: subject 9's record commits to no next key, but you hold one:" "$EVIDENCE/hermes.err"
echo "RED worker-next: mini: refused: subject 9's record commits to no next key, but you hold one"

drift_copy managers native/grain-runtime/hermes-journey.sh
drift_replace $'  --setenv=MINI_GRAIN_CONTROLLER_MANAGER=user --setenv=MINI_GRAIN_WORKER_MANAGER=user \\\n  --setenv="MINI_GRAIN_CONTROLLER_UNIT=$UNIT.service" \\\n' ''
grep -Fx 'systemd-run --user --unit="$UNIT" --description="mini-hermes-journey:$RUN" \' "$COPY/$DRIVER"
if grep -q -- '--setenv=MINI_GRAIN_' "$COPY/$DRIVER"; then echo 'manager plant did not apply' >&2; exit 1; fi
drift_red
grep -Fx 'grain-runtime: managed proof requires root registration or explicit user fixture selection' \
  "$EVIDENCE/evidence/phase-a.connector.log"
grep -F 'FAIL phase-a: worker did not start' "$EVIDENCE/evidence/timeline.tsv"
echo 'RED managers: grain-runtime: managed proof requires root registration or explicit user fixture selection'
