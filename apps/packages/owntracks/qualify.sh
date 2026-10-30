#!/usr/bin/env bash
# Run on hbox as the lane's operator. LANE contains src/ and bin/; CACHE holds
# exactly one quarantine candidate named <packageId>.spk.
set -euo pipefail
LANE=${1:?absolute lane directory}
CACHE=${2:?quarantine directory containing the candidate SPK}
ATTEMPT=${3:-1}
[[ $ATTEMPT =~ ^[a-z0-9-]+$ ]]
RECIPE=$(cd "$(dirname "$0")" && pwd)
RUN="$LANE/world-$ATTEMPT"
OUT="$LANE/qualification-$ATTEMPT"
[[ $LANE == /* && -d $LANE/src && -d $LANE/bin && ! -e $RUN && ! -e $OUT ]]
MINI_OPERATOR_UID=$(id -u)
MINI_OPERATOR_NAME=$(id -un)
export MINI_OPERATOR_UID MINI_OPERATOR_NAME
cleanup() {
  rc=$?
  trap - EXIT
  if [[ -f $RUN/WORLD.env || -f $RUN/broker-setup/recovery.json ]]; then
    down_rc=0
    bash "$LANE/src/scripts/spk-platform/world-down.sh" "$RUN" || down_rc=$?
    if [[ $rc == 0 ]]; then rc=$down_rc; fi
  fi
  exit "$rc"
}
trap cleanup EXIT
flock -o /tank/lanes/world-up.lock \
  bash "$LANE/src/scripts/spk-platform/world-up.sh" "$LANE/bin" "$LANE/bin" "$RUN"
MINI_MARKET_CACHE="$CACHE" QUALIFY_TABLE="$RECIPE/qualify.tsv" \
  QUALIFY_WRITES="$RECIPE/qualify-writes" QUALIFY_STOP=1 \
  bash "$LANE/src/scripts/spk-platform/featured-qualify.sh" "$RUN/WORLD.env" "$OUT" k
