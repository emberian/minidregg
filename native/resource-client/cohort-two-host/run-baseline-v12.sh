#!/usr/bin/env bash
# CONTROL: v12 exactly as shipped (c8fdd000 script, c8fdd000 mini), single host, against the
# scratch world read-only lookup fixture. Run before the MCE3 runs.
set -euo pipefail
. "$(dirname "$0")/env.sh"
SCRIPT=$L/baseline/native/resource-client/cohort-native-tcp.py
sha256sum "$MINI_BASELINE" "$HOST" "$0" "$SCRIPT" | tee $L/logs/baseline-v12.inputs.sha256
python3 $SCRIPT --mini $MINI_BASELINE --fixture $LOOKUP --native-socket $SOCKET \
  --evidence $L/evidence/baseline-v12-scratch --epochs 64 --processing-slots 2 --native-workload every-eight \
  2>&1 | tee $L/logs/baseline-v12.log
