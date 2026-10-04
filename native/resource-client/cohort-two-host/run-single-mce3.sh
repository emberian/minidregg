#!/usr/bin/env bash
# The v12 schedule on one host through roster enrollment (new binary and script): the control
# that the replaced adapter keeps every v12 assertion.
set -euo pipefail
. "$(dirname "$0")/env.sh"
sha256sum "$MINI_NEW" "$HOST" "$0" "$RC/cohort-native-tcp.py" | tee $L/logs/single-mce3.inputs.sha256
python3 $RC/cohort-native-tcp.py --mini $MINI_NEW --fixture $LOOKUP --native-socket $SOCKET \
  --evidence $L/evidence/single-host-mce3 --epochs 64 --processing-slots 2 --native-workload every-eight \
  2>&1 | tee $L/logs/single-mce3.log
