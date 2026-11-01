#!/usr/bin/env bash
# The standing world's operator certifier. Admission remains mini checkpoint's;
# this loop supplies the same periodic trigger as the demo's certifier timer.
set -euo pipefail
[[ $# == 1 ]] || { echo "usage: $0 WORLD_ROOT" >&2; exit 2; }
run=$1
. "$run/WORLD.env"
export MINI_CONSENT_ANCHOR_DIR=$RUN/a
control=$(jq -er .factoryControllerCapability "$RUN/store/base/workroom/genesis.json")
# Leave half the bounded tail for writes racing the next certification.
minimum=$(jq -er '(.tailBound | tonumber | . / 2 | floor) | if . < 1 then 1 else . end' "$RUN/store/base/workroom/genesis.json")
while :; do
  "$BIN/mini" checkpoint --action certify --workspace "$run/certifier" --control "$control" --min-tail "$minimum" || true
  sleep 2
done
