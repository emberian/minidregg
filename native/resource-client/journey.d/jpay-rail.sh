#!/usr/bin/env bash
# Direct JPAY1-4 fixture rail using a pinned base artifact manifest and a rebuilt mini.
# Usage: jpay-rail.sh MANIFEST MINI NEW_RESULTS_ROOT
# The standing train's product_pay_step remains the owner of the regular row.
set -euo pipefail
[ "$#" -eq 3 ] || { echo 'usage: jpay-rail.sh MANIFEST MINI NEW_RESULTS_ROOT' >&2; exit 2; }
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
MANIFEST=$(realpath "$1")
export MINI HOST STORE VERIFIER PAY_WATCHER_BIN JOURNEY_STEP_DIR
MINI=$(realpath "$2")
RESULTS=$(realpath -m "$3")
[ ! -e "$RESULTS" ] || { echo "jpay-rail: refusing to reuse $RESULTS" >&2; exit 2; }
HOST=$(jq -er '.host' "$MANIFEST")
STORE=$(jq -er '.store' "$MANIFEST")
VERIFIER=$(jq -er '.verifier' "$MANIFEST")
PAY_WATCHER_BIN=$(dirname "$HOST")/pay-watcher
for name in host store verifier; do
  binary=$(jq -er --arg name "$name" '.[$name]' "$MANIFEST")
  expected=$(jq -r --arg name "$name" '.sha256[$name] // ""' "$MANIFEST")
  if [ -n "$expected" ]; then
    actual=$(sha256sum "$binary" | cut -d' ' -f1)
    [ "$actual" = "$expected" ] || { echo "jpay-rail: $name hash differs" >&2; exit 2; }
  fi
done
for binary in "$MINI" "$HOST" "$STORE" "$VERIFIER" "$PAY_WATCHER_BIN"; do test -x "$binary"; done
mkdir -m 700 -p "$RESULTS"
cp "$MANIFEST" "$RESULTS/base-manifest.json"
sha256sum "$MINI" "$HOST" "$STORE" "$VERIFIER" "$PAY_WATCHER_BIN" \
  "$HERE"/jpay{1,2,3,4}.sh "$HERE/../../../deploy/pay/mini-pay-watcher" >"$RESULTS/inputs.sha256"
overall=0
: >"$RESULTS/subrows.tsv"
for id in 1 2 3 4; do
  JOURNEY_STEP_DIR=$RESULTS/JPAY$id
  mkdir -m 700 "$JOURNEY_STEP_DIR"
  rc=0
  bash "$HERE/jpay$id.sh" >"$RESULTS/JPAY$id.out" 2>"$RESULTS/JPAY$id.err" || rc=$?
  status=FAIL
  if [ "$rc" -eq 0 ] && grep -Eq "^J-PAY-$id PASS [1-9][0-9]*/[1-9][0-9]*" "$RESULTS/JPAY$id.err"; then
    status=PASS
  else
    overall=1
    cat "$RESULTS/JPAY$id.err" >&2
  fi
  detail=$(tail -1 "$RESULTS/JPAY$id.err")
  printf 'JPAY%s\t%s\t%s\n' "$id" "$status" "$detail" | tee -a "$RESULTS/subrows.tsv"
done
exit "$overall"
