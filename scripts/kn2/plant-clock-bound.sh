#!/usr/bin/env bash
# CLOCK-BOUND plant: only a temporary receiver copy is changed.
# Usage: scripts/kn2/plant-clock-bound.sh [LOG_DIR]
# Run through request_journey after the clock receiver imports are built.
set -euo pipefail
ROOT=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
LOGS=${1:-$(mktemp -d /tmp/mini-clock-bound-evidence.XXXXXX)}
mkdir -p "$LOGS"
TMP=$(mktemp -d /tmp/mini-clock-bound-plant.XXXXXX)
trap 'rm -rf "$TMP"' EXIT
FAULT=$TMP/ClockTickReceiver.lean
cp "$ROOT/Kernel/ClockTickReceiver.lean" "$FAULT"
python3 - "$FAULT" <<'PY'
import pathlib, sys
p = pathlib.Path(sys.argv[1])
s = p.read_text()
old = '    if current.now + bound < next.now then .error .clockStepExceeded else .ok ⟨current, next⟩'
new = '    .ok ⟨current, next⟩ -- CLOCK-BOUND PLANT: step check removed'
assert s.count(old) == 1, 'CLOCK-BOUND mutation must match exactly once'
p.write_text(s.replace(old, new))
assert new in p.read_text() and old not in p.read_text(), 'CLOCK-BOUND mutation not installed'
PY
grep -Fq '    .ok ⟨current, next⟩ -- CLOCK-BOUND PLANT: step check removed' "$FAULT"
# Pin the failing proof line inside the named refuting theorem, not an unrelated error.
LINE=$(awk '/^theorem tick_step_exceeded_refused / { pole=1 } pole && /decideTick bound current next = .error .clockStepExceeded := by/ { print NR; exit }' "$FAULT")
[ -n "$LINE" ] || { echo 'CLOCK-BOUND plant: refuting theorem line missing' >&2; exit 1; }
cd "$ROOT"
if lake env lean "$FAULT" >"$LOGS/plant-clock-bound.log" 2>&1; then
  echo 'CLOCK-BOUND plant: removed check compiled GREEN' >&2
  exit 1
fi
PIN=":$LINE:[0-9]+: error: unsolved goals"
grep -E "$PIN" "$LOGS/plant-clock-bound.log" >"$LOGS/red-line.txt"
grep -Fq 'exceeded : current.now + bound < next.now' "$LOGS/plant-clock-bound.log"
printf 'RED at tick_step_exceeded_refused (proof line %s):\n' "$LINE"
cat "$LOGS/red-line.txt"
printf '%s\n' "$LOGS/plant-clock-bound.log"
