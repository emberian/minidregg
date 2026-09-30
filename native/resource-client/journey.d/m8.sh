#!/usr/bin/env bash
# Journey hook m8: runs the lane's stand-alone journey, fleet-journey.sh, on ITS OWN
# fresh private Store under JOURNEY_STEP_DIR with this journey's pinned
# binaries (the hook contract permits a hook its own Store; jpay2 does the
# same). It does not act on the journey's Store, and its detail line says so:
# the verdict is the lane script's own.
set -u
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
D=$JOURNEY_STEP_DIR/m8
"$HERE/fleet-journey.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$D" >"$JOURNEY_STEP_DIR/m8.out" 2>"$JOURNEY_STEP_DIR/m8.err"
rc=$?
echo "$D"
if [ "$rc" = 0 ]; then
  echo "fleet-journey.sh PASS on its own fresh Store ($D)" >&2
else
  echo "fleet-journey.sh exit $rc on its own fresh Store: $(tail -1 "$JOURNEY_STEP_DIR/m8.err" 2>/dev/null)" >&2
fi
exit "$rc"
