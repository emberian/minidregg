#!/usr/bin/env bash
# Journey hook jinspect: runs the lane's stand-alone journey, inspect-journey.sh
# (K-INSPECT-VIEWS), on ITS OWN fresh private Store under JOURNEY_STEP_DIR with
# this journey's pinned binaries, as j12a does. It does not act on the
# journey's Store, and its detail line says so: the verdict is the lane
# script's own.
set -u
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
D=$JOURNEY_STEP_DIR/jinspect
"$HERE/inspect-journey.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$D" "${JINSPECT_PORT:-22436}" >"$JOURNEY_STEP_DIR/jinspect.out" 2>"$JOURNEY_STEP_DIR/jinspect.err"
rc=$?
echo "$D"
if [ "$rc" = 0 ]; then
  echo "inspect-journey.sh PASS on its own fresh Store ($D): $(tail -2 "$JOURNEY_STEP_DIR/jinspect.out" | head -1)" >&2
else
  echo "inspect-journey.sh exit $rc on its own fresh Store: $(tail -1 "$JOURNEY_STEP_DIR/jinspect.err" 2>/dev/null)" >&2
fi
exit "$rc"
