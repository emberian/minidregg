#!/usr/bin/env bash
# Journey hook j12a: runs the lane's stand-alone journey, affordances-journey.sh, on ITS OWN
# fresh private Store under JOURNEY_STEP_DIR with this journey's pinned
# binaries (the hook contract permits a hook its own Store; jpay2 does the
# same). It does not act on the journey's Store, and its detail line says so:
# the verdict is the lane script's own.
set -u
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
D=$JOURNEY_STEP_DIR/j12a
"$HERE/affordances-journey.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$D" "${J12A_PORT:-22434}" >"$JOURNEY_STEP_DIR/j12a.out" 2>"$JOURNEY_STEP_DIR/j12a.err"
rc=$?
echo "$D"
if [ "$rc" = 0 ]; then
  echo "affordances-journey.sh PASS on its own fresh Store ($D)" >&2
else
  echo "affordances-journey.sh exit $rc on its own fresh Store: $(tail -1 "$JOURNEY_STEP_DIR/j12a.err" 2>/dev/null)" >&2
fi
exit "$rc"
