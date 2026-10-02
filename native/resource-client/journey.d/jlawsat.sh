#!/usr/bin/env bash
# Journey hook jlawsat: runs the lane's stand-alone journey, lawsat-journey.sh, on ITS OWN
# fresh private Store under JOURNEY_STEP_DIR with this journey's pinned
# binaries (the hook contract permits a hook its own Store; j12a does the
# same). It does not act on the journey's Store; the verdict is the lane script's own.
set -u
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
D=$JOURNEY_STEP_DIR/jlawsat
"$HERE/lawsat-journey.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$D" "${JLAWSAT_PORT:-22436}" >"$JOURNEY_STEP_DIR/jlawsat.out" 2>"$JOURNEY_STEP_DIR/jlawsat.err"
rc=$?
echo "$D"
if [ "$rc" = 0 ]; then
  echo "lawsat-journey.sh PASS on its own fresh Store ($D)" >&2
else
  echo "lawsat-journey.sh exit $rc on its own fresh Store: $(tail -1 "$JOURNEY_STEP_DIR/jlawsat.err" 2>/dev/null)" >&2
fi
exit "$rc"
