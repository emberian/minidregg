#!/usr/bin/env bash
# Journey hook j13: runs the lane's stand-alone journey, law-leaf-journey.sh, on ITS OWN
# fresh private Store under JOURNEY_STEP_DIR with this journey's pinned
# binaries (the hook contract permits a hook its own Store; jpay2 does the
# same). It does not act on the journey's Store, and its detail line says so:
# the verdict is the lane script's own.
set -u
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
D=$JOURNEY_STEP_DIR/j13
"$HERE/law-leaf-journey.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$D" "${J13_PORT:-22433}" >"$JOURNEY_STEP_DIR/j13.out" 2>"$JOURNEY_STEP_DIR/j13.err"
rc=$?
echo "$D"
if [ "$rc" = 0 ]; then
  echo "law-leaf-journey.sh PASS on its own fresh Store ($D)" >&2
else
  echo "law-leaf-journey.sh exit $rc on its own fresh Store: $(tail -1 "$JOURNEY_STEP_DIR/j13.err" 2>/dev/null)" >&2
fi
exit "$rc"
