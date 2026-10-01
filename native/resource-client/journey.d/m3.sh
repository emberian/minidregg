#!/usr/bin/env bash
# Journey hook m3: runs the lane's stand-alone journey, provisioning-acceptance.sh, on ITS OWN
# fresh private Store (in its short directory; journey.d/lib/shortdir.sh) with this journey's pinned
# binaries (the hook contract permits a hook its own Store; jpay2 does the
# same). It does not act on the journey's Store, and its detail line says so:
# the verdict is the lane script's own.
set -u
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
. "$HERE/journey.d/lib/shortdir.sh"
journey_shortdir m3   # its sockets live in a short directory, kept as $JOURNEY_STEP_DIR/rt
D=$JOURNEY_D
"$HERE/provisioning-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$D" >"$JOURNEY_STEP_DIR/m3.out" 2>"$JOURNEY_STEP_DIR/m3.err"
rc=$?
echo "$D"
if [ "$rc" = 0 ]; then
  echo "provisioning-acceptance.sh PASS on its own fresh Store ($D)" >&2
else
  echo "provisioning-acceptance.sh exit $rc on its own fresh Store: $(tail -1 "$JOURNEY_STEP_DIR/m3.err" 2>/dev/null)" >&2
fi
exit "$rc"
