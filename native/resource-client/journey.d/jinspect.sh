#!/usr/bin/env bash
# Journey hook jinspect: runs the lane's stand-alone journey, inspect-journey.sh
# (K-INSPECT-VIEWS), on ITS OWN fresh private Store with this journey's pinned
# binaries, as j12a and m5 do. It does not act on the journey's Store, and its
# detail line says so: the verdict is the lane script's own.
#
# The Store's socket lives under the run directory and a Unix socket path must
# fit in sun_path (at most 107 bytes). A journey step directory can be too deep
# for that (ki-full-1: 108 bytes, and `mini serve` could not bind), so the run
# goes to a short private directory, as m5's does; the step directory links to
# it, and the evidence (log/) is copied back so it outlives that directory.
set -u
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
SHORT=$(mktemp -d "${XDG_RUNTIME_DIR:-/tmp}/ji.XXXXXX")
D=$SHORT/r
ln -s "$D" "$JOURNEY_STEP_DIR/jinspect"
"$HERE/inspect-journey.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$D" "${JINSPECT_PORT:-22436}" >"$JOURNEY_STEP_DIR/jinspect.out" 2>"$JOURNEY_STEP_DIR/jinspect.err"
rc=$?
[ -d "$D/log" ] && cp -a "$D/log" "$JOURNEY_STEP_DIR/jinspect-log"
echo "$JOURNEY_STEP_DIR/jinspect-log"
if [ "$rc" = 0 ]; then
  echo "inspect-journey.sh PASS on its own fresh Store ($D; evidence $JOURNEY_STEP_DIR/jinspect-log): $(grep '^rows:' "$JOURNEY_STEP_DIR/jinspect.out")" >&2
else
  echo "inspect-journey.sh exit $rc on its own fresh Store ($D): $(tail -1 "$JOURNEY_STEP_DIR/jinspect.err" 2>/dev/null)" >&2
fi
exit "$rc"
