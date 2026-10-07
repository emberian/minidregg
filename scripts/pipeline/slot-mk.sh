#!/usr/bin/env bash
# slot-mk.sh CMD... : the merge keeper's reserved gate slot ($PIPELINE_GATE_SLOT, default
# /srv/build-slot-mk; never taken by lanes). Where the box has no gate slot, a lane slot via slot.sh.
# The wait is BOUNDED (PIPELINE_GATE_SLOT_WAIT_S, default 3 h): a gate stuck behind its own previous
# run fails loudly with flock's conflict code 75 instead of parking forever.
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
PIPELINE_ROOT=${PIPELINE_ROOT:-/srv/pipeline}
[ -f "$PIPELINE_ROOT/box.env" ] && . "$PIPELINE_ROOT/box.env"
slot=${PIPELINE_GATE_SLOT:-/srv/build-slot-mk}
[ -e "$slot" ] || exec "$here/slot.sh" "$@"
exec flock -w "${PIPELINE_GATE_SLOT_WAIT_S:-10800}" -E 75 "$slot" "$@"
