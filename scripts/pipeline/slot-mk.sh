#!/usr/bin/env bash
# slot-mk.sh CMD... : the merge keeper's reserved build slot on burst-gate (BURST-LANE-BRIEF amendment 4:
# /srv/build-slot-mk, 32G, never taken by lanes). Falls back to slot.sh where the reserved slot is absent.
[ -e /srv/build-slot-mk ] || exec "$(dirname "$0")/slot.sh" "$@"
exec flock -E 75 /srv/build-slot-mk "$@"
