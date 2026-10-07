#!/usr/bin/env bash
# slot.sh CMD... : run CMD holding one of this box's lane build slots ($PIPELINE_SLOTS, from
# $PIPELINE_ROOT/box.env; see lib.sh pipeline_slot). A FAILING cmd is never re-run in another slot.
. "$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)/lib.sh"
pipeline_slot "$@"
