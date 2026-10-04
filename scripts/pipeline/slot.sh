#!/usr/bin/env bash
# slot.sh CMD... : run CMD holding one of the two build slots of this f4 box (BURST brief amendment
# 16:45Z). Unlike `flock -n s1 cmd || flock s2 cmd`, a FAILING cmd is not re-run in slot 2:
# only flock's own conflict code (75) falls through.
flock -n -E 75 /srv/build-slot-1 "$@"; rc=$?
[ $rc = 75 ] || exit $rc
exec flock -E 75 /srv/build-slot-2 "$@"
