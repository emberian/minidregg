#!/usr/bin/env bash
# usage: scripts/lane/lb.sh <log> <targets...>
# Foreground `lake build` of <targets> in THIS checkout (the repo root that
# contains this script), niced, LEAN_NUM_THREADS (default 8); writes
# build-logs/<log>.log and appends EXIT=<rc>. Never cd's into another clone.
set -u
root=$(cd "$(dirname "$0")/../.." && pwd)
cd "$root" || exit 2
export PATH=$HOME/.elan/bin:$PATH
log=build-logs/$1.log; shift
mkdir -p build-logs
LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-8} nice -n 10 lake build "$@" > "$log" 2>&1
rc=$?
echo "EXIT=$rc" >> "$log"
tail -n 5 "$log"
exit $rc
