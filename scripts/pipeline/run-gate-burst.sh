#!/usr/bin/env bash
# run-gate-burst.sh LANE_DIR FROM TAG : MERGE-KEEPER post-merge gate on a burst box, in a fresh
# mk-lane clone (LANE_DIR/src at the candidate). Umbrella in the gate slot under swarm-build, then
# merge-gate-checks.sh (same directory as this script: no /srv/lanes/mk-tools path is assumed).
# Writes LANE_DIR/logs/gate-TAG.{summary,out,done}; gate-TAG.done is written LAST, after the checks.
set -uo pipefail
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
G=$1 FROM=$2 TAG=$3
export THREADS=${THREADS:-8} SWARM_MEM_MAX=${SWARM_MEM_MAX:-64G}
export LAKE_WRAP=${LAKE_WRAP:-"$here/slot-mk.sh swarm-build"}
export SWARM_BUILD_TAG=${SWARM_BUILD_TAG:-gate-$TAG}
cd "$G/src" || exit 2; export PATH=$HOME/.elan/bin:$PATH
# A gate that dies mid-way (ssh drop, OOM of the shell, kill) leaves gate-TAG.aborted, never a silent
# "still running" (COORD-AUDIT C5): .done is written only by the last line below.
trap '[ -f "$G/logs/gate-$TAG.done" ] || echo "ABORTED $(date -Is) rc=$? at ${BASH_COMMAND:0:80}" > "$G/logs/gate-$TAG.aborted"' EXIT
rm -f "$G/logs/gate-$TAG.aborted"
TO=$(git rev-parse HEAD)
{ echo "START $(date -Is) HEAD=$TO"; LEAN_NUM_THREADS=$THREADS $LAKE_WRAP lake build Minidregg +Host.Main:leanArts ObjectiveProofs; echo "UMBRELLA rc=$? $(date -Is)"; } > "$G/logs/gate-$TAG-umbrella.log" 2>&1
grep -q "^UMBRELLA rc=0" "$G/logs/gate-$TAG-umbrella.log" && u=PASS || u=RED
# a `sorry` builds green (a warning): it is RED here, named by count (W20-GATE-MUTATION finding)
ns=$(grep -c "declaration uses 'sorry'" "$G/logs/gate-$TAG-umbrella.log" || true)
[ "$ns" = 0 ] || u="RED(sorry x$ns)"
um="umbrella $u built=$(grep -c "] Built " "$G/logs/gate-$TAG-umbrella.log") :: $(grep -E "Build completed|error:|UMBRELLA rc=75" "$G/logs/gate-$TAG-umbrella.log" | head -3 | tr "\n" " ")"
bash "$here/merge-gate-checks.sh" "$G/src" "$FROM" "$TO" "$TAG" > "$G/logs/gate-$TAG.out" 2>&1
echo "rc=$?" >> "$G/logs/gate-$TAG.out"
echo "$um" >> "$G/logs/gate-$TAG.summary"
echo DONE > "$G/logs/gate-$TAG.done"
