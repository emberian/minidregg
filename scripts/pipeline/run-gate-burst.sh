#!/usr/bin/env bash
# run-gate-burst.sh LANE_DIR FROM TAG : MERGE-KEEPER post-merge gate on a burst box, in a fresh
# mk-lane clone (LANE_DIR/src at the candidate). Umbrella under swarm-build at 8 threads, then
# merge-gate-checks.sh. Writes LANE_DIR/logs/gate-TAG.{summary,out,done}.
set -u
G=$1 FROM=$2 TAG=$3
export THREADS=${THREADS:-8} SWARM_MEM_MAX=${SWARM_MEM_MAX:-32G}
export LAKE_WRAP="/srv/lanes/mk-tools/slot-mk.sh swarm-build"
cd $G/src; export PATH=$HOME/.elan/bin:$PATH
TO=$(git rev-parse HEAD)
{ echo "START $(date -Is) HEAD=$TO"; LEAN_NUM_THREADS=$THREADS /srv/lanes/mk-tools/slot-mk.sh swarm-build lake build Minidregg +Host.Main:leanArts ObjectiveProofs; echo "UMBRELLA rc=$? $(date -Is)"; } > $G/logs/gate-$TAG-umbrella.log 2>&1
grep -q "^UMBRELLA rc=0" $G/logs/gate-$TAG-umbrella.log && u=PASS || u=RED
# a `sorry` builds green (a warning): it is RED here, named by count (W20-GATE-MUTATION finding)
ns=$(grep -c "declaration uses 'sorry'" $G/logs/gate-$TAG-umbrella.log || true)
[ "$ns" = 0 ] || u="RED(sorry x$ns)"
um="umbrella $u built=$(grep -c "] Built " $G/logs/gate-$TAG-umbrella.log) :: $(grep -E "Build completed|error:" $G/logs/gate-$TAG-umbrella.log | head -3 | tr "\n" " ")"
bash /srv/lanes/mk-tools/merge-gate-checks.sh $G/src $FROM $TO $TAG > $G/logs/gate-$TAG.out 2>&1
echo "rc=$?" >> $G/logs/gate-$TAG.out
echo "$um" >> $G/logs/gate-$TAG.summary
echo DONE > $G/logs/gate-$TAG.done
