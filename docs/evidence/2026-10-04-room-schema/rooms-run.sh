#!/bin/bash
# rooms-run.sh TAG BINDIR SRCTREE FIELDS ROSTER_BASE [CLOSURE]
# The W1.11 step-1 scenario on BINDIR's binaries: fresh scratch world, room-shaped declared cell
# `lab` born with FIELDS (timed create), a three-row roster write at ROSTER_BASE (timed propose +
# submit), ONE traced signed read. CLOSURE=1 then probes the v2 declaration's boundary.
set -uo pipefail
L=/home/ember/workbox/claude-lanes/schema-v2
TAG=$1 B=$2 SRCTREE=$3 FIELDS=$4 BASE=$5 CLOSURE=${6:-0}
HOST=$B/minidregg-host MINI=$B/mini STORE=$B/minidregg-link-sqlite-store VERIFIER=$B/minidregg-credential-signature-verifier
OUT=$L/evidence/rooms-$TAG W=$L/w/rooms-$TAG
mkdir -p $OUT $L/w
sha256sum $HOST $MINI $STORE $VERIFIER > $OUT/binaries.sha256
MEASURE_SRC=$SRCTREE $L/measure-room.sh $HOST $MINI $STORE $VERIFIER $W "$FIELDS" $BASE $OUT 0
if [ "$CLOSURE" = 1 ]; then
  WS=$W/sponsor
  echo "=== closure probes (field: wanted, got)" > $OUT/closure.txt
  for case in "1999:refused" "1013:refused" "1000:refused" "2999:admitted" "1000000:admitted"; do
    f=${case%%:*}; want=${case##*:}
    printf "%s\n" "{\"type\":\"minidregg-workspace-proposal-v1\",\"action\":\"invoke\",\"targets\":[{\"name\":\"lab\",\"payload\":{\"type\":\"scalar\",\"actions\":[{\"type\":\"create\",\"key\":{\"type\":\"object\",\"field\":\"$f\"},\"value\":\"9\"}]}}]}" > $OUT/c$f.json
    $MINI workspace --action propose --dir $WS --request $OUT/c$f.json --proposal-id c$f > $OUT/c$f.propose.out 2> $OUT/c$f.propose.err
    prc=$?
    $MINI workspace --action submit --dir $WS --intent $WS/proposals/c$f/intent.json --attempt $WS/attempts/c$f > $OUT/c$f.submit.out 2> $OUT/c$f.submit.err
    rc=$?
    if [ $prc = 0 ] && [ $rc = 0 ]; then got=admitted; else got="refused(propose rc=$prc submit rc=$rc): $(cat $OUT/c$f.propose.err $OUT/c$f.submit.err | tr '\n' ' ' | head -c 300)"; fi
    echo "field $f: want $want, got $got" >> $OUT/closure.txt
  done
fi
kill -TERM $(cat $W/public/server.pid) 2>/dev/null
cat $OUT/timings.txt $OUT/closure.txt 2>/dev/null
