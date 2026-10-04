#!/bin/bash
# growth-run.sh TAG BINDIR SRCTREE FIELDS
# Fresh scratch world w/grow-TAG on BINDIR's binaries (minidregg-host, mini, store, verifier),
# a declared cell `lab` with FIELDS, grown to 300 and then 3000 accepted records. At each level:
# stop the server; Host store-bench (the Host's own open and lookup timings); restart the server
# and time it to "serving" (the end-to-end Host open); 20 timed writes; a receipt lookup of the
# middle and of the last write (`mini retry --mode lookup`). Everything under evidence/grow-TAG.
# Adapted for persvati from the W1.11 lane's hbox growth-run.sh (recovered from its transcript).
set -uo pipefail
L=/home/ember/workbox/claude-lanes/schema-v2
TAG=$1 B=$2 SRCTREE=$3 FIELDS=$4
HOST=$B/minidregg-host MINI=$B/mini STORE=$B/minidregg-link-sqlite-store VERIFIER=$B/minidregg-credential-signature-verifier
WORLD=$L/w/grow-$TAG OUT=$L/evidence/grow-$TAG SOCK=$L/w/g-$TAG.sock
mkdir -p $OUT $L/w
sha256sum $HOST $MINI $STORE $VERIFIER > $OUT/binaries.sha256
sh $SRCTREE/native/resource-client/newparticipant-acceptance.sh $HOST $MINI $STORE $VERIFIER $WORLD $SOCK > $OUT/bootstrap.out 2> $OUT/bootstrap.err || { echo bootstrap-failed > $OUT/state; exit 1; }
CONFIG=$(jq -r .config $WORLD/handoff.json)
WS=$WORLD/sponsor
printf "%s\n" "{\"type\":\"all\",\"predicates\":[]}" > $OUT/permit-all.json
/usr/bin/time -f "create %e s" -o $OUT/create.time $MINI workspace --action create --dir $WS --name lab --storage declared --predicate $OUT/permit-all.json --fields "$FIELDS" > $OUT/create.out 2> $OUT/create.err || { echo create-failed > $OUT/state; exit 1; }
start_server() {
  t0=$(date +%s.%N)
  setsid nohup $MINI serve --host $HOST --config $CONFIG --socket $SOCK > $WORLD/public/serve-$1.log 2>&1 < /dev/null & echo $! > $WORLD/public/server.pid
  for i in $(seq 1 3000); do grep -q serving $WORLD/public/serve-$1.log 2>/dev/null && break; sleep 0.05; done
  t1=$(date +%s.%N)
  echo "server start to serving ($1): $(echo "$t1 - $t0" | bc) s" >> $OUT/open.txt
}
stop_server() { P=$(cat $WORLD/public/server.pid); kill -TERM $P 2>/dev/null; for i in $(seq 1 300); do kill -0 $P 2>/dev/null || break; sleep 0.1; done; }
level() {
  N=$1
  echo "growing-to-$N" > $OUT/state
  $L/grow.sh $MINI $WS $N $OUT/g || { echo grow-failed-$N > $OUT/state; exit 1; }
  stop_server
  ( cd $L && STORE_BENCH_ROOT_STRIDE=${STRIDE[$N]:-0} /usr/bin/time -f "store-bench %e s %M KB" $HOST $CONFIG store-bench ) > $OUT/bench-$N.txt 2>&1
  start_server L$N
  first=$(($(cat $OUT/g/n) + 1))
  $L/grow.sh $MINI $WS $((N + 20)) $OUT/g
  awk -v f=$first '$1 >= f' $OUT/g/writes.tsv > $OUT/writes-at-$N.tsv
  mid=$(( $(cat $OUT/g/n) / 2 )); last=$(cat $OUT/g/n)
  for which in mid last; do id=g${!which}
    /usr/bin/time -f "lookup $which ($id) %e s" -a -o $OUT/lookup-$N.txt $MINI retry --attempt $WS/attempts/$id --mode lookup > $OUT/lookup-$N-$which.out 2> $OUT/lookup-$N-$which.err
    echo "$which: lookup $(jq -c '{transactionId,acceptedCount,worldRoot}' $OUT/lookup-$N-$which.out 2>/dev/null | head -c 300) original $(jq -c '{acceptedCount,worldRoot}' $WS/attempts/$id/outcome.json 2>/dev/null)" >> $OUT/lookup-$N.txt
  done
}
declare -A STRIDE=([300]=${STRIDE300:-0} [3000]=${STRIDE3000:-0})
level 300
level 3000
stop_server
echo done > $OUT/state
