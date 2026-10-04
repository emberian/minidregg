#!/bin/bash
# growth-levels.sh TAG BINDIR LEVEL...: continue the grow-TAG world (made by growth-run.sh) through
# the given record levels. At each level: stop the server; Host store-bench (STRIDE<level> env sets
# STORE_BENCH_ROOT_STRIDE); restart timed to "serving"; 20 timed writes; receipt lookups of the
# middle and the last write.
set -uo pipefail
L=${L:-/srv/lanes/schema-v2-2}
TAG=$1 B=$2; shift 2
HOST=$B/minidregg-host MINI=$B/mini
WORLD=$L/w/grow-$TAG OUT=$L/evidence/grow-$TAG SOCK=$L/w/g-$TAG.sock
CONFIG=$(jq -r .config $WORLD/handoff.json)
WS=$WORLD/sponsor
start_server() {
  t0=$(date +%s.%N)
  setsid nohup $MINI serve --host $HOST --config $CONFIG --socket $SOCK > $WORLD/public/serve-$1.log 2>&1 < /dev/null & echo $! > $WORLD/public/server.pid
  for i in $(seq 1 6000); do grep -q serving $WORLD/public/serve-$1.log 2>/dev/null && break; sleep 0.05; done
  t1=$(date +%s.%N)
  echo "server start to serving ($1): $(awk -v a=$t0 -v b=$t1 'BEGIN{print b-a}') s  load $(cut -d" " -f1 /proc/loadavg)" >> $OUT/open.txt
}
stop_server() { P=$(cat $WORLD/public/server.pid); kill -TERM $P 2>/dev/null; for i in $(seq 1 300); do kill -0 $P 2>/dev/null || break; sleep 0.1; done; }
for N in "$@"; do
  echo "growing-to-$N" > $OUT/state
  $L/grow.sh $MINI $WS $N $OUT/g || { echo grow-failed-$N > $OUT/state; exit 1; }
  stop_server
  sv=STRIDE$N
  ( cd $L && STORE_BENCH_ROOT_STRIDE=${!sv:-0} /usr/bin/time -f "store-bench %e s %M KB" $HOST $CONFIG store-bench ) > $OUT/bench-$N.txt 2>&1
  echo "load $(cut -d" " -f1 /proc/loadavg)" >> $OUT/bench-$N.txt
  start_server L$N
  first=$(($(cat $OUT/g/n) + 1))
  $L/grow.sh $MINI $WS $((N + 20)) $OUT/g
  awk -v f=$first '$1 >= f' $OUT/g/writes.tsv > $OUT/writes-at-$N.tsv
  mid=$(( $(cat $OUT/g/n) / 2 )); last=$(cat $OUT/g/n)
  for which in mid last; do id=g${!which}
    /usr/bin/time -f "lookup $which ($id) %e s" -a -o $OUT/lookup-$N.txt $MINI retry --attempt $WS/attempts/$id --mode lookup > $OUT/lookup-$N-$which.out 2> $OUT/lookup-$N-$which.err
    echo "$which: lookup $(jq -c '{transactionId,acceptedCount,worldRoot}' $OUT/lookup-$N-$which.out 2>/dev/null | head -c 300) original $(jq -c '{acceptedCount,worldRoot}' $WS/attempts/$id/outcome.json 2>/dev/null)" >> $OUT/lookup-$N.txt
  done
done
stop_server
echo done > $OUT/state
