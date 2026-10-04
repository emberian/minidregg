#!/bin/bash
# stop-between-writes.sh TAG PARENT_PID: stop a running growth (its growth-run.sh parent first, then
# its grow.sh right after a write lands), then reconcile the grow state with the attempts on disk.
L=/home/ember/workbox/claude-lanes/schema-v2
TAG=$1 PARENT=$2
G=$L/evidence/grow-$TAG/g WS=$L/w/grow-$TAG/sponsor
kill -TERM $PARENT 2>/dev/null
GROW=$(ps -u ember -o pid=,args= | awk -v t="w/grow-$TAG/sponsor" '$0 ~ /grow\.sh/ && index($0, t) {print $1}' | head -1)
before=$(wc -l < $G/writes.tsv)
while [ "$(wc -l < $G/writes.tsv)" = "$before" ]; do sleep 0.2; done
sleep 0.3
kill -TERM $GROW 2>/dev/null
pkill -TERM -P $GROW 2>/dev/null
sleep 2
n=$(cat $G/n); next=g$((n + 1))
if [ -f $WS/attempts/$next/outcome.json ] && [ "$(jq -r .type $WS/attempts/$next/outcome.json)" = confirmed ]; then
  c=$(jq -r ".acceptedCount // .receipt.acceptedCount" $WS/attempts/$next/outcome.json)
  printf "%s\t%s\tNA\tNA\n" $((n + 1)) $c >> $G/writes.tsv
  echo $((n + 1)) > $G/n; echo $c > $G/count; echo $((n + 1)) > $G/prev
  echo "reconciled: $next landed (count $c)"
else
  for d in $WS/proposals/$next $WS/attempts/$next; do [ -e $d ] && mv $d $d.aborted && echo "aside: $d"; done
fi
echo "stopped $TAG at n=$(cat $G/n) count=$(cat $G/count)"
