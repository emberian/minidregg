#!/bin/bash
# grow.sh MINI WS TARGET_COUNT OUT: scalar writes to `lab` field 2005 until the log
# holds TARGET_COUNT accepted records (as the receipts report). One line per write
# in OUT/writes.tsv: n, acceptedCount, propose_s, submit_s.
set -euo pipefail
MINI=$1 WS=$2 TARGET=$3 OUT=$4
mkdir -p "$OUT/req"
n=$(cat "$OUT/n" 2>/dev/null || echo 0)
count=$(cat "$OUT/count" 2>/dev/null || echo 0)
prev=$(cat "$OUT/prev" 2>/dev/null || echo "")
while [ "$count" -lt "$TARGET" ]; do
  n=$((n+1)); id=g$n
  if [ -z "$prev" ]; then
    printf "%s\n" "{\"type\":\"minidregg-workspace-proposal-v1\",\"action\":\"invoke\",\"targets\":[{\"name\":\"lab\",\"payload\":{\"type\":\"scalar\",\"actions\":[{\"type\":\"create\",\"key\":{\"type\":\"object\",\"field\":\"2005\"},\"value\":\"$n\"}]}}]}" >"$OUT/req/$id.json"
  else
    printf "%s\n" "{\"type\":\"minidregg-workspace-proposal-v1\",\"action\":\"invoke\",\"targets\":[{\"name\":\"lab\",\"payload\":{\"type\":\"scalar\",\"actions\":[{\"type\":\"write\",\"key\":{\"type\":\"object\",\"field\":\"2005\"},\"value\":\"$n\",\"expected\":\"$prev\"}]}}]}" >"$OUT/req/$id.json"
  fi
  t0=$(date +%s.%N)
  "$MINI" workspace --action propose --dir "$WS" --request "$OUT/req/$id.json" --proposal-id "$id" >/dev/null 2>"$OUT/last.err"
  t1=$(date +%s.%N)
  "$MINI" workspace --action submit --dir "$WS" --intent "$WS/proposals/$id/intent.json" --attempt "$WS/attempts/$id" >"$OUT/last.out" 2>>"$OUT/last.err"
  t2=$(date +%s.%N)
  count=$(jq -r ".acceptedCount // .receipt.acceptedCount // empty" "$WS/attempts/$id/outcome.json")
  [ -n "$count" ] || { echo "write $id: no acceptedCount" >&2; exit 1; }
  prev=$n
  printf "%s\t%s\t%.3f\t%.3f\n" "$n" "$count" "$(echo "$t1 - $t0" | bc)" "$(echo "$t2 - $t1" | bc)" >>"$OUT/writes.tsv"
  echo "$n" >"$OUT/n"; echo "$count" >"$OUT/count"; echo "$prev" >"$OUT/prev"
  rm -rf "$WS/proposals/$id" "$WS/attempts/$id.tmp" 2>/dev/null || true
done
echo "count $count after $n writes"
