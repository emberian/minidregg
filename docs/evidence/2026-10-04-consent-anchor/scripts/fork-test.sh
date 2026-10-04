#!/bin/bash
# fork-test.sh: the retained consent anchor detects a rolled-back and a rewritten (forked) prefix
# that a genesis re-admission accepts. World w/fork (fresh, own socket, own anchor dir).
#  1. grow to 5; snapshot the Store (with its head-anchor sidecar: an operator that rolls back both)
#  2. write values A6, A7 -> anchor A at height 7 (kept aside)
#  3. ROLLBACK: restore the height-5 Store; the next client run must refuse (anchor 7 above head 5)
#  4. FORK: with no anchor, write B6, B7 on the height-5 Store (genesis re-admission accepts this valid history)
#  5. offer anchor A against the forked height-7 Store: must refuse as a rewritten prefix
#  6. control: anchor B (the fork's own) accepts the next write
set -uo pipefail
L=${L:-/srv/lanes/schema-v2-2}
B=$L/bin-mine MINI=$B/mini
W=$L/w/fork OUT=$L/evidence/fork SOCK=$L/w/fork.sock
export MINI_CONSENT_ANCHOR_DIR=$OUT/anchors
rm -rf $W $OUT; mkdir -p $OUT/anchors $OUT/req; chmod 700 $OUT/anchors
sh $L/src/native/resource-client/newparticipant-acceptance.sh $B/minidregg-host $MINI $B/minidregg-link-sqlite-store $B/minidregg-credential-signature-verifier $W $SOCK > $OUT/bootstrap.out 2> $OUT/bootstrap.err || { echo bootstrap failed; exit 1; }
CONFIG=$(jq -r .config $W/handoff.json); WS=$W/sponsor
printf '%s\n' '{"type":"all","predicates":[]}' > $OUT/permit-all.json
$MINI workspace --action create --dir $WS --name lab --storage declared --predicate $OUT/permit-all.json --fields 2005 > $OUT/create.out 2> $OUT/create.err || { echo create failed; exit 1; }
write() { # write ID VALUE EXPECTED -> prints acceptedCount or the refusal
  local id=$1 v=$2 e=$3 action
  if [ -z "$e" ]; then action="{\"type\":\"create\",\"key\":{\"type\":\"object\",\"field\":\"2005\"},\"value\":\"$v\"}"
  else action="{\"type\":\"write\",\"key\":{\"type\":\"object\",\"field\":\"2005\"},\"value\":\"$v\",\"expected\":\"$e\"}"; fi
  printf '%s\n' "{\"type\":\"minidregg-workspace-proposal-v1\",\"action\":\"invoke\",\"targets\":[{\"name\":\"lab\",\"payload\":{\"type\":\"scalar\",\"actions\":[$action]}}]}" > $OUT/req/$id.json
  if $MINI workspace --action propose --dir $WS --request $OUT/req/$id.json --proposal-id $id > $OUT/$id.propose.out 2> $OUT/$id.propose.err &&
     $MINI workspace --action submit --dir $WS --intent $WS/proposals/$id/intent.json --attempt $WS/attempts/$id > $OUT/$id.submit.out 2> $OUT/$id.submit.err; then
    echo "$id accepted count=$(jq -r '.acceptedCount // .receipt.acceptedCount' $WS/attempts/$id/outcome.json)"
  else echo "$id REFUSED: $(grep -h -i "consent\|refused" $OUT/$id.propose.err $OUT/$id.submit.err | head -2 | tr '\n' ' ')"; fi
}
stop_server() { P=$(cat $W/public/server.pid); kill -TERM $P; for i in $(seq 1 100); do kill -0 $P 2>/dev/null || break; sleep 0.1; done; }
start_server() { setsid nohup $MINI serve --host $B/minidregg-host --config $CONFIG --socket $SOCK > $W/public/serve-$1.log 2>&1 < /dev/null & echo $! > $W/public/server.pid
  for i in $(seq 1 600); do grep -q serving $W/public/serve-$1.log 2>/dev/null && break; sleep 0.05; done; }
snap() { rm -rf $OUT/$1; mkdir -p $OUT/$1; cp -a $W/store $W/store.head-anchor $OUT/$1/; }
restore() { rm -rf $W/store; cp -a $OUT/$1/store $OUT/$1/store.head-anchor $W/; }
anchor() { ls $OUT/anchors/*.anchor; }
{
echo "== 1. grow to 5"
write w2 2 ""; write w3 3 2; write w4 4 3; write w5 5 4
stop_server; snap s5; start_server s5
echo "== 2. A6 A7"
write a6 60 5; write a7 70 60
cp -p $(anchor) $OUT/anchor-A
stop_server
echo "== 3. ROLLBACK: the height-5 Store under anchor A (height 7)"
restore s5; start_server rb
write r6 61 5
stop_server
echo "== 4. FORK: B6 B7 on the height-5 Store with no retained anchor"
mv $(anchor) $OUT/anchor-moved-aside; restore s5; start_server fork
write b6 600 5; write b7 700 600
cp -p $(anchor) $OUT/anchor-B
echo "== 5. anchor A offered against the forked Store"
cp -p $OUT/anchor-A $(anchor)
write x8 800 700
echo "== 6. control: anchor B accepts"
cp -p $OUT/anchor-B $(anchor)
write c8 800 700
stop_server
} 2>&1 | tee $OUT/fork-test.txt
