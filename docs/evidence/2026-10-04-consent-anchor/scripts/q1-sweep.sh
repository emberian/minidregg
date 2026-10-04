#!/bin/bash
# q1-sweep.sh: consent admission time vs history length on a fresh world (w/grow-sweep).
# At each level: grow (certifying every 64), then time one provider's admission
#   anchored: offered the retained anchor (lagging by the provider's own last write)
#   genesis : no anchor (the pre-anchor behaviour: re-admit every record), up to GENESIS_MAX
# Output: evidence/q1-sweep/sweep.tsv (records, anchored_s, genesis_s, propose_s, submit_s, load, builds)
set -uo pipefail
L=${L:-/srv/lanes/schema-v2-2}; B=$L/bin-mine
export MINI_CONSENT_ANCHOR_DIR=$L/evidence/q1-sweep/anchors
OUT=$L/evidence/q1-sweep; mkdir -p $MINI_CONSENT_ANCHOR_DIR; chmod 700 $MINI_CONSENT_ANCHOR_DIR
GENESIS_MAX=${GENESIS_MAX:-100}
[ -f $L/evidence/grow-sweep/state ] || $L/grow-world.sh sweep $B $L/src 2005 || exit 1
WS=$L/w/grow-sweep/sponsor
printf "records\tanchored_s\tgenesis_s\tpropose_s\tsubmit_s\tload1\tlean_builds\n" > $OUT/sweep.tsv
for N in 10 25 50 100 150 200 250 300; do
  CERTIFY_GENESIS=$L/w/grow-sweep/genesis.json $L/grow.sh $B/mini $WS $N $L/evidence/grow-sweep/g >> $OUT/grow.log 2>&1 || { echo grow-failed-$N; exit 1; }
  C=$(ls -t $WS/attempts/*/config.json | head -1); A=$(ls $MINI_CONSENT_ANCHOR_DIR/*.anchor)
  anch=$(python3 $L/consent-admit.py $B/minidregg-client-consent $C $A | tee -a $OUT/admit.jsonl | jq -r .admission_s)
  gen=NA; [ $N -le $GENESIS_MAX ] && gen=$(python3 $L/consent-admit.py $B/minidregg-client-consent $C | tee -a $OUT/admit.jsonl | jq -r .admission_s)
  w=$(tail -1 $L/evidence/grow-sweep/g/writes.tsv)
  builds=$(pgrep -c -f "lake build" || true)
  printf "%s\t%s\t%s\t%s\t%s\t%s\t%s\n" "$(cat $L/evidence/grow-sweep/g/count)" "$anch" "$gen" "$(echo "$w" | cut -f3)" "$(echo "$w" | cut -f4)" "$(cut -d' ' -f1 /proc/loadavg)" "$builds" >> $OUT/sweep.tsv
done
P=$(cat $L/w/grow-sweep/public/server.pid); kill -TERM $P
cat $OUT/sweep.tsv
