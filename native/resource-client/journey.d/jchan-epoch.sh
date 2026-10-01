#!/usr/bin/env bash
# journey.d/jchan-epoch.sh — a channel domain's epoch records on the kernel (CH-EPOCH, CHANNELS.md
# §2.4 / §9 row 8), on the journey's fresh Store after J5.
#
# A (the sponsor) is the domain's relay and sequencer. A opens the room `chroom` and births the
# domain's channel stream `chan` --in chroom under the author law "every write is by A". Records are
# built by the kernel's own definitions (scripts/probe-channel-epoch.lean, `lake env lean --run`):
# P1 (class 1, E = 16), n = 3, domain 7. Each append's topic is `channelTopic domain epoch`; its
# payload is the canonical EpochRecord.
#
# Rows (expect admitted|refused; a refusal must name its clause, in the refusal or the operator log):
#   e0-admitted              epoch 0, 16 roots, by A                     -> admitted
#   e1-admitted              epoch 1                                     -> admitted
#   e3-gap                   epoch 3 after 1                             -> refused epochGap
#   e0-again                 epoch 0 after 1 (out of order)              -> refused epochNotAfter
#   e2-short                 epoch 2 with E - 1 = 15 roots               -> refused rootCount
#   e2-by-b                  epoch 2 by B (room grant observe+append)    -> refused (author law, or foreignAuthor)
#   e2-admitted              epoch 2 by A, well-formed (control)         -> admitted
#   first-by-b               B's record as the FIRST of a second stream  -> refused law-denied (the birth
#                            author law: no previous record, so only the stream's law can refuse)
#   opening-wrong-length     e1's opening with one mask byte short       -> refused maskLength
#   opening-opens            e1's opening (48 mask bytes + salt)         -> opened 48
#   tail-epochs              the stream holds e0 e1 e2, in order         -> 3 channel topics
#   cold-audit               service stopped: `audit` re-admits every record
# Exported by the journey: MINI HOST CONFIG SOCKET SPONSOR_WS NEWCOMER_WS SPONSOR_SUBJECT
# NEWCOMER_SUBJECT JOURNEY_WORLD JOURNEY_STEP_DIR. CHE_LEAN_ROOT (default: this checkout) is the
# Lean tree the probe runs in. Exit 0 = every row as expected. Last stdout line = the rows file.
set -uo pipefail
D=$JOURNEY_STEP_DIR
W=$JOURNEY_WORLD
AW=$SPONSOR_WS
BW=$NEWCOMER_WS
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
ROOT=${CHE_LEAN_ROOT:-$(cd "$HERE/../../.." && pwd)}
mkdir -p "$D/req"
rows=$D/chan-rows.tsv
: >"$rows"
bad=0
REFUSAL_TAG=44524547472f4e41544956452d484f53542f4f5554434f4d45

oplog() {
  local f
  for f in $(ls -tr "$W"/public/serve*.log 2>/dev/null); do cat "$f"; done | grep "refused" || true
}
OPLOG_SEEN=$(oplog | wc -l)
run() { # NAME cmd...
  local name=$1; shift
  "$@" >"$D/$name.out" 2>"$D/$name.err"; echo $? >"$D/$name.rc"
}
ok() { [ "$(cat "$D/$1.rc")" = 0 ] || { echo "setup $1 failed: $(tail -1 "$D/$1.err")" >&2; cat "$rows" >&2; exit 1; }; }
refusal_text() {
  grep -o 'encoded refusal: [0-9a-f]*' "$D/$1.err" | tail -1 | cut -d' ' -f3 | xxd -r -p 2>/dev/null \
    | tr -c '[:print:]' ' ' | tr -s ' ' | cut -c1-240
}
check() { # NAME EXPECT GOT [DETAIL]
  printf '%s\texpect=%s\tgot=%s\t%s\n' "$1" "$2" "$3" "${4:-}" >>"$rows"
  [ "$2" = "$3" ] || bad=$((bad + 1))
}
probe() { # ARGS... -> stdout of the Lean probe
  (cd "$ROOT" && PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=2 lake env lean --run scripts/probe-channel-epoch.lean "$@")
}
mkrec() { # NAME EPOCH ROOTS  -> $D/rec-NAME.{topic,payload,opening}
  probe record 7 "$2" 1 3 "$3" "$MASK48" 90 >"$D/rec-$1.txt" 2>"$D/rec-$1.err" \
    || { echo "probe record $1 failed: $(tail -1 "$D/rec-$1.err")" >&2; exit 1; }
  grep -E '^[0-9a-f]+$' "$D/rec-$1.txt" >"$D/rec-$1.hex"
  [ "$(wc -l <"$D/rec-$1.hex")" = 3 ] || { echo "probe record $1: not three hex lines" >&2; exit 1; }
  sed -n 1p "$D/rec-$1.hex" >"$D/rec-$1.topic"
  sed -n 2p "$D/rec-$1.hex" >"$D/rec-$1.payload"
  sed -n 3p "$D/rec-$1.hex" >"$D/rec-$1.opening"
}
# append NAME WS STREAM RECNAME: plan (reads the stream once), then submit. The outcome is the first
# step that refused: a plan refusal names its reason in the client's error, a submit refusal in the
# encoded refusal and the operator log.
append() {
  local name=$1 ws=$2 stream=$3 rec=$4
  jq -n --arg n "$stream" --arg t "$(cat "$D/rec-$rec.topic")" --arg p "$(cat "$D/rec-$rec.payload")" \
    '{type:"minidregg-workspace-proposal-v1",action:"invoke",
      targets:[{name:$n,payload:{type:"append",topicHex:$t,payloadHex:$p}}]}' >"$D/req/$name.json"
  run "plan-$name" "$MINI" workspace --action propose --dir "$ws" --request "$D/req/$name.json" --proposal-id "$name"
  if [ "$(cat "$D/plan-$name.rc")" != 0 ]; then
    cp "$D/plan-$name.rc" "$D/$name.rc"; cp "$D/plan-$name.err" "$D/$name.err"; : >"$D/$name.out"; return
  fi
  run "$name" "$MINI" workspace --action submit --dir "$ws" \
    --intent "$ws/proposals/$name/intent.json" --attempt "$ws/attempts/$name"
}
row() { # NAME EXPECT(admitted|refused) [NEEDLE...: a refusal must name one of them]
  local name=$1 expect=$2 got detail fresh needle hit; shift 2
  fresh=$(oplog | tail -n +$((OPLOG_SEEN + 1)) | tail -3 | tr '\n' ' ' | cut -c1-300)
  OPLOG_SEEN=$(oplog | wc -l)
  if [ "$(cat "$D/$name.rc")" = 0 ]; then got=admitted
  else got=refused
  fi
  detail="$(refusal_text "$name") | $(tail -2 "$D/$name.err" | tr '\n' ' ' | cut -c1-240) | $fresh"
  [ "$got" = admitted ] && detail=$(jq -c '{confirmation: (.receipt.confirmation // .confirmation // .type)}' \
    "$D/$name.out" 2>/dev/null | tail -1)
  if [ "$got" = refused ] && [ "$#" -gt 0 ]; then
    hit=""
    for needle in "$@"; do [[ "$detail" == *"$needle"* ]] && hit=$needle && break; done
    [ -n "$hit" ] || got="refused-not-$1"
  fi
  printf '%s\texpect=%s%s\tgot=%s%s\t%s\n' "$name" "$expect" "${1:+ $*}" "$got" "${hit:+ ($hit)}" "$detail" >>"$rows"
  [ "${got%% *}" = "$expect" ] || bad=$((bad + 1))
}

MASK48=010000000000000000000000000000000000000000000000   # P1: E·n = 16·3 positions

A=$SPONSOR_SUBJECT
B=$NEWCOMER_SUBJECT
printf '%s\n' '{"type":"all","predicates":[]}' >"$D/req/permit-all.json"
# the sequencer's author law: every write (mutate = 2, append = 7) is by A
jq -n --arg s "$A" '{type:"any",predicates:[
  {type:"not",predicate:{type:"memberOf",slot:"request/verb",values:["2","7"]}},
  {type:"eq",slot:"request/subject",value:$s}]}' >"$D/req/law-seq.json"

run create-room "$MINI" workspace --action create --dir "$AW" --name chroom --storage declared \
  --predicate "$D/req/permit-all.json"; ok create-room
run create-chan "$MINI" workspace --action create --dir "$AW" --name chan --storage stream \
  --predicate "$D/req/law-seq.json" --in chroom; ok create-chan
chan=$(jq -r .target "$AW/refs/chan.json")

# B joins the room with observe + append (the room grant covers chan); only the laws stand between.
jq -n --arg r "$B" '{type:"minidregg-workspace-proposal-v1",action:"delegate",name:"chroom",
  recipient:$r,verbs:["observe","append"],maxCost:"50000",room:true}' >"$D/req/invite-b.json"
run invite-propose "$MINI" workspace --action propose --dir "$AW" --request "$D/req/invite-b.json" \
  --proposal-id chinvite-b; ok invite-propose
run invite-submit "$MINI" workspace --action submit --dir "$AW" \
  --intent "$AW/proposals/chinvite-b/intent.json" --attempt "$AW/attempts/chinvite-b"; ok invite-submit
run invite-publish "$MINI" workspace --action publish-delegation --dir "$AW" --proposal-id chinvite-b \
  --attempt "$AW/attempts/chinvite-b"; ok invite-publish
run b-import-room "$MINI" workspace --action import --dir "$BW" --name chroom \
  --from-ref "$AW/proposals/chinvite-b/recipient-reference.json"; ok b-import-room
bcap=$(jq -r .observeCapability "$BW/refs/chroom.json")
run b-import-chan "$MINI" workspace --action import --dir "$BW" --name chan --kind object \
  --target "$chan" --observe-capability "$bcap" --operation-capability "$bcap"; ok b-import-chan

# The records, from the kernel's definitions.
mkrec e0 0 16; mkrec e1 1 16; mkrec e3 3 16; mkrec e2short 2 15; mkrec e2 2 16

append e0-admitted "$AW" chan e0;            row e0-admitted admitted
append e1-admitted "$AW" chan e1;            row e1-admitted admitted
append e3-gap "$AW" chan e3;                 row e3-gap refused epochGap
append e0-again "$AW" chan e0;               row e0-again refused epochNotAfter
append e2-short "$AW" chan e2short;          row e2-short refused rootCount
append e2-by-b "$BW" chan e2;                row e2-by-b refused law-denied foreignAuthor
append e2-admitted "$AW" chan e2;            row e2-admitted admitted

# The first record has no previous author to match: the stream's birth law is the lock.
run create-chan2 "$MINI" workspace --action create --dir "$AW" --name chan2 --storage stream \
  --predicate "$D/req/law-seq.json" --in chroom; ok create-chan2
run b-import-chan2 "$MINI" workspace --action import --dir "$BW" --name chan2 --kind object \
  --target "$(jq -r .target "$AW/refs/chan2.json")" --observe-capability "$bcap" --operation-capability "$bcap"
ok b-import-chan2
append first-by-b "$BW" chan2 e0;            row first-by-b refused law-denied

# The opening goes to the operator and the witnesses, not into the channel cell: checked here
# against e1's record bytes by the kernel's openRecord.
short=$(cut -c3- "$D/rec-e1.opening")   # one mask byte short
got=$(probe open "$(cat "$D/rec-e1.payload")" "$short" 2>"$D/open-short.err" | grep -E '^(opened|refused)')
check opening-wrong-length "refused maskLength" "$got" "$(( ${#short} / 2 )) bytes; E·n + 32 = 80"
got=$(probe open "$(cat "$D/rec-e1.payload")" "$(cat "$D/rec-e1.opening")" 2>"$D/open-ok.err" | grep -E '^(opened|refused)')
check opening-opens "opened 48" "$got" "80 bytes"

# The stream holds e0 e1 e2 in order, each under its channel topic.
run tail-chan "$MINI" workspace --action tail --dir "$AW" --name chan --from 1 --count 16
want="$(cat "$D/rec-e0.topic") $(cat "$D/rec-e1.topic") $(cat "$D/rec-e2.topic")"
gotT=$(jq -r '[.entries[].topic] | join(" ")' "$D/tail-chan.out" 2>/dev/null)
if [ "$gotT" = "$want" ]; then check tail-epochs "e0 e1 e2" "e0 e1 e2" "3 entries, channel topics"
else check tail-epochs "e0 e1 e2" "other" "$(jq -c '[.entries[] | {sequence, topic}]' "$D/tail-chan.out" 2>/dev/null | cut -c1-300)"; fi

# Cold audit: stop our service, audit the closed Store, start it again on the same socket.
pidfile=$W/public/server.pid
pid=$(cat "$pidfile")
kids=$(pgrep -P "$pid" | tr '\n' ' ')
kill -TERM "$pid"
for i in $(seq 1 300); do kill -0 "$pid" 2>/dev/null || break; sleep 0.1; done
for k in $kids; do for i in $(seq 1 100); do kill -0 "$k" 2>/dev/null || break; sleep 0.1; done; done
"$MINI" audit --host "$HOST" --config "$CONFIG" >"$D/audit.out" 2>"$D/audit.err"; arc=$?
check cold-audit "exit=0" "exit=$arc" "$(cat "$D/audit.out" "$D/audit.err" | grep -i audit | tail -1 | cut -c1-200)"
setsid nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$W/public/serve-jchan.log" 2>&1 </dev/null &
echo $! >"$pidfile"
for i in $(seq 1 6000); do
  [ -S "$SOCKET" ] && grep -q serving "$W/public/serve-jchan.log" 2>/dev/null && break; sleep 0.1
done

cat "$rows" >&2
n=$(wc -l <"$rows")
[ "$bad" = 0 ] || { echo "$bad of $n channel-epoch rows differ from expectation (see $rows)" >&2; exit 1; }
echo "$n/$n channel-epoch rows as expected: e0 e1 e2 admitted; gap, out-of-order, E-1 roots and a non-sequencer refused by name; a short opening refused maskLength; tail in order; cold audit" >&2
echo "$rows"
