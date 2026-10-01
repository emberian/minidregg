#!/bin/sh
# Pug's `dregg-client-sign` journey (join, send, transfer, receipts) run with
# `mini fleet-sign` -- the same verbs, flags and one-object stdout -- against a
# fresh Mini Store; then a Host restart and an exact retry of a committed
# transfer, and INTERLEAVED turns from three fleet keys at once.
#
# usage: fleet-sign-journey.sh HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY [INTERLEAVED_TURNS]
set -eu
umask 077

if [ "$#" -lt 5 ] || [ "$#" -gt 6 ]; then
  echo "usage: $0 HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY [INTERLEAVED_TURNS]" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 ROOT=$5 TURNS=${6:-100}
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
case "$ROOT" in /*) ;; *) echo 'journey path must be absolute' >&2; exit 2;; esac
[ ! -e "$ROOT" ] && [ ! -L "$ROOT" ] || { echo 'journey directory already exists' >&2; exit 2; }
command -v jq >/dev/null 2>&1 || { echo 'jq is required' >&2; exit 2; }
mkdir -m 700 "$ROOT"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)
OUT="$ROOT/evidence"
mkdir -m 700 "$OUT"
FIX="$ROOT/fixture"
TIMES="$OUT/timings.tsv"
printf 'step\tverb\tseconds\tresult\n' >"$TIMES"

SERVER_PID=
stop_server() {
  if [ -n "$SERVER_PID" ] && kill -0 "$SERVER_PID" 2>/dev/null; then
    kill "$SERVER_PID" 2>/dev/null || true
    i=0
    while kill -0 "$SERVER_PID" 2>/dev/null && [ "$i" -lt 100 ]; do i=$((i + 1)); sleep 0.1; done
  fi
  SERVER_PID=
}
trap stop_server EXIT INT TERM

now() { date +%s.%N; }
elapsed() { awk -v a="$1" -v b="$2" 'BEGIN { printf "%.3f", b - a }'; }

step() {
  name=$1 verb=$2; shift 3
  t0=$(now)
  if "$@" >"$OUT/$name.json" 2>"$OUT/$name.stderr"; then
    printf '%s\t%s\t%s\tok\n' "$name" "$verb" "$(elapsed "$t0" "$(now)")" >>"$TIMES"
  else
    printf '%s\t%s\t%s\tFAILED\n' "$name" "$verb" "$(elapsed "$t0" "$(now)")" >>"$TIMES"
    echo "journey step $name failed:" >&2; tail -20 "$OUT/$name.stderr" >&2; exit 1
  fi
}
refuse() {
  name=$1 verb=$2 expect=$3; shift 4
  t0=$(now)
  if "$@" >"$OUT/$name.json" 2>"$OUT/$name.stderr"; then
    printf '%s\t%s\t%s\tUNEXPECTED-ACCEPT\n' "$name" "$verb" "$(elapsed "$t0" "$(now)")" >>"$TIMES"
    echo "journey refusal pole $name was accepted" >&2; exit 1
  fi
  grep -q -- "$expect" "$OUT/$name.stderr" || {
    echo "refusal pole $name did not name '$expect':" >&2; cat "$OUT/$name.stderr" >&2; exit 1; }
  printf '%s\t%s\t%s\trefused\n' "$name" "$verb" "$(elapsed "$t0" "$(now)")" >>"$TIMES"
}
one_object() { jq -s -e 'length == 1' "$1" >/dev/null || { echo "$1 is not exactly one JSON object" >&2; exit 1; }; }

serve() {
  log=$1
  nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" >"$log" 2>&1 </dev/null &
  SERVER_PID=$!
  i=0
  until grep -q '^mini: serving ' "$log" 2>/dev/null; do
    kill -0 "$SERVER_PID" 2>/dev/null || { echo 'Mini server exited' >&2; exit 1; }
    i=$((i + 1)); [ "$i" -lt 6000 ] || { echo 'Mini server not ready' >&2; exit 1; }
    sleep 0.1
  done
}

t0=$(now)
"$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$FIX" \
  >"$OUT/fixture.stdout" 2>"$OUT/fixture.stderr"
SERVER_PID=$(cat "$FIX/public/server.pid")
printf 'fixture\tgenesis+serve+sponsor\t%s\tok\n' "$(elapsed "$t0" "$(now)")" >>"$TIMES"
CONFIG="$FIX/deployment/pinned-config.json"
SOCKET="$FIX/public/mini.sock"
FEE=$(jq -er '.tariffBase | tostring' "$FIX/operator.json")

# The harness's environment: one fleet home, one sponsor; profiles by name.
export MINI_FLEET_HOME="$ROOT/fleet-home" MINI_FLEET_SPONSOR="$FIX/sponsor"
FS="$MINI fleet-sign"

# --- J1 join (first use creates the key; the sponsor admits it and funds an owned account)
step join-alpha join -- $FS join --profile alpha --fund 1000
step join-bravo join -- $FS join --profile bravo --fund 500
step join-charlie join -- $FS join --profile charlie --fund 500
for p in alpha bravo charlie; do one_object "$OUT/join-$p.json"; done
jq -e '.joined and .materialized and .balance == 1000' "$OUT/join-alpha.json" >/dev/null
A=$(jq -er .cell "$OUT/join-alpha.json"); B=$(jq -er .cell "$OUT/join-bravo.json")
C=$(jq -er .cell "$OUT/join-charlie.json")
step join-alpha-again join -- $FS join --profile alpha --fund 1000
jq -e --arg a "$A" '.joined and (.materialized | not) and .cell == $a and .balance == 1000' \
  "$OUT/join-alpha-again.json" >/dev/null

# --- J2 send (one fleet turn: an event on the profile's own topic + the fee)
step send send -- $FS send --profile alpha --topic client-sign hello from alpha
one_object "$OUT/send.json"
jq -e --arg a "$A" --arg fee "$FEE" '.sent and .agent_cell == $a and .payload == "hello from alpha"
  and .sequence == 1 and (.fee | tostring) == $fee and .finality == "accepted"
  and (.turn_hash | test("^[0-9]+$"))' "$OUT/send.json" >/dev/null

# --- J3 transfer
step transfer transfer -- $FS transfer --profile alpha --to "$B" --amount 25
one_object "$OUT/transfer.json"
jq -e --arg b "$B" '.transferred and .committed and .to == $b and .amount == 25' \
  "$OUT/transfer.json" >/dev/null

# --- J4 receipts: exact by turn hash, and the agent head
SEND_TX=$(jq -er .turn_hash "$OUT/send.json"); TRANSFER_TX=$(jq -er .turn_hash "$OUT/transfer.json")
step receipt-send receipt -- $FS receipt --profile alpha --turn-hash "$SEND_TX"
jq -e --slurpfile s "$OUT/send.json" '.found and .receipt == $s[0].receipt' "$OUT/receipt-send.json" >/dev/null
step receipt-transfer receipt -- $FS receipt --profile bravo --turn-hash "$TRANSFER_TX"
jq -e --slurpfile t "$OUT/transfer.json" '.receipt == $t[0].receipt' "$OUT/receipt-transfer.json" >/dev/null
step receipt-head receipt -- $FS receipt --profile alpha --head
jq -e --slurpfile t "$OUT/transfer.json" '.head.turns == "2" and .head.head == $t[0].receipt' \
  "$OUT/receipt-head.json" >/dev/null

# --- refusals, each naming its reason
refuse unknown-tx receipt 'no accepted transaction' -- $FS receipt --profile alpha --turn-hash 1
refuse self-transfer transfer 'own account' -- $FS transfer --profile alpha --to "$A" --amount 1
refuse overdraw transfer 'bookRefused\|not admitted' -- $FS transfer --profile bravo --to "$A" --amount 100000
refuse bread-cell-id transfer 'Bread cell id' -- $FS transfer --profile alpha \
  --to "$(printf 'ab%.0s' $(seq 32))" --amount 1
refuse http-node send 'no HTTP ingress' -- $FS send --profile alpha --node-url http://127.0.0.1:8899 x
refuse token-file send 'no bearer token' -- $FS send --profile alpha --token-file /dev/null x
refuse tentative transfer 'one commitment level' -- $FS transfer --profile alpha --to "$B" --amount 1 \
  --accept-tentative
refuse not-joined send 'has not joined' -- $FS send --profile delta x
step node-url-unix send -- $FS send --profile alpha --node-url "unix:$SOCKET" --topic news via unix url
refuse wrong-socket send 'differs from pinned' -- $FS send --profile alpha --node-url unix:/nonexistent/mini.sock x

# --- J5 restart + exact retry of the committed transfer
stop_server
t0=$(now)
serve "$FIX/public/serve-restart.log"
printf 'restart\tserve\t%s\tok\n' "$(elapsed "$t0" "$(now)")" >>"$TIMES"
ATTEMPT=$(jq -er .attempt "$OUT/transfer.json")
step exact-retry retry -- $FS retry --profile alpha --attempt "$ATTEMPT"
one_object "$OUT/exact-retry.json"
jq -e --slurpfile t "$OUT/transfer.json" '.confirmation == "replayed" and .receipt == $t[0].receipt' \
  "$OUT/exact-retry.json" >/dev/null
step exact-retry-again retry -- $FS retry --profile alpha --attempt "$ATTEMPT"
jq -e --slurpfile t "$OUT/transfer.json" '.confirmation == "replayed" and .receipt == $t[0].receipt' \
  "$OUT/exact-retry-again.json" >/dev/null
step balance-bravo join -- $FS join --profile bravo --fund 0
jq -e '.balance == 525' "$OUT/balance-bravo.json" >/dev/null   # 500 + 25 once, never twice
step balance-alpha join -- $FS join --profile alpha --fund 0
EXPECT_A=$((1000 - 25 - 3 * FEE))
jq -e --argjson v "$EXPECT_A" '.balance == $v' "$OUT/balance-alpha.json" >/dev/null

# --- J6 interleaved: TURNS turns from three keys at once (sends and transfers)
INTER="$OUT/interleaved.tsv"
printf 'profile\ti\tverb\tseconds\treplans\tresult\n' >"$INTER"
mkdir -m 700 "$OUT/interleaved"
per=$(( (TURNS + 2) / 3 ))
agent_loop() {
  me=$1 peer=$2 n=$3
  i=1
  while [ "$i" -le "$n" ]; do
    f="$OUT/interleaved/$me-$i.json"
    t0=$(now)
    if [ $((i % 2)) -eq 1 ]; then verb=send
      set -- $FS send --profile "$me" --topic chat "$me turn $i"
    else verb=transfer
      set -- $FS transfer --profile "$me" --to "$peer" --amount 1
    fi
    if "$@" >"$f" 2>"$f.stderr"; then r=ok; rp=$(jq -r .replans "$f"); else r=FAILED; rp=-; fi
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$me" "$i" "$verb" "$(elapsed "$t0" "$(now)")" "$rp" "$r" >>"$INTER"
    i=$((i + 1))
  done
}
t0=$(now)
agent_loop alpha "$B" "$per" & P1=$!
agent_loop bravo "$C" "$per" & P2=$!
agent_loop charlie "$A" $((TURNS - 2 * per)) & P3=$!
wait "$P1" "$P2" "$P3"
WALL=$(elapsed "$t0" "$(now)")
printf 'interleaved\t%s-turns-3-keys\t%s\tok\n' "$TURNS" "$WALL" >>"$TIMES"
SUPERSEDED_DIRS="$MINI_FLEET_HOME"/profiles/*/workspace/attempts/*/superseded.json
STALE_PLANS=$(cat $SUPERSEDED_DIRS 2>/dev/null | jq -s '[.[] | select(.reason == "stale-root-at-plan")] | length')
STALE_OBSERVATIONS=$(cat $SUPERSEDED_DIRS 2>/dev/null | jq -s '[.[] | select(.reason == "stale-root-at-observation")] | length')
CONTENTIONS=$(cat $SUPERSEDED_DIRS 2>/dev/null | jq -s '[.[] | select(.reason == "contention")] | length')
FAILED=$(awk -F'\t' 'NR>1 && $6 != "ok"' "$INTER" | wc -l)
REPLANS=$(awk -F'\t' 'NR>1 && $5 != "-" {s += $5} END {print s + 0}' "$INTER")
ADMITTED=$(awk -F'\t' 'NR>1 && $6 == "ok"' "$INTER" | wc -l)
[ "$FAILED" -eq 0 ] || { echo "interleaved: $FAILED turns failed" >&2; exit 1; }

# conservation: every interleaved transfer moved exactly 1, every turn paid FEE
for p in alpha bravo charlie; do
  step "final-$p" join -- $FS join --profile "$p" --fund 0
done
SUM=$(jq -s 'map(.balance) | add' "$OUT/final-alpha.json" "$OUT/final-bravo.json" "$OUT/final-charlie.json")
TOTAL_TURNS=$(( ADMITTED + 3 ))          # send, transfer, the unix-url send
EXPECT_SUM=$(( 2000 - FEE * TOTAL_TURNS ))
[ "$SUM" -eq "$EXPECT_SUM" ] || { echo "conservation: sum $SUM, expected $EXPECT_SUM" >&2; exit 1; }
stop_server

sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$CONFIG" >"$OUT/binaries.sha256"
jq -n --arg turns "$TURNS" --arg admitted "$ADMITTED" --arg replans "$REPLANS" --arg wall "$WALL" \
  --arg sum "$SUM" --arg fee "$FEE" --arg stale "$STALE_PLANS" --arg cont "$CONTENTIONS" --arg sobs "$STALE_OBSERVATIONS" \
  '{type:"minidregg-fleet-sign-journey-v1", interleaved:{turns:$turns, admitted:$admitted,
    replans:$replans, staleObservations:$sobs, stalePlans:$stale, submitContentions:$cont, wallSeconds:$wall},
    balanceSum:$sum, fee:$fee, result:"pass"}' >"$OUT/summary.json"
printf '%s\n' "$OUT"
