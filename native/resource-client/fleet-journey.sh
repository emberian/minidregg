#!/bin/sh
# Agent-fleet journey on one fresh, private Mini Store:
#   join (enroll + owned funded account) x2 -> send (topic event + payment +
#   fee) -> transfer -> receipt lookup (by transaction id, by agent head, by
#   attempt) -> publish x2 -> poll by cursor -> refusal poles -> cold restart
#   and re-poll. Every verb is timed; every refusal is required to refuse.
# Run on the same Linux host as the native Host/Store/verifier. Nothing is
# copied from another Store. The service started here is always stopped.
set -eu
umask 077

if [ "$#" -ne 5 ]; then
  echo "usage: $0 HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 ROOT=$5
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

# step NAME VERB -- command...   (must succeed; stdout -> $OUT/NAME.json)
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
# refuse NAME VERB -- command...  (must fail; the refusal is the result)
refuse() {
  name=$1 verb=$2; shift 3
  t0=$(now)
  if "$@" >"$OUT/$name.json" 2>"$OUT/$name.stderr"; then
    printf '%s\t%s\t%s\tUNEXPECTED-ACCEPT\n' "$name" "$verb" "$(elapsed "$t0" "$(now)")" >>"$TIMES"
    echo "journey refusal pole $name was accepted" >&2; exit 1
  fi
  printf '%s\t%s\t%s\trefused\n' "$name" "$verb" "$(elapsed "$t0" "$(now)")" >>"$TIMES"
}

t0=$(now)
"$HERE/newparticipant-acceptance.sh" "$HOST" "$MINI" "$STORE" "$VERIFIER" "$FIX" \
  >"$OUT/fixture.stdout" 2>"$OUT/fixture.stderr"
SERVER_PID=$(cat "$FIX/public/server.pid")
printf 'fixture\tgenesis+serve+sponsor\t%s\tok\n' "$(elapsed "$t0" "$(now)")" >>"$TIMES"
CONFIG="$FIX/deployment/pinned-config.json"
SOCKET="$FIX/public/mini.sock"
SPONSOR="$FIX/sponsor"
FEE=$(jq -er '.tariffBase | tostring' "$FIX/operator.json")

"$MINI" keygen --secret "$ROOT/agent-a.key" --public "$ROOT/agent-a.pub" >/dev/null
"$MINI" keygen --secret "$ROOT/agent-b.key" --public "$ROOT/agent-b.pub" >/dev/null
mkdir -m 700 "$ROOT/enroll"

# --- join ---------------------------------------------------------------
step join-a join -- "$MINI" fleet --action join --sponsor-workspace "$SPONSOR" \
  --factory-ref factory --name agent-a --new-key "$ROOT/agent-a.key" \
  --enroll-dir "$ROOT/enroll/agent-a" --dir "$ROOT/agent-a" --fund 1000
step join-b join -- "$MINI" fleet --action join --sponsor-workspace "$SPONSOR" \
  --factory-ref factory --name agent-b --new-key "$ROOT/agent-b.key" \
  --enroll-dir "$ROOT/enroll/agent-b" --dir "$ROOT/agent-b" --fund 500
# join also prints each sub-step's record; the join's own record is retained.
cp "$ROOT/agent-a/join-account.json" "$OUT/join-a.record.json"
cp "$ROOT/agent-b/join-account.json" "$OUT/join-b.record.json"
A_ACCOUNT=$(jq -er .account "$OUT/join-a.record.json")
B_ACCOUNT=$(jq -er .account "$OUT/join-b.record.json")
jq -e '.joined and .balance == "1000"' "$OUT/join-a.record.json" >/dev/null
jq -e '.joined and .balance == "500"' "$OUT/join-b.record.json" >/dev/null

# --- send: one topic event that also pays a service account, with the fee ---
step send send -- "$MINI" fleet --action send --dir "$ROOT/agent-a" --account account \
  --topic inbox --payload 'hello from agent-a' --to "$B_ACCOUNT" --amount 7
jq -e --arg fee "$FEE" '.fee == $fee and .transfer.amount == "7" and
  .publication.sequence == "1"' "$OUT/send.json" >/dev/null

# --- transfer -----------------------------------------------------------
step transfer transfer -- "$MINI" fleet --action transfer --dir "$ROOT/agent-a" \
  --account account --to "$B_ACCOUNT" --amount 25
jq -e '.transfer.amount == "25" and .publication == null' "$OUT/transfer.json" >/dev/null

# --- receipt lookup -----------------------------------------------------
SEND_TX=$(jq -er .receipt.transactionId "$OUT/send.json")
TRANSFER_TX=$(jq -er .receipt.transactionId "$OUT/transfer.json")
step receipt-by-transaction receipt -- "$MINI" fleet --action receipt --dir "$ROOT/agent-a" \
  --transaction "$SEND_TX"
jq -e --slurpfile s "$OUT/send.json" '.receipt == $s[0].receipt' \
  "$OUT/receipt-by-transaction.json" >/dev/null
step receipt-by-head receipt -- "$MINI" fleet --action receipt --dir "$ROOT/agent-a" \
  --head-of account
jq -e --slurpfile t "$OUT/transfer.json" '.turns == "2" and .head == $t[0].receipt' \
  "$OUT/receipt-by-head.json" >/dev/null
step receipt-by-attempt receipt -- "$MINI" fleet --action lookup --dir "$ROOT/agent-a" \
  --attempt "$(jq -er .attempt "$OUT/send.json")"
jq -e --slurpfile s "$OUT/send.json" '.type == "confirmed" and .confirmation == "replayed" and
  .transactionId == $s[0].receipt.transactionId and .acceptedCount == $s[0].receipt.acceptedCount' \
  "$OUT/receipt-by-attempt.json" >/dev/null

# --- publish x2 on another topic ------------------------------------------
step publish-1 publish -- "$MINI" fleet --action publish --dir "$ROOT/agent-a" \
  --account account --topic news --payload 'first news'
step publish-2 publish -- "$MINI" fleet --action publish --dir "$ROOT/agent-a" \
  --account account --topic news --payload 'second news'
jq -e '.publication.sequence == "1"' "$OUT/publish-1.json" >/dev/null
jq -e '.publication.sequence == "2"' "$OUT/publish-2.json" >/dev/null

# --- poll by cursor -----------------------------------------------------
step poll-news-0 poll -- "$MINI" fleet --action poll --dir "$ROOT/agent-a" \
  --account account --topic news --since 0
jq -e '.head == "2" and (.events | length) == 2 and .nextCursor == "2" and
  .events[0].payloadText == "first news" and .events[1].payloadText == "second news"' \
  "$OUT/poll-news-0.json" >/dev/null
step poll-news-1 poll -- "$MINI" fleet --action poll --dir "$ROOT/agent-a" \
  --account account --topic news --since 1
jq -e '(.events | length) == 1 and .events[0].sequence == "2"' "$OUT/poll-news-1.json" >/dev/null
step poll-news-2 poll -- "$MINI" fleet --action poll --dir "$ROOT/agent-a" \
  --account account --topic news --since 2
jq -e '(.events | length) == 0 and .nextCursor == "2"' "$OUT/poll-news-2.json" >/dev/null
step poll-inbox poll -- "$MINI" fleet --action poll --dir "$ROOT/agent-a" \
  --account account --topic inbox --since 0
jq -e --slurpfile s "$OUT/send.json" '(.events | length) == 1 and
  .events[0].payloadText == "hello from agent-a" and
  .events[0].transactionId == $s[0].receipt.transactionId' "$OUT/poll-inbox.json" >/dev/null

# --- subscribe: agent-a grants agent-b observe-only on its account ---------
# The existing narrowed-delegation path; reading a topic is the account's
# observe grant, so a subscriber holds exactly that and nothing more.
B_SUBJECT=$(jq -er .subject "$OUT/join-b.record.json")
printf '{"type":"minidregg-workspace-proposal-v1","action":"delegate","name":"account","recipient":"%s","verbs":["observe"],"maxCost":"0"}\n' \
  "$B_SUBJECT" >"$ROOT/observe-grant.json"
step grant-propose delegate -- "$MINI" workspace --action propose --dir "$ROOT/agent-a" \
  --proposal-id observe-b --request "$ROOT/observe-grant.json"
GRANT_ATTEMPT="$ROOT/agent-a/attempts/grant-observe-b"
step grant-submit delegate -- "$MINI" workspace --action submit --dir "$ROOT/agent-a" \
  --intent "$ROOT/agent-a/proposals/observe-b/intent.json" --attempt "$GRANT_ATTEMPT"
step grant-publish delegate -- "$MINI" workspace --action publish-delegation \
  --dir "$ROOT/agent-a" --proposal-id observe-b --attempt "$GRANT_ATTEMPT"
"$MINI" workspace --action import --dir "$ROOT/agent-b" --name a-feed \
  --from-ref "$ROOT/agent-a/proposals/observe-b/recipient-reference.json" >/dev/null
step subscribe-poll poll -- "$MINI" fleet --action poll --dir "$ROOT/agent-b" \
  --account a-feed --topic news --since 0
jq -e --slurpfile p "$OUT/poll-news-0.json" --arg b "$B_SUBJECT" \
  '.subject == $b and .events == $p[0].events' "$OUT/subscribe-poll.json" >/dev/null
# The receiver itself refuses a spend presented with the observe-only grant:
# the plan is released (agent-b may observe), the admission is not.
refuse observe-only-spend transfer -- "$MINI" fleet --action transfer --dir "$ROOT/agent-b" \
  --account a-feed --to "$B_ACCOUNT" --amount 1
grep -q 'capabilityRejected' "$OUT/observe-only-spend.stderr"

# --- Book arithmetic: every fee is a real posting ---------------------------
step read-a read -- "$MINI" workspace --action read --dir "$ROOT/agent-a" --name account
step read-b read -- "$MINI" workspace --action read --dir "$ROOT/agent-b" --name account
EXPECT_A=$((1000 - 7 - 25 - 4 * FEE))
EXPECT_B=$((500 + 7 + 25))
jq -e --arg v "$EXPECT_A" '[.balances[] | select(.[0] == "0") | .[1]] == [$v]' "$OUT/read-a.json" >/dev/null
jq -e --arg v "$EXPECT_B" '[.balances[] | select(.[0] == "0") | .[1]] == [$v]' "$OUT/read-b.json" >/dev/null

# --- refusal poles --------------------------------------------------------
# Overdraw: amount + fee exceeds the paying account's balance.
refuse overdraw transfer -- "$MINI" fleet --action transfer --dir "$ROOT/agent-b" \
  --account account --to "$A_ACCOUNT" --amount 100000
# Names confer nothing: agent-b names agent-a's account and grant, but holds neither.
"$MINI" workspace --action import --dir "$ROOT/agent-b" --name borrowed --kind account \
  --target "$A_ACCOUNT" --observe-capability "$(jq -er .spendCapability "$OUT/join-a.record.json")" \
  >/dev/null
refuse foreign-spend transfer -- "$MINI" fleet --action transfer --dir "$ROOT/agent-b" \
  --account borrowed --to "$B_ACCOUNT" --amount 1
refuse foreign-poll poll -- "$MINI" fleet --action poll --dir "$ROOT/agent-b" \
  --account borrowed --topic news --since 0
# An unknown transaction id is absent, never a guess.
refuse receipt-absent receipt -- "$MINI" fleet --action receipt --dir "$ROOT/agent-a" \
  --transaction 1

# --- cold restart: the journal re-admits every fleet turn ------------------
stop_server
t0=$(now)
nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$FIX/public/serve-restart.log" 2>&1 </dev/null &
SERVER_PID=$!
i=0
while [ ! -S "$SOCKET" ] && [ "$i" -lt 1200 ]; do
  kill -0 "$SERVER_PID" 2>/dev/null || { echo 'restarted Mini server exited' >&2; exit 1; }
  i=$((i + 1)); sleep 0.1
done
printf 'restart\tserve\t%s\tok\n' "$(elapsed "$t0" "$(now)")" >>"$TIMES"
step poll-after-restart poll -- "$MINI" fleet --action poll --dir "$ROOT/agent-a" \
  --account account --topic news --since 0
jq -e --slurpfile p "$OUT/poll-news-0.json" '.events == $p[0].events' \
  "$OUT/poll-after-restart.json" >/dev/null
step receipt-after-restart receipt -- "$MINI" fleet --action receipt --dir "$ROOT/agent-a" \
  --transaction "$TRANSFER_TX"
jq -e --slurpfile t "$OUT/transfer.json" '.receipt == $t[0].receipt' \
  "$OUT/receipt-after-restart.json" >/dev/null
stop_server

sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$CONFIG" >"$OUT/binaries.sha256"
jq -n --arg a "$A_ACCOUNT" --arg b "$B_ACCOUNT" --arg fee "$FEE" \
  --arg ea "$EXPECT_A" --arg eb "$EXPECT_B" \
  '{type:"minidregg-fleet-journey-v1", agentAccount:$a, serviceAccount:$b, fee:$fee,
    expectedBalances:{agent:$ea, service:$eb}, result:"pass"}' >"$OUT/summary.json"
printf '%s\n' "$OUT"
