#!/usr/bin/env bash
# JROTL (K-PREROTATE x the receiver collapse, 66967962): a rotation through the
# generic Receiver whose REPLY IS LOST, and one the Host NEVER SAW.
#
# Two fresh pre-rotated subjects. Their workspaces talk to the journey's Host
# through a recording proxy (journey.d/lib/hostraw.py proxy) that, once:
#   F: forwards op 142 (KEY_ROTATION_SUBMIT), lets the Host decide, and closes
#      the client's connection without the reply (a lost reply). The client's
#      custody falls back to op 143 (KEY_ROTATION_LOOKUP) and must find the
#      rotation confirmed (replayed), exactly once: key epoch 2, not 3.
#   G: drops op 142 without forwarding (the Host never sees it). The client's
#      op 143 lookup must say absent; a retry looks up again and never
#      resubmits (no second op 142 reaches the proxy); the key epoch stays 1.
# Every verdict is read from an artifact: the proxy's per-exchange log and the
# Host's own decoding (`inspect outcome`) of each kept reply.
#
# Hook contract: journey.sh exports MINI HOST CONFIG SOCKET SPONSOR_WS JOURNEY_STEP_DIR.
set -u
umask 077
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
. "$HERE/lib/shortdir.sh"
journey_shortdir jrotl
D=$JOURNEY_STEP_DIR/jrotl
mkdir -p -m 700 "$D" "$D/offline" "$JOURNEY_D"
T=$D/jrotl.tsv; : >"$T"
N=0; BAD=0
PIDS=""
stop_proxies() { for p in $PIDS; do kill "$p" 2>/dev/null; wait "$p" 2>/dev/null; done; PIDS=""; }
trap 'stop_proxies; journey_shortdir_return' EXIT
run() {
  local name=$1; shift
  { printf '%q ' "$@"; echo; } >"$D/$name.cmd"
  timeout 600 "$@" >"$D/$name.out" 2>"$D/$name.err"
  echo $? >"$D/$name.rc"
  return "$(cat "$D/$name.rc")"
}
row() {
  N=$((N + 1))
  if [ "$4" = 1 ]; then printf 'PASS\t%s\t%s\t%s\n' "$1" "$2" "$3" >>"$T"
  else printf 'FAIL\t%s\t%s\t%s\n' "$1" "$2" "$3" >>"$T"; BAD=$((BAD + 1)); fi
}
die() { echo "$T"; echo "JROTL: $*" >&2; exit 1; }
decode() {  # decode REPLY.bin NAME -> $D/NAME.json (the Host's decoding of the outcome)
  tail -c +2 "$1" >"$D/$2.outcome.bin"
  "$HOST" "$CONFIG" inspect outcome "$D/$2.outcome.bin" "$D/$2.json" >"$D/$2.inspect.out" 2>&1
}
proxy() {  # proxy NAME MODE : a one-shot op-142 proxy at $JOURNEY_D/NAME.sock, log $D/NAME.log
  python3 "$HERE/lib/hostraw.py" proxy "$JOURNEY_D/$1.sock" "$SOCKET" 142 1 "$2" "$D/$1.log" \
    >"$D/$1.proxy.out" 2>"$D/$1.proxy.err" &
  PIDS="$PIDS $!"
  for i in $(seq 1 100); do [ -S "$JOURNEY_D/$1.sock" ] && return 0; sleep 0.05; done
  die "proxy $1 did not bind"
}
subject() {  # subject NAME PROXYSOCK : enroll a pre-rotated subject; workspace $D/NAME-ws through the proxy
  local n=$1
  "$MINI" keygen --secret "$D/$n.key" --public "$D/$n.pub" --next-to "$D/offline/$n.next" \
    >"$D/$n-keygen.out" 2>"$D/$n-keygen.err" || die "$n keygen: $(tail -1 "$D/$n-keygen.err")"
  run "$n-plan" "$MINI" enroll --action plan --sponsor-workspace "$SPONSOR_WS" --factory-ref factory \
    --name "jrotl-$n" --new-key "$D/$n.key" --dir "$D/enroll-$n" || die "$n plan: $(tail -1 "$D/$n-plan.err")"
  run "$n-seal" "$MINI" enroll --action seal --dir "$D/enroll-$n" || die "$n seal"
  run "$n-submit" "$MINI" enroll --action submit --dir "$D/enroll-$n" || die "$n submit: $(tail -1 "$D/$n-submit.err")"
  run "$n-init" "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$2" \
    --enrollment "$D/enroll-$n/enrollment.json" --dir "$D/$n-ws" || die "$n init: $(tail -1 "$D/$n-init.err")"
}
epoch() { "$MINI" key-status --workspace "$D/$1-ws" 2>"$D/$1-status.err" | tee "$D/$1-status.json" | jq -r .keyEpoch 2>/dev/null; }
# The proxy log's op-142 and op-143 exchanges: "n op first-byte disposition".
ops() { awk -F '\t' -v o="$2" '$2 == o' "$D/$1.log" 2>/dev/null; }

# ------------------------------------------------ F: the reply of op 142 is lost
proxy f lose-reply
subject f "$JOURNEY_D/f.sock"
row "F enrolled pre-rotated through the proxy, epoch 1" "1" "$(epoch f)" "$([ "$(epoch f)" = 1 ] && echo 1 || echo 0)"
run frot "$MINI" rotate-key --workspace "$D/f-ws" --next-key "$D/offline/f.next"
lost=$(ops f 142 | head -1)
row "the Host decided op 142 and its reply was lost on the way back" "one op-142 exchange, Host reply byte 142, reply-lost" \
  "${lost:-none}" "$(echo "$lost" | awk -F '\t' '$3 == 142 && $4 == "reply-lost" {ok=1} END {print ok+0}')"
n142=$(echo "$lost" | cut -f1)
decode "$D/f.log.$n142-op142.bin" f-lost
row "the lost reply was a confirmation (decoded by the Host)" "confirmed installed" \
  "$(jq -r '"\(.type) \(.confirmation)"' "$D/f-lost.json" 2>/dev/null)" \
  "$(jq -e '.type == "confirmed"' "$D/f-lost.json" >/dev/null 2>&1 && echo 1 || echo 0)"
look=$(ops f 143 | head -1); n143=$(echo "$look" | cut -f1)
[ -n "$n143" ] && decode "$D/f.log.$n143-op143.bin" f-lookup
row "the client recovered by op 143 lookup, which found the rotation confirmed (replayed)" \
  "op 143 forwarded, confirmed replayed; rotate-key exit 0" \
  "lookup=${look:-none}; $(jq -r '"\(.type) \(.confirmation)"' "$D/f-lookup.json" 2>/dev/null); rc=$(cat "$D/frot.rc")" \
  "$([ "$(cat "$D/frot.rc")" = 0 ] && jq -e '.type == "confirmed" and .confirmation == "replayed"' "$D/f-lookup.json" >/dev/null 2>&1 && echo 1 || echo 0)"
row "the lookup's receipt is the lost reply's receipt (same transaction and event)" "equal" \
  "$(jq -c '[.transactionId,.eventId]' "$D/f-lost.json" 2>/dev/null) vs $(jq -c '[.transactionId,.eventId]' "$D/f-lookup.json" 2>/dev/null)" \
  "$([ -n "$(jq -c '[.transactionId,.eventId]' "$D/f-lost.json" 2>/dev/null)" ] && [ "$(jq -c '[.transactionId,.eventId]' "$D/f-lost.json")" = "$(jq -c '[.transactionId,.eventId]' "$D/f-lookup.json")" ] && echo 1 || echo 0)"
row "exactly one rotation happened: epoch 2, and only one op 142 reached the Host" "2; one 142" \
  "epoch $(epoch f); op142 exchanges $(ops f 142 | wc -l)" \
  "$([ "$(epoch f)" = 2 ] && [ "$(ops f 142 | wc -l)" = 1 ] && echo 1 || echo 0)"
run frot-again "$MINI" rotate-key --workspace "$D/f-ws" --next-key "$D/offline/f.next"
row "running rotate-key again on the completed attempt replays its result and sends nothing" \
  "exit 0, replayed true, no new 142/143" \
  "rc=$(cat "$D/frot-again.rc") replayed=$(jq -r .replayed "$D/frot-again.out" 2>/dev/null) op142=$(ops f 142 | wc -l) op143=$(ops f 143 | wc -l)" \
  "$([ "$(cat "$D/frot-again.rc")" = 0 ] && [ "$(jq -r .replayed "$D/frot-again.out" 2>/dev/null)" = true ] && [ "$(ops f 142 | wc -l)" = 1 ] && [ "$(ops f 143 | wc -l)" = 1 ] && echo 1 || echo 0)"

# ------------------------------------------------ G: op 142 never reaches the Host
proxy g never-forward
subject g "$JOURNEY_D/g.sock"
run grot "$MINI" rotate-key --workspace "$D/g-ws" --next-key "$D/offline/g.next"
dropped=$(ops g 142 | head -1)
look=$(ops g 143 | head -1); n143=$(echo "$look" | cut -f1)
[ -n "$n143" ] && decode "$D/g.log.$n143-op143.bin" g-lookup
row "a rotation the Host never saw: op 142 not forwarded; the client's op 143 lookup says absent; rotate-key refuses to claim it" \
  "not-forwarded; absent; exit != 0, remains unconfirmed" \
  "142=${dropped:-none}; lookup $(jq -r .type "$D/g-lookup.json" 2>/dev/null); rc=$(cat "$D/grot.rc") $(grep -m1 -o 'remains unconfirmed' "$D/grot.err")" \
  "$(echo "$dropped" | grep -q not-forwarded && jq -e '.type == "absent"' "$D/g-lookup.json" >/dev/null 2>&1 && [ "$(cat "$D/grot.rc")" != 0 ] && grep -q 'remains unconfirmed' "$D/grot.err" && echo 1 || echo 0)"
run grot-again "$MINI" rotate-key --workspace "$D/g-ws" --next-key "$D/offline/g.next"
row "a retry of the unconfirmed attempt only looks up again: no op 142 is ever sent twice" \
  "op142 exchanges 1 (the dropped one); op143 2; exit != 0" \
  "op142 $(ops g 142 | wc -l) op143 $(ops g 143 | wc -l) rc=$(cat "$D/grot-again.rc")" \
  "$([ "$(ops g 142 | wc -l)" = 1 ] && [ "$(ops g 143 | wc -l)" = 2 ] && [ "$(cat "$D/grot-again.rc")" != 0 ] && echo 1 || echo 0)"
row "G is still at epoch 1: an unconfirmed rotation changed nothing" "1" "$(epoch g)" "$([ "$(epoch g)" = 1 ] && echo 1 || echo 0)"

stop_proxies
echo "$T"
if [ "$BAD" = 0 ]; then
  echo "JROTL: $N/$N checks; a lost op-142 reply recovered by op-143 lookup (epoch 2, one submit); a never-seen rotation looks up absent and is never resubmitted" >&2
  exit 0
fi
echo "JROTL: $BAD of $N checks failed (see $T)" >&2
exit 1
