#!/bin/sh
# Resume one already prepared event-22 ingress after a read-only fee inspector.
# A submit marker is the one-shot boundary; a failed submit must use lookup.
set -eu
umask 077

if [ "$#" -ne 5 ]; then
  echo "usage: $0 EXISTING_RUN MINI STORE_BINARY SOURCE_FEE_FILE NEW_CONTINUATION_DIR" >&2
  exit 2
fi
RUN=$1 MINI=$2 STORE_BINARY=$3 FEE_FILE=$4 CONT=$5
ISSUE="$RUN/issue"
PIN="$ISSUE/pin.json"
for path in "$RUN" "$MINI" "$STORE_BINARY" "$FEE_FILE" "$CONT"; do
  case "$path" in /*) ;; *) echo "all paths must be absolute" >&2; exit 2 ;; esac
done
[ -d "$RUN" ] && [ -x "$MINI" ] && [ -x "$STORE_BINARY" ] &&
  [ -f "$FEE_FILE" ] && [ ! -e "$CONT" ] || exit 2
command -v jq >/dev/null
command -v sha256sum >/dev/null
HOST=$(jq -er '.host' "$PIN")
CONFIG=$(jq -er '.config' "$PIN")
KEY="$RUN/base/workroom/tool.key"
STORE="$RUN/base/workroom/store"
case "$HOST:$CONFIG" in /*:/*) ;; *) exit 2 ;; esac
[ -x "$HOST" ] && [ -f "$CONFIG" ] && [ -f "$KEY" ] && [ -d "$STORE" ] || exit 2
[ "$(sha256sum "$HOST" | cut -d ' ' -f 1)" = "$(jq -er '.hostSha256' "$PIN")" ]
[ "$(sha256sum "$CONFIG" | cut -d ' ' -f 1)" = "$(jq -er '.configSha256' "$PIN")" ]
[ "$(sha256sum "$ISSUE/ingress.bin" | cut -d ' ' -f 1)" = "$(jq -er '.ingressSha256' "$PIN")" ]
[ "$(sha256sum "$ISSUE/plan.bin" | cut -d ' ' -f 1)" = "$(jq -er '.planSha256' "$PIN")" ]
[ ! -e "$ISSUE/submit-marker.json" ] && [ ! -e "$ISSUE/submit.outcome.json" ] || {
  echo "prepared ingress already crossed submit boundary" >&2; exit 2;
}
FEE=$(cat "$FEE_FILE")
case "$FEE" in ''|0*|*[!0-9]*) echo "invalid source-decoded fee" >&2; exit 2 ;; esac

mkdir -m 700 "$CONT"
sha256sum "$0" "$MINI" "$STORE_BINARY" "$HOST" "$CONFIG" "$PIN" \
  "$ISSUE/request.bin" "$ISSUE/plan.bin" "$ISSUE/ingress.bin" "$FEE_FILE" \
  >"$CONT/input-sha256.txt"
printf '%s\n' "$FEE" >"$CONT/signed-birth-fee.txt"
SERVICE_PID=
stop_service() {
  if [ -n "$SERVICE_PID" ]; then
    kill "$SERVICE_PID" 2>/dev/null || :
    wait "$SERVICE_PID" 2>/dev/null || :
    SERVICE_PID=
  fi
}
trap stop_service EXIT
trap 'exit 143' HUP INT TERM
start_service() {
  mode=$1 name=$2
  mkdir -m 700 "$CONT/$name"
  SOCKET="$CONT/$name/mini.sock"
  "$MINI" "$mode" --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$CONT/$name/stdout" 2>"$CONT/$name/stderr" &
  SERVICE_PID=$!
  tick=0
  until [ -S "$SOCKET" ]; do
    kill -0 "$SERVICE_PID" 2>/dev/null || exit 1
    tick=$((tick + 1)); [ "$tick" -lt 120 ] || exit 1
    sleep 1
  done
}
query_payer() {
  label=$1 nonce=$2
  jq -n --arg nonce "$nonce" \
    '{subject:"8",nonce:$nonce,purpose:{type:"query",kind:"account",
      target:"8",view:"resource"},
      grants:[{kind:"account",target:"8",capability:"42"}]}' \
    >"$CONT/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$CONT/$label-intent.json" --key "$KEY" --view resource \
    --dir "$CONT/$label" >"$CONT/$label.stdout"
  jq -er '[.balances[] | select(.[0] == "0")][0][1]' \
    "$CONT/$label/view.json" >"$CONT/$label-balance.txt"
}

# Public signed read is a separate route from the owner-private submit.
start_service serve public-before
query_payer payer-before 86000
"$STORE_BINARY" read-to "$STORE" "$CONT/before-issue-image.bin"
stop_service

start_service serve-operator operator-submit
# This is deliberately the only op54 invocation in the continuation.
"$MINI" grain-share-issue-submit --socket "$SOCKET" --attempt "$ISSUE" \
  >"$CONT/submit.stdout"
jq -e '.type == "confirmed" and .confirmation == "installed"' \
  "$ISSUE/submit.outcome.json" >/dev/null
stop_service

start_service serve public-after
query_payer payer-after 86001
before=$(cat "$CONT/payer-before-balance.txt")
after=$(cat "$CONT/payer-after-balance.txt")
actual=$((before - after))
[ "$actual" -gt 0 ]
printf '%s\n' "$actual" >"$CONT/actual-book-debit.txt"
cmp "$CONT/signed-birth-fee.txt" "$CONT/actual-book-debit.txt"
jq -n '{subject:"8",nonce:"85100",purpose:{type:"query",kind:"object",
    target:"8500",view:"resource"},
    grants:[{kind:"object",target:"8500",capability:"171"}]}' \
  >"$CONT/ticket-read-intent.json"
"$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$CONT/ticket-read-intent.json" --key "$KEY" --view resource \
  --dir "$CONT/ticket-read" >"$CONT/ticket-read.stdout"
jq -e '.cell.document == "8500" and (.cell.entries | length) == 1' \
  "$CONT/ticket-read/view.json" >/dev/null
"$STORE_BINARY" read-to "$STORE" "$CONT/before-lookup-image.bin"
stop_service

# Lookup runs after a second service open, from the original retained ingress.
start_service serve-operator operator-lookup
"$MINI" grain-share-issue-lookup --socket "$SOCKET" --attempt "$ISSUE" \
  >"$CONT/lookup.stdout"
jq -e '.type == "confirmed" and .confirmation == "replayed"' \
  "$ISSUE/lookup-0000.outcome.json" >/dev/null
jq -S '{transactionId,eventId,acceptedCount,worldRoot}' \
  "$ISSUE/submit.outcome.json" >"$CONT/original-receipt.json"
jq -S '{transactionId,eventId,acceptedCount,worldRoot}' \
  "$ISSUE/lookup-0000.outcome.json" >"$CONT/recovered-receipt.json"
cmp "$CONT/original-receipt.json" "$CONT/recovered-receipt.json"
"$STORE_BINARY" read-to "$STORE" "$CONT/after-lookup-image.bin"
cmp "$CONT/before-lookup-image.bin" "$CONT/after-lookup-image.bin"
stop_service
sha256sum -c "$CONT/input-sha256.txt" >"$CONT/input-recheck.txt"
echo "prepared event-22 ingress accepted once and reopened receipt preserved"
