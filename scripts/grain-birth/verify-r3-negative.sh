#!/bin/sh
# Recheck a retained failed worker-bare submission without repeating its writes.
set -eu
HOST=$1
EVIDENCE=$2
MINI=${MINI:?set the source-matched Mini executable}
CONFIG="$EVIDENCE/deployment/pinned-config.json"
SOCKET="$EVIDENCE/negative-post.sock"
SERVICE_PID=
cleanup() {
  if [ -n "$SERVICE_PID" ]; then
    kill "$SERVICE_PID" 2>/dev/null || :
    wait "$SERVICE_PID" 2>/dev/null || :
  fi
}
trap cleanup EXIT HUP INT TERM

jq -e '.type == "confirmed" and .confirmation == "installed" and
  .acceptedCount == "11"' "$EVIDENCE/grain-birth-attempt/outcome.json" >/dev/null
jq -e '.type == "confirmed" and .confirmation == "installed" and
  .acceptedCount == "12"' "$EVIDENCE/owner-bare-attempt/outcome.json" >/dev/null
test -s "$EVIDENCE/worker-bare-attempt/plan.bin"
test -s "$EVIDENCE/worker-bare-attempt/call.bin"
jq -e '.type == "refused" and .phase == "61646d697373696f6e" and
  .detail == "726571756573742072656675736564"' \
  "$EVIDENCE/worker-bare-attempt/outcome.json" >/dev/null

"$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$EVIDENCE/negative-post-serve.stdout" \
  2>"$EVIDENCE/negative-post-serve.stderr" &
SERVICE_PID=$!
tick=0
until [ -S "$SOCKET" ]; do
  kill -0 "$SERVICE_PID" 2>/dev/null || exit 1
  tick=$((tick + 1)); [ "$tick" -lt 120 ] || exit 1
  sleep 1
done

jq -n '{subject:"7",nonce:"42010",
  purpose:{type:"query",kind:"object",target:"8303",view:"resource"},
  grants:[{kind:"object",target:"8303",capability:"103"}]}' \
  >"$EVIDENCE/negative-post-intent.json"
"$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/negative-post-intent.json" \
  --key "$EVIDENCE/controller.key" --view resource \
  --dir "$EVIDENCE/negative-post" >"$EVIDENCE/negative-post.stdout"
jq -e --slurpfile before "$EVIDENCE/owner-bare-content/challenge.json" \
  '.worldRoot == $before[0].worldRoot' \
  "$EVIDENCE/negative-post/challenge.json" >/dev/null
jq -e '.cell.document == "8303" and .cell.entries == []' \
  "$EVIDENCE/negative-post/view.json" >/dev/null
echo "retained worker bare refusal and unchanged signed image PASS"
