#!/bin/sh
# Signed Mini provider-witness gate. Uses the source-authored bootstrap above.
set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: $0 MINIDREGG_HOST NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
HOST=$1
EVIDENCE=$2
MINI=${MINI:-"$HERE/../../native/resource-client/target/debug/mini"}
PROVIDER_BOOTSTRAP=1 BOOTSTRAP_ONLY=1 \
  "$HERE/acceptance.sh" "$HOST" "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
CONFIG="$EVIDENCE/deployment/pinned-config.json"
mkdir -m 700 "$EVIDENCE/provider-session"
SOCKET="$EVIDENCE/provider-session/host.sock"
"$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$EVIDENCE/provider-session.stdout" 2>"$EVIDENCE/provider-session.stderr" &
SERVICE_PID=$!
cleanup() { kill "$SERVICE_PID" 2>/dev/null || :; wait "$SERVICE_PID" 2>/dev/null || :; }
trap cleanup EXIT HUP INT TERM
tick=0
until [ -S "$SOCKET" ]; do
  kill -0 "$SERVICE_PID" 2>/dev/null || { echo "Mini session exited" >&2; exit 1; }
  tick=$((tick + 1))
  [ "$tick" -lt 120 ] || { echo "Mini session socket timeout" >&2; exit 1; }
  sleep 1
done

confirmed() {
  jq -e '.type == "confirmed" and .confirmation == "installed"' "$1" >/dev/null
}
query_task() (
  name=$1 subject=$2 task=$3 capability=$4 key=$5 nonce=$6
  jq -n --arg s "$subject" --arg t "$task" --arg c "$capability" --arg n "$nonce" \
    '{subject:$s,nonce:$n,purpose:{type:"query",kind:"object",target:$t,view:"resource"},
      grants:[{kind:"object",target:$t,capability:$c}]}' >"$EVIDENCE/$name-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-intent.json" --key "$key" --view resource \
    --dir "$EVIDENCE/$name" >"$EVIDENCE/$name.stdout"
)
grain_intent() {
  name=$1 task=$2 subject=$3 capability=$4 nonce=$5 operation=$6 primary=$7
  jq -n --arg t "$task" --arg s "$subject" --arg c "$capability" \
    --arg n "$nonce" --arg label "$name" --argjson op "$operation" \
    --slurpfile source "$EVIDENCE/$primary/view.json" \
    --slurpfile challenge "$EVIDENCE/$primary/challenge.json" \
    '{grain:{task:$t,subject:$s,capability:$c,observeCapability:$c,
      schemaVersion:"1",expectedAuthorityRoot:$challenge[0].signing[0].authorityRoot,
      expectedTargetRoot:$source[0].page.root,
      context:{operationId:$n,payload:$label},
      before:{generation:$source[0].page.grain.generation,
        status:$source[0].page.grain.status,
        remaining:$source[0].page.grain.remaining,
        reserved:$source[0].page.grain.reserved},
      operation:$op,publications:[]},
      grants:[{kind:"object",target:$t,capability:$c}],intentNonce:$n}' \
    >"$EVIDENCE/$name-intent.json"
}
with_parent_witness() {
  name=$1 parent=$2
  jq --slurpfile parent "$EVIDENCE/$parent/view.json" \
    '.grain.parentWitness = {task:"7001",capability:"75",observeCapability:"75",
      expectedTargetRoot:$parent[0].page.root,
      before:{generation:$parent[0].page.grain.generation,
        status:$parent[0].page.grain.status,
        remaining:$parent[0].page.grain.remaining,
        reserved:$parent[0].page.grain.reserved}} |
      .grants += [{kind:"object",target:"7001",capability:"75"}]' \
    "$EVIDENCE/$name-intent.json" >"$EVIDENCE/$name-witness-intent.json"
  mv "$EVIDENCE/$name-witness-intent.json" "$EVIDENCE/$name-intent.json"
}
submit() {
  name=$1 key=$2
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-intent.json" --intent-kind grain-intent \
    --key "$EVIDENCE/$key.key" --dir "$EVIDENCE/$name-attempt" \
    >"$EVIDENCE/$name.stdout"
  confirmed "$EVIDENCE/$name-attempt/outcome.json"
}

query_task parent-initial 7 7001 71 "$EVIDENCE/controller.key" 40001
grain_intent parent-attach 7001 7 71 40002 '{"type":"attach","soft":false}' parent-initial
submit parent-attach controller
query_task provider-initial 9 7004 101 "$EVIDENCE/provider.key" 40003
grain_intent provider-attach 7004 9 101 40004 '{"type":"attach","soft":false}' provider-initial
submit provider-attach provider
query_task parent-running 7 7001 71 "$EVIDENCE/controller.key" 40005
grain_intent parent-reserve 7001 7 71 40006 '{"type":"reserve","amount":"3"}' parent-running
submit parent-reserve controller
query_task parent-pending 7 7001 71 "$EVIDENCE/controller.key" 40007
query_task provider-running 9 7004 101 "$EVIDENCE/provider.key" 40008
jq -e '.page.grain.generation == "1" and .page.grain.status == "3" and
  .page.grain.reserved == "3"' "$EVIDENCE/parent-pending/view.json" >/dev/null
grain_intent provider-overbudget 7004 9 101 40009 \
  '{"type":"reserve","amount":"51"}' provider-running
with_parent_witness provider-overbudget parent-pending
if "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/provider-overbudget-intent.json" --intent-kind grain-intent \
    --key "$EVIDENCE/provider.key" --dir "$EVIDENCE/provider-overbudget-attempt" \
    >"$EVIDENCE/provider-overbudget.stdout" \
    2>"$EVIDENCE/provider-overbudget.stderr"; then
  echo "overbudget provider reserve unexpectedly accepted" >&2
  exit 1
fi
jq -e '.type == "refused"' "$EVIDENCE/provider-overbudget-attempt/outcome.json" >/dev/null
query_task provider-after-refusal 9 7004 101 "$EVIDENCE/provider.key" 40010
test "$(jq -er '.page.root' "$EVIDENCE/provider-after-refusal/view.json")" = \
  "$(jq -er '.page.root' "$EVIDENCE/provider-running/view.json")"
query_task parent-after-refusal 7 7001 71 "$EVIDENCE/controller.key" 40011
test "$(jq -er '.page.root' "$EVIDENCE/parent-after-refusal/view.json")" = \
  "$(jq -er '.page.root' "$EVIDENCE/parent-pending/view.json")"

grain_intent provider-reserve 7004 9 101 40012 \
  '{"type":"reserve","amount":"3"}' provider-after-refusal
with_parent_witness provider-reserve parent-after-refusal
submit provider-reserve provider
query_task provider-pending 9 7004 101 "$EVIDENCE/provider.key" 40013
jq -e '.page.grain.generation == "1" and .page.grain.status == "3" and
  .page.grain.reserved == "3"' "$EVIDENCE/provider-pending/view.json" >/dev/null
query_task parent-after-provider 7 7001 71 "$EVIDENCE/controller.key" 40014
test "$(jq -er '.page.root' "$EVIDENCE/parent-after-provider/view.json")" = \
  "$(jq -er '.page.root' "$EVIDENCE/parent-pending/view.json")"

grain_intent provider-stale 7004 9 101 40015 '{"type":"input"}' provider-pending
with_parent_witness provider-stale parent-after-provider
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/provider-stale-intent.json" --intent-kind grain-intent \
  --key "$EVIDENCE/provider.key" --prepare-only true \
  --dir "$EVIDENCE/provider-stale-attempt" >"$EVIDENCE/provider-stale.stdout"
test -s "$EVIDENCE/provider-stale-attempt/call.bin"
grain_intent parent-hard-trip 7001 7 71 40016 '{"type":"disconnect"}' parent-after-provider
submit parent-hard-trip controller
query_task parent-fenced 7 7001 71 "$EVIDENCE/controller.key" 40017
jq -e '.page.grain.generation == "2" and .page.grain.status == "5" and
  .page.grain.reserved == "3"' "$EVIDENCE/parent-fenced/view.json" >/dev/null
if "$MINI" retry --attempt "$EVIDENCE/provider-stale-attempt" --socket "$SOCKET" \
    --mode submit >"$EVIDENCE/provider-stale-retry.stdout" \
    2>"$EVIDENCE/provider-stale-retry.stderr"; then
  echo "stale provider witness unexpectedly accepted" >&2
  exit 1
fi
jq -e '.type == "refused"' "$EVIDENCE/provider-stale-attempt/retry-0001.json" >/dev/null
test "$(jq -er '.page.root' "$EVIDENCE/parent-fenced/view.json")" != \
  "$(jq -er '.page.root' "$EVIDENCE/parent-after-provider/view.json")"
query_task provider-after-fence 9 7004 101 "$EVIDENCE/provider.key" 40018
test "$(jq -er '.page.root' "$EVIDENCE/provider-after-fence/view.json")" = \
  "$(jq -er '.page.root' "$EVIDENCE/provider-pending/view.json")"
printf 'signed provider joint reserve and refusal gates passed: %s\n' "$EVIDENCE"
