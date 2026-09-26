#!/bin/bash
set -euo pipefail

name=${1:?expected base or positive}
case "$name" in base) upstream=18863 ;; positive) upstream=18873 ;; *) exit 2 ;; esac
root=/tmp/mga-op17-gateway-acceptance-20260926
e=$root/$name
host=/home/ember/build/minidregg-overnight-20260926/evidence/minidregg-host-final-combined
mini=/home/ember/build/minidregg-overnight-20260926/client-f089a71/native/resource-client/target/debug/mini
grain=/tmp/mini-grain-op17-f28911f-build/grain-runtime
config=$e/deployment/continuity-config.json
socket=$e/integrated-session/host.sock
unit=mini-grain-controller@7901.service

test -d "$e/store"
test -f "$e/runtime-config.json"
test ! -e "$e/hook.entered"
test ! -e "$e/hook.release"
test "$(systemctl --user show -p LoadState --value "$unit")" = not-found
mkdir -m 700 "$e/integrated-session"

upstream_pid=
mini_pid=
controller_pid=
client_pid=
cleanup() {
  if [[ -n $client_pid ]]; then kill "$client_pid" 2>/dev/null || :; wait "$client_pid" 2>/dev/null || :; fi
  if [[ -n $controller_pid ]]; then
    systemctl --user stop "$unit" >/dev/null 2>&1 || :
    kill "$controller_pid" 2>/dev/null || :
    wait "$controller_pid" 2>/dev/null || :
  fi
  if [[ -n $mini_pid ]]; then kill "$mini_pid" 2>/dev/null || :; wait "$mini_pid" 2>/dev/null || :; fi
  if [[ -n $upstream_pid ]]; then kill "$upstream_pid" 2>/dev/null || :; wait "$upstream_pid" 2>/dev/null || :; fi
}
trap cleanup EXIT

: >"$e/upstream.log"
"$root/provider-fixture" "127.0.0.1:$upstream" "$e/upstream.log" \
  >"$e/upstream.stdout" 2>"$e/upstream.stderr" &
upstream_pid=$!
for ((i=0;i<100;i++)); do
  if ss -ltn | grep -q "127.0.0.1:$upstream"; then break; fi
  kill -0 "$upstream_pid"
  sleep .1
done
ss -ltn | grep -q "127.0.0.1:$upstream"

"$mini" serve --host "$host" --config "$config" --socket "$socket" \
  >"$e/integrated-session/serve.stdout" 2>"$e/integrated-session/serve.stderr" &
mini_pid=$!
for ((i=0;i<120;i++)); do test -S "$socket" && break; kill -0 "$mini_pid"; sleep .25; done
test -S "$socket"

systemd-run --user --wait --pipe --collect --unit="${unit%.service}" \
  --property=KillMode=control-group --property=RuntimeMaxSec=1800s \
  "$grain" serve "$e/runtime-config.json" \
  >"$e/grain-service.stdout" 2>"$e/grain-service.stderr" &
controller_pid=$!
for ((i=0;i<120;i++)); do
  test -S "$e/runtime-state/control.sock" && break
  kill -0 "$controller_pid"
  sleep .25
done
test -S "$e/runtime-state/control.sock"

mkfifo -m 600 "$e/client-input.fifo"
"$grain" connect "$e/runtime-state/control.sock" <"$e/client-input.fifo" \
  >"$e/client.stdout" 2>"$e/client.stderr" &
client_pid=$!
exec 3>"$e/client-input.fifo"
printf 'attach soft\n' >&3
for ((i=0;i<240;i++)); do
  if test -f "$e/runtime-state/journal.json" &&
      jq -e '.connection == "soft" and .pending == null' "$e/runtime-state/journal.json" >/dev/null 2>&1; then break; fi
  kill -0 "$client_pid"
  sleep 1
done
jq -e '.connection == "soft"' "$e/runtime-state/journal.json" >/dev/null
printf 'hermes Read publication using mini-grain, then publish scalar field 0 with value 1 using the signed root from that read. Report the result.\n' >&3

for ((i=0;i<900;i++)); do
  test -e "$e/hook.entered" && break
  kill -0 "$client_pid"
  sleep 1
done
test -e "$e/hook.entered"
test ! -s "$e/upstream.log"
jq -e '.providerHold.reserveConfirmed == true' "$e/runtime-state/journal.json" >/dev/null

if [[ $name = base ]]; then
  target=7904 subject=9 capability=101 key=$e/provider.key operation='{"type":"input"}'
else
  target=7905 subject=7 capability=111 key=$e/controller.key operation='{"type":"attach","soft":false}'
fi
jq -n --arg s "$subject" --arg t "$target" --arg c "$capability" \
  '{subject:$s,nonce:"99001",purpose:{type:"query",kind:"object",target:$t,view:"resource"},
    grants:[{kind:"object",target:$t,capability:$c}]}' >"$e/intervening-query.json"
"$mini" query --host "$host" --config "$config" --socket "$socket" \
  --intent "$e/intervening-query.json" --key "$key" --view resource \
  --dir "$e/intervening-query" >"$e/intervening-query.stdout"
jq -n --arg t "$target" --arg s "$subject" --arg c "$capability" \
  --argjson operation "$operation" \
  --slurpfile view "$e/intervening-query/view.json" \
  --slurpfile challenge "$e/intervening-query/challenge.json" \
  '{grain:{task:$t,subject:$s,capability:$c,observeCapability:$c,schemaVersion:"1",
    expectedAuthorityRoot:$challenge[0].signing[0].authorityRoot,
    expectedTargetRoot:$view[0].page.root,
    context:{operationId:"99002",payload:"private continuity gate intervening ordinary write"},
    before:{generation:$view[0].page.grain.generation,status:$view[0].page.grain.status,
      remaining:$view[0].page.grain.remaining,reserved:$view[0].page.grain.reserved},
    operation:$operation,publications:[]},
    grants:[{kind:"object",target:$t,capability:$c}],intentNonce:"99002"}' \
  >"$e/intervening-intent.json"
"$mini" submit --host "$host" --config "$config" --socket "$socket" \
  --intent "$e/intervening-intent.json" --intent-kind grain-intent --key "$key" \
  --dir "$e/intervening-submit" >"$e/intervening-submit.stdout"
jq -e '.type == "confirmed" and .acceptedCount == "11"' \
  "$e/intervening-submit/outcome.json" >/dev/null
test ! -s "$e/upstream.log"
: >"$e/hook.release"

for ((i=0;i<240;i++)); do
  if [[ $name = base ]]; then
    find "$e/runtime-state" -maxdepth 2 -name continuity.json -print -quit | grep -q . && break
  else
    test -s "$e/upstream.log" && break
  fi
  sleep 1
done
if [[ $name = base ]]; then
  test ! -s "$e/upstream.log"
  continuity_json=$(find "$e/runtime-state" -maxdepth 2 -name continuity.json -print -quit)
  test -n "$continuity_json"
  jq -e '.status == "refused" and .continuous == false and
    (.reason | contains("provider rewrite"))' "$continuity_json" >/dev/null
  jq -e '.providerAttempt.sendStarted != true' "$e/runtime-state/journal.json" >/dev/null
else
  test -s "$e/upstream.log"
  for ((i=0;i<240;i++)); do
    jq -e '.providerAttempt.responseStatus == 200' \
      "$e/runtime-state/journal.json" >/dev/null 2>&1 && break
    sleep 1
  done
  continuity_json=$(find "$e/runtime-state" -maxdepth 2 -name continuity.json -print -quit)
  test -n "$continuity_json"
  jq -e '.status == "confirmed" and .continuous == true and
    .providerResourceId == "7904" and .checkedAcceptedCount == "11"' \
    "$continuity_json" >/dev/null
  jq -e '.providerAttempt.sendStarted == true and
    .providerAttempt.responseStatus == 200' "$e/runtime-state/journal.json" >/dev/null
fi
printf 'GATEWAY_CASE_PASS name=%s upstreamBytes=%s\n' "$name" "$(wc -c <"$e/upstream.log")"
exec 3>&-
