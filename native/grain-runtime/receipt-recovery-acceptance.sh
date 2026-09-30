#!/bin/sh
# Focused fresh-native lost-MCP-reply -> verified next-prompt receipt journey.
# Linux/systemd only. Run from a private copy of this source tree.
set -eu

if [ "$#" -ne 2 ]; then
  echo 'usage: receipt-recovery-acceptance.sh HOST NEW_EVIDENCE_DIR' >&2
  exit 2
fi
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
HOST=$1 EVIDENCE=$2
MINI=${MINI:-"$REPO/native/resource-client/target/release/mini"}
GRAIN=${GRAIN:-"$HERE/target/release/grain-runtime"}
STORE_BINARY=${STORE_BINARY:-"$REPO/native/hyperdocument-link-sqlite-store/target/release/minidregg-link-sqlite-store"}
SIGNATURE_BINARY=${SIGNATURE_BINARY:-"$REPO/native/credential-signature-verifier/target/release/minidregg-credential-signature-verifier"}
BWRAP=${BWRAP:-"$REPO/deploy/grain-host/bwrap"}
command -v jq >/dev/null 2>&1 || exit 2
command -v systemd-run >/dev/null 2>&1 || exit 2
for binary in "$HOST" "$MINI" "$GRAIN" "$STORE_BINARY" "$SIGNATURE_BINARY" "$BWRAP"; do
  [ -x "$binary" ] || { echo "not executable: $binary" >&2; exit 2; }
done
[ "$(uname -s)" = Linux ] || { echo 'Linux/systemd only' >&2; exit 2; }
HOST=$(realpath "$HOST")
MINI=$(realpath "$MINI")
GRAIN=$(realpath "$GRAIN")
STORE_BINARY=$(realpath "$STORE_BINARY")
SIGNATURE_BINARY=$(realpath "$SIGNATURE_BINARY")
BWRAP=$(realpath "$BWRAP")
[ ! -e "$EVIDENCE" ] || { echo 'evidence directory already exists' >&2; exit 2; }

MINI=$MINI GRAIN=$GRAIN STORE_BINARY=$STORE_BINARY SIGNATURE_BINARY=$SIGNATURE_BINARY \
  BOOTSTRAP_ONLY=1 "$HERE/acceptance.sh" "$HOST" "$EVIDENCE"
EVIDENCE=$(realpath "$EVIDENCE")
CONFIG="$EVIDENCE/deployment/pinned-config.json"
STATE="$EVIDENCE/runtime-state"
SOCKET="$EVIDENCE/session-recovery/host.sock"
CONTROL="$STATE/control.sock"
ADMIN="$STATE/admin.sock"
WORK="$EVIDENCE/worker-work"
RUNTIME_ROOT="$EVIDENCE/worker-runtime"
READY="$WORK/first-ready"
RELEASE="$WORK/first-release"
SECOND="$WORK/second-prompt.json"
UNIT=mini-grain-controller@7001.service
MARKER="mini-grain-recovery:$EVIDENCE"
INVOCATION=
MINI_PID=
GRAIN_PID=
CONNECT_PID=
OBSERVER_PID=
cleanup() {
  if [ -n "$OBSERVER_PID" ]; then kill "$OBSERVER_PID" 2>/dev/null || :; wait "$OBSERVER_PID" 2>/dev/null || :; fi
  if [ -n "$CONNECT_PID" ]; then kill "$CONNECT_PID" 2>/dev/null || :; wait "$CONNECT_PID" 2>/dev/null || :; fi
  if [ -n "$GRAIN_PID" ]; then
    description=$(systemctl --user show -p Description --value "$UNIT" 2>/dev/null || :)
    invocation=$(systemctl --user show -p InvocationID --value "$UNIT" 2>/dev/null || :)
    if [ "$description" = "$MARKER" ] &&
        { [ -z "$INVOCATION" ] || [ "$invocation" = "$INVOCATION" ]; }; then
      systemctl --user stop "$UNIT" >/dev/null 2>&1 || :
    fi
    kill "$GRAIN_PID" 2>/dev/null || :
    wait "$GRAIN_PID" 2>/dev/null || :
  fi
  if [ -n "$MINI_PID" ]; then kill "$MINI_PID" 2>/dev/null || :; wait "$MINI_PID" 2>/dev/null || :; fi
}
trap cleanup EXIT HUP INT TERM

mkdir -m 700 "$STATE" "$EVIDENCE/session-recovery" "$WORK" "$RUNTIME_ROOT"
mkdir -m 700 "$WORK/.hermes"
printf 'timeouts:\n  mcp:\n    tool_call: 1500\n' >"$WORK/.hermes/config.yaml"
chmod 600 "$WORK/.hermes/config.yaml"
cp "$GRAIN" "$RUNTIME_ROOT/grain-runtime"
cp "$HERE/fixture/hermes-acp-recovery" "$RUNTIME_ROOT/hermes-acp"
rustc --edition=2021 -O "$HERE/fixture/broker-drop.rs" -o "$EVIDENCE/broker-drop"
"$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$EVIDENCE/mini-recovery.stdout" 2>"$EVIDENCE/mini-recovery.stderr" &
MINI_PID=$!

wait_socket() {
  socket=$1 pid=$2
  tick=0
  until [ -S "$socket" ]; do
    kill -0 "$pid" 2>/dev/null || { echo "service exited before $socket" >&2; exit 1; }
    tick=$((tick + 1))
    [ "$tick" -lt 120 ] || { echo "socket timeout: $socket" >&2; exit 1; }
    sleep 1
  done
}
wait_journal() {
  expression=$1
  tick=0
  until [ -f "$STATE/journal.json" ] && jq -e "$expression" "$STATE/journal.json" >/dev/null 2>&1; do
    kill -0 "$GRAIN_PID" 2>/dev/null || { echo "controller exited before $expression" >&2; exit 1; }
    tick=$((tick + 1))
    [ "$tick" -lt 1500 ] || { echo "journal timeout: $expression" >&2; exit 1; }
    sleep 1
  done
}
query_publication() {
  label=$1 nonce=$2
  jq -n --arg nonce "$nonce" '{subject:"8",nonce:$nonce,
    purpose:{type:"query",kind:"object",target:"7003",view:"resource"},
    grants:[{kind:"object",target:"7003",capability:"94"}]}' \
    >"$EVIDENCE/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$EVIDENCE/tool.key" \
    --view resource --dir "$EVIDENCE/$label" >"$EVIDENCE/$label.stdout"
}
query_parent() {
  label=$1 nonce=$2
  jq -n --arg nonce "$nonce" '{subject:"7",nonce:$nonce,
    purpose:{type:"query",kind:"object",target:"7001",view:"resource"},
    grants:[{kind:"object",target:"7001",capability:"71"}]}' \
    >"$EVIDENCE/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$EVIDENCE/controller.key" \
    --view resource --dir "$EVIDENCE/$label" >"$EVIDENCE/$label.stdout"
}
wait_socket "$SOCKET" "$MINI_PID"

jq -n --arg mini "$MINI" --arg host "$HOST" --arg cfg "$CONFIG" \
  --arg socket "$SOCKET" --arg key "$EVIDENCE/controller.key" \
  --arg tool "$EVIDENCE/tool.key" --arg state "$STATE" --arg control "$CONTROL" \
  --arg cwd "$EVIDENCE" --arg bwrap "$BWRAP" \
  --arg work "$WORK" --arg runtime "$RUNTIME_ROOT" \
  '{mini:$mini,host:$host,hostConfig:$cfg,hostSocket:$socket,custodyKey:$key,
    stateDir:$state,controlSocket:$control,cwd:$cwd,task:"7001",subject:"7",
    capability:"71",queryCapability:"71",policyControlCapability:"72",
    toolTask:{task:"7002",subject:"8",capability:"81",queryCapability:"81",
      custodyKey:$tool,parentCapability:"73",parentObserveCapability:"73",
      reserve:"2",charge:"1",
      allowedPublications:[{kind:"object",target:"7003",capability:"93",observeCapability:"93"}]},
    commands:[{name:"hermes-acp",program:$bwrap,
      args:["--workspace",$work,"--runtime-root",$runtime,"--network","none",
        "--","/agent/hermes-acp","/workspace/.hermes",
        "/workspace/first-ready","/workspace/first-release",
        "/workspace/second-prompt.json"],
      systemdScope:true,wallTimeSeconds:1500,reserve:"3",charge:"1"}]}' \
  >"$EVIDENCE/runtime-recovery-config.json"

state=$(systemctl --user show -p ActiveState --value "$UNIT" 2>/dev/null || :)
case $state in
  active|activating|deactivating|reloading)
    echo "controller unit already in use: $UNIT ($state)" >&2; exit 1 ;;
esac
systemd-run --user --wait --pipe --collect --unit="${UNIT%.service}" \
  --description="$MARKER" --property=KillMode=control-group \
  --property=RuntimeMaxSec=2400s "$GRAIN" serve "$EVIDENCE/runtime-recovery-config.json" \
  >"$EVIDENCE/grain-recovery.stdout" 2>"$EVIDENCE/grain-recovery.stderr" &
GRAIN_PID=$!
wait_socket "$CONTROL" "$GRAIN_PID"
[ "$(systemctl --user show -p Description --value "$UNIT")" = "$MARKER" ]
INVOCATION=$(systemctl --user show -p InvocationID --value "$UNIT")
[ -n "$INVOCATION" ]

mkfifo "$EVIDENCE/first-input.fifo"
"$GRAIN" connect "$CONTROL" <"$EVIDENCE/first-input.fifo" \
  >"$EVIDENCE/first-connect.stdout" 2>"$EVIDENCE/first-connect.stderr" &
CONNECT_PID=$!
exec 3>"$EVIDENCE/first-input.fifo"
printf 'attach soft\n' >&3
wait_journal '.connection == "soft" and .pending == null'
query_publication before-publish 51001
BEFORE_ROOT=$(jq -er '.cell.root' "$EVIDENCE/before-publish/view.json")
printf 'hermes first\n' >&3
tick=0
until [ -f "$READY" ]; do
  kill -0 "$GRAIN_PID" 2>/dev/null || exit 1
  tick=$((tick + 1))
  [ "$tick" -lt 1500 ] || { echo 'first ACP prompt timeout' >&2; exit 1; }
  sleep 1
done
BROKER=$(find "$STATE" -maxdepth 1 -type s -name 'mcp-*.sock' -print | sort | tail -n 1)
[ -n "$BROKER" ] || { echo 'broker socket absent' >&2; exit 1; }
jq -cn --arg root "$BEFORE_ROOT" '{name:"mini_publish",arguments:{publications:[{
  kind:"object",target:"7003",expectedTargetRoot:$root,
  payload:{type:"scalar",actions:[{type:"create",
    key:{type:"object",resource:"7003",field:"0"},value:"1"}]}}]}}' \
  >"$EVIDENCE/broker-request-line.json"
jq -c . "$EVIDENCE/broker-request-line.json" | tr -d '\n' \
  >"$EVIDENCE/broker-request.json"
jq -e '.name == "mini_publish" and (.arguments.publications | length) == 1' \
  "$EVIDENCE/broker-request.json" >/dev/null
"$EVIDENCE/broker-drop" "$BROKER" "$EVIDENCE/broker-request.json"
wait_journal '(.publicationReceipts | length) == 1 and
  .publicationReceipts[0].targets == ["7003"] and
  .publicationReceipts[0].reported == false and .toolPending == null'
ATTEMPT=$(jq -er '.publicationReceipts[0].attempt' "$STATE/journal.json")
jq -e '.type == "confirmed" and .confirmation == "installed"' \
  "$ATTEMPT/outcome.json" >/dev/null
query_publication after-publish 51002
AFTER_ROOT=$(jq -er '.cell.root' "$EVIDENCE/after-publish/view.json")
[ "$AFTER_ROOT" != "$BEFORE_ROOT" ]
: >"$RELEASE"
wait_journal '.connection == "detached" and .child == null and .pending == null and
  .toolPending == null and .parentHold != null'
FAULT_ID=$(jq -ser '[.[] | select(.grain.task == "7001" and
  (.grain.operation.type == "interrupt" or .grain.operation.type == "cancel"))]
  as $faults | ($faults | length) == 1 and
  $faults[0].grain.operation.type == "interrupt" and
  $faults[0].grain.before == {generation:"1",status:"4",remaining:"97",reserved:"3"}
  | if . then $faults[0].grain.context.operationId else empty end' \
  "$STATE"/source-*.json)
jq -e '.type == "confirmed" and .confirmation == "installed"' \
  "$STATE/attempt-$(printf '%016d' "$FAULT_ID")/outcome.json" >/dev/null
query_parent after-interrupt 52001
jq -e '.cell.grain == {task:"7001",generation:"2",status:"5",
  remaining:"97",reserved:"3"}' "$EVIDENCE/after-interrupt/view.json" >/dev/null
test "$(stat -c %a "$WORK/.hermes/state.db")" = 600
exec 3>&-
wait "$CONNECT_PID" || :
CONNECT_PID=

"$GRAIN" admin "$ADMIN" 'reconcile parent audited' \
  >"$EVIDENCE/reconcile-parent.stdout" 2>"$EVIDENCE/reconcile-parent.stderr"
wait_journal '.parentHold == null'
query_parent after-audited-settle 52002
jq -e '.cell.grain == {task:"7001",generation:"2",status:"0",
  remaining:"99",reserved:"0"}' \
  "$EVIDENCE/after-audited-settle/view.json" >/dev/null
"$GRAIN" admin "$ADMIN" 'reconcile effects' \
  >"$EVIDENCE/reconcile-effects.stdout" 2>"$EVIDENCE/reconcile-effects.stderr"
wait_journal '(.unresolvedExternal | length) == 0'

mkfifo "$EVIDENCE/second-input.fifo"
"$HERE/fixture/observe-mini-retry" "$MINI" "$ATTEMPT" \
  "$EVIDENCE/observed-retry-command.txt" &
OBSERVER_PID=$!
"$GRAIN" connect "$CONTROL" <"$EVIDENCE/second-input.fifo" \
  >"$EVIDENCE/second-connect.stdout" 2>"$EVIDENCE/second-connect.stderr" &
CONNECT_PID=$!
exec 3>"$EVIDENCE/second-input.fifo"
printf 'attach soft\n' >&3
wait_journal '.connection == "soft" and .pending == null'
printf 'recover\nhermes second\n' >&3
wait_journal '.publicationReceipts[0].reported == true and .child == null and
  .pending == null and .connection == "soft"'
jq -e '.hermesSession.id == "recovery-fixture" and
  .hermesSession.loadVerified == true and
  .hermesSession.stateFingerprint != null and
  .hermesSession.retentionIssue == null and
  .hermesSession.pendingPrompt == false' "$STATE/journal.json" >/dev/null
[ -s "$SECOND" ]
wait "$OBSERVER_PID"
OBSERVER_PID=
grep -F -- '--mode lookup' "$EVIDENCE/observed-retry-command.txt" >/dev/null
TRANSACTION=$(jq -er '.publicationReceipts[0].transactionId' "$STATE/journal.json")
EVENT=$(jq -er '.publicationReceipts[0].eventId' "$STATE/journal.json")
ACCEPTED_COUNT=$(jq -er '.publicationReceipts[0].acceptedCount' "$STATE/journal.json")
WORLD_ROOT=$(jq -er '.publicationReceipts[0].worldRoot' "$STATE/journal.json")
jq -e --arg tx "$TRANSACTION" --arg event "$EVENT" \
  --arg count "$ACCEPTED_COUNT" --arg boundary "$WORLD_ROOT" '
  .method == "session/prompt" and
  (.params.prompt[0].text | contains("transactionId=" + $tx)) and
  (.params.prompt[0].text | contains("eventId=" + $event)) and
  (.params.prompt[0].text | contains("acceptedCount=" + $count)) and
  (.params.prompt[0].text | contains("worldRoot=" + $boundary)) and
  (.params.prompt[0].text | contains("publicationTargetIds=7003"))' \
  "$SECOND" >/dev/null
query_publication after-report 51003
[ "$(jq -er '.cell.root' "$EVIDENCE/after-report/view.json")" = "$AFTER_ROOT" ]
jq -se '[.[] | .grain.publications // [] | select(length > 0)] | length == 1' \
  "$STATE"/source-*.json >/dev/null
test "$(find "$ATTEMPT" -maxdepth 1 -name 'retry-*.json' -type f | wc -l | tr -d ' ')" -ge 1
exec 3>&-
wait "$CONNECT_PID" || :
CONNECT_PID=
printf 'PASS fresh native publication with lost MCP reply, audited recovery, exact session/load and historical receipt: %s\n' "$EVIDENCE"
