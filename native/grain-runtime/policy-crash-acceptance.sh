#!/bin/sh
# Fresh native g+1 policy-install crash window, with an isolated Mini wrapper.
set -eu
umask 077
[ "$#" -eq 3 ] || { echo 'usage: policy-crash-acceptance.sh HOST NEW_ABSOLUTE_EVIDENCE_DIR TASK_BASE' >&2; exit 2; }
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
HOST=$(realpath "$1")
EVIDENCE=$2
TASK_BASE=$3
MINI=${MINI:?MINI required}
GRAIN=${GRAIN:?GRAIN required}
STORE_BINARY=${STORE_BINARY:?STORE_BINARY required}
SIGNATURE_BINARY=${SIGNATURE_BINARY:?SIGNATURE_BINARY required}
safe_path() {
  case $1 in
    /*) : ;;
    *) echo "absolute path required: $1" >&2; exit 2 ;;
  esac
  printf '%s\n' "$1" | LC_ALL=C grep -Eq '^/[A-Za-z0-9_./-]+$' || {
    echo "path has unsupported characters: $1" >&2; exit 2;
  }
  case $1/ in
    *'/../'*|*'/./'*|*'//'*) echo "noncanonical path: $1" >&2; exit 2 ;;
  esac
}
for path in "$HOST" "$EVIDENCE" "$MINI" "$GRAIN" "$STORE_BINARY" "$SIGNATURE_BINARY"; do
  safe_path "$path"
done
printf '%s\n' "$TASK_BASE" | grep -Eq '^77[1-9][0-9]$' || {
  echo 'TASK_BASE must be a four-digit 7710..7799 private grain ID' >&2; exit 2;
}
[ "$TASK_BASE" -le 7797 ] || { echo 'TASK_BASE leaves no room for two siblings' >&2; exit 2; }
[ ! -e "$EVIDENCE" ] || { echo 'evidence directory already exists' >&2; exit 2; }
if [ "${POLICY_CRASH_STAGED:-0}" != 1 ]; then
  # Preserve HERE/acceptance.sh's source-owned bootstrap relative path in an
  # immutable private copy; never rewrite the shared source or live guards.
  grep -Fq '7001' "$HERE/acceptance.sh" || {
    echo 'expected original acceptance.sh ID map is absent' >&2; exit 2;
  }
  SOURCE_DIR="$EVIDENCE.source"
  [ ! -e "$SOURCE_DIR" ] || { echo 'private source directory already exists' >&2; exit 2; }
  mkdir -p "$SOURCE_DIR/native/grain-runtime"
  chmod 700 "$SOURCE_DIR" "$SOURCE_DIR/native" "$SOURCE_DIR/native/grain-runtime"
  NEXT_TOOL=$((TASK_BASE + 1))
  NEXT_PUBLICATION=$((TASK_BASE + 2))
  sed -e "s/7001/$TASK_BASE/g" -e "s/7002/$NEXT_TOOL/g" \
    -e "s/7003/$NEXT_PUBLICATION/g" "$HERE/acceptance.sh" \
    >"$SOURCE_DIR/native/grain-runtime/acceptance.sh"
  sed -e "s/7705/$TASK_BASE/g" -e "s/7706/$NEXT_TOOL/g" \
    -e "s/7707/$NEXT_PUBLICATION/g" "$0" \
    >"$SOURCE_DIR/native/grain-runtime/policy-crash-acceptance.sh"
  chmod 700 "$SOURCE_DIR/native/grain-runtime/"*.sh
  sh -n "$SOURCE_DIR/native/grain-runtime/"*.sh
  POLICY_CRASH_STAGED=1 exec "$SOURCE_DIR/native/grain-runtime/policy-crash-acceptance.sh" \
    "$HOST" "$EVIDENCE" "$TASK_BASE"
fi
grep -Fq "target:\"$TASK_BASE\"" "$HERE/acceptance.sh" || {
  echo 'staged bootstrap does not use requested parent ID' >&2; exit 2;
}
MINI=$MINI GRAIN=$GRAIN STORE_BINARY=$STORE_BINARY SIGNATURE_BINARY=$SIGNATURE_BINARY \
  BOOTSTRAP_ONLY=1 "$HERE/acceptance.sh" "$HOST" "$EVIDENCE"
EVIDENCE=$(realpath "$EVIDENCE")
CONFIG="$EVIDENCE/deployment/pinned-config.json"
SOCKET="$EVIDENCE/session-law-crash/host.sock"
STATE="$EVIDENCE/runtime-law-crash"
CONTROL="$STATE/control.sock"
UNIT=mini-grain-controller@7705.service
MARKER="mini-grain-law-crash:$EVIDENCE"
CONTINUATION_MARKER="mini-grain-law-crash-continuation:$EVIDENCE"
INVOCATION=
RUN_PID=
MINI_PID=
CONN_PID=
cleanup() {
  if [ -n "$CONN_PID" ]; then kill "$CONN_PID" 2>/dev/null || :; wait "$CONN_PID" 2>/dev/null || :; fi
  if [ -n "$RUN_PID" ]; then
    actual=$(systemctl --user show -p Description --value "$UNIT" 2>/dev/null || :)
    current=$(systemctl --user show -p InvocationID --value "$UNIT" 2>/dev/null || :)
    if { [ "$actual" = "$MARKER" ] || [ "$actual" = "$CONTINUATION_MARKER" ]; } &&
        [ "$current" = "$INVOCATION" ]; then
      systemctl --user stop "$UNIT" >/dev/null 2>&1 || :
    fi
    kill "$RUN_PID" 2>/dev/null || :
    wait "$RUN_PID" 2>/dev/null || :
  fi
  if [ -n "$MINI_PID" ]; then kill "$MINI_PID" 2>/dev/null || :; wait "$MINI_PID" 2>/dev/null || :; fi
}
trap cleanup EXIT HUP INT TERM
mkdir -m 700 "$EVIDENCE/session-law-crash" "$STATE"
cat >"$EVIDENCE/mini-wrapper" <<WRAPPER
#!/bin/sh
set -eu
REAL='$MINI'
MARKER='$EVIDENCE/fault-ready'
case " \$* " in
  *' --intent-kind grain-policy-install-intent '*)
    "\$REAL" "\$@"
    if mkdir "\$MARKER" 2>/dev/null; then
      while :; do sleep 1; done
    fi
    ;;
  *) exec "\$REAL" "\$@" ;;
esac
WRAPPER
chmod 700 "$EVIDENCE/mini-wrapper"
"$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$EVIDENCE/mini-crash.stdout" 2>"$EVIDENCE/mini-crash.stderr" &
MINI_PID=$!
wait_socket() {
  sock=$1 pid=$2
  tick=0
  until [ -S "$sock" ]; do
    kill -0 "$pid" 2>/dev/null || { echo "service exited before $sock" >&2; exit 1; }
    tick=$((tick + 1))
    [ "$tick" -lt 120 ] || { echo "socket timeout: $sock" >&2; exit 1; }
    sleep 1
  done
}
query_parent() {
  name=$1 nonce=$2
  jq -n --arg nonce "$nonce" '{subject:"7",nonce:$nonce,
    purpose:{type:"query",kind:"object",target:"7705",view:"resource"},
    grants:[{kind:"object",target:"7705",capability:"71"}]}' \
    >"$EVIDENCE/$name-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-intent.json" --key "$EVIDENCE/controller.key" \
    --view resource --dir "$EVIDENCE/$name" >"$EVIDENCE/$name.stdout"
}
query_policy() {
  name=$1 nonce=$2
  jq -n --arg nonce "$nonce" '{subject:"7",nonce:$nonce,
    purpose:{type:"query",kind:"object",target:"7705",view:"policy"},
    grants:[{kind:"object",target:"7705",capability:"71"}]}' \
    >"$EVIDENCE/$name-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-intent.json" --key "$EVIDENCE/controller.key" \
    --view policy --dir "$EVIDENCE/$name" >"$EVIDENCE/$name.stdout"
}
wait_socket "$SOCKET" "$MINI_PID"
jq -n --arg mini "$EVIDENCE/mini-wrapper" --arg host "$HOST" \
  --arg cfg "$CONFIG" --arg socket "$SOCKET" --arg key "$EVIDENCE/controller.key" \
  --arg tool "$EVIDENCE/tool.key" --arg state "$STATE" --arg control "$CONTROL" \
  --arg cwd "$EVIDENCE" '{mini:$mini,host:$host,hostConfig:$cfg,hostSocket:$socket,
    custodyKey:$key,stateDir:$state,controlSocket:$control,cwd:$cwd,
    task:"7705",subject:"7",capability:"71",queryCapability:"71",
    policyControlCapability:"72",toolTask:{task:"7706",subject:"8",
      capability:"81",queryCapability:"81",custodyKey:$tool,
      parentCapability:"73",parentObserveCapability:"73",reserve:"2",charge:"1",
      allowedPublications:[]},commands:[]}' >"$EVIDENCE/runtime-law-crash-config.json"
state=$(systemctl --user show -p ActiveState --value "$UNIT" 2>/dev/null || :)
case $state in active|activating|deactivating|reloading) echo "unit in use: $UNIT" >&2; exit 1;; esac
systemd-run --user --wait --pipe --collect --unit="${UNIT%.service}" \
  --description="$MARKER" --property=KillMode=control-group \
  --property=RuntimeMaxSec=1200s "$GRAIN" serve "$EVIDENCE/runtime-law-crash-config.json" \
  >"$EVIDENCE/controller-first.stdout" 2>"$EVIDENCE/controller-first.stderr" &
RUN_PID=$!
wait_socket "$CONTROL" "$RUN_PID"
[ "$(systemctl --user show -p Description --value "$UNIT")" = "$MARKER" ]
INVOCATION=$(systemctl --user show -p InvocationID --value "$UNIT")
MAIN_PID=$(systemctl --user show -p MainPID --value "$UNIT")
[ -n "$INVOCATION" ] && [ "$MAIN_PID" -gt 0 ]
case $(ps -p "$MAIN_PID" -o args=) in
  "$GRAIN serve $EVIDENCE/runtime-law-crash-config.json") : ;;
  *) echo 'unit MainPID is not the expected controller' >&2; exit 1 ;;
esac
printf 'firstInvocation=%s mainPid=%s\n' "$INVOCATION" "$MAIN_PID" \
  >"$EVIDENCE/controller-identity.txt"
mkfifo "$EVIDENCE/first-input.fifo"
"$GRAIN" connect "$CONTROL" <"$EVIDENCE/first-input.fifo" \
  >"$EVIDENCE/first-connect.stdout" 2>"$EVIDENCE/first-connect.stderr" &
CONN_PID=$!
exec 3>"$EVIDENCE/first-input.fifo"
printf 'attach soft\n' >&3
tick=0
until [ -d "$EVIDENCE/fault-ready" ]; do
  tick=$((tick + 1))
  [ "$tick" -lt 900 ] || { echo 'policy install did not reach crash barrier' >&2; exit 1; }
  sleep 1
done
set -- "$STATE"/policy-attempt-*/outcome.json
[ "$#" -eq 1 ] && [ -f "$1" ]
POLICY_OUTCOME=$1
jq -e '.type == "confirmed" and .confirmation == "installed"' "$POLICY_OUTCOME" >/dev/null
POLICY_ATTEMPT=$(dirname "$POLICY_OUTCOME")
POLICY_CALL_HASH=$(sha256sum "$POLICY_ATTEMPT/call.bin" | cut -d ' ' -f 1)
jq -e '.connection == "fenced" and .pending.operation == "policy install" and
  .pending.attempt == $attempt' --arg attempt "$POLICY_ATTEMPT" "$STATE/journal.json" >/dev/null
[ "$(find "$STATE" -maxdepth 1 -type f -name 'source-*.json' | wc -l | tr -d ' ')" = 0 ]
[ "$(systemctl --user show -p MainPID --value "$UNIT")" = "$MAIN_PID" ]
[ "$(systemctl --user show -p InvocationID --value "$UNIT")" = "$INVOCATION" ]
[ "$(systemctl --user show -p Description --value "$UNIT")" = "$MARKER" ]
systemctl --user kill --kill-whom=main --signal=SIGKILL "$UNIT"
tick=0
until [ "$(systemctl --user show -p MainPID --value "$UNIT")" = 0 ]; do
  tick=$((tick + 1)); [ "$tick" -lt 60 ] || exit 1; sleep 1
done
exec 3>&-
wait "$CONN_PID" 2>/dev/null || :
CONN_PID=
wait "$RUN_PID" 2>/dev/null || :
RUN_PID=
query_parent after-crash 77001
jq -e '.page.grain == {task:"7705",generation:"0",status:"0",
  remaining:"100",reserved:"0"}' "$EVIDENCE/after-crash/view.json" >/dev/null
query_policy installed-before-attach 77002
jq -e '.version == "1"' "$EVIDENCE/installed-before-attach/view.json" >/dev/null
jq -n '{owner:"7",workerSubject:"8",workerGeneration:"1"}' \
  >"$EVIDENCE/expected-g-plus-one.json"
"$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --kind grain-policy --input "$EVIDENCE/expected-g-plus-one.json" \
  --output "$EVIDENCE/expected-g-plus-one.bin"
jq '.predicate' "$EVIDENCE/installed-before-attach/view.json" \
  >"$EVIDENCE/installed-predicate.json"
"$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --kind predicate --input "$EVIDENCE/installed-predicate.json" \
  --output "$EVIDENCE/installed-predicate.bin"
cmp "$EVIDENCE/expected-g-plus-one.bin" "$EVIDENCE/installed-predicate.bin"
# `recover` performs an exact lookup of the retained first install attempt.
systemctl --user reset-failed "$UNIT" >/dev/null 2>&1 || :
state=$(systemctl --user show -p ActiveState --value "$UNIT" 2>/dev/null || :)
case $state in active|activating|deactivating|reloading) echo 'old unit still active' >&2; exit 1;; esac
systemd-run --user --wait --pipe --collect --unit="${UNIT%.service}" \
  --description="$CONTINUATION_MARKER" --property=KillMode=control-group \
  --property=RuntimeMaxSec=1200s "$GRAIN" serve "$EVIDENCE/runtime-law-crash-config.json" \
  >"$EVIDENCE/controller-second.stdout" 2>"$EVIDENCE/controller-second.stderr" &
RUN_PID=$!
tick=0
until [ "$(systemctl --user show -p Description --value "$UNIT" 2>/dev/null || :)" = "$CONTINUATION_MARKER" ] &&
      [ "$(systemctl --user show -p MainPID --value "$UNIT" 2>/dev/null || :)" -gt 0 ] &&
      ss -xl | grep -F "$CONTROL" >/dev/null; do
  kill -0 "$RUN_PID" 2>/dev/null || { echo 'continuation controller exited' >&2; exit 1; }
  tick=$((tick + 1)); [ "$tick" -lt 120 ] || { echo 'continuation controller timeout' >&2; exit 1; }
  sleep 1
done
INVOCATION=$(systemctl --user show -p InvocationID --value "$UNIT")
[ -n "$INVOCATION" ]
[ "$INVOCATION" != "$(sed -n 's/^firstInvocation=\([^ ]*\).*/\1/p' "$EVIDENCE/controller-identity.txt")" ]
printf 'secondInvocation=%s\n' "$INVOCATION" >>"$EVIDENCE/controller-identity.txt"
mkfifo "$EVIDENCE/second-input.fifo"
"$GRAIN" connect "$CONTROL" <"$EVIDENCE/second-input.fifo" \
  >"$EVIDENCE/second-connect.stdout" 2>"$EVIDENCE/second-connect.stderr" &
CONN_PID=$!
exec 3>"$EVIDENCE/second-input.fifo"
printf 'attach soft\nrecover\n' >&3
tick=0
until jq -e '.connection == "detached" and .pending == null' "$STATE/journal.json" >/dev/null 2>&1; do
  tick=$((tick + 1)); [ "$tick" -lt 900 ] || { echo 'exact pending recovery timeout' >&2; exit 1; }; sleep 1
done
[ "$(sha256sum "$POLICY_ATTEMPT/call.bin" | cut -d ' ' -f 1)" = "$POLICY_CALL_HASH" ]
set -- "$POLICY_ATTEMPT"/retry-*.json
[ "$#" -ge 1 ] && [ -f "$1" ]
jq -e '.type == "confirmed" and .confirmation == "replayed"' "$1" >/dev/null
jq -e --slurpfile original "$POLICY_OUTCOME" \
  '.type == "confirmed" and .confirmation == "replayed" and
   .transactionId == $original[0].transactionId and
   .eventId == $original[0].eventId and
   .acceptedCount == $original[0].acceptedCount and
   .imageBoundary == $original[0].imageBoundary' "$1" >/dev/null
printf 'attach soft\n' >&3
tick=0
until jq -e '.connection == "soft" and .pending == null' "$STATE/journal.json" >/dev/null 2>&1; do
  tick=$((tick + 1)); [ "$tick" -lt 900 ] || { echo 'reattach timeout' >&2; exit 1; }; sleep 1
done
query_parent after-reattach 77003
jq -e '.page.grain == {task:"7705",generation:"1",status:"2",
  remaining:"100",reserved:"0"}' "$EVIDENCE/after-reattach/view.json" >/dev/null
jq -se '[.[] | select(.grain.task == "7705" and .grain.operation.type == "attach")] |
  length == 1 and .[0].grain.before == {generation:"0",status:"0",
    remaining:"100",reserved:"0"}' "$STATE"/source-*.json >/dev/null
query_policy policy-after-attach 77004
jq '.predicate' "$EVIDENCE/policy-after-attach/view.json" \
  >"$EVIDENCE/policy-after-attach-predicate.json"
"$MINI" author --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --kind predicate --input "$EVIDENCE/policy-after-attach-predicate.json" \
  --output "$EVIDENCE/policy-after-attach-predicate.bin"
cmp "$EVIDENCE/expected-g-plus-one.bin" "$EVIDENCE/policy-after-attach-predicate.bin"
exec 3>&-
wait "$CONN_PID" 2>/dev/null || :
CONN_PID=
printf 'PASS exact g+1 policy install survived owned-controller crash before attach; lookup-only recovery and signed attach\n'
