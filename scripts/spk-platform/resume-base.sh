#!/bin/sh
# Continue the exact retained integrated base after its first birth was
# confirmed. The fresh-only provisioner and run-base wrappers are never rerun.
# A failed phase keeps its private attempt and is never automatically retried.
set -eu
umask 077

usage() {
  echo "usage: $0 ROOT ORIGINAL_HOST CONTINUATION_HOST MINI STORE_HELPER SIGNATURE_HELPER SPK_HOST ORIGINAL_SUBMIT_RECEIPT REPLAYED_LOOKUP_RECEIPT PINNED_RUN_BASE_SOURCE" >&2
  exit 2
}
[ "$#" -eq 10 ] || usage
ROOT=$1 ORIGINAL_HOST=$2 HOST=$3 MINI=$4 STORE_BINARY=$5 SIGNATURE_BINARY=$6 SPK_HOST=$7
SUBMIT_RECEIPT=$8 LOOKUP_RECEIPT=$9 RUN_SOURCE=${10}
fail() { echo "integrated base continuation: $*" >&2; exit 2; }
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
absolute() {
  case "$1" in /*) ;; *) fail "absolute path required" ;; esac
  case "$1" in *'/../'*|*'/./'*|*'//'*|*'/..'|*'/.'|*'/') fail "noncanonical path" ;; esac
}
private_file() {
  [ -f "$1" ] && [ ! -L "$1" ] && [ -s "$1" ] || fail "retained input absent: $1"
  [ "$(stat -c '%u' "$1")" = "$(id -u)" ] || fail "retained input owner differs: $1"
  mode=$(stat -c '%a' "$1")
  [ $((0$mode & 022)) -eq 0 ] || fail "retained input group/world-writable: $1"
}
protected_dir_chain() {
  directory=$1
  while :; do
    [ -d "$directory" ] && [ ! -L "$directory" ] || fail "protected directory absent or linked: $directory"
    metadata=$(stat -c '%u:%a' "$directory")
    owner=${metadata%%:*}; mode=${metadata#*:}
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory owner: $directory"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable directory ancestor: $directory"
    [ "$directory" = / ] && break
    directory=${directory%/*}; [ -n "$directory" ] || directory=/
  done
}
for path in "$ROOT" "$ORIGINAL_HOST" "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
    "$SPK_HOST" "$SUBMIT_RECEIPT" "$LOOKUP_RECEIPT" "$RUN_SOURCE"; do absolute "$path"; done
case "$ROOT" in /var/lib/minidregg/spk/fixtures/*) ;; *) fail "unexpected fixture root" ;; esac
protected_dir_chain "$ROOT"
for executable in "$ORIGINAL_HOST" "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" "$SPK_HOST"; do
  [ -x "$executable" ] && [ ! -L "$executable" ] || fail "pinned executable unavailable"
done
WORKROOM="$ROOT/base/workroom"
ATTEMPT="$WORKROOM/birth-attempt"
STAGE="$ROOT/base.source-stage"
WORKROOM_SOURCE="$WORKROOM.source-stage/provision-member.sh"
APP_SOURCE="$STAGE/scripts/application-current-birth/native-share-base.sh"
ACTION="$ROOT/continuations/gitweb-journey/base-resume-0001"
case "$SUBMIT_RECEIPT" in "$ATTEMPT"/outcome.json|"$ATTEMPT"/retry-????.json) ;; *) fail "submit receipt is not in original attempt" ;; esac
case "$LOOKUP_RECEIPT" in "$ATTEMPT"/retry-????.json) ;; *) fail "lookup receipt is not in original attempt" ;; esac
for path in "$ATTEMPT" "$STAGE" "$WORKROOM.source-stage" \
    "${SUBMIT_RECEIPT%/*}" "${LOOKUP_RECEIPT%/*}"; do protected_dir_chain "$path"; done
private_file "$ATTEMPT/call.bin"
private_file "$ATTEMPT/attempt.json"
private_file "$ATTEMPT/config.json"
private_file "$SUBMIT_RECEIPT"
private_file "$LOOKUP_RECEIPT"
private_file "$WORKROOM_SOURCE"
private_file "$APP_SOURCE"
private_file "$ROOT/source-stage/agent-allocation.json"
private_file "$WORKROOM/deployment/pinned-config.json"
private_file "$STAGE/input-sha256.txt"
private_file "$STAGE/private-source-sha256.txt"
private_file "$WORKROOM.source-stage/provision.sha256"
private_file "$RUN_SOURCE"
test "$(sha "$RUN_SOURCE")" = \
  c913a09d52cb15562f838acf46e7fa6aea8c1bf072c3eb76547a32338847adde || fail "run-base source differs from original"
if [ -e "$ACTION" ] || [ -L "$ACTION" ]; then
  [ -d "$ACTION" ] && [ ! -L "$ACTION" ] || fail "continuation action linked or malformed"
  new_action=false
else
  new_action=true
  [ ! -e "$WORKROOM/agents/verified" ] && [ ! -L "$WORKROOM/agents/verified" ] || fail "post-birth phase already began"
  [ ! -e "$ROOT/base/app-attempt" ] && [ ! -L "$ROOT/base/app-attempt" ] || fail "app birth phase already began"
  [ ! -e "$ROOT/source-stage/install-v2-handoff.json" ] || fail "base handoff already exists"
fi
test "$(sha "$ATTEMPT/call.bin")" = \
  1ff9d4ad41644a376884d13a6092787a2ca6a2a7d99c30659263f04221d8bdb7 || fail "original birth call differs"
test "$(sha "$ATTEMPT/config.json")" = \
  c2c79aa69f66ecc7922f69f620a9dd9ca24cfea25cd94282fcb1a40c2b8296b8 || fail "original Settings differ"
jq -e --arg host "$ORIGINAL_HOST" --arg config "$ATTEMPT/config.json" '
  .format == "minidregg-resource-client-attempt-v1" and
  .operation == "submit" and .host == $host and .config == $config' \
  "$ATTEMPT/attempt.json" >/dev/null || fail "retained operation identity differs"
test "$(sha "$ORIGINAL_HOST")" = \
  95cd66117983796e4887f03f3ddd25b048d70713fb56ae93c36dbbc379139285 || fail "original Host differs"
test "$(sha "$HOST")" = \
  2c28356f8c59dc5ec4d17c594ed718bca3f73f336790c8eb30bb395557f28bf7 || fail "reviewed continuation Host differs"
test "$(sha "$MINI")" = \
  a339b384f9a6c15d9c3f64e5df243b230da7e5a50d0b252cafbbcd94ad8e47ee || fail "original Mini differs"
test "$(sha "$SPK_HOST")" = \
  1d85b2f21039bc228262ca6a1b0bf52a0c26688f9a7324588d3fbde3679dd2e4 || fail "original physical Host differs"
test "$(sha "$WORKROOM/deployment/pinned-config.json")" = \
  "$(sha "$ATTEMPT/config.json")" || fail "current config differs from original"
(cd "$ROOT" && sha256sum -c "$STAGE/input-sha256.txt" >/dev/null &&
  sha256sum -c "$STAGE/private-source-sha256.txt" >/dev/null &&
  sha256sum -c "$WORKROOM.source-stage/provision.sha256" >/dev/null) || fail "retained source or binary pin differs"
test "$(rg -c '^# The one signed birth receipt covers all eight added grains' "$WORKROOM_SOURCE")" = 1 || fail "workroom continuation marker differs"
test "$(rg -c -F 'birth-attempt/outcome.json' "$WORKROOM_SOURCE")" = 2 || fail "workroom receipt references differ"
test "$(rg -c -F 'CONFIG="$EVIDENCE/workroom/deployment/pinned-config.json"' "$APP_SOURCE")" = 1 || fail "app continuation marker differs"
test "$(rg -c -F 'CONFIG="$ROOT/base/workroom/deployment/pinned-config.json"' "$RUN_SOURCE")" = 1 || fail "handoff continuation marker differs"
jq -e '.type == "confirmed" and
  (.confirmation == "installed" or .confirmation == "recoveredAfterUncertainResponse") and
  ([.transactionId,.eventId,.acceptedCount,.imageBoundary] |
    all(.[]; type == "string" and test("^(0|[1-9][0-9]*)$")))' \
  "$SUBMIT_RECEIPT" >/dev/null || fail "original submit receipt is not confirmed"
jq -e '.type == "confirmed" and .confirmation == "replayed" and
  ([.transactionId,.eventId,.acceptedCount,.imageBoundary] |
    all(.[]; type == "string" and test("^(0|[1-9][0-9]*)$")))' \
  "$LOOKUP_RECEIPT" >/dev/null || fail "read-only original-call lookup is not replayed"
submit_fields=$(jq -Sc '{transactionId,eventId,acceptedCount,imageBoundary}' "$SUBMIT_RECEIPT")
lookup_fields=$(jq -Sc '{transactionId,eventId,acceptedCount,imageBoundary}' "$LOOKUP_RECEIPT")
[ "$submit_fields" = "$lookup_fields" ] || fail "original receipt and replay differ"

[ -d "$ROOT/continuations" ] || mkdir -m 700 "$ROOT/continuations"
[ ! -L "$ROOT/continuations" ] || fail "continuation root linked"
[ -d "$ROOT/continuations/gitweb-journey" ] || mkdir -m 700 "$ROOT/continuations/gitweb-journey"
[ ! -L "$ROOT/continuations/gitweb-journey" ] || fail "journey directory linked"
protected_dir_chain "$ROOT/continuations/gitweb-journey"
if [ "$new_action" = true ]; then
mkdir -m 700 "$ACTION" || fail "continuation already claimed"
printf '%s\n' "$submit_fields" >"$ACTION/adopted-birth-receipt-fields.json"
cp "$LOOKUP_RECEIPT" "$ACTION/adopted-birth-receipt.json"
jq -n --arg originalHost "$ORIGINAL_HOST" --arg continuationHost "$HOST" \
  --arg originalSha256 "$(sha "$ORIGINAL_HOST")" --arg continuationSha256 "$(sha "$HOST")" \
  '{protocol:"mini-spk-gitweb-host-transition-v1",originalHost:$originalHost,
    originalSha256:$originalSha256,continuationHost:$continuationHost,
    continuationSha256:$continuationSha256}' >"$ACTION/host-transition.json"
sync -f "$ACTION/adopted-birth-receipt-fields.json"
sync -f "$ACTION/adopted-birth-receipt.json"
sync -f "$ACTION/host-transition.json"
sync -f "$ACTION"
sync -f "$ROOT/continuations/gitweb-journey"
sha256sum "$ATTEMPT/call.bin" "$ATTEMPT/config.json" "$SUBMIT_RECEIPT" \
  "$LOOKUP_RECEIPT" "$WORKROOM_SOURCE" "$APP_SOURCE" "$RUN_SOURCE" \
  "$ORIGINAL_HOST" "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" "$SPK_HOST" \
  >"$ACTION/input-sha256.txt"

# The generated scripts are a literal projection of the retained reviewed
# source after each fresh-only prefix. They are saved before execution. No
# source codec, authority decision, or receipt is authored in shell.
cat >"$ACTION/workroom-continuation.sh" <<'EOF'
#!/bin/sh
set -eu
umask 077
EVIDENCE=$1 HOST=$2 MINI=$3 STORE_BINARY=$4 SIGNATURE_BINARY=$5
SPK_AGENT_ALLOCATION=$6 ADOPTED_RECEIPT=$7 ACTION_DIR=$8
WORKROOM_PARENT_TASK=7901 WORKROOM_TOOL_TASK=7902
CONFIG="$EVIDENCE/deployment/pinned-config.json"
SEMANTICS=$(jq -er .semantics "$EVIDENCE/operator-profile.json")
SERVICE_PID=
cleanup() { if [ -n "$SERVICE_PID" ]; then kill "$SERVICE_PID" 2>/dev/null || :; wait "$SERVICE_PID" 2>/dev/null || :; fi; }
trap cleanup EXIT HUP INT TERM
RUNTIME_BASE="/run/user/$(id -u)"
[ -d "$RUNTIME_BASE" ] && [ ! -L "$RUNTIME_BASE" ] &&
  [ "$(stat -c '%u:%a' "$RUNTIME_BASE")" = "$(id -u):700" ] || exit 2
SOCKET_DIR=$(mktemp -d "$RUNTIME_BASE/mini-r3w.XXXXXX")
printf '%s\n' "$SOCKET_DIR" >"$ACTION_DIR/socket-dir.txt"
sync -f "$ACTION_DIR/socket-dir.txt"
sync -f "$ACTION_DIR"
SOCKET="$SOCKET_DIR/host.sock"
"$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$ACTION_DIR/workroom-service.stdout" 2>"$ACTION_DIR/workroom-service.stderr" &
SERVICE_PID=$!
tick=0
until [ -S "$SOCKET" ]; do
  kill -0 "$SERVICE_PID" 2>/dev/null || exit 1
  tick=$((tick + 1)); [ "$tick" -lt 120 ] || exit 1
  sleep 1
done
EOF
awk '
  /^decimal\(\) \{/ {emit=1; count++}
  /^"\$MINI" keygen / {emit=0}
  emit {print}
  END {if (count != 1) exit 2}
' "$WORKROOM_SOURCE" >>"$ACTION/workroom-continuation.sh" || fail "workroom helpers differ"
awk '
  /^# The one signed birth receipt covers all eight added grains/ {emit=1; count++}
  emit {
    gsub(/\$EVIDENCE\/birth-attempt\/outcome.json/, "$ADOPTED_RECEIPT")
    print
  }
  END {if (count != 1) exit 2}
' "$WORKROOM_SOURCE" >>"$ACTION/workroom-continuation.sh" || fail "workroom body differs"
cat >"$ACTION/application-continuation.sh" <<'EOF'
#!/bin/sh
set -eu
umask 077
HOST=$1 EVIDENCE=$2 MINI=$3 STORE_BINARY=$4 SIGNATURE_BINARY=$5
SPK_AGENT_ALLOCATION=$6
EOF
awk '
  /^CONFIG="\$EVIDENCE\/workroom\/deployment\/pinned-config.json"$/ {emit=1; count++}
  emit {print}
  END {if (count != 1) exit 2}
' "$APP_SOURCE" >>"$ACTION/application-continuation.sh" || fail "app body differs"
cat >"$ACTION/handoff-continuation.sh" <<'EOF'
#!/bin/sh
set -eu
umask 077
ROOT=$1 HOST=$2 MINI=$3 STORE_BINARY=$4 SIGNATURE_BINARY=$5 SPK_HOST=$6
SPK_AGENT_ALLOCATION="$ROOT/source-stage/agent-allocation.json"
SPK_COMPLETION_PUBLIC=$(od -An -tx1 -v "$ROOT/custody/completion.pub" | tr -d ' \n')
QUALIFY_RESULT="$ROOT/source-stage/qualify-launch-result.json"
EOF
awk '
  /^CONFIG="\$ROOT\/base\/workroom\/deployment\/pinned-config.json"$/ {emit=1; count++}
  emit {print}
  END {if (count != 1) exit 2}
' "$RUN_SOURCE" >>"$ACTION/handoff-continuation.sh" || fail "handoff body differs"
chmod 700 "$ACTION/"*-continuation.sh
for generated in "$ACTION/"*-continuation.sh; do /bin/sh -n "$generated" || fail "generated continuation syntax refused"; done
sha256sum "$ACTION/"*-continuation.sh >"$ACTION/generated-sha256.txt"
sha256sum -c "$ACTION/input-sha256.txt" >"$ACTION/input-precheck.txt" || fail "input drift before continuation"
for prepared in "$ACTION/"*-continuation.sh "$ACTION/input-sha256.txt" \
    "$ACTION/generated-sha256.txt"; do sync -f "$prepared"; done
sync -f "$ACTION"
else
  protected_dir_chain "$ACTION"
  private_file "$ACTION/adopted-birth-receipt-fields.json"
  private_file "$ACTION/adopted-birth-receipt.json"
  private_file "$ACTION/host-transition.json"
  private_file "$ACTION/input-sha256.txt"
  private_file "$ACTION/generated-sha256.txt"
  [ "$(cat "$ACTION/adopted-birth-receipt-fields.json")" = "$lookup_fields" ] || fail "retained adopted receipt differs"
  [ "$(sha "$ACTION/adopted-birth-receipt.json")" = "$(sha "$LOOKUP_RECEIPT")" ] || fail "retained lookup bytes differ"
  jq -e --arg originalHost "$ORIGINAL_HOST" --arg continuationHost "$HOST" \
    --arg originalSha256 "$(sha "$ORIGINAL_HOST")" --arg continuationSha256 "$(sha "$HOST")" '
    .protocol == "mini-spk-gitweb-host-transition-v1" and
    .originalHost == $originalHost and .originalSha256 == $originalSha256 and
    .continuationHost == $continuationHost and .continuationSha256 == $continuationSha256' \
    "$ACTION/host-transition.json" >/dev/null || fail "retained Host transition differs"
  sha256sum -c "$ACTION/input-sha256.txt" >/dev/null || fail "retained action input pin differs"
  sha256sum -c "$ACTION/generated-sha256.txt" >/dev/null || fail "retained generated source differs"
fi
exec 9>"$ACTION/lock"
flock -n 9 || fail "another base continuation holds this action"

# Completed phases are read back and skipped. A started phase without a
# completion marker is uncertain and must be reconciled from its exact Mini
# attempts before any new invocation; only clean phase boundaries resume.
mark_phase() {
  phase=$1
  [ ! -e "$ACTION/$phase.started" ] && [ ! -L "$ACTION/$phase.started" ] ||
    fail "$phase already started without completion; reconcile retained attempts"
  printf '%s\n' started >"$ACTION/$phase.started"
  sync -f "$ACTION/$phase.started"
  sync -f "$ACTION"
}
complete_phase() {
  phase=$1
  printf '%s\n' complete >"$ACTION/$phase.completed"
  sync -f "$ACTION/$phase.completed"
  sync -f "$ACTION"
}
if [ -e "$ACTION/workroom.completed" ]; then
  test -s "$WORKROOM/agents/verified/birth-evidence.json" || fail "completed workroom evidence absent"
else
  [ ! -e "$WORKROOM/agents/verified" ] && [ ! -L "$WORKROOM/agents/verified" ] ||
    fail "workroom phase may already have mutated Store"
  mark_phase workroom
  /bin/sh "$ACTION/workroom-continuation.sh" "$WORKROOM" "$HOST" "$MINI" \
    "$STORE_BINARY" "$SIGNATURE_BINARY" "$ROOT/source-stage/agent-allocation.json" \
    "$ACTION/adopted-birth-receipt.json" "$ACTION" \
    >"$ACTION/workroom.stdout" 2>"$ACTION/workroom.stderr"
  test -s "$WORKROOM/agents/verified/birth-evidence.json" || fail "workroom continuation lacked birth evidence"
  complete_phase workroom
fi
if [ -e "$ACTION/application.completed" ]; then
  test -s "$ROOT/base/app-attempt/outcome.json" || fail "completed app receipt absent"
else
  [ ! -e "$ROOT/base/app-attempt" ] && [ ! -L "$ROOT/base/app-attempt" ] ||
    fail "app phase may already have mutated Store"
  mark_phase application
  /bin/sh "$ACTION/application-continuation.sh" "$HOST" "$ROOT/base" "$MINI" \
    "$STORE_BINARY" "$SIGNATURE_BINARY" "$ROOT/source-stage/agent-allocation.json" \
    >"$ACTION/application.stdout" 2>"$ACTION/application.stderr"
  test -s "$ROOT/base/app-attempt/outcome.json" || fail "app receipt absent"
  complete_phase application
fi
if [ -e "$ACTION/handoff.completed" ]; then
  test -s "$ROOT/source-stage/install-v2-handoff.json" || fail "completed handoff absent"
else
  [ ! -e "$ROOT/source-stage/install-v2-handoff.json" ] || fail "handoff may already exist"
  mark_phase handoff
  /bin/sh "$ACTION/handoff-continuation.sh" "$ROOT" "$HOST" "$MINI" \
    "$STORE_BINARY" "$SIGNATURE_BINARY" "$SPK_HOST" \
    >"$ACTION/handoff.stdout" 2>"$ACTION/handoff.stderr"
  test -s "$ROOT/source-stage/install-v2-handoff.json" || fail "qualified INSTALL handoff absent"
  complete_phase handoff
fi
sha256sum -c "$ACTION/input-sha256.txt" >"$ACTION/input-postcheck.txt" || fail "retained inputs changed"
sha256sum -c "$ACTION/generated-sha256.txt" >"$ACTION/generated-postcheck.txt" || fail "generated continuation changed"
if [ -e "$ACTION/complete.txt" ]; then
  grep -Fxq 'base continuation complete; original birth receipt adopted, no fresh bootstrap' \
    "$ACTION/complete.txt" || fail "final marker differs"
else
  printf '%s\n' 'base continuation complete; original birth receipt adopted, no fresh bootstrap' >"$ACTION/complete.txt"
  sync -f "$ACTION/complete.txt"
fi
sync -f "$ACTION"
