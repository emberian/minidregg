#!/bin/sh
# One append-only continuation of r3's app phase after reserve43000 was
# refused because its tool grain was paused. Preserve that exact refusal.
set -eu
umask 077
[ "$#" -eq 1 ] || { echo 'usage: recover-r3-app-attach.sh ROOT' >&2; exit 2; }
R=$1
[ "$R" = /var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-client-session-r3 ] || exit 2
A=$R/continuations/gitweb-journey/base-resume-0001
P=$A/app-recovery-0001
D=$R/continuations/first-birth-retry-0002
BASE=$R/base
STORE=$BASE/workroom/store/forward-link.sqlite3
T=$BASE/app-reserve-attempt
SOURCE=$A/application-continuation.sh
HOST=$D/bin/minidregg-host-2649-fin-repair
MINI=/tank/dregg-build/minidregg-007b513-client-evidence/bin/mini-007b513
STORE_BINARY=/tank/dregg-build/minidregg-9746c47-helpers-evidence/bin/minidregg-link-sqlite-store-9746c47
SIGNATURE_BINARY=/tank/dregg-build/minidregg-9746c47-helpers-evidence/bin/minidregg-credential-signature-verifier-9746c47
fail() { echo "r3 app recovery: $*" >&2; exit 2; }
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
protected_chain() {
  dir=$1
  while :; do
    [ -d "$dir" ] && [ ! -L "$dir" ] || fail "directory absent or linked: $dir"
    owner=$(stat -c '%u' "$dir")
    mode=$(stat -c '%a' "$dir")
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory: $dir"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable directory ancestor: $dir"
    [ "$dir" = / ] && break
    dir=${dir%/*}; [ -n "$dir" ] || dir=/
  done
}
for dir in "$R" "$A" "$BASE" "$T" "$D"; do protected_chain "$dir"; done
exec 9>"$A/lock"
flock -n 9 || fail 'another base continuation owns the lock'
[ -s "$A/workroom.completed" ] && [ -s "$A/application.started" ] || fail 'phase boundary differs'
[ ! -e "$A/application.completed" ] && [ ! -L "$A/application.completed" ] || fail 'app phase completed'
[ ! -e "$P" ] && [ ! -L "$P" ] || fail 'app recovery already attempted'
[ ! -e "$BASE/app-attempt" ] && [ ! -L "$BASE/app-attempt" ] || fail 'app birth already attempted'
[ ! -e "$BASE/session-attempt" ] && [ ! -L "$BASE/session-attempt" ] || fail 'session birth already attempted'
[ "$(sha "$STORE")" = 449278317fac429751ee208b39f5d6b97328c3fa84bf4fbcf6f1a962bb4bf5a9 ] || fail 'Store changed since refusal'
[ "$(sha "$SOURCE")" = c10a5629165d4ef0f5b3d2f3ee4306f30301122a55f2f74b9dd576eb2d8ce0b1 ] || fail 'original app source changed'
[ "$(sha "$A/application.stderr")" = 7d02c8cb5328d4de84a8479ad11d2097d3d79446735eeff00561789b03641cf5 ] || fail 'original stderr changed'
[ "$(sha "$T/intent.json")" = c6e0d40941f6f97af89af7611352e57b3b152f88d1d10d7f94f41f6fedb050ae ] || fail 'refused intent changed'
[ "$(sha "$T/call.bin")" = a14297a81ca175a3986e3fa23d29481cf01b39ea1f2740dc436e03c818a2c87d ] || fail 'refused call changed'
[ "$(sha "$T/outcome.bin")" = cad60ad085bd57da8465cc0a556adaf35547ac11efba9191fbcc688d9c809b22 ] || fail 'refused outcome changed'
[ "$(sha "$T/outcome.json")" = 82bd41a677c72c6884c143b207d1b52b279d3d6e0f12bd1fe1a79bb6e23e265e ] || fail 'refused presentation changed'
[ "$(sha "$BASE/app-reserve-before/view.json")" = 81cab989772db5ea4d9ec7fd92c09aea9faccb82b64979684d4540f4de81005a ] || fail 'pre-reserve view changed'
[ "$(sha "$BASE/workroom/tool-born/challenge.json")" = ed35ec4836f7dfee7999c14ee6ce44a7fde79672d061fa8ea651b68ee31ab8af ] || fail 'historical signed height changed'
[ "$(sha "$BASE/workroom/delegated-parent/view.json")" = d6f6b7bb1f5e1b52684c38971df9bd8199f1a088b80dbce832a206f9c71df267 ] || fail 'signed parent view changed'
[ "$(sha "$BASE/workroom/delegated-parent/intent.json")" = 6b5159c78185b04449a6777bad6d3bebe32bc74297fc12340997f20cbe4fec43 ] || fail 'parent witness query changed'
[ ! -e "$BASE/workroom/worker-bare-post/challenge.json" ] || fail 'direct fixture history unexpectedly present'
jq -e '.height == "17"' "$BASE/workroom/tool-born/challenge.json" >/dev/null || fail 'historical source height differs'
jq -e '.type == "refused" and .phase == "61646d697373696f6e" and .detail == "726571756573742072656675736564"' "$T/outcome.json" >/dev/null || fail 'not the exact admission refusal'
jq -e '.grain.task == "7902" and .grain.context.operationId == "43000" and
  .grain.operation == {type:"reserve",amount:"5"} and
  .grain.before == {generation:"0",status:"0",remaining:"50",reserved:"0"}' "$T/intent.json" >/dev/null || fail 'not the paused-tool reserve'
jq -e '.cell.grain == {task:"7902",generation:"0",status:"0",remaining:"50",reserved:"0"}' "$BASE/app-reserve-before/view.json" >/dev/null || fail 'pre-reserve read differs'
jq -e '.cell.grain == {task:"7901",generation:"0",status:"0",remaining:"100",reserved:"0"}' "$BASE/workroom/delegated-parent/view.json" >/dev/null || fail 'parent is not paused'
jq -e '.subject == "8" and .grants == [{kind:"object",target:"7901",capability:"73"}]' "$BASE/workroom/delegated-parent/intent.json" >/dev/null || fail 'parent witness grant differs'
[ "$(sha "$HOST")" = 2c28356f8c59dc5ec4d17c594ed718bca3f73f336790c8eb30bb395557f28bf7 ] || fail 'Host changed'
[ "$(sha "$MINI")" = a339b384f9a6c15d9c3f64e5df243b230da7e5a50d0b252cafbbcd94ad8e47ee ] || fail 'Mini changed'
(cd / && sha256sum -c "$A/input-sha256.txt" >/dev/null &&
  sha256sum -c "$A/generated-sha256.txt" >/dev/null) || fail 'retained inputs changed'
old_unit=mini-spk-platform-r3-base-app-handoff-client-session.service
status=$(systemctl --user show "$old_unit" -p ActiveState --value)
main_pid=$(systemctl --user show "$old_unit" -p MainPID --value)
case "$status" in inactive|failed) ;; *) fail "old unit state is $status" ;; esac
[ "$main_pid" = 0 ] || fail 'old unit still running'
journalctl --user -u "$old_unit" --no-pager --output=cat |
  grep -Fq 'Main process exited, code=exited, status=1/FAILURE' || fail 'old failure not retained'
! fuser -s "$STORE" 2>/dev/null || fail 'Store has a live opener'
for file in "$T"/*; do
  [ -f "$file" ] && [ ! -L "$file" ] || fail "refused member absent or linked: $file"
  [ "$(stat -c '%u' "$file")" = "$(id -u)" ] || fail "foreign refused member: $file"
  mode=$(stat -c '%a' "$file")
  [ $((0$mode & 022)) -eq 0 ] || fail "writable refused member: $file"
done
mkdir -m 700 "$P" || fail 'recovery already claimed'
mkdir -m 700 "$P/refused-attempt"
cp -p "$T"/* "$P/refused-attempt/"
sha256sum "$T"/* >"$P/refused-original-sha256.txt"
sha256sum "$P/refused-attempt"/* >"$P/refused-archive-sha256.txt"
for file in "$P/refused-attempt"/*; do sync -f "$file"; done
sync -f "$P/refused-original-sha256.txt"
sync -f "$P/refused-archive-sha256.txt"
sync -f "$P/refused-attempt"
cat >"$P/session-function.txt" <<'EOF'
start_session() {
  name=$1
  RUNTIME_BASE="/run/user/$(id -u)"
  [ -d "$RUNTIME_BASE" ] && [ ! -L "$RUNTIME_BASE" ] &&
    [ "$(stat -c '%u:%a' "$RUNTIME_BASE")" = "$(id -u):700" ] || exit 2
  SOCKET_DIR=$(mktemp -d "$RUNTIME_BASE/mini-r3a.XXXXXX")
  printf '%s\n' "$SOCKET_DIR" >"$RECOVERY/$name-socket-dir.txt"
  sync -f "$RECOVERY/$name-socket-dir.txt"
  SOCKET="$SOCKET_DIR/host.sock"
  "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$RECOVERY/$name-service.stdout" 2>"$RECOVERY/$name-service.stderr" &
  SERVICE_PID=$!
  tick=0
  until [ -S "$SOCKET" ]; do
    kill -0 "$SERVICE_PID" 2>/dev/null || exit 1
    tick=$((tick + 1)); [ "$tick" -lt 120 ] || exit 1
    sleep 1
  done
}
EOF
cat >"$P/attach-and-reserve.txt" <<'EOF'
# The integrated workroom left both parent and tool paused. The birth source
# needs a reserved hard parent witness and a separately reserved hard tool.
query app-parent-attach-recovery-before 7 7901 71 "$EVIDENCE/workroom/controller.key" 43401
jq -e '.cell.grain == {task:"7901",generation:"0",status:"0",remaining:"100",reserved:"0"}' \
  "$EVIDENCE/app-parent-attach-recovery-before/view.json" >/dev/null
jq -n --slurpfile read "$EVIDENCE/app-parent-attach-recovery-before/view.json" \
  --slurpfile challenge "$EVIDENCE/app-parent-attach-recovery-before/challenge.json" '
  {grain:{task:"7901",subject:"7",capability:"71",observeCapability:"71",
    schemaVersion:"1",expectedAuthorityRoot:$challenge[0].authorityRoot,
    expectedTargetRoot:$read[0].cell.root,
    context:{operationId:"43400",payload:"r3 app parent hard attach"},
    before:($read[0].cell.grain | {generation,status,remaining,reserved}),
    operation:{type:"attach",soft:false},publications:[]},
   grants:[{kind:"object",target:"7901",capability:"71"}],intentNonce:"43400"}' \
  >"$EVIDENCE/app-parent-attach-recovery-intent.json"
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/app-parent-attach-recovery-intent.json" --intent-kind grain-intent \
  --key "$EVIDENCE/workroom/controller.key" \
  --dir "$EVIDENCE/app-parent-attach-recovery-attempt" \
  >"$EVIDENCE/app-parent-attach-recovery.stdout"
confirmed "$EVIDENCE/app-parent-attach-recovery-attempt/outcome.json"
query app-parent-attached-recovery 7 7901 71 "$EVIDENCE/workroom/controller.key" 43402
jq -e '.cell.grain == {task:"7901",generation:"1",status:"1",remaining:"100",reserved:"0"}' \
  "$EVIDENCE/app-parent-attached-recovery/view.json" >/dev/null
query app-parent-reserve-recovery-before 7 7901 71 "$EVIDENCE/workroom/controller.key" 43411
jq -n --slurpfile read "$EVIDENCE/app-parent-reserve-recovery-before/view.json" \
  --slurpfile challenge "$EVIDENCE/app-parent-reserve-recovery-before/challenge.json" '
  {grain:{task:"7901",subject:"7",capability:"71",observeCapability:"71",
    schemaVersion:"1",expectedAuthorityRoot:$challenge[0].authorityRoot,
    expectedTargetRoot:$read[0].cell.root,
    context:{operationId:"43410",payload:"r3 app parent witness reserve"},
    before:($read[0].cell.grain | {generation,status,remaining,reserved}),
    operation:{type:"reserve",amount:"1"},publications:[]},
   grants:[{kind:"object",target:"7901",capability:"71"}],intentNonce:"43410"}' \
  >"$EVIDENCE/app-parent-reserve-recovery-intent.json"
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/app-parent-reserve-recovery-intent.json" --intent-kind grain-intent \
  --key "$EVIDENCE/workroom/controller.key" \
  --dir "$EVIDENCE/app-parent-reserve-recovery-attempt" \
  >"$EVIDENCE/app-parent-reserve-recovery.stdout"
confirmed "$EVIDENCE/app-parent-reserve-recovery-attempt/outcome.json"
query app-parent-reserved-recovery 8 7901 73 "$EVIDENCE/workroom/tool.key" 43412
jq -e '.cell.grain == {task:"7901",generation:"1",status:"3",remaining:"99",reserved:"1"}' \
  "$EVIDENCE/app-parent-reserved-recovery/view.json" >/dev/null
# The refused reserve43000 did not mutate the paused tool. Use fresh IDs.
query app-tool-attach-recovery-before 8 7902 81 "$EVIDENCE/workroom/tool.key" 43501
jq -e '.cell.grain == {task:"7902",generation:"0",status:"0",remaining:"50",reserved:"0"}' \
  "$EVIDENCE/app-tool-attach-recovery-before/view.json" >/dev/null
jq -n --slurpfile read "$EVIDENCE/app-tool-attach-recovery-before/view.json" \
  --slurpfile challenge "$EVIDENCE/app-tool-attach-recovery-before/challenge.json" '
  {grain:{task:"7902",subject:"8",capability:"81",observeCapability:"81",
    schemaVersion:"1",expectedAuthorityRoot:$challenge[0].authorityRoot,
    expectedTargetRoot:$read[0].cell.root,
    context:{operationId:"43500",payload:"r3 app tool hard attach"},
    before:($read[0].cell.grain | {generation,status,remaining,reserved}),
    operation:{type:"attach",soft:false},publications:[]},
   grants:[{kind:"object",target:"7902",capability:"81"}],intentNonce:"43500"}' \
  >"$EVIDENCE/app-tool-attach-recovery-intent.json"
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/app-tool-attach-recovery-intent.json" --intent-kind grain-intent \
  --key "$EVIDENCE/workroom/tool.key" \
  --dir "$EVIDENCE/app-tool-attach-recovery-attempt" \
  >"$EVIDENCE/app-tool-attach-recovery.stdout"
confirmed "$EVIDENCE/app-tool-attach-recovery-attempt/outcome.json"
query app-tool-attached-recovery 8 7902 81 "$EVIDENCE/workroom/tool.key" 43502
jq -e '.cell.grain == {task:"7902",generation:"1",status:"1",remaining:"50",reserved:"0"}' \
  "$EVIDENCE/app-tool-attached-recovery/view.json" >/dev/null
reserve_tool app-reserve-recovery 43510 5
EOF
cat >"$P/remaining-check.txt" <<'EOF'
jq -e --slurpfile initial "$EVIDENCE/app-tool-attach-recovery-before/view.json" '
  .cell.grain.remaining == ((($initial[0].cell.grain.remaining | tonumber) - 9) | tostring) and
  .cell.grain.reserved == "0"' \
EOF
sync -f "$P/session-function.txt"
sync -f "$P/attach-and-reserve.txt"
sync -f "$P/remaining-check.txt"
awk -v session="$P/session-function.txt" -v attach="$P/attach-and-reserve.txt" \
  -v remainingFile="$P/remaining-check.txt" '
  $0 == "SPK_AGENT_ALLOCATION=$6" {print; print "RECOVERY=$7"; arg++; next}
  $0 == "start_session() {" {
    while ((getline line < session) > 0) print line
    close(session); skipping=1; sessions++; next
  }
  skipping && $0 == "stop_session() {" {skipping=0}
  skipping {next}
  $0 == "reserve_tool app-reserve 43000 5" {
    while ((getline line < attach) > 0) print line
    close(attach); reserves++; next
  }
  index($0, "worker-bare-post/challenge.json") {
    gsub(/worker-bare-post/, "tool-born"); oldHeight++; print; next
  }
  index($0, ".cell.grain.remaining == \"38\" and .cell.grain.reserved == \"0\"") {
    while ((getline line < remainingFile) > 0) print line
    close(remainingFile); remaining++; next
  }
  {print}
  END {if (arg != 1 || sessions != 1 || reserves != 1 || oldHeight != 1 || remaining != 1 || skipping) exit 2}
' "$SOURCE" >"$P/application-attach-continuation.sh" || fail 'exact app substitution refused'
chmod 700 "$P/application-attach-continuation.sh"
/bin/sh -n "$P/application-attach-continuation.sh" || fail 'generated script syntax refused'
sha256sum "$SOURCE" "$P/application-attach-continuation.sh" >"$P/script-sha256.txt"
sync -f "$P/application-attach-continuation.sh"
sync -f "$P/script-sha256.txt"
sync -f "$P"
[ "$(sha "$STORE")" = 449278317fac429751ee208b39f5d6b97328c3fa84bf4fbcf6f1a962bb4bf5a9 ] || fail 'Store changed before attach'
/bin/sh "$P/application-attach-continuation.sh" "$HOST" "$BASE" "$MINI" \
  "$STORE_BINARY" "$SIGNATURE_BINARY" "$R/source-stage/agent-allocation.json" "$P" \
  >"$P/application.stdout" 2>"$P/application.stderr"
for attempt in app session; do
  [ -s "$BASE/$attempt-attempt/outcome.json" ] || fail "$attempt birth receipt absent"
  jq -e '.type == "confirmed" and .confirmation == "installed"' \
    "$BASE/$attempt-attempt/outcome.json" >/dev/null || fail "$attempt birth not installed"
done
sha256sum "$BASE/app-attempt/outcome.json" "$BASE/session-attempt/outcome.json" \
  "$P/application-attach-continuation.sh" >"$P/success-sha256.txt"
sync -f "$P/success-sha256.txt"
jq -n --arg recovery "$P" --arg appSha256 "$(sha "$BASE/app-attempt/outcome.json")" \
  --arg sessionSha256 "$(sha "$BASE/session-attempt/outcome.json")" '
  {protocol:"mini-spk-r3-app-attach-recovery-v1",recovery:$recovery,
   appSha256:$appSha256,sessionSha256:$sessionSha256}' >"$A/application-recovery-link.json"
sync -f "$A/application-recovery-link.json"
printf '%s\n' 'complete via app-recovery-0001' >"$A/application.completed"
sync -f "$A/application.completed"
sync -f "$A"
printf '%s\n' "$A/application.completed"
