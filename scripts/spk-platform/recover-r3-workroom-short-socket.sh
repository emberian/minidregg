#!/bin/sh
# One reviewed recovery of the r3 workroom phase that stopped before socket
# bind. Preserve the original generated script, marker, and failure evidence.
set -eu
umask 077

[ "$#" -eq 1 ] || { echo 'usage: recover-r3-workroom-short-socket.sh ROOT' >&2; exit 2; }
R=$1
[ "$R" = /var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-client-session-r3 ] || exit 2
W="$R/base/workroom"
A="$R/continuations/gitweb-journey/base-resume-0001"
P="$A/workroom-recovery-0001"
D="$R/continuations/first-birth-retry-0002"
STORE="$W/store/forward-link.sqlite3"
ORIGINAL="$A/workroom-continuation.sh"
HOST="$D/bin/minidregg-host-2649-fin-repair"
MINI=/tank/dregg-build/minidregg-007b513-client-evidence/bin/mini-007b513
STORE_BINARY=/tank/dregg-build/minidregg-9746c47-helpers-evidence/bin/minidregg-link-sqlite-store-9746c47
SIGNATURE_BINARY=/tank/dregg-build/minidregg-9746c47-helpers-evidence/bin/minidregg-credential-signature-verifier-9746c47
fail() { echo "r3 workroom recovery: $*" >&2; exit 2; }
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
for dir in "$R" "$W" "$A" "$D"; do protected_chain "$dir"; done
exec 9>"$A/lock"
flock -n 9 || fail 'another base continuation owns the lock'
[ -d "$A" ] && [ ! -L "$A" ] && [ -s "$A/workroom.started" ] || fail 'original started phase absent'
[ ! -e "$A/workroom.completed" ] && [ ! -L "$A/workroom.completed" ] || fail 'workroom already completed'
[ ! -e "$P" ] && [ ! -L "$P" ] || fail 'recovery already attempted; reconcile it'
[ ! -e "$W/agents/verified" ] && [ ! -L "$W/agents/verified" ] || fail 'native workroom phase may already have begun'
[ ! -e "$R/base/app-attempt" ] && [ ! -L "$R/base/app-attempt" ] || fail 'app phase may already have begun'
[ ! -e "$W/continuation-session/host.sock" ] && [ ! -L "$W/continuation-session/host.sock" ] || fail 'old socket appeared'
[ "$(sha "$ORIGINAL")" = fdc0f3bd2c03c5212deb72f709f9f7a3d7ec4b12898afc4b463d179ddf1d629c ] || fail 'original generated script differs'
[ "$(sha "$A/generated-sha256.txt")" = 823d4db17c4f81960a539dce3d42aff947069d6342dc7596eea95131c2b4830c ] || fail 'original generated manifest differs'
[ "$(sha "$W/continuation-session/stderr")" = c36ed286dda7c825c7f74121a110aca3e9e46711f77da2227bb09d77f69e766a ] || fail 'socket refusal evidence differs'
grep -Fq 'path must be shorter than SUN_LEN' "$W/continuation-session/stderr" || fail 'old failure was not socket-length refusal'
[ "$(sha "$STORE")" = e5515e158fdfb03afdafc3951a3a73c2b779bac37eb8428a146c8244611e30e5 ] || fail 'Store changed since pre-bind refusal'
[ "$(sha "$HOST")" = 2c28356f8c59dc5ec4d17c594ed718bca3f73f336790c8eb30bb395557f28bf7 ] || fail 'selected Host differs'
[ "$(sha "$MINI")" = a339b384f9a6c15d9c3f64e5df243b230da7e5a50d0b252cafbbcd94ad8e47ee ] || fail 'Mini differs'
old_unit=mini-spk-platform-r3-base-resume-r2-client-session.service
status=$(systemctl --user show "$old_unit" -p ActiveState --value)
main_pid=$(systemctl --user show "$old_unit" -p MainPID --value)
case "$status" in inactive|failed) ;; *) fail "old unit state is $status" ;; esac
[ "$main_pid" = 0 ] || fail "old unit still has MainPID $main_pid"
! fuser -s "$STORE" 2>/dev/null || fail 'Store has a live opener'
journalctl --user -u "$old_unit" --no-pager --output=cat |
  grep -Fq 'status=1/FAILURE' || fail 'old unit failure is not retained'
(cd / && sha256sum -c "$A/generated-sha256.txt" >/dev/null) || fail 'original generated sources differ'
(cd / && sha256sum -c "$A/input-sha256.txt" >/dev/null) || fail 'original action inputs differ'
mkdir -m 700 "$P" || fail 'recovery action already claimed'
jq -n --arg original "$ORIGINAL" --arg originalSha256 "$(sha "$ORIGINAL")" \
  --arg oldServiceErrorSha256 "$(sha "$W/continuation-session/stderr")" \
  --arg acceptedStoreSha256 "$(sha "$STORE")" '
  {protocol:"mini-spk-r3-workroom-prebind-recovery-v1",originalGeneratedScript:$original,
   originalSha256:$originalSha256,oldServiceErrorSha256:$oldServiceErrorSha256,
   acceptedStoreSha256:$acceptedStoreSha256,oldUnit:"mini-spk-platform-r3-base-resume-r2-client-session.service",
   reason:"old socket exceeded SUN_LEN before query; no verified directory or Store change"}' >"$P/provenance.json"
sync -f "$P/provenance.json"
sync -f "$P"
sync -f "$A"
awk '
  $0 == "EVIDENCE=$1 HOST=$2 MINI=$3 STORE_BINARY=$4 SIGNATURE_BINARY=$5" {
    print; print "RECOVERY=$8"; a++; next
  }
  $0 == "mkdir -m 700 \"$EVIDENCE/continuation-session\"" {
    print "RUNTIME_BASE=\"/run/user/$(id -u)\""
    print "[ -d \"$RUNTIME_BASE\" ] && [ ! -L \"$RUNTIME_BASE\" ] &&"
    print "  [ \"$(stat -c '\''%u:%a'\'' \"$RUNTIME_BASE\")\" = \"$(id -u):700\" ] || exit 2"
    print "SOCKET_DIR=$(mktemp -d \"$RUNTIME_BASE/mini-r3w.XXXXXX\")"
    print "printf '\''%s\\n'\'' \"$SOCKET_DIR\" >\"$RECOVERY/socket-dir.txt\""
    print "sync -f \"$RECOVERY/socket-dir.txt\""
    print "sync -f \"$RECOVERY\""
    b++; next
  }
  $0 == "SOCKET=\"$EVIDENCE/continuation-session/host.sock\"" {
    print "SOCKET=\"$SOCKET_DIR/host.sock\""; c++; next
  }
  $0 == "  >\"$EVIDENCE/continuation-session/stdout\" 2>\"$EVIDENCE/continuation-session/stderr\" &" {
    print "  >\"$RECOVERY/service.stdout\" 2>\"$RECOVERY/service.stderr\" &"; d++; next
  }
  {print}
  END {if (a != 1 || b != 1 || c != 1 || d != 1) exit 2}
' "$ORIGINAL" >"$P/workroom-short-socket.sh" || fail 'exact launcher substitution refused'
chmod 700 "$P/workroom-short-socket.sh"
/bin/sh -n "$P/workroom-short-socket.sh" || fail 'recovery script syntax refused'
old_body=$(awk '/^# The one signed birth receipt covers all eight added grains/{emit=1} emit{print}' "$ORIGINAL" | sha256sum | cut -d ' ' -f 1)
new_body=$(awk '/^# The one signed birth receipt covers all eight added grains/{emit=1} emit{print}' "$P/workroom-short-socket.sh" | sha256sum | cut -d ' ' -f 1)
[ "$old_body" = "$new_body" ] || fail 'workroom body changed'
sha256sum "$ORIGINAL" "$P/workroom-short-socket.sh" >"$P/script-sha256.txt"
sync -f "$P/workroom-short-socket.sh"
sync -f "$P/script-sha256.txt"
sync -f "$P"
[ "$(sha "$STORE")" = e5515e158fdfb03afdafc3951a3a73c2b779bac37eb8428a146c8244611e30e5 ] || fail 'Store changed before recovery run'
/bin/sh "$P/workroom-short-socket.sh" "$W" "$HOST" "$MINI" \
  "$STORE_BINARY" "$SIGNATURE_BINARY" "$R/source-stage/agent-allocation.json" \
  "$A/adopted-birth-receipt.json" "$P" >"$P/workroom.stdout" 2>"$P/workroom.stderr"
[ -s "$W/agents/verified/birth-evidence.json" ] || fail 'workroom signed evidence absent'
sha256sum "$W/agents/verified/birth-evidence.json" "$P/workroom-short-socket.sh" >"$P/success-sha256.txt"
sync -f "$P/success-sha256.txt"
jq -n --arg recovery "$P" --arg signedEvidenceSha256 "$(sha "$W/agents/verified/birth-evidence.json")" '
  {protocol:"mini-spk-r3-workroom-recovery-link-v1",recovery:$recovery,
   signedEvidenceSha256:$signedEvidenceSha256}' >"$A/workroom-recovery-link.json"
sync -f "$A/workroom-recovery-link.json"
printf '%s\n' 'complete via workroom-recovery-0001' >"$A/workroom.completed"
sync -f "$A/workroom.completed"
sync -f "$A"
printf '%s\n' "$A/workroom.completed"
