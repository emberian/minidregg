#!/bin/sh
# Reconcile the exact r3 app recovery after its final, incorrect status assertion.
# This observes retained receipts and signed reads; it never invokes Mini or the Store.
set -eu
umask 077
[ "$#" -eq 1 ] || { echo 'usage: complete-r3-app-recovery.sh ROOT' >&2; exit 2; }
R=$1
[ "$R" = /var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-client-session-r3 ] || exit 2
A=$R/continuations/gitweb-journey/base-resume-0001
P=$A/app-recovery-0001
B=$R/base
STORE=$B/workroom/store/forward-link.sqlite3
UNIT=mini-spk-platform-r3-app-attach-recovery-client-session.service
INVOCATION=eb28b8d18f7e4a9f8ae0fe3d280dad67
fail() { echo "r3 app completion: $*" >&2; exit 2; }
sha() { sha256sum "$1" | cut -d ' ' -f 1; }
protected_chain() {
  dir=$1
  while :; do
    [ -d "$dir" ] && [ ! -L "$dir" ] || fail "directory absent or linked: $dir"
    owner=$(stat -c '%u' "$dir")
    mode=$(stat -c '%a' "$dir")
    { [ "$owner" = 0 ] || [ "$owner" = "$(id -u)" ]; } || fail "foreign directory: $dir"
    [ $((0$mode & 022)) -eq 0 ] || fail "writable ancestor: $dir"
    [ "$dir" = / ] && break
    dir=${dir%/*}; [ -n "$dir" ] || dir=/
  done
}
retained() {
  [ -f "$1" ] && [ ! -L "$1" ] && [ -s "$1" ] || fail "retained file absent: $1"
  [ "$(stat -c '%u' "$1")" = "$(id -u)" ] || fail "foreign file: $1"
  mode=$(stat -c '%a' "$1")
  [ $((0$mode & 022)) -eq 0 ] || fail "writable file: $1"
}
for d in "$R" "$A" "$P" "$B"; do protected_chain "$d"; done
exec 9>"$A/lock"
flock -n 9 || fail 'base action has another owner'
[ -s "$A/application.started" ] && [ -s "$A/workroom.completed" ] || fail 'phase boundary differs'
for p in "$A/application.completed" "$A/application-recovery-link.json" \
    "$P/final-observation.json" "$B/additional-sessions.json"; do
  [ ! -e "$p" ] && [ ! -L "$p" ] || fail "completion already attempted: $p"
done
state=$(systemctl --user show "$UNIT" -p ActiveState --value)
pid=$(systemctl --user show "$UNIT" -p MainPID --value)
case "$state" in inactive|failed) ;; *) fail "unit state $state" ;; esac
[ "$pid" = 0 ] || fail 'unit still has a main process'
journalctl --user -u "$UNIT" --no-pager --output=json |
  jq -e --arg invocation "$INVOCATION" '
    select(.USER_INVOCATION_ID == $invocation and
      (.MESSAGE | contains("Main process exited, code=exited, status=1/FAILURE")))' \
    >/dev/null ||
  fail 'exact failed invocation absent'
! fuser -s "$STORE" 2>/dev/null || fail 'Store still open'
retained "$STORE"
[ "$(sha "$STORE")" = bd7c2eca5fbc66214d71aba923144c5b6ac6aa7bfdea0398a74f368183e46cef ] ||
  fail 'Store changed after final signed read'
(cd / && sha256sum -c "$A/input-sha256.txt" >/dev/null &&
  sha256sum -c "$A/generated-sha256.txt" >/dev/null &&
  sha256sum -c "$P/script-sha256.txt" >/dev/null) || fail 'retained sources or binaries changed'
for n in app session bob-web-session alice-api-session hermes-a-session hermes-b-session; do
  retained "$B/$n-attempt/outcome.json"
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    ([.acceptedCount,.transactionId,.eventId,.imageBoundary] |
      all(.[]; type == "string" and test("^(0|[1-9][0-9]*)$")))' \
    "$B/$n-attempt/outcome.json" >/dev/null || fail "$n birth receipt not installed"
done
for n in app session; do
  retained "$B/$n-attempt/retry-0001.json"
  jq -e --slurpfile original "$B/$n-attempt/outcome.json" '
    .type == "confirmed" and .confirmation == "replayed" and
    [.acceptedCount,.transactionId,.eventId,.imageBoundary] ==
    [$original[0].acceptedCount,$original[0].transactionId,
      $original[0].eventId,$original[0].imageBoundary]' \
    "$B/$n-attempt/retry-0001.json" >/dev/null || fail "$n lookup differs"
done
retained "$B/additional-sessions.jsonl"
[ "$(wc -l < "$B/additional-sessions.jsonl")" -eq 4 ] || fail 'four session rows required'
for route in bob-web alice-api hermes-a hermes-b; do
  for kind in session descriptor; do
    retained "$B/$route-$kind-born/view.bin"
    retained "$B/$route-$kind-born/view.json"
  done
  jq -e --arg route "$route" --slurpfile original "$B/$route-session-attempt/outcome.json" '
    select(.route == $route) |
    [.birthReceipt.acceptedCount,.birthReceipt.transactionId,
      .birthReceipt.eventId,.birthReceipt.imageBoundary] ==
    [$original[0].acceptedCount,$original[0].transactionId,
      $original[0].eventId,$original[0].imageBoundary]' \
    "$B/additional-sessions.jsonl" >/dev/null || fail "$route retained receipt differs"
  jq -e --arg route "$route" \
    --arg sessionSha "$(sha "$B/$route-session-born/view.json")" \
    --arg descriptorSha "$(sha "$B/$route-descriptor-born/view.json")" '
    select(.route == $route) |
    .sessionViewSha256 == $sessionSha and
    .descriptorViewSha256 == $descriptorSha' \
    "$B/additional-sessions.jsonl" >/dev/null || fail "$route signed view hash differs"
done
for n in app-born package-born snapshot-born session-born descriptor-born \
    app-policy package-policy snapshot-policy session-policy descriptor-policy; do
  retained "$B/$n/view.bin"
  retained "$B/$n/view.json"
done
retained "$B/additional-session-tool-after/view.bin"
retained "$B/additional-session-tool-after/view.json"
jq -e '.page.grain == {task:"7902",generation:"1",status:"1",remaining:"25",reserved:"0"}' \
  "$B/additional-session-tool-after/view.json" >/dev/null || fail 'final attached tool differs'
[ "$(jq -r .acceptedCount "$B/hermes-b-session-attempt/outcome.json")" = 27 ] ||
  fail 'final accepted count differs'

# No Native operation occurs below. A failed save leaves the original phase
# started and the new reconciliation artifacts explicit for review.
jq -s '{type:"mini-spk-additional-session-births-v1",sessions:.}' \
  "$B/additional-sessions.jsonl" >"$B/additional-sessions.json"
sync -f "$B/additional-sessions.json"
jq -n --arg invocation "$INVOCATION" --arg storeSha256 "$(sha "$STORE")" \
  --arg scriptSha256 "$(sha "$P/application-attach-continuation.sh")" \
  --arg sessionsSha256 "$(sha "$B/additional-sessions.json")" \
  --arg finalViewSha256 "$(sha "$B/additional-session-tool-after/view.bin")" '
  {protocol:"mini-spk-r3-app-final-observation-v1",failedUnitInvocation:$invocation,
   failedUnitStatus:1,failedPredicate:"expected reserved-hard status 3 after final settlement",
   sourceFinalStatus:"attached-hard status 1, reserved 0",acceptedCount:"27",
   storeSha256:$storeSha256,scriptSha256:$scriptSha256,
   sessionsSha256:$sessionsSha256,finalSignedViewSha256:$finalViewSha256}' \
  >"$P/final-observation.json"
sync -f "$P/final-observation.json"
jq -n --arg recovery "$P" --arg observationSha256 "$(sha "$P/final-observation.json")" \
  --arg appSha256 "$(sha "$B/app-attempt/outcome.json")" \
  --arg sessionSha256 "$(sha "$B/session-attempt/outcome.json")" '
  {protocol:"mini-spk-r3-app-attach-recovery-v1",recovery:$recovery,
   observationSha256:$observationSha256,appSha256:$appSha256,
   sessionSha256:$sessionSha256}' >"$A/application-recovery-link.json"
sync -f "$A/application-recovery-link.json"
printf '%s\n' 'complete via app-recovery-0001 final observation; original unit failed assertion' \
  >"$A/application.completed"
sync -f "$A/application.completed"
sync -f "$A"; sync -f "$P"; sync -f "$B"
printf '%s\n' "$A/application.completed"
