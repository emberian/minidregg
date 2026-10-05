#!/bin/sh
# The v4 failed-create chronology, recorded through the real code paths on a
# fresh scratch Store with no root: a real Mini Host admits every record and
# the ordinary spk-host broker, grain CLI, resident and supervisor author and
# sign them. Only the operating-system boundary is modeled: spk-host is the
# `fixture-os` build (native/spk-host/src/os.rs, fixture_os.rs), whose units,
# cgroups, mounts, identities and root custody live below RUN_ROOT/fos.
#
#   fixture-v4.sh RUN_ROOT                 the whole recording (RUN_ROOT must not exist)
#   fixture-v4.sh --base RUN_ROOT          Store, app birth, INSTALL and route only;
#                                          every service stopped afterwards
#   fixture-v4.sh --chronology RUN_ROOT    the START chronology on such a base
#   fixture-v4.sh --restart RUN_ROOT       on a COPY of a recorded chronology: the retried
#                                          START's op38 reply is lost (its reply frame,
#                                          outcome and completed marker removed, the three
#                                          active markers retained); the g<retry> resident
#                                          unit restarts and must reconcile by op39 lookup
#                                          alone: the recovered receipt equals the recorded
#                                          one and nothing is resubmitted
#
# A base is copied (cp -a, at the same path) to repeat the chronology.
# RUN_ROOT must not exist for a recording or a base; its parent must be an owner-private chain (the
# fixture principal stands in for root, so every ancestor must be root- or
# principal-owned and not group/world writable: use $XDG_RUNTIME_DIR).
#
# Chronology (app 9101, instance `a` of grain-journey.sh):
#   install (INSTALL v3) -> the first START is a create (v3 BEGIN op66/67/22,
#   CLAIM op68/69/26) whose unit ExecStart fails after Entered with no child
#   (the integration-qualification trigger) -> the unit's OnFailure= supervisor
#   reconciles it (failed-START recovery op206-209, custodian-signed report) ->
#   the next START is the governed repeat create (v4 retry BEGIN op66/67/22,
#   CLAIM op68/69/26, COMPLETION op70/71/38) -> app running.
# The result is RUN_ROOT/fixture.json naming every path a replay test needs.
#
# Environment:
#   LANE_BIN  directory with minidregg-host, mini, minidregg-client-consent,
#             minidregg-link-sqlite-store, minidregg-credential-signature-verifier
#             and spk-host (built with --features fixture-os,integration-qualification)
#   SPK       the signed package (default: sntfy)
set -eu
umask 077

MODE=all
case "${1:-}" in --base) MODE=base; shift ;; --chronology) MODE=chronology; shift ;; --restart) MODE=restart; shift ;; esac
[ "$#" -eq 1 ] || { sed -n '2,36p' "$0" >&2; exit 2; }
RUN=$1
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
LANE_BIN=${LANE_BIN:?set LANE_BIN}
SPK=${SPK:-/home/ember/build/mini-datamodel-20260930/spk-apps/market/sntfy.spk}
fail() { echo "fixture-v4: $*" >&2; exit 1; }
case "$RUN" in /*) ;; *) fail "RUN_ROOT must be absolute" ;; esac
FOS=$RUN/fos
BIN=$RUN/bin
GRAINS=$RUN/grains
SPKROOT=$RUN/spk
J=$REPO/scripts/spk-platform/grain-journey.sh
JRUN=$RUN/journey
export MINI_FIXTURE_OS=$FOS

start_broker() {
  setsid "$BIN/spk-host" broker-serve "$FOS/broker.json" >>"$FOS/logs/broker.log" 2>&1 </dev/null &
  echo "$!" >"$FOS/broker.pid"
  tick=0
  until [ -S "$GRAINS/broker.sock" ]; do
    kill -0 "$(cat "$FOS/broker.pid")" 2>/dev/null || { tail -n 5 "$FOS/logs/broker.log" >&2; fail "broker exited"; }
    tick=$((tick + 1)); [ "$tick" -lt 200 ] || fail "broker socket timeout"
    sleep 0.1
  done
}
stop_all() {
  for state in "$FOS"/state/*.json; do
    [ -e "$state" ] || continue
    "$FOS/systemctl" stop "$(basename "$state" .json)" >/dev/null 2>&1 || :
  done
  sh "$J" stop-services "$JRUN" >/dev/null 2>&1 || :
  kill "$(cat "$FOS/broker.pid")" 2>/dev/null || :
  tick=0
  while kill -0 "$(cat "$FOS/broker.pid")" 2>/dev/null && [ "$tick" -lt 100 ]; do
    tick=$((tick + 1)); sleep 0.1
  done
  rm -f "$FOS/broker.pid" "$GRAINS/broker.sock"
}
export BIN SPK GRAINS_ROOT=$GRAINS BROKER_SOCKET=$GRAINS/broker.sock

if [ "$MODE" = restart ]; then
  [ -s "$RUN/fixture.json" ] || fail "$RUN holds no recorded chronology"
  [ ! -e "$RUN/restart.json" ] || fail "$RUN was already restarted: restart a fresh copy"
  STATE=$(jq -er .stateRoot "$RUN/fixture.json")
  APP=$(jq -er .app "$RUN/fixture.json")
  RETRY=$(jq -er .retryGeneration "$RUN/fixture.json")
  G=$STATE/apps/$APP/g$RETRY
  SIGN=$G/completion-sign-attempt-retry-v4
  RECORDED=$(jq -c .retryCompletion.completionReceipt "$RUN/fixture.json")
  if [ -e "$G/start-completed-retry-v4.json" ]; then
    [ "$RECORDED" = "$(jq -c .completionReceipt "$G/start-completed-retry-v4.json")" ] ||
      fail "recorded completion differs from fixture.json"
  fi
  # The op38 reply is lost: the submit marker and the exact ingress stay.
  rm -f "$G/start-completed-retry-v4.json" "$SIGN/op38-frame.bin" "$SIGN/op38-outcome.bin" "$SIGN/op38-outcome.json"
  for pair in begin-attempt-retry-v4/op66-requested.json:lifecycle-begin-retry-v4-active.json \
      claim-author-attempt-retry-v4/op68-requested.json:lifecycle-claim-retry-v4-active.json \
      completion-sign-attempt-retry-v4/op70-requested.json:lifecycle-completion-retry-v4-active.json; do
    ( umask 077; cp "$G/${pair%%:*}" "$G/${pair#*:}" )
  done
  start_broker
  trap stop_all EXIT
  sh "$J" phase "$JRUN" services
  UNIT=$(jq -er .unit "$G/resident.json")
  "$FOS/systemctl" stop "$UNIT" >/dev/null 2>&1 || :
  "$FOS/systemctl" start "$UNIT" || :
  tick=0
  until [ -s "$G/start-completed-retry-v4.json" ]; do
    state=$("$FOS/systemctl" show "$UNIT" --property=ActiveState --value)
    case "$state" in failed|inactive) [ -s "$G/start-completed-retry-v4.json" ] || fail "restarted resident ended $state without reconciling (see $FOS/logs)";; esac
    tick=$((tick + 1)); [ "$tick" -lt 600 ] || fail "restarted resident did not reconcile"
    sleep 0.5
  done
  RECOVERED=$(jq -c .completionReceipt "$G/start-completed-retry-v4.json")
  EVIDENCE=$(jq -er .evidenceName "$G/start-completed-retry-v4.json")
  case "$EVIDENCE" in op39-lookup-*/outcome.json) ;; *) fail "reconciled from $EVIDENCE, not an op39 lookup" ;; esac
  jq -e '.type == "replayed" or .confirmation == "replayed"' "$SIGN/$EVIDENCE" >/dev/null ||
    fail "op39 lookup is not a replay of the original admission"
  [ "$RECOVERED" = "$RECORDED" ] || fail "recovered receipt $RECOVERED differs from recorded $RECORDED"
  [ ! -e "$SIGN/op38-outcome.bin" ] || fail "the restart resubmitted op38"
  jq -n --argjson recorded "$RECORDED" --argjson recovered "$RECOVERED" --arg evidence "$EVIDENCE" \
    '{protocol:"mini-spk-fixture-v4-restart-v1",recorded:$recorded,recovered:$recovered,evidence:$evidence}' >"$RUN/restart.json"
  stop_all
  trap - EXIT
  echo "fixture-v4: restart reconciled by op39: $RECOVERED"
  exit 0
fi

if [ "$MODE" = chronology ]; then
  [ -e "$RUN/base.done" ] || fail "$RUN is not a recorded base"
  [ ! -e "$RUN/fixture.json" ] || fail "$RUN already holds a chronology"
  start_broker
  trap stop_all EXIT
  sh "$J" phase "$JRUN" services
else
[ ! -e "$RUN" ] || fail "RUN_ROOT exists"
mkdir -m 700 "$RUN"
mkdir -m 700 "$FOS" "$FOS/units" "$FOS/state" "$FOS/logs" "$FOS/mounts"
mkdir -m 755 "$BIN" "$GRAINS" "$SPKROOT" "$SPKROOT/packages"
mkdir -m 700 "$SPKROOT/inbox"
for name in minidregg-host mini minidregg-client-consent minidregg-link-sqlite-store \
    minidregg-credential-signature-verifier spk-host; do
  install -m 755 "$LANE_BIN/$name" "$BIN/$name"
done
env -u MINI_FIXTURE_OS "$BIN/spk-host" fixture-systemctl daemon-reload 2>/dev/null &&
  fail "spk-host answers fixture-systemctl without MINI_FIXTURE_OS" || :
for helper in spk-ingest spk-var-volume; do
  install -m 755 "$REPO/native/spk-host/tests/fixture-os/$helper" "$FOS/$helper"
done
printf '#!/bin/sh\nexec %s fixture-systemctl "$@"\n' "$BIN/spk-host" >"$FOS/systemctl"
chmod 755 "$FOS/systemctl"
digest() { printf '%s' "$1" | sha256sum | cut -c1-64; }
printf 'deployment_id=%s\nhost_id=%s\n' "$(digest fixture-v4-deployment)" "$(digest fixture-v4-host)" \
  >"$FOS/host-identity"
chmod 600 "$FOS/host-identity"
jq -n --arg grains "$GRAINS" --arg spkRoot "$SPKROOT" --arg user "$(id -un)" \
  --arg spk "$BIN/spk-host" --arg sha "$(sha256sum "$BIN/spk-host" | cut -c1-64)" \
  --arg ingest "$FOS/spk-ingest" --arg volume "$FOS/spk-var-volume" '
  {protocol:"mini-spk-broker-config-v1",grainsRoot:$grains,spkRoot:$spkRoot,
   brokerSocket:($grains + "/broker.sock"),operatorUser:$user,unitPrefix:"mini",
   spkHost:$spk,spkHostSha256:$sha,ingestHelper:$ingest,volumeHelper:$volume,
   appUids:[61001,61002,61003]}' >"$FOS/broker.json"
chmod 600 "$FOS/broker.json"

start_broker
trap stop_all EXIT
# The profile is read when grain-journey.sh starts: phases after `profile` run
# in a fresh invocation.
sh "$J" phase "$JRUN" store services workroom profile
sh "$J" phase "$JRUN" birth-a install-a share-a
: >"$RUN/base.done"
if [ "$MODE" = base ]; then
  stop_all
  trap - EXIT
  echo "fixture-v4: base recorded at $RUN"
  exit 0
fi
fi

PROFILE_RESULT=$JRUN/evidence/profile-result.json
STATE=$(jq -er .stateRoot "$PROFILE_RESULT")
PROFILE=$(jq -er .profilePath "$PROFILE_RESULT")
APP=9101
APPDIR=$STATE/apps/$APP
before=$(ls -d "$APPDIR"/g* 2>/dev/null | wc -l)
[ "$before" = 0 ] || fail "app $APP already has a generation before its first START"

# The first START is a create; its unit ExecStart fails after Entered with no
# child (hostd::qualification_refuse_spawn, integration-qualification).
( umask 077; : >"$APPDIR/qualification-fail-spawn-v1" )
if sh "$J" phase "$JRUN" start-a; then
  fail "the armed first START reported success"
fi
[ ! -e "$APPDIR/qualification-fail-spawn-v1" ] || fail "trigger not consumed: START never reached ExecStart"
FAILED=$(for g in "$APPDIR"/g*/qualification-fail-spawn-consumed-v1; do basename "$(dirname "$g")"; done |
  sed 's/^g//' | sort -n | tail -n 1)
[ -n "$FAILED" ] || fail "no generation consumed the trigger"
jq -e '.startAction == {kind:"create",index:0}' "$APPDIR/g$FAILED/resident.json" >/dev/null ||
  fail "the failed START was not the first create"

# The unit's OnFailure= supervisor reconciles the claimed, childless START.
RECOVERED=$APPDIR/g$FAILED/failed-start-recovered-v1.json
tick=0
until [ -s "$RECOVERED" ]; do
  tick=$((tick + 1)); [ "$tick" -lt 1800 ] || fail "no failed-START recovery receipt (see $FOS/logs)"
  sleep 0.5
done
jq -e --arg g "$FAILED" '.generation == $g and .outcome.type == "confirmed"
  and .outcome.confirmation == "installed"' "$RECOVERED" >/dev/null ||
  fail "failed-START recovery receipt is not a fresh confirmed admission"
supervisor=mini-spk-supervisor@$(basename "$(dirname "$STATE")")-$APP.service
tick=0
until [ "$("$FOS/systemctl" show "$supervisor" --property=ActiveState --value)" != active ]; do
  tick=$((tick + 1)); [ "$tick" -lt 600 ] || fail "supervisor $supervisor did not finish"
  sleep 0.2
done

# The next START repeats the create under the governed v4 retry.
sh "$J" phase "$JRUN" start-a2 || fail "retried START failed (see $JRUN/evidence/start-a2.stderr)"
RETRY=$((FAILED + 2))
COMPLETED=$APPDIR/g$RETRY/start-completed-retry-v4.json
[ -s "$COMPLETED" ] || fail "g$RETRY has no retry-v4 completion"
jq -e '.startAction == {kind:"create",index:0}' "$APPDIR/g$RETRY/resident.json" >/dev/null ||
  fail "the retried START was not the repeat create"

stop_all
trap - EXIT
jq -n --arg run "$RUN" --arg fos "$FOS" --arg state "$STATE" --arg profile "$PROFILE" \
  --arg app "$APP" --arg failed "$FAILED" --arg retry "$RETRY" \
  --arg config "$JRUN/store/base/workroom/deployment/pinned-config.json" \
  --arg host "$BIN/minidregg-host" --arg mini "$BIN/mini" \
  --slurpfile recovered "$RECOVERED" --slurpfile completed "$COMPLETED" '
  {protocol:"mini-spk-fixture-v4-chronology-v1",runRoot:$run,fixtureOs:$fos,
   stateRoot:$state,profile:$profile,app:$app,failedGeneration:$failed,
   retryGeneration:$retry,miniConfig:$config,host:$host,mini:$mini,
   recovery:$recovered[0],retryCompletion:$completed[0]}' >"$RUN/fixture.json"
echo "fixture-v4: recorded $RUN/fixture.json"
