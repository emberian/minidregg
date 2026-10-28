#!/usr/bin/env bash
# Actual Mini receiving journey: a new private Store, signed runtime install,
# current share/enrollment and dispatch, two grains, refusal and restart.
# Cross-file globals come from world.sh; redirects deliberately stay operator-owned.
# shellcheck disable=SC2024,SC2154,SC2174
set -euo pipefail
umask 077
invocation_args=("$@")
usage() {
  cat <<'HELP'
usage: scripts/oracle-shared-data-journey.sh [--resume|--continue-controller|--continue-session|--continue-activation|--recover-application-api REQUEST_ID|--continue-checkpoint CHECKPOINT_JSON|--recover-foreground PLAN_JSON] BASE_BIN OWN_BIN RUN_ROOT SIGNED_RUNTIME_SPK DATA_SOURCE INVENTORY_JSON

Linux operator account with user systemd/linger, subordinate UID/GID allocation,
passwordless access to deploy/spk-host/install-user-world, bwrap, jq, curl, python3.
BASE_BIN: qualified Host, mini, sqlite-store, signature verifier, client consent.
OWN_BIN: current spk-host, mini-spk-broker, mini-spk-volume-helper, spk-data-publish, grain-runtime.
All paths absolute; NEW_RUN_ROOT must have protected ancestors. Without --resume
it must not exist. --resume requires the exact U3 initial allocation/authoring
selectors and a retained prepared INSTALL; older receiving-only worlds refuse.
--continue-controller requires the exact preserved pre-START controller-create
failure after both installs, publication and share. It never repeats those phases.
--continue-session preserves the definite null-operation session refusal, applies
qualified stopped-controller repairs, and uses a new tool ID after native enrollment.
Its --resume-prepared suffix is limited to the recorded source-manifest refusal
with a durable backup, identical stopped state, and no repair or tool attempt.
--continue-activation preserves an admitted session/grant and failed pre-commit
route enrollment. It upgrades the stopped runtime, supervises the dead app into
a native STOP and successor START, then enrolls a newly checked route.
--continue-checkpoint accepts an explicitly sealed unstarted phase boundary;
completed effects remain retained and any started phase requires inspection.
--recover-foreground requires an independently qualified binary manifest and
an explicitly reviewed recovery plan for the retained uncertain session. It
invokes one native recovery of the same foreground ID and parent reservation;
it never resends the tool request. A failed recovery remains inspect-only.
Creates and removes only a fresh scratch Store namespace. Keeps evidence in RUN.
The input data is read only; publication copies it once into this Store's custody.
No public deployment and no direct fd3 calls. Uses the same current receiving
path as the grain API: event22 share, event28 enrollment and admitted dispatch.
ORACLE_STOP_BENCHMARK_JSON must name the qualified same-Host copied-Store cold/served receipt.
Fresh STOP probes check resident refresh and refusals, without duplicate cold walks.
Run inside a bounded operator unit, e.g. RuntimeMaxSec=10800 CPUQuota=200%.
HELP
}
[[ ${1:-} != --help ]] || { usage; exit 0; }
mode=new
checkpoint=
recovery_plan=
session_resume_prepared=0
case ${1:-} in
  --resume) mode=resume; shift ;;
  --continue-controller) mode=continue-controller; shift ;;
  --continue-session) mode=continue-session; shift ;;
  --continue-activation) mode=continue-activation; shift ;;
  --recover-application-api) mode=recover-application-api; api_recovery_request=${2:?request ID required}; shift 2 ;;
  --continue-checkpoint) mode=continue-checkpoint; checkpoint=${2:?checkpoint required}; shift 2 ;;
  --recover-foreground) mode=recover-foreground; recovery_plan=${2:?recovery plan required}; shift 2 ;;
esac
if [[ ${1:-} == --resume-prepared ]]; then
  [[ $mode == continue-session ]] || { usage >&2; exit 2; }
  session_resume_prepared=1; shift
fi
[[ $# == 6 ]] || { usage >&2; exit 2; }
base=$1 own=$2 run=$3 spk=$4 source=$5 inventory=$6
benchmark=${ORACLE_STOP_BENCHMARK_JSON:?qualified copied-Store STOP benchmark receipt required}
repo=$(cd "$(dirname "$0")/.." && pwd)
journey=$repo/scripts/spk-platform/grain-journey.sh
fail() { echo "Oracle shared-data journey: $*" >&2; exit 1; }
[[ $(uname -s) == Linux ]] || fail 'Linux required'
for path in "$base" "$own" "$run" "$spk" "$source" "$inventory" "$benchmark"; do
  [[ $path == /* && $path != *[!a-zA-Z0-9_./-]* && $path != */../* && $path != */./* && $path != *//* ]] || fail "simple absolute canonical path required: $path"
done
if [[ $mode != new ]]; then
  if [[ -z ${ORACLE_ACCEPTANCE_LOCK_FD:-} ]]; then
    exec python3 -B "$repo/deploy/oracle/acceptance/continue_controller.py" \
      --locked-exec "$run" bash "$0" "${invocation_args[@]}"
  fi
  python3 -B "$repo/deploy/oracle/acceptance/continue_controller.py" --verify-lock "$run"
fi
if [[ $mode == new ]]; then
  [[ ! -e $run && ! -L $run ]] || fail 'run directory already exists'
else
  if [[ $mode == continue-session || $mode == continue-activation || $mode == recover-application-api || $mode == continue-checkpoint || $mode == recover-foreground ]]; then
    python3 -B "$repo/deploy/oracle/acceptance/continue_controller.py" --check-session-custody "$run" >/dev/null
  else
    [[ -d $run && ! -L $run && $(stat -c '%u:%a' "$run") == "$(id -u):700" ]] || fail 'retained run custody differs'
  fi
  # This recipe cannot extend historical receiving-only worlds. Check the
  # exact fresh U3 allocation and initial authoring selectors before any phase.
  python3 - "$run" "$repo/deploy/oracle/acceptance/agent-allocation.json" <<'PYRESUME'
import json, pathlib, sys
run, source = map(pathlib.Path, sys.argv[1:])
raw = source.read_bytes()
for retained in ('agent-lifetime/allocation.json', 'world/store/source-stage/agent-allocation.json'):
    path = run / retained
    if not path.is_file() or path.is_symlink() or path.read_bytes() != raw:
        raise SystemExit('resume refused: exact initial U3 agent allocation absent')
a = json.loads(raw)
expected = []
for agent in a['agents']:
    c = agent['plannedCaps']
    expected.append({'legacy': {
        'ticketResource': int(agent['ticket']), 'packageManifest': int(a['packageManifest']),
        'snapshotManifest': int(a['snapshotManifest']), 'sessionObserve': int(c['sessionOwner']),
        'manifestObserve': int(c['controllerManifestObserve']), 'enrollmentObserve': int(c['descriptorOwner']),
        'parentTask': int(agent['controller']['task']), 'parentCapability': int(c['parentOwner']),
        'parentObserve': int(c['parentOwner']), 'purseTask': int(agent['dispatch']['task']),
        'purseCapability': int(c['dispatchOwner']), 'purseObserve': int(c['dispatchOwner']),
        'payerSubject': int(agent['dispatch']['subject']), 'reserveAmount': 1, 'maximumCharge': 1},
        'grantResource': int(agent['persistentGrant']), 'grantObserveCapability': int(c['grantObserve'])})
config = json.loads((run / 'world/store/base/workroom/deployment/pinned-config.json').read_bytes())
if config.get('agentLifetimeDispatchTargets') != expected:
    raise SystemExit('resume refused: initial U3 lifetime authoring selectors differ')
if not (run / 'bin/grain-runtime').is_file():
    raise SystemExit('resume refused: retained U3 controller runtime absent')
PYRESUME
  if [[ $mode == resume ]]; then
    [[ -f $run/initial-attempt/input-sha256.txt ]] || fail 'preserve original attempt evidence before resume'
    [[ $(sha256sum "$spk" | cut -d ' ' -f1) == $(awk 'NR==1{print $1}' "$run/initial-attempt/input-sha256.txt") ]] || fail 'resume package differs'
    [[ $(sha256sum "$inventory" | cut -d ' ' -f1) == $(awk 'NR==2{print $1}' "$run/initial-attempt/input-sha256.txt") ]] || fail 'resume inventory differs'
    sha256sum -c "$run/binary-sha256.txt" >"$run/resume-binary-check.txt"
  fi
fi
for tool in jq curl python3 sha256sum timeout; do command -v "$tool" >/dev/null || fail "missing $tool"; done
[[ $mode != new ]] || command -v getfacl >/dev/null || fail 'missing getfacl'
ancestor=$(dirname "$run")
while :; do
  [[ -d $ancestor && ! -L $ancestor ]] || fail "ancestor absent or linked: $ancestor"
  ancestor_mode=$(stat -c '%a' "$ancestor")
  (( (8#$ancestor_mode & 8#022) == 0 )) || fail "writable ancestor: $ancestor"
  # controller-stage grants traversal only on private ancestors. Its existing
  # guard refuses extended ACLs rather than changing another world's access.
  # Detect that same conflict before genesis or a large data publication.
  if [[ $mode == new ]] && (( (8#$ancestor_mode & 1) == 0 )); then
    ancestor_acl=$(getfacl -c -p -n -- "$ancestor") || fail "cannot inspect ancestor ACL: $ancestor"
    if printf '%s\n' "$ancestor_acl" | awk '/^(mask:|default:|(user|group):[^:]+:)/ { found=1 } END { exit !found }'; then
      fail "private ancestor has extended ACL: $ancestor; use an independent run root outside preserved worlds"
    fi
  fi
  [[ $ancestor == / ]] && break
  ancestor=$(dirname "$ancestor")
done
[[ -f $spk && ! -L $spk && -f $inventory && ! -L $inventory && -d $source && ! -L $source ]] || fail 'inputs absent or linked'
[[ -f $benchmark && ! -L $benchmark ]] || fail 'qualified STOP benchmark absent or linked'
# Refuse a receipt from an older Host before creating a Store or copying data.
# The final report still checks the full cold/served comparison and controls.
[[ -f $base/minidregg-host && -x $base/minidregg-host ]] || fail 'Host executable absent'
jq -e --arg host "$(sha256sum "$base/minidregg-host" | cut -d ' ' -f1)" '
  .schema == "mini-stop-inspection-continuation-v1" and .passed == true
  and .host_sha256 == $host
' "$benchmark" >/dev/null || fail 'STOP benchmark must qualify the selected Host binary'
[[ $(stat -c '%s' "$spk") -le 268435456 ]] || fail 'runtime exceeds Mini signed package admission cap'
# The publisher, signed package inspector and Mini decide identity/acceptance.
# These are preflight and evidence pins only.
inventory_sha=$(sha256sum "$inventory" | cut -d ' ' -f1)
export SPK=$spk CLASS_A=L CLASS_B=L GET_PATH_A=/health GET_PATH_B=/health
export KIND_A=api KIND_B=api ROLE_BASIS_A='{"type":"role","id":"0"}' ROLE_BASIS_B='{"type":"role","id":"0"}'
if [[ ${ORACLE_BROWSER_B:-0} == 1 ]]; then
  [[ $mode == new || $mode == continue-activation || $mode == recover-application-api ]] || fail 'browser-B requires a fresh or unstarted activation qualification'
  [[ ${ORACLE_BROWSER_PORT:-} =~ ^[1-9][0-9]{3,4}$ ]] && ((ORACLE_BROWSER_PORT>=1024 && ORACLE_BROWSER_PORT<=65535)) || fail 'explicit browser port required'
  [[ ${ORACLE_CADDY_BIN:-} == /* && -x $ORACLE_CADDY_BIN && ! -L $ORACLE_CADDY_BIN
      && ${ORACLE_CADDY_SHA256:-} =~ ^[0-9a-f]{64}$ ]] || fail 'pinned Caddy executable required'
  [[ $(sha256sum "$ORACLE_CADDY_BIN" | cut -d ' ' -f1) == "$ORACLE_CADDY_SHA256" ]] || fail 'Caddy pin differs'
  export KIND_B=web GRAIN_EXPECTED_HOST_B=localhost:$ORACLE_BROWSER_PORT
elif [[ ${ORACLE_BROWSER_B:-0} != 0 ]]; then
  fail 'ORACLE_BROWSER_B must be 0 or 1'
fi
case ${ORACLE_POOLED_TENANT_PROBE:-0} in
  0) ;;
  1) [[ $mode == new || $mode == continue-activation || $mode == recover-application-api ]] || fail 'pooled tenant probe requires a fresh or unstarted activation qualification' ;;
  *) fail 'ORACLE_POOLED_TENANT_PROBE must be 0 or 1' ;;
esac
export POST_PATH_A=/query POST_PATH_B=/query POST_TYPE_A=application/json POST_TYPE_B=application/json
. "$repo/deploy/oracle/acceptance/world.sh"
configured=0
preserve_existing_exit=0
[[ $mode != continue-controller && $mode != continue-session && $mode != continue-activation && $mode != recover-application-api && $mode != continue-checkpoint && $mode != recover-foreground ]] || preserve_existing_exit=1
trap world_cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
export ORACLE_IMPORT_PROFILE=${ORACLE_IMPORT_PROFILE:-operator-appliance-v1}
case "$ORACLE_IMPORT_PROFILE" in standard-v1|market-large-v1|operator-appliance-v1) ;; *) fail 'unknown operator import profile';; esac
controller_create_verb=controller-create
if [[ $mode == recover-foreground ]]; then
  world_recover_foreground "$run" "$repo"
  # A recovered definite refusal concludes this retained failed journey. It
  # never creates a grant or starts an application; cleanup preserves the Store.
  if [[ ${foreground_settlement_only:-0} == 1 ]]; then exit 0; fi
elif [[ $mode == recover-application-api ]]; then
  world_recover_application_api
elif [[ $mode == continue-activation ]]; then
  world_continue_activation "$run" "$repo"
elif [[ $mode == continue-checkpoint ]]; then
  world_continue_checkpoint "$run" "$repo"
elif [[ $mode == continue-session ]]; then
  world_continue_session "$run" "$repo"
elif [[ $mode == continue-controller ]]; then
  world_continue_controller "$run" "$repo"
else
disk_plan=$(world_disk_plan) || fail 'fresh journey does not fit unchanged import and later verification space guards'
if [[ $mode == new ]]; then
  world_prepare "$base" "$own" "$run" "$repo"
else
  world_resume "$run" "$repo"
fi
printf '%s\n' "$disk_plan" >"$run/disk-plan.json"
jq --argjson bytes "$(stat -c '%s' "$spk")" '
  {selected_profile:(.importProfile // "standard-v1"),
   deadline_seconds:(([60 + 3 * (($bytes + 1048575) / 1048576 | floor), (if .importProfile=="standard-v1" or .importProfile==null then 900 else 1800 end)] | min)),
   signed_spk_bytes:$bytes,mini_raw_admission_cap_bytes:268435456}'   "$GRAINS_ROOT/broker/config.json" >"$run/import-profile.json"
{
  sha256sum "$spk" "$inventory" "$benchmark"
  world_source_manifest
} >"$run/input-sha256.txt"
cp "$inventory" "$run/inventory.json"
cp "$benchmark" "$run/copied-store-stop-benchmark.json"
fi
phase() { timeout 1800 "$journey" phase "$run/world" "$@"; }
if [[ $mode != continue-controller && $mode != continue-session && $mode != continue-activation && $mode != recover-application-api && $mode != continue-checkpoint && $mode != recover-foreground ]]; then
# INSTALL does not launch the app or open its signed data attachment. Complete
# both installations while the large-profile spool reserve is available, then
# publish data before either START. The native guards remain unchanged.
world_disk_snapshot before-install
phase birth-a install-a birth-b install-b
world_disk_snapshot after-install
# Publication is physical custody; it does not manufacture a Mini grant.
timeout 3600 "$BIN/spk-data-publish" publish --store "$GRAINS_ROOT/spk/public-data" \
  --source "$source" --inventory "$inventory" >"$run/publication.json" 2>"$run/publication.stderr"
publication=$GRAINS_ROOT/spk/public-data/sha256-$inventory_sha
[[ -d $publication && ! -L $publication ]] || fail 'publisher did not produce exact inventory slot'
world_disk_snapshot after-publication
phase share-a
fi
publication=$GRAINS_ROOT/spk/public-data/sha256-$inventory_sha
if [[ $mode != continue-session && $mode != continue-activation && $mode != recover-application-api && $mode != continue-checkpoint && $mode != recover-foreground ]]; then world_controller_prepare; fi
if [[ $mode == continue-checkpoint || $mode == recover-foreground ]]; then world_phase_record admitted-application-journey started; fi
if [[ $mode == continue-activation || $mode == recover-application-api ]]; then
  world_controller_activate "$continuation/successor-start.json" initial
  world_phase_record enrollment completed "$run/agent-lifetime/enrollment-initial/result.json"
else
  phase start-a
  world_controller_activate "$run/world/evidence/start-a.stdout" initial
fi
world_controller_probe initial probe
world_authority_probe
phase floor-a enroll-a get-a
# This HTTP route invokes the current Mini request admission on every call.
# A process/socket existing is not counted as admission or query success.
request() {
  local letter=$1 label=$2 id=$3 conversation=$4 question=$5
  local body
  body=$(jq -nc --arg id "$id" --arg conversation "$conversation" --arg question "$question" \
    '{request_id:$id,conversation_id:$conversation,text:$question}')
  if [[ $letter == a ]]; then export POST_BODY_A=$body; else export POST_BODY_B=$body; fi
  phase "post-$letter$label"
}
if [[ ${ORACLE_POOLED_TENANT_PROBE:-0} == 1 ]]; then
  jq -n '{protocol:"mini-oracle-pooled-tenant-probe-v1",app:"9101",path:"/query",
    request:{request_id:"mini-u3-weather-structured",conversation_id:"mini-owner-pool-collision",text:"Who wrote Leaves of Grass?"}}' \
    >"$run/pooled-tenant-probe-request.json"
  request a 15 mini-u3-weather-structured mini-owner-pool-collision 'Who wrote Leaves of Grass?'
fi
request a 1 oracle-isolation oracle-acceptance 'Who wrote Leaves of Grass?'
request a 2 oracle-austen oracle-followup 'Who wrote Emma?'
request a 3 oracle-pronoun oracle-followup 'When was she born?'
request a 4 oracle-isa oracle-weather 'ISA temperature at 3,000 m altitude?'
request a 5 oracle-bad-units oracle-weather 'ISA temperature at 3,000 m/s altitude?'
request a 9 oracle-mars-supplied oracle-mars 'Earth takes 365.25 days to orbit the Sun and Mars takes 687 days. How many Earth years are 3 Mars years?'
request a 10 oracle-shakespeare oracle-dates 'When was William Shakespeare born?'
request a 11 oracle-salinger oracle-dates 'When was J. D. Salinger born?'
request a 12 oracle-order-salinger oracle-order-salinger 'Who is older, J. D. Salinger or Jimmy Carter?'
request a 13 oracle-order-shakespeare oracle-order-shakespeare 'Who is older, William Shakespeare or Isaac Newton?'
request a 14 oracle-order-uncertain oracle-order-uncertain 'Who is older, Hildegard of Bingen or William Shakespeare?'
phase share-b start-b floor-b enroll-b get-b
if [[ ${ORACLE_BROWSER_B:-0} == 1 ]]; then world_browser_probe; fi
# Reusing both IDs with a different body would conflict in a shared journal.
request b 1 oracle-isolation oracle-acceptance 'Who wrote Emma?'
request a 6 oracle-isolation oracle-acceptance 'Who wrote Leaves of Grass?'
cmp "$run/world/evidence/post-a1-body.body" "$run/world/evidence/post-a6-body.body"
"$BIN/spk-host" grain status "$profile" 9101 >"$run/before-stop-a.json"
"$BIN/spk-host" grain status "$profile" 9201 >"$run/before-stop-b.json"
# Keep the native configs/receipts before the scratch namespace is removed.
mkdir -m 700 "$run/receiving"
retain() {
  local app=$1 generation configfile image_dir
  for configfile in "$state/apps/$app"/g*/resident.json; do
    [[ -f $configfile ]] || continue
    generation=$(basename "$(dirname "$configfile")")
    mkdir -p -m 700 "$run/receiving/$app/$generation"
    cp "$configfile" "$run/receiving/$app/$generation/resident.json"
    for file in "$(dirname "$configfile")"/*completed*.json "$(dirname "$configfile")"/*admitted*.json; do
      [[ ! -f $file ]] || cp "$file" "$run/receiving/$app/$generation/"
    done
    if [[ -d $(dirname "$configfile")/stop-completion ]]; then
      cp -a "$(dirname "$configfile")/stop-completion" "$run/receiving/$app/$generation/"
    fi
  done
  cp "$state/apps/$app/install/launch-descriptor/launch-inspection.json" "$run/receiving/$app/launch-inspection.json"
  cp "$state/apps/$app/install/install-completed-v2.json" "$run/receiving/$app/install-completed-v2.json"
  image_dir=$(jq -er .imageDir "$state/apps/$app/install/install.json")
  cp "$image_dir/import-policy.json" "$run/receiving/$app/import-policy.json"
  cp "$image_dir/root/opt/oracle/APPLIANCE.json" "$run/receiving/$app/APPLIANCE.json"
  cp "$image_dir/root/minidregg-data.json" "$run/receiving/$app/minidregg-data.json"
}
retain 9101; retain 9201
# Native config and Linux mount evidence: inspect only processes in these two
# Store-qualified units. sudo is read-only here, never a mount or app launch.
read_proc_evidence() {
  local path=$1 output=$2
  # Some qualified hosts permit the operator's namespace-parent observation;
  # hosts with stricter proc policy use their existing read-only sudo grant.
  cat "$path" >"$output" 2>/dev/null || sudo -n cat "$path" >"$output"
}
capture_mounts() {
  local app=$1 unit cg pid resident
  unit=$("$BIN/spk-host" grain status "$profile" "$app" | jq -er '[.runs[] | select(.state=="running")][-1].unit')
  cg=$(systemctl --user show "$unit" -p ControlGroup --value)
  mkdir -p -m 700 "$run/receiving/$app/mounts"
  mkdir -p -m 700 "$run/receiving/$app/namespaces"
  resident=$(systemctl --user show "$unit" -p MainPID --value)
  [[ $resident =~ ^[1-9][0-9]*$ ]] || fail 'running resident PID absent'
  read_proc_evidence "/proc/$resident/uid_map" "$run/receiving/$app/namespaces/$resident.uid_map"
  read_proc_evidence "/proc/$resident/gid_map" "$run/receiving/$app/namespaces/$resident.gid_map"
  while read -r pid; do
    [[ $pid =~ ^[1-9][0-9]*$ ]] || continue
    read_proc_evidence "/proc/$pid/mountinfo" "$run/receiving/$app/mounts/$pid.txt" || fail 'cannot inspect app mount custody'
  done <"/sys/fs/cgroup$cg/cgroup.procs"
}
capture_mounts 9101; capture_mounts 9201
a_generation=$(jq -er '[.runs[] | select(.state=="running")][-1].generation' "$run/before-stop-a.json")
world_controller_stop before-app-stop
phase stop-a
world_reclaim_stopped_agent_socket 9101 "$a_generation" before-data-refusals
world_operator_identity >"$run/op155-operator-before.json"
world_stop_probe 9101 "$a_generation" "$run/op155-a"
world_operator_identity >"$run/op155-operator-after-a.json"
cmp "$run/op155-operator-before.json" "$run/op155-operator-after-a.json"
# These mutations affect only this journey's freshly published directory.
# Rename preserves the original files/inodes/fingerprints exactly for restore.
held=$GRAINS_ROOT/spk/public-data/withheld-$inventory_sha
mv "$publication" "$held"
restore_publication() {
  if [[ -d $held ]]; then
    [[ ! -d $publication ]] || mv "$publication" "$run/wrong-publication"
    mv "$held" "$publication"
  fi
}
# Restore before cleanup even after any negative-test failure.
trap 'original=$?; restore_publication; world_cleanup "$original"' EXIT
refuse_start() {
  local label=$1 result failed_unit invocation
  "$BIN/spk-host" grain status "$profile" 9101 >"$run/$label-before.json"
  set +e
  timeout 120 "$BIN/spk-host" grain start "$profile" 9101 >"$run/$label.stdout" 2>"$run/$label.stderr"
  result=$?
  set -e
  [[ $result != 0 && $result != 124 ]] || fail "$label did not refuse promptly"
  printf '%s\n' "$result" >"$run/$label.exit"
  "$BIN/spk-host" grain status "$profile" 9101 >"$run/$label-after.json"
  jq -e 'all(.runs[]; .state == "stopped" or .state == "never-begun")' "$run/$label-after.json" >/dev/null || fail "$label left live or uncertain lifecycle"
  : >"$run/$label.unit.log"
  while read -r failed_unit; do
    [[ $failed_unit == mini-spk-s$store-a9101-g*.service ]] || fail 'refusal unit outside this Store'
    invocation=$(systemctl --user show "$failed_unit" -p InvocationID --value)
    if [[ $invocation =~ ^[0-9a-f]{32}$ ]]; then
      journalctl --user --no-pager -u "$failed_unit" "_SYSTEMD_INVOCATION_ID=$invocation" >>"$run/$label.unit.log"
    else fail 'failed resident invocation identity absent'; fi
  done < <(jq -r '.runs[] | select(.state=="never-begun") | .unit' "$run/$label-after.json")
  [[ -z $(systemctl --user list-units --state=running --plain --no-legend "mini-spk-s$store-a9101-*.service") ]] || fail "$label launched a resident"
}
refuse_start missing-data
mkdir -m 755 "$publication"
jq '.files[0].sha256 = ("0" * 64)' "$held/inventory.json" >"$publication/inventory.json"
cp "$held/receipt.json" "$publication/receipt.json"
chmod 444 "$publication/inventory.json" "$publication/receipt.json"
mkdir -m 555 "$publication/data"
# Match a real publication's immutable directory modes so this case reaches
# the signed inventory mismatch instead of stopping at a custody-mode refusal.
chmod 555 "$publication"
refuse_start wrong-data
grep -q "published inventory differs from signed attachment digest" "$run/wrong-data.stderr" "$run/wrong-data.unit.log" || fail 'wrong inventory refused for an unrelated reason'
restore_publication
phase start-a2
world_controller_activate "$run/world/evidence/start-a2.stdout" restart
world_controller_probe restart probe-after-restart
phase floor-a2 enroll-a2 get-a2
capture_mounts 9101
request a 7 oracle-isolation oracle-acceptance 'Who wrote Leaves of Grass?'
cmp "$run/world/evidence/post-a1-body.body" "$run/world/evidence/post-a7-body.body"
request a 8 oracle-pronoun oracle-followup 'When was she born?'
cmp "$run/world/evidence/post-a3-body.body" "$run/world/evidence/post-a8-body.body"
request b 2 oracle-isolation oracle-acceptance 'Who wrote Emma?'
cmp "$run/world/evidence/post-b1-body.body" "$run/world/evidence/post-b2-body.body"

# Reproduce the prior recovery gap in this fresh Store: physically stop B's
# exact owned unit while retaining its completed START/Running journal, then
# ask the normal source-bound STOP path to reconcile that same incarnation.
mkdir -m 700 "$run/reconcile-b"
"$BIN/spk-host" grain status "$profile" 9201 >"$run/reconcile-b/before.json"
generation=$(jq -er '[.runs[] | select(.state=="running")][-1].generation' "$run/reconcile-b/before.json")
unit=$(jq -er '[.runs[] | select(.state=="running")][-1].unit' "$run/reconcile-b/before.json")
[[ $generation =~ ^[1-9][0-9]*$ && $unit == mini-spk-s$store-a9201-g$generation.service ]] || fail 'reconciliation target outside this Store'
cp "$state/apps/9201/g$generation/record.json" "$run/reconcile-b/record-before.json"
systemctl --user show "$unit" -p Id -p LoadState -p ActiveState -p MainPID -p InvocationID -p ControlGroup -p Job >"$run/reconcile-b/manager-before.txt"
timeout 120 systemctl --user stop "$unit"
systemctl --user show "$unit" -p Id -p LoadState -p ActiveState -p MainPID -p InvocationID -p ControlGroup -p Job >"$run/reconcile-b/manager-inactive.txt"
cp "$state/apps/9201/g$generation/record.json" "$run/reconcile-b/record-inactive.json"
cmp "$run/reconcile-b/record-before.json" "$run/reconcile-b/record-inactive.json"
"$BIN/spk-host" grain status "$profile" 9201 >"$run/reconcile-b/after-manager.json"
phase stop-b
world_operator_identity >"$run/op155-operator-before-b.json"
cmp "$run/op155-operator-before.json" "$run/op155-operator-before-b.json"
world_stop_probe 9201 "$generation" "$run/op155-b" \
  "$state/apps/9101/g$a_generation/stop-claim/committed-v3.bin"
world_operator_identity >"$run/op155-operator-after-b.json"
cmp "$run/op155-operator-before.json" "$run/op155-operator-after-b.json"
"$BIN/spk-host" grain status "$profile" 9201 >"$run/reconcile-b/after-native-stop.json"
cp "$state/apps/9201/g$generation/record.json" "$run/reconcile-b/record-stopped.json"
phase start-b2 floor-b2 enroll-b2 get-b2
capture_mounts 9201
request b 3 oracle-isolation oracle-acceptance 'Who wrote Emma?'
cmp "$run/world/evidence/post-b1-body.body" "$run/world/evidence/post-b3-body.body"
retain 9101; retain 9201
world_controller_stop before-final-stops
phase stop-a2 stop-b2 status-a status-b
world_reclaim_stopped_agent_socket 9101 "$(jq -er .generation "$run/world/evidence/stop-a2.stdout")" final-stop
retain 9101; retain 9201
world_disk_snapshot after-stops
sha256sum -c "$run/input-sha256.txt" >"$run/input-recheck.txt"
if [[ -n ${continuation:-} ]]; then
  sha256sum -c "${recovery_manifest:-$continuation/recovery-input-sha256.txt}" >"$continuation/recovery-input-recheck.txt"
fi
if [[ -f $run/resume-retained-install-sha256.txt ]]; then
  sha256sum -c "$run/resume-retained-install-sha256.txt" >"$run/resume-retained-install-recheck.txt"
fi
journalctl --user --no-pager -u "mini-spk-ingest-s$store-*.service" -o json >"$run/import-units.jsonl"
python3 "$repo/deploy/oracle/acceptance/report.py" "$run" "$inventory_sha"
if [[ $mode == continue-checkpoint || $mode == recover-foreground ]]; then world_phase_record admitted-application-journey completed "$run/report.json"; fi
echo "Oracle shared-data acceptance passed: $run/report.json"
