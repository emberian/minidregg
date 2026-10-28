#!/usr/bin/env bash
# Cross-file globals are intentional; sudo output remains operator-owned.
# shellcheck disable=SC2024,SC2034,SC2154,SC2174
# Sourced by the Oracle journey. This is a transport/fixture harness only;
# Mini's Host and broker remain the authority and physical-custody receivers.
# Every root effect uses the existing fixed deployment installer/helper.

# One source list for both fresh and continued execution. Immutable snapshot
# manifests cover the remaining inherited tree; these are the direct runtime
# helpers and fixture inputs selected by this harness.
world_source_manifest() {
  sha256sum "$repo/scripts/oracle-shared-data-journey.sh" \
    "$repo/deploy/oracle/acceptance/world.sh" "$repo/deploy/oracle/acceptance/report.py" "$repo/deploy/oracle/acceptance/browser_edge.py" \
    "$repo/deploy/oracle/acceptance/continue_controller.py" "$repo/deploy/oracle/acceptance/recover_foreground.py" "$repo/deploy/oracle/acceptance/recover_activation.py" "$repo/deploy/oracle/acceptance/recover_application_api.py" "$repo/deploy/oracle/acceptance/volume_cleanup.py" \
    "$repo/deploy/oracle/acceptance/agent.py" "$repo/deploy/oracle/acceptance/agent-cases.json" \
    "$repo/deploy/oracle/acceptance/agent-allocation.json" "$repo/scripts/oracle-agent-lifetime-journey.sh" \
    "$repo/scripts/oracle-stop-inspection-probe.py" "$repo/scripts/oracle-agent-authority-probe.py" \
    "$repo/scripts/spk-platform/grain-journey.sh" "$repo/scripts/spk-platform/grain-store.sh" \
    "$repo/scripts/spk-platform/prepare-lifetime-route.sh" "$repo/scripts/spk-platform/check-agent-allocation.sh" \
    "$repo/scripts/workroom/agent-enrollment.sh" \
    "$repo/deploy/spk-host/install-user-world" "$repo/deploy/spk-host/controller-world.py"
}

# Capacity accounting only. The native materializer and verifier independently
# apply their unchanged statvfs guards; this does not reserve or grant space.
world_disk_plan() {
  python3 - "$spk" "$inventory" "$ORACLE_IMPORT_PROFILE" /var/lib/mini-spk-worlds <<'PY'
import json, os, pathlib, sys
spk, inventory, profile, root = sys.argv[1:]
raw = pathlib.Path(spk).stat().st_size
data = sum(f['size'] for f in json.loads(pathlib.Path(inventory).read_bytes())['files'])
decoded = (20 * 1024**3 if profile == 'operator-appliance-v1' else 768 * 1024**2)
s = os.statvfs(root)
available = s.f_bavail * s.f_frsize
materialize_guard = 2 * raw + 2 * decoded
verify_guard = raw + decoded
# Source qualification still uses the standard decoded cap for this runtime.
# Plan for both full 2-GiB volumes, inbox+retained SPK, the maximum qualified
# extracted image, and 64 MiB for Store/metadata. Large import spools are gone
# before dataset publication begins.
retained_allowance = data + 4 * 1024**3 + 2 * raw + 768 * 1024**2 + 64 * 1024**2
projected = available - retained_allowance
plan = {'schema': 'mini-oracle-disk-plan-v1', 'filesystem_path': root,
        'available_bytes': available, 'runtime_spk_bytes': raw,
        'dataset_bytes': data, 'materialize_guard_bytes': materialize_guard,
        'verify_guard_bytes': verify_guard, 'retained_allowance_bytes': retained_allowance,
        'projected_available_after_publication': projected,
        'order': 'install-both-before-publication', 'reservation': False,
        'fits': available >= materialize_guard and projected >= verify_guard}
print(json.dumps(plan, indent=2))
if not plan['fits']:
    raise SystemExit(1)
PY
}

world_disk_snapshot() {
  python3 - "$GRAINS_ROOT" "$run/disk-$1.json" <<'PY'
import json, os, pathlib, sys, time
root, output = sys.argv[1:]
s = os.statvfs(root)
pathlib.Path(output).write_text(json.dumps({'path': root, 'unix_seconds': time.time(),
    'available_bytes': s.f_bavail * s.f_frsize, 'free_bytes': s.f_bfree * s.f_frsize}, indent=2) + '\n')
PY
}

# Pin the actual existing operator process across the two read-only inspection
# boundaries. PID alone is insufficient because it can be reused.
world_operator_identity() {
  python3 - "$run/world/sock/operator.pid" <<'PYIDENTITY'
import json, pathlib, sys
pid = int(pathlib.Path(sys.argv[1]).read_text())
proc = pathlib.Path('/proc') / str(pid)
fields = (proc / 'stat').read_text().rsplit(')', 1)[1].split()
print(json.dumps({'pid': pid, 'start_ticks': int(fields[19]),
                  'executable': str((proc / 'exe').resolve(strict=True))}, sort_keys=True))
PYIDENTITY
}

world_stop_probe() {
  local app=$1 generation=$2 output=$3 previous_claim=${4:-}
  local args=()
  [[ -z $previous_claim ]] || args+=(--mismatched-committed "$previous_claim")
  timeout 1800 python3 "$repo/scripts/oracle-stop-inspection-probe.py" \
    --host "$BIN/minidregg-host" --config "$config" \
    --operator-socket "$run/world/sock/operator/host.sock" \
    --public-socket "$run/world/sock/participant/host.sock" \
    --plan "$state/apps/$app/g$generation/stop-claim/stop-plan-v2.bin" \
    --committed "$state/apps/$app/g$generation/stop-claim/committed-v3.bin" \
    --out "$output" --deadline 1200 --resident-only "${args[@]}" >"$output.stdout" 2>"$output.stderr"
}

world_browser_probe() {
  timeout 1850 python3 -B "$repo/deploy/oracle/acceptance/browser_edge.py" run "$run" "$state" \
    "$ORACLE_CADDY_BIN" "$ORACLE_CADDY_SHA256" "$ORACLE_BROWSER_PORT" \
    >"$run/browser-probe.stdout" 2>"$run/browser-probe.stderr"
}


world_controller_prepare() {
  local home
  timeout 120 sudo -n -- "$installer" "$controller_create_verb" "$store" "$helper" >"$run/agent-lifetime/controller-create.json"
  controller_created=1
  if [[ $controller_create_verb == controller-resume-create ]]; then
    jq -e --argjson expected "$(jq -er .controller_uid "$continuation/prepared.json")" \
      '.resumedPendingCreation == true and .controllerUid == $expected' \
      "$run/agent-lifetime/controller-create.json" >/dev/null || fail 'pending controller identity changed'
  fi
  cp "$GRAINS_ROOT/controller/namespace.json" "$run/agent-lifetime/controller-namespace.json"
  home=$(jq -er .controllerHome "$run/agent-lifetime/controller-create.json")
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" prepare-controller "$run" "$repo" "$home" \
    >"$run/agent-lifetime/prepare-controller.stdout" 2>"$run/agent-lifetime/prepare-controller.stderr"
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" prepare-worker-policy "$run" "$repo" \
    "$run/agent-lifetime/controller-stage/controller.json" \
    >"$run/agent-lifetime/worker-policy.stdout" 2>"$run/agent-lifetime/worker-policy.stderr"
  timeout 120 sudo -n -- "$installer" controller-stage "$store" "$helper" \
    "$run/agent-lifetime/controller-stage" "$BIN" \
    "$run/world/sock/operator/host.sock" "$run/world/sock/participant/host.sock" \
    >"$run/agent-lifetime/controller-stage-receipt.json"
  controller_staged=1
  timeout 240 sudo -n -- "$installer" controller-start "$store" "$helper" >"$run/agent-lifetime/controller-bootstrap-start.json"
  world_controller_birth
}

world_controller_birth() {
  local request_id
  request_id=$("${controller_runtime:-$BIN/grain-runtime}" tool-id)
  if [[ ${mode:-} == continue-session || ${mode:-} == continue-checkpoint ]]; then
    [[ $request_id != $(jq -er .boundary.request_id "$run/continuations/session-refusal-1/prepared.json") ]] || fail 'new tool ID reused definite refusal'
  fi
  printf '%s\n' "$request_id" >"$run/agent-lifetime/session-birth.request-id"
  jq .nextTool.arguments "$run/agent-lifetime/controller-stage.json" >"$run/agent-lifetime/session-birth.arguments.json"
  # One actual controller-owned birth. A missing/uncertain reply is retained;
  # this harness never resends the request or manufactures its birth journal.
  timeout 1800 sudo -n -- "$installer" controller-tool "$store" "$helper" "$request_id" \
    mini_create_application_session "$run/agent-lifetime/session-birth.arguments.json" \
    >"$run/agent-lifetime/session-birth.result.json" 2>"$run/agent-lifetime/session-birth.stderr"
  timeout 120 sudo -n -- "$installer" controller-tool-result "$store" "$helper" "$request_id" \
    >"$run/agent-lifetime/session-birth.retained-result.json"
  cmp "$run/agent-lifetime/session-birth.result.json" "$run/agent-lifetime/session-birth.retained-result.json"
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" issue-grant "$run" "$repo" \
    "$run/agent-lifetime/session-birth.result.json" \
    >"$run/agent-lifetime/issue-grant.stdout" 2>"$run/agent-lifetime/issue-grant.stderr"
  timeout 120 sudo -n -- "$installer" controller-tool-ack "$store" "$helper" "$request_id" \
    >"$run/agent-lifetime/session-birth.ack.json"
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" prepare-route "$run" "$repo" \
    "$run/agent-lifetime/controller-create.json" \
    >"$run/agent-lifetime/prepare-route.stdout" 2>"$run/agent-lifetime/prepare-route.stderr"
}

world_controller_stop() {
  local snapshot_result=0
  if [[ ${controller_staged:-0} == 1 ]]; then
    world_consent_snapshot "before-stop-$1" || snapshot_result=$?
  fi
  timeout 120 sudo -n -- "$installer" controller-stop "$store" "$helper" >"$run/agent-lifetime/controller-stop-$1.json" || return
  return "$snapshot_result"
}

# Observe the system service before stop resets its accounting. These are
# physical measurements, not a consent/admission result.
world_consent_snapshot() {
  local label=$1 consent_unit observed_exit
  consent_unit=$(jq -er '.consent.serviceUnit' "$run/agent-lifetime/controller-stage-receipt.json") || return
  [[ $consent_unit == "mini-spk-controller-consent-$store.service" ]] || return 1
  if systemctl show "$consent_unit" --no-pager \
    -p LoadState -p ActiveState -p SubState -p MainPID -p InvocationID \
    -p MemoryCurrent -p MemoryPeak -p MemoryMax -p MemorySwapMax -p Result \
    >"$run/agent-lifetime/consent-memory-$label.properties" \
    2>"$run/agent-lifetime/consent-memory-$label.stderr"; then observed_exit=0; else observed_exit=$?; fi
  python3 - "$run/agent-lifetime/consent-memory-$label" "$consent_unit" "$observed_exit" <<'PYCONSENT'
import json, pathlib, sys, time
prefix, unit, exit_code = sys.argv[1:]
properties = dict(line.split('=', 1) for line in pathlib.Path(prefix + '.properties').read_text().splitlines() if '=' in line)
value = {'schema': 'mini-oracle-consent-resources-v1', 'unit': unit,
         'unix_seconds': time.time(), 'observation_exit': int(exit_code), 'properties': properties}
pathlib.Path(prefix + '.json').write_text(json.dumps(value, indent=2) + '\n')
PYCONSENT
}

# Publish an exact stopped config, then let the native enrollment command
# prove its permitted transition and commit the journal binding. No journal edits.
world_controller_enroll() {
  local enrollment_mode=$1 bundle=$2 label=$3 directory
  directory=$run/agent-lifetime/enrollment-$label
  mkdir -m 700 "$directory"
  timeout 120 sudo -n -- "$installer" controller-journal "$store" "$helper" >"$directory/before.json"
  python3 - "$directory" "$bundle/controller.json" "$enrollment_mode" <<'PYREQUEST'
import hashlib, json, os, pathlib, sys
output, target, mode = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3]
journal = json.loads((output / 'before.json').read_bytes())
canonical = json.dumps(journal['binding'], sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()
request = {'protocol': 'mini-controller-application-enrollment-v1', 'mode': mode,
           'expectedBindingSha256': hashlib.sha256(canonical).hexdigest(),
           'targetConfigSha256': hashlib.sha256(target.read_bytes()).hexdigest()}
fd = os.open(output / 'request.json', os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
with os.fdopen(fd, 'w') as sink:
    json.dump(request, sink, sort_keys=True, separators=(',', ':'))
    sink.write('\n')
PYREQUEST
  timeout 120 sudo -n -- "$installer" controller-config "$store" "$helper" "$bundle" \
    >"$directory/config.json"
  timeout 1850 sudo -n -- "$installer" controller-enroll "$store" "$helper" "$directory/request.json" \
    >"$directory/result.json" 2>"$directory/stderr"
  timeout 120 sudo -n -- "$installer" controller-journal "$store" "$helper" >"$directory/after.json"
  python3 - "$directory" <<'PYCHECK'
import hashlib, json, pathlib, sys
p = pathlib.Path(sys.argv[1]); read = lambda name: json.loads((p / name).read_bytes())
before, after, result = read('before.json'), read('after.json'), read('result.json')
binding = json.dumps(after['binding'], sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()
assert result['protocol'] == 'mini-controller-application-enrollment-v1' and result['status'] == 'enrolled'
assert result['replayed'] is False
assert result['requestSha256'] == hashlib.sha256((p / 'request.json').read_bytes()).hexdigest()
assert result['bindingSha256'] == hashlib.sha256(binding).hexdigest()
assert before['binding']['configPath'] == after['binding']['configPath']
assert {k:v for k,v in before.items() if k != 'binding'} == {k:v for k,v in after.items() if k != 'binding'}
PYCHECK
}

world_controller_activate() {
  local start_result=$1 label=$2 activation bundle
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" activate "$run" "$repo" "$start_result" \
    >"$run/agent-lifetime/activate-$label.stdout" 2>"$run/agent-lifetime/activate-$label.stderr"
  activation=$(cat "$run/agent-lifetime/activate-$label.stdout")
  bundle=$(jq -er .bundle "$activation")
  world_controller_stop "before-$label"
  world_controller_enroll application "$bundle" "$label"
  cp "$bundle/controller.json" "$run/agent-lifetime/controller-active-$label.json"
  timeout 240 sudo -n -- "$installer" controller-start "$store" "$helper" >"$run/agent-lifetime/controller-start-$label.json"
  export ORACLE_CONTROLLER_INSTALLER=$installer ORACLE_CONTROLLER_STORE=$store ORACLE_CONTROLLER_HELPER=$helper
  export QUALIFIED_LIFETIME_HOST_BINARY=$BIN/minidregg-host
  QUALIFIED_LIFETIME_HOST_SHA256=$(sha256sum "$BIN/minidregg-host" | cut -d ' ' -f1)
  QUALIFIED_RUNTIME_SHA256=$(sha256sum "${controller_runtime:-$BIN/grain-runtime}" | cut -d ' ' -f1)
  export QUALIFIED_LIFETIME_HOST_SHA256 QUALIFIED_RUNTIME_SHA256
}

world_controller_probe() {
  local label=$1 directory=$2
  timeout 1800 sudo -n -- "$installer" controller-prepare-idle "$store" "$helper" \
    >"$run/agent-lifetime/readiness-$directory.json" 2>"$run/agent-lifetime/readiness-$directory.stderr"
  jq -e --arg task "$(jq -er .task "$run/agent-lifetime/controller-active-$label.json")" '
    .type == "mini-grain-idle-readiness-v1" and .ready == true and .task == $task and
    .signedTask.grain.task == $task and
    ((.connection == "hard" and .signedTask.grain.status == "1") or
     (.connection == "soft" and .signedTask.grain.status == "2")) and
    .signedTask.grain.reserved == "0"' "$run/agent-lifetime/readiness-$directory.json" >/dev/null \
    || fail 'controller has not reached signed idle readiness'
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" \
    "${controller_runtime:-$BIN/grain-runtime}" "$run/agent-lifetime/controller-active-$label.json" oracle-app \
    "$repo/deploy/oracle/acceptance/agent-cases.json" "$run/agent-lifetime/$directory" \
    >"$run/agent-lifetime/$directory.stdout" 2>"$run/agent-lifetime/$directory.stderr"
  world_consent_snapshot "after-$directory"
}

world_authority_probe() {
  local matched=$run/agent-lifetime/probe/discover-core-query.lifetime-attempt.json attempt_id
  attempt_id=$(python3 - "$matched" <<'PYATTEMPT'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_bytes())['lifetimeSettlement']['dispatchAttemptId']
if not isinstance(value, int) or isinstance(value, bool) or not 0 <= value < 2**64:
    raise SystemExit('native dispatch attempt ID absent or invalid')
print(value)
PYATTEMPT
)
  timeout 120 sudo -n -- "$installer" controller-reserve-export "$store" "$helper" "$attempt_id" \
    >"$run/agent-lifetime/authority-reserve-export.json"
  timeout 600 python3 "$repo/scripts/oracle-agent-authority-probe.py" \
    --host "$BIN/minidregg-host" --config "$config" \
    --operator-socket "$run/world/sock/operator/host.sock" \
    --public-socket "$run/world/sock/participant/host.sock" \
    --controller-export "$run/agent-lifetime/authority-reserve-export.json" \
    --application-attempt "$matched" --out "$run/agent-lifetime/authority" --deadline 180 \
    >"$run/agent-lifetime/authority.stdout" 2>"$run/agent-lifetime/authority.stderr"
}

world_prepare() {
  local base=$1 own=$2 run=$3 repo=$4 op_name start count registry bwrap deployment host
  [[ $(id -u) != 0 ]] || fail 'run as the operator, not root'
  op_uid=$(id -u); op_name=$(id -un)
  export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid}
  systemctl --user is-active default.target >/dev/null
  [[ $(loginctl show-user "$op_uid" -p Linger --value) == yes ]] || fail 'operator linger required'
  mkdir -m 700 "$run" "$run/bin" "$run/world" "$run/world/evidence"
  for binary in mini minidregg-host minidregg-link-sqlite-store minidregg-credential-signature-verifier minidregg-client-consent; do
    install -m 755 "$base/$binary" "$run/bin/$binary"
  done
  for binary in spk-host mini-spk-broker mini-spk-volume-helper spk-data-publish grain-runtime; do
    install -m 755 "$own/$binary" "$run/bin/$binary"
  done
  install -m 755 "$repo/deploy/spk-host/spk-ingest" "$run/bin/spk-ingest"
  sha256sum "$run/bin/"* >"$run/binary-sha256.txt"
  export BIN=$run/bin
  SPK_AGENT_ALLOCATION=$(sh "$repo/scripts/oracle-agent-lifetime-journey.sh" provision "$run" "$repo")
  export SPK_AGENT_ALLOCATION
  # No broker is contacted by this phase. Store identity comes from the Host.
  GRAINS_ROOT=/var/lib/mini-spk-worlds/0000000000000000 \
    BROKER_SOCKET=/var/lib/mini-spk-worlds/0000000000000000/runtime-0000000000000000/broker.sock \
    "$journey" phase "$run/world" store >"$run/store-phase.log" 2>&1
  config=$run/world/store/base/workroom/deployment/pinned-config.json
  "$BIN/minidregg-host" "$config" profile >"$run/native-profile.json"
  store=$(jq -er '.storeTag | select(test("^[0-9a-f]{16}$"))' "$run/native-profile.json")
  export GRAINS_ROOT=/var/lib/mini-spk-worlds/$store
  export BROKER_SOCKET=$GRAINS_ROOT/runtime-$store/broker.sock
  helper=/usr/local/libexec/mini-spk-volume-helper-$(od -An -N8 -tx1 /dev/urandom | tr -d ' \n')
  installer=$repo/deploy/spk-host/install-user-world
  units=$XDG_RUNTIME_DIR/systemd/user
  mkdir -p -m 700 "$units"
  # Find a free 16-ID slice in the operator's allocation. The installer rechecks
  # under its global lock and refuses a race; this harness never evicts a world.
  read -r start count < <(awk -F: -v user="$op_name" '$1==user && $3>=16 {print $2,$3;exit}' /etc/subuid)
  [[ $start =~ ^[0-9]+$ && $count =~ ^[0-9]+$ ]] || fail 'subuid allocation missing'
  end=$((start+count))
  while ((start+16<=end)); do
    occupied=0
    for registry in /etc/mini-spk-volumes/*.json /etc/mini-spk-controller-reservations/*.json; do
      [[ -f $registry ]] || continue
      if jq -e --argjson first "$start" --argjson last "$((start+16))" '((.appUids // []) + [.controllerUid, .controllerGid]) | map(select(type == "number")) | any(. >= $first and . < $last)' "$registry" >/dev/null; then occupied=1; break; fi
    done
    [[ $occupied == 1 ]] || break
    start=$((start+16))
  done
  ((start+16<=end)) || fail 'no unused subordinate UID slice'
  bwrap=$(sh "$repo/deploy/grain-host/resolve-bwrap")
  deployment=$(od -An -N32 -tx1 /dev/urandom | tr -d ' \n')
  host=$(sha256sum /etc/machine-id | cut -d ' ' -f1)
  jq -n --arg store "$store" --arg helper "$helper" --arg root "$GRAINS_ROOT" \
    '{store:$store,helper:$helper,root:$root}' >"$run/world-identity.json"
  sudo -n -- "$installer" install "$BIN/mini-spk-volume-helper" "$helper" "$store" "$deployment" "$host" "$op_uid" "$start" 16 >"$run/root-setup.log" 2>&1
  configured=1
  registry=/etc/mini-spk-volumes/$store.json
  jq -n --slurpfile r "$registry" --arg binary "$BIN/spk-host" --arg sha "$(sha256sum "$BIN/spk-host" | cut -d ' ' -f1)" \
    --arg ingest "$BIN/spk-ingest" --arg op "$op_name" --arg importProfile "$ORACLE_IMPORT_PROFILE" --arg bwrap "$bwrap" \
    --arg bwrapSha "$(sha256sum "$bwrap" | cut -d ' ' -f1)" '
    $r[0] as $r | {protocol:"mini-spk-broker-config-v3",store:$r.store,grainsRoot:$r.grainsRoot,
    spkRoot:($r.grainsRoot+"/spk"),brokerSocket:($r.grainsRoot+"/runtime-"+$r.store+"/broker.sock"),
    operatorUser:$op,unitPrefix:"mini",spkHost:$binary,spkHostSha256:$sha,bwrap:$bwrap,
    bwrapSha256:$bwrapSha,ingestHelper:$ingest,volumeHelper:$r.helper,
    appUids:$r.appUids,residentHomeReadOnlyPaths:[],importProfile:$importProfile}' >"$GRAINS_ROOT/broker/config.json"
  chmod 600 "$GRAINS_ROOT/broker/config.json"
  sed "s|%h/.local/libexec/mini-spk-broker|$BIN/mini-spk-broker|" \
    "$repo/deploy/spk-host/mini-spk-broker@.service" >"$units/mini-spk-broker@$store.service"
  printf "\n[Service]\nMemoryMax=512M\nMemorySwapMax=0\nCPUQuota=100%%\nTasksMax=128\nRuntimeMaxSec=10800\n" >>"$units/mini-spk-broker@$store.service"
  systemctl --user daemon-reload
  systemctl --user start "mini-spk-broker@$store.service"
  for ((i=0;i<100;i++)); do [[ ! -S $BROKER_SOCKET ]] || break; sleep .1; done
  [[ -S $BROKER_SOCKET && $(stat -c '%u:%a' "$BROKER_SOCKET") == "$op_uid:600" ]] || fail 'private broker readiness failed'
  "$journey" phase "$run/world" services workroom profile >"$run/prepare.log" 2>&1
  profile=$(jq -er .profilePath "$run/world/evidence/profile-result.json")
  state=$(jq -er .stateRoot "$run/world/evidence/profile-result.json")
}


# Resume only the already recorded native Store. No grant/claim journal is reset.
world_resume() {
  local run=$1 repo=$2 op_name
  op_uid=$(id -u); op_name=$(id -un)
  export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid}
  export BIN=$run/bin
  store=$(jq -er '.store | select(test("^[0-9a-f]{16}$"))' "$run/world-identity.json")
  helper=$(jq -er .helper "$run/world-identity.json")
  export GRAINS_ROOT=/var/lib/mini-spk-worlds/$store
  export BROKER_SOCKET=$GRAINS_ROOT/runtime-$store/broker.sock
  [[ $(jq -er .root "$run/world-identity.json") == "$GRAINS_ROOT" ]] || fail 'resume namespace differs'
  [[ $helper =~ ^/usr/local/libexec/mini-spk-volume-helper-[0-9a-f]{16}$ ]] || fail 'resume helper malformed'
  [[ $(jq -er .helper "/etc/mini-spk-volumes/$store.json") == "$helper" ]] || fail 'resume registry differs'
  [[ $(jq -er .operatorUid "/etc/mini-spk-volumes/$store.json") == "$op_uid" ]] || fail 'resume operator differs'
  installer=$repo/deploy/spk-host/install-user-world
  units=$XDG_RUNTIME_DIR/systemd/user
  profile=$(jq -er .profilePath "$run/world/evidence/profile-result.json")
  state=$(jq -er .stateRoot "$run/world/evidence/profile-result.json")
  "$BIN/spk-host" grain status "$profile" 9101 >"$run/resume-install-status.json"
  jq -e '.installPrepared and (.installCompleted | not) and (.runs | length == 0)'     "$run/resume-install-status.json" >/dev/null || fail 'resume supports only a prepared, incomplete INSTALL with no START'
  for retained in install-prepared-v2.json install.json; do
    expected=$(tar -xOf "$run/initial-attempt/native-state.tar" "apps/9101/install/$retained" | sha256sum | cut -d ' ' -f1)
    [[ $(sha256sum "$state/apps/9101/install/$retained" | cut -d ' ' -f1) == "$expected" ]] || fail 'retained INSTALL bytes changed'
  done
  sha256sum "$state/apps/9101/install/install-prepared-v2.json" "$state/apps/9101/install/install.json" >"$run/resume-retained-install-sha256.txt"
  configured=1
  # Operator physical import bounds may change; the retained install.json and
  # source-owned prepared BEGIN/claim bytes do not change. grain install checks
  # the prepared record and resumes only ensure_image/completion.
  jq --arg selected "$ORACLE_IMPORT_PROFILE" '.importProfile=$selected'     "$GRAINS_ROOT/broker/config.json" >"$GRAINS_ROOT/broker/config.resume.json"
  chmod 600 "$GRAINS_ROOT/broker/config.resume.json"
  mv "$GRAINS_ROOT/broker/config.resume.json" "$GRAINS_ROOT/broker/config.json"
  cp "$GRAINS_ROOT/broker/config.json" "$run/resume-broker-config.json"
  systemctl --user start "mini-spk-broker@$store.service"
  for ((i=0;i<100;i++)); do [[ ! -S $BROKER_SOCKET ]] || break; sleep .1; done
  [[ -S $BROKER_SOCKET ]] || fail 'resumed broker socket absent'
  "$journey" phase "$run/world" services workroom profile >"$run/resume-prepare.log" 2>&1
}

# Only the checked pre-START account-creation boundary can enter here. All
# prior source operations remain completed; only existing services restart.
world_continue_controller() {
  local run=$1 repo=$2 app
  op_uid=$(id -u)
  export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid}
  export BIN=$run/bin
  store=$(jq -er '.store | select(test("^[0-9a-f]{16}$"))' "$run/world-identity.json")
  helper=$(jq -er .helper "$run/world-identity.json")
  export GRAINS_ROOT=/var/lib/mini-spk-worlds/$store
  export BROKER_SOCKET=$GRAINS_ROOT/runtime-$store/broker.sock
  [[ $(jq -er .root "$run/world-identity.json") == "$GRAINS_ROOT" ]] || fail 'continuation namespace differs'
  [[ $helper =~ ^/usr/local/libexec/mini-spk-volume-helper-[0-9a-f]{16}$ ]] || fail 'continuation helper malformed'
  jq -e --arg helper "$helper" --argjson uid "$op_uid" \
    '.helper == $helper and .operatorUid == $uid' "/etc/mini-spk-volumes/$store.json" >/dev/null || fail 'continuation registry differs'
  [[ $(systemctl --user show "mini-spk-broker@$store.service" -p ActiveState --value) == inactive ]] || fail 'broker was not stopped'
  installer=$repo/deploy/spk-host/install-user-world
  units=$XDG_RUNTIME_DIR/systemd/user
  config=$run/world/store/base/workroom/deployment/pinned-config.json
  profile=$(jq -er .profilePath "$run/world/evidence/profile-result.json")
  state=$(jq -er .stateRoot "$run/world/evidence/profile-result.json")
  continuation=$(python3 "$repo/deploy/oracle/acceptance/continue_controller.py" "$run" "$spk" "$inventory" "$benchmark" "$repo")
  [[ $continuation == "$run/continuations/controller-create-1" ]] || fail 'continuation evidence path differs'
  preserve_existing_exit=0
  sha256sum "$0" "$repo/deploy/oracle/acceptance/world.sh" "$repo/deploy/oracle/acceptance/report.py" "$repo/deploy/oracle/acceptance/browser_edge.py" \
    "$repo/deploy/oracle/acceptance/continue_controller.py" "$repo/deploy/oracle/acceptance/volume_cleanup.py" "$installer" "$repo/deploy/spk-host/controller-world.py" \
    >"$continuation/recovery-input-sha256.txt"
  configured=1
  systemctl --user start "mini-spk-broker@$store.service"
  for ((i=0;i<100;i++)); do [[ ! -S $BROKER_SOCKET ]] || break; sleep .1; done
  [[ -S $BROKER_SOCKET && $(stat -c '%u:%a' "$BROKER_SOCKET") == "$op_uid:600" ]] || fail 'continuation broker readiness failed'
  "$journey" phase "$run/world" services >"$continuation/services.log" 2>&1
  for app in 9101 9201; do
    timeout 1800 "$BIN/spk-host" grain status "$profile" "$app" >"$continuation/status-$app.json"
    jq -e --arg app "$app" '.app == $app and .installCompleted and (.runs | length == 0)' \
      "$continuation/status-$app.json" >/dev/null || fail 'continuation requires installed grains with no START'
  done
  world_disk_snapshot before-controller-continuation
  controller_create_verb=controller-resume-create
}

# A second, narrower seam: account/stage and six grants already exist, but
# the original tool was definitively refused before any session operation.
world_continue_session() {
  local run=$1 repo=$2 fresh app target bundle
  local resume_args=()
  op_uid=$(id -u)
  export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid}
  export BIN=$run/bin
  store=$(jq -er '.store | select(test("^[0-9a-f]{16}$"))' "$run/world-identity.json")
  helper=$(jq -er .helper "$run/world-identity.json")
  export GRAINS_ROOT=/var/lib/mini-spk-worlds/$store
  export BROKER_SOCKET=$GRAINS_ROOT/runtime-$store/broker.sock
  [[ $(jq -er .root "$run/world-identity.json") == "$GRAINS_ROOT" ]] || fail 'session continuation namespace differs'
  [[ $helper =~ ^/usr/local/libexec/mini-spk-volume-helper-[0-9a-f]{16}$ ]] || fail 'session continuation helper malformed'
  installer=$repo/deploy/spk-host/install-user-world
  units=$XDG_RUNTIME_DIR/systemd/user
  config=$run/world/store/base/workroom/deployment/pinned-config.json
  profile=$(jq -er .profilePath "$run/world/evidence/profile-result.json")
  state=$(jq -er .stateRoot "$run/world/evidence/profile-result.json")
  fresh=$(mktemp -d "$run/session-refusal-preflight.XXXXXXXX")
  timeout 120 sudo -n -- "$installer" controller-export "$store" "$helper" >"$fresh/controller-export.json"
  # Check the complete runtime helper list before publishing a backup boundary.
  # This manifest is reused after preparation; missing inputs cannot leave a
  # prepared continuation that has not yet checked its own source dependencies.
  world_source_manifest >"$fresh/source-input-sha256.txt"
  sha256sum "$own/grain-runtime" >>"$fresh/source-input-sha256.txt"
  [[ ${session_resume_prepared:-0} != 1 ]] || resume_args+=("$fresh/source-input-sha256.txt")
  continuation=$(python3 -B "$repo/deploy/oracle/acceptance/continue_controller.py" --session-refusal \
    "$run" "$spk" "$inventory" "$benchmark" "$repo" "$fresh/controller-export.json" "${resume_args[@]}")
  [[ $continuation == "$run/continuations/session-refusal-1" ]] || fail 'session continuation evidence path differs'
  controller_runtime=$continuation/bin/grain-runtime
  recovery_manifest=$continuation/recovery-input-sha256.txt
  if [[ ${session_resume_prepared:-0} == 1 ]]; then
    recovery_manifest=$continuation/source-resume-1-input-sha256.txt
    [[ $(sha256sum "$controller_runtime" | cut -d ' ' -f1) == $(sha256sum "$own/grain-runtime" | cut -d ' ' -f1) ]] || fail 'prepared runtime changed'
  else
    mkdir -m 700 "$continuation/bin"
    install -m 500 "$own/grain-runtime" "$controller_runtime"
  fi
  (set -o noclobber; cat "$fresh/source-input-sha256.txt" >"$recovery_manifest")
  sha256sum "$controller_runtime" >>"$recovery_manifest"
  preserve_existing_exit=0
  configured=1 controller_created=1 controller_staged=1
  timeout 120 sudo -n -- "$installer" controller-consent-storage "$store" "$helper" >"$continuation/consent-storage.json"
  timeout 120 sudo -n -- "$installer" controller-runtime-upgrade "$store" "$helper" "$controller_runtime" \
    >"$continuation/runtime-upgrade.json"
  jq -e --arg expected "$(sha256sum "$controller_runtime" | cut -d ' ' -f1)" \
    --arg previous "$(sha256sum "$BIN/grain-runtime" | cut -d ' ' -f1)" \
    '.runtimeSha256 == $expected and .previousRuntimeSha256 == $previous' \
    "$continuation/runtime-upgrade.json" >/dev/null || fail 'installed runtime upgrade differs'
  systemctl --user start "mini-spk-broker@$store.service"
  for ((i=0;i<100;i++)); do [[ ! -S $BROKER_SOCKET ]] || break; sleep .1; done
  [[ -S $BROKER_SOCKET && $(stat -c '%u:%a' "$BROKER_SOCKET") == "$op_uid:600" ]] || fail 'session continuation broker readiness failed'
  "$journey" phase "$run/world" services >"$continuation/services.log" 2>&1
  for app in 9101 9201; do
    timeout 1800 "$BIN/spk-host" grain status "$profile" "$app" >"$continuation/status-$app.json"
    jq -e --arg app "$app" '.app == $app and .installCompleted and (.runs | length == 0)' \
      "$continuation/status-$app.json" >/dev/null || fail 'session continuation requires installed grains with no START'
  done
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" prepare-bootstrap-dispatch "$run" "$repo" \
    "$run/agent-lifetime/controller-create.json" >"$continuation/bootstrap-target.stdout" 2>"$continuation/bootstrap-target.stderr"
  target=$(cat "$continuation/bootstrap-target.stdout")
  [[ $target == "$run/agent-lifetime/native-prepare-bootstrap-dispatch/controller-update/controller.json" ]] || fail 'bootstrap target path differs'
  bundle=$(dirname "$target")
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" prepare-worker-policy "$run" "$repo" "$target" \
    >"$continuation/worker-policy.stdout" 2>"$continuation/worker-policy.stderr"
  world_controller_enroll bootstrap-dispatch "$bundle" bootstrap-dispatch
  timeout 240 sudo -n -- "$installer" controller-start "$store" "$helper" >"$continuation/controller-bootstrap-start.json"
  # Original null-operation error is archived, not ACKable. Only this new tool
  # ID may create a session; its successful native result uses normal ACK.
  world_controller_birth
}

# Continue only the failed, pre-commit lifetime-route enrollment. The old
# session, grant and START remain admitted; a dead incarnation is supervised
# through native STOP and successor START, never relaunched in place.
world_continue_activation() {
  local run=$1 repo=$2 fresh unit expected_runtime
  op_uid=$(id -u)
  export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid}
  export BIN=$run/bin
  store=$(jq -er '.store | select(test("^[0-9a-f]{16}$"))' "$run/world-identity.json")
  helper=$(jq -er .helper "$run/world-identity.json")
  export GRAINS_ROOT=/var/lib/mini-spk-worlds/$store
  export BROKER_SOCKET=$GRAINS_ROOT/runtime-$store/broker.sock
  [[ $(jq -er .root "$run/world-identity.json") == "$GRAINS_ROOT"
      && $helper =~ ^/usr/local/libexec/mini-spk-volume-helper-[0-9a-f]{16}$ ]] || fail 'activation namespace differs'
  installer=$repo/deploy/spk-host/install-user-world
  units=$XDG_RUNTIME_DIR/systemd/user
  config=$run/world/store/base/workroom/deployment/pinned-config.json
  profile=$(jq -er .profilePath "$run/world/evidence/profile-result.json")
  state=$(jq -er .stateRoot "$run/world/evidence/profile-result.json")
  expected_runtime=${ORACLE_RECOVERY_RUNTIME_SHA256:?qualified recovery runtime digest required}
  [[ $expected_runtime =~ ^[0-9a-f]{64}$
      && $(sha256sum "$own/grain-runtime" | cut -d ' ' -f1) == "$expected_runtime" ]] || fail 'recovery runtime pin differs'
  sha256sum -c "$run/binary-sha256.txt" >"$run/activation-original-binary-check.txt"
  [[ $(sha256sum "$base/minidregg-host" | cut -d ' ' -f1) == $(sha256sum "$BIN/minidregg-host" | cut -d ' ' -f1) ]] || fail 'recovery Host changed'
  fresh=$(mktemp -d "$run/activation-preflight.XXXXXXXX")
  timeout 120 sudo -n -- "$installer" controller-export "$store" "$helper" >"$fresh/controller-export.json"
  timeout 120 sudo -n -- "$installer" controller-status "$store" "$helper" >"$fresh/controller-status.json"
  unit=$(jq -er .unit "$run/world/evidence/start-a.stdout")
  [[ $unit == mini-spk-s"$store"-a9101-g*.service ]] || fail 'old app unit differs'
  systemctl --user show "$unit" -p Id -p LoadState -p ActiveState -p SubState -p MainPID -p InvocationID -p Job >"$fresh/manager.txt"
  [[ $(systemctl --user show "mini-spk-broker@$store.service" -p ActiveState --value) == inactive ]] || fail 'broker is not stopped'
  [[ ! -S $run/world/sock/operator/host.sock && ! -S $run/world/sock/participant/host.sock ]] || fail 'operator services are not stopped'
  if [[ -f $run/continuations/activation-recovery-1/socket-failure/boundary.json ]]; then
    local next_generation
    next_generation=$(jq -er '.successor_generation | select(test("^[0-9]+$"))' "$run/continuations/activation-recovery-1/socket-failure/boundary.json")
    systemctl --user show "mini-spk-s$store-a9101-g$next_generation.service" -p Id -p ActiveState -p MainPID -p Job >"$fresh/manager-successor.txt"
    [[ ${ORACLE_SOCKET_RECLAIM_BIN:-} == /* && ${ORACLE_SOCKET_RECLAIM_SHA256:-} =~ ^[0-9a-f]{64}$
        && $(sha256sum "$ORACLE_SOCKET_RECLAIM_BIN" | cut -d ' ' -f1) == "$ORACLE_SOCKET_RECLAIM_SHA256" ]] || fail 'qualified native socket reclaimer pin required'
  fi
  world_source_manifest >"$fresh/source-input-sha256.txt"
  sha256sum "$own/grain-runtime" >>"$fresh/source-input-sha256.txt"
  continuation=$(python3 -B "$repo/deploy/oracle/acceptance/recover_activation.py" "$run" "$fresh")
  if [[ $continuation == "$run/continuations/activation-successor-1" ]]; then
    world_finish_activation_successor "$fresh"
    return
  fi
  [[ $continuation == "$run/continuations/activation-recovery-1" ]] || fail 'activation recovery path differs'
  if [[ -d $continuation/bin ]]; then
    [[ $(sha256sum "$continuation/bin/grain-runtime" | cut -d ' ' -f1) == "$expected_runtime" ]] || fail 'prepared runtime changed'
  else
    mkdir -m700 "$continuation/bin"
    install -m500 "$own/grain-runtime" "$continuation/bin/grain-runtime"
  fi
  controller_runtime=$continuation/bin/grain-runtime
  cp "$fresh/source-input-sha256.txt" "$continuation/recovery-input-sha256.txt"
  sha256sum "$controller_runtime" >>"$continuation/recovery-input-sha256.txt"
  preserve_existing_exit=0
  configured=1 controller_created=1 controller_staged=1
  if [[ ! -f $continuation/phases/runtime-upgrade.completed.json ]]; then
    world_phase_record runtime-upgrade started
    timeout 120 sudo -n -- "$installer" controller-runtime-upgrade "$store" "$helper" "$controller_runtime" >"$continuation/runtime-upgrade.json"
    jq -e --arg expected "$expected_runtime" --arg previous "$(sha256sum "$BIN/grain-runtime" | cut -d ' ' -f1)" \
      '.runtimeSha256 == $expected and .previousRuntimeSha256 == $previous' "$continuation/runtime-upgrade.json" >/dev/null || fail 'runtime upgrade differs'
    world_phase_record runtime-upgrade completed "$continuation/runtime-upgrade.json"
  fi
  world_phase_record public-listener started
  timeout 120 sudo -n -- "$installer" controller-public-listener "$store" "$helper" "$BIN/mini" \
    >"$continuation/public-listener.json"
  jq -e --arg binary "$GRAINS_ROOT/controller/public-listener/mini" \
    --arg digest "$(sha256sum "$BIN/mini" | cut -d ' ' -f1)" --arg socket "$run/world/sock/participant/host.sock" \
    --slurpfile before "$fresh/controller-status.json" '
    .store == $before[0].store and .controllerUid == $before[0].controllerUid and
    .publicListener.binary == $binary and .publicListener.binarySha256 == $digest and
    .publicListener.socket == $socket and .publicListener.controllerUid == .controllerUid' \
    "$continuation/public-listener.json" >/dev/null || fail 'activation listener registration pins differ'
  export SPK_PUBLIC_LISTENER_RECEIPT=$continuation/public-listener.json
  world_phase_record public-listener completed "$continuation/public-listener.json"
  world_phase_record services started
  systemctl --user start "mini-spk-broker@$store.service"
  for ((i=0;i<100;i++)); do [[ ! -S $BROKER_SOCKET ]] || break; sleep .1; done
  [[ -S $BROKER_SOCKET && $(stat -c '%u:%a' "$BROKER_SOCKET") == "$op_uid:600" ]] || fail 'recovery broker readiness failed'
  "$journey" phase "$run/world" services >"$continuation/services.log" 2>&1
  world_phase_record services completed "$run/world/sock/operator.pid.identity.json" "$run/world/sock/participant.pid.identity.json"
  world_phase_record supervise started
  timeout 1800 "$BIN/spk-host" grain supervise "$profile" 9101 >"$continuation/supervise.json" 2>"$continuation/supervise.stderr"
  jq -e --arg old "$(jq -er .boundary.old_generation "$continuation/prepared.json")" \
    '.action == "stop-and-continue" and .crashed.generation == $old and .start.app == "9101"
     and (.start.generation | tonumber) > ($old | tonumber) and .start.completion.completionReceipt.eventId' \
    "$continuation/supervise.json" >/dev/null || fail 'supervision did not admit successor START'
  jq .start "$continuation/supervise.json" >"$continuation/successor-start.json"
  local old_generation
  old_generation=$(jq -er .boundary.old_generation "$continuation/prepared.json")
  cp "$state/apps/9101/g$old_generation/record.json" "$continuation/old-record-after-stop.json"
  cp -a "$state/apps/9101/g$old_generation/stop-completion" "$continuation/stop-completion"
  world_phase_record supervise completed "$continuation/supervise.json" "$continuation/successor-start.json"
  world_phase_record enrollment started
}

world_finish_activation_successor() {
  local fresh=$1 socket controller_uid
  controller_runtime=$run/continuations/activation-recovery-1/bin/grain-runtime
  [[ $(sha256sum "$controller_runtime" | cut -d ' ' -f1) == "$expected_runtime" ]] || fail 'successor controller runtime differs'
  cp "$fresh/source-input-sha256.txt" "$continuation/recovery-input-sha256.txt"
  sha256sum "$ORACLE_SOCKET_RECLAIM_BIN" >>"$continuation/recovery-input-sha256.txt"
  preserve_existing_exit=0
  configured=1 controller_created=1 controller_staged=1
  socket=$(jq -er .socket.path "$continuation/prepared.json")
  controller_uid=$(jq -er .controller_uid "$continuation/prepared.json")
  world_phase_record socket-reclaim started
  timeout 30 "$ORACLE_SOCKET_RECLAIM_BIN" grain reclaim-agent-socket "$socket" "$controller_uid" \
    >"$continuation/socket-reclaim.json" 2>"$continuation/socket-reclaim.stderr"
  python3 - "$continuation" <<'PYRECLAIM'
import json,pathlib,sys
p=pathlib.Path(sys.argv[1]); before=json.loads((p/'prepared.json').read_bytes()); result=json.loads((p/'socket-reclaim.json').read_bytes())
assert result['protocol']=='mini-spk-agent-socket-reclaim-v1' and result['removed'] is True
assert result['nativeOperationSubmitted'] is False and result['socket']==before['socket']['path']
assert result['controllerUid']==before['controller_uid'] and result['ownerUid']==before['socket']['uid']
assert result['previous']=={key:(int(before['socket'][key],8) if key=='mode' else before['socket'][key]) for key in ('device','inode','mode','uid')}
PYRECLAIM
  world_phase_record socket-reclaim completed "$continuation/socket-reclaim.json"
  cp "$fresh/controller-status.json" "$continuation/public-listener.json"
  jq -e --arg binary "$GRAINS_ROOT/controller/public-listener/mini" \
    --arg digest "$(sha256sum "$BIN/mini" | cut -d ' ' -f1)" --arg socket "$run/world/sock/participant/host.sock" '
    .stopped == true and .publicListener.binary == $binary and .publicListener.binarySha256 == $digest and
    .publicListener.socket == $socket and .publicListener.controllerUid == .controllerUid' \
    "$continuation/public-listener.json" >/dev/null || fail 'successor listener registration differs'
  export SPK_PUBLIC_LISTENER_RECEIPT=$continuation/public-listener.json
  world_phase_record services started
  systemctl --user start "mini-spk-broker@$store.service"
  for ((i=0;i<100;i++)); do [[ ! -S $BROKER_SOCKET ]] || break; sleep .1; done
  [[ -S $BROKER_SOCKET && $(stat -c '%u:%a' "$BROKER_SOCKET") == "$op_uid:600" ]] || fail 'successor broker readiness failed'
  "$journey" phase "$run/world" services >"$continuation/services.log" 2>&1
  world_phase_record services completed "$run/world/sock/operator.pid.identity.json" "$run/world/sock/participant.pid.identity.json"
  world_phase_record successor-start started
  timeout 1800 "$BIN/spk-host" grain start "$profile" 9101 >"$continuation/successor-start.json" 2>"$continuation/successor-start.stderr"
  jq -e --arg generation "$(jq -er .successor_generation "$continuation/prepared.json")" '
    .protocol == "mini-spk-grain-start-v1" and .app == "9101" and .generation == $generation and
    .startAction.kind == "continue" and .completion.completionReceipt.eventId' \
    "$continuation/successor-start.json" >/dev/null || fail 'native never-begun successor START differs'
  world_phase_record successor-start completed "$continuation/successor-start.json"
  world_phase_record enrollment started
}

# Compatibility for a retained old resident binary. The new native reclaimer
# owns transport cleanup; the native completed STOP remains the prerequisite.
world_reclaim_stopped_agent_socket() {
  local app=$1 generation=$2 label=$3 directory socket uid
  [[ -n ${ORACLE_SOCKET_RECLAIM_BIN:-} ]] || return 0
  [[ $app == 9101 && $generation =~ ^[0-9]+$ && $label =~ ^[a-z0-9-]+$ ]] || fail 'socket reclamation selector differs'
  [[ $(sha256sum "$ORACLE_SOCKET_RECLAIM_BIN" | cut -d ' ' -f1) == "$ORACLE_SOCKET_RECLAIM_SHA256" ]] || fail 'socket reclaimer changed'
  directory=$run/native-agent-socket-reclaims/$label
  mkdir -p -m700 "$run/native-agent-socket-reclaims"
  mkdir -m700 "$directory"
  python3 - "$state/apps/$app/g$generation" "$directory" <<'PYSTOPSOCKET'
import json,pathlib,stat,subprocess,sys
p,out=map(pathlib.Path,sys.argv[1:]); read=lambda name:json.loads((p/name).read_bytes())
record=read('record.json'); assert record['phase']=='stopped' and record.get('dispatch_in_flight') is None
unit=record['identity']['unit']
manager=dict(line.split('=',1) for line in subprocess.check_output(['systemctl','--user','show',unit,'-p','Id','-p','ActiveState','-p','MainPID','-p','Job'],text=True).splitlines())
assert manager['Id']==unit and manager['ActiveState'] in ('inactive','failed') and manager['MainPID']=='0' and manager['Job'] in ('','0')
receipts=[json.loads(x.read_bytes()) for x in (p/'stop-completion').rglob('receipt-anchor.json')]
assert receipts and all(x.get('eventId') and x.get('worldRoot') for x in receipts)
agents=read('resident.json')['agents']; assert len(agents)==1
agent=agents[0]; socket=pathlib.Path(agent['socket']); before=None
try:
 m=socket.lstat(); assert stat.S_ISSOCK(m.st_mode)
 before={'device':m.st_dev,'inode':m.st_ino,'mode':stat.S_IMODE(m.st_mode),'uid':m.st_uid}
except FileNotFoundError: pass
value={'socket':str(socket),'controllerUid':agent['controllerUid'],'previous':before,'record':record,'manager':manager,'stopReceipts':receipts}
(out/'before.json').write_text(json.dumps(value,indent=2)+'\n')
PYSTOPSOCKET
  socket=$(jq -er .socket "$directory/before.json")
  uid=$(jq -er .controllerUid "$directory/before.json")
  timeout 30 "$ORACLE_SOCKET_RECLAIM_BIN" grain reclaim-agent-socket "$socket" "$uid" >"$directory/result.json" 2>"$directory/stderr"
  jq -e --slurpfile before "$directory/before.json" '
    .protocol == "mini-spk-agent-socket-reclaim-v1" and .nativeOperationSubmitted == false and
    .socket == $before[0].socket and .controllerUid == $before[0].controllerUid and
    .previous == $before[0].previous and .removed == ($before[0].previous != null)' "$directory/result.json" >/dev/null || fail 'after-STOP native socket receipt differs'
  sha256sum "$ORACLE_SOCKET_RECLAIM_BIN" >"$directory/binary-sha256.txt"
}

world_recovery_operator_upgrades() {
  local memory=${ORACLE_RECOVERY_CONSENT_MEMORY_MIB:-} mini=${ORACLE_RECOVERY_MINI_BIN:-} unit
  if [[ -n $memory ]]; then
    unit=mini-spk-controller-consent-$store.service
    jq -e --arg unit "$unit" '.stoppedUnits | index($unit) != null' "$continuation/observations/controller-status.json" >/dev/null || fail 'consent unit not in stopped controller'
    world_phase_record consent-memory started
    systemctl show "$unit" -p Id -p ActiveState -p MainPID -p MemoryMax -p MemorySwapMax >"$continuation/consent-memory-before.properties"
    timeout 120 sudo -n -- "$installer" controller-consent-memory "$store" "$helper" "$memory" >"$continuation/consent-memory.json"
    jq -e --arg store "$store" --argjson memory "$memory" '.store == $store and .memoryMiB == $memory and .nativeOperationSubmitted == false' "$continuation/consent-memory.json" >/dev/null || fail 'consent memory revision differs'
    systemctl show "$unit" -p Id -p ActiveState -p MainPID -p MemoryMax -p MemorySwapMax >"$continuation/consent-memory-after.properties"
    [[ $(sed -n 's/^MemoryMax=//p' "$continuation/consent-memory-after.properties") == $((memory * 1024 * 1024)) ]] || fail 'consent memory manager limit differs'
    world_phase_record consent-memory completed "$continuation/consent-memory.json" "$continuation/consent-memory-before.properties" "$continuation/consent-memory-after.properties"
  fi
  if [[ -n $mini ]]; then
    world_phase_record mini-upgrade started
    sha256sum "$GRAINS_ROOT/controller/bin/mini" >"$continuation/mini-before.sha256"
    timeout 120 sudo -n -- "$installer" controller-mini-upgrade "$store" "$helper" "$continuation/bin/mini" >"$continuation/mini-upgrade.json"
    jq -e --arg store "$store" --arg expected "$ORACLE_RECOVERY_MINI_SHA256" --arg previous "$(cut -d ' ' -f1 "$continuation/mini-before.sha256")" '
      .store == $store and .miniSha256 == $expected and
      (.previousMiniSha256 == $previous or (.alreadyConfigured == true and $previous == $expected))' "$continuation/mini-upgrade.json" >/dev/null || fail 'controller Mini revision differs'
    world_phase_record mini-upgrade completed "$continuation/mini-upgrade.json" "$continuation/mini-before.sha256"
  fi
}

world_resume_api_recovery() {
  local fresh resumed old_generation expected_runtime
  op_uid=$(id -u)
  export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid} BIN=$run/bin
  store=$(jq -er '.store | select(test("^[0-9a-f]{16}$"))' "$run/world-identity.json")
  helper=$(jq -er .helper "$run/world-identity.json")
  export GRAINS_ROOT=/var/lib/mini-spk-worlds/$store BROKER_SOCKET=/var/lib/mini-spk-worlds/$store/runtime-$store/broker.sock
  [[ $(jq -er .root "$run/world-identity.json") == "$GRAINS_ROOT" && $helper =~ ^/usr/local/libexec/mini-spk-volume-helper-[0-9a-f]{16}$ ]] || fail 'API resumption namespace differs'
  installer=$repo/deploy/spk-host/install-user-world
  units=$XDG_RUNTIME_DIR/systemd/user
  config=$run/world/store/base/workroom/deployment/pinned-config.json
  profile=$(jq -er .profilePath "$run/world/evidence/profile-result.json")
  state=$(jq -er .stateRoot "$run/world/evidence/profile-result.json")
  expected_runtime=${ORACLE_RECOVERY_RUNTIME_SHA256:?qualified runtime required}
  [[ $expected_runtime =~ ^[0-9a-f]{64}$ && $(sha256sum "$own/grain-runtime" | cut -d ' ' -f1) == "$expected_runtime" ]] || fail 'resumption runtime pin differs'
  [[ ${ORACLE_SOCKET_RECLAIM_BIN:-} == /* && ${ORACLE_SOCKET_RECLAIM_SHA256:-} =~ ^[0-9a-f]{64}$
      && $(sha256sum "$ORACLE_SOCKET_RECLAIM_BIN" | cut -d ' ' -f1) == "$ORACLE_SOCKET_RECLAIM_SHA256" ]] || fail 'resumption reclaimer pin differs'
  [[ $api_recovery_resume == "$run/continuations/application-api-recovery-"* && ${api_recovery_resume##*-} =~ ^[0-9]+$ ]] || fail 'resumption directory differs'
  [[ -f $repo/scripts/application-payer-successor.py ]] || fail 'native custody successor helper absent'
  sha256sum -c "$run/binary-sha256.txt" >"$run/api-resumption-original-binary-check.txt"
  fresh=$(mktemp -d "$run/api-resumption-preflight.XXXXXXXX")
  timeout 120 sudo -n -- "$installer" controller-export "$store" "$helper" >"$fresh/controller-export.json"
  timeout 120 sudo -n -- "$installer" controller-status "$store" "$helper" >"$fresh/controller-status.json"
  systemctl --user show "$(jq -er .boundary.old_record.identity.unit "$api_recovery_resume/prepared.json")" -p Id -p MainPID -p ActiveState -p Job >"$fresh/manager.txt"
  systemctl --user show "mini-spk-broker@$store.service" -p Id -p MainPID -p ActiveState -p ControlGroup >"$fresh/broker-manager.txt"
  python3 -B "$repo/deploy/oracle/acceptance/recover_application_api.py" --check-stopped-broker "$fresh" "$BROKER_SOCKET" "mini-spk-broker@$store.service" "$op_uid" >"$fresh/broker-stopped.json"
  [[ ! -S $run/world/sock/operator/host.sock && ! -S $run/world/sock/participant/host.sock ]] || fail 'API resumption services are not stopped'
  world_source_manifest >"$fresh/source-input-sha256.txt"
  sha256sum "$own/grain-runtime" "$ORACLE_SOCKET_RECLAIM_BIN" "$repo/scripts/application-payer-successor.py" >>"$fresh/source-input-sha256.txt"
  resumed=$(python3 -B "$repo/deploy/oracle/acceptance/recover_application_api.py" --resume-after-stop "$run" "$api_recovery_resume" "$fresh")
  [[ $resumed == "$api_recovery_resume/resumption" ]] || fail 'resumption output differs'
  continuation=$api_recovery_resume
  mkdir -m700 "$resumed/bin"
  install -m500 "$own/grain-runtime" "$resumed/bin/grain-runtime"
  controller_runtime=$resumed/bin/grain-runtime
  cp "$fresh/source-input-sha256.txt" "$resumed/source-input-sha256.txt"
  sha256sum "$controller_runtime" >>"$resumed/source-input-sha256.txt"
  preserve_existing_exit=0 configured=1 controller_created=1 controller_staged=1
  world_phase_record resume-runtime-upgrade started
  timeout 120 sudo -n -- "$installer" controller-runtime-upgrade "$store" "$helper" "$controller_runtime" >"$resumed/runtime-upgrade.json"
  jq -e --arg expected "$expected_runtime" --arg previous "$(jq -er .runtime_sha256 "$resumed/prepared.json")" '.runtimeSha256 == $expected and .previousRuntimeSha256 == $previous' "$resumed/runtime-upgrade.json" >/dev/null || fail 'resumption runtime upgrade differs'
  world_phase_record resume-runtime-upgrade completed "$resumed/runtime-upgrade.json" "$resumed/prepared.json" "$resumed/prior-exit.json"
  cp "$fresh/controller-status.json" "$resumed/public-listener.json"
  jq -e --arg binary "$GRAINS_ROOT/controller/public-listener/mini" --arg digest "$(sha256sum "$BIN/mini" | cut -d ' ' -f1)" --arg socket "$run/world/sock/participant/host.sock" '.publicListener.binary == $binary and .publicListener.binarySha256 == $digest and .publicListener.socket == $socket and .publicListener.controllerUid == .controllerUid' "$resumed/public-listener.json" >/dev/null || fail 'resumption listener differs'
  export SPK_PUBLIC_LISTENER_RECEIPT=$resumed/public-listener.json
  world_phase_record resume-services started
  systemctl --user start "mini-spk-broker@$store.service"
  for ((i=0;i<100;i++)); do [[ ! -S $BROKER_SOCKET ]] || break; sleep .1; done
  [[ -S $BROKER_SOCKET && $(stat -c '%u:%a' "$BROKER_SOCKET") == "$op_uid:600" ]] || fail 'resumption broker differs'
  "$journey" phase "$run/world" services >"$resumed/services.log" 2>&1
  world_phase_record resume-services completed "$run/world/sock/operator.pid.identity.json" "$run/world/sock/participant.pid.identity.json"
  world_phase_record payer-route-successor started
  timeout 120 sudo -n -- "$installer" controller-status "$store" "$helper" >"$resumed/controller-status.json"
  timeout 120 sudo -n -- "$installer" controller-journal "$store" "$helper" >"$resumed/controller-journal.json"
  timeout 120 sudo -n -- "$installer" controller-export "$store" "$helper" >"$resumed/controller-export.json"
  jq -n --arg root "$run/agent-lifetime" --arg allocation "$run/agent-lifetime/allocation.json" --arg profile "$profile" --arg host "$BIN/minidregg-host" --arg config "$config" --arg spkHost "$BIN/spk-host" --arg repo "$repo" --arg status "$resumed/controller-status.json" --arg journal "$resumed/controller-journal.json" --arg stop "$continuation/stop.json" --arg evidence "$resumed/controller-export.json" --arg output "$run/agent-lifetime/repair-payer-custody" '{protocol:"mini-application-payer-successor-v1",attachmentRoot:$root,allocation:$allocation,profile:$profile,host:$host,hostConfig:$config,spkHost:$spkHost,correctedRepo:$repo,controllerStatus:$status,controllerJournal:$journal,controllerEvidence:$evidence,inspectionMode:"detached",stopReceipt:$stop,outputDir:$output,successorName:"oracle-agent-v2"}' >"$resumed/payer-successor-request.json"
  timeout 1800 python3 -B "$repo/scripts/application-payer-successor.py" "$resumed/payer-successor-request.json" >"$resumed/payer-successor.stdout" 2>"$resumed/payer-successor.stderr"
  [[ $(cat "$resumed/payer-successor.stdout") == "$run/agent-lifetime/repair-payer-custody/complete.json" ]] || fail 'payer successor output differs'
  jq -e '.protocol == "mini-application-payer-successor-complete-v1" and .app == "9101" and .successor == "oracle-agent-v2" and .grantChanged == false and .sessionChanged == false' "$run/agent-lifetime/repair-payer-custody/complete.json" >/dev/null || fail 'payer successor receipt differs'
  world_phase_record payer-route-successor completed "$resumed/payer-successor-request.json" "$run/agent-lifetime/repair-payer-custody/complete.json" "$run/agent-lifetime/registered-agent-route.json"
  old_generation=$(jq -er .boundary.old_generation "$continuation/prepared.json")
  cp "$state/apps/9101/g$old_generation/record.json" "$continuation/old-record-after-stop.json"
  cp -a "$state/apps/9101/g$old_generation/stop-completion" "$continuation/stop-completion"
  world_reclaim_stopped_agent_socket 9101 "$old_generation" api-recovery-${continuation##*-}
  world_phase_record retire-incarnation completed "$continuation/stop.json" "$continuation/old-record-after-stop.json" "$run/native-agent-socket-reclaims/api-recovery-${continuation##*-}/result.json"
  world_phase_record successor-start started
  timeout 1800 "$BIN/spk-host" grain start "$profile" 9101 >"$continuation/successor-start.json" 2>"$continuation/successor-start.stderr"
  jq -e --arg old "$old_generation" '.protocol == "mini-spk-grain-start-v1" and .app == "9101" and (.generation | tonumber) > ($old | tonumber) and .startAction.kind == "continue" and .completion.completionReceipt.eventId' "$continuation/successor-start.json" >/dev/null || fail 'resumption successor differs'
  world_phase_record successor-start completed "$continuation/successor-start.json"
  world_phase_record enrollment started
}

world_recover_application_api() {
  if [[ -n ${api_recovery_resume:-} ]]; then world_resume_api_recovery; return; fi
  local fresh expected_runtime current_unit previous_execution reclaim_label
  op_uid=$(id -u)
  export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid} BIN=$run/bin
  store=$(jq -er '.store | select(test("^[0-9a-f]{16}$"))' "$run/world-identity.json")
  helper=$(jq -er .helper "$run/world-identity.json")
  export GRAINS_ROOT=/var/lib/mini-spk-worlds/$store BROKER_SOCKET=/var/lib/mini-spk-worlds/$store/runtime-$store/broker.sock
  [[ $(jq -er .root "$run/world-identity.json") == "$GRAINS_ROOT" && $helper =~ ^/usr/local/libexec/mini-spk-volume-helper-[0-9a-f]{16}$ ]] || fail 'API recovery namespace differs'
  installer=$repo/deploy/spk-host/install-user-world
  units=$XDG_RUNTIME_DIR/systemd/user
  config=$run/world/store/base/workroom/deployment/pinned-config.json
  profile=$(jq -er .profilePath "$run/world/evidence/profile-result.json")
  state=$(jq -er .stateRoot "$run/world/evidence/profile-result.json")
  expected_runtime=${ORACLE_RECOVERY_RUNTIME_SHA256:?qualified runtime required}
  [[ ( $api_recovery_request == --readiness || $api_recovery_request =~ ^[0-9a-f]{32}$ ) && $expected_runtime =~ ^[0-9a-f]{64}$
      && $(sha256sum "$own/grain-runtime" | cut -d ' ' -f1) == "$expected_runtime" ]] || fail 'API recovery request/runtime pin differs'
  [[ ${ORACLE_SOCKET_RECLAIM_BIN:-} == /* && ${ORACLE_SOCKET_RECLAIM_SHA256:-} =~ ^[0-9a-f]{64}$
      && $(sha256sum "$ORACLE_SOCKET_RECLAIM_BIN" | cut -d ' ' -f1) == "$ORACLE_SOCKET_RECLAIM_SHA256" ]] || fail 'native socket reclaimer pin differs'
  if [[ -n ${ORACLE_RECOVERY_MINI_BIN:-}${ORACLE_RECOVERY_MINI_SHA256:-} ]]; then
    [[ ${ORACLE_RECOVERY_MINI_BIN:-} == /* && -f $ORACLE_RECOVERY_MINI_BIN && ! -L $ORACLE_RECOVERY_MINI_BIN && ${ORACLE_RECOVERY_MINI_SHA256:-} =~ ^[0-9a-f]{64}$
        && $(sha256sum "$ORACLE_RECOVERY_MINI_BIN" | cut -d ' ' -f1) == "$ORACLE_RECOVERY_MINI_SHA256" ]] || fail 'qualified Mini input differs'
  fi
  if [[ -n ${ORACLE_RECOVERY_CONSENT_MEMORY_MIB:-} ]]; then
    [[ $ORACLE_RECOVERY_CONSENT_MEMORY_MIB =~ ^[1-9][0-9]{2,4}$ && $ORACLE_RECOVERY_CONSENT_MEMORY_MIB -ge 256 && $ORACLE_RECOVERY_CONSENT_MEMORY_MIB -le 16384 && $((ORACLE_RECOVERY_CONSENT_MEMORY_MIB % 256)) == 0 ]] || fail 'consent memory input differs'
  fi
  sha256sum -c "$run/binary-sha256.txt" >"$run/api-original-binary-check.txt"
  fresh=$(mktemp -d "$run/api-preflight.XXXXXXXX")
  timeout 120 sudo -n -- "$installer" controller-export "$store" "$helper" >"$fresh/controller-export.json"
  timeout 120 sudo -n -- "$installer" controller-status "$store" "$helper" >"$fresh/controller-status.json"
  previous_execution=$(python3 -B "$repo/deploy/oracle/acceptance/recover_application_api.py" --previous "$run")
  current_unit=$(jq -er .unit "$previous_execution/successor-start.json")
  [[ $current_unit == mini-spk-s"$store"-a9101-g*.service ]] || fail 'API recovery unit differs'
  systemctl --user show "$current_unit" -p Id -p ActiveState -p MainPID -p Job >"$fresh/manager.txt"
  [[ $(systemctl --user show "mini-spk-broker@$store.service" -p ActiveState --value) == inactive
      && ! -S $run/world/sock/operator/host.sock && ! -S $run/world/sock/participant/host.sock ]] || fail 'API recovery services are not stopped'
  world_source_manifest >"$fresh/source-input-sha256.txt"
  sha256sum "$own/grain-runtime" "$ORACLE_SOCKET_RECLAIM_BIN" >>"$fresh/source-input-sha256.txt"
  [[ -z ${ORACLE_RECOVERY_MINI_BIN:-} ]] || sha256sum "$ORACLE_RECOVERY_MINI_BIN" >>"$fresh/source-input-sha256.txt"
  continuation=$(python3 -B "$repo/deploy/oracle/acceptance/recover_application_api.py" "$run" "$fresh" "$api_recovery_request")
  [[ $continuation == "$run/continuations/application-api-recovery-"* && ${continuation##*-} =~ ^[0-9]+$ ]] || fail 'API recovery output differs'
  mkdir -m700 "$continuation/bin"
  install -m500 "$own/grain-runtime" "$continuation/bin/grain-runtime"
  controller_runtime=$continuation/bin/grain-runtime
  cp "$fresh/source-input-sha256.txt" "$continuation/recovery-input-sha256.txt"
  sha256sum "$controller_runtime" >>"$continuation/recovery-input-sha256.txt"
  if [[ -n ${ORACLE_RECOVERY_MINI_BIN:-} ]]; then
    install -m500 "$ORACLE_RECOVERY_MINI_BIN" "$continuation/bin/mini"
    sha256sum "$continuation/bin/mini" >>"$continuation/recovery-input-sha256.txt"
  fi
  preserve_existing_exit=0
  configured=1 controller_created=1 controller_staged=1
  world_recovery_operator_upgrades
  world_phase_record runtime-upgrade started
  timeout 120 sudo -n -- "$installer" controller-runtime-upgrade "$store" "$helper" "$controller_runtime" >"$continuation/runtime-upgrade.json"
  jq -e --arg expected "$expected_runtime" --arg previous "$(jq -er .boundary.runtime_sha256 "$continuation/prepared.json")" '.runtimeSha256 == $expected and .previousRuntimeSha256 == $previous' "$continuation/runtime-upgrade.json" >/dev/null || fail 'API runtime upgrade differs'
  world_phase_record runtime-upgrade completed "$continuation/runtime-upgrade.json"
  cp "$fresh/controller-status.json" "$continuation/public-listener.json"
  jq -e --arg binary "$GRAINS_ROOT/controller/public-listener/mini" --arg digest "$(sha256sum "$BIN/mini" | cut -d ' ' -f1)" --arg socket "$run/world/sock/participant/host.sock" '
    .publicListener.binary == $binary and .publicListener.binarySha256 == $digest and
    .publicListener.socket == $socket and .publicListener.controllerUid == .controllerUid' "$continuation/public-listener.json" >/dev/null || fail 'API public listener pin differs'
  export SPK_PUBLIC_LISTENER_RECEIPT=$continuation/public-listener.json
  world_phase_record services started
  systemctl --user start "mini-spk-broker@$store.service"
  for ((i=0;i<100;i++)); do [[ ! -S $BROKER_SOCKET ]] || break; sleep .1; done
  [[ -S $BROKER_SOCKET && $(stat -c '%u:%a' "$BROKER_SOCKET") == "$op_uid:600" ]] || fail 'API recovery broker readiness failed'
  "$journey" phase "$run/world" services >"$continuation/services.log" 2>&1
  world_phase_record services completed "$run/world/sock/operator.pid.identity.json" "$run/world/sock/participant.pid.identity.json"
  if [[ $(jq -er '.boundary.kind // "unreserved-api"' "$continuation/prepared.json") == unreserved-api ]]; then
    world_phase_record controller-start started
    timeout 240 sudo -n -- "$installer" controller-start "$store" "$helper" >"$continuation/controller-start.json"
    world_phase_record controller-start completed "$continuation/controller-start.json"
    world_phase_record native-recovery started
    timeout 1850 sudo -n -- "$installer" controller-recover-api-unreserved "$store" "$helper" "$api_recovery_request" >"$continuation/native-recovery.json" 2>"$continuation/native-recovery.stderr"
    timeout 120 sudo -n -- "$installer" controller-journal "$store" "$helper" >"$continuation/after-api-journal.json"
    python3 -B "$repo/deploy/oracle/acceptance/recover_application_api.py" --check-native "$continuation"
    world_phase_record native-recovery completed "$continuation/native-recovery.json" "$continuation/after-api-journal.json"
    world_phase_record native-reconciliation started
    if jq -e '.parentHold != null' "$continuation/after-api-journal.json" >/dev/null; then
      timeout 1850 sudo -n -- "$installer" controller-reconcile "$store" "$helper" parent >"$continuation/reconcile-parent.stdout" 2>"$continuation/reconcile-parent.stderr"
    fi
    timeout 1850 sudo -n -- "$installer" controller-reconcile "$store" "$helper" effects >"$continuation/reconcile-effects.stdout" 2>"$continuation/reconcile-effects.stderr"
    timeout 1850 sudo -n -- "$installer" controller-reconcile "$store" "$helper" foreground-audited >"$continuation/reconcile-foreground.stdout" 2>"$continuation/reconcile-foreground.stderr"
    timeout 120 sudo -n -- "$installer" controller-journal "$store" "$helper" >"$continuation/terminal-journal.json"
    timeout 120 sudo -n -- "$installer" controller-export "$store" "$helper" >"$continuation/terminal-export.json"
    python3 -B "$repo/deploy/oracle/acceptance/recover_application_api.py" --check-terminal "$continuation"
    world_phase_record native-reconciliation completed "$continuation/terminal-journal.json" "$continuation/terminal-export.json"
    # Audited is already reported and has no definitive response: no result ACK
    # applies. The native audit remains the retained terminal observation.
  fi
  world_controller_stop before-api-incarnation-retirement
  world_phase_record retire-incarnation started
  timeout 1800 "$BIN/spk-host" grain stop "$profile" 9101 >"$continuation/stop.json" 2>"$continuation/stop.stderr"
  local old_generation
  old_generation=$(jq -er .boundary.old_generation "$continuation/prepared.json")
  jq -e --arg old "$old_generation" '.protocol == "mini-spk-grain-stop-v1" and .app == "9101" and .generation == $old' "$continuation/stop.json" >/dev/null || fail 'API recovery STOP identity differs'
  cp "$state/apps/9101/g$old_generation/record.json" "$continuation/old-record-after-stop.json"
  cp -a "$state/apps/9101/g$old_generation/stop-completion" "$continuation/stop-completion"
  reclaim_label=api-recovery-${continuation##*-}
  world_reclaim_stopped_agent_socket 9101 "$old_generation" "$reclaim_label"
  world_phase_record retire-incarnation completed "$continuation/stop.json" "$continuation/old-record-after-stop.json" "$run/native-agent-socket-reclaims/$reclaim_label/result.json"
  world_phase_record successor-start started
  timeout 1800 "$BIN/spk-host" grain start "$profile" 9101 >"$continuation/successor-start.json" 2>"$continuation/successor-start.stderr"
  jq -e --arg old "$old_generation" '.protocol == "mini-spk-grain-start-v1" and .app == "9101" and (.generation | tonumber) > ($old | tonumber) and .startAction.kind == "continue" and .completion.completionReceipt.eventId' "$continuation/successor-start.json" >/dev/null || fail 'API successor START differs'
  world_phase_record successor-start completed "$continuation/successor-start.json"
  world_phase_record enrollment started
}

world_phase_record() {
  python3 -B "$repo/deploy/oracle/acceptance/continue_controller.py" --phase \
    "$run" "$continuation/phases" "$@"
}

# A checkpoint is a checked observation of an unstarted boundary, never a
# request to replay a source phase. Each new execution gets its own directory.
world_continue_checkpoint() {
  local run=$1 repo=$2 fresh target bundle app
  op_uid=$(id -u)
  export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid}
  export BIN=$run/bin
  store=$(jq -er .store "$run/world-identity.json")
  helper=$(jq -er .helper "$run/world-identity.json")
  export GRAINS_ROOT=/var/lib/mini-spk-worlds/$store
  export BROKER_SOCKET=$GRAINS_ROOT/runtime-$store/broker.sock
  installer=$repo/deploy/spk-host/install-user-world
  units=$XDG_RUNTIME_DIR/systemd/user
  config=$run/world/store/base/workroom/deployment/pinned-config.json
  profile=$(jq -er .profilePath "$run/world/evidence/profile-result.json")
  state=$(jq -er .stateRoot "$run/world/evidence/profile-result.json")
  fresh=$(mktemp -d "$run/checkpoint-preflight.XXXXXXXX")
  timeout 120 sudo -n -- "$installer" controller-export "$store" "$helper" >"$fresh/controller-export.json"
  timeout 120 sudo -n -- "$installer" controller-status "$store" "$helper" >"$fresh/controller-status.json"
  world_source_manifest >"$fresh/source-input-sha256.txt"
  sha256sum "$own/mini" "$own/grain-runtime" >>"$fresh/source-input-sha256.txt"
  continuation=$(python3 -B "$repo/deploy/oracle/acceptance/continue_controller.py" --begin-checkpoint \
    "$checkpoint" "$spk" "$inventory" "$benchmark" "$repo" "$fresh/controller-export.json" \
    "$fresh/controller-status.json" "$fresh/source-input-sha256.txt")
  [[ $continuation == "$run/continuations/checkpoint-"* ]] || fail 'checkpoint execution path differs'
  recovery_manifest=$continuation/recovery-input-sha256.txt
  (set -o noclobber; cat "$fresh/source-input-sha256.txt" >"$recovery_manifest")
  controller_runtime=$run/continuations/session-refusal-1/bin/grain-runtime
  [[ $(sha256sum "$controller_runtime" | cut -d ' ' -f1) == $(sha256sum "$own/grain-runtime" | cut -d ' ' -f1) ]] || fail 'checkpoint runtime differs'
  preserve_existing_exit=0
  configured=1 controller_created=1 controller_staged=1

  world_phase_record public-listener started
  timeout 120 sudo -n -- "$installer" controller-public-listener "$store" "$helper" "$own/mini" \
    >"$continuation/public-listener.json"
  jq -e --arg binary "$GRAINS_ROOT/controller/public-listener/mini" \
    --arg digest "$(sha256sum "$own/mini" | cut -d ' ' -f1)" --arg socket "$run/world/sock/participant/host.sock" \
    --slurpfile before "$fresh/controller-status.json" '
    del(.publicListener) == $before[0] and .publicListener.binary == $binary and
    .publicListener.binarySha256 == $digest and .publicListener.socket == $socket and
    .publicListener.controllerUid == .controllerUid' "$continuation/public-listener.json" >/dev/null || fail 'listener registration pins differ'
  export SPK_PUBLIC_LISTENER_RECEIPT=$continuation/public-listener.json
  world_phase_record public-listener completed "$continuation/public-listener.json"

  world_phase_record services started
  systemctl --user start "mini-spk-broker@$store.service"
  for ((i=0;i<100;i++)); do [[ ! -S $BROKER_SOCKET ]] || break; sleep .1; done
  [[ -S $BROKER_SOCKET && $(stat -c '%u:%a' "$BROKER_SOCKET") == "$op_uid:600" ]] || fail 'checkpoint broker readiness failed'
  "$journey" phase "$run/world" services >"$continuation/services.log" 2>&1
  world_phase_record services completed "$run/world/sock/operator.pid.identity.json" \
    "$run/world/sock/participant.pid.identity.json" "$continuation/services.log"
  for app in 9101 9201; do
    timeout 1800 "$BIN/spk-host" grain status "$profile" "$app" >"$continuation/status-$app.json"
    jq -e --arg app "$app" '.app == $app and .installCompleted and (.runs | length == 0)' \
      "$continuation/status-$app.json" >/dev/null || fail 'checkpoint requires installed grains with no START'
  done
  world_phase_record bootstrap-target started
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" prepare-bootstrap-dispatch "$run" "$repo" \
    "$run/agent-lifetime/controller-create.json" >"$continuation/bootstrap-target.stdout" 2>"$continuation/bootstrap-target.stderr"
  target=$(cat "$continuation/bootstrap-target.stdout")
  [[ $target == "$run/agent-lifetime/native-prepare-bootstrap-dispatch/controller-update/controller.json" ]] || fail 'bootstrap target differs'
  bundle=$(dirname "$target")
  world_phase_record bootstrap-target completed "$target"
  world_phase_record worker-policy started
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" prepare-worker-policy "$run" "$repo" "$target" \
    >"$continuation/worker-policy.stdout" 2>"$continuation/worker-policy.stderr"
  python3 - "$run/agent-lifetime/native-prepare-worker-policy/worker-policy.json" "$target" <<'PYPOLICY'
import hashlib,json,pathlib,sys
p,t=map(pathlib.Path,sys.argv[1:]); v=json.loads(p.read_bytes()); config=json.loads(t.read_bytes())
read=lambda f:json.loads(pathlib.Path(f).read_bytes())
assert v['protocol']=='mini-oracle-bootstrap-worker-policy-v1' and v['workerGeneration']=='1'
assert v['controllerConfigSha256']==hashlib.sha256(t.read_bytes()).hexdigest()
assert v['workers']==[config[k]['subject'] for k in ('toolTask','dispatchTask')]
o=read(pathlib.Path(v['attempt'])/'outcome.json')
assert o['type']=='confirmed' and o['confirmation'] in ('installed','replayed')
assert {k:o[k] for k in ('transactionId','eventId','acceptedCount','worldRoot')}==v['receipt']
b,a=read(pathlib.Path(v['before'])/'view.json'),read(pathlib.Path(v['after'])/'view.json')
assert b['version']=='0' and a['version']=='1' and a['previous']==b['address']
assert b['policyId']==a['policyId']==config['task']
PYPOLICY
  world_phase_record worker-policy completed "$run/agent-lifetime/native-prepare-worker-policy/worker-policy.json" \
    "$run/agent-lifetime/native-prepare-worker-policy/owner-policy-attempt/outcome.json"
  world_phase_record bootstrap-enrollment started
  world_controller_enroll bootstrap-dispatch "$bundle" bootstrap-dispatch
  world_phase_record bootstrap-enrollment completed "$run/agent-lifetime/enrollment-bootstrap-dispatch/request.json" \
    "$run/agent-lifetime/enrollment-bootstrap-dispatch/result.json" "$run/agent-lifetime/enrollment-bootstrap-dispatch/after.json"
  world_phase_record controller-start started
  timeout 240 sudo -n -- "$installer" controller-start "$store" "$helper" >"$continuation/controller-bootstrap-start.json"
  world_phase_record controller-start completed "$continuation/controller-bootstrap-start.json"
  world_phase_record session-and-grant started
  world_controller_birth
  jq -e '.isError == false and .operationId != null' "$run/agent-lifetime/session-birth.retained-result.json" >/dev/null
  world_phase_record session-and-grant completed "$run/agent-lifetime/session-birth.retained-result.json" \
    "$run/agent-lifetime/issued-grant.json" "$run/agent-lifetime/session-birth.ack.json"
}

# Resume the retained native operation and reservation, never submit its tool
# request again. All original client output remains at its original path.
world_recover_foreground() {
  local run=$1 repo=$2 fresh candidate old_mini new_mini request_id app
  op_uid=$(id -u)
  export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid} BIN=$run/bin
  store=$(jq -er .store "$run/world-identity.json")
  helper=$(jq -er .helper "$run/world-identity.json")
  export GRAINS_ROOT=/var/lib/mini-spk-worlds/$store
  export BROKER_SOCKET=$GRAINS_ROOT/runtime-$store/broker.sock
  installer=$repo/deploy/spk-host/install-user-world
  jq -e --arg run "$run" --arg spk "$spk" --arg inventory "$inventory" --arg benchmark "$benchmark" \
    '.run == $run and .spk.path == $spk and .inventory.path == $inventory and .benchmark.path == $benchmark' \
    "$recovery_plan" >/dev/null || fail 'recovery plan differs from selected v5 inputs'
  units=$XDG_RUNTIME_DIR/systemd/user
  config=$run/world/store/base/workroom/deployment/pinned-config.json
  profile=$(jq -er .profilePath "$run/world/evidence/profile-result.json")
  state=$(jq -er .stateRoot "$run/world/evidence/profile-result.json")
  fresh=$(mktemp -d "$run/foreground-recovery-preflight.XXXXXXXX")
  timeout 120 sudo -n -- "$installer" controller-export "$store" "$helper" >"$fresh/controller-export.json"
  timeout 120 sudo -n -- "$installer" controller-status "$store" "$helper" >"$fresh/controller-status.json"
  controller_runtime=$(jq -er .runtime.path "$recovery_plan")
  candidate=$(jq -er .public_mini.path "$recovery_plan")
  old_mini=$(jq -er .old_public_mini_sha256 "$recovery_plan")
  new_mini=$(jq -er .public_mini.sha256 "$recovery_plan")
  request_id=$(jq -er .request_id "$recovery_plan")
  world_source_manifest >"$fresh/source-input-sha256.txt"
  sha256sum "$controller_runtime" "$candidate" >>"$fresh/source-input-sha256.txt"
  continuation=$(python3 -B "$repo/deploy/oracle/acceptance/recover_foreground.py" directory "$recovery_plan")
  python3 -B "$repo/deploy/oracle/acceptance/recover_foreground.py" prepare "$recovery_plan" \
    "$fresh/controller-export.json" "$fresh/controller-status.json" "$fresh/source-input-sha256.txt" "$continuation" \
    >"$fresh/prepared.stdout"
  recovery_manifest=$continuation/recovery-input-sha256.txt
  (set -o noclobber; cat "$fresh/source-input-sha256.txt" >"$recovery_manifest")
  configured=1 controller_created=1 controller_staged=1 preserve_existing_exit=0
  if [[ $(jq -r '.goal // "resume-session"' "$recovery_plan") == settle-refusal ]]; then
    preserve_retained_namespace=1
  fi
  world_phase_record runtime-upgrade started
  timeout 120 sudo -n -- "$installer" controller-runtime-upgrade "$store" "$helper" "$controller_runtime" \
    >"$continuation/runtime-upgrade.json"
  jq -e --arg wanted "$(jq -er .runtime.sha256 "$recovery_plan")" '.runtimeSha256 == $wanted' \
    "$continuation/runtime-upgrade.json" >/dev/null || fail 'recovery runtime differs'
  world_phase_record runtime-upgrade completed "$continuation/runtime-upgrade.json"
  world_phase_record public-listener-upgrade started
  if [[ $old_mini == "$new_mini" ]]; then
    timeout 120 sudo -n -- "$installer" controller-status "$store" "$helper" \
      >"$continuation/public-listener-status.json"
    jq -e --arg digest "$new_mini" '.stopped == true and .publicListener.binarySha256 == $digest' \
      "$continuation/public-listener-status.json" >/dev/null || fail 'already-qualified public listener differs'
    jq '. + {publicListenerSelection:"already-qualified"}' "$continuation/public-listener-status.json" \
      >"$continuation/public-listener.json"
  else
    timeout 120 sudo -n -- "$installer" controller-public-listener-upgrade "$store" "$helper" "$candidate" "$old_mini" "$new_mini" \
      >"$continuation/public-listener.json"
  fi
  jq -e --arg digest "$new_mini" '.publicListener.binarySha256 == $digest' "$continuation/public-listener.json" >/dev/null
  export SPK_PUBLIC_LISTENER_RECEIPT=$continuation/public-listener.json
  world_phase_record public-listener-upgrade completed "$continuation/public-listener.json"
  world_phase_record services started
  systemctl --user start "mini-spk-broker@$store.service"
  for ((i=0;i<100;i++)); do [[ ! -S $BROKER_SOCKET ]] || break; sleep .1; done
  [[ -S $BROKER_SOCKET && $(stat -c '%u:%a' "$BROKER_SOCKET") == "$op_uid:600" ]] || fail 'recovery broker readiness failed'
  "$journey" phase "$run/world" services >"$continuation/services.log" 2>&1
  for app in 9101 9201; do
    timeout 1800 "$BIN/spk-host" grain status "$profile" "$app" >"$continuation/status-$app.json"
    jq -e --arg app "$app" '.app == $app and .installCompleted and (.runs | length == 0)' "$continuation/status-$app.json" >/dev/null
  done
  world_phase_record services completed "$continuation/status-9101.json" "$continuation/status-9201.json"
  world_phase_record controller-start started
  timeout 240 sudo -n -- "$installer" controller-start "$store" "$helper" >"$continuation/controller-start.json"
  world_phase_record controller-start completed "$continuation/controller-start.json"
  world_phase_record exact-foreground-recovery started
  # Exactly one private admin invocation. Timeout/failure leaves this phase
  # started; there is no retry, result substitute or unconditional ACK.
  timeout 1850 sudo -n -- "$installer" controller-recover-session "$store" "$helper" "$request_id" \
    >"$continuation/recovery-result.json" 2>"$continuation/recovery.stderr"
  timeout 120 sudo -n -- "$installer" controller-tool-result "$store" "$helper" "$request_id" \
    >"$continuation/retained-result.json"
  timeout 120 sudo -n -- "$installer" controller-journal "$store" "$helper" >"$continuation/settled-journal.json"
  timeout 120 sudo -n -- "$installer" controller-export "$store" "$helper" >"$continuation/settled-export.json"
  python3 -B "$repo/deploy/oracle/acceptance/recover_foreground.py" result "$recovery_plan" \
    "$continuation/recovery-result.json" "$continuation/retained-result.json" "$continuation/settled-journal.json" "$continuation/settled-export.json"
  if [[ ${preserve_retained_namespace:-0} == 1 ]]; then
    world_phase_record exact-foreground-recovery completed "$continuation/recovery-result.json" \
      "$continuation/retained-result.json" "$continuation/settled-journal.json" "$continuation/settled-export.json"
    world_phase_record refusal-ack started
    timeout 120 sudo -n -- "$installer" controller-tool-ack "$store" "$helper" "$request_id" \
      >"$continuation/refusal.ack.json"
    jq -e --arg id "$request_id" '.type == "tool-acknowledged" and .requestId == $id and .isError != true' \
      "$continuation/refusal.ack.json" >/dev/null
    timeout 120 sudo -n -- "$installer" controller-journal "$store" "$helper" >"$continuation/acknowledged-journal.json"
    world_phase_record refusal-ack completed "$continuation/refusal.ack.json" "$continuation/acknowledged-journal.json"
    foreground_settlement_only=1
    return
  fi
  (set -o noclobber; cat "$continuation/retained-result.json" >"$run/agent-lifetime/session-birth.retained-result.json")
  world_phase_record exact-foreground-recovery completed "$continuation/recovery-result.json" \
    "$continuation/retained-result.json" "$continuation/settled-journal.json" "$continuation/settled-export.json"
  world_phase_record session-grant started
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" issue-grant "$run" "$repo" \
    "$continuation/retained-result.json" >"$continuation/issue-grant.stdout" 2>"$continuation/issue-grant.stderr"
  timeout 120 sudo -n -- "$installer" controller-tool-ack "$store" "$helper" "$request_id" \
    >"$run/agent-lifetime/session-birth.ack.json"
  jq -e --arg id "$request_id" '.type == "tool-acknowledged" and .requestId == $id and .isError != true' \
    "$run/agent-lifetime/session-birth.ack.json" >/dev/null
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" prepare-route "$run" "$repo" \
    "$run/agent-lifetime/controller-create.json" >"$continuation/prepare-route.stdout" 2>"$continuation/prepare-route.stderr"
  world_phase_record session-grant completed "$run/agent-lifetime/issued-grant.json" "$run/agent-lifetime/session-birth.ack.json"
}

# Run only after the world services have stopped. The planner observes physical
# state; all unmount/destroy effects still go through native volume custody.
world_cleanup_volumes() {
  local preserve=$1 evidence=$2 request action status_request
  mkdir -m 700 "$evidence" || return
  status_request=$(jq -cer --arg root "$GRAINS_ROOT" \
    '{verb:"volumes-status",store:.store,deploymentId:.deploymentId,volumesRoot:($root+"/volumes")}' \
    "/etc/mini-spk-volumes/$store.json") || return
  timeout 120 sudo -n -- "$helper" "$status_request" >"$evidence/status.json" || return
  python3 -B "$repo/deploy/oracle/acceptance/volume_cleanup.py" "$GRAINS_ROOT" \
    "$evidence/status.json" >"$evidence/plan.json" || return
  while IFS= read -r request; do
    action=$(jq -er .action <<<"$request") || return
    if [[ $action == unmount ]]; then
      timeout 120 sudo -n -- "$helper" "$(jq -c .request <<<"$request")" || return
    elif [[ $action != already-unmounted ]]; then
      return 1
    fi
    if [[ $preserve == false ]]; then
      timeout 120 sudo -n -- "$helper" "$(jq -c '.request | .verb="destroy"' <<<"$request")" || return
    fi
  done < <(jq -c '.volumes[]' "$evidence/plan.json")
}

world_cleanup() {
  local result=${1:-$?} cleanup_result=0 unit preserve_namespace=false exit_path volume_evidence
  trap - EXIT INT TERM
  if [[ -d $run/browser ]]; then
    python3 -B "$repo/deploy/oracle/acceptance/browser_edge.py" stop "$run/browser" >>"$run/cleanup.log" 2>&1 || cleanup_result=1
  fi
  if [[ ${configured:-0} == 1 ]]; then
    if [[ ${controller_created:-0} == 1 ]]; then
      world_controller_stop cleanup >>"$run/cleanup.log" 2>&1 || cleanup_result=1
      if [[ ${controller_staged:-0} == 1 ]]; then
        timeout 120 sudo -n -- "$installer" controller-journal "$store" "$helper" \
          >"$run/agent-lifetime/controller-final-journal.json" 2>>"$run/cleanup.log" || cleanup_result=1
      fi
      # The public listener owns its socket's ACL. Stop it before removing the
      # controller registration and restoring its exact ancestor ACL grants.
      "$journey" stop-services "$run/world" >>"$run/cleanup.log" 2>&1 || cleanup_result=1
      if [[ $result == 0 && $cleanup_result == 0 && ${preserve_retained_namespace:-0} != 1 ]]; then
        timeout 120 sudo -n -- "$installer" controller-remove "$store" "$helper" \
          >"$run/agent-lifetime/controller-remove.json" 2>>"$run/cleanup.log" || cleanup_result=1
      fi
      [[ $cleanup_result == 0 ]] || preserve_namespace=true
    fi
    if [[ ${controller_created:-0} != 1 ]]; then
      "$journey" stop-services "$run/world" >>"$run/cleanup.log" 2>&1 || cleanup_result=1
    fi
    while read -r unit; do
      [[ -n $unit ]] || continue
      journalctl --user --no-pager -u "$unit" >>"$run/residents.log" 2>&1 || cleanup_result=1
      systemctl --user stop "$unit" >>"$run/cleanup.log" 2>&1 || cleanup_result=1
    done < <(systemctl --user list-units --all --plain --no-legend "mini-spk-s$store-a*.service" "mini-spk-supervisor@$store-*.service" "mini-spk-supervisor-s$store@*.service" | awk '{print $1}')
    systemctl --user stop "mini-spk-broker@$store.service" >>"$run/cleanup.log" 2>&1 || cleanup_result=1
    journalctl --user --no-pager -u "mini-spk-broker@$store.service" >"$run/broker.log" 2>&1 || cleanup_result=1
    # Keep the native receiving journals even when the first install/start fails.
    # They are private evidence, not public report content; no data-image copy.
    if [[ -n ${state:-} && -d $state/apps ]]; then
      tar -C "$state" -cf "$run/native-state.tar" apps 2>>"$run/cleanup.log" || { cleanup_result=1; preserve_namespace=true; }
    fi
    # A failed journey keeps its own stopped namespace and state volumes for
    # diagnosis/recovery. Never erase an uncertain admitted operation's journal.
    [[ $result == 0 && ${preserve_retained_namespace:-0} != 1 ]] || preserve_namespace=true
    if [[ $cleanup_result == 0 ]]; then
      if volume_evidence=$(mktemp -d "${continuation:-$run}/volume-cleanup.XXXXXXXX"); then
        # The helper owns this new child; mktemp protects the unique parent.
        world_cleanup_volumes "$preserve_namespace" "$volume_evidence/observations" \
          >>"$run/cleanup.log" 2>&1 || cleanup_result=1
      else
        cleanup_result=1
      fi
    fi
    [[ $cleanup_result == 0 ]] || preserve_namespace=true
    # This registry is uniquely created by this run. A failed unmount prevents
    # installer removal; preserve the entire namespace for diagnosis in that case.
    if [[ $preserve_namespace == false ]]; then
    sudo -n -- "$installer" remove "$store" "$helper" >>"$run/cleanup.log" 2>&1 || cleanup_result=1
    rm -f "$units/mini-spk-broker@$store.service"
    while read -r unit; do [[ -z $unit ]] || rm -f "$units/$unit"; done < <(find "$units" -maxdepth 1 -type f \( -name "*s$store*" -o -name "mini-spk-supervisor@$store-*.service" \) -printf '%f\n')
    systemctl --user daemon-reload
    [[ ! -e /etc/mini-spk-volumes/$store.json && ! -e /etc/sudoers.d/mini-spk-$store && ! -e $helper ]] || cleanup_result=1
    fi
  fi
  if [[ -d $run && ${preserve_existing_exit:-0} != 1 ]]; then
    exit_path=$run/exit.json
    if [[ -n ${continuation:-} && -d $continuation ]]; then
      exit_path=$continuation/exit.json
    fi
    jq -n --argjson execution "$result" --argjson cleanup "$cleanup_result" --argjson preserved "$preserve_namespace" '{execution_exit:$execution,cleanup_exit:$cleanup,namespace_preserved:$preserved}' >"$exit_path"
  fi
  [[ $result != 0 || $cleanup_result == 0 ]] || result=1
  exit "$result"
}
