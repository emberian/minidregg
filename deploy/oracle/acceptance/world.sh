#!/usr/bin/env bash
# Cross-file globals are intentional; sudo output remains operator-owned.
# shellcheck disable=SC2024,SC2034,SC2154,SC2174
# Sourced by the Oracle journey. This is a transport/fixture harness only;
# Mini's Host and broker remain the authority and physical-custody receivers.
# Every root effect uses the existing fixed deployment installer/helper.

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
    --out "$output" --deadline 1200 "${args[@]}" >"$output.stdout" 2>"$output.stderr"
}

world_controller_prepare() {
  local home request_id
  timeout 120 sudo -n -- "$installer" controller-create "$store" "$helper" >"$run/agent-lifetime/controller-create.json"
  controller_created=1
  cp "$GRAINS_ROOT/controller/namespace.json" "$run/agent-lifetime/controller-namespace.json"
  home=$(jq -er .controllerHome "$run/agent-lifetime/controller-create.json")
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" prepare-controller "$run" "$repo" "$home" \
    >"$run/agent-lifetime/prepare-controller.stdout" 2>"$run/agent-lifetime/prepare-controller.stderr"
  timeout 120 sudo -n -- "$installer" controller-stage "$store" "$helper" \
    "$run/agent-lifetime/controller-stage" "$BIN" \
    "$run/world/sock/operator/host.sock" "$run/world/sock/participant/host.sock" \
    >"$run/agent-lifetime/controller-stage-receipt.json"
  controller_staged=1
  timeout 240 sudo -n -- "$installer" controller-start "$store" "$helper" >"$run/agent-lifetime/controller-bootstrap-start.json"
  request_id=$("$BIN/grain-runtime" tool-id)
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
  timeout 120 sudo -n -- "$installer" controller-stop "$store" "$helper" >"$run/agent-lifetime/controller-stop-$1.json"
}

world_controller_activate() {
  local start_result=$1 label=$2 activation bundle
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" activate "$run" "$repo" "$start_result" \
    >"$run/agent-lifetime/activate-$label.stdout" 2>"$run/agent-lifetime/activate-$label.stderr"
  activation=$(cat "$run/agent-lifetime/activate-$label.stdout")
  bundle=$(jq -er .bundle "$activation")
  world_controller_stop "before-$label"
  timeout 120 sudo -n -- "$installer" controller-config "$store" "$helper" "$bundle" \
    >"$run/agent-lifetime/controller-config-$label.json"
  cp "$bundle/controller.json" "$run/agent-lifetime/controller-active-$label.json"
  timeout 240 sudo -n -- "$installer" controller-start "$store" "$helper" >"$run/agent-lifetime/controller-start-$label.json"
  export ORACLE_CONTROLLER_INSTALLER=$installer ORACLE_CONTROLLER_STORE=$store ORACLE_CONTROLLER_HELPER=$helper
  export QUALIFIED_LIFETIME_HOST_BINARY=$BIN/minidregg-host
  QUALIFIED_LIFETIME_HOST_SHA256=$(sha256sum "$BIN/minidregg-host" | cut -d ' ' -f1)
  QUALIFIED_RUNTIME_SHA256=$(sha256sum "$BIN/grain-runtime" | cut -d ' ' -f1)
  export QUALIFIED_LIFETIME_HOST_SHA256 QUALIFIED_RUNTIME_SHA256
}

world_controller_probe() {
  local label=$1 directory=$2
  timeout 1800 sh "$repo/scripts/oracle-agent-lifetime-journey.sh" \
    "$BIN/grain-runtime" "$run/agent-lifetime/controller-active-$label.json" oracle-app \
    "$repo/deploy/oracle/acceptance/agent-cases.json" "$run/agent-lifetime/$directory" \
    >"$run/agent-lifetime/$directory.stdout" 2>"$run/agent-lifetime/$directory.stderr"
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

world_cleanup() {
  local result=${1:-$?} cleanup_result=0 unit request verb preserve_namespace=false
  trap - EXIT INT TERM
  if [[ ${configured:-0} == 1 ]]; then
    if [[ ${controller_created:-0} == 1 ]]; then
      world_controller_stop cleanup >>"$run/cleanup.log" 2>&1 || cleanup_result=1
      if [[ ${controller_staged:-0} == 1 ]]; then
        timeout 120 sudo -n -- "$installer" controller-export "$store" "$helper" \
          >"$run/agent-lifetime/controller-final-export.json" 2>>"$run/cleanup.log" || cleanup_result=1
      fi
      if [[ $result == 0 && $cleanup_result == 0 ]]; then
        timeout 120 sudo -n -- "$installer" controller-remove "$store" "$helper" \
          >"$run/agent-lifetime/controller-remove.json" 2>>"$run/cleanup.log" || cleanup_result=1
      fi
      [[ $cleanup_result == 0 ]] || preserve_namespace=true
    fi
    "$journey" stop-services "$run/world" >>"$run/cleanup.log" 2>&1 || cleanup_result=1
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
    [[ $result == 0 ]] || preserve_namespace=true
    for request in "$GRAINS_ROOT/broker"/volume-*.json; do
      [[ -f $request ]] || continue
      verbs=unmount
      [[ $preserve_namespace == true ]] || verbs='unmount destroy'
      for verb in $verbs; do
        sudo -n -- "$helper" "$(jq -c --arg verb "$verb" '.verb=$verb' "$request")" >>"$run/cleanup.log" 2>&1 || cleanup_result=1
      done
    done
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
  if [[ -d $run ]]; then
    jq -n --argjson execution "$result" --argjson cleanup "$cleanup_result" --argjson preserved "$preserve_namespace" '{execution_exit:$execution,cleanup_exit:$cleanup,namespace_preserved:$preserved}' >"$run/exit.json"
  fi
  [[ $result != 0 || $cleanup_result == 0 ]] || result=1
  exit "$result"
}
