#!/bin/bash
# full BASE_BIN OWN_RUST_BIN NEW_RUN_ROOT SIGNED_SPK
# custody BASE_BIN OWN_RUST_BIN NEW_RUN_ROOT: root volume receiving + plant only.
# ROOT SETUP and ROOT CLEANUP use the deployment installer. The acceptance phase
# uses sudo only for the single fixed-verb helper; all long-lived processes are
# uid 1001 user units. No live Store or public node is selected.
set -euo pipefail
umask 077
[[ $# == 4 || $# == 5 ]] || { echo "usage: $0 full|custody BASE_BIN OWN_RUST_BIN NEW_RUN_ROOT [SIGNED_SPK]" >&2; exit 2; }
mode=$1 base=$2 own=$3 run=$4 spk=${5:-}
[[ $mode == full || $mode == custody || $mode == cleanup ]] || exit 2
[[ $(id -u) == 1001 ]] || { echo 'two-world acceptance requires uid 1001' >&2; exit 1; }
[[ $run == /* && $run != *[!a-zA-Z0-9_./-]* ]] || exit 2
if [[ $mode == cleanup ]]; then
  [[ -f $run/root-setup.log && ! -L $run ]] || exit 2
else
  [[ ! -e $run ]] || { echo 'fresh simple absolute run root required' >&2; exit 2; }
  ancestor=$(dirname "$run")
  while :; do
    [[ -d $ancestor && ! -L $ancestor ]] || exit 2
    (( (8#$(stat -c '%a' "$ancestor") & 8#022) == 0 )) || { echo "scratch custody refuses writable ancestor: $ancestor" >&2; exit 2; }
    [[ $ancestor == / ]] && break
    ancestor=$(dirname "$ancestor")
  done
fi
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
installer=$repo/deploy/spk-host/install-user-world
if [[ $mode == full && -z $spk ]]; then spk=$("$here/fetch-test-spk.sh"); fi
if [[ $mode == full ]]; then [[ -f $spk && ! -L $spk ]] || { echo 'two-world acceptance requires the staged signed SPK' >&2; exit 1; }; fi
systemctl --user is-active default.target >/dev/null
[[ $(loginctl show-user 1001 -p Linger --value) == yes ]] || { echo 'operator linger is required' >&2; exit 1; }
if [[ $mode != cleanup ]]; then
mkdir -m 700 -p /run/user/1001/systemd/user "$run/bin" "$run/a/evidence" "$run/b/evidence"
for binary in mini minidregg-host minidregg-link-sqlite-store minidregg-credential-signature-verifier minidregg-client-consent; do
  install -m 755 "$base/$binary" "$run/bin/$binary"
done
for binary in spk-host mini-spk-broker mini-spk-volume-helper; do
  install -m 755 "$own/$binary" "$run/bin/$binary"
done
install -m 755 "$repo/deploy/spk-host/spk-ingest" "$run/bin/spk-ingest"
sha256sum "$run/bin/"* >"$run/binary-sha256.txt"
runid=$(od -An -N8 -tx1 /dev/urandom | tr -d ' \n')
helper=/usr/local/libexec/mini-spk-volume-helper-$runid
else
  helper=$(awk '/^ROOT SETUP store=/ {for(i=1;i<=NF;i++) if($i ~ /^helper=/) {sub(/^helper=/,"",$i);print $i;exit}}' "$run/root-setup.log")
  [[ $helper =~ ^/usr/local/libexec/mini-spk-volume-helper-[0-9a-f]{16}$ ]] || exit 2
fi
stores=() roots=() configured=()
cleanup() {
  local original=$? cleanup_rc=0 store root unit request verb index world
  trap - EXIT INT TERM
  index=0
  for store in "${stores[@]}"; do
    root=/var/lib/mini-spk-worlds/$store
    world=a; [[ $index == 0 ]] || world=b
    if [[ -f $run/$world/store/base/workroom/deployment/pinned-config.json ]]; then
      if ! BIN="$run/bin" GRAINS_ROOT="$root" BROKER_SOCKET="$root/runtime-$store/broker.sock" "$here/grain-journey.sh" stop-services "$run/$world" >>"$run/cleanup-services.log" 2>&1; then cleanup_rc=1; fi
    fi
    # Bound names from this scratch store only; no globally scoped stop.
    : >"$run/residents-$store.log"
    while read -r unit; do
      [[ -n $unit ]] || continue
      if ! journalctl --user --no-pager -u "$unit" >>"$run/residents-$store.log"; then cleanup_rc=1; fi
      if ! systemctl --user stop "$unit"; then cleanup_rc=1; fi
    done < <(systemctl --user list-units --all --plain --no-legend "mini-spk-s$store-a*.service" "mini-spk-supervisor@$store-*.service" "mini-spk-supervisor-s$store@*.service" | awk '{print $1}')
    if systemctl --user is-active "mini-spk-broker@$store.service" >/dev/null; then
      if ! systemctl --user stop "mini-spk-broker@$store.service"; then cleanup_rc=1; fi
    fi
    if ! journalctl --user --no-pager -u "mini-spk-broker@$store.service" >"$run/broker-$store.log"; then cleanup_rc=1; fi
    for request in "$root/broker"/volume-*.json; do
      [[ -f $request ]] || continue
      for verb in unmount destroy; do
        payload=$(jq -c --arg verb "$verb" '.verb=$verb' "$request")
        if ! sudo -n -- "$helper" "$payload" >>"$run/volume-helper.log" 2>&1; then cleanup_rc=1; fi
      done
    done
    if [[ -f /etc/mini-spk-volumes/$store.json ]]; then
      if ! sudo -n -- "$installer" remove "$store" "$helper" >>"$run/root-cleanup.log" 2>&1; then cleanup_rc=1; fi
    fi
    rm -f "/run/user/1001/systemd/user/mini-spk-broker@$store.service"
    while read -r unit; do [[ -z $unit ]] || rm -f "/run/user/1001/systemd/user/$unit"; done < <(find /run/user/1001/systemd/user -maxdepth 1 -type f \( -name "*s$store*" -o -name "mini-spk-supervisor@$store-*.service" \) -printf '%f\n')
    [[ ! -e /etc/sudoers.d/mini-spk-$store && ! -e /etc/mini-spk-volumes/$store.json ]] || cleanup_rc=1
    index=$((index+1))
  done
  systemctl --user daemon-reload
  [[ ! -e $helper ]] || cleanup_rc=1
  printf 'cleanup original=%s removal_assertions=%s\n' "$original" "$cleanup_rc" | tee -a "$run/result.log"
  if [[ $original == 0 && $cleanup_rc != 0 ]]; then exit 1; fi
  exit "$original"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
if [[ $mode == cleanup ]]; then
  while read -r store; do
    [[ $store =~ ^[0-9a-f]{16}$ ]] || exit 2
    stores+=("$store")
    roots+=("/var/lib/mini-spk-worlds/$store")
  done < <(awk '/^ROOT SETUP BEGIN store=/ {sub(/^store=/,"",$4);print $4}' "$run/root-setup.log")
  [[ ${#stores[@]} == 2 ]] || exit 2
  exit 0
fi
# Only scratch identities are generated; do not reuse an existing grain profile.
for world in a b; do
  if [[ $mode == full ]]; then
    BIN="$run/bin" GRAINS_ROOT=/var/lib/mini-spk-worlds/0000000000000000 \
      BROKER_SOCKET=/var/lib/mini-spk-worlds/0000000000000000/runtime-0000000000000000/broker.sock \
      "$here/grain-journey.sh" phase "$run/$world" store | tee "$run/$world/store-phase.log"
    config=$run/$world/store/base/workroom/deployment/pinned-config.json
    "$run/bin/minidregg-host" "$config" profile >"$run/$world/native-profile.json"
    store=$(jq -er '.storeTag | select(test("^[0-9a-f]{16}$"))' "$run/$world/native-profile.json")
  else store=$(od -An -N8 -tx1 /dev/urandom | tr -d ' \n'); fi
  stores+=("$store")
  roots+=("/var/lib/mini-spk-worlds/$store")
done
[[ ${stores[0]} != "${stores[1]}" ]] || { echo 'two-world store identity collision' >&2; exit 1; }
start=$(awk -F: '$1=="ember" && $3>=32 {print $2;exit}' /etc/subuid)
[[ $start =~ ^[0-9]+$ ]] || exit 1
for index in 0 1; do
  store=${stores[$index]} root=${roots[$index]}
  deployment=$(od -An -N32 -tx1 /dev/urandom | tr -d ' \n')
  host=$(sha256sum /etc/machine-id | cut -d ' ' -f1)
  printf 'ROOT SETUP BEGIN store=%s\n' "$store" | tee -a "$run/root-setup.log"
  sudo -n -- "$installer" install "$run/bin/mini-spk-volume-helper" "$helper" "$store" "$deployment" "$host" 1001 "$((start+index*16))" 16 >>"$run/root-setup.log" 2>&1
  registry=/etc/mini-spk-volumes/$store.json
  jq -n --slurpfile registry "$registry" --arg binary "$run/bin/spk-host" --arg sha "$(sha256sum "$run/bin/spk-host" | cut -d ' ' -f1)" --arg ingest "$run/bin/spk-ingest" '
    $registry[0] as $r | {protocol:"mini-spk-broker-config-v2",store:$r.store,grainsRoot:$r.grainsRoot,spkRoot:($r.grainsRoot+"/spk"),brokerSocket:($r.grainsRoot+"/runtime-"+$r.store+"/broker.sock"),operatorUser:"ember",unitPrefix:"mini",spkHost:$binary,spkHostSha256:$sha,ingestHelper:$ingest,volumeHelper:$r.helper,appUids:$r.appUids,residentHomeReadOnlyPaths:[]}' >"$root/broker/config.json"
  chmod 600 "$root/broker/config.json"
  sed "s|%h/.local/libexec/mini-spk-broker|$run/bin/mini-spk-broker|" "$repo/deploy/spk-host/mini-spk-broker@.service" >"/run/user/1001/systemd/user/mini-spk-broker@$store.service"
  systemctl --user daemon-reload
  systemctl --user start "mini-spk-broker@$store.service"
  socket=$root/runtime-$store/broker.sock
  for attempt in $(seq 1 100); do [[ ! -S $socket ]] || break; sleep 0.1; done
  [[ -S $socket && $(stat -c '%u:%a' "$socket") == 1001:600 ]] || { echo 'operator broker socket custody failed' >&2; exit 1; }
  pid=$(systemctl --user show "mini-spk-broker@$store.service" -p MainPID --value)
  [[ $(awk '/^Uid:/ {print $2}' "/proc/$pid/status") == 1001 ]] || { echo 'broker runs as root' >&2; exit 1; }
  jq '.appUids[]' "$registry" | LC_ALL=C sort >"$run/uids-$index.txt"
done
[[ -z $(comm -12 "$run/uids-0.txt" "$run/uids-1.txt") ]] || { echo 'two-world namespace uid collision' >&2; exit 1; }
[[ ${roots[0]}/runtime-${stores[0]}/broker.sock != "${roots[1]}/runtime-${stores[1]}/broker.sock" ]] || exit 1
# Constructor refusal precedes all grain effects. Two ids must give disjoint
# names even when both app/generation coordinates are identical.
for index in 0 1; do
  "$run/bin/spk-host" grain unit-name "${stores[$index]}" 9101 2 >"$run/name-$index.json"
done
[[ $(jq -er .unit "$run/name-0.json") != "$(jq -er .unit "$run/name-1.json")" ]] || { echo 'unit-name-collision: two stores rendered one unit' >&2; exit 1; }
phase() {
  local index=$1; shift
  local world=a
  [[ $index == 0 ]] || world=b
  BIN="$run/bin" SPK="$spk" GRAINS_ROOT="${roots[$index]}" \
    BROKER_SOCKET="${roots[$index]}/runtime-${stores[$index]}/broker.sock" \
    "$here/grain-journey.sh" phase "$run/$world" "$@"
}
if [[ $mode == full ]]; then
  # Both brokers are already up; both Stores/apps stay up during the restart.
  for index in 0 1; do
    phase "$index" services workroom profile birth-a install-a share-a
    world=a; [[ $index == 0 ]] || world=b
    profile=$(jq -er .profilePath "$run/$world/evidence/profile-result.json")
    "$here/prepare-resident-config.sh" "$run/bin/spk-host" "$profile" 9101 >"$run/$world/evidence/prepared-resident.json"
    resident=$(jq -er .residentConfig "$run/$world/evidence/prepared-resident.json")
    "$run/bin/spk-host" resident-validate "$resident" >"$run/$world/evidence/resident-validate.stdout"
    phase "$index" start-a floor-a enroll-a get-a
  done
  for index in 0 1; do
    phase "$index" post-a stop-a
    sudo -n -- "$helper" "$(jq -c '.verb="unmount"' "${roots[$index]}/broker/volume-9101.json")" >>"$run/volume-helper.log" 2>&1
    phase "$index" start-a2 floor-a2 enroll-a2 get-a2 poll-a2
    other=$((1-index))
    phase "$other" get-a2 status-a
    phase "$index" birth-b install-b share-b start-b floor-b enroll-b get-b status-a status-b
  done
  for index in 0 1; do
    world=a; [[ $index == 0 ]] || world=b
    profile=$(jq -er .profilePath "$run/$world/evidence/profile-result.json")
    "$run/bin/spk-host" grain status "$profile" 9101 >"$run/status-$index.json"
    jq -er '.runs[] | select(.state=="running") | .unit' "$run/status-$index.json" >"$run/units-$index.txt"
    while read -r unit; do
      [[ $unit == mini-spk-s${stores[$index]}-a9101-g*.service ]] || { echo 'unit-name-collision: resident unit does not carry its store' >&2; exit 1; }
      cg=$(systemctl --user show "$unit" -p ControlGroup --value)
      while read -r pid; do
        [[ $(awk '/^Uid:/ {print $2}' "/proc/$pid/status") != 0 ]] || { echo 'root process in scratch resident cgroup' >&2; exit 1; }
      done <"/sys/fs/cgroup$cg/cgroup.procs"
    done <"$run/units-$index.txt"
  done
  [[ -z $(comm -12 "$run/units-0.txt" "$run/units-1.txt") ]] || { echo 'unit-name-collision: two worlds share a resident unit' >&2; exit 1; }
  for index in 0 1; do
    registry=/etc/mini-spk-volumes/${stores[$index]}.json
    payload=$(jq -c '{verb:"volumes-status",store:.store,deploymentId:.deploymentId,volumesRoot:(.grainsRoot+"/volumes")}' "$registry")
    sudo -n -- "$helper" "$payload" >"$run/volume-status-$index.json" 2>>"$run/volume-helper.log"
    jq -e --arg store "${stores[$index]}" '.protocol=="mini-spk-volumes-status-v1" and .store==$store and (.volumes|length)==2 and all(.volumes[]; .mounted and .settled and .request.store==$store)' "$run/volume-status-$index.json" >/dev/null
  done
  # Live copy is the original filesystem freeze/copy/thaw transaction.
  sudo -n -- "$helper" "$(jq -c '.verb="freeze"' "${roots[0]}/broker/volume-9101.json")" >>"$run/volume-helper.log" 2>&1
  printf 'PASS two-world uid=1001 install/start/http/stop/restart/second-instance disjoint-units sockets subuids\n' | tee -a "$run/result.log"
else
  # Actual fixed-verb root receiver with no Mini semantics asserted.
  registry=/etc/mini-spk-volumes/${stores[0]}.json
  jq -n --slurpfile r "$registry" '$r[0] as $r | {verb:"create",store:$r.store,deploymentId:$r.deploymentId,grain:"9101",volumePath:($r.grainsRoot+"/vars/"+$r.store+"-9101"),appUid:$r.appUids[0],sizeMib:512,volumeId:("a"*64),importSha256:null}' >"${roots[0]}/broker/volume-9101.json"
  sudo -n -- "$helper" "$(jq -c . "${roots[0]}/broker/volume-9101.json")" >>"$run/volume-helper.log" 2>&1
  sudo -n -- "$helper" "$(jq -c '.verb="unmount"' "${roots[0]}/broker/volume-9101.json")" >>"$run/volume-helper.log" 2>&1
  # Re-create of an exact registered volume must remount, never allocate again.
  sudo -n -- "$helper" "$(jq -c . "${roots[0]}/broker/volume-9101.json")" >>"$run/volume-helper.log" 2>&1
  sudo -n -- "$helper" "$(jq -c '.verb="freeze"' "${roots[0]}/broker/volume-9101.json")" >>"$run/volume-helper.log" 2>&1
  echo 'PASS isolated mounted ext4/freeze/export receiving (SPK lifecycle unqualified)' | tee -a "$run/result.log"
fi
# Both modes retain the cross-world mutation's receiving evidence.
"$here/plant-helper-cross-world-volume.sh" "$helper" "${roots[0]}/broker/volume-9101.json" "/etc/mini-spk-volumes/${stores[1]}.json" "$run/cross-world-plant"
