#!/usr/bin/env bash
# Register the physical grain host for an existing Mini Store. Does not create
# a Store, start another Host, or birth a workroom. The returned broker.json
# names the exact root/helper selected for the Store's native profile.
# broker-world-up.sh BIN CONFIG.json NEW_OUTPUT_DIR
set -euo pipefail
umask 077
[[ $# == 3 ]] || { echo "usage: $0 BIN CONFIG.json NEW_OUTPUT_DIR" >&2; exit 2; }
bin=$1 config=$2 run=$3
fail() { echo "broker-world-up: $*" >&2; exit 2; }
[[ $(uname -s) == Linux ]] || fail 'Linux required'
for path in "$bin" "$config" "$run"; do
  [[ $path == /* && $path != *[!a-zA-Z0-9_./-]* ]] || fail 'simple absolute paths required'
done
[[ -f $config && ! -L $config && ! -e $run && ! -L $run ]] || fail 'regular config and fresh output directory required'
ancestor=$(dirname "$run")
while :; do
  [[ -d $ancestor && ! -L $ancestor ]] || fail 'unsafe output ancestor'
  (( (8#$(stat -c '%a' "$ancestor") & 8#022) == 0 )) || fail 'writable output ancestor'
  [[ $ancestor == / ]] && break
  ancestor=$(dirname "$ancestor")
done
op_uid=$(id -u) op_name=$(id -un)
[[ $op_uid != 0 ]] || fail 'run as the Store operator, not root'
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid}
units=/run/user/$op_uid/systemd/user
systemctl --user is-active default.target >/dev/null
[[ $(loginctl show-user "$op_uid" -p Linger --value) == yes ]] || fail 'operator linger required'
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
installer=$repo/deploy/spk-host/install-user-world
for binary in minidregg-host spk-host mini-spk-broker mini-spk-volume-helper spk-ingest; do
  [[ -x $bin/$binary && ! -L $bin/$binary ]] || fail "missing binary $binary"
done
mkdir -m 700 "$run"
mkdir -p -m 700 "$units"
"$bin/minidregg-host" "$config" profile >"$run/native-profile.json"
store=$(jq -er '.storeTag | select(test("^[0-9a-f]{16}$"))' "$run/native-profile.json")
root=/var/lib/mini-spk-worlds/$store
[[ ! -e /etc/mini-spk-volumes/$store.json ]] || fail 'Store already has a registered grain world; use its existing profile'
runid=$(od -An -N8 -tx1 /dev/urandom | tr -d ' \n')
helper=/usr/local/libexec/mini-spk-volume-helper-$runid
# A recovery locator is written before any root installation. broker.json remains
# a success-only result; this separate record lets world-down finish interrupted setup.
jq -n --arg store "$store" --arg root "$root" --arg helper "$helper" \
  '{protocol:"mini-spk-world-recovery-v1",store:$store,grainsRoot:$root,
    brokerSocket:($root+"/runtime-"+$store+"/broker.sock"),helper:$helper}' >"$run/recovery.json"
# A free 16-ID slice of the operator's subordinate allocation: a lane box carries several standing
# worlds, and the installer refuses a slice another world's registry already names.
read -r start count < <(awk -F: -v user="$op_name" '$1==user && $3>=16 {print $2,$3;exit}' /etc/subuid)
[[ $start =~ ^[0-9]+$ && $count =~ ^[0-9]+$ ]] || { echo "no /etc/subuid range for $op_name" >&2; exit 1; }
end=$((start + count))
while ((start + 16 <= end)); do
  occupied=0
  for registry in /etc/mini-spk-volumes/*.json; do
    [[ -f $registry ]] || continue
    if jq -e --argjson first "$start" --argjson last "$((start + 16))" '.appUids | any(. >= $first and . < $last)' "$registry" >/dev/null 2>&1; then occupied=1; break; fi
  done
  [[ $occupied == 1 ]] || break
  start=$((start + 16))
done
((start + 16 <= end)) || { echo "no unused 16-ID subordinate slice for $op_name" >&2; exit 1; }
bwrap=$(sh "$repo/deploy/grain-host/resolve-bwrap") || exit 1
deployment=$(od -An -N32 -tx1 /dev/urandom | tr -d ' \n')
host=$(sha256sum /etc/machine-id | cut -d ' ' -f1)
printf 'ROOT SETUP BEGIN store=%s\n' "$store" | tee -a "$run/root-setup.log"
sudo -n -- "$installer" install "$bin/mini-spk-volume-helper" "$helper" "$store" "$deployment" "$host" "$op_uid" "$start" 16 >>"$run/root-setup.log" 2>&1
printf 'ROOT SETUP store=%s helper=%s\n' "$store" "$helper" | tee -a "$run/root-setup.log"
registry=/etc/mini-spk-volumes/$store.json
# MINI_IMPORT_PROFILE is the operator's physical intake budget for materialising a package:
# standard-v1 (256 MiB raw, 768 MiB decoded), market-large-v1 (512 MiB, 2 GiB: the market's
# class L apps) or operator-appliance-v1 (the oracle runtime). The wall clock scales with each
# package's size (spk-host import-limits).
import_profile=${MINI_IMPORT_PROFILE:-standard-v1}
case $import_profile in standard-v1|market-large-v1|operator-appliance-v1) ;; *) echo "unknown MINI_IMPORT_PROFILE $import_profile" >&2; exit 2;; esac
# A host whose SPK store sits on a small disk names a root-custodied scratch root in
# /etc/mini-spk-volumes/ingest-scratch (one absolute path, root 0644): install-user-world makes
# <root>/<store> for the operator, and this world's intake spools there (the profile's decoded bound
# is 20 GiB for operator-appliance-v1). Absent: the SPK store itself.
ingest_scratch=
if [[ -e /etc/mini-spk-volumes/ingest-scratch ]]; then
  ingest_scratch=$(</etc/mini-spk-volumes/ingest-scratch)/$store
fi
# Home visibility is an explicit bounded inventory; native broker custody
# validation remains authoritative for every file and socket parent.
if [[ -n ${MINI_RESIDENT_HOME_PATHS:-} ]]; then
  jq -e 'type == "array" and length <= 256 and all(.[]; type == "string")' "$MINI_RESIDENT_HOME_PATHS" >/dev/null
  cp -- "$MINI_RESIDENT_HOME_PATHS" "$run/resident-home-paths.json"
else
  printf '[]\n' >"$run/resident-home-paths.json"
fi
jq -n --slurpfile homePaths "$run/resident-home-paths.json" --slurpfile registry "$registry" --arg binary "$bin/spk-host" --arg sha "$(sha256sum "$bin/spk-host" | cut -d ' ' -f1)" --arg ingest "$bin/spk-ingest" --arg op "$op_name" \
  --arg bwrap "$bwrap" --arg bwrapSha "$(sha256sum "$bwrap" | cut -d ' ' -f1)" --arg importProfile "$import_profile" --arg ingestScratch "$ingest_scratch" '
  $registry[0] as $r | {protocol:"mini-spk-broker-config-v3",store:$r.store,grainsRoot:$r.grainsRoot,spkRoot:($r.grainsRoot+"/spk"),brokerSocket:($r.grainsRoot+"/runtime-"+$r.store+"/broker.sock"),operatorUser:$op,unitPrefix:"mini",spkHost:$binary,spkHostSha256:$sha,bwrap:$bwrap,bwrapSha256:$bwrapSha,ingestHelper:$ingest,volumeHelper:$r.helper,appUids:$r.appUids,residentHomeReadOnlyPaths:$homePaths[0],importProfile:$importProfile} + (if $ingestScratch == "" then {} else {ingestScratch:$ingestScratch} end)' >"$root/broker/config.json"
chmod 600 "$root/broker/config.json"
sed "s|%h/.local/libexec/mini-spk-broker|$bin/mini-spk-broker|" "$repo/deploy/spk-host/mini-spk-broker@.service" >"$units/mini-spk-broker@$store.service"
systemctl --user daemon-reload
systemctl --user start "mini-spk-broker@$store.service"
socket=$root/runtime-$store/broker.sock
# A loaded box starts the broker slowly: wait up to two minutes for its socket.
# The broker binds its socket and then sets its mode: wait for the finished state, not the bind.
for attempt in $(seq 1 1200); do [[ -S $socket && $(stat -c '%u:%a' "$socket" 2>/dev/null) == "$op_uid:600" ]] && break; sleep 0.1; done
[[ -S $socket && $(stat -c '%u:%a' "$socket") == "$op_uid:600" ]] || { echo 'operator broker socket custody failed' >&2; exit 1; }
jq -n --arg store "$store" --arg root "$root" --arg socket "$socket" --arg helper "$helper" \
  --arg unit "mini-spk-broker@$store.service" --arg config "$config" \
  --arg configSha "$(sha256sum "$config" | cut -d ' ' -f1)" \
  '{protocol:"mini-spk-existing-world-broker-v1",store:$store,grainsRoot:$root,brokerSocket:$socket,
    helper:$helper,brokerUnit:$unit,miniConfig:$config,miniConfigSha256:$configSha}' >"$run/broker.json"
printf '%s\n' "$run/broker.json"
