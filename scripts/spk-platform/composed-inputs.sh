#!/bin/bash
# composed-inputs.sh WORLD-IDENTITY.json CANDIDATE_DIR OUT_DIR: the three inputs the composed
# scenario's apps, connector and residents phases read (native/resource-client/composed-scenario.py),
# derived from a jworld-scratch world (dregg-infra edge/mini/journey/jworld-scratch.sh) through the
# real installers, as the Store operator (the uid that runs the world's units; on dregg-build the
# lanes user). Nothing here invents an identity: every value comes from the world's inventory, the
# candidate's manifest, the node's pinned config and genesis, and the operator's own custody.
#
#   OUT_DIR/platform-inputs.json   mini platform inputs (what the constructor's platform-provision.py writes)
#   OUT_DIR/app-selection.json     mini-spk-same-store-selection-v1 (owner, members, package, ids)
#   OUT_DIR/documents-binding.json mini-protected-same-store-v1 (owner, member, reader, reviewer)
#   OUT_DIR/resident-binding.json  mini-same-world-resident-binding-v1
#   OUT_DIR/composed-args.txt      the exact `composed-scenario.py spec ...` arguments to add
#   OUT_DIR/broker-setup/recovery.json  the teardown locator: run `world-down.sh OUT_DIR` before the world goes down
#
# The SPK platform on the scenario's own Store: ROOT SETUP (deploy/spk-host/install-user-world under
# sudo -n), the operator broker unit, `same-store-profile.py` (grain init-store against the existing
# config). It REFUSES BY NAME, before any effect, a world whose pinned config lacks the operator
# policy a grain host needs (`lifecycleManagement`, `completionCustodianKey`, `grainBirthTariff`): those
# are pinned at genesis by the workroom provisioner's WORKROOM_OPERATOR_POLICY and are absent from the
# demo's genesis-params.json today; the refusal names the fields. Reads MINI_TEST_SPK (the pinned
# sntfy) or fetches it with fetch-test-spk.sh.
#
# The connector and residents phases need what a world may lack (an https route front, the EtherCalc
# package, root-held resident custody). Each missing piece is named on stderr and in OUT_DIR/result.log
# as `CONNECTOR UNAVAILABLE: <reason>` / `RESIDENTS UNAVAILABLE: <reason>` (owner area in the reason),
# the selection then carries no "connector", and the script still writes every input and exits 0, so
# the phases that can run do; the scenario's own preflight fails the connector phase by name.
set -euo pipefail
umask 077
[[ $# == 3 ]] || { echo "usage: $0 WORLD-IDENTITY.json CANDIDATE_DIR OUT_DIR" >&2; exit 2; }
world=$1 cand=$2 out=$3
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
refuse() { echo "composed-inputs: $*" >&2; exit 1; }
[[ -f $world && -d $cand && ! -e $out ]] || refuse "need an inventory file, a candidate directory and a fresh OUT_DIR"
jq -e '.type == "mini-world-identity-v1" and (.members | type == "object" and length >= 4)' "$world" >/dev/null \
  || refuse "WORLD-IDENTITY.json is not mini-world-identity-v1 with at least four members (owner, member, reader, reviewer / two authors and a witness)"
mkdir -m 700 "$out"
manifest=$cand/manifest.json
[[ -f $manifest ]] || refuse "candidate has no manifest.json"
# The scratch world's node: the sponsor workspace names the Store, config and sockets.
sponsor_ws=$(jq -r '.members | to_entries[] | select(.value.entry == "sponsor") | .value.workspace' "$world" | head -1)
[[ -n $sponsor_ws && -f $sponsor_ws/workspace.json ]] || refuse "the inventory names no sponsor workspace"
config=$(jq -r .config "$sponsor_ws/workspace.json")
socket=$(jq -r .socket "$sponsor_ws/workspace.json")
host=$(jq -r .host "$sponsor_ws/workspace.json")
node=$(dirname "$(dirname "$config")")
[[ -f $config && -S $socket && -x $host ]] || refuse "sponsor workspace does not pin a config, a live public socket and a Host"
private_socket=$(jq -r '.operator // empty' "$node/ingress.json" 2>/dev/null || true)
[[ -n $private_socket ]] || private_socket=$(dirname "$(dirname "$socket")")/operator/mini.sock
# A grain install talks to the Host over the private operator socket (mini serve-operator), never the public
# one; a world served by a single public `mini serve` cannot install, so say so here, not as spk-host's bare ENOENT.
[[ -S $private_socket ]] || refuse "no live private operator socket at $private_socket: the world serves only its public socket; bring it up with serve-operator + serve-public-proxy (edge store-entry.sh, public-ingress.sh)"
genesis=$node/genesis.json
[[ -f $genesis ]] || refuse "no genesis.json beside the node's config ($node)"
# ── the operator policy a grain host needs, pinned at genesis ────────────────
missing=()
for field in lifecycleManagement completionCustodianKey grainBirthTariff; do
  jq -e --arg f "$field" 'has($f)' "$config" >/dev/null || missing+=("$field")
done
if [[ ${#missing[@]} -gt 0 ]]; then
  refuse "operatorPolicyRequired: the world's pinned config lacks ${missing[*]}; a grain host needs them pinned at genesis (scripts/workroom/provision.sh WORKROOM_OPERATOR_POLICY: lifecycleManagement {managementSubject, managementKeyId} with a management key pair the operator holds, completionCustodianKey = the completion custodian's public key, grainBirthTariff {base, perBirth}); the demo's genesis-params.json does not carry them and deploy/candidate/params.sh does not pass them: a genesis change for L9/infra and L1, not a derivation"
fi
management_subject=$(jq -r .lifecycleManagement.managementSubject "$config")
management_key=$(jq -r .lifecycleManagement.managementKeyId "$config")
# The management custody: the operator's key for the pinned management subject, beside the node.
for candidate_key in "$node/keys/management.key" "$node/tool.key" "$node/keys/tool.key"; do
  # A world may name the management key as an alias (management.key -> sponsor.key); the attach
  # protocol takes custody only of a regular file, so the alias resolves to the file it names.
  [[ -f $candidate_key ]] && mgmt_seed=$(readlink -e "$candidate_key") && break
done
[[ -n ${mgmt_seed:-} ]] || refuse "managementCustodyRequired: no management seed beside the node for subject $management_subject (keys/management.key)"
mgmt_pub=${mgmt_seed%.key}.pub
[[ -f $mgmt_pub ]] || refuse "no public half $mgmt_pub"
completion_seed=$node/keys/completion.seed
completion_pub=$node/keys/completion.pub
[[ -f $completion_seed && -f $completion_pub ]] || refuse "completionCustodyRequired: $completion_seed / $completion_pub (the key whose public half the config pins as completionCustodianKey)"
[[ $(jq -r .completionCustodianKey "$config") == "$(od -An -tx1 -v "$completion_pub" | tr -d ' \n')" ]] || refuse "the completion seed beside the node is not the one the config pins"
# ── the candidate's manifest, with the roles the same-store adapters read ───────
# The world runs the copy of the candidate its install placed beside the Store (the sponsor's Host
# names it); the adapters compare member workspaces against the manifest's paths, so the manifest is
# that installed copy's, provided every role's bytes are the CANDIDATE_DIR manifest's.
installed=$(dirname "$(dirname "$host")")/manifest.json
if [[ -f $installed && $(readlink -f "$installed") != $(readlink -f "$manifest") ]]; then
  jq -e --slurpfile c "$manifest" '.sha256 == $c[0].sha256' "$installed" >/dev/null \
    || refuse "the world's installed candidate ($installed) is not CANDIDATE_DIR's (role digests differ)"
  manifest=$installed
fi
for role in host mini store verifier spkHost; do
  jq -e --arg r "$role" 'has($r) and (.sha256 | has($r))' "$manifest" >/dev/null || refuse "candidate manifest lacks role $role"
done
bwrap=$(sh "$repo/deploy/grain-host/resolve-bwrap") || refuse "no usable bwrap"
jq --arg bwrap "$bwrap" --arg sha "$(sha256sum "$bwrap" | cut -d ' ' -f1)" '. + {bwrap:$bwrap} | .sha256 += {bwrap:$sha}' "$manifest" >"$out/manifest.json"
# ── the SPK platform on this Store: root setup, broker, profile ─────────────────
op_uid=$(id -u) op_name=$(id -un)
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$op_uid}
units=/run/user/$op_uid/systemd/user
[[ $(loginctl show-user "$op_uid" -p Linger --value) == yes ]] || refuse "operator linger is required"
store=$("$host" "$config" profile | jq -er '.storeTag | select(test("^[0-9a-f]{16}$"))')
grains=/var/lib/mini-spk-worlds/$store
[[ ! -e $grains ]] || refuse "a grain world for store $store already exists at $grains"
mkdir -m 700 -p "$units" "$out/bin" "$out/evidence"
for binary in mini-spk-broker mini-spk-volume-helper; do install -m 755 "$cand/bin/$binary" "$out/bin/$binary"; done
# The runtime the broker runs is the manifest's spkHost, the one the grain profile pins
# (same-store-profile.py), at its path and digest; a private copy would be a second spelling.
spk_host=$(jq -er .spkHost "$out/manifest.json") spk_host_sha=$(jq -er .sha256.spkHost "$out/manifest.json")
[[ $(sha256sum "$spk_host" | cut -d ' ' -f1) == "$spk_host_sha" ]] || refuse "the manifest's spkHost $spk_host differs from its digest"
install -m 755 "$repo/deploy/spk-host/spk-ingest" "$out/bin/spk-ingest"
runid=$(od -An -N8 -tx1 /dev/urandom | tr -d ' \n')
helper=/usr/local/libexec/mini-spk-volume-helper-$runid
# A user-namespaced container (dregg-infra's composed machine, Stage B) keeps its volumes behind a host-side custodian:
# CUSTODIAN_SOCKET (or the root-owned one-line file /etc/mini-composed-custodian) names its socket, the grains' app uids lie
# inside the container's own 0..65535 range, and the custodian's host directory is bound over the world's `vars`.
custodian=${CUSTODIAN_SOCKET:-$(cat /etc/mini-composed-custodian 2>/dev/null || true)}
start=$(awk -F: -v user="$op_name" '$1==user && $3>=32 {print $2;exit}' /etc/subuid)
[[ $start =~ ^[0-9]+$ ]] || refuse "no /etc/subuid range for $op_name"
deployment=$(jq -r '.deployment // .domain' "$genesis" | sha256sum | cut -d ' ' -f1)
hostid=$(sha256sum /etc/machine-id | cut -d ' ' -f1)
printf 'ROOT SETUP BEGIN store=%s\n' "$store" | tee -a "$out/root-setup.log"
sudo -n -- "$repo/deploy/spk-host/install-user-world" install "$out/bin/mini-spk-volume-helper" "$helper" "$store" "$deployment" "$hostid" "$op_uid" "$start" 16 ${custodian:+"$custodian"} >>"$out/root-setup.log" 2>&1
if [[ -n $custodian ]]; then
  [[ -d /var/lib/composed-vars ]] || refuse "custodian mode: /var/lib/composed-vars (the custodian's vars directory) is not bound in"
  sudo -n -- mount --bind /var/lib/composed-vars "$grains/vars" || refuse "custodian mode: cannot bind the custodian's vars over $grains/vars"
fi
printf 'ROOT SETUP store=%s helper=%s\n' "$store" "$helper" | tee -a "$out/root-setup.log"
# The teardown locator world-down.sh reads: `world-down.sh OUT_DIR` stops this Store's grain units and
# broker, destroys its volumes through the helper and removes the root registry, sudoers rule, helper
# and /var/lib/mini-spk-worlds/STORE (install-user-world remove). Whoever takes the world down runs it
# first; without it every composed run left its grain world behind (123 GB on dregg-build, 2026-10-28).
mkdir -m 700 "$out/broker-setup"
jq -n --arg store "$store" --arg grains "$grains" --arg helper "$helper" \
  '{protocol:"mini-spk-world-recovery-v1",store:$store,grainsRoot:$grains,brokerSocket:($grains+"/runtime-"+$store+"/broker.sock"),helper:$helper}' \
  >"$out/broker-setup/recovery.json"
registry=/etc/mini-spk-volumes/$store.json
jq -n --slurpfile registry "$registry" --arg binary "$spk_host" --arg sha "$spk_host_sha" --arg ingest "$out/bin/spk-ingest" --arg op "$op_name" \
  --arg bwrap "$bwrap" --arg bwrapSha "$(sha256sum "$bwrap" | cut -d ' ' -f1)" '
  $registry[0] as $r | {protocol:"mini-spk-broker-config-v3",store:$r.store,grainsRoot:$r.grainsRoot,spkRoot:($r.grainsRoot+"/spk"),brokerSocket:($r.grainsRoot+"/runtime-"+$r.store+"/broker.sock"),operatorUser:$op,unitPrefix:"mini",spkHost:$binary,spkHostSha256:$sha,bwrap:$bwrap,bwrapSha256:$bwrapSha,ingestHelper:$ingest,volumeHelper:$r.helper,appUids:$r.appUids,residentHomeReadOnlyPaths:[]}' >"$grains/broker/config.json"
chmod 600 "$grains/broker/config.json"
sed "s|%h/.local/libexec/mini-spk-broker|$out/bin/mini-spk-broker|" "$repo/deploy/spk-host/mini-spk-broker@.service" >"$units/mini-spk-broker@$store.service"
systemctl --user daemon-reload
systemctl --user start "mini-spk-broker@$store.service"
broker=$grains/runtime-$store/broker.sock
for attempt in $(seq 1 100); do [[ ! -S $broker ]] || break; sleep 0.1; done
[[ -S $broker ]] || refuse "operator broker socket did not appear"
# The grain-host profile over the EXISTING config (no genesis, no services).
jq -n --arg manifest "$out/manifest.json" --arg commit "$(jq -r .sourceCommit "$manifest")" --arg config "$config" --arg sha "$(sha256sum "$config" | cut -d ' ' -f1)" \
  --arg private "$private_socket" --arg grains "$grains" --arg broker "$broker" --arg semantics "$(jq -r .expectedSemantics "$genesis")" \
  --arg cseed "$completion_seed" --arg cpub "$completion_pub" --arg bwrap "$bwrap" --arg root "$out/evidence/profile" \
  --arg ms "$management_subject" --arg mk "$management_key" --arg mseed "$mgmt_seed" --arg mpub "$mgmt_pub" '
  {protocol:"mini-spk-same-store-profile-input-v1",manifest:$manifest,expectedSourceCommit:$commit,miniConfig:$config,miniConfigSha256:$sha,
   privateSocket:$private,grainsRoot:$grains,brokerSocket:$broker,semantics:$semantics,completionSeed:$cseed,completionPublicKey:$cpub,bwrap:$bwrap,root:$root,
   management:{subject:$ms,keyId:$mk,keyEpoch:"2",seedPath:$mseed,publicKeyPath:$mpub}}' >"$out/profile-input.json"
python3 -I "$here/same-store-profile.py" "$out/profile-input.json" >"$out/profile.stdout"
# ── platform-inputs.json: the constructor's shape, from this world ──────────────
inventory=$(jq '[.members | to_entries[] | {key: .value.subject, value: {subject: .value.subject, workspace: .value.workspace, home: .value.home}}] | from_entries' "$world")
authority='{}'
# The factory, as the sponsor holds it (genesis gave the sponsor its reference), and the metered parent
# and tool tasks mini apps bootstrap registered: every capability is the one the sponsor's reference names.
[[ $(jq -r .target "$sponsor_ws/refs/factory.json" 2>/dev/null) == "$(jq -r .factoryId "$genesis")" ]] \
  || refuse "the sponsor workspace holds no reference to genesis's factory $(jq -r .factoryId "$genesis") (refs/factory.json)"
for role in factory parent tool; do
  ref=$sponsor_ws/refs/$role.json
  [[ -f $ref ]] || refuse "meteredTasksRequired: no $ref; run \`mini apps bootstrap --dir $sponsor_ws\` first (deploy/market/INSTALL.md §4 step 0)"
  key=task; [[ $role != factory ]] || key=target
  authority=$(jq --arg role "$role" --arg key "$key" --slurpfile r "$ref" '.[$role] = {($key): $r[0].target, ownerCapability: $r[0].observeCapability, managementCapability: $r[0].operationCapability}' <<<"$authority")
done
# The factory capability a birth cites is the signer's own: the creator is the MANAGEMENT subject, and genesis enrolled
# each subject with its own factory capability (factoryObserveCapabilityId). The sponsor's refs/factory.json names the
# sponsor's, which in a distinct-management world (sponsor owns, tool manages) is not the creator's: the birth then
# fails "no-grant ... (phase prepare)". Only managementCapability changes: the owner's births (the resident's) keep
# the owner's own ownerCapability.
sponsor_subject=$(jq -r .subject "$sponsor_ws/workspace.json")
if [[ $management_subject != "$sponsor_subject" ]]; then
  mgmt_factory=$(jq -r --arg ms "$management_subject" '[.enrollments[] | select((.key.subject | tostring) == $ms) | .factoryObserveCapabilityId][0] // empty' "$genesis")
  [[ -n $mgmt_factory ]] || refuse "managementFactoryCapabilityRequired: genesis enrolls management subject $management_subject without a factory capability"
  authority=$(jq --arg c "$mgmt_factory" '.factory.managementCapability = $c' <<<"$authority")
fi
# The owner custody: the world's operator owner when its inventory names one apart from management
# (jworld-scratch JWORLD_MANAGEMENT=distinct: sponsor 7 owns, tool 8 manages); else the one operator
# principal is both.
owner=$(jq -c --arg ms "$management_subject" --arg mk "$management_key" --arg mseed "$mgmt_seed" --arg mpub "$mgmt_pub" \
  '(.operatorCustody.owner // null) as $o
   | if $o != null and ($o.subject | tostring) != $ms
     then {subject: ($o.subject | tostring), keyId: ($o.keyId | tostring), keyEpoch: "2", seed: $o.seed, publicKey: $o.publicKey}
     else {subject: $ms, keyId: $mk, keyEpoch: "2", seed: $mseed, publicKey: $mpub} end' "$world")
for f in seed publicKey; do [[ -f $(jq -r ".$f" <<<"$owner") ]] || refuse "the world's operator owner custody names no $f file"; done
jq -n --arg config "$config" --arg genesis "$genesis" --arg manifest "$out/manifest.json" --arg public "$socket" --arg private "$private_socket" \
  --arg sponsor "$sponsor_ws" --argjson inventory "$inventory" --argjson authority "$authority" --argjson owner "$owner" \
  --arg cseed "$completion_seed" --arg cpub "$completion_pub" --arg ms "$management_subject" --arg mk "$management_key" --arg mseed "$mgmt_seed" --arg mpub "$mgmt_pub" \
  --arg domain "$(jq -r .domain "$genesis")" --arg msha "$(sha256sum "$out/manifest.json" | cut -d ' ' -f1)" --arg csha "$(sha256sum "$config" | cut -d ' ' -f1)" '
  {identity:{domain:($domain|tonumber),manifestSha256:$msha,configSha256:$csha},config:$config,genesis:$genesis,manifest:$manifest,
   publicSocket:$public,privateSocket:$private,operatorWorkspace:$sponsor,memberInventory:$inventory,
   custody:{completionSeed:$cseed,completionPublic:$cpub,
     owner:$owner,
     management:{subject:$ms,keyId:$mk,keyEpoch:"2",seed:$mseed,publicKey:$mpub}},
   authority:$authority}' >"$out/platform-inputs.json"
# ── the metered workroom: parent reserved, tool attached (workroom-ready.sh) ──────
bash "$here/workroom-ready.sh" "$world" "$out/evidence/workroom" || refuse "the metered workroom is not ready"
# The rooms phase creates "<op>-room" over the first N inventory members (composed-scenario.py generate;
# the gate passes N 5 and op "jd3"); it churns the last of them. The app owner owns that room
# (`--room-owner`, below): the resident's founder must control it (`chat adopt`), and the owner's own
# `<op>-room/notes` reference is the document the connector exports into and the resident reads.
op=${COMPOSED_OP:-jd3} n=${COMPOSED_N:-5}
# ── the participants, in inventory order (generate's population order) ───────────
names=$(jq -r '.members | keys_unsorted[]' "$world")
owner=$(sed -n 2p <<<"$names"); member=$(sed -n 3p <<<"$names"); reader=$(sed -n 4p <<<"$names"); reviewer=$(sed -n 1p <<<"$names")
churned=$(sed -n "${n}p" <<<"$names")
[[ -n $churned ]] || refuse "the inventory has fewer than COMPOSED_N=$n members"
subject_of() { jq -r --arg n "$1" '.members[$n].subject' "$world"; }
custody_owner=$(jq -r .custody.owner.subject "$out/platform-inputs.json")
# Each unavailable phase input is named (stderr and result.log) and the phase's input is left out or
# left to its consumer's own refusal; every other input is still written, so the phases that can run do.
unavailable() { local phase=$1; shift; printf '%s UNAVAILABLE: %s\n' "$phase" "$*" | tee -a "$out/result.log" >&2; }
# ── the connector: an independent participant, the EtherCalc package, an https route front ───
connector_reasons=()
# Independent of the app's owner, its session members, the operator custody (owner/management) and the
# member the churn phase kicks from the room.
connector_name=
while IFS= read -r name; do
  case $name in "$owner"|"$member"|"$churned") continue ;; esac
  s=$(subject_of "$name")
  [[ $s != "$management_subject" && $s != "$custody_owner" ]] || continue
  connector_name=$name; break
done <<<"$names"
[[ -n $connector_name ]] || connector_reasons+=("connectorParticipantRequired: no inventory member is independent of the app owner $owner, session member $member, the operator custody ($management_subject) and the churned member $churned; a world with at least $((n > 4 ? n : 4)) hosted members is needed (jworld-scratch MEMBERS)")
# The app is the qualified EtherCalc: its csv export is what the connector phase captures, so the apps
# and connector phases share one app (deputy's ruling, 2026-10-28). MINI_TEST_SPK overrides the path.
spk=${MINI_TEST_SPK:-$(TEST_SPK=ethercalc "$here/fetch-test-spk.sh")}
spk_sha=$(sha256sum "$spk" | cut -d ' ' -f1)
# The connector's capture is EtherCalc's `_/SHEET/csv` export under its signed read-only role 1
# (app-document.md; native/resource-client/src/app_document.rs). The qualified EtherCalc package is
# docs/evidence/2026-09-27-spk-app-selection's (SHA-256 93bd2c29..., 11,983,992 B).
ethercalc_sha=93bd2c296692368252ea7b5610a7930db60e5b283340a60b6be8a812c7e309ee
# The size class the 2026-10-01 SPK survey measured: EtherCalc M, the others S.
size_class=S; [[ $spk_sha != "$ethercalc_sha" ]] || size_class=M
[[ $spk_sha == "$ethercalc_sha" ]] || connector_reasons+=("connectorPackageRequired: the app is $(basename "$spk") ($spk_sha), the connector captures EtherCalc's _/SHEET/csv export and needs the qualified EtherCalc SPK ($ethercalc_sha, market package 9b3b76152e7d8db9f54dba7455ea9239) as the app (MINI_TEST_SPK); the apps and connector phases share one app: harness (composed-inputs package choice, with the apps-phase owner)")
# The capture fetches https://HOST/_/SHEET/csv with verified TLS through ordinary DNS (no --resolve), so
# the world must front its grain routes over https and declare it: WORLD-IDENTITY.json
# "routeFront": {"domain": D, "port": P|null, "ca": "/abs/ca.pem"|null}; the connector route is served at
# connector.D[:P]. A scratch world (plain processes, no root) serves no route front today.
front=$(jq -c '.routeFront // empty' "$world")
connector_host= connector_ca=null
if [[ -z $front ]]; then
  connector_reasons+=("routeFrontRequired: the world serves no https front for its grain routes (WORLD-IDENTITY.json has no routeFront {domain, port, ca}); jworld-scratch.sh brings up only the private Host, the public relay and sshd: an https grain-route front (spk-browser-proxy with a test CA, its names resolvable on the box) is edge/infra's")
elif ! jq -e '(.domain | type == "string" and test("^[a-z0-9]([a-z0-9.-]{0,200}[a-z0-9])?$"))
      and (.port == null or (.port | type == "number" and . >= 1 and . <= 65535 and floor == .))
      and (.ca == null or (.ca | type == "string" and startswith("/")))' <<<"$front" >/dev/null; then
  connector_reasons+=("routeFrontMalformed: WORLD-IDENTITY.json routeFront is not {domain: lowercase DNS name, port: 1..65535|null, ca: absolute path|null}: $front")
else
  connector_host=connector.$(jq -r '.domain + (if .port == null then "" else ":" + (.port | tostring) end)' <<<"$front")
  connector_ca=$(jq -c .ca <<<"$front")
  [[ $connector_ca == null || -f $(jq -r . <<<"$connector_ca") ]] || connector_reasons+=("routeFrontCaAbsent: routeFront names CA $connector_ca, which is not a file")
fi
connector=null
if [[ ${#connector_reasons[@]} -eq 0 ]]; then
  connector=$(jq -nc --arg subject "$connector_name" --arg host "$connector_host" --argjson ca "$connector_ca" '{subject: $subject, host: $host, ca: $ca}')
else
  for reason in "${connector_reasons[@]}"; do unavailable CONNECTOR "$reason"; done
fi
# ── the selection: owner, members, package, unused ids, and the connector when the world has one ───
jq -n -f "$here/composed-selection.jq" --arg evidence "$out/evidence" --arg grains "$grains" --arg broker "$broker" --arg spk "$spk" --arg sha "$spk_sha" --arg sizeClass "$size_class" \
  --arg owner "$owner" --arg member "$member" --arg op "$op" --argjson connector "$connector" >"$out/app-selection.json"
python3 -I -c 'import importlib.util,json,sys; s=importlib.util.spec_from_file_location("i",sys.argv[1]); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); m.selection_shape(json.load(open(sys.argv[2])))' \
  "$here/same-store-inputs.py" "$out/app-selection.json" || refuse "the written selection does not satisfy same-store-inputs.py selection_shape"
# ── the documents binding: four distinct members, their own workspaces ───────────
jq -n --arg manifest "$out/manifest.json" --arg msha "$(sha256sum "$out/manifest.json" | cut -d ' ' -f1)" --arg config "$config" --arg socket "$socket" \
  --arg store "$node" --slurpfile w "$world" --arg owner "$owner" --arg member "$member" --arg reader "$reader" --arg reviewer "$reviewer" '
  $w[0].members as $m | {protocol:"mini-protected-same-store-v1",manifestPath:$manifest,manifestSha256:$msha,configPath:$config,socketPath:$socket,storePath:$store,
   owner:{workspace:$m[$owner].workspace,home:$m[$owner].home},member:{workspace:$m[$member].workspace,home:$m[$member].home},
   reader:{workspace:$m[$reader].workspace,home:$m[$reader].home},reviewer:{workspace:$m[$reviewer].workspace,home:$m[$reviewer].home}}' >"$out/documents-binding.json"
# ── the resident binding: authors owner + member, the reader as provider witness ─────────────
# The resident's frame root is the one whose var/lib/mini/store/node is this node (it requires
# BASE/var/lib/mini/store/node/deployment/pinned-config.json to be the config).
resident_reasons=()
base=${node%/var/lib/mini/store/node}
[[ $base != "$node" ]] || resident_reasons+=("residentsCanonicalNodeRequired: the node $node is not BASE/var/lib/mini/store/node")
task=8802
# The operator-owned private controllers/TASK directory the resident requires (the frame's root
# pre-provisions it; a scratch world's frame belongs to the operator).
controller_dir=$base/var/lib/mini/controllers/$task
if [[ ! -e $controller_dir ]]; then
  mkdir -p -m 700 "$controller_dir"
elif [[ ! -d $controller_dir || -L $controller_dir || $(stat -c %u "$controller_dir") != "$op_uid" || -e $controller_dir/receiving ]]; then
  resident_reasons+=("residentsControllerDirectoryTaken: $controller_dir exists and is not a fresh private directory of the operator")
fi
[[ $custody_owner != "$management_subject" ]] || resident_reasons+=("residentsDistinctManagementRequired: the world's genesis enrolls one operator principal ($management_subject), so platform-inputs custody names it as both owner and lifecycle management; the resident needs an owner and a separate management (tool) principal, each enrolled with its own account and key beside the node (the constructor's 7/controller.key and 8/tool.key): genesis params, L9/infra (jworld-scratch, deploy/candidate/params.sh)")
broker_client=$base/etc/mini/keys-client.json
[[ -f $broker_client && $(stat -c %u "$broker_client") == 0 && $(( 8#$(stat -c %a "$broker_client") & 8#022 )) == 0 ]] \
  || resident_reasons+=("residentsKeyBrokerRequired: $broker_client is not a root-owned key broker client config (the resident's credential custody); a rootless scratch world has none: edge/infra")
launch_gate=$(jq -r .launchGate "$out/manifest.json")
[[ -x $(dirname "$launch_gate")/bwrap ]] || resident_reasons+=("residentsWorkerLauncherRequired: no executable bwrap beside the manifest's launch-gate ($(dirname "$launch_gate")); the resident's worker launcher is installed there by the frame: candidate packaging / edge/infra")
# The two root acts are performed by the resident adapter (same-world-resident.py root_handoffs) only
# beside a real root frame: COMPOSED_ROOT_HANDOFFS=sudo and a working `sudo -n` (a container whose root
# is the world's root). Elsewhere they are unavailable.
if [[ ${COMPOSED_ROOT_HANDOFFS:-} != sudo ]] || ! sudo -n true 2>/dev/null; then
  resident_reasons+=("residentsRootHandoffsRequired: the typed resident waits (exit 75) for two root acts mid-run, the provider custody copy (controller-entry provider-custody-copy v2: BASE/etc/mini/providers.json and receiving/provider-copy-ready.json) and the controller registration receipt ($out/resident-registration-receipt.json, controller-entry.py register); the composed scenario has no step that performs them: harness (composed-scenario residents phase) with edge/infra (controller-entry under sudo -n)")
fi
[[ $connector != null ]] || resident_reasons+=("residentsConnectorRequired: the resident consumes the connector's saved export, and the connector is unavailable (above)")
for reason in "${resident_reasons[@]}"; do unavailable RESIDENTS "$reason"; done
document=$(jq -r '.connector.document // empty' "$out/app-selection.json")
[[ -n $document ]] || document=$op-notes
owner_workspace=$(jq -r --arg o "$owner" '.members[$o].workspace' "$world")
jq -n -f "$here/composed-resident.jq" --arg inputs "$out/platform-inputs.json" --arg base "$base" --arg a0 "$owner" --arg a1 "$member" --arg witness "$reader" \
  --arg ownerWorkspace "$owner_workspace" --arg document "$document" \
  --arg registration "$out/resident-registration-receipt.json" --arg op "$op" \
  --arg acp "$repo/testing/journeys/shared-resident-fixture-acp" --arg acpsha "$(sha256sum "$repo/testing/journeys/shared-resident-fixture-acp" | cut -d ' ' -f1)" \
  --arg prov "$repo/testing/journeys/shared-resident-fixture-provider.py" --arg provsha "$(sha256sum "$repo/testing/journeys/shared-resident-fixture-provider.py" | cut -d ' ' -f1)" \
  >"$out/resident-binding.json"
printf -- '--app-world-inputs %s %s --documents-binding %s --residents-binding %s --room-owner %s\n' "$out/platform-inputs.json" "$out/app-selection.json" "$out/documents-binding.json" "$out/resident-binding.json" "$owner" >"$out/composed-args.txt"
printf 'COMPOSED INPUTS store=%s grains=%s broker=%s connector=%s\n' "$store" "$grains" "$broker" "$([[ $connector == null ]] && echo unavailable || echo "$connector_name@$connector_host")" | tee -a "$out/result.log"
cat "$out/composed-args.txt"
