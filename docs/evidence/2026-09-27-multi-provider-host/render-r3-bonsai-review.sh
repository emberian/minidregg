#!/usr/bin/env bash
# Render keyless A/B controller candidates beside, never inside, the live r3 Store.
# Usage on hbox: bash render-r3-bonsai-review.sh MINI HOST LAUNCHER ROOT_A ROOT_B
set -euo pipefail
umask 077
[[ $# == 5 ]] || { echo 'five absolute artifact paths required' >&2; exit 64; }
mini=$1 host=$2 launcher=$3 root_a=$4 root_b=$5
for artifact in "$mini" "$host" "$launcher" "$root_a" "$root_b"; do
  [[ $artifact == /* && -e $artifact && ! -L $artifact ]] || exit 65
done
[[ -x $mini && -x $host && -x $launcher && -d $root_a && -d $root_b ]] || exit 65
[[ ${launcher##*/} == bwrap && $root_a != "$root_b" ]] || exit 65
require_sha() {
  [[ $(sha256sum "$1" | cut -d' ' -f1) == "$2" ]] || { echo "source image pin differs: $1" >&2; exit 65; }
}
require_sha "$mini" 2f205b791bc4a2ae796af277afd6f574b5e15e592b4237075fc5122202403953
require_sha "$host" 89973efe154b3f53bb279a931a93aed0b0a1d341d759dc776dca635dda01c354
require_sha "$launcher" efda87a5033fc24bb074cc68bfcca8686a448cd4e10175ca8d74b2c6884961a7
require_sha "${launcher%/*}/launch-gate" 2cf1d29ad7fcbce8e2e476ce803bc0c77785f720ceca02ba77e2530b849e7fb6
for root in "$root_a" "$root_b"; do
  require_sha "$root/grain-runtime" 7cb370ec7292004842c4680b77736cee9bda408665085b09f75b61c04036e40c
  require_sha "$root/grain-provider-bridge" 2877ef2a5293ee0b2a7c22d0c0216dab865d3174dd68b312889661cb4f90cfcb
  require_sha "$root/hermes-acp" d9b2b31dcce207f8397a7e1606a6d8586a25e661744b610340d83b2c0c25b7ee
done

r3=/var/lib/minidregg/spk/fixtures/gitweb-v2-20260927-client-session-r3
allocation=$r3/source-stage/agent-allocation.json
pinned=$r3/base/workroom/deployment/pinned-config.json
host_candidate=/tank/dregg-preview/mini-r3-bonsai-review-20260927/host-cb55-candidate.json
out=/tank/dregg-preview/mini-r3-bonsai64k-review-20260927
[[ $(sha256sum "$pinned" | cut -d' ' -f1) == c2c79aa69f66ecc7922f69f620a9dd9ca24cfea25cd94282fcb1a40c2b8296b8 ]] || exit 65
require_sha "$allocation" ce11093ce0e3e0500ece3962d2f4cf600bdf1b9e326255d7abd04741a0abd222
[[ -f $host_candidate && ! -L $host_candidate ]] || exit 65
require_sha "$host_candidate" 0af8e9422f54dbe840d79f449829152d44c92653f4aa33bf8203b1217a021a2f
mkdir -m 700 "$out"
[[ $(stat -c %a "$out") == 700 ]] || exit 65
for suffix in a b; do
  [[ ! -e $out/$suffix ]] || { echo "existing candidate: $out/$suffix" >&2; exit 73; }
done

for route in hermes-a hermes-b; do
  if [[ $route == hermes-a ]]; then suffix=a; root=$root_a; port=18762
  else suffix=b; root=$root_b; port=18763; fi
  member=$out/$suffix
  mkdir -m 700 "$member"
  mkdir -m 700 "$member/state" "$member/cwd" "$member/workspace"
  [[ $(stat -c %a "$member/state") == 700 ]] || exit 65
  output=$member/controller-review.json
  [[ ! -e $output ]] || { echo "existing candidate: $output" >&2; exit 73; }
  jq --arg route "$route" --arg r3 "$r3" --arg member "$member" \
    --arg mini "$mini" --arg host "$host" --arg launcher "$launcher" \
    --arg root "$root" --arg host_config "$host_candidate" \
    --arg host_socket "$out/host.sock" --argjson port "$port" '
    .agents[] | select(.route == $route) | . as $a |
    {mini:$mini,host:$host,hostConfig:$host_config,hostSocket:$host_socket,
     controlSocket:($member+"/state/control.sock"),
     custodyKey:($r3+"/base/workroom/agents/"+$route+"/controller.key"),
     stateDir:($member+"/state"),cwd:($member+"/cwd"),
     task:$a.controller.task,subject:$a.controller.subject,
     capability:$a.plannedCaps.parentOwner,queryCapability:$a.plannedCaps.parentOwner,
     policyControlCapability:$a.plannedCaps.parentControl,
     toolTask:{task:$a.tool.task,subject:$a.tool.subject,
       capability:$a.plannedCaps.toolOwner,queryCapability:$a.plannedCaps.toolOwner,
       custodyKey:($r3+"/base/workroom/agents/"+$route+"/tool.key"),
       parentCapability:$a.plannedCaps.parentToolWitness,
       parentObserveCapability:$a.plannedCaps.parentToolWitness,
       reserve:"2",charge:"1",allowedPublications:[]},
     providerTask:{task:$a.provider.task,subject:$a.provider.subject,
       capability:$a.plannedCaps.providerOwner,queryCapability:$a.plannedCaps.providerOwner,
       custodyKey:($r3+"/base/workroom/agents/"+$route+"/provider.key"),
       parentCapability:$a.plannedCaps.parentProviderWitness,
       parentObserveCapability:$a.plannedCaps.parentProviderWitness,
       reserve:"1",charge:"0",metering:true,
       maxInputTokens:65024,maxOutputTokens:512,maxIterations:2,
       model:"bonsai2-27b-ptq1",
       upstreamUrl:"http://127.0.0.1:18081/v1/chat/completions",
       providerKeyFile:($member+"/state/provider.key"),
       gatewayBind:("127.0.0.1:"+($port|tostring)),
       maxRequestBytes:1048576,maxResponseBytes:8388608,
       timeoutSeconds:180},
     commands:[{name:"hermes-acp",program:$launcher,
       args:["--workspace",($member+"/workspace"),"--runtime-root",$root,
         "--network","none","--","/agent/hermes-acp"],
       systemdScope:true,wallTimeSeconds:600,reserve:"3",charge:"1"}]}
  ' "$allocation" > "$output"
  chmod 600 "$output"
  jq -e '.providerTask.metering == true and .providerTask.charge == "0" and
      .commands[0].args[5] == "none" and .toolTask.allowedPublications == []' "$output" >/dev/null
done
sha256sum "$pinned" "$allocation" "$mini" "$host" "$launcher" \
  "${launcher%/*}/launch-gate" \
  "$root_a/hermes-acp" "$root_a/grain-runtime" "$root_a/grain-provider-bridge" \
  "$root_b/hermes-acp" "$root_b/grain-runtime" "$root_b/grain-provider-bridge" \
  "$host_candidate" "$out/a/controller-review.json" \
  "$out/b/controller-review.json" > "$out/artifact-sha256.txt"
chmod 600 "$out/artifact-sha256.txt"
cat "$out/artifact-sha256.txt"
