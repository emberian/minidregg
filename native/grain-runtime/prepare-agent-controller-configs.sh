#!/bin/sh
# Add an explicit model-free parent allowance to two protected, already
# provisioned agent configs. This creates no Store, key, receipt or authority.
set -eu
umask 077

if [ "$#" -ne 6 ]; then
  echo "usage: $0 ALLOCATION.json BASE_A.json BASE_B.json RESERVE CHARGE NEW_DIR" >&2
  exit 2
fi
allocation=$1 base_a=$2 base_b=$3 reserve=$4 charge=$5 output=$6
for path in "$allocation" "$base_a" "$base_b" "$output"; do
  case "$path" in /*) ;; *) echo "paths must be absolute" >&2; exit 2 ;; esac
done
for path in "$allocation" "$base_a" "$base_b"; do
  [ -f "$path" ] && [ ! -L "$path" ] || exit 2
done
[ ! -e "$output" ] && [ ! -L "$output" ] || exit 2
case "$reserve" in ''|0|0*|*[!0-9]*) exit 2 ;; esac
case "$charge" in ''|*[!0-9]*) exit 2 ;; esac
[ "${#reserve}" -le 18 ] && [ "${#charge}" -le 18 ] || exit 2
[ "$charge" -le "$reserve" ] || exit 2
command -v jq >/dev/null
command -v sha256sum >/dev/null
jq -e '.protocol == "mini-spk-integrated-allocation-v1" and
  .status == "reserved-coordinates-only" and .app == "8401" and
  ([.agents[].route] == ["hermes-a","hermes-b"])' "$allocation" >/dev/null
mkdir -m 700 "$output"

one() {
  base=$1 route=$2 destination=$3
  jq -e --slurpfile allocation "$allocation" --arg route "$route" \
    --arg reserve "$reserve" --arg charge "$charge" '
    ($allocation[0].agents[] | select(.route == $route)) as $agent |
    if .foregroundTool == null and
      .task == $agent.controller.task and .subject == $agent.controller.subject and
      .toolTask.task == $agent.tool.task and .toolTask.subject == $agent.tool.subject and
      .dispatchTask.task == $agent.dispatch.task and
      .dispatchTask.subject == $agent.dispatch.subject and
      .providerTask.task == $agent.provider.task and
      .providerTask.subject == $agent.provider.subject and
      .toolTask.allowedApplicationApiRoutes[0].appResource == $allocation[0].app and
      .toolTask.allowedApplicationApiRoutes[0].sessionResource == $agent.session and
      .toolTask.allowedApplicationApiRoutes[0].ticketResource == $agent.ticket and
      .toolTask.allowedApplicationApiRoutes[0].signedApiPath == "/repo.git/" and
      .toolTask.registeredSharedApplications[0].issue.kind == "grainBackedEvent22" and
      ([.task,.toolTask.task,.dispatchTask.task,.providerTask.task] | unique | length) == 4 and
      ([.subject,.toolTask.subject,.dispatchTask.subject,.providerTask.subject] | unique | length) == 4
    then . + {foregroundTool:{reserve:$reserve,charge:$charge}}
    else error("controller config differs from reserved identity or native app profile") end
  ' "$base" >"$destination"
  chmod 600 "$destination"
}
one "$base_a" hermes-a "$output/agent-a.json"
one "$base_b" hermes-b "$output/agent-b.json"
sha256sum "$0" "$allocation" "$base_a" "$base_b" \
  "$output/agent-a.json" "$output/agent-b.json" >"$output/input-and-output-sha256.txt"
echo "$output/agent-a.json"
echo "$output/agent-b.json"
