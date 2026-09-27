#!/bin/sh
set -eu
if [ "$#" -ne 2 ]; then
  echo "usage: $0 /absolute/allocation-v1.json /absolute/overlay-script" >&2
  exit 2
fi
allocation=$1 overlay=$2
scratch=$(mktemp -d /tmp/grain-agent-overlay-smoke.XXXXXX)
trap 'rm -rf "$scratch"' EXIT
for route in hermes-a hermes-b; do
  case "$route" in hermes-a) label=a ;; hermes-b) label=b ;; esac
  jq -n --slurpfile pins "$allocation" --arg route "$route" '
    ($pins[0].agents[] | select(.route == $route)) as $a |
    {task:$a.controller.task,subject:$a.controller.subject,
      toolTask:{task:$a.tool.task,subject:$a.tool.subject,
        registeredSharedApplications:[{issue:{kind:"grainBackedEvent22"}}],
        allowedApplicationApiRoutes:[{appResource:$pins[0].app,
          sessionResource:$a.session,ticketResource:$a.ticket,
          signedApiPath:"/repo.git/"}]},
      dispatchTask:{task:$a.dispatch.task,subject:$a.dispatch.subject},
      providerTask:{task:$a.provider.task,subject:$a.provider.subject}}
  ' >"$scratch/$label-base.json"
done
"$overlay" "$allocation" "$scratch/a-base.json" "$scratch/b-base.json" \
  2 0 "$scratch/output" >/dev/null
jq -e '.foregroundTool == {reserve:"2",charge:"0"}' \
  "$scratch/output/agent-a.json" "$scratch/output/agent-b.json" >/dev/null
jq '.providerTask.subject = "12"' "$scratch/a-base.json" \
  >"$scratch/wrong-provider.json"
if "$overlay" "$allocation" "$scratch/wrong-provider.json" \
    "$scratch/b-base.json" 2 0 "$scratch/refused" >/dev/null 2>&1; then
  echo "wrong provider subject was accepted" >&2
  exit 1
fi
echo "explicit foreground profile PASS; wrong provider subject REFUSED"
