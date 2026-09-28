#!/bin/sh
set -eu
umask 077
fixture=/home/hbox/mini-agent-ticket-schema-r1
script=/home/hbox/issue-agent-ticket-independent.sh
host=$fixture/host-independent-parent-r1
mini=$fixture/mini
config=$fixture/config.json
socket=$fixture/independent-parent-r1.sock
scope=$fixture/independent-parent-scope-r1.json
policy=$fixture/independent-parent-policy-r1.json
positive=$fixture/independent-parent-positive-r1
negative=$fixture/independent-parent-negative-r1
allocation=$fixture/allocation.json

jq '.originGeneration="0"' "$fixture/scope3.json" >"$scope"
jq '.parent={task:"7901",capability:"73",observeCapability:"73"}' \
  "$fixture/policy4.json" >"$policy"
perl -MIO::Socket::UNIX -MSocket \
  -e '$s=IO::Socket::UNIX->new(Type=>SOCK_STREAM,Local=>$ARGV[0],Listen=>1) or die; sleep 60' \
  "$socket" &
pid=$!
trap 'kill "$pid" 2>/dev/null || :' EXIT
while [ ! -S "$socket" ]; do sleep 0.1; done
mini_sha=$(sha256sum "$mini" | cut -d ' ' -f1)
host_sha=$(sha256sum "$host" | cut -d ' ' -f1)
"$script" prepare "$mini" "$host" "$config" "$socket" "$allocation" \
  hermes-a "$scope" "$policy" "$positive" "$mini_sha" "$host_sha"
jq -e '
  .request.spec.ticket.participant.origin ==
    {type:"agent",task:"7920",generation:"0"} and
  .request.parent ==
    {task:"7901",capability:"73",observeCapability:"73"} and
  .finalizedGrainBirth.parent.task == "7901" and
  .finalizedGrainBirth.parent.before.generation == "1"
  ' "$positive/preview-plan.json" >/dev/null
if MOCK_ORIGIN_OVERRIDE=1 "$script" prepare "$mini" "$host" "$config" \
  "$socket" "$allocation" hermes-a "$scope" "$policy" "$negative" \
  "$mini_sha" "$host_sha" >"$fixture/independent-parent-negative-r1.log" 2>&1; then
  exit 3
fi
[ ! -e "$negative/stage.json" ]
printf 'issuer parent7901 generation1 and recipient origin7920 generation0 remain distinct; altered plan origin refused\n'
