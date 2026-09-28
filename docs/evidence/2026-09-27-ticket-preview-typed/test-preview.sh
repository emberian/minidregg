#!/bin/sh
set -eu
umask 077
fixture=/home/hbox/mini-agent-ticket-schema-r1
mini=/home/hbox/mini-ticket-preview-typed-r3.sh
human=/home/hbox/issue-human-ticket-typed-r3.sh
agent=/home/hbox/issue-agent-ticket-typed-r3.sh
config=$fixture/config.json
allocation=$fixture/allocation.json
socket=$fixture/typed-preview-r3.sock

perl -MIO::Socket::UNIX -MSocket \
  -e '$s=IO::Socket::UNIX->new(Type=>SOCK_STREAM,Local=>$ARGV[0],Listen=>1) or die; sleep 60' \
  "$socket" &
pid=$!
trap 'kill "$pid" 2>/dev/null || :' EXIT
while [ ! -S "$socket" ]; do sleep 0.1; done
sha() { sha256sum "$1" | cut -d ' ' -f1; }
mini_sha=$(sha "$mini")

human_host=$fixture/host
"$human" prepare "$mini" "$human_host" "$config" "$socket" \
  "$allocation" alice-web "$fixture/human-scope.json" \
  "$fixture/human-policy.json" "$fixture/typed-human-r3" \
  "$mini_sha" "$(sha "$human_host")"
cmp "$fixture/typed-human-r3/request.bin" \
  "$fixture/typed-human-r3/preview-native/request.bin"
cmp "$fixture/typed-human-r3/preview-plan.bin" \
  "$fixture/typed-human-r3/preview-native/plan.bin"
cmp "$fixture/typed-human-r3/preview-plan.json" \
  "$fixture/typed-human-r3/preview-native/plan-inspected.json"

agent_host=$fixture/host-independent-parent-r1
"$agent" prepare "$mini" "$agent_host" "$config" "$socket" \
  "$allocation" hermes-a "$fixture/independent-parent-scope-r1.json" \
  "$fixture/independent-parent-policy-r1.json" \
  "$fixture/typed-agent-r3" "$mini_sha" "$(sha "$agent_host")"
cmp "$fixture/typed-agent-r3/request.bin" \
  "$fixture/typed-agent-r3/preview-native/request.bin"
cmp "$fixture/typed-agent-r3/preview-plan.bin" \
  "$fixture/typed-agent-r3/preview-native/plan.bin"
cmp "$fixture/typed-agent-r3/preview-plan.json" \
  "$fixture/typed-agent-r3/preview-native/plan-inspected.json"

jq '.planSha256="0000000000000000000000000000000000000000000000000000000000000000"' \
  "$fixture/typed-agent-r3/preview-native/plan-pin.json" \
  >"$fixture/typed-agent-r3/preview-native/plan-pin-changed.json"
mv "$fixture/typed-agent-r3/preview-native/plan-pin-changed.json" \
  "$fixture/typed-agent-r3/preview-native/plan-pin.json"
if "$agent" approve "$fixture/typed-agent-r3" "$fixture/signers.json" \
  "$fixture/typed-agent-r3-approval.json" \
  >"$fixture/typed-agent-r3-changed-pin.log" 2>&1; then exit 4; fi
[ ! -e "$fixture/typed-agent-r3-approval.json" ]

if MOCK_BAD_PLAN_PIN=1 "$human" prepare "$mini" "$human_host" \
  "$config" "$socket" "$allocation" alice-web \
  "$fixture/human-scope.json" "$fixture/human-policy.json" \
  "$fixture/typed-human-bad-pin-r3" "$mini_sha" "$(sha "$human_host")" \
  >"$fixture/typed-human-bad-pin-r3.log" 2>&1; then exit 3; fi
[ ! -e "$fixture/typed-human-bad-pin-r3/stage.json" ]
printf 'typed preview retained exact human and agent request/plan bytes; altered initial and retained pins refused\n'
