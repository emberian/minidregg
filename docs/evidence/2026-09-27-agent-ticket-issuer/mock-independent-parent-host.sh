#!/bin/sh
# Schema-only Host stand-in for the issuer-parent/recipient-origin separation.
set -eu
config=$1
shift
[ -f "$config" ] || exit 2
case "$1:$2" in
  author:application-share-issue-grain-request)
    cp "$3" "$4" ;;
  inspect:application-share-issue-grain-request)
    canonical=$(xxd -p -c 1000000 "$3" | tr -d '\n')
    jq --arg canonical "$canonical" \
      '{type:"application-grain-share-issue-request-v1",
        canonicalRequest:$canonical,canonicalSpec:"0123",spec:.spec,
        payer:.payer,funding:.funding,sourceCapabilities:.sourceCapabilities,
        tool:.tool,parent:.parent}' "$3" >"$4" ;;
  application-grain-share-issue-plan:*)
    printf 'mock plan' >"$3" ;;
  inspect:application-share-issue-grain-plan)
    attempt=${4%/*}
    jq --slurpfile request "$attempt/request-inspected.json" '
      {type:"application-grain-share-issue-plan-v1",
       canonicalRequest:$request[0].canonicalRequest,
       request:$request[0],
       finalizedGrainBirth:{
         tool:{before:{reserved:"3"}},
         parent:{task:$request[0].parent.task,
           capability:$request[0].parent.capability,
           observeCapability:$request[0].parent.observeCapability,
           before:{generation:"1",status:"3",remaining:"99",reserved:"1"}}},
       slots:[{role:"app",index:"0",header:"6162",
         signing:{keyId:"10010",keyEpoch:"0"}}]}
      ' "$attempt/request-inspected.json" >"$4"
    if [ "${MOCK_ORIGIN_OVERRIDE:-}" = 1 ]; then
      jq '.request.spec.ticket.participant.origin.generation="2"' "$4" >"$4.tmp"
      mv "$4.tmp" "$4"
    fi ;;
  *) exit 8 ;;
esac
