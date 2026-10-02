#!/bin/bash
# usage: hostile.sh MINI RUNROOT STOPFILE COUNTS -- a hostile writer beside the timers. Once J5 has
# enrolled the third subject ($W/third-workspace, used by no later step), the sponsor births one
# resource `hostile-w` OWNED by the third subject (declared field 1, permit-all; the only sponsor
# attempt this script makes), the third workspace imports the owner grant as `hostile`, and then
# the third subject writes field 1 := i (expected i-1) every HOSTILE_S seconds (default 2) after
# the previous write returns. Every installed acceptedCount goes to COUNTS: journey.sh counts it
# as a timer record, never a stranger's.
MINI=$1; R=$2; STOP=$3; C=$4; W=$R/world; SW=$W/sponsor; TW=$W/third-workspace; L=$R/hostile.log; H=$R/hostile
HOSTILE_S=${HOSTILE_S:-2}
done_() { grep -q "^EXIT=" "$STOP" 2>/dev/null; }
count() { jq -r 'select(.type == "confirmed" and .confirmation == "installed") | .acceptedCount // empty' "$1" 2>/dev/null | head -1; }
# The birth below changes the authority root; it waits for HOSTILE_AFTER (a step directory,
# default K4: after J8, so no J-step propose/submit pair is split by it). The writes after it
# move only the world root and height, as a tick does.
AFTER=${HOSTILE_AFTER:-K4}
while [ ! -f "$TW/workspace.json" ] || [ ! -S "$W/public/mini.sock" ] || [ ! -d "$R/steps/$AFTER" ]; do done_ && exit 0; sleep 2; done
mkdir -p -m 700 "$H"
THIRD=$(jq -r .subject "$TW/workspace.json")
printf '%s\n' '{"type":"all","predicates":[]}' >"$H/permit-all.json"
until "$MINI" workspace --action create --dir "$SW" --name hostile-w --storage declared --owner "$THIRD" \
    --predicate "$H/permit-all.json" --fields 1 >"$H/create.out" 2>"$H/create.err"; do
  echo "$(date +%s) create failed: $(tail -1 "$H/create.err")" >>"$L"; done_ && exit 0; sleep 5
done
k=$(count "$SW/attempts/create-hostile-w/outcome.json"); [ -n "$k" ] && echo "$k" >>"$C"
echo "$(date +%s) create installed count=$k" >>"$L"
REF=$SW/refs/hostile-w.json
"$MINI" workspace --action import --dir "$TW" --name hostile --kind object --target "$(jq -r .target "$REF")" \
  --observe-capability "$(jq -r .observeCapability "$REF")" --operation-capability "$(jq -r .operationCapability "$REF")" \
  >>"$L" 2>&1 || { echo "import failed" >>"$L"; exit 1; }
i=0; n=0
while ! done_; do
  i=$((i + 1)); n=$((n + 1)); id=h-$n
  if [ "$i" = 1 ]; then act='"type":"create","key":{"type":"object","field":"1"},"value":"1"'
  else act='"type":"write","key":{"type":"object","field":"1"},"value":"'$i'","expected":"'$((i - 1))'"'; fi
  printf '{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"hostile","payload":{"type":"scalar","actions":[{%s}]}}]}\n' "$act" >"$H/$id.json"
  k=
  if "$MINI" workspace --action propose --dir "$TW" --request "$H/$id.json" --proposal-id "$id" >"$H/$id.p.out" 2>"$H/$id.p.err" \
     && "$MINI" workspace --action submit --dir "$TW" --intent "$TW/proposals/$id/intent.json" --attempt "$TW/attempts/$id" >"$H/$id.s.out" 2>"$H/$id.s.err"; then
    k=$(count "$TW/attempts/$id/outcome.json"); [ -n "$k" ] && echo "$k" >>"$C"
    echo "$(date +%s) write $i installed count=$k" >>"$L"
  else
    k=$(count "$TW/attempts/$id/outcome.json" 2>/dev/null); [ -n "$k" ] && echo "$k" >>"$C"
    echo "$(date +%s) write $i FAILED $(cat "$H/$id.s.err" "$H/$id.p.err" 2>/dev/null | tail -2 | tr '\n' ' ' | cut -c1-300)" >>"$L"
    [ -n "$k" ] || i=$((i - 1))
  fi
  sleep "$HOSTILE_S"
done
