#!/bin/sh
# Extend the reviewed current-image app/session birth source with four distinct
# participant sessions. Produces source only; the qualifier gates its execution.
set -eu
umask 077

if [ "$#" -ne 3 ]; then
  echo "usage: $0 CURRENT_APP_SOURCE ALLOCATION_JSON NEW_OUTPUT_SOURCE" >&2
  exit 2
fi
SOURCE=$1 ALLOCATION=$2 OUTPUT=$3
[ -f "$SOURCE" ] && [ -f "$ALLOCATION" ] || exit 2
[ ! -e "$OUTPUT" ] && [ ! -L "$OUTPUT" ] || exit 2
jq -e '
  [.humans[].route] == ["alice-web","bob-web","alice-api"] and
  [.agents[].route] == ["hermes-a","hermes-b"] and
  [.humans[] | .session,.descriptor] == ["8404","8405","8406","8407",
    "8410","8411"] and
  [.agents[] | .session,.descriptor] == ["8420","8421","8422","8423"]
' "$ALLOCATION" >/dev/null || {
  echo "participant session allocation differs" >&2; exit 2;
}
STAGE=$OUTPUT.stage
[ ! -e "$STAGE" ] && [ ! -L "$STAGE" ] || exit 2
mkdir -m 700 "$STAGE"
trap 'rm -rf -- "$STAGE"' EXIT HUP INT TERM

cat >"$STAGE/additional-sessions" <<'EOF'
# The app and Alice Web session are already source-born. Each additional
# session uses a fresh current-image tool reserve, birth, and owner readback.
for route in bob-web alice-api hermes-a hermes-b; do
  spec=$(jq -c --arg route "$route" '
    (.humans[],.agents[]) | select(.route == $route)' \
    "$SPK_AGENT_ALLOCATION")
  [ -n "$spec" ] && [ "$spec" != null ] || exit 2
  session=$(printf '%s\n' "$spec" | jq -er .session)
  descriptor=$(printf '%s\n' "$spec" | jq -er .descriptor)
  kind=$(printf '%s\n' "$spec" | jq -er .sessionKind)
  owner=$(if [ "$route" = bob-web ] || [ "$route" = alice-api ]; then
    printf '%s\n' "$spec" | jq -er .subject
  else
    printf '%s\n' "$spec" | jq -er .controller.subject
  fi)
  case "$route" in
    bob-web) nonce=45000; owner_key="$EVIDENCE/workroom/member.key" ;;
    alice-api) nonce=46000; owner_key="$EVIDENCE/workroom/tool.key" ;;
    hermes-a) nonce=47000
      owner_key="$EVIDENCE/workroom/agents/hermes-a/controller.key" ;;
    hermes-b) nonce=48000
      owner_key="$EVIDENCE/workroom/agents/hermes-b/controller.key" ;;
  esac
  reserve_tool "$route-session-reserve" "$nonce" 4
  birth_source "$route-session" "$((nonce + 100))" applicationSessionGrainBirth
  jq -n --slurpfile base "$EVIDENCE/$route-session-base.json" \
    --argjson spec "$spec" '
    $base[0] | .applicationSessionGrainBirth.applicationSessionBirth =
      (.applicationSessionGrainBirth.source +
        {session:{app:"8401",session:$spec.session,
          descriptor:$spec.descriptor,participant:
            (if $spec.subject then $spec.subject else $spec.controller.subject end),
          kind:$spec.sessionKind,
          sessionOwnerCapability:$spec.plannedCaps.sessionOwner,
          sessionControlCapability:$spec.plannedCaps.sessionControl,
          descriptorOwnerCapability:$spec.plannedCaps.descriptorOwner,
          descriptorControlCapability:$spec.plannedCaps.descriptorControl}}) |
    del(.applicationSessionGrainBirth.source)' \
    >"$EVIDENCE/$route-session-source.json"
  submit_current "$route-session" current-session-intent \
    "$EVIDENCE/workroom/tool.key"
  session_cap=$(printf '%s\n' "$spec" | jq -er .plannedCaps.sessionOwner)
  descriptor_cap=$(printf '%s\n' "$spec" | jq -er .plannedCaps.descriptorOwner)
  query "$route-session-born" "$owner" "$session" "$session_cap" \
    "$owner_key" "$((nonce + 200))"
  query "$route-descriptor-born" "$owner" "$descriptor" \
    "$descriptor_cap" "$owner_key" "$((nonce + 201))"
  jq -e --arg t "$session" '
    ([.page.entries[] | select(.key.type == "object" and
      .key.resource == $t)] | length) == 4' \
    "$EVIDENCE/$route-session-born/view.json" >/dev/null
  jq -e --arg d "$descriptor" '
    .page.document == $d and .page.entries == []' \
    "$EVIDENCE/$route-descriptor-born/view.json" >/dev/null
  jq -cn --arg route "$route" --arg owner "$owner" \
    --arg session "$session" --arg descriptor "$descriptor" \
    --arg kind "$kind" \
    --arg sessionViewSha "$(sha256sum \
      "$EVIDENCE/$route-session-born/view.json" | cut -d ' ' -f 1)" \
    --arg descriptorViewSha "$(sha256sum \
      "$EVIDENCE/$route-descriptor-born/view.json" | cut -d ' ' -f 1)" \
    --slurpfile receipt "$EVIDENCE/$route-session-attempt/outcome.json" '
    {route:$route,participant:$owner,kind:$kind,session:$session,
     descriptor:$descriptor,sessionViewSha256:$sessionViewSha,
     descriptorViewSha256:$descriptorViewSha,
     birthReceipt:($receipt[0] |
       {acceptedCount,transactionId,eventId,imageBoundary})}' \
    >>"$EVIDENCE/additional-sessions.jsonl"
done
query additional-session-tool-after 8 7902 81 \
  "$EVIDENCE/workroom/tool.key" 49000
jq -e '.page.grain.status == "3" and .page.grain.reserved == "0" and
  (.page.grain.remaining | tonumber > 0)' \
  "$EVIDENCE/additional-session-tool-after/view.json" >/dev/null
jq -s '{type:"mini-spk-additional-session-births-v1",sessions:.}' \
  "$EVIDENCE/additional-sessions.jsonl" \
  >"$EVIDENCE/additional-sessions.json"
EOF

awk -v extension="$STAGE/additional-sessions" '
  /^shasum -a 256 -c "\$EVIDENCE\/input-sha256.txt"/ {
    while ((getline line < extension) > 0) print line
    close(extension); inserted++
  }
  { print }
  END { if (inserted != 1) exit 2 }
' "$SOURCE" >"$OUTPUT"
chmod 700 "$OUTPUT"
sh -n "$OUTPUT"
