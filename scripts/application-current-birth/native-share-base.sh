#!/bin/sh
# Metered app and session births authored from one verifier-opened Mini image.
# This exercises current height and policy admission; native issuer rotation is
# a separate, currently unavailable operation.
set -eu
umask 077

if [ "$#" -ne 2 ]; then
  echo "usage: $0 SOURCE_MATCHED_HOST NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
HOST=$1
EVIDENCE=$2
MINI=${MINI:-"$REPO/native/resource-client/target/debug/mini"}
STORE_BINARY=${STORE_BINARY:-"$REPO/native/hyperdocument-link-sqlite-store/target/debug/minidregg-link-sqlite-store"}
SIGNATURE_BINARY=${SIGNATURE_BINARY:-"$REPO/native/credential-signature-verifier/target/debug/minidregg-credential-signature-verifier"}
for executable in "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY"; do
  [ -x "$executable" ] || { echo "not executable: $executable" >&2; exit 2; }
done
command -v jq >/dev/null 2>&1 || { echo "jq is required" >&2; exit 2; }
[ ! -e "$EVIDENCE" ] || { echo "evidence directory already exists" >&2; exit 2; }
mkdir -m 700 "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
shasum -a 256 "$0" "$REPO/scripts/grain-birth/native-share-member.sh" \
  "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
  >"$EVIDENCE/input-sha256.txt"

MINI="$MINI" STORE_BINARY="$STORE_BINARY" SIGNATURE_BINARY="$SIGNATURE_BINARY" \
  /bin/sh "$REPO/scripts/grain-birth/native-share-member.sh" "$HOST" "$EVIDENCE/workroom" \
  >"$EVIDENCE/workroom.stdout" 2>"$EVIDENCE/workroom.stderr"
CONFIG="$EVIDENCE/workroom/deployment/pinned-config.json"
SERVICE_PID=
cleanup() {
  if [ -n "$SERVICE_PID" ]; then
    kill "$SERVICE_PID" 2>/dev/null || :
    wait "$SERVICE_PID" 2>/dev/null || :
  fi
}
trap cleanup EXIT HUP INT TERM
start_session() {
  name=$1
  mkdir -m 700 "$EVIDENCE/$name"
  SOCKET="$EVIDENCE/$name/host.sock"
  "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$EVIDENCE/$name/stdout" 2>"$EVIDENCE/$name/stderr" &
  SERVICE_PID=$!
  tick=0
  until [ -S "$SOCKET" ]; do
    kill -0 "$SERVICE_PID" 2>/dev/null || { echo "Mini serve failed" >&2; exit 1; }
    tick=$((tick + 1))
    [ "$tick" -lt 120 ] || { echo "Mini serve timeout" >&2; exit 1; }
    sleep 1
  done
}
stop_session() {
  kill "$SERVICE_PID" 2>/dev/null || :
  wait "$SERVICE_PID" 2>/dev/null || :
  SERVICE_PID=
}
start_session first-session

confirmed() {
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    (.acceptedCount | type == "string" and test("^[1-9][0-9]*$"))' "$1" >/dev/null
}
receipt_projection() {
  jq -S '{transactionId,eventId,acceptedCount,worldRoot}' "$1" >"$2"
}
check_replay() {
  name=$1
  "$MINI" retry --attempt "$EVIDENCE/$name-attempt" --mode lookup --socket "$SOCKET" \
    >"$EVIDENCE/$name-replay.stdout"
  jq -e '.type == "confirmed" and .confirmation == "replayed"' \
    "$EVIDENCE/$name-attempt/retry-0001.json" >/dev/null
  receipt_projection "$EVIDENCE/$name-attempt/outcome.json" \
    "$EVIDENCE/$name-original-receipt.json"
  receipt_projection "$EVIDENCE/$name-attempt/retry-0001.json" \
    "$EVIDENCE/$name-replayed-receipt.json"
  cmp "$EVIDENCE/$name-original-receipt.json" "$EVIDENCE/$name-replayed-receipt.json"
}
query() (
  name=$1 subject=$2 task=$3 capability=$4 key=$5 nonce=$6
  jq -n --arg s "$subject" --arg t "$task" --arg c "$capability" --arg n "$nonce" \
    '{subject:$s,nonce:$n,purpose:{type:"query",kind:"object",target:$t,view:"resource"},
      grants:[{kind:"object",target:$t,capability:$c}]}' >"$EVIDENCE/$name-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-intent.json" --key "$key" --view resource \
    --dir "$EVIDENCE/$name" >"$EVIDENCE/$name.stdout"
)
query_policy() (
  name=$1 subject=$2 task=$3 capability=$4 key=$5 nonce=$6
  jq -n --arg s "$subject" --arg t "$task" --arg c "$capability" --arg n "$nonce" \
    '{subject:$s,nonce:$n,purpose:{type:"query",kind:"object",target:$t,view:"policy"},
      grants:[{kind:"object",target:$t,capability:$c}]}' >"$EVIDENCE/$name-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-intent.json" --key "$key" --view policy \
    --dir "$EVIDENCE/$name" >"$EVIDENCE/$name.stdout"
)
reserve_tool() {
  name=$1 nonce=$2 amount=$3
  query "$name-before" 8 7902 81 "$EVIDENCE/workroom/tool.key" "$((nonce + 1))"
  jq -n --arg n "$nonce" --arg amount "$amount" \
    --slurpfile read "$EVIDENCE/$name-before/view.json" \
    --slurpfile challenge "$EVIDENCE/$name-before/challenge.json" \
    '{grain:{task:"7902",subject:"8",capability:"81",observeCapability:"81",
      schemaVersion:"1",
      expectedTargetRoot:$read[0].cell.root,
      context:{operationId:$n,payload:"current app birth reserve"},
      before:($read[0].cell.grain | {generation,status,remaining,reserved}),
      operation:{type:"reserve",amount:$amount},publications:[]},
      grants:[{kind:"object",target:"7902",capability:"81"}],intentNonce:$n}' \
    >"$EVIDENCE/$name-intent.json"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-intent.json" --intent-kind grain-intent \
    --key "$EVIDENCE/workroom/tool.key" --dir "$EVIDENCE/$name-attempt" \
    >"$EVIDENCE/$name.stdout"
  confirmed "$EVIDENCE/$name-attempt/outcome.json"
}
# The direct grain-birth workroom supplies an already reserved hard parent.
# An integrated workroom may leave that parent paused. Only its initial paused
# generation may attach and reserve the one-unit birth witness.
ensure_app_parent_reserved() {
  query app-parent-prepare-before 7 7901 71 "$EVIDENCE/workroom/controller.key" 42971
  if jq -e '.cell.grain.generation == "1" and .cell.grain.status == "3" and
      .cell.grain.reserved == "1"' \
      "$EVIDENCE/app-parent-prepare-before/view.json" >/dev/null; then
    return
  fi
  jq -e '.cell.grain == {task:"7901",generation:"0",status:"0",remaining:"100",reserved:"0"}' \
    "$EVIDENCE/app-parent-prepare-before/view.json" >/dev/null
  jq -n --slurpfile read "$EVIDENCE/app-parent-prepare-before/view.json" \
    --slurpfile challenge "$EVIDENCE/app-parent-prepare-before/challenge.json" '
    {grain:{task:"7901",subject:"7",capability:"71",observeCapability:"71",
      schemaVersion:"1",
      expectedTargetRoot:$read[0].cell.root,
      context:{operationId:"42970",payload:"current app parent hard attach"},
      before:($read[0].cell.grain | {generation,status,remaining,reserved}),
      operation:{type:"attach",soft:false},publications:[]},
     grants:[{kind:"object",target:"7901",capability:"71"}],intentNonce:"42970"}' \
    >"$EVIDENCE/app-parent-attach-intent.json"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/app-parent-attach-intent.json" --intent-kind grain-intent \
    --key "$EVIDENCE/workroom/controller.key" --dir "$EVIDENCE/app-parent-attach-attempt" \
    >"$EVIDENCE/app-parent-attach.stdout"
  confirmed "$EVIDENCE/app-parent-attach-attempt/outcome.json"
  query app-parent-attached 7 7901 71 "$EVIDENCE/workroom/controller.key" 42972
  jq -e '.cell.grain == {task:"7901",generation:"1",status:"1",remaining:"100",reserved:"0"}' \
    "$EVIDENCE/app-parent-attached/view.json" >/dev/null
  jq -n --slurpfile read "$EVIDENCE/app-parent-attached/view.json" \
    --slurpfile challenge "$EVIDENCE/app-parent-attached/challenge.json" '
    {grain:{task:"7901",subject:"7",capability:"71",observeCapability:"71",
      schemaVersion:"1",
      expectedTargetRoot:$read[0].cell.root,
      context:{operationId:"42980",payload:"current app parent witness reserve"},
      before:($read[0].cell.grain | {generation,status,remaining,reserved}),
      operation:{type:"reserve",amount:"1"},publications:[]},
     grants:[{kind:"object",target:"7901",capability:"71"}],intentNonce:"42980"}' \
    >"$EVIDENCE/app-parent-reserve-intent.json"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/app-parent-reserve-intent.json" --intent-kind grain-intent \
    --key "$EVIDENCE/workroom/controller.key" --dir "$EVIDENCE/app-parent-reserve-attempt" \
    >"$EVIDENCE/app-parent-reserve.stdout"
  confirmed "$EVIDENCE/app-parent-reserve-attempt/outcome.json"
  query app-parent-reserved 8 7901 73 "$EVIDENCE/workroom/tool.key" 42981
  jq -e '.cell.grain == {task:"7901",generation:"1",status:"3",remaining:"99",reserved:"1"}' \
    "$EVIDENCE/app-parent-reserved/view.json" >/dev/null
}
# The direct grain-birth workroom already attaches its tool. The integrated
# workroom leaves it paused after construction. A fresh app birth needs a
# running tool before reserve; only the initial paused generation may attach.
ensure_app_tool_attached() {
  query app-tool-attach-before 8 7902 81 "$EVIDENCE/workroom/tool.key" 42991
  if jq -e '.cell.grain.generation == "1" and .cell.grain.status == "1" and
      .cell.grain.reserved == "0"' \
      "$EVIDENCE/app-tool-attach-before/view.json" >/dev/null; then
    return
  fi
  jq -e '.cell.grain.generation == "0" and .cell.grain.status == "0" and
    .cell.grain.reserved == "0"' \
    "$EVIDENCE/app-tool-attach-before/view.json" >/dev/null
  jq -n --slurpfile read "$EVIDENCE/app-tool-attach-before/view.json" \
    --slurpfile challenge "$EVIDENCE/app-tool-attach-before/challenge.json" '
    {grain:{task:"7902",subject:"8",capability:"81",observeCapability:"81",
      schemaVersion:"1",
      expectedTargetRoot:$read[0].cell.root,
      context:{operationId:"42990",payload:"current app tool hard attach"},
      before:($read[0].cell.grain | {generation,status,remaining,reserved}),
      operation:{type:"attach",soft:false},publications:[]},
     grants:[{kind:"object",target:"7902",capability:"81"}],intentNonce:"42990"}' \
    >"$EVIDENCE/app-tool-attach-intent.json"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/app-tool-attach-intent.json" --intent-kind grain-intent \
    --key "$EVIDENCE/workroom/tool.key" --dir "$EVIDENCE/app-tool-attach-attempt" \
    >"$EVIDENCE/app-tool-attach.stdout"
  confirmed "$EVIDENCE/app-tool-attach-attempt/outcome.json"
  query app-tool-attached 8 7902 81 "$EVIDENCE/workroom/tool.key" 42992
  jq -e --slurpfile before "$EVIDENCE/app-tool-attach-before/view.json" '
    .cell.grain.generation == "1" and .cell.grain.status == "1" and
    .cell.grain.remaining == $before[0].cell.grain.remaining and
    .cell.grain.reserved == "0"' "$EVIDENCE/app-tool-attached/view.json" >/dev/null
}
birth_source() {
  name=$1 nonce=$2 spec_field=$3
  query "$name-tool" 8 7902 81 "$EVIDENCE/workroom/tool.key" "$((nonce + 1))"
  query "$name-parent" 8 7901 73 "$EVIDENCE/workroom/tool.key" "$((nonce + 2))"
  jq -e --slurpfile parent "$EVIDENCE/$name-parent/challenge.json" \
    '.height == $parent[0].height and .worldRoot == $parent[0].worldRoot' \
    "$EVIDENCE/$name-tool/challenge.json" >/dev/null
  jq -e '.cell.grain.status == "3" and .cell.grain.reserved != "0"' \
    "$EVIDENCE/$name-tool/view.json" >/dev/null
  jq -e '.cell.grain.status == "3" and .cell.grain.reserved == "1"' \
    "$EVIDENCE/$name-parent/view.json" >/dev/null
  jq -n --arg nonce "$nonce" --arg spec "$spec_field" \
    --slurpfile genesis "$EVIDENCE/workroom/genesis.json" \
    --slurpfile tool "$EVIDENCE/$name-tool/view.json" \
    --slurpfile parent "$EVIDENCE/$name-parent/view.json" \
    --slurpfile challenge "$EVIDENCE/$name-tool/challenge.json" \
    '{subject:"8",nonce:$nonce,
      grants:[{kind:"object",target:"10",capability:"55"},
        {kind:"account",target:"8",capability:"42"},
        {kind:"object",target:"7902",capability:"81"},
        {kind:"object",target:"7901",capability:"73"}],
      shell:{tariff:{base:"2",perBirth:"1"},
        source:{genesis:$genesis[0],template:{issuer:"5",ownerBudget:"100000",lifetime:"10000"},
          creator:"8",nonce:$nonce,sourceCapabilities:["42"],funding:[],feePayer:"8"},
        tool:{task:"7902",capability:"81",observeCapability:"81",targetRoot:$tool[0].cell.root,
          before:($tool[0].cell.grain | {generation,status,remaining,reserved})},
        parent:{task:"7901",capability:"73",observeCapability:"73",targetRoot:$parent[0].cell.root,
          before:($parent[0].cell.grain | {generation,status,remaining,reserved})}}}
      | {subject,nonce,grants,($spec):.shell}' \
    >"$EVIDENCE/$name-base.json"
}
submit_current() {
  name=$1 command=$2 key=$3
  "$MINI" "$command" --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --source "$EVIDENCE/$name-source.json" --dir "$EVIDENCE/$name-author" \
    >"$EVIDENCE/$name-author.stdout"
  [ -s "$EVIDENCE/$name-author/intent.bin" ]
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-author/intent.bin" --intent-kind binary \
    --key "$key" --dir "$EVIDENCE/$name-attempt" >"$EVIDENCE/$name-submit.stdout"
  confirmed "$EVIDENCE/$name-attempt/outcome.json"
}

ensure_app_parent_reserved
ensure_app_tool_attached
reserve_tool app-reserve 43000 5
birth_source app 43100 applicationGrainBirth
jq '.applicationGrainBirth.applicationBirth =
    (.applicationGrainBirth.source +
      {application:{app:"8401",packageManifest:"8402",snapshotManifest:"8403",owner:"8",
        appOwnerCapability:"141",appControlCapability:"142",
        packageOwnerCapability:"143",packageControlCapability:"144",
        snapshotOwnerCapability:"145",snapshotControlCapability:"146"}}) |
    del(.applicationGrainBirth.source)' "$EVIDENCE/app-base.json" >"$EVIDENCE/app-source.json"
if [ -s "$EVIDENCE/workroom/worker-bare-post/challenge.json" ]; then
  OLD_CHALLENGE="$EVIDENCE/workroom/worker-bare-post/challenge.json"
elif [ -s "$EVIDENCE/workroom/tool-born/challenge.json" ]; then
  # The integrated workroom has no direct-fixture worker-bare-post query.
  OLD_CHALLENGE="$EVIDENCE/workroom/tool-born/challenge.json"
else
  echo "retained pre-birth signed challenge absent" >&2; exit 1
fi
OLD_HEIGHT=$(jq -er '.height' "$OLD_CHALLENGE")
jq -e --arg old "$OLD_HEIGHT" '.height != $old' \
  "$EVIDENCE/app-tool/challenge.json" >/dev/null
jq --arg height "$OLD_HEIGHT" '.applicationGrainBirth.applicationBirth.height=$height' \
  "$EVIDENCE/app-source.json" >"$EVIDENCE/app-stale-source.json"
if "$MINI" current-application-intent --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --source "$EVIDENCE/app-stale-source.json" --dir "$EVIDENCE/app-stale-author" \
    >"$EVIDENCE/app-stale.stdout" 2>"$EVIDENCE/app-stale.stderr"; then
  echo "stale app birth height unexpectedly authored" >&2; exit 1
fi
[ ! -e "$EVIDENCE/app-stale-author/intent.bin" ]
submit_current app current-application-intent "$EVIDENCE/workroom/tool.key"
query app-born 8 8401 141 "$EVIDENCE/workroom/tool.key" 43200
query package-born 8 8402 143 "$EVIDENCE/workroom/tool.key" 43201
query snapshot-born 8 8403 145 "$EVIDENCE/workroom/tool.key" 43202
query_policy app-policy 8 8401 141 "$EVIDENCE/workroom/tool.key" 43203
query_policy package-policy 8 8402 143 "$EVIDENCE/workroom/tool.key" 43204
query_policy snapshot-policy 8 8403 145 "$EVIDENCE/workroom/tool.key" 43205
jq -e --arg target "8401" \
  '([.cell.entries[] | select(.key.type == "object" and .key.resource == $target)] | length) == 4' \
  "$EVIDENCE/app-born/view.json" >/dev/null
jq -e '.type == "resource" and .cell.entries == []' \
  "$EVIDENCE/package-born/view.json" >/dev/null
jq -e '.type == "resource" and .cell.entries == []' \
  "$EVIDENCE/snapshot-born/view.json" >/dev/null
for target in app package snapshot; do
  case "$target" in
    app) id=8401 ;;
    package) id=8402 ;;
    snapshot) id=8403 ;;
  esac
  jq -e --arg id "$id" '.policyId == $id and .version == "0"' \
    "$EVIDENCE/$target-policy/view.json" >/dev/null
done

query app-tool-before-reopen 8 7902 81 "$EVIDENCE/workroom/tool.key" 43206
# The Store's durable image (seed + every log record), read under the Store's own
# anchor identity, as the Host's transport opens it (`Config.anchorIdentity`,
# printed by `describe` as storeAnchorIdentity; never re-derived here). The legacy single-blob `read-to` image no longer
# exists: the Store keeps a durable log, so `read-to` refuses ("published byte
# record is missing").
durable_image() {
  _image_id=$("$HOST" "$CONFIG" describe | jq -er .storeAnchorIdentity)
  "$STORE_BINARY" --anchor-identity "$_image_id" durable-read "$1" 1 1 "$2"
}
durable_image "$EVIDENCE/workroom/store" "$EVIDENCE/app-before-reopen-image.bin"
stop_session
start_session reopened-session
check_replay app
durable_image "$EVIDENCE/workroom/store" "$EVIDENCE/app-after-lookup-image.bin"
cmp "$EVIDENCE/app-before-reopen-image.bin" "$EVIDENCE/app-after-lookup-image.bin"
query app-tool-after-lookup 8 7902 81 "$EVIDENCE/workroom/tool.key" 43207
jq -S '.cell.grain | {generation,status,remaining,reserved}' \
  "$EVIDENCE/app-tool-before-reopen/view.json" >"$EVIDENCE/app-tool-before-reopen-state.json"
jq -S '.cell.grain | {generation,status,remaining,reserved}' \
  "$EVIDENCE/app-tool-after-lookup/view.json" >"$EVIDENCE/app-tool-after-lookup-state.json"
cmp "$EVIDENCE/app-tool-before-reopen-state.json" "$EVIDENCE/app-tool-after-lookup-state.json"
query app-reopened 8 8401 141 "$EVIDENCE/workroom/tool.key" 43300
jq -e --slurpfile born "$EVIDENCE/app-born/view.json" \
  '.cell == $born[0].cell' "$EVIDENCE/app-reopened/view.json" >/dev/null

reserve_tool session-reserve 44000 4
birth_source session 44100 applicationSessionGrainBirth
jq '.applicationSessionGrainBirth.applicationSessionBirth =
    (.applicationSessionGrainBirth.source +
      {session:{app:"8401",session:"8404",descriptor:"8405",participant:"8",kind:"web",
        sessionOwnerCapability:"147",sessionControlCapability:"148",
        descriptorOwnerCapability:"149",descriptorControlCapability:"150"}}) |
    del(.applicationSessionGrainBirth.source)' "$EVIDENCE/session-base.json" \
    >"$EVIDENCE/session-source.json"
submit_current session current-session-intent "$EVIDENCE/workroom/tool.key"
query session-born 8 8404 147 "$EVIDENCE/workroom/tool.key" 44200
query descriptor-born 8 8405 149 "$EVIDENCE/workroom/tool.key" 44201
query_policy session-policy 8 8404 147 "$EVIDENCE/workroom/tool.key" 44204
query_policy descriptor-policy 8 8405 149 "$EVIDENCE/workroom/tool.key" 44205
jq -e --arg target "8404" \
  '([.cell.entries[] | select(.key.type == "object" and .key.resource == $target)] | length) == 4' \
  "$EVIDENCE/session-born/view.json" >/dev/null
jq -e '.type == "resource" and .cell.entries == []' \
  "$EVIDENCE/descriptor-born/view.json" >/dev/null
for target in session descriptor; do
  if [ "$target" = session ]; then id=8404; else id=8405; fi
  jq -e --arg id "$id" '.policyId == $id and .version == "0"' \
    "$EVIDENCE/$target-policy/view.json" >/dev/null
done
query session-tool-before-reopen 8 7902 81 "$EVIDENCE/workroom/tool.key" 44206
durable_image "$EVIDENCE/workroom/store" "$EVIDENCE/session-before-reopen-image.bin"
stop_session
start_session session-reopened
check_replay session
durable_image "$EVIDENCE/workroom/store" "$EVIDENCE/session-after-lookup-image.bin"
cmp "$EVIDENCE/session-before-reopen-image.bin" "$EVIDENCE/session-after-lookup-image.bin"
query session-tool-after-lookup 8 7902 81 "$EVIDENCE/workroom/tool.key" 44207
jq -S '.cell.grain | {generation,status,remaining,reserved}' \
  "$EVIDENCE/session-tool-before-reopen/view.json" \
  >"$EVIDENCE/session-tool-before-reopen-state.json"
jq -S '.cell.grain | {generation,status,remaining,reserved}' \
  "$EVIDENCE/session-tool-after-lookup/view.json" \
  >"$EVIDENCE/session-tool-after-lookup-state.json"
cmp "$EVIDENCE/session-tool-before-reopen-state.json" \
  "$EVIDENCE/session-tool-after-lookup-state.json"
query tool-after 8 7902 81 "$EVIDENCE/workroom/tool.key" 44202
query parent-after 8 7901 73 "$EVIDENCE/workroom/tool.key" 44203
jq -e --slurpfile initial "$EVIDENCE/app-tool-attach-before/view.json" '
  .cell.grain.remaining == ((($initial[0].cell.grain.remaining | tonumber) - 9) | tostring) and
  .cell.grain.reserved == "0"' \
  "$EVIDENCE/tool-after/view.json" >/dev/null
jq -e '.cell.grain.status == "3" and .cell.grain.reserved == "1"' \
  "$EVIDENCE/parent-after/view.json" >/dev/null
shasum -a 256 -c "$EVIDENCE/input-sha256.txt" >"$EVIDENCE/input-recheck.txt"
echo "current metered app/session birth native acceptance PASS"
