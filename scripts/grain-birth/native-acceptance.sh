#!/bin/sh
# Fresh, source-owned Mini acceptance for a worker creating a content resource
# under a reserved tool grain and a same-generation parent witness.
set -eu
umask 077

if [ "$#" -ne 2 ]; then
  echo "usage: $0 COMPOSITE_HOST NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
HOST=$1
EVIDENCE=$2
MINI=${MINI:-"$REPO/native/resource-client/target/debug/mini"}
STORE_BINARY=${STORE_BINARY:-"$REPO/native/hyperdocument-link-sqlite-store/target/debug/minidregg-link-sqlite-store"}
SIGNATURE_BINARY=${SIGNATURE_BINARY:-"$REPO/native/credential-signature-verifier/target/debug/minidregg-credential-signature-verifier"}
SOURCE="$REPO/scripts/workroom/provision.sh"
SOURCE_SHA=9abee2b9f84cd0ab3b4dc228684bceba7b8134f41609b6ab857698dfbba76509
test "$(sha256sum "$SOURCE" | cut -d ' ' -f 1)" = "$SOURCE_SHA" || {
  echo "workroom source changed; review overlay before use" >&2; exit 2;
}
test ! -e "$EVIDENCE" || { echo "evidence directory exists" >&2; exit 2; }
STAGE=$(mktemp -d)
SERVICE_PID=
cleanup() {
  if [ -n "$SERVICE_PID" ]; then kill "$SERVICE_PID" 2>/dev/null || :; wait "$SERVICE_PID" 2>/dev/null || :; fi
  rm -rf "$STAGE"
}
trap cleanup EXIT HUP INT TERM

# This private exact-source overlay changes only the operator-pinned new
# permission tariff and installed factory law. Owner 7 keeps bare birth;
# worker 8 is permitted only by the grain-backed factory mode slot.
# shellcheck disable=SC2016 # Match the provisioner's literal shell variable.
sed \
  -e 's|"signatureBinary":"$SIGNATURE_BINARY"}|"signatureBinary":"$SIGNATURE_BINARY","grainBirthTariff":{"base":2,"perBirth":1}}|' \
  -e 's|"birth":{"genesis":|"birth":{"grainBirthTariff":{"base":"2","perBirth":"1"},"genesis":|' \
  -e 's|"factoryPredicate":{"type":"all","predicates":\[\]}|"factoryPredicate":{"type":"any","predicates":[{"type":"eq","slot":"request/subject","value":"7"},{"type":"all","predicates":[{"type":"eq","slot":"request/subject","value":"8"},{"type":"any","predicates":[{"type":"eq","slot":"request/verb","value":"1"},{"type":"eq","slot":"birth/mode/grain-backed","value":"1"}]}]}]}|' \
  "$SOURCE" > "$STAGE/provision.sh"
test "$(rg -c 'grainBirthTariff' "$STAGE/provision.sh")" = 6
test "$(rg -c 'birth/mode/grain-backed' "$STAGE/provision.sh")" = 1
chmod 700 "$STAGE/provision.sh"
sha256sum "$STAGE/provision.sh" > "$STAGE/provision.sha256"
WORKROOM_PARENT_TASK=7901 WORKROOM_TOOL_TASK=7902 \
  MINI="$MINI" STORE_BINARY="$STORE_BINARY" SIGNATURE_BINARY="$SIGNATURE_BINARY" \
  "$STAGE/provision.sh" "$HOST" "$EVIDENCE"
cp "$STAGE/provision.sha256" "$EVIDENCE/overlay.sha256"
cp "$STAGE/provision.sh" "$EVIDENCE/overlay-provision.sh"
jq -e '.grainBirthTariff == {base:2,perBirth:1}' "$EVIDENCE/operator.json" >/dev/null
jq -e '.factoryPredicate == {type:"any",predicates:[
    {type:"eq",slot:"request/subject",value:"7"},
    {type:"all",predicates:[
      {type:"eq",slot:"request/subject",value:"8"},
      {type:"any",predicates:[
        {type:"eq",slot:"request/verb",value:"1"},
        {type:"eq",slot:"birth/mode/grain-backed",value:"1"}]}]}]}' \
  "$EVIDENCE/genesis.json" >/dev/null
jq -e '.birth.grainBirthTariff == {base:"2",perBirth:"1"} and
    ([.birth.resources[].target] | index("8301") | not)' \
  "$EVIDENCE/birth-intent.json" >/dev/null

CONFIG="$EVIDENCE/deployment/pinned-config.json"
mkdir -m 700 "$EVIDENCE/composite-session"
SOCKET="$EVIDENCE/composite-session/host.sock"
"$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$EVIDENCE/composite-session/stdout" 2>"$EVIDENCE/composite-session/stderr" &
SERVICE_PID=$!
tick=0
until [ -S "$SOCKET" ]; do
  kill -0 "$SERVICE_PID" 2>/dev/null || { echo "Mini serve failed" >&2; exit 1; }
  tick=$((tick + 1)); [ "$tick" -lt 120 ] || { echo "Mini serve timeout" >&2; exit 1; }
  sleep 1
done

confirmed() {
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    (.acceptedCount | type == "string" and test("^[1-9][0-9]*$"))' "$1" >/dev/null
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
grain_action() {
  name=$1 subject=$2 task=$3 capability=$4 key=$5 nonce=$6 operation=$7
  query "$name-before" "$subject" "$task" "$capability" "$key" "$((nonce + 1))"
  jq -n --arg task "$task" --arg subject "$subject" --arg cap "$capability" \
    --arg nonce "$nonce" --argjson operation "$operation" \
    --slurpfile read "$EVIDENCE/$name-before/view.json" \
    --slurpfile challenge "$EVIDENCE/$name-before/challenge.json" \
    '{grain:{task:$task,subject:$subject,capability:$cap,observeCapability:$cap,
      schemaVersion:"1",
      expectedTargetRoot:$read[0].cell.root,
      context:{operationId:$nonce,payload:"fresh grain-backed birth acceptance"},
      before:{generation:$read[0].cell.grain.generation,status:$read[0].cell.grain.status,
        remaining:$read[0].cell.grain.remaining,reserved:$read[0].cell.grain.reserved},
      operation:$operation,publications:[]},
      grants:[{kind:"object",target:$task,capability:$cap}],intentNonce:$nonce}' \
    >"$EVIDENCE/$name-intent.json"
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$name-intent.json" --intent-kind grain-intent \
    --key "$key" --dir "$EVIDENCE/$name-attempt" >"$EVIDENCE/$name.stdout"
  confirmed "$EVIDENCE/$name-attempt/outcome.json"
}

grain_action parent-attach 7 7901 71 "$EVIDENCE/controller.key" 40000 \
  '{"type":"attach","soft":false}'
grain_action parent-reserve 7 7901 71 "$EVIDENCE/controller.key" 40010 \
  '{"type":"reserve","amount":"1"}'
grain_action tool-attach 8 7902 81 "$EVIDENCE/tool.key" 40020 \
  '{"type":"attach","soft":false}'
grain_action tool-reserve 8 7902 81 "$EVIDENCE/tool.key" 40030 \
  '{"type":"reserve","amount":"4"}'

query tool-ready 8 7902 81 "$EVIDENCE/tool.key" 40040
query parent-ready 8 7901 73 "$EVIDENCE/tool.key" 40041
jq -e '.cell.grain.status == "3" and .cell.grain.reserved == "4"' \
  "$EVIDENCE/tool-ready/view.json" >/dev/null
jq -e '.cell.grain.status == "3" and .cell.grain.reserved == "1"' \
  "$EVIDENCE/parent-ready/view.json" >/dev/null
jq -e --slurpfile parent "$EVIDENCE/parent-ready/challenge.json" \
  '.height == $parent[0].height and .worldRoot == $parent[0].worldRoot' \
  "$EVIDENCE/tool-ready/challenge.json" >/dev/null

# New object 8301 is absent from genesis and from the earlier provisioner.
# Its owner/control grants are allocated by the birth source, not by Rust.
jq -n --slurpfile genesis "$EVIDENCE/genesis.json" \
  --slurpfile tool "$EVIDENCE/tool-ready/view.json" \
  --slurpfile parent "$EVIDENCE/parent-ready/view.json" \
  --slurpfile challenge "$EVIDENCE/tool-ready/challenge.json" \
  '{subject:"8",nonce:"41000",
    grainBirth:{tariff:{base:"2",perBirth:"1"},
      birth:{genesis:$genesis[0],template:{issuer:"5",ownerBudget:"100000",lifetime:"10000"},
        height:$challenge[0].height,creator:"8",nonce:"41000",
        resources:[{kind:"object",storage:"content",
          target:"8301",owner:"8",ownerCapability:"85",controlCapability:"86",
          predicate:{type:"all",predicates:[]}}],
        sourceCapabilities:["42"],funding:[],feePayer:"8"},
      tool:{task:"7902",capability:"81",observeCapability:"81",
        targetRoot:$tool[0].cell.root,
        before:($tool[0].cell.grain | {generation,status,remaining,reserved})},
      parent:{task:"7901",capability:"73",observeCapability:"73",
        targetRoot:$parent[0].cell.root,
        before:($parent[0].cell.grain | {generation,status,remaining,reserved})}},
    grants:[{kind:"object",target:"10",capability:"55"},
      {kind:"account",target:"8",capability:"42"},
      {kind:"object",target:"7902",capability:"81"},
      {kind:"object",target:"7901",capability:"73"}]}' \
  >"$EVIDENCE/grain-birth-intent.json"
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/grain-birth-intent.json" --intent-kind grain-birth-intent \
  --key "$EVIDENCE/tool.key" --dir "$EVIDENCE/grain-birth-attempt" \
  >"$EVIDENCE/grain-birth.stdout"
confirmed "$EVIDENCE/grain-birth-attempt/outcome.json"
query born-content 8 8301 85 "$EVIDENCE/tool.key" 41010
jq -e '.type == "resource" and .cell.entries == []' \
  "$EVIDENCE/born-content/view.json" >/dev/null
query tool-after 8 7902 81 "$EVIDENCE/tool.key" 41011
query parent-after 8 7901 73 "$EVIDENCE/tool.key" 41012
jq -e '.cell.grain.remaining == "47" and .cell.grain.reserved == "0"' \
  "$EVIDENCE/tool-after/view.json" >/dev/null
jq -e '.cell.grain.status == "3" and .cell.grain.reserved == "1"' \
  "$EVIDENCE/parent-after/view.json" >/dev/null

# A same-profile owner-7 bare content birth is the positive factory-law
# control. The only factory predicate alternative for worker 8 requires the
# composite mode slot; both account predicates are the genesis's `all []`.
jq --slurpfile observed "$EVIDENCE/tool-after/challenge.json" \
  '{subject:"7",nonce:"41500",
    birth:(.grainBirth.birth | .creator="7" | .nonce="41500" |
      .height=$observed[0].height |
      .grainBirthTariff={base:"2",perBirth:"1"} |
      .resources[0].target="8303" | .resources[0].owner="7" |
      .resources[0].ownerCapability="103" |
      .resources[0].controlCapability="104" |
      .sourceCapabilities=["41"] | .feePayer="7"),
    grants:[{kind:"object",target:"10",capability:"54"},
      {kind:"account",target:"7",capability:"41"}]}' \
  "$EVIDENCE/grain-birth-intent.json" >"$EVIDENCE/owner-bare-intent.json"
"$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  --intent "$EVIDENCE/owner-bare-intent.json" --intent-kind birth-intent \
  --key "$EVIDENCE/controller.key" --dir "$EVIDENCE/owner-bare-attempt" \
  >"$EVIDENCE/owner-bare.stdout"
confirmed "$EVIDENCE/owner-bare-attempt/outcome.json"
query owner-bare-content 7 8303 103 "$EVIDENCE/controller.key" 41510
jq -e '.type == "resource" and .cell.entries == []' \
  "$EVIDENCE/owner-bare-content/view.json" >/dev/null

# The same worker's ordinary bare birth has valid source-account authority,
# but the installed factory law has no grain-backed mode slot on that route.
# The public native submit boundary intentionally erases the internal refusal
# reason; require that exact public admission refusal after a prepared call.
jq --slurpfile observed "$EVIDENCE/owner-bare-content/challenge.json" \
  '{subject:"8",nonce:"42000",
    birth:(.grainBirth.birth | .nonce="42000" |
      .height=$observed[0].height |
      .grainBirthTariff={base:"2",perBirth:"1"} |
      .resources[0].target="8302" |
      .resources[0].ownerCapability="87" |
      .resources[0].controlCapability="88"),
    grants:[{kind:"object",target:"10",capability:"55"},
      {kind:"account",target:"8",capability:"42"}]}' \
  "$EVIDENCE/grain-birth-intent.json" >"$EVIDENCE/worker-bare-intent.json"
if "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/worker-bare-intent.json" --intent-kind birth-intent \
    --key "$EVIDENCE/tool.key" --dir "$EVIDENCE/worker-bare-attempt" \
    >"$EVIDENCE/worker-bare.stdout" 2>"$EVIDENCE/worker-bare.stderr"; then
  echo "worker bare birth unexpectedly accepted" >&2; exit 1
fi
test -s "$EVIDENCE/worker-bare-attempt/plan.bin"
test -s "$EVIDENCE/worker-bare-attempt/call.bin"
jq -e '.type == "refused" and .phase == "61646d697373696f6e" and
  .detail == "726571756573742072656675736564"' \
  "$EVIDENCE/worker-bare-attempt/outcome.json" >/dev/null
query worker-bare-post 7 8303 103 "$EVIDENCE/controller.key" 42010
jq -e --slurpfile before "$EVIDENCE/owner-bare-content/challenge.json" \
  '.worldRoot == $before[0].worldRoot' \
  "$EVIDENCE/worker-bare-post/challenge.json" >/dev/null
echo "grain-backed resource birth native acceptance PASS"
