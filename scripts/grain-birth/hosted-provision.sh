#!/bin/sh
# Fresh Mini-only governed factory and grain provision for an actual hosted
# Hermes resource birth. The caller starts the host/controller/provider later.
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
SOURCE_SHA=202a6ee4495ed46c474e2a965b258b6f2a4a94412d58f2319c69e9c8c35bd1cb
test "$(sha256sum "$SOURCE" | cut -d ' ' -f 1)" = "$SOURCE_SHA" || {
  echo "workroom source changed; review overlay before use" >&2; exit 2;
}
test ! -e "$EVIDENCE" || { echo "evidence directory exists" >&2; exit 2; }
STAGE=$(mktemp -d)
trap 'rm -rf "$STAGE"' EXIT HUP INT TERM

# Keep the committed workroom provisioner byte-for-byte; this exact-SHA
# private overlay enables only the independent grain-birth tariff and a
# factory law where owner 7 may use bare birth and worker 8 needs the
# explicit grain-backed mode for mutation. Worker observation remains valid.
# shellcheck disable=SC2016 # Match the provisioner's literal shell variable.
sed \
  -e 's|"signatureBinary":"$SIGNATURE_BINARY"}|"signatureBinary":"$SIGNATURE_BINARY","grainBirthTariff":{"base":2,"perBirth":1}}|' \
  -e 's|"birth":{"genesis":|"birth":{"grainBirthTariff":{"base":"2","perBirth":"1"},"genesis":|' \
  -e 's|"factoryPredicate":{"type":"all","predicates":\[\]}|"factoryPredicate":{"type":"any","predicates":[{"type":"eq","slot":"request/subject","value":"7"},{"type":"all","predicates":[{"type":"eq","slot":"request/subject","value":"8"},{"type":"any","predicates":[{"type":"eq","slot":"request/verb","value":"1"},{"type":"eq","slot":"birth/mode/grain-backed","value":"1"}]}]}]}|' \
  "$SOURCE" > "$STAGE/provision.sh"
test "$(rg -c 'grainBirthTariff' "$STAGE/provision.sh")" = 6
test "$(rg -c 'birth/mode/grain-backed' "$STAGE/provision.sh")" = 1
chmod 700 "$STAGE/provision.sh"
WORKROOM_PARENT_TASK=9301 WORKROOM_TOOL_TASK=9302 \
  MINI="$MINI" STORE_BINARY="$STORE_BINARY" SIGNATURE_BINARY="$SIGNATURE_BINARY" \
  "$STAGE/provision.sh" "$HOST" "$EVIDENCE"
sha256sum "$STAGE/provision.sh" > "$EVIDENCE/overlay.sha256"
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
jq -e '(.birth.resources | map(.target) | index("9303")) == null' \
  "$EVIDENCE/birth-intent.json" >/dev/null

# `genesis` is the source-authored bootstrap source, not a copied resource
# view. It carries no logical height; the runtime must derive birth.height
# from matching signed tool and parent query challenges after reservation.
jq --slurpfile genesis "$EVIDENCE/genesis.json" '
  .toolTask.reserve = "4" |
  .toolTask.allowedBirthFamilies = [{
    name:"note",genesis:$genesis[0],
    template:{issuer:"5",ownerBudget:"100000",lifetime:"10000"},
    predicate:{type:"all",predicates:[]},
    factoryTarget:"10",factoryObserveCapability:"55",
    payerAccount:"8",payerCapability:"42",payerObserveCapability:"42",
    tariffBase:"2",tariffPerBirth:"1",
    targetStart:"9303",ownerCapabilityStart:"185",controlCapabilityStart:"186",
    maxBirths:1,maxResultBytes:262144
  }]' "$EVIDENCE/runtime-config.base.json" \
  > "$EVIDENCE/runtime-config.birth-base.json"
jq -e '.task == "9301" and .toolTask.task == "9302" and
  .toolTask.allowedBirthFamilies[0].genesis.genesisHeight == "10" and
  (.toolTask.allowedBirthFamilies[0].genesis | has("height") | not)' \
  "$EVIDENCE/runtime-config.birth-base.json" >/dev/null
printf '%s\n' "$EVIDENCE/runtime-config.birth-base.json"
