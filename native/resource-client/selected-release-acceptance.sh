#!/bin/sh
# Fresh source/recipient Stores for one source-authored owner-signed release.
# Run only with a source-matched Host that exposes the selected-release author
# routes. All semantic encoders and admission remain in Lean.
set -eu
umask 077

if [ "$#" -ne 2 ]; then
  echo "usage: $0 MINIDREGG_HOST NEW_EVIDENCE_DIRECTORY" >&2
  exit 2
fi

HOST=$1
EVIDENCE=$2
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
MINI=${MINI:-"$HERE/target/debug/mini"}
STORE_BINARY=${STORE_BINARY:-"$REPO/native/hyperdocument-link-sqlite-store/target/debug/minidregg-link-sqlite-store"}
SIGNATURE_BINARY=${SIGNATURE_BINARY:-"$REPO/native/credential-signature-verifier/target/debug/minidregg-credential-signature-verifier"}
for executable in "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY"; do
  [ -x "$executable" ] || { echo "not executable: $executable" >&2; exit 2; }
done
command -v jq >/dev/null 2>&1 || { echo "jq is required" >&2; exit 2; }
command -v rustc >/dev/null 2>&1 || { echo "rustc is required for the one-shot drop-reply proxy" >&2; exit 2; }
[ ! -e "$EVIDENCE" ] || { echo "refusing existing evidence directory" >&2; exit 2; }
case ${SELECTED_RELEASE_STOP_AFTER_ORIGINAL:-0} in
  0|1) ;;
  *) echo "SELECTED_RELEASE_STOP_AFTER_ORIGINAL must be 0 or 1" >&2; exit 2 ;;
esac
MESSAGE_SUFFIX=${SELECTED_RELEASE_MESSAGE_ID_SUFFIX:-}
if [ -n "$MESSAGE_SUFFIX" ]; then
  case $MESSAGE_SUFFIX in
    *[!A-Za-z0-9-]*) echo "invalid selected release Message-ID suffix" >&2; exit 2 ;;
  esac
  [ "${#MESSAGE_SUFFIX}" -le 64 ] || {
    echo "selected release Message-ID suffix exceeds 64 bytes" >&2; exit 2;
  }
fi
mkdir -m 700 "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
shasum -a 256 "$0" "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
  "$HERE/selected-release-drop-reply.rs" >"$EVIDENCE/input-sha256.txt"

decimal() {
  jq -er --arg field "$2" '.[$field] | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' "$1"
}

confirmed() {
  jq -e --arg kind "$2" '.type == "confirmed" and .confirmation == $kind and
    (all(.transactionId, .eventId, .acceptedCount, .imageBoundary;
      type == "string" and test("^(0|[1-9][0-9]*)$")))' "$1" >/dev/null
}

refused() {
  jq -e '.type == "refused" and (.phase | type == "string" and test("^[0-9a-f]+$")) and
    (.detail | type == "string" and test("^[0-9a-f]+$"))' "$1" >/dev/null
}

logical_image() {
  "$STORE_BINARY" read-to "$EVIDENCE/recipient/store" "$EVIDENCE/recipient/$1-image.bin"
}

digest_file() {
  shasum -a 256 "$1" | awk '{print $1}'
}

"$MINI" keygen --secret "$EVIDENCE/owner.key" --public "$EVIDENCE/owner.pub" \
  >"$EVIDENCE/owner-public.txt"
OWNER_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/owner.pub" | tr -d ' \n')

# The source and recipient are distinct deployments, with independent Stores
# and domains. The same enrolled owner key signs a source query and a selected
# recipient release. No source receipt is inferred from a claimed SourceRef.
provision() {
  side=$1 domain=$2 target=$3
  root="$EVIDENCE/$side"
  mkdir -m 700 "$root"
  cat >"$root/operator.json" <<EOF
{"domain":$domain,"federation":9,"factoryId":10,"resourceBookId":11,
 "authorityCellId":12,"issuer":5,"ownerBudget":100000,"lifetime":10000,
 "tariffBase":3,"tariffPerBirth":2,"tariffPerGrant":1,
 "tariffPerInitialPayloadByte":0,"collector":99,"asset":0,
 "genesisHeight":10,"expectedSeed":0,"storageBinary":"$STORE_BINARY",
 "storageRoot":"$root/store","signatureBinary":"$SIGNATURE_BINARY"}
EOF
  "$HOST" "$root/operator.json" profile >"$root/profile.json"
  semantics=$(decimal "$root/profile.json" semantics)
  cat >"$root/genesis.json" <<EOF
{"domain":"$domain","factoryId":"10","resourceBookId":"11",
 "authorityCellId":"12","federation":"9","tariffBase":"3",
 "tariffPerBirth":"2","tariffPerGrant":"1","tariffPerInitialPayloadByte":"0",
 "collector":"99","asset":"0","expectedSemantics":"$semantics",
 "issuerEpoch":"2","genesisHeight":"10",
 "factoryPredicate":{"type":"all","predicates":[]},
 "enrollments":[{"key":{"keyId":"7007","keyEpoch":"2","algorithm":"1",
   "subject":"7","publicKey":"$OWNER_PUBLIC","activeFrom":"0",
   "activeUntil":"1000000"},"accountId":"7",
   "spendCapabilityId":"41","controlCapabilityId":"51",
   "factoryObserveCapabilityId":"54","initialBalance":"100",
   "accountPredicate":{"type":"all","predicates":[]} }],
 "factoryControllerSubject":"7","factoryControllerCapability":"53",
 "meterAllowance":{"incidences":"10000000","turnBytes":"10000000",
   "memoryTouches":"10000000","witnessBytes":"10000000",
   "proofWork":"10000000","storageBytes":"10000000",
   "networkBytes":"10000000","sideEffectCount":"10000000",
   "feeDebit":"10000000","leaseByteBlocks":"10000000"}}
EOF
  "$MINI" bootstrap --host "$HOST" --config "$root/operator.json" \
    --source "$root/genesis.json" --dir "$root/deployment" >"$root/bootstrap.stdout"
  config="$root/deployment/pinned-config.json"
  cat >"$root/birth-intent.json" <<EOF
{"subject":"7","nonce":"22000","birth":{"genesis":$(cat "$root/genesis.json"),
 "template":{"issuer":"5","ownerBudget":"100000","lifetime":"10000"},
 "creator":"7","nonce":"22000","resources":[
   {"kind":"object","storage":"content","target":"$target","owner":"7",
    "ownerCapability":"61","controlCapability":"62",
    "predicate":{"type":"all","predicates":[]}}],
 "sourceCapabilities":["41"],"funding":[],"feePayer":"7"},
 "grants":[{"kind":"object","target":"10","capability":"54"},
   {"kind":"account","target":"7","capability":"41"}]}
EOF
  "$MINI" submit --host "$HOST" --config "$config" \
    --intent "$root/birth-intent.json" --intent-kind birth-intent \
    --key "$EVIDENCE/owner.key" --dir "$root/birth" >"$root/birth.stdout"
  confirmed "$root/birth/outcome.json" installed
}

provision source 8611 8001
provision recipient 8612 600
SOURCE_CONFIG="$EVIDENCE/source/deployment/pinned-config.json"
RECIPIENT_CONFIG="$EVIDENCE/recipient/deployment/pinned-config.json"

query_resource() {
  side=$1 target=$2 label=$3 nonce=$4
  root="$EVIDENCE/$side"
  jq -n --arg target "$target" --arg nonce "$nonce" \
    '{subject:"7",nonce:$nonce,
      purpose:{type:"query",kind:"object",target:$target,view:"resource"},
      grants:[{kind:"object",target:$target,capability:"61"}]}' \
    >"$root/$label-intent.json"
  if [ "$side" = recipient ] && [ -n "${RECIPIENT_SOCKET:-}" ]; then
    "$MINI" query --host "$HOST" --config "$root/deployment/pinned-config.json" \
      --socket "$RECIPIENT_SOCKET" --intent "$root/$label-intent.json" \
      --key "$EVIDENCE/owner.key" --view resource --dir "$root/$label" \
      >"$root/$label.stdout"
  else
    "$MINI" query --host "$HOST" --config "$root/deployment/pinned-config.json" \
      --intent "$root/$label-intent.json" --key "$EVIDENCE/owner.key" \
      --view resource --dir "$root/$label" >"$root/$label.stdout"
  fi
}

query_resource source 8001 before 30001
query_resource recipient 600 before 30002
jq -e '.page.entries == []' "$EVIDENCE/source/before/view.json" >/dev/null
jq -e '.page.entries == []' "$EVIDENCE/recipient/before/view.json" >/dev/null

query_policy() {
  label=$1 nonce=$2
  jq -n --arg nonce "$nonce" \
    '{subject:"7",nonce:$nonce,
      purpose:{type:"query",kind:"object",target:"600",view:"policy"},
      grants:[{kind:"object",target:"600",capability:"61"}]}' \
    >"$EVIDENCE/recipient/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$RECIPIENT_CONFIG" \
    --intent "$EVIDENCE/recipient/$label-intent.json" --key "$EVIDENCE/owner.key" \
    --view policy --dir "$EVIDENCE/recipient/$label" \
    >"$EVIDENCE/recipient/$label.stdout"
}
query_policy before-policy 30008

NOTE_HEX=$(printf '%s' 'Selected source note: one exact public version.' | od -An -tx1 -v | tr -d ' \n')
CHANGED_HEX=$(printf '%s' 'Changed selected source note under the same release key.' | od -An -tx1 -v | tr -d ' \n')
jq -n --slurpfile view "$EVIDENCE/source/before/view.json" \
  --slurpfile challenge "$EVIDENCE/source/before/challenge.json" \
  --arg payload "$NOTE_HEX" --arg changed "$CHANGED_HEX" \
  '{subject:"7",nonce:"30003",purpose:{type:"prepare",draft:{type:"invoke",
    command:{subject:"7",expectedAuthorityRoot:$challenge[0].signing[0].authorityRoot,
      nonce:"30004",targets:[{kind:"object",target:"8001",capability:"61",
        observeCapability:null,schemaVersion:"1",expectedTargetRoot:$view[0].page.root,
        payload:{type:"content",actions:[{type:"createAtom",atom:"7401",
          kind:{type:"text"},payload:$payload},
          {type:"createAtom",atom:"7402",kind:{type:"text"},payload:$changed}]}}]}}},
    grants:[{kind:"object",target:"8001",capability:"61"}]}' \
  >"$EVIDENCE/source/create-intent.json"
"$MINI" submit --host "$HOST" --config "$SOURCE_CONFIG" \
  --intent "$EVIDENCE/source/create-intent.json" --key "$EVIDENCE/owner.key" \
  --dir "$EVIDENCE/source/create" >"$EVIDENCE/source/create.stdout"
confirmed "$EVIDENCE/source/create/outcome.json" installed
query_resource source 8001 selected 30005
jq -e --arg payload "$NOTE_HEX" --arg changed "$CHANGED_HEX" \
  '.page.entries | length == 2 and
  any(.[]; .type == "atom" and .id == "7401" and .payload == $payload) and
  any(.[]; .type == "atom" and .id == "7402" and .payload == $changed)' \
  "$EVIDENCE/source/selected/view.json" >/dev/null

# Replace the recipient birth law with the exact owner-subject lock required
# by FnSelectiveReleaseSignature.select. This is a signed native policy install.
cat >"$EVIDENCE/recipient/install-intent.json" <<EOF
{"subject":"7","nonce":"30006","purpose":{"type":"prepare","draft":{
 "type":"install-source","subject":"7","control":"62","declaration":{
 "expectedPreRoot":"$(jq -er '.signing[0].authorityRoot' "$EVIDENCE/recipient/before-policy/challenge.json")",
 "expected":{"version":"0","address":"$(jq -er '.address' "$EVIDENCE/recipient/before-policy/view.json")"},
 "nonce":"30007","source":{"policyId":"600","version":"1",
 "domain":"8612","semantics":"$(decimal "$EVIDENCE/recipient/profile.json" semantics)",
 "previous":"$(jq -er '.address' "$EVIDENCE/recipient/before-policy/view.json")",
 "predicate":{"type":"eq","slot":"request/subject","value":"7"}}}}},
 "grants":[{"kind":"object","target":"600","capability":"61"}]}
EOF
"$MINI" submit --host "$HOST" --config "$RECIPIENT_CONFIG" \
  --intent "$EVIDENCE/recipient/install-intent.json" --key "$EVIDENCE/owner.key" \
  --dir "$EVIDENCE/recipient/install" >"$EVIDENCE/recipient/install.stdout"
confirmed "$EVIDENCE/recipient/install/outcome.json" installed
query_policy current-policy 30009
jq -e '.predicate == {"type":"eq","slot":"request/subject","value":"7"} and
  .version == "1"' "$EVIDENCE/recipient/current-policy/view.json" >/dev/null
query_resource recipient 600 current 30010
jq -e '.page.entries == []' "$EVIDENCE/recipient/current/view.json" >/dev/null

# Candidate preparation is a current signed selection, not proof that a
# source-side publication command was admitted. That stronger journey has a
# separate gate. The recipient still verifies owner signature/current law.
"$MINI" keygen --secret "$EVIDENCE/wrong-signer.key" \
  --public "$EVIDENCE/wrong-signer.pub" >"$EVIDENCE/wrong-signer-public.txt"
SIGNED_SOURCE_HEX=$(od -An -tx1 -v "$EVIDENCE/source/selected/signed-observation.bin" | tr -d ' \n')
POLICY_ADDRESS=$(decimal "$EVIDENCE/recipient/current-policy/view.json" address)
RECIPIENT_SEMANTICS=$(decimal "$EVIDENCE/recipient/profile.json" semantics)

build_candidate() {
  label=$1 atom=$2 owner_nonce=$3 signer=$4
  root="$EVIDENCE/candidate-$label"
  mkdir -m 700 "$root"
  jq -n --arg query "$SIGNED_SOURCE_HEX" --arg atom "$atom" \
    --arg semantics "$RECIPIENT_SEMANTICS" --arg policy "$POLICY_ADDRESS" \
    --arg nonce "$owner_nonce" \
    --arg message "<${label}${MESSAGE_SUFFIX:+-$MESSAGE_SUFFIX}@mini.invalid>" \
    '{signedQueryHex:$query,atom:$atom,destinationDomain:"8612",
      destinationSemantics:$semantics,destinationTarget:"600",
      group:"fn.test",messageId:$message,policyRoot:$policy,
      keysetRoot:"0",epoch:"2",ownerSubject:"7",ownerNonce:$nonce,
      expiresAt:"1000000",from:"owner@example.invalid",
      date:"Sun, 27 Sep 2026 12:00:00 +0000",subject:"Selected public note"}' \
    >"$root/request.json"
  "$HOST" "$SOURCE_CONFIG" selected-release-prepare \
    "$root/request.json" "$root/preimage.bin"
  "$MINI" selected-release-sign --host "$HOST" --config "$SOURCE_CONFIG" \
    --preimage "$root/preimage.bin" --key "$signer" \
    --output "$root/signature.bin"
  "$HOST" "$SOURCE_CONFIG" selected-release-assemble \
    "$root/preimage.bin" "$root/signature.bin" \
    'owner@example.invalid' 'Sun, 27 Sep 2026 12:00:00 +0000' \
    'Selected public note' "$root/packet.bin" "$root/article.eml"
}

build_ingress() {
  label=$1 query_label=$2
  root="$EVIDENCE/candidate-$label"
  authority=$(jq -er '.signing[0].authorityRoot' \
    "$EVIDENCE/recipient/$query_label/challenge.json")
  target=$(jq -er '.page.root' "$EVIDENCE/recipient/$query_label/view.json")
  "$HOST" "$RECIPIENT_CONFIG" selected-release-ingress \
    "$root/packet.bin" 61 "$authority" "$target" "$root/ingress.bin"
}

RECIPIENT_SOCKET="$EVIDENCE/recipient/session/host.sock"
mkdir -m 700 "$EVIDENCE/recipient/session"
SERVICE_PID=
DROP_PID=
SERVE_RUN=0
cleanup() {
  if [ -n "$DROP_PID" ]; then
    kill "$DROP_PID" 2>/dev/null || true
    wait "$DROP_PID" 2>/dev/null || true
  fi
  if [ -n "$SERVICE_PID" ]; then
    kill "$SERVICE_PID" 2>/dev/null || true
    wait "$SERVICE_PID" 2>/dev/null || true
  fi
}
trap cleanup EXIT INT TERM
start_recipient() {
  SERVE_RUN=$((SERVE_RUN + 1))
  "$MINI" serve --host "$HOST" --config "$RECIPIENT_CONFIG" \
    --socket "$RECIPIENT_SOCKET" >"$EVIDENCE/recipient/serve-$SERVE_RUN.stdout" \
    2>"$EVIDENCE/recipient/serve-$SERVE_RUN.stderr" &
  SERVICE_PID=$!
  count=0
  until [ -S "$RECIPIENT_SOCKET" ]; do
    kill -0 "$SERVICE_PID" 2>/dev/null || { echo "recipient service exited" >&2; exit 1; }
    count=$((count + 1))
    [ "$count" -le 30 ] || { echo "recipient socket start timed out" >&2; exit 1; }
    sleep 1
  done
}
stop_recipient() {
  kill "$SERVICE_PID"
  wait "$SERVICE_PID" 2>/dev/null || true
  SERVICE_PID=
}
start_recipient

build_candidate original 7401 99001 "$EVIDENCE/owner.key"
build_ingress original current
if [ "${SELECTED_RELEASE_STOP_AFTER_ORIGINAL:-0}" = 1 ]; then
  # Private fixture handoff only: the selected candidate is not source
  # publication authority, and recipient op20 has not been submitted.
  shasum -a 256 "$0" "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
    "$HERE/selected-release-drop-reply.rs" >"$EVIDENCE/final-input-sha256.txt"
  cmp "$EVIDENCE/input-sha256.txt" "$EVIDENCE/final-input-sha256.txt"
  printf 'selected candidate prepared without publication or receiving: %s\n' "$EVIDENCE"
  exit 0
fi
"$MINI" selected-release-submit --host "$HOST" --config "$RECIPIENT_CONFIG" \
  --socket "$RECIPIENT_SOCKET" --ingress "$EVIDENCE/candidate-original/ingress.bin" \
  --dir "$EVIDENCE/recipient/original-attempt" >"$EVIDENCE/recipient/original.stdout"
ORIGINAL_OUTCOME="$EVIDENCE/recipient/original-attempt/request-0000.outcome.json"
confirmed "$ORIGINAL_OUTCOME" installed
logical_image after-original
query_resource recipient 600 after-original 30011
PACKET_HEX=$(od -An -tx1 -v "$EVIDENCE/candidate-original/packet.bin" | tr -d ' \n')
jq -e --arg packet "$PACKET_HEX" '.page.entries | length == 1 and
  .[0].type == "atom" and .[0].payload == $packet' \
  "$EVIDENCE/recipient/after-original/view.json" >/dev/null

build_candidate conflict 7402 99001 "$EVIDENCE/owner.key"
build_ingress conflict after-original
if "$MINI" selected-release-submit --host "$HOST" --config "$RECIPIENT_CONFIG" \
  --socket "$RECIPIENT_SOCKET" --ingress "$EVIDENCE/candidate-conflict/ingress.bin" \
  --dir "$EVIDENCE/recipient/conflict-attempt" >"$EVIDENCE/recipient/conflict.stdout" \
  2>"$EVIDENCE/recipient/conflict.stderr"; then
  echo "changed same-key release unexpectedly installed" >&2; exit 1
fi
refused "$EVIDENCE/recipient/conflict-attempt/request-0000.outcome.json"
jq -e '.phase == "61646d697373696f6e"' \
  "$EVIDENCE/recipient/conflict-attempt/request-0000.outcome.json" >/dev/null
if "$MINI" selected-release-lookup --attempt "$EVIDENCE/recipient/conflict-attempt" \
  --socket "$RECIPIENT_SOCKET" >"$EVIDENCE/recipient/conflict-lookup.stdout" \
  2>"$EVIDENCE/recipient/conflict-lookup.stderr"; then
  echo "changed same-key lookup unexpectedly found a receipt" >&2; exit 1
fi
refused "$EVIDENCE/recipient/conflict-attempt/request-0001.outcome.json"
jq -e '.phase == "7265706c6179"' \
  "$EVIDENCE/recipient/conflict-attempt/request-0001.outcome.json" >/dev/null
logical_image after-conflict
cmp "$EVIDENCE/recipient/after-original-image.bin" \
  "$EVIDENCE/recipient/after-conflict-image.bin"

build_candidate wrong-signer 7401 99002 "$EVIDENCE/wrong-signer.key"
build_ingress wrong-signer after-original
if "$MINI" selected-release-submit --host "$HOST" --config "$RECIPIENT_CONFIG" \
  --socket "$RECIPIENT_SOCKET" --ingress "$EVIDENCE/candidate-wrong-signer/ingress.bin" \
  --dir "$EVIDENCE/recipient/wrong-signer-attempt" \
  >"$EVIDENCE/recipient/wrong-signer.stdout" \
  2>"$EVIDENCE/recipient/wrong-signer.stderr"; then
  echo "wrong owner signer unexpectedly installed" >&2; exit 1
fi
refused "$EVIDENCE/recipient/wrong-signer-attempt/request-0000.outcome.json"
jq -e '.phase == "61646d697373696f6e"' \
  "$EVIDENCE/recipient/wrong-signer-attempt/request-0000.outcome.json" >/dev/null
logical_image after-wrong-signer
cmp "$EVIDENCE/recipient/after-original-image.bin" \
  "$EVIDENCE/recipient/after-wrong-signer-image.bin"
"$MINI" selected-release-lookup --attempt "$EVIDENCE/recipient/wrong-signer-attempt" \
  --socket "$RECIPIENT_SOCKET" \
  >"$EVIDENCE/recipient/wrong-signer-lookup.stdout"
jq -e '.type == "absent"' \
  "$EVIDENCE/recipient/wrong-signer-attempt/request-0001.outcome.json" >/dev/null
query_resource recipient 600 after-negatives 30012
test "$(jq -er '.page.root' "$EVIDENCE/recipient/after-negatives/view.json")" = \
  "$(jq -er '.page.root' "$EVIDENCE/recipient/after-original/view.json")"
test "$(jq -er '.imageBoundary' "$EVIDENCE/recipient/after-negatives/challenge.json")" = \
  "$(jq -er '.imageBoundary' "$EVIDENCE/recipient/after-original/challenge.json")"

# The proxy forwards one exact op20 frame, waits for and privately retains its
# complete native reply, then drops only the client response. A confirmed
# native write must be recovered by exact op21, never by guessing from EOF.
build_candidate lost-reply 7401 99003 "$EVIDENCE/owner.key"
build_ingress lost-reply after-negatives
rustc --edition=2021 -D warnings "$HERE/selected-release-drop-reply.rs" \
  -o "$EVIDENCE/drop-reply-proxy"
DROP_SOCKET="$EVIDENCE/recipient/session/drop.sock"
"$EVIDENCE/drop-reply-proxy" "$RECIPIENT_SOCKET" "$DROP_SOCKET" \
  "$EVIDENCE/recipient/drop-request.frame" "$EVIDENCE/recipient/drop-reply.frame" \
  >"$EVIDENCE/recipient/drop-proxy.stdout" 2>"$EVIDENCE/recipient/drop-proxy.stderr" &
DROP_PID=$!
count=0
until [ -S "$DROP_SOCKET" ]; do
  kill -0 "$DROP_PID" 2>/dev/null || { echo "drop proxy exited" >&2; exit 1; }
  count=$((count + 1))
  [ "$count" -le 30 ] || { echo "drop proxy start timed out" >&2; exit 1; }
  sleep 1
done
if "$MINI" selected-release-submit --host "$HOST" --config "$RECIPIENT_CONFIG" \
  --socket "$DROP_SOCKET" --ingress "$EVIDENCE/candidate-lost-reply/ingress.bin" \
  --dir "$EVIDENCE/recipient/lost-attempt" \
  >"$EVIDENCE/recipient/lost.stdout" 2>"$EVIDENCE/recipient/lost.stderr"; then
  echo "dropped reply unexpectedly reached client" >&2; exit 1
fi
wait "$DROP_PID"
DROP_PID=
grep -q 'response uncertain' "$EVIDENCE/recipient/lost.stderr"
test "$(od -An -tu1 -j4 -N1 "$EVIDENCE/recipient/drop-reply.frame" | tr -d ' \n')" = 20
dd if="$EVIDENCE/recipient/drop-reply.frame" \
  of="$EVIDENCE/recipient/drop-native-outcome.bin" bs=1 skip=5 2>/dev/null
"$HOST" "$RECIPIENT_CONFIG" inspect outcome \
  "$EVIDENCE/recipient/drop-native-outcome.bin" \
  "$EVIDENCE/recipient/drop-native-outcome.json"
confirmed "$EVIDENCE/recipient/drop-native-outcome.json" installed
logical_image after-lost
query_resource recipient 600 after-lost 30014
LOST_PACKET_HEX=$(od -An -tx1 -v "$EVIDENCE/candidate-lost-reply/packet.bin" | tr -d ' \n')
jq -e --arg packet "$LOST_PACKET_HEX" '.page.entries |
  length == 2 and any(.[]; .type == "atom" and .payload == $packet)' \
  "$EVIDENCE/recipient/after-lost/view.json" >/dev/null
"$MINI" selected-release-lookup --attempt "$EVIDENCE/recipient/lost-attempt" \
  --socket "$RECIPIENT_SOCKET" >"$EVIDENCE/recipient/lost-lookup.stdout"
confirmed "$EVIDENCE/recipient/lost-attempt/request-0001.outcome.json" replayed
logical_image after-lost-lookup
cmp "$EVIDENCE/recipient/after-lost-image.bin" \
  "$EVIDENCE/recipient/after-lost-lookup-image.bin"
jq -S '{transactionId,eventId,acceptedCount,imageBoundary}' \
  "$EVIDENCE/recipient/drop-native-outcome.json" \
  >"$EVIDENCE/recipient/drop-native-receipt.json"
jq -S '{transactionId,eventId,acceptedCount,imageBoundary}' \
  "$EVIDENCE/recipient/lost-attempt/request-0001.outcome.json" \
  >"$EVIDENCE/recipient/lost-recovered-receipt.json"
cmp "$EVIDENCE/recipient/drop-native-receipt.json" \
  "$EVIDENCE/recipient/lost-recovered-receipt.json"

# A new policy head with the same exact subject lock keeps reads possible,
# while a new packet pinned to the old head must fail fresh current-law check.
query_policy pre-law 30015
PRE_LAW_ADDRESS=$(decimal "$EVIDENCE/recipient/pre-law/view.json" address)
jq -n --slurpfile prior "$EVIDENCE/recipient/pre-law/view.json" \
  --slurpfile challenge "$EVIDENCE/recipient/pre-law/challenge.json" \
  --arg semantics "$RECIPIENT_SEMANTICS" \
  '{subject:"7",nonce:"30016",purpose:{type:"prepare",draft:{
    type:"install-source",subject:"7",control:"62",declaration:{
      expectedPreRoot:$challenge[0].signing[0].authorityRoot,
      expected:{version:$prior[0].version,address:$prior[0].address},
      nonce:"30017",source:{policyId:"600",version:"2",domain:"8612",
        semantics:$semantics,previous:$prior[0].address,
        predicate:{type:"eq",slot:"request/subject",value:"7"}}}}},
    grants:[{kind:"object",target:"600",capability:"61"}]}' \
  >"$EVIDENCE/recipient/rotate-law-intent.json"
"$MINI" submit --host "$HOST" --config "$RECIPIENT_CONFIG" \
  --socket "$RECIPIENT_SOCKET" --intent "$EVIDENCE/recipient/rotate-law-intent.json" \
  --key "$EVIDENCE/owner.key" --dir "$EVIDENCE/recipient/rotate-law" \
  >"$EVIDENCE/recipient/rotate-law.stdout"
confirmed "$EVIDENCE/recipient/rotate-law/outcome.json" installed
logical_image after-law
query_policy after-law-policy 30018
test "$(decimal "$EVIDENCE/recipient/after-law-policy/view.json" address)" != "$PRE_LAW_ADDRESS"
query_resource recipient 600 after-law 30019

build_candidate stale-law 7401 99005 "$EVIDENCE/owner.key"
build_ingress stale-law after-law
if "$MINI" selected-release-submit --host "$HOST" --config "$RECIPIENT_CONFIG" \
  --socket "$RECIPIENT_SOCKET" --ingress "$EVIDENCE/candidate-stale-law/ingress.bin" \
  --dir "$EVIDENCE/recipient/stale-law-attempt" \
  >"$EVIDENCE/recipient/stale-law.stdout" \
  2>"$EVIDENCE/recipient/stale-law.stderr"; then
  echo "stale current-law release unexpectedly installed" >&2; exit 1
fi
refused "$EVIDENCE/recipient/stale-law-attempt/request-0000.outcome.json"
jq -e '.phase == "61646d697373696f6e"' \
  "$EVIDENCE/recipient/stale-law-attempt/request-0000.outcome.json" >/dev/null
logical_image after-law-refusal
cmp "$EVIDENCE/recipient/after-law-image.bin" \
  "$EVIDENCE/recipient/after-law-refusal-image.bin"
query_resource recipient 600 after-law-refusal 30020
test "$(jq -er '.page.root' "$EVIDENCE/recipient/after-law-refusal/view.json")" = \
  "$(jq -er '.page.root' "$EVIDENCE/recipient/after-law/view.json")"
test "$(jq -er '.imageBoundary' "$EVIDENCE/recipient/after-law-refusal/challenge.json")" = \
  "$(jq -er '.imageBoundary' "$EVIDENCE/recipient/after-law/challenge.json")"

"$MINI" selected-release-lookup --attempt "$EVIDENCE/recipient/original-attempt" \
  --socket "$RECIPIENT_SOCKET" \
  >"$EVIDENCE/recipient/original-historical.stdout"
confirmed "$EVIDENCE/recipient/original-attempt/request-0001.outcome.json" replayed
logical_image before-reopen
cmp "$EVIDENCE/recipient/after-law-image.bin" \
  "$EVIDENCE/recipient/before-reopen-image.bin"
stop_recipient
start_recipient
"$MINI" selected-release-lookup --attempt "$EVIDENCE/recipient/original-attempt" \
  --socket "$RECIPIENT_SOCKET" \
  >"$EVIDENCE/recipient/original-reopened.stdout"
confirmed "$EVIDENCE/recipient/original-attempt/request-0002.outcome.json" replayed
logical_image after-reopen
cmp "$EVIDENCE/recipient/before-reopen-image.bin" \
  "$EVIDENCE/recipient/after-reopen-image.bin"
jq -S '{transactionId,eventId,acceptedCount,imageBoundary}' "$ORIGINAL_OUTCOME" \
  >"$EVIDENCE/recipient/original-receipt.json"
for lookup in request-0001 request-0002; do
  jq -S '{transactionId,eventId,acceptedCount,imageBoundary}' \
    "$EVIDENCE/recipient/original-attempt/$lookup.outcome.json" \
    >"$EVIDENCE/recipient/$lookup-receipt.json"
  cmp "$EVIDENCE/recipient/original-receipt.json" \
    "$EVIDENCE/recipient/$lookup-receipt.json"
done
query_resource recipient 600 reopened 30021
test "$(jq -er '.page.root' "$EVIDENCE/recipient/reopened/view.json")" = \
  "$(jq -er '.page.root' "$EVIDENCE/recipient/after-law/view.json")"
test "$(jq -er '.imageBoundary' "$EVIDENCE/recipient/reopened/challenge.json")" = \
  "$(jq -er '.imageBoundary' "$EVIDENCE/recipient/after-law/challenge.json")"
query_resource source 8001 source-final 30022
test "$(jq -er '.page.root' "$EVIDENCE/source/source-final/view.json")" = \
  "$(jq -er '.page.root' "$EVIDENCE/source/selected/view.json")"
shasum -a 256 "$0" "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
  "$HERE/selected-release-drop-reply.rs" >"$EVIDENCE/final-input-sha256.txt"
cmp "$EVIDENCE/input-sha256.txt" "$EVIDENCE/final-input-sha256.txt"
jq -n --slurpfile original "$ORIGINAL_OUTCOME" \
  --slurpfile lost "$EVIDENCE/recipient/drop-native-outcome.json" \
  --arg scriptSha "$(digest_file "$0")" \
  --arg proxySha "$(digest_file "$HERE/selected-release-drop-reply.rs")" \
  --arg hostSha "$(digest_file "$HOST")" \
  --arg miniSha "$(digest_file "$MINI")" \
  --arg sourceRoot "$(jq -er '.page.root' "$EVIDENCE/source/selected/view.json")" \
  --arg recipientRoot "$(jq -er '.page.root' "$EVIDENCE/recipient/reopened/view.json")" \
  --arg stableImageSha "$(digest_file "$EVIDENCE/recipient/after-reopen-image.bin")" \
  --arg originalIngressSha "$(digest_file "$EVIDENCE/candidate-original/ingress.bin")" \
  --arg lostIngressSha "$(digest_file "$EVIDENCE/candidate-lost-reply/ingress.bin")" \
  '{type:"minidregg-selected-candidate-receiving-v2",
    sourcePublicationAuthorized:false,
    source:{domain:"8611",resource:"8001",selectedAtom:"7401",root:$sourceRoot},
    recipient:{domain:"8612",resource:"600",root:$recipientRoot,
      logicalImageSha256:$stableImageSha},
    inputSha256:{script:$scriptSha,proxy:$proxySha,host:$hostSha,mini:$miniSha,
      originalIngress:$originalIngressSha,lostIngress:$lostIngressSha},
    original:($original[0] | {type,confirmation,transactionId,eventId,
      acceptedCount,imageBoundary}),
    lostReplyNative:($lost[0] | {type,confirmation,transactionId,eventId,
      acceptedCount,imageBoundary}),
    checks:["same-key conflict", "wrong signer", "absent lookup no write",
      "lost reply exact lookup", "stale current law", "historical receipt after reopen",
      "complete logical image equality after refusals and reopen"]}' \
  >"$EVIDENCE/public-summary.json"
printf 'selected-candidate receiving PASS: %s\n' "$EVIDENCE"
