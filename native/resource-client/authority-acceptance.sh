#!/bin/sh
set -eu

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
  if [ ! -x "$executable" ]; then
    echo "not executable: $executable" >&2
    exit 2
  fi
done
if ! command -v jq >/dev/null 2>&1; then
  echo "jq is required" >&2
  exit 2
fi
if [ -e "$EVIDENCE" ]; then
  echo "refusing to replace evidence directory: $EVIDENCE" >&2
  exit 2
fi
mkdir "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
SCRIPT_SHA256=$(shasum -a 256 "$0" | awk '{print $1}')

decimal() {
  jq -er --arg field "$2" '.[$field] |
    select(type == "string" and test("^(0|[1-9][0-9]*)$"))' "$1"
}

challenge_decimal() {
  decimal "$1" "$2"
}

receipt() {
  jq -e '.type == "confirmed" and .confirmation == $kind and
    (all(.transactionId, .eventId, .acceptedCount, .imageBoundary;
      type == "string" and test("^(0|[1-9][0-9]*)$")))' \
    --arg kind "$2" "$1" >/dev/null
}

refusal() {
  jq -e '.type == "refused" and
    (.phase | type == "string" and test("^[0-9a-f]+$")) and
    (.detail | type == "string" and test("^[0-9a-f]+$"))' "$1" >/dev/null
}

query_resource() {
  name=$1
  subject=$2
  capability=$3
  key=$4
  cat >"$EVIDENCE/$name-intent.json" <<EOF
{"subject":"$subject","nonce":"$5",
 "purpose":{"type":"query","kind":"object","target":"600","view":"resource"},
 "grants":[{"kind":"object","target":"600","capability":"$capability"}]}
EOF
  "$MINI" query --host "$HOST" --config "$CONFIG" \
    --intent "$EVIDENCE/$name-intent.json" --key "$key" --view resource \
    --dir "$EVIDENCE/$name" >"$EVIDENCE/$name.stdout"
}

query_policy() {
  name=$1
  subject=$2
  capability=$3
  key=$4
  cat >"$EVIDENCE/$name-intent.json" <<EOF
{"subject":"$subject","nonce":"$5",
 "purpose":{"type":"query","kind":"object","target":"600","view":"policy"},
 "grants":[{"kind":"object","target":"600","capability":"$capability"}]}
EOF
  "$MINI" query --host "$HOST" --config "$CONFIG" \
    --intent "$EVIDENCE/$name-intent.json" --key "$key" --view policy \
    --dir "$EVIDENCE/$name" >"$EVIDENCE/$name.stdout"
}

"$MINI" keygen --secret "$EVIDENCE/alice.key" --public "$EVIDENCE/alice.pub" \
  >"$EVIDENCE/alice-public.txt"
"$MINI" keygen --secret "$EVIDENCE/bob.key" --public "$EVIDENCE/bob.pub" \
  >"$EVIDENCE/bob-public.txt"
ALICE_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/alice.pub" | tr -d ' \n')
BOB_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/bob.pub" | tr -d ' \n')
test "$ALICE_PUBLIC" != "$BOB_PUBLIC"

cat >"$EVIDENCE/operator.json" <<EOF
{"domain":8501,"federation":9,"factoryId":10,"resourceBookId":11,
 "authorityCatalogueId":12,"issuer":5,"ownerBudget":100000,"lifetime":10000,
 "tariffBase":3,"tariffPerBirth":2,"tariffPerGrant":1,
 "tariffPerInitialPayloadByte":0,"collector":99,"asset":0,
 "genesisHeight":10,"expectedSeed":0,"storageBinary":"$STORE_BINARY",
 "storageRoot":"$EVIDENCE/store","signatureBinary":"$SIGNATURE_BINARY"}
EOF
"$HOST" "$EVIDENCE/operator.json" profile >"$EVIDENCE/operator-profile.json"
SEMANTICS=$(decimal "$EVIDENCE/operator-profile.json" semantics)

cat >"$EVIDENCE/genesis.json" <<EOF
{
 "domain":"8501","factoryId":"10","resourceBookId":"11",
 "authorityCatalogueId":"12","federation":"9","tariffBase":"3",
 "tariffPerBirth":"2","tariffPerGrant":"1","tariffPerInitialPayloadByte":"0",
 "collector":"99","asset":"0","expectedSemantics":"$SEMANTICS",
 "issuerEpoch":"2","genesisHeight":"10",
 "factoryPredicate":{"type":"all","predicates":[]},
 "enrollments":[
   {"key":{"keyId":"7007","keyEpoch":"2","algorithm":"1","subject":"7",
     "publicKey":"$ALICE_PUBLIC","activeFrom":"0","activeUntil":"1000000",
     "revoked":false},
    "accountId":"7","spendCapabilityId":"41","controlCapabilityId":"51",
    "factoryObserveCapabilityId":"54","initialBalance":"100",
    "accountPredicate":{"type":"all","predicates":[]}},
   {"key":{"keyId":"8008","keyEpoch":"2","algorithm":"1","subject":"8",
     "publicKey":"$BOB_PUBLIC","activeFrom":"0","activeUntil":"1000000",
     "revoked":false},
    "accountId":"8","spendCapabilityId":"42","controlCapabilityId":"52",
    "factoryObserveCapabilityId":"55","initialBalance":"200",
    "accountPredicate":{"type":"all","predicates":[]}}
 ],
 "factoryControllerSubject":"7","factoryControllerCapability":"53",
 "meterAllowance":{"incidences":"10000000","turnBytes":"10000000",
   "memoryTouches":"10000000","witnessBytes":"10000000",
   "proofWork":"10000000","storageBytes":"10000000",
   "networkBytes":"10000000","sideEffectCount":"10000000",
   "feeDebit":"10000000","leaseByteBlocks":"10000000"}
}
EOF

"$MINI" bootstrap --host "$HOST" --config "$EVIDENCE/operator.json" \
  --source "$EVIDENCE/genesis.json" --dir "$EVIDENCE/deployment" \
  >"$EVIDENCE/bootstrap.stdout"
CONFIG="$EVIDENCE/deployment/pinned-config.json"

cat >"$EVIDENCE/birth-intent.json" <<EOF
{"subject":"7","nonce":"22000",
 "birth":{"genesis":$(cat "$EVIDENCE/genesis.json"),
   "template":{"issuer":"5","ownerBudget":"100000","lifetime":"10000"},
   "creator":"7","nonce":"22000",
   "resources":[{"kind":"object","storage":"declared","target":"600",
     "owner":"7","ownerCapability":"61","controlCapability":"62",
     "predicate":{"type":"all","predicates":[]}}],
   "sourceCapabilities":["41"],"funding":[],"feePayer":"7"},
 "grants":[{"kind":"object","target":"10","capability":"54"},
   {"kind":"account","target":"7","capability":"41"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/birth-intent.json" --intent-kind birth-intent \
  --key "$EVIDENCE/alice.key" --dir "$EVIDENCE/birth-attempt" \
  >"$EVIDENCE/birth.stdout"
receipt "$EVIDENCE/birth-attempt/outcome.json" installed
test "$(decimal "$EVIDENCE/birth-attempt/outcome.json" acceptedCount)" = 1

query_policy policy-before 7 61 "$EVIDENCE/alice.key" 30001
POLICY_VIEW="$EVIDENCE/policy-before/view.json"
OLD_ADDRESS=$(decimal "$POLICY_VIEW" address)
test "$(decimal "$POLICY_VIEW" version)" = 0
test "$(decimal "$POLICY_VIEW" policyId)" = 600
test "$(decimal "$POLICY_VIEW" domain)" = 8501
test "$(decimal "$POLICY_VIEW" semantics)" = "$SEMANTICS"
jq -e '.previous == null and .predicate == {"type":"all","predicates":[]}' \
  "$POLICY_VIEW" >/dev/null
POLICY_ROOT=$(jq -er '.signing[0].authorityRoot |
  select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$EVIDENCE/policy-before/challenge.json")

# The public view is a complete, source-owned record, not a display-only digest.
jq '{policyId, version, domain, semantics, previous, predicate}' "$POLICY_VIEW" \
  >"$EVIDENCE/policy-before-source.json"
"$MINI" author --host "$HOST" --config "$CONFIG" --kind policy \
  --input "$EVIDENCE/policy-before-source.json" \
  --output "$EVIDENCE/policy-before-roundtrip.bin"
ROUNDTRIP=$(od -An -tx1 -v "$EVIDENCE/policy-before-roundtrip.bin" | tr -d ' \n')
CANONICAL=$(jq -er '.canonical | select(type == "string" and test("^[0-9a-f]+$"))' "$POLICY_VIEW")
test "$ROUNDTRIP" = "$CANONICAL"

# Current rule: both can read, only Bob can mutate, only Alice can delegate
# and manage policy/revocation. The previous all[] rule admits this install.
cat >"$EVIDENCE/install-intent.json" <<EOF
{"subject":"7","nonce":"30002","purpose":{"type":"prepare","draft":{
 "type":"install-source","subject":"7","control":"62","declaration":{
   "expectedPreRoot":"$POLICY_ROOT",
   "expected":{"version":"0","address":"$OLD_ADDRESS"},
   "nonce":"30003","source":{"policyId":"600","version":"1",
     "domain":"8501","semantics":"$SEMANTICS","previous":"$OLD_ADDRESS",
     "predicate":{"type":"any","predicates":[
       {"type":"all","predicates":[
         {"type":"eq","slot":"request/verb","value":"1"},
         {"type":"memberOf","slot":"request/subject","values":["7","8"]}]},
       {"type":"all","predicates":[
         {"type":"eq","slot":"request/verb","value":"2"},
         {"type":"eq","slot":"request/subject","value":"8"}]},
       {"type":"all","predicates":[
         {"type":"memberOf","slot":"request/verb","values":["3","4","5"]},
         {"type":"eq","slot":"request/subject","value":"7"}]}
     ]}}}}},
 "grants":[{"kind":"object","target":"600","capability":"61"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/install-intent.json" --key "$EVIDENCE/alice.key" \
  --dir "$EVIDENCE/install-attempt" >"$EVIDENCE/install.stdout"
receipt "$EVIDENCE/install-attempt/outcome.json" installed
test "$(decimal "$EVIDENCE/install-attempt/outcome.json" acceptedCount)" = 2

query_policy policy-after 7 61 "$EVIDENCE/alice.key" 30004
NEW_ADDRESS=$(decimal "$EVIDENCE/policy-after/view.json" address)
test "$NEW_ADDRESS" != "$OLD_ADDRESS"
test "$(decimal "$EVIDENCE/policy-after/view.json" version)" = 1
test "$(decimal "$EVIDENCE/policy-after/view.json" previous)" = "$OLD_ADDRESS"
jq -e '.predicate.type == "any" and (.predicate.predicates | length) == 3' \
  "$EVIDENCE/policy-after/view.json" >/dev/null
jq '{policyId, version, domain, semantics, previous, predicate}' \
  "$EVIDENCE/policy-after/view.json" >"$EVIDENCE/policy-after-source.json"
"$MINI" author --host "$HOST" --config "$CONFIG" --kind policy \
  --input "$EVIDENCE/policy-after-source.json" \
  --output "$EVIDENCE/policy-after-roundtrip.bin"
ROUNDTRIP=$(od -An -tx1 -v "$EVIDENCE/policy-after-roundtrip.bin" | tr -d ' \n')
CANONICAL=$(jq -er '.canonical | select(type == "string" and test("^[0-9a-f]+$"))' \
  "$EVIDENCE/policy-after/view.json")
test "$ROUNDTRIP" = "$CANONICAL"

query_resource alice-before-delegate 7 61 "$EVIDENCE/alice.key" 30005
TARGET_ROOT=$(jq -er '.page.root | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$EVIDENCE/alice-before-delegate/view.json")
AUTHORITY_ROOT=$(jq -er '.signing[0].authorityRoot |
  select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$EVIDENCE/alice-before-delegate/challenge.json")
BEFORE_DENIAL=$(challenge_decimal "$EVIDENCE/alice-before-delegate/challenge.json" imageBoundary)

# A valid Alice signer and owner grant cannot mutate under the installed law.
cat >"$EVIDENCE/alice-denied-intent.json" <<EOF
{"subject":"7","nonce":"30006","purpose":{"type":"prepare","draft":{
 "type":"invoke","command":{"subject":"7","expectedAuthorityRoot":"$AUTHORITY_ROOT",
 "nonce":"30007","targets":[{"kind":"object","target":"600",
 "capability":"61","observeCapability":null,"schemaVersion":"1",
 "expectedTargetRoot":"$TARGET_ROOT","payload":{"type":"scalar","actions":[
   {"type":"create","key":{"type":"object","resource":"600","field":"0"},
    "value":"1"}]}}]}}},
 "grants":[{"kind":"object","target":"600","capability":"61"}]}
EOF
if "$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/alice-denied-intent.json" --key "$EVIDENCE/alice.key" \
  --dir "$EVIDENCE/alice-denied-attempt" >"$EVIDENCE/alice-denied.stdout" \
  2>"$EVIDENCE/alice-denied.stderr"; then
  echo "Alice mutation unexpectedly passed the installed rule" >&2
  exit 1
fi
test -s "$EVIDENCE/alice-denied-attempt/call.bin"
refusal "$EVIDENCE/alice-denied-attempt/outcome.json"
test -f "$EVIDENCE/alice-denied-attempt/signed-observation.bin"
query_resource alice-after-denial 7 61 "$EVIDENCE/alice.key" 30008
test "$(challenge_decimal "$EVIDENCE/alice-after-denial/challenge.json" imageBoundary)" = "$BEFORE_DENIAL"
test "$(challenge_decimal "$EVIDENCE/alice-after-denial/challenge.json" height)" = 12
test "$(jq -er '.page.root' "$EVIDENCE/alice-after-denial/view.json")" = "$TARGET_ROOT"
jq -e '(.page.entries | length) == 1 and
  .page.entries[0].key.type == "object" and
  .page.entries[0].key.resource == "600" and
  .page.entries[0].key.field == "1" and
  .page.entries[0].value == "0"' \
  "$EVIDENCE/alice-after-denial/view.json" >/dev/null

cat >"$EVIDENCE/delegate-intent.json" <<EOF
{"subject":"7","nonce":"30009","purpose":{"type":"prepare","draft":{
 "type":"delegate-source","command":{"kind":"object","domain":"8501",
 "semantics":"$SEMANTICS","subject":"7","nonce":"30010",
 "expectedTargetRoot":"$TARGET_ROOT","parentId":"61","target":"600",
 "expectedPreRoot":"$AUTHORITY_ROOT",
 "child":{"id":"63","root":"61","parent":"61","issuer":"5",
   "holder":{"type":"subject","subject":"8"},"targets":["600"],
   "verbs":["observe","mutate"],"maxCost":"50000",
   "notBefore":"10","notAfter":"1000","issuerEpoch":"2",
   "policyId":"600","policyEpoch":"0","ancestors":["61"],"channels":[]}}}},
 "grants":[{"kind":"object","target":"600","capability":"61"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/delegate-intent.json" --key "$EVIDENCE/alice.key" \
  --dir "$EVIDENCE/delegate-attempt" >"$EVIDENCE/delegate.stdout"
receipt "$EVIDENCE/delegate-attempt/outcome.json" installed
test "$(decimal "$EVIDENCE/delegate-attempt/outcome.json" acceptedCount)" = 3

query_resource bob-before-write 8 63 "$EVIDENCE/bob.key" 30011
BOB_ROOT=$(jq -er '.page.root | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$EVIDENCE/bob-before-write/view.json")
test "$BOB_ROOT" = "$TARGET_ROOT"
BOB_AUTHORITY_ROOT=$(jq -er '.signing[0].authorityRoot |
  select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$EVIDENCE/bob-before-write/challenge.json")

cat >"$EVIDENCE/bob-write-intent.json" <<EOF
{"subject":"8","nonce":"30012","purpose":{"type":"prepare","draft":{
 "type":"invoke","command":{"subject":"8","expectedAuthorityRoot":"$BOB_AUTHORITY_ROOT",
 "nonce":"30013","targets":[{"kind":"object","target":"600",
 "capability":"63","observeCapability":null,"schemaVersion":"1",
 "expectedTargetRoot":"$BOB_ROOT","payload":{"type":"scalar","actions":[
   {"type":"create","key":{"type":"object","resource":"600","field":"0"},
    "value":"1"}]}}]}}},
 "grants":[{"kind":"object","target":"600","capability":"63"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/bob-write-intent.json" --key "$EVIDENCE/bob.key" \
  --dir "$EVIDENCE/bob-write-attempt" >"$EVIDENCE/bob-write.stdout"
receipt "$EVIDENCE/bob-write-attempt/outcome.json" installed
test "$(decimal "$EVIDENCE/bob-write-attempt/outcome.json" acceptedCount)" = 4

query_resource alice-after-bob 7 61 "$EVIDENCE/alice.key" 30014
jq -e '[.page.entries[] | select(.key.type == "object" and .key.resource == "600" and
  .key.field == "0" and .value == "1")] | length == 1' \
  "$EVIDENCE/alice-after-bob/view.json" >/dev/null
POST_BOB_ROOT=$(jq -er '.page.root | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$EVIDENCE/alice-after-bob/view.json")
POST_BOB_AUTHORITY=$(jq -er '.signing[0].authorityRoot |
  select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$EVIDENCE/alice-after-bob/challenge.json")
test "$POST_BOB_ROOT" != "$BOB_ROOT"
test "$(challenge_decimal "$EVIDENCE/alice-after-bob/challenge.json" height)" = 14

# The child has observe+mutate, never program policy management. The host
# accepts its signatures but refuses the fully signed management call.
query_policy bob-policy 8 63 "$EVIDENCE/bob.key" 30015
BOB_POLICY_ROOT=$(jq -er '.signing[0].authorityRoot |
  select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$EVIDENCE/bob-policy/challenge.json")
BOB_POLICY_ADDRESS=$(decimal "$EVIDENCE/bob-policy/view.json" address)
BEFORE_CONTROL_DENIAL=$(challenge_decimal "$EVIDENCE/bob-policy/challenge.json" imageBoundary)
cat >"$EVIDENCE/bob-denied-install-intent.json" <<EOF
{"subject":"8","nonce":"30016","purpose":{"type":"prepare","draft":{
 "type":"install-source","subject":"8","control":"63","declaration":{
   "expectedPreRoot":"$BOB_POLICY_ROOT",
   "expected":{"version":"1","address":"$BOB_POLICY_ADDRESS"},
   "nonce":"30017","source":{"policyId":"600","version":"2",
     "domain":"8501","semantics":"$SEMANTICS","previous":"$BOB_POLICY_ADDRESS",
     "predicate":{"type":"all","predicates":[]}}}}},
 "grants":[{"kind":"object","target":"600","capability":"63"}]}
EOF
if "$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/bob-denied-install-intent.json" --key "$EVIDENCE/bob.key" \
  --dir "$EVIDENCE/bob-denied-install-attempt" \
  >"$EVIDENCE/bob-denied-install.stdout" \
  2>"$EVIDENCE/bob-denied-install.stderr"; then
  echo "Bob unexpectedly gained policy management" >&2
  exit 1
fi
test -f "$EVIDENCE/bob-denied-install-attempt/signed-observation.bin"
test -s "$EVIDENCE/bob-denied-install-attempt/call.bin"
refusal "$EVIDENCE/bob-denied-install-attempt/outcome.json"
query_policy alice-policy-before-revoke 7 61 "$EVIDENCE/alice.key" 30018
test "$(challenge_decimal "$EVIDENCE/alice-policy-before-revoke/challenge.json" imageBoundary)" = "$BEFORE_CONTROL_DENIAL"
test "$(challenge_decimal "$EVIDENCE/alice-policy-before-revoke/challenge.json" height)" = 14
test "$(decimal "$EVIDENCE/alice-policy-before-revoke/view.json" address)" = "$NEW_ADDRESS"

cat >"$EVIDENCE/revoke-intent.json" <<EOF
{"subject":"7","nonce":"30019","purpose":{"type":"prepare","draft":{
 "type":"revoke-source","command":{"kind":"object","subject":"7",
 "nonce":"30020","target":"600","victimKind":"object","capability":"63",
 "controlCapability":"62","expectedTargetRoot":"$POST_BOB_ROOT",
 "expectedAuthorityRoot":"$POST_BOB_AUTHORITY"}}},
 "grants":[{"kind":"object","target":"600","capability":"61"}]}
EOF
"$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/revoke-intent.json" --key "$EVIDENCE/alice.key" \
  --dir "$EVIDENCE/revoke-attempt" >"$EVIDENCE/revoke.stdout"
receipt "$EVIDENCE/revoke-attempt/outcome.json" installed
test "$(decimal "$EVIDENCE/revoke-attempt/outcome.json" acceptedCount)" = 5

# Bob's fresh, separately signed read and mutation can no longer use child 63.
cat >"$EVIDENCE/bob-after-revoke-query.json" <<'EOF'
{"subject":"8","nonce":"30021",
 "purpose":{"type":"query","kind":"object","target":"600","view":"resource"},
 "grants":[{"kind":"object","target":"600","capability":"63"}]}
EOF
if "$MINI" query --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/bob-after-revoke-query.json" --key "$EVIDENCE/bob.key" \
  --view resource --dir "$EVIDENCE/bob-after-revoke-query" \
  >"$EVIDENCE/bob-after-revoke-query.stdout" \
  2>"$EVIDENCE/bob-after-revoke-query.stderr"; then
  echo "Bob unexpectedly read through revoked grant" >&2
  exit 1
fi
test ! -e "$EVIDENCE/bob-after-revoke-query/view.json"

query_resource alice-before-retry 7 61 "$EVIDENCE/alice.key" 30022
FINAL_BEFORE_BOUNDARY=$(challenge_decimal "$EVIDENCE/alice-before-retry/challenge.json" imageBoundary)
FINAL_BEFORE_HEIGHT=$(challenge_decimal "$EVIDENCE/alice-before-retry/challenge.json" height)
test "$FINAL_BEFORE_HEIGHT" = 15
test "$FINAL_BEFORE_BOUNDARY" = "$(decimal "$EVIDENCE/revoke-attempt/outcome.json" imageBoundary)"
FINAL_TARGET_ROOT=$(jq -er '.page.root | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$EVIDENCE/alice-before-retry/view.json")
test "$FINAL_TARGET_ROOT" = "$POST_BOB_ROOT"
jq -e '(.page.entries | length) == 2 and
  ([.page.entries[] | select(.key.type == "object" and .key.resource == "600" and
    .key.field == "0" and .value == "1")] | length) == 1 and
  ([.page.entries[] | select(.key.type == "object" and .key.resource == "600" and
    .key.field == "1" and .value == "0")] | length) == 1' \
  "$EVIDENCE/alice-before-retry/view.json" >/dev/null
FINAL_AUTHORITY_ROOT=$(jq -er '.signing[0].authorityRoot |
  select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$EVIDENCE/alice-before-retry/challenge.json")
cat >"$EVIDENCE/bob-after-revoke-invoke.json" <<EOF
{"subject":"8","nonce":"30023","purpose":{"type":"prepare","draft":{
 "type":"invoke","command":{"subject":"8","expectedAuthorityRoot":"$FINAL_AUTHORITY_ROOT",
 "nonce":"30024","targets":[{"kind":"object","target":"600",
 "capability":"63","observeCapability":null,"schemaVersion":"1",
 "expectedTargetRoot":"$FINAL_TARGET_ROOT","payload":{"type":"scalar","actions":[
   {"type":"create","key":{"type":"object","resource":"600","field":"2"},
    "value":"2"}]}}]}}},
 "grants":[{"kind":"object","target":"600","capability":"63"}]}
EOF
if "$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/bob-after-revoke-invoke.json" --key "$EVIDENCE/bob.key" \
  --dir "$EVIDENCE/bob-after-revoke-invoke" \
  >"$EVIDENCE/bob-after-revoke-invoke.stdout" \
  2>"$EVIDENCE/bob-after-revoke-invoke.stderr"; then
  echo "Bob unexpectedly mutated through revoked grant" >&2
  exit 1
fi
test ! -e "$EVIDENCE/bob-after-revoke-invoke/outcome.json"

# Historical retry is allowed to return the original receipt, but must leave
# the current boundary and height unchanged after the later revocation.
CALL_HASH_BEFORE=$(shasum -a 256 "$EVIDENCE/bob-write-attempt/call.bin" | awk '{print $1}')
"$MINI" retry --attempt "$EVIDENCE/bob-write-attempt" --mode submit \
  >"$EVIDENCE/bob-retry.stdout"
CALL_HASH_AFTER=$(shasum -a 256 "$EVIDENCE/bob-write-attempt/call.bin" | awk '{print $1}')
test "$CALL_HASH_BEFORE" = "$CALL_HASH_AFTER"
receipt "$EVIDENCE/bob-write-attempt/retry-0001.json" replayed
for field in transactionId eventId acceptedCount imageBoundary; do
  initial=$(decimal "$EVIDENCE/bob-write-attempt/outcome.json" "$field")
  replay=$(decimal "$EVIDENCE/bob-write-attempt/retry-0001.json" "$field")
  test "$initial" = "$replay"
done
query_resource alice-final 7 61 "$EVIDENCE/alice.key" 30025
test "$(challenge_decimal "$EVIDENCE/alice-final/challenge.json" imageBoundary)" = "$FINAL_BEFORE_BOUNDARY"
test "$(challenge_decimal "$EVIDENCE/alice-final/challenge.json" height)" = "$FINAL_BEFORE_HEIGHT"
jq -e '(.page.entries | length) == 2 and
  ([.page.entries[] | select(.key.type == "object" and .key.resource == "600" and
    .key.field == "0" and .value == "1")] | length) == 1 and
  ([.page.entries[] | select(.key.type == "object" and .key.resource == "600" and
    .key.field == "1" and .value == "0")] | length) == 1' \
  "$EVIDENCE/alice-final/view.json" >/dev/null

birth_id=$(decimal "$EVIDENCE/birth-attempt/outcome.json" transactionId)
install_id=$(decimal "$EVIDENCE/install-attempt/outcome.json" transactionId)
delegate_id=$(decimal "$EVIDENCE/delegate-attempt/outcome.json" transactionId)
bob_id=$(decimal "$EVIDENCE/bob-write-attempt/outcome.json" transactionId)
revoke_id=$(decimal "$EVIDENCE/revoke-attempt/outcome.json" transactionId)
cat >"$EVIDENCE/authority-acceptance.json" <<EOF
{"status":"pass","host":"$HOST","semantics":"$SEMANTICS",
 "scriptSha256":"$SCRIPT_SHA256",
 "birthTransaction":"$birth_id","policyInstallTransaction":"$install_id",
 "delegationTransaction":"$delegate_id","bobWriteTransaction":"$bob_id",
 "revocationTransaction":"$revoke_id","bobCallSha256":"$CALL_HASH_AFTER",
 "finalHeight":"$FINAL_BEFORE_HEIGHT","finalImageBoundary":"$FINAL_BEFORE_BOUNDARY",
 "policyRefusedAliceMutation":true,"bobManagementRefused":true,
 "revokedBobReadAndMutationRefused":true,"historicalRetryExact":true}
EOF
cat "$EVIDENCE/authority-acceptance.json"
