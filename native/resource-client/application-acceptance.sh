#!/bin/sh
# Native two-participant application birth gate. No hosted model or app process runs.
set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: $0 SOURCE_MATCHED_MINIDREGG_HOST NEW_PRIVATE_EVIDENCE_DIRECTORY" >&2
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
[ ! -e "$EVIDENCE" ] || { echo "refusing existing evidence: $EVIDENCE" >&2; exit 2; }
mkdir -m 700 "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)
umask 077
shasum -a 256 "$0" "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY" \
  >"$EVIDENCE/input-sha256.txt"

decimal() {
  jq -er --arg field "$2" '.[$field] | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' "$1"
}
confirmed() {
  jq -e '.type == "confirmed" and .confirmation == "installed" and
    (all(.transactionId, .eventId, .acceptedCount, .worldRoot;
      type == "string" and test("^(0|[1-9][0-9]*)$")))' "$1" >/dev/null
}
query() (
  label=$1 subject=$2 target=$3 capability=$4 key=$5 nonce=$6 view=$7
  jq -n --arg subject "$subject" --arg target "$target" \
    --arg capability "$capability" --arg nonce "$nonce" --arg view "$view" \
    '{subject:$subject,nonce:$nonce,
      purpose:{type:"query",kind:"object",target:$target,view:$view},
      grants:[{kind:"object",target:$target,capability:$capability}]}' \
    >"$EVIDENCE/$label-intent.json"
  "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" --view "$view" \
    --dir "$EVIDENCE/$label" >"$EVIDENCE/$label.stdout"
  [ -s "$EVIDENCE/$label/view.bin" ] && [ -s "$EVIDENCE/$label/signed-observation.bin" ]
)
deny_query() (
  label=$1 subject=$2 target=$3 capability=$4 key=$5 nonce=$6
  jq -n --arg subject "$subject" --arg target "$target" \
    --arg capability "$capability" --arg nonce "$nonce" \
    '{subject:$subject,nonce:$nonce,
      purpose:{type:"query",kind:"object",target:$target,view:"resource"},
      grants:[{kind:"object",target:$target,capability:$capability}]}' \
    >"$EVIDENCE/$label-intent.json"
  if "$MINI" query --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --key "$key" --view resource \
    --dir "$EVIDENCE/$label" >"$EVIDENCE/$label.stdout" \
    2>"$EVIDENCE/$label.stderr"; then
    echo "unauthorized read succeeded: $label" >&2
    exit 1
  fi
  reason_hex=$(printf '%s' 'observation refused' | od -An -tx1 -v | tr -d ' \n')
  if ! { [ -s "$EVIDENCE/$label/signed-observation.bin" ] &&
      [ ! -e "$EVIDENCE/$label/view.json" ] &&
      grep -Fq 'host refused query' "$EVIDENCE/$label.stderr" &&
      grep -Fq "$reason_hex" "$EVIDENCE/$label.stderr"; }; then
    echo "missing exact native observation refusal: $label" >&2
    exit 1
  fi
)
submit_kind() (
  label=$1 kind=$2 key=$3
  "$MINI" submit --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --intent "$EVIDENCE/$label-intent.json" --intent-kind "$kind" \
    --key "$key" --dir "$EVIDENCE/$label-attempt" >"$EVIDENCE/$label.stdout"
  confirmed "$EVIDENCE/$label-attempt/outcome.json"
  [ -s "$EVIDENCE/$label-attempt/call.bin" ]
)
start_session() {
  session=$1
  mkdir -m 700 "$EVIDENCE/$session"
  SOCKET=$EVIDENCE/$session/host.sock
  "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >"$EVIDENCE/$session/mini.stdout" 2>"$EVIDENCE/$session/mini.stderr" &
  SERVICE_PID=$!
  tick=0
  until [ -S "$SOCKET" ]; do
    kill -0 "$SERVICE_PID" 2>/dev/null || { echo "Mini service exited" >&2; exit 1; }
    tick=$((tick + 1))
    [ "$tick" -lt 120 ] || { echo "Mini service startup timed out" >&2; exit 1; }
    sleep 1
  done
}
stop_session() {
  if [ -n "${SERVICE_PID:-}" ]; then
    kill "$SERVICE_PID" 2>/dev/null || :
    wait "$SERVICE_PID" 2>/dev/null || :
    SERVICE_PID=
  fi
}
trap stop_session EXIT HUP INT TERM

for who in owner first second; do
  "$MINI" keygen --secret "$EVIDENCE/$who.key" --public "$EVIDENCE/$who.pub" \
    >"$EVIDENCE/$who-public.txt"
done
OWNER_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/owner.pub" | tr -d ' \n')
FIRST_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/first.pub" | tr -d ' \n')
SECOND_PUBLIC=$(od -An -tx1 -v "$EVIDENCE/second.pub" | tr -d ' \n')
[ "$OWNER_PUBLIC" != "$FIRST_PUBLIC" ] && [ "$OWNER_PUBLIC" != "$SECOND_PUBLIC" ] &&
  [ "$FIRST_PUBLIC" != "$SECOND_PUBLIC" ]

cat >"$EVIDENCE/operator.json" <<EOF
{"domain":8527,"federation":9,"factoryId":10,"resourceBookId":11,
 "authorityCellId":12,"issuer":5,"ownerBudget":100000,"lifetime":10000,
 "tariffBase":3,"tariffPerBirth":2,"tariffPerGrant":1,
 "tariffPerInitialPayloadByte":0,"collector":99,"asset":0,
 "genesisHeight":10,"expectedSeed":0,"storageBinary":"$STORE_BINARY",
 "storageRoot":"$EVIDENCE/store","signatureBinary":"$SIGNATURE_BINARY"}
EOF
"$HOST" "$EVIDENCE/operator.json" profile >"$EVIDENCE/operator-profile.json"
SEMANTICS=$(decimal "$EVIDENCE/operator-profile.json" semantics)

cat >"$EVIDENCE/genesis.json" <<EOF
{"domain":"8527","factoryId":"10","resourceBookId":"11",
 "authorityCellId":"12","federation":"9","tariffBase":"3",
 "tariffPerBirth":"2","tariffPerGrant":"1","tariffPerInitialPayloadByte":"0",
 "collector":"99","asset":"0","expectedSemantics":"$SEMANTICS",
 "issuerEpoch":"2","genesisHeight":"10",
 "factoryPredicate":{"type":"all","predicates":[]},
 "enrollments":[
  {"key":{"keyId":"7007","keyEpoch":"2","algorithm":"1","subject":"7",
    "publicKey":"$OWNER_PUBLIC","activeFrom":"0","activeUntil":"1000000","nextKeyDigest":null},
   "accountId":"7","spendCapabilityId":"41","controlCapabilityId":"51",
   "factoryObserveCapabilityId":"54","initialBalance":"1000",
   "accountPredicate":{"type":"all","predicates":[]}},
  {"key":{"keyId":"8008","keyEpoch":"2","algorithm":"1","subject":"8",
    "publicKey":"$FIRST_PUBLIC","activeFrom":"0","activeUntil":"1000000","nextKeyDigest":null},
   "accountId":"8","spendCapabilityId":"42","controlCapabilityId":"52",
   "factoryObserveCapabilityId":"55","initialBalance":"1000",
   "accountPredicate":{"type":"all","predicates":[]}},
  {"key":{"keyId":"9009","keyEpoch":"2","algorithm":"1","subject":"9",
    "publicKey":"$SECOND_PUBLIC","activeFrom":"0","activeUntil":"1000000","nextKeyDigest":null},
   "accountId":"9","spendCapabilityId":"43","controlCapabilityId":"53",
   "factoryObserveCapabilityId":"56","initialBalance":"1000",
   "accountPredicate":{"type":"all","predicates":[]}}
 ],
 "factoryControllerSubject":"7","factoryControllerCapability":"57","clockTickers":[],
 "tailBound":"256",
 "meterAllowance":{"incidences":"10000000","turnBytes":"10000000",
   "memoryTouches":"10000000","witnessBytes":"10000000",
   "proofWork":"10000000","storageBytes":"10000000",
   "networkBytes":"10000000","sideEffectCount":"10000000",
   "feeDebit":"10000000","leaseByteBlocks":"10000000"}}
EOF
"$MINI" bootstrap --host "$HOST" --config "$EVIDENCE/operator.json" \
  --source "$EVIDENCE/genesis.json" --dir "$EVIDENCE/deployment" \
  >"$EVIDENCE/bootstrap.stdout"
CONFIG=$EVIDENCE/deployment/pinned-config.json
start_session session-first

# The signed factory query supplies the exact current height for each later
# grant template. A stale height is refused by native TemplateBound admission.
query factory-owner 7 10 54 "$EVIDENCE/owner.key" 10001 resource
APP_HEIGHT=$(decimal "$EVIDENCE/factory-owner/challenge.json" height)
cat >"$EVIDENCE/app-intent.json" <<EOF
{"subject":"7","nonce":"11001","applicationBirth":{
 "genesis":$(cat "$EVIDENCE/genesis.json"),
 "template":{"issuer":"5","ownerBudget":"100000","lifetime":"10000"},
 "height":"$APP_HEIGHT","creator":"7","nonce":"11001",
 "application":{"app":"6100","packageManifest":"6101","snapshotManifest":"6102",
   "owner":"7","appOwnerCapability":"101","appControlCapability":"102",
   "packageOwnerCapability":"103","packageControlCapability":"104",
   "snapshotOwnerCapability":"105","snapshotControlCapability":"106"},
 "sourceCapabilities":["41"],"funding":[],"feePayer":"7"},
 "grants":[{"kind":"object","target":"10","capability":"54"},
   {"kind":"account","target":"7","capability":"41"}]}
EOF
submit_kind app application-birth-intent "$EVIDENCE/owner.key"
query app-owner 7 6100 101 "$EVIDENCE/owner.key" 10002 resource
query package-owner 7 6101 103 "$EVIDENCE/owner.key" 10003 resource
query snapshot-owner 7 6102 105 "$EVIDENCE/owner.key" 10004 resource
query app-policy 7 6100 101 "$EVIDENCE/owner.key" 10005 policy
jq -e --arg target "6100" '[.cell.entries[] |
  select(.key.type == "object" and .key.resource == $target)] | length == 4' \
  "$EVIDENCE/app-owner/view.json" >/dev/null
jq -e '.policyId == "6100" and .version == "0"' \
  "$EVIDENCE/app-policy/view.json" >/dev/null

for member in first second; do
  if [ "$member" = first ]; then
    subject=8 key=$EVIDENCE/first.key account=8 spend=42 observe=55
    session_target=6208 descriptor=6308 owner_cap=201 control_cap=202
    descriptor_owner=203 descriptor_control=204 kind=web nonce=12008 tag=0
  else
    subject=9 key=$EVIDENCE/second.key account=9 spend=43 observe=56
    session_target=6209 descriptor=6309 owner_cap=211 control_cap=212
    descriptor_owner=213 descriptor_control=214 kind=api nonce=12009 tag=4
  fi
  query "factory-$member" "$subject" 10 "$observe" "$key" "$nonce" resource
  height=$(decimal "$EVIDENCE/factory-$member/challenge.json" height)
  cat >"$EVIDENCE/session-$member-intent.json" <<EOF
{"subject":"$subject","nonce":"$nonce","applicationSessionBirth":{
 "genesis":$(cat "$EVIDENCE/genesis.json"),
 "template":{"issuer":"5","ownerBudget":"100000","lifetime":"10000"},
 "height":"$height","creator":"$subject","nonce":"$nonce",
 "session":{"app":"6100","session":"$session_target","descriptor":"$descriptor",
   "participant":"$subject","kind":"$kind",
   "sessionOwnerCapability":"$owner_cap","sessionControlCapability":"$control_cap",
   "descriptorOwnerCapability":"$descriptor_owner",
   "descriptorControlCapability":"$descriptor_control"},
 "sourceCapabilities":["$spend"],"funding":[],"feePayer":"$account"},
 "grants":[{"kind":"object","target":"10","capability":"$observe"},
   {"kind":"account","target":"$account","capability":"$spend"}]}
EOF
  submit_kind "session-$member" application-session-birth-intent "$key"
  query "session-$member-read" "$subject" "$session_target" "$owner_cap" \
    "$key" "$((nonce + 100))" resource
  query "descriptor-$member-read" "$subject" "$descriptor" "$descriptor_owner" \
    "$key" "$((nonce + 101))" resource
  query "session-$member-policy" "$subject" "$session_target" "$owner_cap" \
    "$key" "$((nonce + 102))" policy
  jq -e --arg resource "$session_target" --arg tag "$tag" \
    '([.cell.entries[] | select(.key.type == "object" and .key.resource == $resource and
      .key.field == "0" and .value == "6100")] | length) == 1 and
     ([.cell.entries[] | select(.key.type == "object" and .key.resource == $resource and
      .key.field == "3" and .value == $tag)] | length) == 1' \
    "$EVIDENCE/session-$member-read/view.json" >/dev/null
  jq -e --arg target "$session_target" '.policyId == $target and .version == "0"' \
    "$EVIDENCE/session-$member-policy/view.json" >/dev/null
done

# The factory-issued owner grant includes delegation. Each child has observe
# alone; neither the capability nor this fixture authorizes app dispatch.
for member in first second; do
  if [ "$member" = first ]; then subject=8 child=301; else subject=9 child=302; fi
  query "app-before-delegate-$member" 7 6100 101 "$EVIDENCE/owner.key" \
    "$((13000 + subject))" resource
  root=$(jq -er '.cell.root | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
    "$EVIDENCE/app-before-delegate-$member/view.json")
  authority=$(jq -er '.authorityRoot |
    select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
    "$EVIDENCE/app-before-delegate-$member/challenge.json")
  cat >"$EVIDENCE/delegate-$member-intent.json" <<EOF
{"subject":"7","nonce":"$((14000 + subject))","purpose":{"type":"prepare","draft":{
 "type":"delegate-source","command":{"kind":"object","domain":"8527",
 "semantics":"$SEMANTICS","subject":"7","nonce":"$((15000 + subject))",
 "expectedTargetRoot":"$root","parentId":"101","target":"6100",
 "child":{"id":"$child","root":"101","parent":"101","issuer":"5",
   "holder":{"type":"subject","subject":"$subject"},"targets":["6100"],
   "verbs":["observe"],"maxCost":"50000","notBefore":"10","notAfter":"1000",
   "issuerEpoch":"2","policyId":"6100","policyEpoch":"0",
   "ancestors":["101"],"channels":[]}}}},
 "grants":[{"kind":"object","target":"6100","capability":"101"}]}
EOF
  submit_kind "delegate-$member" intent "$EVIDENCE/owner.key"
done
query app-first 8 6100 301 "$EVIDENCE/first.key" 16008 resource
query app-second 9 6100 302 "$EVIDENCE/second.key" 16009 resource
FIRST_ROOT=$(jq -er '.cell.root' "$EVIDENCE/app-first/view.json")
SECOND_ROOT=$(jq -er '.cell.root' "$EVIDENCE/app-second/view.json")
[ "$FIRST_ROOT" = "$SECOND_ROOT" ]
"$STORE_BINARY" read-to "$EVIDENCE/store" "$EVIDENCE/before-denied-image.bin"
deny_query second-cannot-read-first 9 6208 201 "$EVIDENCE/second.key" 17009
deny_query first-cannot-read-second 8 6209 211 "$EVIDENCE/first.key" 17008
"$STORE_BINARY" read-to "$EVIDENCE/store" "$EVIDENCE/after-denied-image.bin"
cmp "$EVIDENCE/before-denied-image.bin" "$EVIDENCE/after-denied-image.bin"

# Restart the pinned Host session, recover the original exact signed call by
# lookup, and show that no second birth or debit was installed.
query factory-before-reopen 7 10 54 "$EVIDENCE/owner.key" 18001 resource
BEFORE_BOUNDARY=$(decimal "$EVIDENCE/factory-before-reopen/challenge.json" worldRoot)
"$STORE_BINARY" read-to "$EVIDENCE/store" "$EVIDENCE/before-reopen-image.bin"
stop_session
start_session session-reopen
"$MINI" retry --attempt "$EVIDENCE/session-first-attempt" --mode lookup \
  --socket "$SOCKET" >"$EVIDENCE/session-first-replay.stdout"
jq -e '.type == "confirmed" and .confirmation == "replayed"' \
  "$EVIDENCE/session-first-attempt/retry-0001.json" >/dev/null
for field in transactionId eventId acceptedCount worldRoot; do
  [ "$(decimal "$EVIDENCE/session-first-attempt/outcome.json" "$field")" = \
    "$(decimal "$EVIDENCE/session-first-attempt/retry-0001.json" "$field")" ]
done
query factory-after-reopen 7 10 54 "$EVIDENCE/owner.key" 18002 resource
[ "$(decimal "$EVIDENCE/factory-after-reopen/challenge.json" worldRoot)" = \
  "$BEFORE_BOUNDARY" ]
query app-first-reopen 8 6100 301 "$EVIDENCE/first.key" 18008 resource
query app-second-reopen 9 6100 302 "$EVIDENCE/second.key" 18009 resource
[ "$(jq -er '.cell.root' "$EVIDENCE/app-first-reopen/view.json")" = "$FIRST_ROOT" ]
[ "$(jq -er '.cell.root' "$EVIDENCE/app-second-reopen/view.json")" = "$FIRST_ROOT" ]
"$STORE_BINARY" read-to "$EVIDENCE/store" "$EVIDENCE/after-reopen-image.bin"
cmp "$EVIDENCE/before-reopen-image.bin" "$EVIDENCE/after-reopen-image.bin"

jq -n --arg app "6100" --arg first "6208" --arg second "6209" \
  --arg boundary "$BEFORE_BOUNDARY" \
  --slurpfile appReceipt "$EVIDENCE/app-attempt/outcome.json" \
  --slurpfile firstReceipt "$EVIDENCE/session-first-attempt/outcome.json" \
  --slurpfile secondReceipt "$EVIDENCE/session-second-attempt/outcome.json" \
  '{status:"pass",scope:"native-two-subject-app-birth-and-observe",
    app:$app,firstSession:$first,secondSession:$second,
    appReceipt:$appReceipt[0],firstSessionReceipt:$firstReceipt[0],
    secondSessionReceipt:$secondReceipt[0],reopenWorldRoot:$boundary,
    appObserveDelegatedSeparately:true,crossSessionReadsRefused:true,
    originalSessionReceiptReplayed:true}' \
  >"$EVIDENCE/application-acceptance.json"
cat "$EVIDENCE/application-acceptance.json"
