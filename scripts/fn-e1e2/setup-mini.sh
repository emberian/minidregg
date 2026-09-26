#!/bin/sh
# Create one fresh Mini consumer identity for the fn E1/E2 exchange.
# Keep the resulting directory private: it contains the custody key and Store.
set -eu

if [ "$#" -ne 2 ]; then
  echo "usage: $0 MINIDREGG_HOST NEW_DIRECTORY" >&2
  exit 2
fi

HOST=$1
ROOT=$2
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REPO=$(CDPATH='' cd -- "$HERE/../.." && pwd)
MINI=${MINI:-"$REPO/native/resource-client/target/debug/mini"}
STORE_BINARY=${STORE_BINARY:-"$REPO/native/hyperdocument-link-sqlite-store/target/debug/minidregg-link-sqlite-store"}
SIGNATURE_BINARY=${SIGNATURE_BINARY:-"$REPO/native/credential-signature-verifier/target/debug/minidregg-credential-signature-verifier"}
FN_FIXTURES=${FN_FIXTURES:-"$REPO/../fn/tests/fixtures/dregg-e1"}
GATEWAY_SUBJECT=${GATEWAY_SUBJECT:-7}
ORDINARY_SUBJECT=${ORDINARY_SUBJECT:-8}

case "$GATEWAY_SUBJECT:$ORDINARY_SUBJECT" in
  *[!0-9:]*|:*|*:) echo "subjects must be decimal integers" >&2; exit 2 ;;
esac
for subject in "$GATEWAY_SUBJECT" "$ORDINARY_SUBJECT"; do
  case "$subject" in
    0|0*) echo "subjects must be positive canonical decimals" >&2; exit 2 ;;
  esac
  if [ "${#subject}" -gt 9 ]; then
    echo "subject exceeds setup's supported range" >&2
    exit 2
  fi
done
if [ "$GATEWAY_SUBJECT" = "$ORDINARY_SUBJECT" ]; then
  echo "gateway and ordinary subjects must differ" >&2
  exit 2
fi

for file in "$HOST" "$MINI" "$STORE_BINARY" "$SIGNATURE_BINARY"; do
  if [ ! -x "$file" ]; then
    echo "not executable: $file" >&2
    exit 2
  fi
done
if [ ! -f "$FN_FIXTURES/independent-pin.json" ]; then
  echo "missing fn fixture: $FN_FIXTURES/independent-pin.json" >&2
  exit 2
fi
command -v jq >/dev/null 2>&1 || { echo "jq is required" >&2; exit 2; }
if [ -e "$ROOT" ]; then
  echo "refusing to replace directory: $ROOT" >&2
  exit 2
fi
umask 077
mkdir -m 700 "$ROOT"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)

"$MINI" keygen --secret "$ROOT/custody.key" --public "$ROOT/custody.pub" \
  >"$ROOT/public-key.txt"
PUBLIC_KEY=$(od -An -tx1 -v "$ROOT/custody.pub" | tr -d ' \n')
"$MINI" keygen --secret "$ROOT/ordinary.key" --public "$ROOT/ordinary.pub" \
  >"$ROOT/ordinary-public-key.txt"
ORDINARY_PUBLIC_KEY=$(od -An -tx1 -v "$ROOT/ordinary.pub" | tr -d ' \n')
if [ "$PUBLIC_KEY" = "$ORDINARY_PUBLIC_KEY" ]; then
  echo "gateway and ordinary custody keys collided" >&2
  exit 1
fi

cat >"$ROOT/operator.json" <<EOF
{
  "domain":8501,"federation":9,"factoryId":10,"resourceBookId":11,
  "authorityCatalogueId":12,"issuer":5,"ownerBudget":300000,"lifetime":10000,
  "tariffBase":3,"tariffPerBirth":2,"tariffPerGrant":1,
  "tariffPerInitialPayloadByte":0,"collector":99,"asset":0,
  "genesisHeight":10,"expectedSeed":0,
  "storageBinary":"$STORE_BINARY","storageRoot":"$ROOT/store",
  "signatureBinary":"$SIGNATURE_BINARY"
}
EOF
"$HOST" "$ROOT/operator.json" profile >"$ROOT/profile.json"
SEMANTICS=$(jq -er '.semantics | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' "$ROOT/profile.json")

cat >"$ROOT/genesis.json" <<EOF
{
  "domain":"8501","factoryId":"10","resourceBookId":"11",
  "authorityCatalogueId":"12","federation":"9","tariffBase":"3",
  "tariffPerBirth":"2","tariffPerGrant":"1","tariffPerInitialPayloadByte":"0",
  "collector":"99","asset":"0","expectedSemantics":"$SEMANTICS",
  "issuerEpoch":"2","genesisHeight":"10",
  "factoryPredicate":{"type":"all","predicates":[]},
  "enrollments":[{
    "key":{"keyId":"7007","keyEpoch":"2","algorithm":"1","subject":"$GATEWAY_SUBJECT",
           "publicKey":"$PUBLIC_KEY","activeFrom":"0","activeUntil":"1000000",
           "revoked":false},
    "accountId":"$GATEWAY_SUBJECT","spendCapabilityId":"41","controlCapabilityId":"51",
    "factoryObserveCapabilityId":"54","initialBalance":"100",
    "accountPredicate":{"type":"all","predicates":[]}
  },{
    "key":{"keyId":"8008","keyEpoch":"2","algorithm":"1","subject":"$ORDINARY_SUBJECT",
           "publicKey":"$ORDINARY_PUBLIC_KEY","activeFrom":"0","activeUntil":"1000000",
           "revoked":false},
    "accountId":"$ORDINARY_SUBJECT","spendCapabilityId":"42","controlCapabilityId":"52",
    "factoryObserveCapabilityId":"55","initialBalance":"100",
    "accountPredicate":{"type":"all","predicates":[]}
  }],
  "factoryControllerSubject":"$GATEWAY_SUBJECT","factoryControllerCapability":"53",
  "meterAllowance":{
    "incidences":"10000000","turnBytes":"10000000","memoryTouches":"10000000",
    "witnessBytes":"10000000","proofWork":"10000000","storageBytes":"10000000",
    "networkBytes":"10000000","sideEffectCount":"10000000","feeDebit":"10000000",
    "leaseByteBlocks":"10000000"
  }
}
EOF

"$MINI" bootstrap --host "$HOST" --config "$ROOT/operator.json" \
  --source "$ROOT/genesis.json" --dir "$ROOT/deployment" >"$ROOT/bootstrap.stdout"

cat >"$ROOT/birth-intent.json" <<EOF
{
  "subject":"$GATEWAY_SUBJECT","nonce":"22000",
  "birth":{
    "genesis":$(cat "$ROOT/genesis.json"),
    "template":{"issuer":"5","ownerBudget":"300000","lifetime":"10000"},
    "creator":"$GATEWAY_SUBJECT","nonce":"22000",
    "resources":[{"kind":"object","storage":"content","target":"600",
      "owner":"$GATEWAY_SUBJECT","ownerCapability":"61","controlCapability":"62",
      "predicate":{"type":"eq","slot":"request/subject","value":"$GATEWAY_SUBJECT"}}],
    "sourceCapabilities":["41"],"funding":[],"feePayer":"$GATEWAY_SUBJECT"
  },
  "grants":[{"kind":"object","target":"10","capability":"54"},
            {"kind":"account","target":"$GATEWAY_SUBJECT","capability":"41"}]
}
EOF

"$MINI" submit --host "$HOST" --config "$ROOT/deployment/pinned-config.json" \
  --intent "$ROOT/birth-intent.json" --intent-kind birth-intent \
  --key "$ROOT/custody.key" --dir "$ROOT/birth-attempt" >"$ROOT/birth.stdout"
jq -e '.type == "confirmed" and .confirmation == "installed" and .acceptedCount == "1"' \
  "$ROOT/birth-attempt/outcome.json" >/dev/null

cat >"$ROOT/gateway-policy-query.json" <<EOF
{"subject":"$GATEWAY_SUBJECT","nonce":"30000",
 "purpose":{"type":"query","kind":"object","target":"600","view":"policy"},
 "grants":[{"kind":"object","target":"600","capability":"61"}]}
EOF
"$MINI" query --host "$HOST" --config "$ROOT/deployment/pinned-config.json" \
  --intent "$ROOT/gateway-policy-query.json" --key "$ROOT/custody.key" --view policy \
  --dir "$ROOT/gateway-policy-query" >"$ROOT/gateway-policy-query.stdout"
jq -e --arg subject "$GATEWAY_SUBJECT" \
  '.policyId == "600" and .version == "0" and
   .predicate == {"type":"eq","slot":"request/subject","value":$subject}' \
  "$ROOT/gateway-policy-query/view.json" >/dev/null
POLICY_ADDRESS=$(jq -er '.address | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
  "$ROOT/gateway-policy-query/view.json")
# The gateway pin is an operator observation of the just-installed policy
# head. It is outside the genesis runtime-parameter commitment; keep the
# original bootstrap output intact and hand this copy to fn consumer routes.
jq --argjson subject "$GATEWAY_SUBJECT" --argjson address "$POLICY_ADDRESS" \
  '.fnGateway = {application:"mini-e1",subject:$subject,target:600,
                 capability:61,policyAddress:$address}' \
  "$ROOT/deployment/pinned-config.json" >"$ROOT/gateway-config.json"
jq '.storageBinary = "" | .storageRoot = ""' \
  "$ROOT/gateway-config.json" >"$ROOT/independent-verifier-pin.json"

# Give the ordinary signer a valid current mutation capability. The resource
# law still denies its subject, so a direct signed submission probes policy
# enforcement rather than merely the absence of a grant. The fn harness
# deliberately replays only genesis+birth into its A/B Stores.
cat >"$ROOT/gateway-query.json" <<EOF
{"subject":"$GATEWAY_SUBJECT","nonce":"30001",
 "purpose":{"type":"query","kind":"object","target":"600","view":"resource"},
 "grants":[{"kind":"object","target":"600","capability":"61"}]}
EOF
"$MINI" query --host "$HOST" --config "$ROOT/deployment/pinned-config.json" \
  --intent "$ROOT/gateway-query.json" --key "$ROOT/custody.key" --view resource \
  --dir "$ROOT/gateway-query" >"$ROOT/gateway-query.stdout"
TARGET_ROOT=$(jq -er '.page.root' "$ROOT/gateway-query/view.json")
AUTHORITY_ROOT=$(jq -er '.signing[0].authorityRoot' "$ROOT/gateway-query/challenge.json")
cat >"$ROOT/delegate-intent.json" <<EOF
{"subject":"$GATEWAY_SUBJECT","nonce":"30009","purpose":{"type":"prepare","draft":{
 "type":"delegate-source","command":{"kind":"object","domain":"8501",
 "semantics":"$SEMANTICS","subject":"$GATEWAY_SUBJECT","nonce":"30010",
 "expectedTargetRoot":"$TARGET_ROOT","parentId":"61","target":"600",
 "expectedPreRoot":"$AUTHORITY_ROOT",
 "child":{"id":"63","root":"61","parent":"61","issuer":"5",
   "holder":{"type":"subject","subject":"$ORDINARY_SUBJECT"},"targets":["600"],
   "verbs":["observe","mutate"],"maxCost":"300000",
   "notBefore":"10","notAfter":"1000","issuerEpoch":"2",
   "policyId":"600","policyEpoch":"0","ancestors":["61"],"channels":[]}}}},
 "grants":[{"kind":"object","target":"600","capability":"61"}]}
EOF
"$MINI" submit --host "$HOST" --config "$ROOT/deployment/pinned-config.json" \
  --intent "$ROOT/delegate-intent.json" --key "$ROOT/custody.key" \
  --dir "$ROOT/delegate-attempt" >"$ROOT/delegate.stdout"
jq -e '.type == "confirmed" and .confirmation == "installed" and .acceptedCount == "2"' \
  "$ROOT/delegate-attempt/outcome.json" >/dev/null

# The origin pin refers to the public, historical Mini report inside R. Its
# storage and signature helper are local verification inputs, not a second
# writable Store. fn's source claim remains separately supplied to the harness.
jq --arg signature "$SIGNATURE_BINARY" \
  '.signatureBinary = $signature | .storageBinary = "" | .storageRoot = ""' \
  "$FN_FIXTURES/independent-pin.json" >"$ROOT/origin-pin.json"
jq -n --argjson subject "$GATEWAY_SUBJECT" \
  '{application:"mini-e1",subject:$subject,target:600,capability:61}' \
  >"$ROOT/policy.json"

printf 'prepared Mini consumer: %s\n' "$ROOT"
printf 'pinned-config=%s\n' "$ROOT/deployment/pinned-config.json"
printf 'gateway-config=%s\n' "$ROOT/gateway-config.json"
printf 'independent-verifier-pin=%s\n' "$ROOT/independent-verifier-pin.json"
printf 'genesis=%s\n' "$ROOT/deployment/genesis.bin"
printf 'birth-intent=%s\n' "$ROOT/birth-intent.json"
printf 'custody-key=%s\n' "$ROOT/custody.key"
printf 'ordinary-key=%s\n' "$ROOT/ordinary.key"
printf 'ordinary-capability=%s\n' 63
printf 'origin-pin=%s\n' "$ROOT/origin-pin.json"
printf 'policy=%s\n' "$ROOT/policy.json"
