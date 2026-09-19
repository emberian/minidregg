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
  echo "jq is required for acceptance assertions" >&2
  exit 2
fi
if [ -e "$EVIDENCE" ]; then
  echo "refusing to replace evidence directory: $EVIDENCE" >&2
  exit 2
fi
mkdir "$EVIDENCE"
EVIDENCE=$(CDPATH='' cd -- "$EVIDENCE" && pwd)

"$MINI" keygen --secret "$EVIDENCE/alice.key" --public "$EVIDENCE/alice.pub" \
  >"$EVIDENCE/public-key.txt"
PUBLIC_KEY=$(od -An -tx1 -v "$EVIDENCE/alice.pub" | tr -d ' \n')

cat >"$EVIDENCE/operator.json" <<EOF
{
  "domain": 8501,
  "federation": 9,
  "factoryId": 10,
  "resourceBookId": 11,
  "authorityCatalogueId": 12,
  "issuer": 5,
  "ownerBudget": 100000,
  "lifetime": 10000,
  "tariffBase": 3,
  "tariffPerBirth": 2,
  "tariffPerGrant": 1,
  "tariffPerInitialPayloadByte": 0,
  "collector": 99,
  "asset": 0,
  "genesisHeight": 10,
  "expectedSeed": 0,
  "storageBinary": "$STORE_BINARY",
  "storageRoot": "$EVIDENCE/store",
  "signatureBinary": "$SIGNATURE_BINARY"
}
EOF

"$HOST" "$EVIDENCE/operator.json" profile >"$EVIDENCE/operator-profile.json"
SEMANTICS=$(jq -er '.semantics' "$EVIDENCE/operator-profile.json")

cat >"$EVIDENCE/genesis.json" <<EOF
{
  "domain": "8501",
  "factoryId": "10",
  "resourceBookId": "11",
  "authorityCatalogueId": "12",
  "federation": "9",
  "tariffBase": "3",
  "tariffPerBirth": "2",
  "tariffPerGrant": "1",
  "tariffPerInitialPayloadByte": "0",
  "collector": "99",
  "asset": "0",
  "expectedSemantics": "$SEMANTICS",
  "issuerEpoch": "2",
  "genesisHeight": "10",
  "factoryPredicate": {"type": "all", "predicates": []},
  "enrollments": [{
    "key": {
      "keyId": "7007",
      "keyEpoch": "2",
      "algorithm": "1",
      "subject": "7",
      "publicKey": "$PUBLIC_KEY",
      "activeFrom": "0",
      "activeUntil": "1000000",
      "revoked": false
    },
    "accountId": "7",
    "spendCapabilityId": "41",
    "controlCapabilityId": "51",
    "factoryObserveCapabilityId": "54",
    "initialBalance": "100",
    "accountPredicate": {"type": "all", "predicates": []}
  }],
  "factoryControllerSubject": "7",
  "factoryControllerCapability": "53",
  "meterAllowance": {
    "incidences": "10000000",
    "turnBytes": "10000000",
    "memoryTouches": "10000000",
    "witnessBytes": "10000000",
    "proofWork": "10000000",
    "storageBytes": "10000000",
    "networkBytes": "10000000",
    "sideEffectCount": "10000000",
    "feeDebit": "10000000",
    "leaseByteBlocks": "10000000"
  }
}
EOF

"$MINI" bootstrap --host "$HOST" --config "$EVIDENCE/operator.json" \
  --source "$EVIDENCE/genesis.json" --dir "$EVIDENCE/deployment" \
  >"$EVIDENCE/bootstrap.stdout"
CONFIG="$EVIDENCE/deployment/pinned-config.json"

cat >"$EVIDENCE/birth-intent.json" <<EOF
{
  "subject": "7",
  "nonce": "22000",
  "birth": {
    "genesis": $(cat "$EVIDENCE/genesis.json"),
    "template": {"issuer": "5", "ownerBudget": "100000", "lifetime": "10000"},
    "creator": "7",
    "nonce": "22000",
    "resources": [{
      "kind": "object",
      "storage": "content",
      "target": "600",
      "owner": "7",
      "ownerCapability": "61",
      "controlCapability": "62",
      "predicate": {"type": "all", "predicates": []}
    }],
    "sourceCapabilities": ["41"],
    "funding": [],
    "feePayer": "7"
  },
  "grants": [
    {"kind": "object", "target": "10", "capability": "54"},
    {"kind": "account", "target": "7", "capability": "41"}
  ]
}
EOF

"$MINI" submit --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/birth-intent.json" --intent-kind birth-intent \
  --key "$EVIDENCE/alice.key" --dir "$EVIDENCE/birth-attempt" \
  >"$EVIDENCE/birth.stdout"
jq -e '.type == "confirmed" and .confirmation == "installed"' \
  "$EVIDENCE/birth-attempt/outcome.json" >/dev/null

cat >"$EVIDENCE/query-before.json" <<'EOF'
{
  "subject": "7",
  "nonce": "30001",
  "purpose": {"type": "query", "kind": "object", "target": "600", "view": "resource"},
  "grants": [{"kind": "object", "target": "600", "capability": "61"}]
}
EOF
"$MINI" query --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/query-before.json" --key "$EVIDENCE/alice.key" --view resource \
  --dir "$EVIDENCE/query-before" >"$EVIDENCE/query-before.stdout"
TARGET_ROOT=$(jq -er '.page.root' "$EVIDENCE/query-before/view.json")
AUTHORITY_ROOT=$(jq -er '.signing[0].authorityRoot' "$EVIDENCE/query-before/challenge.json")
jq -e '.page.entries == []' "$EVIDENCE/query-before/view.json" >/dev/null

cat >"$EVIDENCE/content-intent.json" <<EOF
{
  "subject": "7",
  "nonce": "30002",
  "purpose": {
    "type": "prepare",
    "draft": {
      "type": "invoke",
      "command": {
        "subject": "7",
        "expectedAuthorityRoot": "$AUTHORITY_ROOT",
        "nonce": "30003",
        "targets": [{
          "kind": "object",
          "target": "600",
          "capability": "61",
          "observeCapability": null,
          "schemaVersion": "1",
          "expectedTargetRoot": "$TARGET_ROOT",
          "payload": {
            "type": "content",
            "actions": [{
              "type": "createDocument",
              "rootElement": "1001",
              "schema": "1",
              "body": {"type": "container", "children": []}
            }]
          }
        }]
      }
    }
  },
  "grants": [{"kind": "object", "target": "600", "capability": "61"}]
}
EOF

printf '%s\n' "$HOST" >"$EVIDENCE/real-host-path"
cat >"$EVIDENCE/drop-first-submit.sh" <<'EOF'
#!/bin/sh
set -eu
SELF=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
REAL_HOST=$(cat "$SELF/real-host-path")
if [ "$2" = submit ] && mkdir "$SELF/submit-output-dropped.once" 2>/dev/null; then
  exec "$REAL_HOST" "$1" "$2" "$3" "$SELF/nonexistent-output-parent/outcome.bin"
fi
exec "$REAL_HOST" "$@"
EOF
chmod 755 "$EVIDENCE/drop-first-submit.sh"

if "$MINI" submit --host "$EVIDENCE/drop-first-submit.sh" --config "$CONFIG" \
  --intent "$EVIDENCE/content-intent.json" --key "$EVIDENCE/alice.key" \
  --dir "$EVIDENCE/content-attempt" >"$EVIDENCE/content-lost.stdout" \
  2>"$EVIDENCE/content-lost.stderr"; then
  echo "expected first content submission to lose its outcome" >&2
  exit 1
fi
test -f "$EVIDENCE/content-attempt/call.bin"
test ! -e "$EVIDENCE/content-attempt/outcome.bin"
test ! -e "$EVIDENCE/content-attempt/outcome.json"

CALL_HASH_BEFORE=$(shasum -a 256 "$EVIDENCE/content-attempt/call.bin" | awk '{print $1}')
"$MINI" retry --attempt "$EVIDENCE/content-attempt" --mode submit \
  >"$EVIDENCE/retry-submit.stdout"
"$MINI" retry --attempt "$EVIDENCE/content-attempt" --mode lookup \
  >"$EVIDENCE/retry-lookup.stdout"
CALL_HASH_AFTER=$(shasum -a 256 "$EVIDENCE/content-attempt/call.bin" | awk '{print $1}')
test "$CALL_HASH_BEFORE" = "$CALL_HASH_AFTER"
jq -e '.type == "confirmed" and .confirmation == "replayed"' \
  "$EVIDENCE/content-attempt/retry-0001.json" >/dev/null
jq -e '.type == "confirmed" and .confirmation == "replayed"' \
  "$EVIDENCE/content-attempt/retry-0002.json" >/dev/null
for field in transactionId eventId acceptedCount imageBoundary; do
  test "$(jq -r ".$field" "$EVIDENCE/content-attempt/retry-0001.json")" = \
    "$(jq -r ".$field" "$EVIDENCE/content-attempt/retry-0002.json")"
done

cat >"$EVIDENCE/query-after.json" <<'EOF'
{
  "subject": "7",
  "nonce": "30004",
  "purpose": {"type": "query", "kind": "object", "target": "600", "view": "resource"},
  "grants": [{"kind": "object", "target": "600", "capability": "61"}]
}
EOF
"$MINI" query --host "$HOST" --config "$CONFIG" \
  --intent "$EVIDENCE/query-after.json" --key "$EVIDENCE/alice.key" --view resource \
  --dir "$EVIDENCE/query-after" >"$EVIDENCE/query-after.stdout"
jq -e '[.page.entries[].type] | sort == ["document", "element"]' \
  "$EVIDENCE/query-after/view.json" >/dev/null
test "$TARGET_ROOT" != "$(jq -r '.page.root' "$EVIDENCE/query-after/view.json")"

cat >"$EVIDENCE/acceptance.json" <<EOF
{
  "status": "pass",
  "host": "$HOST",
  "semantics": "$SEMANTICS",
  "contentCallSha256": "$CALL_HASH_AFTER",
  "birthTransaction": $(jq '.transactionId' "$EVIDENCE/birth-attempt/outcome.json"),
  "contentTransaction": $(jq '.transactionId' "$EVIDENCE/content-attempt/retry-0001.json"),
  "lostOutcomeRecoveredByExactRetry": true
}
EOF
cat "$EVIDENCE/acceptance.json"
