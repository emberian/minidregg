#!/bin/sh
# Fresh, private one-sponsor Mini image for independent participant enrollment.
# Run on the same Linux host as the native Host/Store/verifier. No prior Store,
# resource allocation, participant identity, or genesis image is copied.
set -eu
umask 077

if [ "$#" -ne 5 ]; then
  echo "usage: $0 HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 ROOT=$5
# Each Store is an independent deployment: its domain and its sponsor subject
# number are operator choices. Two Stores that exchange selected releases need
# distinct domains, and the recipient enrolls the source owner under its home
# subject number, so the two sponsor subjects must also differ.
DOMAIN=${NEWPARTICIPANT_DOMAIN:-8501}
SUBJECT=${NEWPARTICIPANT_SPONSOR_SUBJECT:-7}
for value in "$DOMAIN" "$SUBJECT"; do
  case $value in ""|0?*|*[!0-9]*) echo "domain and sponsor subject must be canonical decimal" >&2; exit 2;; esac
done
for executable in "$HOST" "$MINI" "$STORE" "$VERIFIER"; do
  case "$executable" in /*) ;; *) echo "binary path must be absolute: $executable" >&2; exit 2;; esac
  [ -x "$executable" ] || { echo "not executable: $executable" >&2; exit 2; }
done
command -v jq >/dev/null 2>&1 || { echo 'jq is required' >&2; exit 2; }
command -v sha256sum >/dev/null 2>&1 || { echo 'sha256sum is required' >&2; exit 2; }
case "$ROOT" in /*) ;; *) echo 'fixture path must be absolute' >&2; exit 2;; esac
[ ! -e "$ROOT" ] && [ ! -L "$ROOT" ] || { echo 'fixture already exists' >&2; exit 2; }
mkdir -m 700 "$ROOT"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)
mkdir -m 700 "$ROOT/public" "$ROOT/namespace" "$ROOT/attempts"

"$MINI" keygen --secret "$ROOT/sponsor.key" --public "$ROOT/sponsor.pub" \
  >"$ROOT/sponsor-keygen.json"
"$MINI" keygen --secret "$ROOT/newcomer.key" --public "$ROOT/newcomer.pub" \
  >"$ROOT/newcomer-keygen.json"
SPONSOR_PUBLIC=$(od -An -tx1 -v "$ROOT/sponsor.pub" | tr -d ' \n')
NEWCOMER_PUBLIC=$(od -An -tx1 -v "$ROOT/newcomer.pub" | tr -d ' \n')
[ "$SPONSOR_PUBLIC" != "$NEWCOMER_PUBLIC" ] || { echo 'keys unexpectedly equal' >&2; exit 1; }

cat >"$ROOT/operator.json" <<EOF
{"domain":$DOMAIN,"federation":9,"factoryId":10,"resourceBookId":11,
 "authorityCatalogueId":12,"issuer":5,"ownerBudget":100000,"lifetime":10000,
 "tariffBase":3,"tariffPerBirth":2,"tariffPerGrant":1,
 "tariffPerInitialPayloadByte":0,"collector":99,"asset":0,
 "genesisHeight":10,"expectedSeed":0,"storageBinary":"$STORE",
 "storageRoot":"$ROOT/store","signatureBinary":"$VERIFIER"}
EOF
"$HOST" "$ROOT/operator.json" profile >"$ROOT/profile.json"
SEMANTICS=$(jq -er '.semantics | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' "$ROOT/profile.json")

cat >"$ROOT/genesis.json" <<EOF
{"domain":"$DOMAIN","factoryId":"10","resourceBookId":"11",
 "authorityCatalogueId":"12","federation":"9","tariffBase":"3",
 "tariffPerBirth":"2","tariffPerGrant":"1","tariffPerInitialPayloadByte":"0",
 "collector":"99","asset":"0","expectedSemantics":"$SEMANTICS",
 "issuerEpoch":"2","genesisHeight":"10",
 "factoryPredicate":{"type":"all","predicates":[]},
 "enrollments":[{"key":{"keyId":"7007","keyEpoch":"2","algorithm":"1",
   "subject":"$SUBJECT","publicKey":"$SPONSOR_PUBLIC","activeFrom":"0",
   "activeUntil":"1000000","revoked":false},
   "accountId":"7","spendCapabilityId":"41","controlCapabilityId":"51",
   "factoryObserveCapabilityId":"54","initialBalance":"100000",
   "accountPredicate":{"type":"all","predicates":[]}}],
 "factoryControllerSubject":"$SUBJECT","factoryControllerCapability":"53",
 "meterAllowance":{"incidences":"10000000","turnBytes":"10000000",
   "memoryTouches":"10000000","witnessBytes":"10000000",
   "proofWork":"10000000","storageBytes":"10000000",
   "networkBytes":"10000000","sideEffectCount":"10000000",
   "feeDebit":"10000000","leaseByteBlocks":"10000000"}}
EOF

# A hosted operator may enroll its own agent-grain subjects at genesis. The
# only AgentGrain birth route on the current Host is the historical birth
# intent, which Mini admits only against the genesis image, so a hosted
# grain's owner and worker subjects must exist before any other event.
if [ -n "${EXTRA_GENESIS_ENROLLMENTS:-}" ]; then
  case "$EXTRA_GENESIS_ENROLLMENTS" in /*) ;; *) echo 'EXTRA_GENESIS_ENROLLMENTS must be absolute' >&2; exit 2;; esac
  jq -e 'type == "array" and length > 0 and length <= 8 and
    all(.[]; .key.subject != "7" and .accountId != "7")' \
    "$EXTRA_GENESIS_ENROLLMENTS" >/dev/null ||
    { echo 'extra genesis enrollments are invalid' >&2; exit 2; }
  jq --slurpfile extra "$EXTRA_GENESIS_ENROLLMENTS" '.enrollments += $extra[0]' \
    "$ROOT/genesis.json" >"$ROOT/genesis-extended.json"
  mv "$ROOT/genesis-extended.json" "$ROOT/genesis.json"
fi

"$MINI" bootstrap --host "$HOST" --config "$ROOT/operator.json" \
  --source "$ROOT/genesis.json" --dir "$ROOT/deployment" \
  >"$ROOT/bootstrap.stdout"
CONFIG="$ROOT/deployment/pinned-config.json"
[ -s "$CONFIG" ] || { echo 'bootstrap produced no pinned config' >&2; exit 1; }

cat >"$ROOT/sponsor-birth-context.json" <<EOF
{"type":"minidregg-participant-birth-context-v1",
 "genesis":$(cat "$ROOT/genesis.json"),
 "template":{"issuer":"5","ownerBudget":"100000","lifetime":"10000"},
 "sourceCapabilities":["41"],"funding":[],"feePayer":"7",
 "grants":[{"kind":"object","target":"10","capability":"54"},
   {"kind":"account","target":"7","capability":"41"}]}
EOF

SOCKET="$ROOT/public/mini.sock"
nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
  >"$ROOT/public/serve.log" 2>&1 </dev/null &
SERVER_PID=$!
printf '%s\n' "$SERVER_PID" >"$ROOT/public/server.pid"
ready=0
attempt=0
while [ "$attempt" -lt 1200 ]; do
  if [ -S "$SOCKET" ]; then ready=1; break; fi
  kill -0 "$SERVER_PID" 2>/dev/null || { echo 'Mini server exited' >&2; exit 1; }
  attempt=$((attempt + 1))
  sleep 0.1
done
[ "$ready" -eq 1 ] || {
  echo 'Mini public socket did not appear within 120 seconds' >&2
  tail -40 "$ROOT/public/serve.log" >&2
  exit 1
}

"$MINI" workspace --action init --host "$HOST" --config "$CONFIG" \
  --socket "$SOCKET" --key "$ROOT/sponsor.key" --subject "$SUBJECT" \
  --birth-context "$ROOT/sponsor-birth-context.json" \
  --namespace-root "$ROOT/namespace" --dir "$ROOT/sponsor" \
  >"$ROOT/sponsor-workspace.stdout"
"$MINI" workspace --action import --dir "$ROOT/sponsor" --name factory \
  --kind object --target 10 --observe-capability 54 --control-capability 53 \
  >"$ROOT/factory-import.stdout"
"$MINI" workspace --action read --dir "$ROOT/sponsor" --name factory \
  >"$ROOT/factory-read.json"
jq -e '.type == "minidregg-participant-reference-v1" and .target == "10" and
  .observeCapability == "54" and .controlCapability == "53"' \
  "$ROOT/sponsor/refs/factory.json" >/dev/null

sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$CONFIG" \
  "$ROOT/genesis.json" "$ROOT/sponsor/refs/factory.json" \
  >"$ROOT/source-binaries-and-fixture.sha256"
cat >"$ROOT/handoff.json" <<EOF
{"type":"minidregg-newparticipant-fixture-v1",
 "root":"$ROOT","host":"$HOST","mini":"$MINI",
 "config":"$CONFIG","publicSocket":"$SOCKET","sponsorWorkspace":"$ROOT/sponsor",
 "factoryRef":"factory","newKey":"$ROOT/newcomer.key",
 "newPublicKey":"$NEWCOMER_PUBLIC","namespaceRoot":"$ROOT/namespace",
 "enrollmentAttempt":"$ROOT/attempts/newcomer",
 "domain":"$DOMAIN","sponsorSubject":"$SUBJECT",
 "status":"fresh-genesis-and-sponsor-workspace; no newcomer admitted"}
EOF
printf '%s\n' "$ROOT/handoff.json"
