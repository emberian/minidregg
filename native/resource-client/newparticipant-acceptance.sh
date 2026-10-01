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
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
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
"$MINI" keygen --secret "$ROOT/clock.key" --public "$ROOT/clock.pub" \
  >"$ROOT/clock-keygen.json"
CLOCK_PUBLIC=$(od -An -tx1 -v "$ROOT/clock.pub" | tr -d ' \n')

# NEWPARTICIPANT_CLOCK_OBSERVER=SUBJECT adds a second clock ticker (a chain observer
# that asserts chain time) to genesis: enrolled with its own key and account, with a
# C_tick of its own (SUBJECT*100+1), and a clock workspace at ROOT/observer.
OBSERVER=${NEWPARTICIPANT_CLOCK_OBSERVER:-}
if [ -n "$OBSERVER" ]; then
  case $OBSERVER in 0?*|*[!0-9]*) echo "observer subject must be canonical decimal" >&2; exit 2;; esac
  [ -z "${EXTRA_GENESIS_ENROLLMENTS:-}" ] && [ -z "${EXTRA_CLOCK_TICKERS:-}" ] ||
    { echo "NEWPARTICIPANT_CLOCK_OBSERVER composes with no other extra genesis input" >&2; exit 2; }
  "$MINI" keygen --secret "$ROOT/observer.key" --public "$ROOT/observer.pub" \
    >"$ROOT/observer-keygen.json"
  OBSERVER_PUBLIC=$(od -An -tx1 -v "$ROOT/observer.pub" | tr -d ' \n')
  jq -n --arg s "$OBSERVER" --arg public "$OBSERVER_PUBLIC" '
    ($s|tonumber) as $n | def c(k): ($n * 100 + k | tostring);
    [{key: {keyId: c(0), keyEpoch: "2", algorithm: "1", subject: $s, publicKey: $public,
            activeFrom: "0", activeUntil: "1000000"},
      accountId: $s, spendCapabilityId: c(2), controlCapabilityId: c(3),
      factoryObserveCapabilityId: c(4), initialBalance: "0",
      accountPredicate: {type: "all", predicates: []}}]' >"$ROOT/observer-enrollment.json"
  jq -n --arg s "$OBSERVER" '[{subject: $s, capability: (($s|tonumber) * 100 + 1 | tostring)}]' \
    >"$ROOT/observer-ticker.json"
  EXTRA_GENESIS_ENROLLMENTS=$ROOT/observer-enrollment.json
  EXTRA_CLOCK_TICKERS=$ROOT/observer-ticker.json
  export EXTRA_GENESIS_ENROLLMENTS EXTRA_CLOCK_TICKERS
fi
SPONSOR_PUBLIC=$(od -An -tx1 -v "$ROOT/sponsor.pub" | tr -d ' \n')
NEWCOMER_PUBLIC=$(od -An -tx1 -v "$ROOT/newcomer.pub" | tr -d ' \n')
[ "$SPONSOR_PUBLIC" != "$NEWCOMER_PUBLIC" ] || { echo 'keys unexpectedly equal' >&2; exit 1; }

# The one genesis template (genesis.sh) from the example params, with this
# Store's domain and sponsor subject; it honours EXTRA_GENESIS_ENROLLMENTS.
jq --argjson domain "$DOMAIN" --argjson subject "$SUBJECT" \
  '.domain = $domain | .sponsor.subject = $subject' \
  "$HERE/genesis-params.example.json" >"$ROOT/genesis-params.json"
sh "$HERE/genesis.sh" "$ROOT/genesis-params.json" "$SPONSOR_PUBLIC" "$CLOCK_PUBLIC" \
  "$HOST" "$STORE" "$VERIFIER" "$ROOT"

"$MINI" bootstrap --host "$HOST" --config "$ROOT/operator.json" \
  --source "$ROOT/genesis.json" --dir "$ROOT/deployment" \
  >"$ROOT/bootstrap.stdout"
CONFIG="$ROOT/deployment/pinned-config.json"
[ -s "$CONFIG" ] || { echo 'bootstrap produced no pinned config' >&2; exit 1; }

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
# The clock subject's own workspace (the ticker's; not the sponsor's).
"$MINI" clock --action init --dir "$ROOT/clock" --host "$HOST" --config "$CONFIG" \
  --socket "$SOCKET" --key "$ROOT/clock.key" \
  --subject "$(jq -r .clock.subject "$ROOT/genesis-params.json")" \
  --capability "$(jq -r .clock.tickCapabilityId "$ROOT/genesis-params.json")" \
  >"$ROOT/clock-workspace.stdout"
if [ -n "$OBSERVER" ]; then
  "$MINI" clock --action init --dir "$ROOT/observer" --host "$HOST" --config "$CONFIG" \
    --socket "$SOCKET" --key "$ROOT/observer.key" --subject "$OBSERVER" \
    --capability "$((OBSERVER * 100 + 1))" >"$ROOT/observer-workspace.stdout"
fi
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
 "factoryRef":"factory","newKey":"$ROOT/newcomer.key","clockWorkspace":"$ROOT/clock",
 "newPublicKey":"$NEWCOMER_PUBLIC","namespaceRoot":"$ROOT/namespace",
 "enrollmentAttempt":"$ROOT/attempts/newcomer",
 "domain":"$DOMAIN","sponsorSubject":"$SUBJECT",
 "status":"fresh-genesis-and-sponsor-workspace; no newcomer admitted"}
EOF
printf '%s\n' "$ROOT/handoff.json"
