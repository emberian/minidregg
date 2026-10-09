#!/bin/sh
# Fresh, private one-sponsor Mini image for independent participant enrollment.
# Run on the same Linux host as the native Host/Store/verifier. No prior Store,
# resource allocation, participant identity, or genesis image is copied.
set -eu
umask 077

if [ "$#" -ne 5 ] && [ "$#" -ne 6 ]; then
  echo "usage: $0 HOST MINI STORE VERIFIER NEW_PRIVATE_DIRECTORY [PUBLIC_SOCKET]" >&2
  exit 2
fi
HOST=$1 MINI=$2 STORE=$3 VERIFIER=$4 ROOT=$5
# The public socket defaults to ROOT/public/mini.sock; a caller whose ROOT is
# deep (the journey's world) names a short one (journey.d/lib/shortdir.sh).
SOCKET=${6:-}
# Each Store is an independent deployment: its domain and its sponsor subject
# number are operator choices. Two Stores that exchange selected releases need
# distinct domains, and the recipient enrolls the source owner under its home
# subject number, so the two sponsor subjects must also differ.
DOMAIN=${NEWPARTICIPANT_DOMAIN:-8501}
SUBJECT=${NEWPARTICIPANT_SPONSOR_SUBJECT:-7}
for value in "$DOMAIN" "$SUBJECT"; do
  case $value in ""|0?*|*[!0-9]*) echo "domain and sponsor subject must be canonical decimal" >&2; exit 2;; esac
done
# The template owner budget (every owner capability's maxCost). A birth intent's
# observation costs its byte length, so a fixture that births a Nock program
# (J-NOCK-2b, ~566 KB) raises it; the default is unchanged.
OWNER_BUDGET=${NEWPARTICIPANT_OWNER_BUDGET:-100000}
SPONSOR_BALANCE=${NEWPARTICIPANT_SPONSOR_BALANCE:-100000}
case "$SPONSOR_BALANCE" in ''|*[!0-9]*) echo 'NEWPARTICIPANT_SPONSOR_BALANCE must be decimal' >&2; exit 2;; esac
# Compiled-in evaluators this Store's operator disables (space-separated registry
# names, e.g. "nock"; K-EVAL). Written into the genesis params; default none.
DISABLED_EVALUATORS=${NEWPARTICIPANT_DISABLED_EVALUATORS:-}
case "$OWNER_BUDGET" in ''|*[!0-9]*) echo 'NEWPARTICIPANT_OWNER_BUDGET must be decimal' >&2; exit 2;; esac
for executable in "$HOST" "$MINI" "$STORE" "$VERIFIER"; do
  case "$executable" in /*) ;; *) echo "binary path must be absolute: $executable" >&2; exit 2;; esac
  [ -x "$executable" ] || { echo "not executable: $executable" >&2; exit 2; }
done
command -v jq >/dev/null 2>&1 || { echo 'jq is required' >&2; exit 2; }
HERE=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
command -v sha256sum >/dev/null 2>&1 || { echo 'sha256sum is required' >&2; exit 2; }
case "$ROOT" in /*) ;; *) echo 'fixture path must be absolute' >&2; exit 2;; esac
[ ! -e "$ROOT" ] && [ ! -L "$ROOT" ] || { echo 'fixture already exists' >&2; exit 2; }
case "${SOCKET:-/}" in /*) ;; *) echo 'public socket path must be absolute' >&2; exit 2;; esac
. "$HERE/journey.d/lib/shortdir.sh"
journey_check_sun_len "${SOCKET:-$ROOT/public/mini.sock}" "the public socket of $ROOT"
mkdir -m 700 "$ROOT"
ROOT=$(CDPATH='' cd -- "$ROOT" && pwd)
mkdir -m 700 "$ROOT/public" "$ROOT/namespace" "$ROOT/attempts"
SOCKET=${SOCKET:-$ROOT/public/mini.sock}

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
            activeFrom: "0", activeUntil: "1000000", nextKeyDigest: null},
      accountId: $s, spendCapabilityId: c(2), controlCapabilityId: c(3),
      factoryObserveCapabilityId: c(4), initialBalance: "0",
      accountPredicate: {type: "all", predicates: []}}]' >"$ROOT/observer-enrollment.json"
  jq -n --arg s "$OBSERVER" '[{subject: $s, capability: (($s|tonumber) * 100 + 1 | tostring)}]' \
    >"$ROOT/observer-ticker.json"
  EXTRA_GENESIS_ENROLLMENTS=$ROOT/observer-enrollment.json
  EXTRA_CLOCK_TICKERS=$ROOT/observer-ticker.json
  export EXTRA_GENESIS_ENROLLMENTS EXTRA_CLOCK_TICKERS
fi
# The PAY observer (PAY.md §3.5): an enrolled subject whose genesis capability on the pay
# cell (verb observePayment, the pay law `eq request/subject 30`) is the only authority that
# can report a payment. On a deployment its key is /etc/mini/pay/observer.key (0600, mini).
mkdir -m 700 "$ROOT/pay"
"$MINI" keygen --secret "$ROOT/pay/observer.key" --public "$ROOT/pay/observer.pub" \
  >"$ROOT/pay/observer-keygen.json"
SPONSOR_PUBLIC=$(od -An -tx1 -v "$ROOT/sponsor.pub" | tr -d ' \n')
NEWCOMER_PUBLIC=$(od -An -tx1 -v "$ROOT/newcomer.pub" | tr -d ' \n')
OBSERVER_PUBLIC=$(od -An -tx1 -v "$ROOT/pay/observer.pub" | tr -d ' \n')
[ "$SPONSOR_PUBLIC" != "$NEWCOMER_PUBLIC" ] || { echo 'keys unexpectedly equal' >&2; exit 1; }

# The observer enrolls at genesis like any subject and is named as the pay
# observer (genesis.sh GENESIS_PAY_OBSERVER); 4031/4032 are the pay controller's
# and the self-enrollment capabilities.
cat >"$ROOT/pay/genesis-enrollments.json" <<EOF
[{"key":{"keyId":"7030","keyEpoch":"2","algorithm":"1","subject":"30",
  "publicKey":"$OBSERVER_PUBLIC","activeFrom":"0","activeUntil":"1000000","nextKeyDigest":null},
  "accountId":"130","spendCapabilityId":"1030","controlCapabilityId":"2030",
  "factoryObserveCapabilityId":"3030","initialBalance":"100",
  "accountPredicate":{"type":"all","predicates":[]}}]
EOF
# A caller's own EXTRA_GENESIS_ENROLLMENTS (hosted agent-grain subjects) is kept;
# the observer is appended to it.
if [ -n "${EXTRA_GENESIS_ENROLLMENTS:-}" ]; then
  jq -s '.[0] + .[1]' "$EXTRA_GENESIS_ENROLLMENTS" "$ROOT/pay/genesis-enrollments.json" \
    >"$ROOT/pay/genesis-enrollments-all.json"
else
  cp "$ROOT/pay/genesis-enrollments.json" "$ROOT/pay/genesis-enrollments-all.json"
fi
cat >"$ROOT/pay/genesis-observer.json" <<EOF
{"subject":"30","capability":"4030","controlCapability":"4031","enrolCapability":"4032"}
EOF
# The one genesis template (genesis.sh) from the example params, with this
# Store's domain and sponsor subject; it honours EXTRA_GENESIS_ENROLLMENTS and
# MINI_TAIL_BOUND (the tail bound L, default the example's 256 = 4 x 64).
jq --argjson domain "$DOMAIN" --argjson subject "$SUBJECT" --argjson budget "$OWNER_BUDGET" --argjson balance "$SPONSOR_BALANCE" \
  --arg disabled "$DISABLED_EVALUATORS" --argjson tail "${MINI_TAIL_BOUND:-256}" \
  --arg objective "${OBJECTIVE_INVOCATION_POLICY:-}" \
  '.domain = $domain | .sponsor.subject = $subject | .sponsor.initialBalance = $balance | .ownerBudget = $budget | .tailBound = $tail
   | ($disabled | split(" ") | map(select(length > 0))) as $off
   | if ($off | length) > 0 then .disabledEvaluators = $off else . end
   | if $objective != "" then .objectiveInvocation = $objective else . end' \
  "$HERE/genesis-params.example.json" >"$ROOT/genesis-params.json"
sh "$HERE/../../deploy/candidate/params.sh" fill-genesis "$ROOT/genesis-params.json"
EXTRA_GENESIS_ENROLLMENTS="$ROOT/pay/genesis-enrollments-all.json" \
GENESIS_PAY_OBSERVER="$ROOT/pay/genesis-observer.json" \
  sh "$HERE/genesis.sh" "$ROOT/genesis-params.json" "$SPONSOR_PUBLIC" "$CLOCK_PUBLIC" \
  "$HOST" "$STORE" "$VERIFIER" "$ROOT"

"$MINI" bootstrap --host "$HOST" --config "$ROOT/operator.json" \
  --source "$ROOT/genesis.json" --dir "$ROOT/deployment" \
  >"$ROOT/bootstrap.stdout"
CONFIG="$ROOT/deployment/pinned-config.json"
[ -s "$CONFIG" ] || { echo 'bootstrap produced no pinned config' >&2; exit 1; }

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
  --namespace-root "$ROOT/namespace" --dir "$ROOT/sponsor" --no-prerotation \
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

"$MINI" workspace --action init --host "$HOST" --config "$CONFIG" \
  --socket "$SOCKET" --key "$ROOT/pay/observer.key" --subject 30 --no-prerotation \
  --dir "$ROOT/pay/observer" >"$ROOT/pay/observer-workspace.stdout"
jq -e '.payObserver == {"subject":"30","capability":"4030","controlCapability":"4031","enrolCapability":"4032"}' \
  "$ROOT/genesis.json" >/dev/null
[ -s "$ROOT/deployment/pay-ledger-genesis.json" ] || { echo 'bootstrap retained no genesis pay ledger' >&2; exit 1; }

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
 "payObserver":{"subject":"30","capability":"4030","key":"$ROOT/pay/observer.key",
   "workspace":"$ROOT/pay/observer"},
 "status":"fresh-genesis-and-sponsor-workspace; no newcomer admitted"}
EOF
printf '%s\n' "$ROOT/handoff.json"
