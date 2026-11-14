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
# The template owner budget (every owner capability's perRequestBytes). A birth intent's
# observation costs its byte length, so a fixture that births a Nock program
# (J-NOCK-2b, ~566 KB) raises it; the default is unchanged.
OWNER_BUDGET=${NEWPARTICIPANT_OWNER_BUDGET:-100000}
SPONSOR_BALANCE=${NEWPARTICIPANT_SPONSOR_BALANCE:-100000}
# Optional finite physical meter allocation for long-running fixtures. Keep all
# admission checks; a larger workload needs an explicitly funded fresh genesis.
METER_ALLOWANCE=${NEWPARTICIPANT_METER_ALLOWANCE:-}
case "$METER_ALLOWANCE" in 0?*|*[!0-9]*) echo 'NEWPARTICIPANT_METER_ALLOWANCE must be canonical decimal' >&2; exit 2;; esac
case "$SPONSOR_BALANCE" in ''|*[!0-9]*) echo 'NEWPARTICIPANT_SPONSOR_BALANCE must be decimal' >&2; exit 2;; esac
# Compiled-in evaluators this Store's operator disables (space-separated registry
# names, e.g. "nock"; K-EVAL). Written into the genesis params; default none.
DISABLED_EVALUATORS=${NEWPARTICIPANT_DISABLED_EVALUATORS:-}
# A world that will host applications retains the common grain platform
# configuration and generates its completion custodian before bootstrap.
GRAIN_PLATFORM=${NEWPARTICIPANT_GRAIN_PLATFORM:-0}
case "$GRAIN_PLATFORM" in 0|1) ;; *) echo 'NEWPARTICIPANT_GRAIN_PLATFORM must be 0 or 1' >&2; exit 2;; esac
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
SOCKET=${SOCKET:-$ROOT/public/mini.sock}

# ---- the world template --------------------------------------------------------------------
# NEWPARTICIPANT_TEMPLATE_DIR, if set, holds one tar per VARIANT of this fixture: the four binaries'
# digests and every knob above (domain, sponsor, budgets, evaluators, tail, the Objective policy, the
# clock observer, the extra genesis inputs by content, the serve mode, this script and genesis.sh).
# The first caller of a variant builds the world below and leaves it there; every later caller
# restores it: the files copied, the template's absolute paths rewritten to this ROOT and SOCKET,
# `mini serve` started (about 2 s instead of genesis, bootstrap and three workspace inits). A
# restored world IS the world the knobs describe (same genesis, same keys, same records), so nothing
# a caller asserts changes; what it shares with other callers of the same candidate is test keys.
# The Store (sqlite files and the head anchor) holds no path; every text file naming one is rewritten.
# ON BY DEFAULT (ember 2026-10-27: keep snapshots and fast-forward them; avoid replays): unset means
# $TMPDIR/minidregg-world-templates-UID (the variant digests the binaries, so candidates never share a
# template); NEWPARTICIPANT_TEMPLATE_DIR="" (journey-runner's JOURNEY_WORLD_TEMPLATES=0) builds fresh,
# the control for the published before/after number.
TEMPLATE_DIR=${NEWPARTICIPANT_TEMPLATE_DIR-${TMPDIR:-/tmp}/minidregg-world-templates-$(id -u)}
TEMPLATE_VARIANT= TEMPLATE_TAR= TEMPLATE_META=
variant_digest() {
  # contents only (`sha256sum -` names no path): a caller's spec file lives under its own run root
  { for b in "$HOST" "$MINI" "$STORE" "$VERIFIER" "$HERE/genesis-params.example.json" "$HERE/genesis.sh" "$0"; do sha256sum <"$b"; done
    printf 'domain=%s subject=%s budget=%s balance=%s disabled=%s tail=%s objective=%s observer=%s serve=%s now=%s step=%s socket-in-root=%s grain-platform=%s\n' \
      "$DOMAIN" "$SUBJECT" "$OWNER_BUDGET" "$SPONSOR_BALANCE" "$DISABLED_EVALUATORS" "${MINI_TAIL_BOUND:-256}" \
      "${OBJECTIVE_INVOCATION_POLICY:-}" "${NEWPARTICIPANT_CLOCK_OBSERVER:-}" "${NEWPARTICIPANT_SERVE:-serve}" \
      "${GENESIS_NOW:-}" "${MAX_STEP_SECONDS:-}" "$(case $SOCKET in "$ROOT"/*) echo yes;; *) echo no;; esac)" "$GRAIN_PLATFORM"
    printf 'meterAllowance=%s\n' "$METER_ALLOWANCE"
    for f in "${EXTRA_GENESIS_ENROLLMENTS:-}" "${NEWPARTICIPANT_EXTRA_SUBJECTS:-}" "${EXTRA_CLOCK_TICKERS:-}" "${NEWPARTICIPANT_PROVIDER_SERVICES:-}"; do
      [ -n "$f" ] && { printf '%s ' "$(basename "$f")"; sha256sum <"$f"; }
    done
  } | sha256sum | cut -c1-32
}
start_serve() {
  SERVE=${NEWPARTICIPANT_SERVE:-serve}
  case $SERVE in serve|serve-operator) ;; *) echo 'NEWPARTICIPANT_SERVE must be serve or serve-operator' >&2; exit 2;; esac
  nohup "$MINI" "$SERVE" --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
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
}
stop_serve() {  # the fixture's own server, by its PID file, for the template capture
  pid=$(cat "$ROOT/public/server.pid")
  kill -TERM "$pid" 2>/dev/null || true
  attempt=0
  while kill -0 "$pid" 2>/dev/null; do
    attempt=$((attempt + 1)); [ "$attempt" -lt 600 ] || { echo 'Mini server did not stop for the template capture' >&2; exit 1; }
    sleep 0.1
  done
  rm -f "$SOCKET"
}
fixture_digests() {
  sha256sum "$HOST" "$MINI" "$STORE" "$VERIFIER" "$CONFIG" \
    "$ROOT/genesis.json" "$ROOT/sponsor/refs/factory.json" \
    >"$ROOT/source-binaries-and-fixture.sha256"
}
restore_template() {  # the template's files into ROOT, its paths rewritten, the service up
  t_root=$(jq -r .root "$TEMPLATE_META"); t_socket=$(jq -r .socket "$TEMPLATE_META")
  # The template's binaries by path: the variant is keyed by their CONTENT, so a later candidate with
  # byte-identical binaries restores a template that names the first candidate's directory, which a
  # sweep may have removed (hbox 2026-11-06: the restored pinned config's storageBinary named a swept
  # candidate and every Host read died `native helper closed its reply after 0 bytes`). Each is
  # rewritten to this caller's binary; a template recorded before the meta carried them is rebuilt.
  t_bins=""
  for pair in "host=$HOST" "mini=$MINI" "store=$STORE" "verifier=$VERIFIER"; do
    was=$(jq -r --arg k "${pair%%=*}" '.binaries[$k] // empty' "$TEMPLATE_META")
    [ -n "$was" ] || { echo "template $TEMPLATE_VARIANT predates its binary paths; rebuilding it" >&2; rm -f "$TEMPLATE_TAR" "$TEMPLATE_META"; return 1; }
    [ "$was" = "${pair#*=}" ] || t_bins="$t_bins -e s#$was#${pair#*=}#g"
  done
  tar -xf "$TEMPLATE_TAR" -C "$ROOT"
  # every text file that names the template's root, socket or binaries; the Store, the anchor, keys and
  # retained frames hold no path (grep finds none in them, and they are skipped by name anyway)
  grep -rlF -e "$t_root" -e "$t_socket" "$ROOT" 2>/dev/null | while IFS= read -r f; do
    case $f in *.sqlite3|*.sqlite3-*|*head-anchor*|*.bin|*.key|*.key.*|*.pub|*.frame) continue ;; esac
    sed -i -e "s#$t_socket#$SOCKET#g" -e "s#$t_root#$ROOT#g" $t_bins "$f"
  done
  [ -z "$t_bins" ] || grep -rlE '"(storageBinary|signatureBinary|host|mini)"' "$ROOT" --include=*.json 2>/dev/null | while IFS= read -r f; do
    sed -i $t_bins "$f"
  done
  rm -f "$ROOT/public/serve.log" "$ROOT/public/server.pid" "$ROOT/public/mini.config"
  CONFIG="$ROOT/deployment/pinned-config.json"
  [ -s "$CONFIG" ] || { echo "template at $TEMPLATE_TAR has no pinned config" >&2; exit 1; }
  jq -e --arg root "$ROOT/store" '.storageRoot == $root' "$CONFIG" >/dev/null || { echo 'template restore did not rewrite storageRoot' >&2; exit 1; }
  start_serve
  "$MINI" workspace --action read --dir "$ROOT/sponsor" --name factory >"$ROOT/factory-read.json"
  fixture_digests
  printf '%s\n' "restored from template $TEMPLATE_VARIANT ($TEMPLATE_TAR)" >"$ROOT/template-restored.txt"
  printf '%s\n' "$ROOT/handoff.json"
}
if [ -n "$TEMPLATE_DIR" ]; then
  case "$TEMPLATE_DIR" in /*) ;; *) echo 'NEWPARTICIPANT_TEMPLATE_DIR must be absolute' >&2; exit 2;; esac
  mkdir -p -m 700 "$TEMPLATE_DIR"
  TEMPLATE_VARIANT=$(variant_digest)
  TEMPLATE_TAR=$TEMPLATE_DIR/$TEMPLATE_VARIANT.tar
  TEMPLATE_META=$TEMPLATE_DIR/$TEMPLATE_VARIANT.json
  if [ -s "$TEMPLATE_TAR" ] && [ -s "$TEMPLATE_META" ] && restore_template; then
    exit 0
  fi
fi
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
# The PAY observer (docs/PAY.md §3.5): an enrolled subject whose genesis capability on the pay
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
# NEWPARTICIPANT_EXTRA_SUBJECTS, if set, is an absolute path to a JSON array of further genesis
# enrollments WITHOUT their public keys: this fixture makes each subject's key here, at
# ROOT/extra/SUBJECT.key (its public half beside it, `mini keygen`'s next key too), and fills
# `.key.publicKey` in. A caller that made its own keys passes EXTRA_GENESIS_ENROLLMENTS instead;
# the difference is that a world described this way is the same world every time (no per-run key
# in its genesis), so it has a template.
if [ -n "${NEWPARTICIPANT_EXTRA_SUBJECTS:-}" ]; then
  case "$NEWPARTICIPANT_EXTRA_SUBJECTS" in /*) ;; *) echo 'NEWPARTICIPANT_EXTRA_SUBJECTS must be absolute' >&2; exit 2;; esac
  jq -e 'type == "array" and length <= 8 and all(.[]; .key.subject | type == "string")' "$NEWPARTICIPANT_EXTRA_SUBJECTS" >/dev/null ||
    { echo 'NEWPARTICIPANT_EXTRA_SUBJECTS: an array of at most 8 enrollments, each with .key.subject' >&2; exit 2; }
  mkdir -m 700 "$ROOT/extra"
  : >"$ROOT/extra/public-keys.tsv"
  for s in $(jq -r '.[].key.subject' "$NEWPARTICIPANT_EXTRA_SUBJECTS"); do
    case $s in ""|0?*|*[!0-9]*) echo "extra subject must be canonical decimal: $s" >&2; exit 2;; esac
    "$MINI" keygen --secret "$ROOT/extra/$s.key" --public "$ROOT/extra/$s.pub" >"$ROOT/extra/$s-keygen.json"
    printf '%s\t%s\n' "$s" "$(od -An -tx1 -v "$ROOT/extra/$s.pub" | tr -d ' \n')" >>"$ROOT/extra/public-keys.tsv"
  done
  jq --rawfile keys "$ROOT/extra/public-keys.tsv" '
    ($keys | split("\n") | map(select(length > 0) | split("\t") | {key: .[0], value: .[1]}) | from_entries) as $pub
    | map(.key.publicKey = $pub[.key.subject])' "$NEWPARTICIPANT_EXTRA_SUBJECTS" >"$ROOT/pay/genesis-extra-subjects.json"
else
  printf '[]\n' >"$ROOT/pay/genesis-extra-subjects.json"
fi
if [ -n "${EXTRA_GENESIS_ENROLLMENTS:-}" ]; then
  jq -s '.[0] + .[1] + .[2]' "$EXTRA_GENESIS_ENROLLMENTS" "$ROOT/pay/genesis-extra-subjects.json" "$ROOT/pay/genesis-enrollments.json" \
    >"$ROOT/pay/genesis-enrollments-all.json"
else
  jq -s '.[0] + .[1]' "$ROOT/pay/genesis-extra-subjects.json" "$ROOT/pay/genesis-enrollments.json" \
    >"$ROOT/pay/genesis-enrollments-all.json"
fi
cat >"$ROOT/pay/genesis-observer.json" <<EOF
{"subject":"30","capability":"4030","enrolCapability":"4032"}
EOF
# The one genesis template (genesis.sh) from the example params, with the grain
# platform only when requested by an application-hosting journey, and with this
# Store's domain and sponsor subject; it honours EXTRA_GENESIS_ENROLLMENTS and
# MINI_TAIL_BOUND (the tail bound L, default the example's 256 = 4 x 64).
jq --argjson domain "$DOMAIN" --argjson subject "$SUBJECT" --argjson budget "$OWNER_BUDGET" --argjson balance "$SPONSOR_BALANCE" \
  --arg meter "$METER_ALLOWANCE" --arg disabled "$DISABLED_EVALUATORS" --argjson tail "${MINI_TAIL_BOUND:-256}" \
  --arg objective "${OBJECTIVE_INVOCATION_POLICY:-}" --argjson grains "$GRAIN_PLATFORM" \
  '.domain = $domain | .sponsor.subject = $subject | .sponsor.initialBalance = $balance | .ownerBudget = $budget | .tailBound = $tail
   | if $meter != "" then .meterAllowance |= with_entries(.value = ($meter | tonumber)) else . end
   | ($disabled | split(" ") | map(select(length > 0))) as $off
   | if ($off | length) > 0 then .disabledEvaluators = $off else . end
   | if $objective != "" then .objectiveInvocation = $objective else . end
   | if $grains == 1 then
       .grainPlatform.lifecycleManagement = {managementSubject:.sponsor.subject,managementKeyId:.sponsor.keyId}
     else del(.grainPlatform) end' \
  "$HERE/genesis-params.example.json" >"$ROOT/genesis-params.json"
. "$HERE/journey.d/lib/genesis-params.sh"
resolve_params_sh "$HERE/../.." || exit 2
sh "$GENESIS_PARAMS_SH" fill-genesis "$ROOT/genesis-params.json"
fill_completion_custodian "$ROOT/genesis-params.json" "$ROOT" "$MINI" || exit 2
EXTRA_GENESIS_ENROLLMENTS="$ROOT/pay/genesis-enrollments-all.json" \
GENESIS_PAY_OBSERVER="$ROOT/pay/genesis-observer.json" \
  sh "$HERE/genesis.sh" "$ROOT/genesis-params.json" "$SPONSOR_PUBLIC" "$CLOCK_PUBLIC" \
  "$HOST" "$STORE" "$VERIFIER" "$ROOT"

# NEWPARTICIPANT_PROVIDER_SERVICES=FILE: the Host's per-route provider tariffs
# (a JSON array) pinned from the first event, as a hosted Hermes purse needs.
if [ -n "${NEWPARTICIPANT_PROVIDER_SERVICES:-}" ]; then
  jq --slurpfile p "$NEWPARTICIPANT_PROVIDER_SERVICES" '.providerServices = $p[0]' "$ROOT/operator.json" >"$ROOT/operator.json.tmp" &&
    mv "$ROOT/operator.json.tmp" "$ROOT/operator.json"
fi
"$MINI" bootstrap --host "$HOST" --config "$ROOT/operator.json" \
  --source "$ROOT/genesis.json" --dir "$ROOT/deployment" \
  >"$ROOT/bootstrap.stdout"
CONFIG="$ROOT/deployment/pinned-config.json"
[ -s "$CONFIG" ] || { echo 'bootstrap produced no pinned config' >&2; exit 1; }

# NEWPARTICIPANT_SERVE=serve-operator serves the private operator socket (a
# hosted resident's preflight requires it); the default is the public serve.
start_serve

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
jq -e '.payControlCapability == "4031" and .payObserver == {"subject":"30","capability":"4030","enrolCapability":"4032"}' \
  "$ROOT/genesis.json" >/dev/null
[ -s "$ROOT/deployment/pay-ledger-genesis.json" ] || { echo 'bootstrap retained no genesis pay ledger' >&2; exit 1; }

fixture_digests
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
# The first world of a variant is the template: captured with its server stopped (a quiescent Store),
# published atomically (meta, then tar), the server started again for this caller.
if [ -n "$TEMPLATE_TAR" ] && [ ! -s "$TEMPLATE_TAR" ]; then
  stop_serve
  tmp_tar=$TEMPLATE_TAR.$$.tmp tmp_meta=$TEMPLATE_META.$$.tmp
  (cd "$ROOT" && tar -cf "$tmp_tar" --exclude=./public/serve.log --exclude=./public/server.pid --exclude=./public/mini.config \
     --exclude=./template-restored.txt .)
  jq -n --arg root "$ROOT" --arg socket "$SOCKET" --arg variant "$TEMPLATE_VARIANT" \
    --arg host "$HOST" --arg mini "$MINI" --arg store "$STORE" --arg verifier "$VERIFIER" \
    '{type:"minidregg-newparticipant-template-v1",root:$root,socket:$socket,variant:$variant,
      binaries:{host:$host,mini:$mini,store:$store,verifier:$verifier}}' >"$tmp_meta"
  mv "$tmp_meta" "$TEMPLATE_META" && mv "$tmp_tar" "$TEMPLATE_TAR"
  start_serve
fi
printf '%s\n' "$ROOT/handoff.json"
