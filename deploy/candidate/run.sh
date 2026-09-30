#!/bin/sh
# Operate one Mini Store from a built candidate. Every path is the operator's.
#
#   run.sh init    --manifest CANDIDATE/manifest.json --params PARAMS.json --state NEW_DIR
#   run.sh serve   --state DIR     foreground; for systemd or any supervisor
#   run.sh start   --state DIR     background, with DIR/public/server.pid
#   run.sh stop    --state DIR     stop what `start` started (checks the pid's cmdline)
#   run.sh status  --state DIR
#   run.sh sponsor --state DIR     create the genesis sponsor's workspace (Store must be serving)
#   run.sh unit    --state DIR     print a systemd unit that runs `serve`
#
# `init` generates the sponsor key, writes operator.json and genesis.json from
# PARAMS.json, and bootstraps a fresh Store through the Host. It never reuses
# an existing Store, key or genesis. See INTERFACES.md for every file it writes.
set -eu
umask 077
CANDIDATE_PROG=run.sh
here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd -P)
# shellcheck source=deploy/candidate/lib.sh
. "$here/lib.sh"
candidate_require jq sha256sum od tr ps

[ $# -ge 1 ] || { sed -n '2,15p' "$0" >&2; exit 2; }
action=$1
shift
manifest="" params="" state=""
while [ $# -gt 0 ]; do
  case "$1" in
    --manifest) manifest=$2; shift 2 ;;
    --params) params=$2; shift 2 ;;
    --state) state=$2; shift 2 ;;
    *) candidate_die "unknown argument: $1" ;;
  esac
done
[ -n "$state" ] || candidate_die "--state DIR is required"

check_params() {
  # Every genesis coordinate is a JSON integer the operator chose. jq holds
  # numbers as doubles, so refuse anything at or above 2^53 rather than round it.
  jq -e '
    def int: type == "number" and . >= 0 and . == floor and . < 9007199254740992;
    .type == "minidregg-candidate-genesis-params-v1"
    and ([.domain, .federation, .factoryId, .resourceBookId, .authorityCatalogueId, .issuer,
          .ownerBudget, .lifetime, .tariffBase, .tariffPerBirth, .tariffPerGrant,
          .tariffPerInitialPayloadByte, .collector, .asset, .genesisHeight, .issuerEpoch,
          .factoryControllerCapability] | all(int))
    and (.sponsor | [.subject, .keyId, .keyEpoch, .activeFrom, .activeUntil, .accountId,
          .spendCapabilityId, .controlCapabilityId, .factoryObserveCapabilityId,
          .initialBalance] | all(int))
    and (.meterAllowance | type == "object" and length == 10 and (map_values(int) | all))
  ' "$1" >/dev/null || candidate_die "params file fails the minidregg-candidate-genesis-params-v1 schema (INTERFACES.md)"
}

init() {
  [ -n "$manifest" ] || candidate_die "init needs --manifest"
  [ -n "$params" ] || candidate_die "init needs --params (start from genesis-params.example.json)"
  candidate_resolve "$manifest"
  params=$(candidate_abs "$params")
  check_params "$params"
  state=$(candidate_abs "$state")
  [ ! -e "$state" ] && [ ! -L "$state" ] || candidate_die "refusing existing state directory: $state"
  mkdir -m 700 "$state"
  mkdir -m 700 "$state/keys" "$state/public" "$state/namespace" "$state/tmp" "$state/logs"
  TMPDIR=$state/tmp
  export TMPDIR
  cp "$params" "$state/genesis-params.json"
  p=$state/genesis-params.json
  params=$p

  "$MINI" keygen --secret "$state/keys/sponsor.key" --public "$state/keys/sponsor.pub" \
    >"$state/keys/sponsor.pub.hex"
  sponsor_public=$(od -An -tx1 -v "$state/keys/sponsor.pub" | tr -d ' \n')

  jq -n --slurpfile p "$p" --arg store "$STORE" --arg root "$state/store" --arg verifier "$VERIFIER" '
    $p[0] as $p |
    {domain: $p.domain, federation: $p.federation, factoryId: $p.factoryId,
     resourceBookId: $p.resourceBookId, authorityCatalogueId: $p.authorityCatalogueId,
     issuer: $p.issuer, ownerBudget: $p.ownerBudget, lifetime: $p.lifetime,
     tariffBase: $p.tariffBase, tariffPerBirth: $p.tariffPerBirth, tariffPerGrant: $p.tariffPerGrant,
     tariffPerInitialPayloadByte: $p.tariffPerInitialPayloadByte, collector: $p.collector,
     asset: $p.asset, genesisHeight: $p.genesisHeight, expectedSeed: 0,
     storageBinary: $store, storageRoot: $root, signatureBinary: $verifier}' >"$state/operator.json"

  "$HOST" "$state/operator.json" profile >"$state/profile.json"
  semantics=$(jq -er '.semantics | select(type == "string" and test("^(0|[1-9][0-9]*)$"))' \
    "$state/profile.json") || candidate_die "Host profile has no semantics digest"

  jq -n --slurpfile p "$p" --arg semantics "$semantics" --arg public "$sponsor_public" '
    $p[0] as $p | def s: tostring;
    {domain: ($p.domain|s), factoryId: ($p.factoryId|s), resourceBookId: ($p.resourceBookId|s),
     authorityCatalogueId: ($p.authorityCatalogueId|s), federation: ($p.federation|s),
     tariffBase: ($p.tariffBase|s), tariffPerBirth: ($p.tariffPerBirth|s),
     tariffPerGrant: ($p.tariffPerGrant|s),
     tariffPerInitialPayloadByte: ($p.tariffPerInitialPayloadByte|s),
     collector: ($p.collector|s), asset: ($p.asset|s), expectedSemantics: $semantics,
     issuerEpoch: ($p.issuerEpoch|s), genesisHeight: ($p.genesisHeight|s),
     factoryPredicate: {type: "all", predicates: []},
     enrollments: [{key: {keyId: ($p.sponsor.keyId|s), keyEpoch: ($p.sponsor.keyEpoch|s),
                          algorithm: "1", subject: ($p.sponsor.subject|s), publicKey: $public,
                          activeFrom: ($p.sponsor.activeFrom|s),
                          activeUntil: ($p.sponsor.activeUntil|s), revoked: false},
                    accountId: ($p.sponsor.accountId|s),
                    spendCapabilityId: ($p.sponsor.spendCapabilityId|s),
                    controlCapabilityId: ($p.sponsor.controlCapabilityId|s),
                    factoryObserveCapabilityId: ($p.sponsor.factoryObserveCapabilityId|s),
                    initialBalance: ($p.sponsor.initialBalance|s),
                    accountPredicate: {type: "all", predicates: []}}],
     factoryControllerSubject: ($p.sponsor.subject|s),
     factoryControllerCapability: ($p.factoryControllerCapability|s),
     meterAllowance: ($p.meterAllowance | map_values(s))}' >"$state/genesis.json"

  "$MINI" bootstrap --host "$HOST" --config "$state/operator.json" \
    --source "$state/genesis.json" --dir "$state/deployment" >"$state/logs/bootstrap.stdout"
  [ -s "$state/deployment/pinned-config.json" ] || candidate_die "bootstrap produced no pinned config"

  jq -n --slurpfile p "$p" --slurpfile g "$state/genesis.json" '
    $p[0] as $p | def s: tostring;
    {type: "minidregg-participant-birth-context-v1", genesis: $g[0],
     template: {issuer: ($p.issuer|s), ownerBudget: ($p.ownerBudget|s), lifetime: ($p.lifetime|s)},
     sourceCapabilities: [($p.sponsor.spendCapabilityId|s)], funding: [],
     feePayer: ($p.sponsor.accountId|s),
     grants: [{kind: "object", target: ($p.factoryId|s),
               capability: ($p.sponsor.factoryObserveCapabilityId|s)},
              {kind: "account", target: ($p.sponsor.accountId|s),
               capability: ($p.sponsor.spendCapabilityId|s)}]}' >"$state/sponsor-birth-context.json"

  jq -n --arg manifest "$CANDIDATE_MANIFEST" --arg host "$(candidate_sha256 "$HOST")" \
    --arg config "$(candidate_sha256 "$state/deployment/pinned-config.json")" \
    --arg created "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    '{type: "minidregg-candidate-state-v1", manifest: $manifest, hostSha256: $host,
      pinnedConfigSha256: $config, createdUtc: $created}' >"$state/state.json"
  printf '%s\n' "$state/deployment/pinned-config.json"
}

serve_exec() {
  candidate_state "$state"
  TMPDIR=$STATE/tmp
  export TMPDIR
  exec "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET"
}

server_pid() {
  [ -f "$STATE/public/server.pid" ] || return 1
  pid=$(cat "$STATE/public/server.pid")
  case "$pid" in ''|*[!0-9]*) return 1 ;; esac
  [ -r "/proc/$pid/cmdline" ] || return 1
  cmdline=$(tr '\0' ' ' <"/proc/$pid/cmdline")
  case "$cmdline" in
    *" serve "*"--socket $SOCKET"*) printf '%s\n' "$pid" ;;
    *) return 1 ;;
  esac
}

start() {
  candidate_state "$state"
  if pid=$(server_pid); then candidate_die "already serving as pid $pid"; fi
  TMPDIR=$STATE/tmp
  export TMPDIR
  nohup "$MINI" serve --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    >>"$STATE/logs/serve.log" 2>&1 </dev/null &
  pid=$!
  printf '%s\n' "$pid" >"$STATE/public/server.pid"
  waited=0
  until [ -S "$SOCKET" ] && grep -q "mini: serving $SOCKET with host process" "$STATE/logs/serve.log"; do
    kill -0 "$pid" 2>/dev/null || { tail -20 "$STATE/logs/serve.log" >&2; candidate_die "mini serve exited"; }
    waited=$((waited + 1))
    [ "$waited" -lt 1200 ] || candidate_die "socket did not appear within 120 s"
    sleep 0.1
  done
  printf 'serving %s pid %s\n' "$SOCKET" "$pid"
}

any_alive() {
  for candidate_pid in "$@"; do
    kill -0 "$candidate_pid" 2>/dev/null && return 0
  done
  return 1
}

stop() {
  candidate_state "$state"
  pid=$(server_pid) || { echo "not running (no live server.pid naming $SOCKET)"; return 0; }
  children=$(ps -o pid= --ppid "$pid" | tr -d ' ' || true)
  kill -TERM "$pid"
  waited=0
  # shellcheck disable=SC2086
  while any_alive "$pid" $children; do
    waited=$((waited + 1))
    [ "$waited" -lt 600 ] || candidate_die "pid $pid or its Host child still alive after 60 s"
    sleep 0.1
  done
  rm -f "$STATE/public/server.pid"
  printf 'stopped pid %s (host children: %s)\n' "$pid" "$(echo $children)"
}

status() {
  candidate_state "$state"
  if pid=$(server_pid); then printf 'serving %s pid %s\n' "$SOCKET" "$pid"; else echo "not running"; fi
}

sponsor() {
  candidate_state "$state"
  [ -S "$SOCKET" ] || candidate_die "Store is not serving at $SOCKET"
  if [ -f "$STATE/sponsor/workspace.json" ]; then
    echo "sponsor workspace exists: $STATE/sponsor"
    return 0
  fi
  p=$STATE/genesis-params.json
  "$MINI" workspace --action init --host "$HOST" --config "$CONFIG" --socket "$SOCKET" \
    --key "$STATE/keys/sponsor.key" --subject "$(jq -r '.sponsor.subject | tostring' "$p")" \
    --birth-context "$STATE/sponsor-birth-context.json" \
    --namespace-root "$STATE/namespace" --dir "$STATE/sponsor" >"$STATE/logs/sponsor-init.stdout"
  "$MINI" workspace --action import --dir "$STATE/sponsor" --name factory --kind object \
    --target "$(jq -r '.factoryId | tostring' "$p")" \
    --observe-capability "$(jq -r '.sponsor.factoryObserveCapabilityId | tostring' "$p")" \
    --control-capability "$(jq -r '.factoryControllerCapability | tostring' "$p")" \
    >"$STATE/logs/sponsor-factory-import.stdout"
  "$MINI" workspace --action read --dir "$STATE/sponsor" --name factory >"$STATE/logs/sponsor-factory-read.json"
  echo "sponsor workspace: $STATE/sponsor"
}

unit() {
  candidate_state "$state"
  cat <<EOF
# Mini Store for $STATE. Install as a user unit (systemctl --user) under the
# account that owns $STATE, or as a system unit with User= set to that account.
[Unit]
Description=Mini Store ($STATE)
After=local-fs.target

[Service]
Type=simple
ExecStart=$here/run.sh serve --state $STATE
Restart=on-failure
RestartSec=5
UMask=0077
KillMode=control-group
TimeoutStopSec=60
NoNewPrivileges=yes
PrivateTmp=yes

[Install]
WantedBy=default.target
EOF
}

case "$action" in
  init) init ;;
  serve) serve_exec ;;
  start) start ;;
  stop) stop ;;
  status) status ;;
  sponsor) sponsor ;;
  unit) unit ;;
  *) candidate_die "unknown action: $action" ;;
esac
