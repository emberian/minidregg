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

# The one genesis template: genesis.sh beside this script in a built
# candidate, native/resource-client/genesis.sh in a source tree.
if [ -f "$here/genesis.sh" ]; then
  GENESIS=$here/genesis.sh
else
  GENESIS=$here/../../native/resource-client/genesis.sh
fi
check_params() { sh "$GENESIS" --check "$1" || candidate_die "params file fails the minidregg-candidate-genesis-params-v1 schema (INTERFACES.md)"; }

init() {
  [ -n "$manifest" ] || candidate_die "init needs --manifest"
  [ -n "$params" ] || candidate_die "init needs --params (start from genesis-params.example.json)"
  candidate_resolve "$manifest"
  params=$(candidate_abs "$params")
  check_params "$params"
  state=$(candidate_abs "$state")
  [ ! -e "$state" ] && [ ! -L "$state" ] || candidate_die "refusing existing state directory: $state"
  # A Unix socket path must fit sockaddr_un.sun_path (108 bytes incl. NUL).
  socket_path="$state/public/mini.sock"
  [ "${#socket_path}" -lt 108 ] \
    || candidate_die "state path too long: $socket_path is ${#socket_path} bytes; a Unix socket path must be under 108"
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
  # The clock subject's key (its workspace: `mini clock --action init`, e.g. the
  # deploy's /var/lib/mini/clock); the sponsor holds no tick authority.
  "$MINI" keygen --secret "$state/keys/clock.key" --public "$state/keys/clock.pub" \
    >"$state/keys/clock.pub.hex"
  clock_public=$(od -An -tx1 -v "$state/keys/clock.pub" | tr -d ' \n')

  sh "$GENESIS" "$p" "$sponsor_public" "$clock_public" "$HOST" "$STORE" "$VERIFIER" "$state" \
    || candidate_die "genesis template refused (see above)"

  "$MINI" bootstrap --host "$HOST" --config "$state/operator.json" \
    --source "$state/genesis.json" --dir "$state/deployment" >"$state/logs/bootstrap.stdout"
  [ -s "$state/deployment/pinned-config.json" ] || candidate_die "bootstrap produced no pinned config"

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
