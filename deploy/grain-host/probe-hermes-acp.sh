#!/usr/bin/env bash
# Isolated upstream Hermes ACP initialization through the real Linux launcher.
# The runtime root must already contain /agent/hermes-acp, its upstream source
# and venv, and /agent/grain-runtime. No provider request or model call occurs.
set -euo pipefail

if [[ $# != 2 ]]; then
  echo 'usage: probe-hermes-acp.sh ABS_BWRAP_LAUNCHER ABS_RUNTIME_ROOT' >&2
  exit 64
fi
launcher=$(realpath -e -- "$1")
runtime_root=$(realpath -e -- "$2")
[[ -x $launcher && -x $runtime_root/hermes-acp && -x $runtime_root/grain-runtime ]] || exit 66
scratch=$(mktemp -d /tmp/mini-hermes-acp-probe.XXXXXX)
task=$$
controller="mini-grain-controller@$task.service"
check_unit="mini-grain-t${task}-o1"
init_unit="mini-grain-t${task}-o2"
cleanup() {
  systemctl --user stop "$controller" "$check_unit.service" "$init_unit.service" >/dev/null 2>&1 || :
  rm -rf -- "$scratch"
}
trap cleanup EXIT
mkdir -m 700 "$scratch/controller" "$scratch/workspace"
mkdir -m 700 "$scratch/workspace/.hermes" "$scratch/workspace/.cache" \
  "$scratch/workspace/.config" "$scratch/workspace/.local" "$scratch/workspace/.local/share"
printf 'test-only-key' > "$scratch/controller/key"
printf '{}' > "$scratch/controller/task.json"
printf '{}' > "$scratch/controller/host.json"
export MINI_GRAIN_CONTROLLER_UNIT="$controller"
export MINI_GRAIN_STATE_DIR="$scratch/controller"
export MINI_GRAIN_CUSTODY_KEY="$scratch/controller/key"
export MINI_GRAIN_TASK_CONFIG="$scratch/controller/task.json"
export MINI_GRAIN_HOST_CONFIG="$scratch/controller/host.json"

printf 'host=%s upstream_pyproject_sha256=%s upstream_lock_sha256=%s wrapper_sha256=%s keyless_runtime_sha256=%s\n' \
  "$(hostname)" \
  "$(sha256sum "$runtime_root/source/pyproject.toml" | cut -d' ' -f1)" \
  "$(sha256sum "$runtime_root/source/uv.lock" | cut -d' ' -f1)" \
  "$(sha256sum "$runtime_root/hermes-acp" | cut -d' ' -f1)" \
  "$(sha256sum "$runtime_root/grain-runtime" | cut -d' ' -f1)"
systemd-run --user --unit="mini-grain-controller@$task" \
  --property=RuntimeMaxSec=30s /bin/sleep 30 >/dev/null

MINI_GRAIN_UNIT="$check_unit" timeout 20 "$launcher" \
  --workspace "$scratch/workspace" --runtime-root "$runtime_root" \
  --network none -- /agent/hermes-acp --check > "$scratch/check.log" 2>&1
rg -q 'Hermes ACP check OK' "$scratch/check.log"
echo 'PASS upstream hermes-acp --check in no-network worker unit'

export MINI_GRAIN_UNIT="$init_unit"
coproc ACP {
  timeout 25 "$launcher" --workspace "$scratch/workspace" \
    --runtime-root "$runtime_root" --network none -- /agent/hermes-acp
}
printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":1,"clientCapabilities":{"fs":{"readTextFile":false,"writeTextFile":false}},"clientInfo":{"name":"mini-linux-probe","version":"0.1"}}}' >&"${ACP[1]}"
IFS= read -r -t 20 response <&"${ACP[0]}"
printf '%s\n' "$response" | jq -e \
  '.id == 1 and .result.protocolVersion == 1 and (.result.authMethods | any(.id == "hermes-setup"))' >/dev/null
echo 'PASS upstream ACP initialize protocol v1; setup-only auth'
kill -TERM "$ACP_PID" >/dev/null 2>&1 || :
wait "$ACP_PID" || :
for _ in {1..20}; do
  state=$(systemctl --user show -p ActiveState --value "$init_unit.service" 2>/dev/null || :)
  [[ $state != inactive ]] || break
  sleep 0.1
done
[[ $state == inactive ]]
echo 'PASS worker unit inactive after connector stop'
