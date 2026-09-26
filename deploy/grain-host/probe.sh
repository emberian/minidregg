#!/usr/bin/env bash
# Bounded Linux user-systemd/bwrap containment probe. Uses only transient user
# units and a private /tmp tree; no Mini/fn deployment or privileged changes.
set -euo pipefail
umask 077

launcher=$(realpath -e "${1:-$(dirname "$0")/bwrap}")
gate=$(realpath -e "$(dirname "$launcher")/launch-gate")
helper_source=$(realpath -e "$(dirname "$0")/probe_socket.rs")
scratch=$(mktemp -d /tmp/mini-grain-probe.XXXXXX)
task=$$
hard_unit="mini-grain-t${task}-o1"
bound_unit="mini-grain-t${task}-o2"
controller="mini-grain-controller@${task}.service"
cleanup() {
  systemctl --user stop "$hard_unit.service" "$bound_unit.service" "$controller" >/dev/null 2>&1 || :
  [[ -z ${broker_pid:-} ]] || kill "$broker_pid" >/dev/null 2>&1 || :
  rm -rf -- "$scratch"
}
trap cleanup EXIT

printf 'host=%s kernel=%s systemd=%s launcher_sha256=%s gate_sha256=%s probe_sha256=%s socket_helper_sha256=%s\n' \
  "$(hostname)" "$(uname -r)" "$(systemctl --version | head -1)" \
  "$(sha256sum "$launcher" | cut -d' ' -f1)" \
  "$(sha256sum "$gate" | cut -d' ' -f1)" \
  "$(sha256sum "$0" | cut -d' ' -f1)" \
  "$(sha256sum "$helper_source" | cut -d' ' -f1)"
[[ $($launcher --launch-gate-protocol) == mini-grain-launch-gate-v1 ]]
echo 'PASS launcher requires sibling gate protocol v1'
mkdir "$scratch/runtime" "$scratch/work" "$scratch/controller"
printf 'key' > "$scratch/controller/key"
printf '{}' > "$scratch/controller/task.json"
printf '{}' > "$scratch/controller/host.json"
export MINI_GRAIN_STATE_DIR="$scratch/controller"
export MINI_GRAIN_CUSTODY_KEY="$scratch/controller/key"
export MINI_GRAIN_TASK_CONFIG="$scratch/controller/task.json"
export MINI_GRAIN_HOST_CONFIG="$scratch/controller/host.json"
unset MINI_GRAIN_CONTROLLER_UNIT MINI_GRAIN_BROKER_SOCKET MINI_GRAIN_TOOL_CUSTODY_KEY || :

rustc --edition=2021 -o "$scratch/runtime/probe-socket" "$helper_source"
"$scratch/runtime/probe-socket" server "$scratch/controller/broker.sock" > "$scratch/broker.recv" &
broker_pid=$!
for _ in {1..30}; do
  [[ ! -S "$scratch/controller/broker.sock" ]] || break
  sleep 0.1
done
[[ -S "$scratch/controller/broker.sock" ]]
export MINI_GRAIN_BROKER_SOCKET="$scratch/controller/broker.sock"
"$gate" init "$scratch/controller" "mini-grain-t${task}-o3" >/dev/null
MINI_GRAIN_UNIT="mini-grain-t${task}-o3" timeout 10 "$launcher" --workspace "$scratch/work" \
  --runtime-root "$scratch/runtime" --network none -- /agent/probe-socket client /run/mini-grain.sock \
  > "$scratch/broker.out" 2>&1
wait "$broker_pid"
broker_pid=
rg -q broker-pong "$scratch/broker.out"
rg -q broker-received-ping "$scratch/broker.recv"
echo 'PASS broker socket connect through exact bind'
unset MINI_GRAIN_BROKER_SOCKET
if MINI_GRAIN_HOST_CONFIG=/usr/bin/true MINI_GRAIN_UNIT="mini-grain-t${task}-o4" \
  "$launcher" --workspace "$scratch/work" --runtime-root "$scratch/runtime" \
  --network none -- /agent/probe-socket client /run/mini-grain.sock > "$scratch/usr-refusal.out" 2>&1; then
  echo '/usr host-config exposure was accepted' >&2; exit 1
fi
rg -q 'exposed by worker mount: /usr' "$scratch/usr-refusal.out"
echo 'PASS /usr host-config exposure refused before launch'
if MINI_GRAIN_UNIT="mini-grain-t${task}-o5" \
  "$launcher" --workspace "$scratch" --runtime-root "$scratch/runtime" \
  --network none -- /agent/probe-socket client /run/mini-grain.sock > "$scratch/work-refusal.out" 2>&1; then
  echo 'workspace containing controller state was accepted' >&2; exit 1
fi
rg -q 'exposed by worker mount' "$scratch/work-refusal.out"
echo 'PASS workspace containing controller state refused before launch'
printf 'probe-only' > "$scratch/work/provider.key"
for provider_var in MINI_GRAIN_PROVIDER_CUSTODY_KEY MINI_GRAIN_PROVIDER_KEY_FILE; do
  if env "$provider_var=$scratch/work/provider.key" MINI_GRAIN_UNIT="mini-grain-t${task}-o6" \
    "$launcher" --workspace "$scratch/work" --runtime-root "$scratch/runtime" \
    --network none -- /agent/probe-socket client /run/mini-grain.sock \
    > "$scratch/provider-refusal.out" 2>&1; then
    echo "$provider_var exposure was accepted" >&2; exit 1
  fi
  rg -q 'exposed by worker mount' "$scratch/provider-refusal.out"
done
echo 'PASS provider custody and key file exposure refused before launch'
for invalid_max in 0 1801 99999999999999999999 12x; do
  if MINI_GRAIN_RUNTIME_MAX_SEC=$invalid_max MINI_GRAIN_UNIT="mini-grain-t${task}-o6" \
    "$launcher" --workspace "$scratch/work" --runtime-root "$scratch/runtime" \
    --network none -- /agent/probe-socket client /run/mini-grain.sock \
    > "$scratch/runtime-max-refusal.out" 2>&1; then
    echo "invalid worker runtime max was accepted: $invalid_max" >&2; exit 1
  fi
  rg -q 'MINI_GRAIN_RUNTIME_MAX_SEC' "$scratch/runtime-max-refusal.out"
done
echo 'PASS invalid worker runtime max refused before launch'

printf '#!/bin/sh\nsetsid /bin/sleep 30 &\necho started > /workspace/started\nwait\n' > "$scratch/runtime/setsid-probe"
chmod +x "$scratch/runtime/setsid-probe"

wait_started() {
  for _ in {1..30}; do
    [[ ! -s "$scratch/work/started" ]] || return 0
    sleep 0.1
  done
  echo 'worker did not start' >&2
  return 1
}
host_pids() {
  local cg
  cg=$(systemctl --user show -p ControlGroup --value "$1.service")
  [[ -n $cg && -f /sys/fs/cgroup$cg/cgroup.procs ]]
  cat "/sys/fs/cgroup$cg/cgroup.procs"
}
assert_dead() {
  local pid state
  for pid in $1; do
    if [[ -e /proc/$pid ]]; then
      state=$(ps -o stat= -p "$pid" || :)
      [[ $state == Z* ]] || { echo "live host pid $pid: $state" >&2; return 1; }
    fi
  done
}

"$gate" init "$scratch/controller" "$hard_unit" >/dev/null
MINI_GRAIN_RUNTIME_MAX_SEC=47 MINI_GRAIN_UNIT="$hard_unit" "$launcher" --workspace "$scratch/work" \
  --runtime-root "$scratch/runtime" --network none -- /agent/setsid-probe \
  > "$scratch/hard.out" 2>&1 &
wrapper=$!
wait_started
[[ $(systemctl --user show -p RuntimeMaxUSec --value "$hard_unit.service") == 47s ]]
echo 'PASS controller-selected 47-second worker lifetime installed in transient unit'
pids=$(host_pids "$hard_unit")
printf 'hard cgroup=%s host_pids=%s\n' \
  "$(systemctl --user show -p ControlGroup --value "$hard_unit.service")" \
  "$(tr '\n' ',' <<< "$pids")"
kill -TERM "$wrapper"
wait "$wrapper" || :
assert_dead "$pids"
printf 'PASS wrapper TERM stopped setsid unit (%s host pids, state=%s)\n' \
  "$(wc -w <<< "$pids" | tr -d ' ')" \
  "$(systemctl --user show -p ActiveState --value "$hard_unit.service" || :)"

rm "$scratch/work/started"
systemd-run --user --unit="mini-grain-controller@$task" \
  --property=RuntimeMaxSec=20s /bin/sleep 20 >/dev/null
"$gate" init "$scratch/controller" "$bound_unit" >/dev/null
MINI_GRAIN_CONTROLLER_UNIT="$controller" MINI_GRAIN_UNIT="$bound_unit" \
  "$launcher" --workspace "$scratch/work" --runtime-root "$scratch/runtime" \
  --network none -- /agent/setsid-probe > "$scratch/bound.out" 2>&1 &
wrapper=$!
wait_started
pids=$(host_pids "$bound_unit")
printf 'bound cgroup=%s host_pids=%s\n' \
  "$(systemctl --user show -p ControlGroup --value "$bound_unit.service")" \
  "$(tr '\n' ',' <<< "$pids")"
systemctl --user stop "$controller"
wait "$wrapper" || :
assert_dead "$pids"
printf 'PASS controller BindsTo stopped setsid unit (%s host pids, state=%s)\n' \
  "$(wc -w <<< "$pids" | tr -d ' ')" \
  "$(systemctl --user show -p ActiveState --value "$bound_unit.service" || :)"
