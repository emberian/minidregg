#!/usr/bin/env bash
# Isolated Linux/systemd race experiment for launch-gate.rs. No Mini node.
set -euo pipefail
umask 077

[[ $# == 1 && $1 == /* && ! -e $1 ]] || {
  echo 'usage: launch-gate-probe.sh NEW_ABSOLUTE_SCRATCH_ROOT' >&2; exit 2;
}
root=$1
here=$(cd -- "$(dirname -- "$0")" && pwd)
gate_source=$(realpath -e "$here/../../deploy/grain-host/launch-gate.rs")
mkdir -m 700 -- "$root"
rustc --edition=2021 "$gate_source" -o "$root/launch-gate"
gate=$root/launch-gate
task="$(date +%s)$$"
late="mini-grain-t${task}-o1"
running="mini-grain-t${task}-o2"
preinit="mini-grain-t${task}-o3"

cleanup() {
  systemctl --user kill --signal=SIGKILL --kill-whom=all "$late.service" "$running.service" >/dev/null 2>&1 || :
  systemctl --user stop "$late.service" "$running.service" >/dev/null 2>&1 || :
}
trap cleanup EXIT

cat > "$root/worker.sh" <<'EOF'
#!/bin/sh
set -eu
echo "$$" > "$1"
exec /bin/sleep 30
EOF
chmod 700 "$root/worker.sh"

# A start request reaches systemd before the fence, but ExecStart is delayed
# by a real transient-unit ExecStartPre. The gate must reject it after fence.
"$gate" init "$root" "$late" > "$root/late-init.log"
systemd-run --user --no-block --unit="$late" \
  --property=KillMode=control-group --property='ExecStartPre=/bin/sleep 3' \
  "$gate" run "$root" "$late" -- /bin/sh "$root/worker.sh" "$root/late-worker.pid" \
  > "$root/late-systemd.log" 2>&1
rg -q 'Running as unit:' "$root/late-systemd.log"
state=$(systemctl --user show -p ActiveState --value "$late.service")
[[ $state == activating ]] || { echo "late unit not in ExecStartPre: $state" >&2; exit 1; }
substate=$(systemctl --user show -p SubState --value "$late.service")
[[ $substate == start-pre ]] || { echo "late unit not in start-pre: $substate" >&2; exit 1; }
printf 'late_start_before_fence_state=%s\n' "$state" > "$root/race.log"
"$gate" fence "$root" "$late" > "$root/late-fence.log"
sleep 4
[[ ! -e $root/late-worker.pid ]] || { echo 'delayed worker ran after fence' >&2; exit 1; }
result=$(systemctl --user show -p Result --value "$late.service")
status=$(systemctl --user show -p ExecMainStatus --value "$late.service")
[[ $result == exit-code && $status == 1 ]] || {
  echo "late gate did not refuse: result=$result status=$status" >&2; exit 1;
}
printf 'late_gate_result=%s exec_status=%s\n' "$result" "$status" >> "$root/race.log"
printf 'PASS prior systemd start request, delayed ExecStart, fence first: worker did not run\n' >> "$root/race.log"

# A fence before even the gate initialization must also be terminal.
"$gate" fence "$root" "$preinit" > "$root/preinit-fence.log"
if "$gate" init "$root" "$preinit" > "$root/preinit-init.log" 2>&1; then
  echo 'init rearmed a fenced operation' >&2; exit 1
fi
if "$gate" run "$root" "$preinit" -- /bin/sh "$root/worker.sh" "$root/preinit-worker.pid" \
    > "$root/preinit-run.log" 2>&1; then
  echo 'fenced operation launched' >&2; exit 1
fi
[[ ! -e $root/preinit-worker.pid ]]
printf 'PASS fence before init cannot rearm or launch\n' >> "$root/race.log"

# If the gate has already started the worker, fence persists first, then
# systemd kills that exact unit and a later retry cannot run another worker.
"$gate" init "$root" "$running" > "$root/running-init.log"
systemd-run --user --wait --collect --unit="$running" \
  --property=KillMode=control-group \
  "$gate" run "$root" "$running" -- /bin/sh "$root/worker.sh" "$root/running-worker.pid" \
  > "$root/running-systemd.log" 2>&1 &
running_client=$!
for _ in {1..50}; do
  [[ ! -s $root/running-worker.pid ]] || break
  sleep 0.1
done
[[ -s $root/running-worker.pid ]]
worker_pid=$(cat "$root/running-worker.pid")
worker_cgroup=$(systemctl --user show -p ControlGroup --value "$running.service")
[[ $worker_cgroup == /* && -r /sys/fs/cgroup$worker_cgroup/cgroup.procs ]]
"$gate" fence "$root" "$running" > "$root/running-fence.log"
systemctl --user kill --signal=SIGKILL --kill-whom=all "$running.service"
systemctl --user stop "$running.service" >/dev/null 2>&1 || :
wait "$running_client" || :
for _ in {1..30}; do
  if ! kill -0 "$worker_pid" 2>/dev/null; then break; fi
  sleep 0.1
done
if kill -0 "$worker_pid" 2>/dev/null; then
  stat=$(ps -o stat= -p "$worker_pid" || :)
  [[ $stat == Z* ]] || { echo "worker remains live: $worker_pid $stat" >&2; exit 1; }
fi
if [[ -d /sys/fs/cgroup$worker_cgroup ]]; then
  while IFS= read -r procs; do
    [[ ! -s $procs ]] || { echo "worker cgroup still has processes: $procs" >&2; exit 1; }
  done < <(find "/sys/fs/cgroup$worker_cgroup" -name cgroup.procs -type f)
fi
if "$gate" run "$root" "$running" -- /bin/sh "$root/worker.sh" "$root/retry-worker.pid" \
    > "$root/retry-run.log" 2>&1; then
  echo 'worker relaunched after fence' >&2; exit 1
fi
[[ ! -e $root/retry-worker.pid ]]
printf 'PASS fence plus exact unit kill stops running worker and blocks retry\n' >> "$root/race.log"

sha256sum "$gate" "$gate_source" "$here/launch-gate-probe.sh" > "$root/sha256.txt"
uname -a > "$root/platform.log"
systemctl --version | head -1 >> "$root/platform.log"
cat "$root/race.log"
printf 'evidence=%s\n' "$root"
