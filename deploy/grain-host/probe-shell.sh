#!/usr/bin/env bash
# Component probe of the forced-command wrapper and the real control connector.
# Requires a built grain-runtime binary; never opens a Mini store or SSH account.
set -euo pipefail
umask 077

runtime=${1:?usage: probe-shell.sh ABS_GRAIN_RUNTIME}
[[ $runtime == /* && -x $runtime ]] || { echo 'absolute executable grain runtime required' >&2; exit 64; }
here=$(cd "$(dirname "$0")" && pwd)
scratch=$(mktemp -d /tmp/mini-grain-shell.XXXXXX)
server_pid=
cleanup() {
  [[ -z $server_pid ]] || kill "$server_pid" >/dev/null 2>&1 || :
  rm -rf -- "$scratch"
}
trap cleanup EXIT

cp "$here/../../native/grain-runtime/src/control.rs" "$scratch/control.rs"
cp "$here/probe_control.rs" "$scratch/probe_control.rs"
rustc --edition=2021 -A dead_code "$scratch/probe_control.rs" -o "$scratch/probe-control"
socket=$scratch/controller.sock
log=$scratch/events.log
"$scratch/probe-control" "$socket" "$log" &
server_pid=$!
for _ in {1..100}; do
  [[ ! -S $socket ]] || break
  sleep 0.05
done
[[ -S $socket ]] || { echo 'probe controller did not create socket' >&2; exit 1; }

index=0
for mode in hard soft soft; do
  index=$((index + 1))
  args=("$runtime" "$socket")
  [[ $mode != soft ]] || args+=(soft)
  printf 'status\n' | SSH_ORIGINAL_COMMAND='run forbidden' \
    "$here/grain-ssh" "${args[@]}" > "$scratch/$index.out" \
    2> "$scratch/$index.err"
done
for _ in {1..100}; do
  if ! kill -0 "$server_pid" >/dev/null 2>&1; then break; fi
  sleep 0.05
done
if kill -0 "$server_pid" >/dev/null 2>&1; then
  echo 'probe controller did not settle three detachments' >&2
  exit 1
fi
wait "$server_pid"
server_pid=

rg -q '^attached:1:soft=false$' "$log"
rg -q '^hard-interrupt:1$' "$log"
rg -q '^detached:1:hard=true$' "$log"
rg -q '^attached:2:soft=true$' "$log"
rg -q '^detached:2:hard=false$' "$log"
rg -q '^attached:3:soft=true$' "$log"
rg -q '^detached:3:hard=false$' "$log"
[[ $(rg -c '^line:[123]:status$' "$log") == 3 ]]
if rg -q 'forbidden|line:[123]:attach' "$log"; then
  echo 'wrapper forwarded an original command or a second attach' >&2
  exit 1
fi
if "$here/grain-ssh" "$runtime" "$socket" invalid > "$scratch/invalid.out" 2>&1; then
  echo 'invalid mode was accepted' >&2
  exit 1
fi
rg -q 'attachment mode must be hard or soft' "$scratch/invalid.out"
cat "$log"
printf 'PASS hard EOF interrupted once; two soft EOFs detached and reconnected; original command ignored\n'
