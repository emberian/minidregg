#!/bin/bash
# stop-residents.sh RUN_ROOT: stop the consent and codec residents a world started, by the PID
# files in its own anchor directory (RUN_ROOT/a), and assert they are gone. Works on a world
# that never finished coming up (no WORLD.env needed). A PID is signalled only when its file
# names it and /proc/PID/cmdline is still a `mini ...-resident` process: never by pattern.
set -uo pipefail
[[ $# == 1 && -d $1 ]] || { echo "usage: $0 RUN_ROOT" >&2; exit 2; }
dir=$1/a
rc=0
[[ -d $dir ]] || exit 0
pids=()
for file in "$dir"/*.pid; do
  [[ -f $file ]] || continue
  pid=$(tr -d '[:space:]' <"$file")
  [[ $pid =~ ^[0-9]+$ ]] || { echo "stop-residents: $file does not hold a pid" >&2; rc=1; continue; }
  if [[ -r /proc/$pid/cmdline ]] && tr '\0' ' ' </proc/$pid/cmdline | grep -q -- '-resident '; then
    # the resident's descendants (its Host, store and verifier children), named before it ends
    kids=$(pgrep -P "$pid" || true)
    kill "$pid" 2>/dev/null && pids+=("$pid" $kids)
  fi
done
for pid in "${pids[@]}"; do
  for _ in $(seq 1 100); do kill -0 "$pid" 2>/dev/null || continue 2; sleep 0.1; done
  echo "stop-residents: resident $pid survived its world" >&2; rc=1
done
exit $rc
