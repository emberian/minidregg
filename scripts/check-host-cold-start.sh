#!/usr/bin/env bash
# check-host-cold-start.sh HOST: the native Host must start without doing work.
#
# Lean runs every compiled nullary `def` of every linked module in that module's
# initializer, before `main`. A proof exhibit or demo table left computable in a
# module the Host imports is therefore paid by every Host start: `mini serve`
# (the first signed read after a restart waits for it), bootstrap, and every CLI
# call. Measured 2026-10-01 (COLD-READ): `Compiler.Emit.spendDescriptor` flattened
# 2,696,666 gates in `initialize_Compiler_Emit` -- 6-9 s of CPU and ~390 MB per
# start on persvati, 24-27 s on the public node -- against 0.1 s and ~78 MB
# without it.
#
# The check runs the Host with no arguments (initializers, then the usage text)
# and refuses a peak RSS over HOST_INIT_MAX_RSS_KB or user+system CPU over
# HOST_INIT_MAX_CPU_S. Peak RSS is the steady signal (it does not move with box
# load); the CPU bound is loose for the same reason. Requires GNU time.
set -euo pipefail
export LC_ALL=C
host=${1:?usage: check-host-cold-start.sh HOST}
[[ -f "$host" && -x "$host" ]] || { echo "check-host-cold-start: Host executable absent or not executable: $host" >&2; exit 2; }
max_rss_kb=${HOST_INIT_MAX_RSS_KB:-160000}
max_cpu_s=${HOST_INIT_MAX_CPU_S:-1.5}
[[ -x /usr/bin/time ]] || { echo "check-host-cold-start: needs GNU time at /usr/bin/time" >&2; exit 2; }
report=$(mktemp)
output=$(mktemp)
trap 'rm -f "$report" "$output"' EXIT
status=0
/usr/bin/time -o "$report" -f '%U %S %M %e' "$host" >"$output" 2>&1 || status=$?
# Main deliberately returns 1 for the no-argument usage request. An exec
# failure, signal, or unrelated error must not become a cheap startup PASS.
if [[ "$status" != 1 ]] || ! grep -q 'minidregg-host:' "$output" || ! grep -q 'minidregg-host CONFIG' "$output"; then
  echo "check-host-cold-start: Host did not complete its no-argument usage path (exit $status)" >&2
  cat "$output" >&2
  exit 2
fi
read -r user sys rss wall < <(tail -1 "$report")
[[ "$rss" =~ ^[0-9]+$ ]] || { echo "check-host-cold-start: no measurement for $host" >&2; cat "$report" >&2; exit 2; }
cpu=$(awk -v u="$user" -v s="$sys" 'BEGIN { printf "%.2f", u + s }')
echo "host cold start: cpu ${cpu}s (user $user sys $sys), peak RSS $((rss / 1024)) MB, wall ${wall}s"
fail=0
if (( rss > max_rss_kb )); then
  echo "check-host-cold-start: peak RSS ${rss} KB exceeds ${max_rss_kb} KB: a module initializer is building data at startup" >&2
  fail=1
fi
if awk -v c="$cpu" -v m="$max_cpu_s" 'BEGIN { exit !(c > m) }'; then
  echo "check-host-cold-start: startup CPU ${cpu}s exceeds ${max_cpu_s}s: a module initializer is computing at startup" >&2
  fail=1
fi
if (( fail )); then
  echo "  find it: sample the Host under gdb at startup; the innermost initialize_<Module> frame names the module" >&2
  exit 1
fi
