#!/usr/bin/env bash
# Run a command while sampling the machine's memory, swap, Lean process count and
# free disk to stdout, then print the extremes. Exit status is the command's.
#
#   bash scripts/ci-run-sampled.sh lake build Theory Pred
#
# Why it exists: hosted-runner jobs of this repo have died with "The runner has
# received a shutdown signal" (exit 143) in the middle of a Lean build, after 20,
# 30, 36 and 68 minutes, with no error of our own. A job killed that way runs no
# further step, so the evidence has to already be in the log: the last sample
# line before the cut shows whether memory, swap or disk was exhausted.
#
#   CI_SAMPLE_SECS     seconds between samples (default 60)
#   CI_WORKED_SECS     a command that ran longer than this did real work (default 300);
#                      under GitHub Actions the step outputs secs= and worked=true|false,
#                      which decide whether a build cache is worth saving
#   CI_SAMPLE_MEMINFO  meminfo file to read (default /proc/meminfo; tests point it elsewhere)
set -uo pipefail
[ "$#" -gt 0 ] || { echo "usage: ci-run-sampled.sh COMMAND [ARG...]" >&2; exit 2; }
interval=${CI_SAMPLE_SECS:-60}
meminfo=${CI_SAMPLE_MEMINFO:-/proc/meminfo}
samples=$(mktemp "${TMPDIR:-/tmp}/ci-samples.XXXXXX")

sample() {
  local mem lean load disk
  mem=$(awk '/^MemAvailable:/{a=$2} /^SwapTotal:/{st=$2} /^SwapFree:/{sf=$2}
             END{printf "mem_avail_mb=%d swap_used_mb=%d", a/1024, (st-sf)/1024}' "$meminfo")
  lean=$(ps -eo rss=,comm= | awk '{k = split($2, p, "/")} p[k]=="lean"{n++; if ($1>m) m=$1}
                                 END{printf "lean_procs=%d lean_max_rss_mb=%d", n, m/1024}')
  load=$(awk '{print $1}' /proc/loadavg 2>/dev/null || echo na)
  disk=$(df -Pm . | awk 'NR==2{print $4}')
  echo "$mem $lean load1=$load disk_avail_mb=$disk"
}

(
  while :; do
    line="[res $(date -u +%H:%M:%S)] $(sample)"
    echo "$line" | tee -a "$samples"
    sleep "$interval"
  done
) &
sampler=$!

start=$SECONDS
"$@"
rc=$?
elapsed=$(( SECONDS - start ))

kill "$sampler" 2>/dev/null
wait "$sampler" 2>/dev/null
echo "[res] extremes over $(wc -l < "$samples" | tr -d ' ') samples, command exit $rc:" \
  "$(awk '{for (i = 1; i <= NF; i++) { split($i, kv, "=");
      if (kv[1] == "mem_avail_mb"    && (!(kv[1] in v) || kv[2] < v[kv[1]])) v[kv[1]] = kv[2];
      if (kv[1] == "disk_avail_mb"   && (!(kv[1] in v) || kv[2] < v[kv[1]])) v[kv[1]] = kv[2];
      if (kv[1] ~ /^(swap_used_mb|lean_procs|lean_max_rss_mb)$/ && (!(kv[1] in v) || kv[2] + 0 > v[kv[1]] + 0)) v[kv[1]] = kv[2] }}
    END{printf "min mem_avail_mb=%s, max swap_used_mb=%s, max lean_procs=%s, max lean_max_rss_mb=%s, min disk_avail_mb=%s",
        v["mem_avail_mb"], v["swap_used_mb"], v["lean_procs"], v["lean_max_rss_mb"], v["disk_avail_mb"]}' "$samples")"
rm -f "$samples"
if [ -n "${GITHUB_OUTPUT:-}" ]; then
  {
    echo "secs=$elapsed"
    if [ "$elapsed" -gt "${CI_WORKED_SECS:-300}" ]; then echo "worked=true"; else echo "worked=false"; fi
  } >> "$GITHUB_OUTPUT"
fi
exit "$rc"
