#!/usr/bin/env bash
# Run an unchanged pipeline row in a private, capped scope. The sampler stays
# outside that scope so the evidence survives a group OOM kill.
set -uo pipefail
if [ "$#" -lt 2 ] || [ "$#" -gt 3 ]; then
  echo "usage: $0 BIN_DIR ROW [NEW_EVIDENCE_DIR]" >&2
  exit 2
fi
bin=$(realpath "$1")
row=$2
case "$row" in call|send|domain|objectrecord) ;; *) echo "unsupported row: $row" >&2; exit 2;; esac
repo=$(CDPATH='' cd -- "$(dirname -- "$0")/../.." && pwd)
if [ "$#" = 3 ]; then
  evidence=$3
  [ ! -e "$evidence" ] || { echo "evidence directory already exists" >&2; exit 2; }
  mkdir -m 700 -p "$evidence"
else
  evidence=$(mktemp -d "${TMPDIR:-/tmp}/kern-rss.XXXXXX")
fi
evidence=$(realpath "$evidence")
scratch=$(mktemp -d "${TMPDIR:-/tmp}/kr.XXXXXX")
unit=kern-rss-$(basename "$scratch")
unit=${unit//./-}
cap=${KERN_RSS_CAP_GIB:-10}
case "$cap" in 1|2|3|4|5|6|7|8|9|10|11|12) ;; *) echo "cap must be 1..12 GiB" >&2; exit 2;; esac
export SRC=$repo BIN=$bin RUN=$scratch OUT=$evidence LEANENV=1 ROW=$row
export ROWSFILE=$repo/scripts/pipeline/journey-rows
printf 'source=%s\nrow=%s\nbin=%s\ncap_gib=%s\nscratch=%s\n' \
  "$(git -C "$repo" rev-parse HEAD)" "$row" "$bin" "$cap" "$scratch" >"$evidence/inputs.txt"
sha256sum "$bin/minidregg-host" "$ROWSFILE" >"$evidence/inputs.sha256"
printf 'epoch_s pid ppid rss_kib vsz_kib elapsed_s command\n' >"$evidence/process-rss.txt"
systemd-run --user --scope --quiet --unit="$unit" \
  -p "MemoryMax=${cap}G" -p MemorySwapMax=0 \
  -- timeout "${KERN_RSS_TIMEOUT_S:-1800}" bash -c \
  '. "$ROWSFILE"; cd "$RUN" && "row_$ROW"' \
  >"$evidence/scope.out" 2>"$evidence/scope.err" &
runner=$!
while kill -0 "$runner" 2>/dev/null; do
  cg=$(systemctl --user show "$unit.scope" -p ControlGroup --value 2>/dev/null)
  if [ -n "$cg" ] && [ -r "/sys/fs/cgroup$cg/cgroup.procs" ]; then
    pids=$(paste -sd, "/sys/fs/cgroup$cg/cgroup.procs")
    if [ -n "$pids" ]; then
      stamp=$(date +%s)
      ps -ww -p "$pids" -o pid=,ppid=,rss=,vsz=,etimes=,args= 2>/dev/null |
        awk -v stamp="$stamp" '{print stamp, $0}' >>"$evidence/process-rss.txt"
      for p in ${pids//,/ }; do
        if [ -r "/proc/$p/status" ]; then
          awk -v stamp="$stamp" -v pid="$p" '/^Vm(HWM|RSS):/ {print stamp, pid, $0}' \
            "/proc/$p/status" >>"$evidence/process-hwm.txt" 2>/dev/null
          printf '%s %s %s\n' "$stamp" "$p" "$(readlink "/proc/$p/exe" 2>/dev/null)" >>"$evidence/process-exe.txt"
        fi
      done
    fi
    for metric in memory.current memory.peak memory.events; do
      if [ -r "/sys/fs/cgroup$cg/$metric" ]; then
        awk -v stamp="$(date +%s)" -v metric="$metric" '{print stamp, metric, $0}' \
          "/sys/fs/cgroup$cg/$metric" >>"$evidence/cgroup-memory.txt"
      fi
    done
    systemctl --user show "$unit.scope" -p MemoryMax -p MemoryPeak -p Result \
      >"$evidence/scope.properties" 2>/dev/null
  fi
  sleep 2
done
wait "$runner"
rc=$?
if systemctl --user show "$unit.scope" -p MemoryMax -p MemoryPeak -p Result >"$evidence/scope-final.properties" 2>/dev/null; then
  if [ -s "$evidence/scope.properties" ]; then cat "$evidence/scope.properties"; fi
fi
journalctl --user -u "$unit.scope" --no-pager >"$evidence/scope.log" 2>&1
# Retain the scratch world for diagnosis, including the last unfinished command.
# The driver stores command transcripts only once each subprocess returns.
printf 'exit=%s\nevidence=%s\nscratch=%s\n' "$rc" "$evidence" "$scratch"
awk 'NR>1 && $4>peak {peak=$4; pid=$2; line=$0} END {
  printf "peak_sampled_process_rss_kib=%d pid=%s\n%s\n", peak, pid, line
}' "$evidence/process-rss.txt"
if [ -f "$evidence/process-hwm.txt" ]; then
  awk '$3=="VmHWM:" && $4>peak {peak=$4; pid=$2} END {
    printf "peak_observed_process_hwm_kib=%d pid=%s\n", peak, pid
  }' "$evidence/process-hwm.txt"
fi
if [ -f "$evidence/cgroup-memory.txt" ]; then
  awk '$2=="memory.peak" && $3>peak {peak=$3} END {
    printf "peak_observed_scope_bytes=%d\n", peak
  }' "$evidence/cgroup-memory.txt"
fi
exit "$rc"
