#!/usr/bin/env bash
# scripts/burst/cold-build.sh [--tip SHA] -- ONE cold umbrella build of $SRV/mini at TIP (default: its HEAD):
# Mathlib cache, then `lake build Minidregg +Host.Main:leanArts ObjectiveProofs` under swarm-build (COLD_MEM 64G)
# in the gate slot when the box has one. Result file $SRV/mini-logs/cold-build-<ts>.result (tip, rc, walls).
set -uo pipefail
SRV=${SRV:-/srv}; [ -f "$SRV/pipeline/box.env" ] && . "$SRV/pipeline/box.env"
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$PATH
tip=""; while [ $# -gt 0 ]; do case "$1" in --tip) tip=$2; shift 2 ;; *) echo "cold-build: unknown $1" >&2; exit 64 ;; esac; done
cd "$SRV/mini" || exit 1
if [ -n "$tip" ]; then git cat-file -e "$tip^{commit}" 2>/dev/null || git fetch -q origin "$tip"; git checkout -q -B main "$tip" || { echo "checkout $tip failed"; exit 1; }; fi
TIP=$(git rev-parse HEAD); TS=$(date -u +%Y%m%dT%H%M%SZ); R=$SRV/mini-logs/cold-build-$TS.result
echo "tip=$TIP" > "$R"; echo "cache_start=$(date -Is)" >> "$R"; s0=$(date +%s)
lake exe cache get > "$SRV/mini-logs/cache-get-$TS.log" 2>&1; echo "cache_rc=$? cache_wall=$(( $(date +%s)-s0 ))s" >> "$R"
echo "build_start=$(date -Is)" >> "$R"; s1=$(date +%s)
wrap=""; [ -x "$SRV/pipeline/scripts/slot-mk.sh" ] && wrap="$SRV/pipeline/scripts/slot-mk.sh"
SWARM_BUILD_TAG=cold-build SWARM_MEM_MAX=${COLD_MEM:-64G} LEAN_NUM_THREADS=${COLD_THREADS:-$(nproc)} $wrap swarm-build lake build Minidregg +Host.Main:leanArts ObjectiveProofs > "$SRV/mini-logs/cold-build-$TS.log" 2>&1
rc=$?
echo "build_rc=$rc build_wall=$(( $(date +%s)-s1 ))s build_end=$(date -Is)" >> "$R"
echo "built_lines=$(grep -c '\] Built ' "$SRV/mini-logs/cold-build-$TS.log")" >> "$R"
ln -sfn "cold-build-$TS.log" "$SRV/mini-logs/cold-build-latest.log"; ln -sfn "cold-build-$TS.result" "$SRV/mini-logs/cold-build-latest.result"
cat "$R"; exit $rc
