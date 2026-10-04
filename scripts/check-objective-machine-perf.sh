#!/usr/bin/env bash
# Regression row: the compiled Lean Core4 machine (the code admission
# re-execution runs) must stay fast. Runs the StressWork packet
# (native/objective-emit/Stress.obend, work(14): 524,293 ticks, 49,163 heap
# cells) through `runBounded` and `forceWith` as compiled under the
# ObjectiveBendDemandMachineFast @[csimp] lemmas, and FAILS if either takes more
# than MINI_OBJECTIVE_MACHINE_MS milliseconds (default 2000; measured ~40 ms on
# hbox; the specification's own compiled code takes 11-16 s, so the bound
# separates the two by an order of magnitude on either side).
#
# usage: scripts/check-objective-machine-perf.sh [--side fast|reference] [--core CORE_JSON] [--bin DIR]
#   --core      a source.core.json for StressWork already produced by
#               native/objective-emit/packets.ts (otherwise bun produces it)
#   --bin       drivers already built by native/objective-emit/fastmachine/build.sh
#               (otherwise the row builds them)
#   --side reference   runs the specification's code instead: the control, it must FAIL
set -euo pipefail
repo=$(cd "$(dirname "$0")/.." && pwd)
side=fast; core=""; bin=""
while [ $# -gt 0 ]; do
  case "$1" in
    --side) side=$2; shift 2 ;;
    --core) core=$2; shift 2 ;;
    --bin) bin=$2; shift 2 ;;
    *) echo "usage: $0 [--side fast|reference] [--core CORE_JSON] [--bin DIR]" >&2; exit 2 ;;
  esac
done
case "$side" in fast|reference) ;; *) echo "--side fast|reference" >&2; exit 2 ;; esac
bound=${MINI_OBJECTIVE_MACHINE_MS:-2000}
work=$(mktemp -d "${TMPDIR:-/tmp}/objective-machine-perf.XXXXXX")
trap 'rm -rf "$work"' EXIT
if [ -z "$core" ]; then
  command -v bun >/dev/null || { echo "objective-machine-perf: FAIL no bun to produce the StressWork packet (pass --core)"; exit 1; }
  printf '[{"name":"StressWork","modules":[{"name":"Stress","source":"%s"}],"entry":"work","arguments":["14"]}]\n' \
    "$repo/native/objective-emit/Stress.obend" > "$work/cohort.json"
  bun "$repo/native/objective-emit/packets.ts" "$work/packets" "$work/cohort.json" >/dev/null
  core=$work/packets/StressWork/source.core.json
fi
[ -f "$core" ] || { echo "objective-machine-perf: FAIL no core packet at $core"; exit 1; }
if [ -z "$bin" ]; then
  bin=$work/bin
  "$repo/native/objective-emit/fastmachine/build.sh" "$bin" >"$work/build.log" 2>&1 ||
    { tail -20 "$work/build.log"; echo "objective-machine-perf: FAIL driver build"; exit 1; }
fi
status=0
for mode in run force; do
  line=$("$bin/objective-machine-$side" bench "$core" "$mode")
  echo "$line"
  verdict=$(python3 - "$line" "$mode" "$bound" <<'PY'
import json, sys
r = json.loads(sys.argv[1]); mode = sys.argv[2]; bound = float(sys.argv[3])
# the workload must be the one the bound was set for, or the bound means nothing
if r["outcome"] != "finished" or r["heap"] != 49163 or (mode == "force" and r["ticks"] != 524293):
    print(f"FAIL workload changed: {r}")
elif r["ms"] > bound:
    print(f"FAIL {mode} {r['ms']:.1f} ms > {bound:.0f} ms")
else:
    print(f"PASS {mode} {r['ms']:.1f} ms <= {bound:.0f} ms")
PY
)
  echo "objective-machine-perf: $side $verdict"
  case "$verdict" in PASS*) ;; *) status=1 ;; esac
done
exit $status
