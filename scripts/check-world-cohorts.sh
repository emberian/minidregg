#!/usr/bin/env bash
# check-world-cohorts.sh -- every world preview cohort, through the Lean front end.
#
# Runs tests/objective-bend-source/check-preview.ts over every world/*/preview-cohort.json and
# any other world/*/*cohort*.json (market's is market-cohort.json). A cohort is PASS only when
# check-preview exits 0 AND prints its pass marker ("status":"passed") AND the number of rows it
# checked equals the number of rows in the file; any mismatch of any row's `expected` is RED.
# Every cohort runs, even after a red one; the exit status is the number of red cohorts (plus one
# if the instrument self-test fails).
#
# SELF-TEST (every run, before the cohorts): the first row of the first cohort is copied with its
# `expected` flipped, and the check MUST refuse it. A gate that cannot go red is not a gate: if the
# planted wrong expectation passes, the instrument is dead and the gate is RED.
#
# Cohorts with no `world/*/*cohort*.json` at all are RED (a rename must not read as green).
# env: LAKE_ROOT  a built tree providing .lake/build/lib/lean (default: this checkout; read only)
#      BUN        bun binary (default: bun)
#      WORLD_COHORTS_ONLY="world/bounty ..."  run a subset (exits non-zero: the rest are NOT-RUN)
# Logs: build-logs/world-cohorts/.
set -uo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo" || exit 2
export PATH=$HOME/.elan/bin:$HOME/.bun/bin:$PATH
lake_root=${LAKE_ROOT:-$repo}
bun=${BUN:-bun}
logs=$repo/build-logs/world-cohorts; mkdir -p "$logs"
work=$(mktemp -d "${TMPDIR:-/tmp}/world-cohorts.XXXXXX")
only=${WORLD_COHORTS_ONLY:-}
export LEAN_NUM_THREADS=2
red=0

command -v "$bun" >/dev/null 2>&1 || { echo "world-cohorts: RED: needs bun: '$bun' not on PATH"; exit 1; }
command -v lean >/dev/null 2>&1 || { echo "world-cohorts: RED: needs warm base: no lean binary on PATH"; exit 1; }
if [ "$lake_root" = "$repo" ]; then lake build Host.ObjectiveBendFrontEnd >"$logs/build.log" 2>&1 || { echo "world-cohorts: RED: lake build Host.ObjectiveBendFrontEnd failed ($logs/build.log)"; exit 1; }; fi
[ -f "$lake_root/.lake/build/lib/lean/Host/ObjectiveBendFrontEnd.olean" ] \
  || { echo "world-cohorts: RED: needs warm base: no built front end under $lake_root"; exit 1; }
LEAN=$(cd "$lake_root" && lake env which lean) || exit 1
LEAN_PATH=$(cd "$lake_root" && lake env printenv LEAN_PATH) || exit 1
export LEAN LEAN_PATH

mapfile -t cohorts < <(find world -mindepth 2 -maxdepth 2 -name '*cohort*.json' | LC_ALL=C sort)
[ "${#cohorts[@]}" -gt 0 ] || { echo "world-cohorts: RED: no world/*/*cohort*.json found"; exit 1; }

rows_of() { python3 -c 'import json,sys;print(len(json.load(open(sys.argv[1]))))' "$1"; }
run_check() { "$bun" tests/objective-bend-source/check-preview.ts "$1" "$2" "$LEAN" "$LEAN_PATH"; }

# ---- instrument self-test: one planted wrong expectation must be refused ----------------------
selftest() {
  local src=${cohorts[0]}
  python3 - "$src" "$work/planted-cohort.json" <<'PY' || return 1
import json,os,sys
src,dst=sys.argv[1:3]
rows=json.load(open(src))
row=next(r for r in rows if "expected" in r and r.get("expectedStatus") is None)
row["modules"]=[{**m,"source":os.path.relpath(os.path.join(os.path.dirname(src),m["source"]),os.path.dirname(dst))} for m in row["modules"]]
e=row["expected"]
row["expected"]=(not e) if isinstance(e,bool) else (str(int(e)+1) if str(e).isdigit() else str(e)+"-PLANTED")
row["name"]="PlantedWrongExpectation"
json.dump([row],open(dst,"w"))
PY
  if run_check "$work/planted-cohort.json" "$work/planted-out" > "$logs/selftest.log" 2>&1; then
    echo "self-test: the planted wrong expectation PASSED (exit 0): the check cannot go red"; return 1
  fi
  grep -q 'actual typed source result differs: PlantedWrongExpectation' "$logs/selftest.log" \
    || { echo "self-test: refused, but not for the planted expectation (see $logs/selftest.log)"; return 1; }
  echo "self-test: a planted wrong expectation is refused"
}
if st=$(selftest 2>&1); then echo "world-cohorts: ok: $st ($logs/selftest.log)"
else red=$((red + 1)); echo "world-cohorts: RED: $(echo "$st" | tail -1)"; fi

total=0
for c in "${cohorts[@]}"; do
  name=$(dirname "$c")/$(basename "$c" .json)
  if [ -n "$only" ] && [[ " $only " != *" $(dirname "$c") "* ]]; then
    red=$((red + 1)); echo "world-cohorts: RED: $c: not in WORLD_COHORTS_ONLY"; continue
  fi
  log=$logs/$(echo "$name" | tr / _).log
  n=$(rows_of "$c")
  run_check "$c" "$work/$(echo "$name" | tr / _)" > "$log" 2>&1; rc=$?
  if [ "$rc" != 0 ]; then
    red=$((red + 1)); echo "world-cohorts: RED: $c: exit $rc; $(grep -v '^[[:space:]]*$' "$log" | tail -1 | cut -c1-300) ($log)"
  elif ! grep -q '"status":"passed"' "$log"; then
    red=$((red + 1)); echo "world-cohorts: RED: $c: exit 0 but no passed marker ($log)"
  else
    k=$(python3 -c 'import json,sys;print(len(json.load(open(sys.argv[1]))["sourceResults"]))' <(grep '"status":"passed"' "$log" | tail -1))
    if [ "$k" != "$n" ]; then red=$((red + 1)); echo "world-cohorts: RED: $c: $n rows in the file, $k checked ($log)"
    else total=$((total + n)); echo "world-cohorts: ok: $c: $n rows passed"; fi
  fi
done
echo "world-cohorts: $red red of $((${#cohorts[@]} + 1)) checks ($total cohort rows passed over ${#cohorts[@]} cohorts; work $work)"
[ "$red" = 0 ] && echo "WORLD COHORTS PASS: ${#cohorts[@]} cohorts, $total rows"
exit "$red"
