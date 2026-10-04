#!/usr/bin/env bash
# check-objective-frontend.sh — the Objective Bend front end as one gate.
#
# Every row runs, even after a red one. A row is PASS only when its command exits 0
# AND its own log carries the row's pass marker (a check that stops printing its
# verdict is red, not green: the verdict is read from the artifact, not the exit code
# alone). The exit status is the number of red rows. Logs: build-logs/objective-frontend/.
#
#   TypeScript only (bun):
#     elaborate-tests   native/bend-source/objective-elaborate-tests.ts
#     c4-tests          native/bend-source/objective-c4-tests.ts (pommette vectors, 4000 DAGs)
#     check-parser      tests/objective-bend-source/check-parser.ts
#   Need a built Lean tree (LAKE_ROOT, default this checkout) with the Theory oleans:
#     check-preview     tests/objective-bend-source/check-preview.ts over preview-cohort.json
#     elaborate-tv      translation validation: Compiler/ObjectiveBendElaborate (Lean) against
#                       the TS elaborator; builds Compiler.ObjectiveBendElaborate first, which
#                       no default lake target does (it is in ResearchWip only)
#     examples          scripts/check-objective-examples.sh (typed packets, drivers, cohort)
#     tutorial          scripts/check-objective-tutorial.ts: every command block of
#                       docs/OBJECTIVE-BEND-TUTORIAL.md re-run through docs/tutorial/run.ts
#
# A Lean row with no lean binary, no Theory oleans or no Compiler/ObjectiveBendElaborate.olean
# is RED and says "needs warm base": nothing is skipped and nothing falls back.
# env: LAKE_ROOT  a built tree providing .lake/build/lib/lean (default: this checkout; when it
#                 is another tree it is only read, never built into)
#      BUN        bun binary (default: bun)
#      OBJECTIVE_FRONTEND_ONLY="row ..."  run a subset (exits non-zero: NOT-RUN rows are red)
set -uo pipefail
repo=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo" || exit 2
export PATH=$HOME/.elan/bin:$HOME/.bun/bin:$PATH
lake_root=${LAKE_ROOT:-$repo}
bun=${BUN:-bun}
logs=$repo/build-logs/objective-frontend; mkdir -p "$logs"
work=$(mktemp -d "${TMPDIR:-/tmp}/objective-frontend.XXXXXX")
only=${OBJECTIVE_FRONTEND_ONLY:-}
export LEAN_NUM_THREADS=2
ROWS=(elaborate-tests c4-tests check-parser check-preview elaborate-tv examples tutorial)
declare -A STATUS
red=0

need_bun() { command -v "$bun" >/dev/null 2>&1 || { echo "needs bun: '$bun' not on PATH"; return 1; }; }
need_lean() {
  command -v lean >/dev/null 2>&1 || { echo "needs warm base: no lean binary on PATH"; return 1; }
  [ -d "$lake_root/.lake/build/lib/lean/Theory" ] || { echo "needs warm base: no built Theory oleans under $lake_root/.lake/build/lib/lean"; return 1; }
}
need_elaborator_olean() {
  if [ "$lake_root" = "$repo" ]; then
    lake build Compiler.ObjectiveBendElaborate || return 1
  fi
  [ -f "$lake_root/.lake/build/lib/lean/Compiler/ObjectiveBendElaborate.olean" ] \
    || { echo "needs warm base: Compiler/ObjectiveBendElaborate.olean is not built under $lake_root"; return 1; }
}
lean_path() { (cd "$lake_root" && lake env printenv LEAN_PATH); }

r_elaborate-tests() { need_bun && "$bun" native/bend-source/objective-elaborate-tests.ts; }
r_c4-tests()        { need_bun && "$bun" native/bend-source/objective-c4-tests.ts; }
r_check-parser()    { need_bun && "$bun" tests/objective-bend-source/check-parser.ts; }
r_check-preview()   {
  need_bun && need_lean || return 1
  local lean; lean=$(cd "$lake_root" && lake env which lean) || return 1
  "$bun" tests/objective-bend-source/check-preview.ts tests/objective-bend-source/preview-cohort.json \
    "$work/preview" "$lean" "$lake_root/.lake/build/lib/lean" "$(command -v "$bun")"
}
r_elaborate-tv()    {
  need_bun && need_lean && need_elaborator_olean || return 1
  local lp; lp=$(lean_path) || return 1
  "$bun" native/bend-source/objective-elaborate-tv.ts "$work/tv" env "LEAN_PATH=$lp" lean --run Host/ObjectiveBendElaborateRun.lean
}
r_examples()        {
  need_bun && need_lean || return 1
  LAKE_ROOT=$lake_root BUN=$bun WORK=$work/examples bash scripts/check-objective-examples.sh
}
r_tutorial()        {
  need_bun && need_lean || return 1
  LEAN=$(cd "$lake_root" && lake env which lean) OLEAN_ROOT=$lake_root/.lake/build/lib/lean "$bun" scripts/check-objective-tutorial.ts
}
# The marker each row must print (extended regex); a row with no marker line is red.
declare -A MARK=(
  [elaborate-tests]='^EVERY OBEND ELABORATES: [0-9]+ files$'
  [c4-tests]='^C4 ORDERED-PRESENTATION INVARIANCE PASS'
  [check-parser]='^EVERY OBEND PARSES: [0-9]+ files$'
  [check-preview]='"status":"passed"'
  [elaborate-tv]='"status":"passed"'
  [examples]='^results: '
  [tutorial]='^TUTORIAL PASS: [0-9]+ commands'
)

for row in "${ROWS[@]}"; do
  if [ -n "$only" ] && [[ " $only " != *" $row "* ]]; then
    STATUS[$row]=NOT-RUN; red=$((red + 1)); echo "objective-frontend: RED: $row: not in OBJECTIVE_FRONTEND_ONLY"; continue
  fi
  log=$logs/$row.log
  "r_$row" >"$log" 2>&1; rc=$?
  marker=${MARK[$row]}
  if [ "$rc" != 0 ]; then
    STATUS[$row]=RED; red=$((red + 1))
    echo "objective-frontend: RED: $row: exit $rc; $(grep -v '^[[:space:]]*$' "$log" | tail -1 | cut -c1-200) ($log)"
  elif ! grep -Eq "$marker" "$log"; then
    STATUS[$row]=RED; red=$((red + 1))
    echo "objective-frontend: RED: $row: exit 0 but no line matches /$marker/ ($log)"
  elif [ "$row" = examples ] && grep -q '^FAIL' "$(sed -n 's/^results: //p' "$log" | tail -1)"; then
    STATUS[$row]=RED; red=$((red + 1))
    echo "objective-frontend: RED: $row: a FAIL row in $(sed -n 's/^results: //p' "$log" | tail -1) ($log)"
  else
    STATUS[$row]=PASS
    echo "objective-frontend: ok: $row: $(grep -E "$marker" "$log" | tail -1 | cut -c1-160)"
  fi
done
echo "objective-frontend: $red red of ${#ROWS[@]} rows (work $work)"
exit "$red"
