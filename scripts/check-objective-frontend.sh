#!/usr/bin/env bash
# check-objective-frontend.sh — the Objective Bend front end as one gate.
#
# Every row runs, even after a red one. A row is PASS only when its command exits 0
# AND its own log carries the row's pass marker (a check that stops printing its
# verdict is red, not green: the verdict is read from the artifact, not the exit code
# alone). The exit status is the number of red rows. Logs: build-logs/objective-frontend/.
#
# There is one front end, in Lean (Host/ObjectiveBendFrontEnd: Compiler/ObjectiveBendParse,
# Compiler/ObjectiveBendElaborate, Compiler/ObjectiveBendC4); every row drives it. Rows need a
# built Lean tree (LAKE_ROOT, default this checkout, where the needed modules are built first):
#     identity          the compiled-in front-end identity's manifest equals sha256sum of the
#                       listed source files (the pin names exactly these bytes)
#     elaborate-tests   tests/objective-bend-source/check-elaborate.ts (the elaboration cohort)
#     c4-tests          Compiler/ObjectiveBendC4Vectors: pommette vectors, refusals and the
#                       ordered-presentation invariance on 4000 seeded DAGs (compiled theorems)
#     check-parser      tests/objective-bend-source/check-parser.ts
#     check-preview     tests/objective-bend-source/check-preview.ts over preview-cohort.json
#     ltuo-probes       tests/objective-bend-source/ltuo/check-probes.ts: the LTUO characterization
#                       probes, each pinned at its CURRENT outcome with the TARGET its LT row owes
#                       (a target met without promoting the pin is red, as is any other move)
#     publication       tests/objective-native/PublicationReplay.lean: what the Host publishes is
#                       what the receiver's replay recomputes; foreign pin, changed source and
#                       tampered core are refused
#     activity-replay   tests/objective-native/ActivityReplay.lean: the activity kernel replays
#                       the package stored with an activity artifact and loads the program
#                       from it; foreign core, foreign front end, missing package and another
#                       source are refused
#     examples          scripts/check-objective-examples.sh (typed packets, drivers, cohort)
#     tutorial          scripts/check-objective-tutorial.ts: every command block of
#                       docs/OBJECTIVE-BEND-TUTORIAL.md re-run through docs/tutorial/run.ts
#
# A row with no lean binary or no built front end is RED and says "needs warm base":
# nothing is skipped and nothing falls back.
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
ROWS=(identity elaborate-tests c4-tests check-parser check-preview ltuo-probes publication activity-replay examples tutorial)
declare -A STATUS
red=0

need_bun() { command -v "$bun" >/dev/null 2>&1 || { echo "needs bun: '$bun' not on PATH"; return 1; }; }
need_lean() {
  command -v lean >/dev/null 2>&1 || { echo "needs warm base: no lean binary on PATH"; return 1; }
  if [ "$lake_root" = "$repo" ]; then
    lake build Host.ObjectiveBendFrontEnd Host.ObjectivePackageAuthor Compiler.ObjectiveBendC4Vectors \
      Kernel.ObjectiveActivity || return 1
  fi
  [ -f "$lake_root/.lake/build/lib/lean/Host/ObjectiveBendFrontEnd.olean" ] \
    || { echo "needs warm base: no built front end (Host/ObjectiveBendFrontEnd.olean) under $lake_root"; return 1; }
}
lean_path() { (cd "$lake_root" && lake env printenv LEAN_PATH); }
front_env() { LEAN=$(cd "$lake_root" && lake env which lean) && LEAN_PATH=$(lean_path) && export LEAN LEAN_PATH; }

r_identity() {
  need_lean && front_env || return 1
  "$LEAN" --run Host/ObjectiveBendFrontEndMain.lean identity > "$work/identity.json" || return 1
  python3 - "$work/identity.json" <<'PY'
import hashlib,json,sys
j=json.load(open(sys.argv[1]));lines=j["manifest"].rstrip("\n").split("\n")
assert lines[0]=="DREGG/OBJECTIVE-BEND/FRONT-END/v1",lines[0]
for line in lines[1:]:
  name,digest=line.split(" ")
  actual=hashlib.sha256(open("Compiler/"+name,"rb").read()).hexdigest()
  assert actual==digest,f"{name}: compiled-in {digest}, on disk {actual} (stale build)"
assert hashlib.sha256(j["manifest"].encode()).hexdigest()==j["frontEnd"],"identity is not the manifest hash"
print("FRONT-END IDENTITY PASS: "+j["frontEnd"]+" = sha256 of the manifest of "+str(len(lines)-1)+" source files, each matching the checkout")
PY
}
r_elaborate-tests() { need_bun && need_lean && front_env && "$bun" tests/objective-bend-source/check-elaborate.ts; }
r_c4-tests() {
  need_lean && front_env || return 1
  printf 'import Compiler.ObjectiveBendC4Vectors\n#eval IO.println Minidregg.Compiler.ObjectiveBendC4Vectors.summary\n' > "$work/c4.lean"
  "$LEAN" "$work/c4.lean"
}
r_check-parser()    { need_bun && need_lean && front_env && "$bun" tests/objective-bend-source/check-parser.ts; }
r_check-preview()   {
  need_bun && need_lean && front_env || return 1
  "$bun" tests/objective-bend-source/check-preview.ts tests/objective-bend-source/preview-cohort.json \
    "$work/preview" "$LEAN" "$LEAN_PATH"
}
r_ltuo-probes()     {
  need_bun && need_lean && front_env || return 1
  "$bun" tests/objective-bend-source/ltuo/check-probes.ts tests/objective-bend-source/ltuo/probe-cohort.json \
    "$work/ltuo-probes" "$LEAN" "$LEAN_PATH"
}
r_publication()     {
  need_lean && front_env || return 1
  "$LEAN" --run tests/objective-native/PublicationReplay.lean world/NativeReceipt.obend note
}
r_activity-replay() {
  need_lean && front_env || return 1
  "$LEAN" --run tests/objective-native/ActivityReplay.lean world/activity/Tally.obend tally
}
r_examples()        {
  need_bun && need_lean || return 1
  LAKE_ROOT=$lake_root BUN=$bun WORK=$work/examples bash scripts/check-objective-examples.sh
}
r_tutorial()        { need_bun && need_lean && front_env && "$bun" scripts/check-objective-tutorial.ts; }
# The marker each row must print (extended regex); a row with no marker line is red.
declare -A MARK=(
  [identity]='^FRONT-END IDENTITY PASS: [0-9a-f]{64} '
  [elaborate-tests]='^EVERY OBEND ELABORATES: [0-9]+ files$'
  [c4-tests]='^C4 ORDERED-PRESENTATION INVARIANCE PASS'
  [check-parser]='^EVERY OBEND PARSES: [0-9]+ files$'
  [check-preview]='"status":"passed"'
  [ltuo-probes]='^LTUO PROBES CURRENT: [0-9]+ rows pinned'
  [publication]='^PUBLICATION REPLAY PASS: '
  [activity-replay]='^ACTIVITY REPLAY PASS: '
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
