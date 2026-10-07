#!/usr/bin/env bash
# merge-gate-checks.sh SRC FROM TO TAG  -- MERGE-KEEPER post-merge checks (run AFTER the umbrella
# `lake build Minidregg +Host.Main:leanArts ObjectiveProofs` is green in SRC at TO).
# Every check runs even after a red. Logs: <basedir>/logs/gate-TAG-<check>.log; summary
# <basedir>/logs/gate-TAG.summary (one line per check: name PASS|RED rc secs). Exit = number red.
# Rust: only the rows of scripts/check-rust-tests.sh whose crate FROM..TO touches (rust-rows.py).
set -u
SRC=$1 FROM=$2 TO=$3 TAG=$4
B=$(cd "$SRC/.." && pwd); H=$(cd "$(dirname "$0")" && pwd)
L=$B/logs; mkdir -p "$L"
S=$L/gate-$TAG.summary; : > "$S"
export PATH=$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.bun/bin:$PATH
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$B/rust-target}
export LOCAL_GATES_CARGO_JOBS=${LOCAL_GATES_CARGO_JOBS:-4}
cd "$SRC"
[ "$(git rev-parse HEAD)" = "$(git rev-parse "$TO")" ] || { echo "HEAD != $TO" | tee -a "$S"; exit 99; }
red=0
run() { local n=$1; shift; local s=$(date +%s); ( "$@" ) > "$L/gate-$TAG-$n.log" 2>&1; local rc=$?
  local st=PASS; [ $rc = 0 ] || { st=RED; red=$((red+1)); }
  echo "$n $st rc=$rc $(( $(date +%s) - s ))s :: $(tail -n 1 "$L/gate-$TAG-$n.log" | cut -c1-200)" | tee -a "$S"; }
# lean targets the range DECLARES (new [[lean_lib]]/[[lean_exe]] names in lakefile.toml) are built too:
# the umbrella does not reach a new exe root, CI's lake-build gate does
tnames() { git show "$1:lakefile.toml" | sed -n '/^\[\[lean_\(lib\|exe\)\]\]/{n;s/^name *= *"\(.*\)"$/\1/p}' | sort; }
newt=$(comm -13 <(tnames "$FROM") <(tnames "$TO") | grep -v '^ResearchWip$' | tr '\n' ' ')
if [ -n "$newt" ]; then run new-targets env LEAN_NUM_THREADS=${THREADS:-6} ${LAKE_WRAP:-nice -n 10} lake build $newt; fi
# EVERY lean_exe root, every batch (cv 01a1147a-f80e): the umbrella reaches none of the exe-only
# modules, so Compiler.ObjectiveBendCDiffGen sat red on main unseen and a range that broke
# Kernel/ConsentAnchor (outside Minidregg, inside minidregg-client-consent) would have landed.
exes=$(git show "$TO:lakefile.toml" | sed -n '/^\[\[lean_exe\]\]/{n;s/^name *= *"\(.*\)"$/\1/p}' | tr '\n' ' ')
run exe-roots env LEAN_NUM_THREADS=${THREADS:-6} ${LAKE_WRAP:-nice -n 10} lake build $exes
run host-closure    bash scripts/check-host-closure.sh
run import-boundary bash scripts/check-import-boundary.sh
run proof-hygiene   bash scripts/check-proof-hygiene.sh
run build-surfaces  python3 scripts/lean-build-surfaces.py check
# The pure-script pins local-gates runs and this list lacked (W20-GATE-MUTATION, 2026-10-05): each is
# seconds, none builds Lean. Mutants that each of them kills and this gate did not see: a new unrooted
# module (build-closure), an @[export] nothing calls (exports), an is_absolute() in a shell-line parser
# (shell-paths), a request byte routed without a Host receiver (host-operations), a stale SheetLaw embed
# (gen-sheetlaw), a stale status page (website).
run build-closure   bash -c 'bash scripts/check-build-closure.sh && python3 scripts/test_build_gate_boundaries.py && python3 scripts/test_lean_build_surfaces.py'
run exports         bash scripts/check-exports.sh
run unit-tests      bash scripts/check-unit-tests.sh
run policy-portal   bash scripts/check-canonical-policy-portal.sh
run shell-paths     bash scripts/check-shell-paths.sh
run host-operations bash -c 'python3 scripts/host-operations.py check && python3 scripts/test-host-operations.py'
run gen-sheetlaw    python3 scripts/gen-sheetlaw.py --check
run website         python3 website/gen-status.py --check
# A `sorry` or a declared axiom in a deployed module is only a WARNING to the umbrella build above
# (measured: `theorem t : 1 = 2 := sorry` in Compiler/DeclaredEffectCellRegistry builds green); the
# tree-wide axiom census is what turns it red. Deployed is built by the umbrella, so this elaborates
# Deployed + the census module only.
run axiom-census    ${LAKE_WRAP:-nice -n 10} lake build AxiomCensus
run objective-proofs bash scripts/check-objective-proofs.sh proofs
# The hypothesis ledger over AxiomCensusResearch. Its [RED] families on main are a known
# baseline (hyp-ledger-baseline.txt next to this script, ROOT 10-05: six toothless rows red on
# clean 259a2fb0); a batch is RED here only for a [RED] family outside that baseline, a failed
# self-test, or an instrument that did not run. KNOWN-RED is reported and does not count.
ledger() {
  local log="$L/gate-$TAG-hyp-ledger.log" s=$(date +%s) rc reds new st
  # the ledger's own imports too: scripts/HypothesisLedger.lean may import a module outside the
  # AxiomCensusResearch closure (kn2-hyp-ledger: Kernel.GenericSimplexObservationSafety), and the
  # ledger refuses to run on an absent olean
  local imports; imports=$(sed -n 's/^import \([A-Za-z0-9_.]*\).*/\1/p' scripts/HypothesisLedger.lean | tr '\n' ' ')
  ${LAKE_WRAP:-nice -n 10} lake build AxiomCensusResearch $imports > "$L/gate-$TAG-hyp-ledger-build.log" 2>&1 \
    || { echo "hyp-ledger RED (AxiomCensusResearch did not build)" | tee -a "$S"; red=$((red+1)); return; }
  bash scripts/check-hypothesis-ledger.sh > "$log" 2>&1; rc=$?
  reds=$(grep -aE '^[A-Za-z0-9_.]+ [|] [A-Z]+ [|] [A-Z]+ \[RED\]' "$log" | cut -d' ' -f1 | sort -u)
  new=$(comm -23 <(printf '%s\n' "$reds" | sed '/^$/d') <(sort -u "$H/hyp-ledger-baseline.txt") | tr '\n' ' ')
  if [ $rc = 0 ]; then st=PASS
  elif [ -n "$reds" ] && [ -z "$new" ] && ! grep -aq 'self-test .*: FAIL' "$log"; then st="KNOWN-RED($(printf '%s\n' "$reds" | wc -l) baseline)"
  else st="RED(new: ${new:-none}; self-test/instrument: see log)"; red=$((red+1)); fi
  echo "hyp-ledger $st rc=$rc $(( $(date +%s) - s ))s :: $(grep -ac 'self-test .*: PASS' "$log") self-tests pass" | tee -a "$S"
}
ledger
python3 "$H/rust-rows.py" "$SRC" "$FROM" "$TO" "$B/tmp-rust-rows-$TAG.sh" > "$L/gate-$TAG-rust-rows.txt" 2>&1 || { echo "rust-rows RED (selector failed)" | tee -a "$S"; red=$((red+1)); }
cat "$L/gate-$TAG-rust-rows.txt"
run rust-rows       ${LAKE_WRAP:-} bash "$B/tmp-rust-rows-$TAG.sh"
# non-Lean, non-Rust tests the change touches: deploy tooling, changed python test files
if git diff --name-only "$FROM..$TO" | grep -q '^deploy/'; then
  run deploy-scripts bash -c 'python3 deploy/pay/test-render-enrol.py && python3 deploy/candidate/test-package.py && bash deploy/candidate/test-lane-build.sh'
  run spk-shell bash scripts/check-spk-shell-tests.sh
fi
for f in $(git diff --name-only --diff-filter=AM "$FROM..$TO" | grep -E '(^|/)test_[^/]*\.py$'); do
  run "py-$(basename "$f" .py)" bash -c "cd $(dirname "$f") && python3 $(basename "$f")"
done
d=$(git status --porcelain --untracked-files=no | wc -l)
[ "$d" = 0 ] && echo "tracked-clean PASS" | tee -a "$S" || { echo "tracked-clean RED ($d tracked files changed)" | tee -a "$S"; git status --porcelain --untracked-files=no | head -20 >> "$S"; red=$((red+1)); }
echo "TOTAL red=$red HEAD=$(git rev-parse HEAD) $(date -Is)" | tee -a "$S"
exit $red
