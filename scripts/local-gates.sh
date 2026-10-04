#!/usr/bin/env bash
# The one gate. EVERY gate runs, even after an earlier one is red (the first red
# must not hide the second); the exit status is the number of red gates (0 =
# PASS). Each gate's output goes to stdout and to build-logs/local-gates/NAME.log;
# the end is a one-line-per-gate summary with wall seconds. No fallback, no skip.
#
#   host-operations request-byte allocations match Host receivers and socket routes; mutation checks
#   hygiene        no bare `#print axioms`, no project `axiom`; Assurance/SheetLaw.lean
#                  §2 is the embed of the MUD sheet JSON (scripts/gen-sheetlaw.py --check)
#   lake-build     builds declared qualification libraries and executables; ResearchWip
#                  is an explicit opt-in source target. Successful builds compare their
#                  pinned axiom footprints and link the declared executables.
#   cold-start     the native Host starts without doing work (scripts/check-host-cold-start.sh:
#                  peak RSS and CPU of a bare start; a computable nullary def in a module
#                  the Host links runs at every Host start)
#   hyp-ledger     scripts/check-hypothesis-ledger.sh over AxiomCensusResearch (built by
#                  lake-build): no VACUOUS/INCONSISTENT row, no un-allowlisted TOOTHLESS
#                  assumption, no stale allowlist entry; self-tests its instrument each run
#   objective-proofs   ObjectiveProofs built; every Theory/ObjectiveBend* statement and
#                  exact axiom set equals scripts/gates/objective-{statements.snapshot,axioms.pin}
#                  (scripts/check-objective-proofs.sh proofs; self-tests its instrument each run)
#   objective-c    the C backend differential against runBounded, State bytes included
#                  (scripts/check-objective-proofs.sh c; needs bun)
#   drift          the build changed no tracked file (Lean-emitted descriptors, vectors,
#                  glue); compared against the tree as it stood before the build
#   prover-glue    the Lean-emitted prover glue is byte-identical to what its source emits
#   build-closure  source classification/target coverage and gate regression tests
#   host-closure   the import closure of Host.Main equals scripts/gates/host-closure.pin
#   import-tiers   every import is inside the tier table of scripts/check-import-boundary.sh
#   exports        every @[export] is called from native/ or allowlisted with a reason
#   shell-paths    no shell-line parser confines a friend-typed path by is_absolute();
#                  paths go through shell::session_fs (scripts/check-shell-paths.sh; self-tests)
#   objective-frontend  the Objective Bend front end (scripts/check-objective-frontend.sh), all through
#                  the Lean front end: identity manifest, elaboration cohort, C4 vectors, parser,
#                  preview cohort, typed examples, and the tutorial re-run; a row with no built
#                  tree is RED ("needs warm base")
#   website        website/status.html is what website/gen-status.py generates from README.md's
#                  Honest state table, and every <pre data-source=PATH> block on a page is text
#                  of PATH; two controls (a mutated README row, a mutated block) must be refused
#   rust-tests     the filtered native test lines of scripts/check-rust-tests.sh
#   deploy-scripts the deploy tooling's own tests, no Lean/Rust build: candidate packager (consent pair
#                  required; stub roles), lane-build pack refusals, self-enrollment terms renderer
#                  (50 DREGG/week -> tariff integers)
#   spk-shell      every deploy/spk-host/tests/*.sh (scripts/check-spk-shell-tests.sh);
#                  a skip (exit 77) is red
#   journey        native/resource-client/journey.sh from this tree on a fresh Store
#                  (scripts/check-journey.sh; G at 1000 records unless
#                  LOCAL_GATES_GROWTH_LEVELS says otherwise, and then G is UNMEASURED)
#
# LOCAL_GATES_ONLY="name ..." runs a subset for debugging; such a run always exits
# non-zero (the gates it did not run are listed as NOT-RUN), so it can never read green.
set -uo pipefail
repo_root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$repo_root"
export PATH=$HOME/.elan/bin:$PATH
lake=${LAKE:-lake}
logdir=$repo_root/build-logs/local-gates
mkdir -p "$logdir"
# Read target declarations so newly added qualification libraries enter the gate.
# ResearchWip is classified source awaiting qualification and remains opt-in.
lib_targets=$(sed -n '/^\[\[lean_lib\]\]/{n;s/^name *= *"\(.*\)"$/\1/p}' lakefile.toml | grep -v '^ResearchWip$' | tr '\n' ' ')
exe_targets=$(sed -n '/^\[\[lean_exe\]\]/{n;s/^name *= *"\(.*\)"$/\1/p}' lakefile.toml | tr '\n' ' ')

GATES=(host-operations hygiene lake-build cold-start hyp-ledger objective-proofs objective-c drift prover-glue build-closure host-closure import-tiers exports shell-paths objective-frontend website rust-tests deploy-scripts spk-shell journey)
declare -A STATUS SECS LAST
red=0
only=${LOCAL_GATES_ONLY:-}

g_host-operations() { python3 scripts/host-operations.py check && python3 scripts/test-host-operations.py; }
g_hygiene()       { bash scripts/check-proof-hygiene.sh && python3 scripts/gen-sheetlaw.py --check; }
g_lake-build()    { echo "ResearchWip is opt-in; source classification is checked separately."; echo "lake build $lib_targets$exe_targets"; "$lake" build $lib_targets $exe_targets; }
g_cold-start()    { bash scripts/check-host-cold-start.sh .lake/build/bin/minidregg-host; }
g_hyp-ledger()    { bash scripts/check-hypothesis-ledger.sh; }
g_objective-proofs() { bash scripts/check-objective-proofs.sh proofs; }
g_objective-c()      { bash scripts/check-objective-proofs.sh c; }
g_drift() {
  local after; after=$(git diff --binary | git hash-object --stdin)
  if [[ "$tree_before" != "$after" ]]; then
    git diff --stat
    echo "drift: the build rewrote tracked files; commit the Lean-emitted copies"; return 1
  fi
  echo "drift: the build changed no tracked file"
}
g_prover-glue()   { bash scripts/check-prover-glue.sh; }
g_build-closure() { bash scripts/check-build-closure.sh && python3 scripts/test_build_gate_boundaries.py && python3 scripts/test_lean_build_surfaces.py; }
g_host-closure()  { bash scripts/check-host-closure.sh; }
g_import-tiers()  { bash scripts/check-import-boundary.sh; }
g_exports()       { bash scripts/check-exports.sh; }
g_shell-paths()   { bash scripts/check-shell-paths.sh; }
g_objective-frontend() { bash scripts/check-objective-frontend.sh; }
g_website()       { python3 website/gen-status.py --check; }
g_rust-tests()    { bash scripts/check-rust-tests.sh; }
g_deploy-scripts() { python3 deploy/pay/test-render-enrol.py && python3 deploy/candidate/test-package.py && bash deploy/candidate/test-lane-build.sh; }
g_spk-shell()     { bash scripts/check-spk-shell-tests.sh; }
g_journey()       { bash scripts/check-journey.sh; }

tree_before=$(git diff --binary | git hash-object --stdin)
t_all=$(date +%s)
for g in "${GATES[@]}"; do
  if [ -n "$only" ] && [[ " $only " != *" $g "* ]]; then
    STATUS[$g]=NOT-RUN; SECS[$g]=0; LAST[$g]="not in LOCAL_GATES_ONLY"; red=$((red + 1)); continue
  fi
  echo "== gate $g"
  t0=$(date +%s)
  "g_$g" 2>&1 | tee "$logdir/$g.log"
  rc=${PIPESTATUS[0]}
  SECS[$g]=$(( $(date +%s) - t0 ))
  LAST[$g]=$(grep -v '^[[:space:]]*$' "$logdir/$g.log" | tail -1 | cut -c1-150)
  if [ "$rc" = 0 ]; then STATUS[$g]=PASS; else STATUS[$g]=FAIL; red=$((red + 1)); fi
  echo "== gate $g: ${STATUS[$g]} (${SECS[$g]} s)"
done

{
  printf '\n%-14s %-7s %7s  %s\n' gate status wall_s "last line"
  for g in "${GATES[@]}"; do
    printf '%-14s %-7s %7s  %s\n' "$g" "${STATUS[$g]}" "${SECS[$g]}" "${LAST[$g]}"
  done
  printf 'gates: %s red of %s (%s s total; rev %s%s)\n' "$red" "${#GATES[@]}" "$(( $(date +%s) - t_all ))" \
    "$(git rev-parse --short HEAD)" "$([ -n "$(git status --porcelain --untracked-files=no)" ] && echo ' + uncommitted edits')"
} | tee "$logdir/summary.txt"
[ "$red" = 0 ] && echo "gates: PASS"
exit "$red"
