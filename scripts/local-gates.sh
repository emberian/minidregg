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
#   fn-wire        fn's exported wire grammar (protocol/fn/wire-grammar.json at the fn revision
#                  Compiler/FnWirePinned.lean pins) through Mini's one interpreter: pinned BLAKE3,
#                  every vector's exact decoder answer, planted-fault controls (scripts/check-fn-wire.sh;
#                  FN_REPO=<fn clone> also compares the file with fn's at that revision)
#   hyp-ledger     scripts/check-hypothesis-ledger.sh over AxiomCensusResearch (built by
#                  lake-build): no VACUOUS/INCONSISTENT row, no un-allowlisted TOOTHLESS
#                  assumption, no stale allowlist entry; self-tests its instrument each run
#   native-transcripts every recorded verifier transcript (CredentialSignatureIO.Transcript; the
#                  one Assurance.NativeAcceptedFixture replays the first native Objective acceptance
#                  with) is still the pinned verifier's answer: scripts/check-native-transcripts.sh
#                  lists them all from AxiomCensusResearch and re-submits each triple (verified; a
#                  flipped signature byte must read invalid)
#   objective-proofs   ObjectiveProofs built; every Theory/ObjectiveBend* statement and
#                  exact axiom set equals scripts/gates/objective-{statements.snapshot,axioms.pin}
#                  (scripts/check-objective-proofs.sh proofs; self-tests its instrument each run)
#   objective-c    the C backend differential against runBounded, State bytes included
#                  (scripts/check-objective-proofs.sh c; needs bun)
#   objective-cgen the same differential over 1000 GENERATED well-typed Core4 programs (fixed seeds), with two
#                  planted runtime.c miscompiles that must each turn it red (scripts/check-objective-proofs.sh cgen)
#   drift          the build changed no tracked file and emitted no new untracked one (Lean-emitted descriptors, vectors,
#                  glue); compared against the tree as it stood before the build
#   prover-glue    the Lean-emitted prover glue is byte-identical to what its source emits
#   build-closure  source classification/target coverage, the obsolete-policy-verifier source scan, and gate regression tests
#   unit-tests     the python unittest modules no other gate ran (scripts/gates/unit-tests.tsv: a floor of tests per
#                  module, known-red rows that must still fail, a new test_*.py in no row is red)
#   host-closure   the import closure of Host.Main equals scripts/gates/host-closure.pin
#   import-tiers   every import is inside the tier table of scripts/check-import-boundary.sh
#   exports        every @[export] is called from native/ or allowlisted with a reason
#   shell-paths    no shell-line parser confines a friend-typed path by is_absolute();
#                  paths go through shell::session_fs (scripts/check-shell-paths.sh; self-tests)
#   objective-frontend  the Objective Bend front end (scripts/check-objective-frontend.sh), all through
#                  the Lean front end: identity manifest, elaboration cohort, C4 vectors, parser,
#                  preview cohort, typed examples, and the tutorial re-run; a row with no built
#                  tree is RED ("needs warm base")
#   world-cohorts every world/*/*cohort*.json (the worlds ported from Bread: bounty, play, story,
#                  market, commons, ...) run through the Lean front end preview, every row checked
#                  against its `expected`; a row count that differs from the file is red, and a
#                  planted wrong expectation must be refused each run (scripts/check-world-cohorts.sh)
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

GATES=(host-operations hygiene lake-build cold-start fn-wire hyp-ledger native-transcripts objective-proofs objective-c objective-cgen drift prover-glue build-closure unit-tests host-closure import-tiers exports shell-paths objective-frontend world-cohorts website rust-tests deploy-scripts spk-shell journey)
declare -A STATUS SECS LAST
red=0
only=${LOCAL_GATES_ONLY:-}

g_host-operations() { python3 scripts/host-operations.py check && python3 scripts/test-host-operations.py; }
g_hygiene()       { bash scripts/check-proof-hygiene.sh && python3 scripts/gen-sheetlaw.py --check; }
g_lake-build()    { echo "ResearchWip is opt-in; source classification is checked separately."; echo "lake build $lib_targets$exe_targets"; "$lake" build $lib_targets $exe_targets; }
g_cold-start()    { bash scripts/check-host-cold-start.sh .lake/build/bin/minidregg-host; }
g_fn-wire()       { bash scripts/check-fn-wire.sh; }
g_hyp-ledger()    { bash scripts/check-hypothesis-ledger.sh; }
g_native-transcripts() { bash scripts/check-native-transcripts.sh; }
g_objective-proofs() { bash scripts/check-objective-proofs.sh proofs; }
g_objective-c()      { bash scripts/check-objective-proofs.sh c; }
g_objective-cgen()   { bash scripts/check-objective-proofs.sh cgen; }
# The state the drift gate compares: tracked changes AND the names and bytes of untracked,
# non-ignored files. A build that EMITS a new descriptor or vector nobody committed is drift too
# (W20 mutant drift-new-untracked); the gates' own logs and caches are not.
tree_state() {
  { git diff --binary
    git ls-files --others --exclude-standard -z | grep -zvE '^(build-logs/|target-gates/)|(^|/)__pycache__/' | xargs -0 -r sha256sum
  } | git hash-object --stdin
}
g_drift() {
  local after; after=$(tree_state)
  if [[ "$tree_before" != "$after" ]]; then
    git diff --stat; git ls-files --others --exclude-standard | grep -vE '^(build-logs/|target-gates/)|(^|/)__pycache__/' | sed 's/^/  new untracked: /'
    echo "drift: the build rewrote tracked files or emitted new ones; commit the Lean-emitted copies"; return 1
  fi
  echo "drift: the build changed no tracked file"
}
g_prover-glue()   { bash scripts/check-prover-glue.sh; }
g_build-closure() { bash scripts/check-build-closure.sh && bash scripts/check-canonical-policy-portal.sh && python3 scripts/test_build_gate_boundaries.py && python3 scripts/test_lean_build_surfaces.py; }
g_unit-tests()    { bash scripts/check-unit-tests.sh; }
g_host-closure()  { bash scripts/check-host-closure.sh; }
g_import-tiers()  { bash scripts/check-import-boundary.sh; }
g_exports()       { bash scripts/check-exports.sh; }
g_shell-paths()   { bash scripts/check-shell-paths.sh; }
g_objective-frontend() { bash scripts/check-objective-frontend.sh; }
g_world-cohorts() { bash scripts/check-world-cohorts.sh; }
g_website()       { python3 website/gen-status.py --check; }
g_rust-tests()    { bash scripts/check-rust-tests.sh; }
g_deploy-scripts() { python3 deploy/pay/test-render-enrol.py && python3 deploy/candidate/test-package.py && bash deploy/candidate/test-lane-build.sh; }
g_spk-shell()     { bash scripts/check-spk-shell-tests.sh; }
g_journey()       { bash scripts/check-journey.sh; }

tree_before=$(tree_state)
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
