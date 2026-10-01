#!/usr/bin/env bash
# The one gate. EVERY gate runs, even after an earlier one is red (the first red
# must not hide the second); the exit status is the number of red gates (0 =
# PASS). Each gate's output goes to stdout and to build-logs/local-gates/NAME.log;
# the end is a one-line-per-gate summary with wall seconds. No fallback, no skip.
#
#   hygiene        no bare `#print axioms`, no project `axiom`; Assurance/SheetLaw.lean
#                  §2 is the embed of the MUD sheet JSON (scripts/gen-sheetlaw.py --check)
#   lake-build     lake build every lean_lib + every lean_exe in lakefile.toml (Minidregg,
#                  AxiomCensus, minidregg-host, nock-eval, ...): every library module elaborates, every
#                  pinned axiom footprint is compared, the tree-wide #assert_axioms_tree
#                  runs, and the Host executable links
#   cold-start     the native Host starts without doing work (scripts/check-host-cold-start.sh:
#                  peak RSS and CPU of a bare start; a computable nullary def in a module
#                  the Host links runs at every Host start)
#   hyp-ledger     scripts/check-hypothesis-ledger.sh over AxiomCensusResearch (built by
#                  lake-build): no VACUOUS/INCONSISTENT row, no un-allowlisted TOOTHLESS
#                  assumption, no stale allowlist entry; self-tests its instrument each run
#   drift          the build changed no tracked file (Lean-emitted descriptors, vectors,
#                  glue); compared against the tree as it stood before the build
#   prover-glue    the Lean-emitted prover glue is byte-identical to what its source emits
#   build-closure  every tracked library module is reachable from what lake-build builds
#   host-closure   the import closure of Host.Main equals scripts/gates/host-closure.pin
#   import-tiers   every import is inside the tier table of scripts/check-import-boundary.sh
#   exports        every @[export] is called from native/ or allowlisted with a reason
#   rust-tests     the filtered native test lines of scripts/check-rust-tests.sh
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
# lake-build builds EVERY lean_lib and lean_exe the lakefile declares (the umbrella,
# AxiomCensus, any other root library, the executables), read from the lakefile so a
# new root library cannot be left out of the gate.
lib_targets=$(sed -n '/^\[\[lean_lib\]\]/{n;s/^name *= *"\(.*\)"$/\1/p}' lakefile.toml | tr '\n' ' ')
exe_targets=$(sed -n '/^\[\[lean_exe\]\]/{n;s/^name *= *"\(.*\)"$/\1/p}' lakefile.toml | tr '\n' ' ')

GATES=(hygiene lake-build cold-start hyp-ledger drift prover-glue build-closure host-closure import-tiers exports rust-tests journey)
declare -A STATUS SECS LAST
red=0
only=${LOCAL_GATES_ONLY:-}

g_hygiene()       { bash scripts/check-proof-hygiene.sh && python3 scripts/gen-sheetlaw.py --check; }
g_lake-build()    { echo "lake build $lib_targets$exe_targets"; "$lake" build $lib_targets $exe_targets; }
g_cold-start()    { bash scripts/check-host-cold-start.sh .lake/build/bin/minidregg-host; }
g_hyp-ledger()    { bash scripts/check-hypothesis-ledger.sh; }
g_drift() {
  local after; after=$(git diff --binary | git hash-object --stdin)
  if [[ "$tree_before" != "$after" ]]; then
    git diff --stat
    echo "drift: the build rewrote tracked files; commit the Lean-emitted copies"; return 1
  fi
  echo "drift: the build changed no tracked file"
}
g_prover-glue()   { bash scripts/check-prover-glue.sh; }
g_build-closure() { bash scripts/check-build-closure.sh; }
g_host-closure()  { bash scripts/check-host-closure.sh; }
g_import-tiers()  { bash scripts/check-import-boundary.sh; }
g_exports()       { bash scripts/check-exports.sh; }
g_rust-tests()    { bash scripts/check-rust-tests.sh; }
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
