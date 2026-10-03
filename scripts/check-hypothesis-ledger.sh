#!/usr/bin/env bash
# check-hypothesis-ledger.sh -- the statement audit as an instrument.
#
# Runs scripts/HypothesisLedger.lean over the research umbrella
# (AxiomCensusResearch: Minidregg and every Host module) and fails on
#   * a VACUOUS row      (a family whose negation is proved, still bound by a theorem),
#   * an INCONSISTENT row (a family proved AND refuted),
#   * a TOOTHLESS assumption (an open hypothesis with no named satisfying AND
#     refuting instance) not in scripts/hypothesis-ledger-allow.txt,
#   * a stale allowlist entry (the ratchet only tightens),
#   * a broken instrument: a planted family classified wrongly, a pinned real
#     row that moved, or fewer consumed families than the pinned floor.
# STALE rows (a family proved outright, still bound as a premise) are printed,
# not gated.
#
# Before the real run it tests the instrument itself, every time:
#   (a) a scratch family with a proved negation and a consumer is planted;
#       the run must exit non-zero and print it VACUOUS;
#   (b) the scan loop is deleted; the run must exit non-zero on the instrument;
#   (c) the real run must not see the scratch plant.
# The copies are written to a temporary directory; the tree is never edited.
#
# usage: scripts/check-hypothesis-ledger.sh [--no-self-test]
# Requires the research umbrella built (scripts/lane/rb.sh); never rebuilds it.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
cd "$root"
export PATH=$HOME/.elan/bin:$PATH
ledger=scripts/HypothesisLedger.lean
export HYP_LEDGER_ALLOW="$root/scripts/hypothesis-ledger-allow.txt"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/hyp-ledger.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

run() { # run <file> <log>; prints the exit status, never fails the script
  set +e
  # Give scratch copies an explicit package root while retaining the project
  # toolchain and imported environment selected by lake env.
  lake env lean --root="$(dirname "$1")" "$1" >"$2" 2>&1
  local status=$?
  set -e
  echo "$status"
}

# Report a failed prerequisite as such; it is not an instrument refutation.
if ! lake env lean --deps "$ledger" >"$tmp/dependencies.log" 2>&1; then
  echo "hypothesis-ledger: dependency preflight FAILED; instrument not run" >&2
  cat "$tmp/dependencies.log" >&2
  exit 2
fi
while IFS= read -r dependency; do
  if [[ "$dependency" == *.olean && ! -f "$dependency" ]]; then
    echo "hypothesis-ledger: compiled dependency absent: $dependency; instrument not run" >&2
    exit 2
  fi
done < "$tmp/dependencies.log"

self_test=1
[ "${1:-}" = "--no-self-test" ] && self_test=0
failed=0

if [ "$self_test" = 1 ]; then
  # (a) plant a refuted family with a consumer
  python3 - "$ledger" "$tmp/plant.lean" <<'EOF'
import sys
src = open(sys.argv[1]).read()
anchor = "set_option maxHeartbeats 0 in\nrun_meta"
assert src.count(anchor) == 1, "self-test: run_meta anchor not found"
plant = """namespace Minidregg.Scratch
def Bogus : Prop := False
theorem bogus_refuted : ¬ Bogus := id
theorem bogus_consumer (h : Bogus) : True := trivial
end Minidregg.Scratch

"""
open(sys.argv[2], "w").write(src.replace(anchor, plant + anchor))
EOF
  status=$(run "$tmp/plant.lean" "$tmp/plant.log")
  row=$(grep -a "^Minidregg.Scratch.Bogus | REFUTED | VACUOUS \[RED\]" "$tmp/plant.log" || true)
  if [ "$status" != 0 ] && [ -n "$row" ] && grep -aq "RED: Minidregg.Scratch.Bogus is VACUOUS" "$tmp/plant.log"; then
    echo "self-test (a) planted refuted family: PASS (exit $status; ${row%%  \[*})"
  else
    echo "self-test (a) planted refuted family: FAIL (exit $status)"; cat "$tmp/plant.log"; failed=1
  fi

  # (b) delete the scan
  python3 - "$ledger" "$tmp/noscan.lean" <<'EOF'
import sys
src = open(sys.argv[1]).read()
begin, end = "  -- SCAN-BEGIN\n", "  -- SCAN-END\n"
assert src.count(begin) == 1 and src.count(end) == 1, "self-test: scan markers not found"
i, j = src.index(begin), src.index(end) + len(end)
open(sys.argv[2], "w").write(src[:i] + src[j:])
EOF
  status=$(run "$tmp/noscan.lean" "$tmp/noscan.log")
  if [ "$status" != 0 ] && grep -aq "hypothesis-ledger: instrument:" "$tmp/noscan.log"; then
    echo "self-test (b) scan deleted: PASS (exit $status; $(grep -ac "hypothesis-ledger: instrument:" "$tmp/noscan.log") instrument failures, first: $(grep -a -m1 "hypothesis-ledger: instrument:" "$tmp/noscan.log"))"
  else
    echo "self-test (b) scan deleted: FAIL (exit $status)"; cat "$tmp/noscan.log"; failed=1
  fi
fi

# (c) the real run
status=$(run "$ledger" "$tmp/real.log")
grep -av "^Note:\|linter\|warning: unused variable\|^$" "$tmp/real.log" || true
if [ "$self_test" = 1 ]; then
  if grep -aq "Minidregg.Scratch" "$tmp/real.log"; then
    echo "self-test (c) plant removed: FAIL (the real run sees the scratch plant)"; failed=1
  else
    echo "self-test (c) plant removed: PASS (no scratch row; real run exit $status)"
  fi
fi
if [ "$failed" != 0 ]; then
  echo "hypothesis-ledger: instrument self-test FAILED" >&2
  exit 1
fi
if [ "$status" != 0 ]; then
  echo "hypothesis-ledger: FAILED (see above)" >&2
  exit 1
fi
