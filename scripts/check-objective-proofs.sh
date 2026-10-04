#!/usr/bin/env bash
# check-objective-proofs.sh -- the Objective Bend Core4 gates.
#
#   proofs    `lake build ObjectiveProofs` (+ the checkpoint round trip), then the
#             statement/axiom snapshot: scripts/ObjectiveSnapshot.lean prints every
#             declaration of a Theory.ObjectiveBend* module (elaborated type; the body
#             of a Prop-valued definition; a hash of any other definition's body) and
#             every theorem's exact axiom set. They must equal
#             scripts/gates/objective-statements.snapshot and
#             scripts/gates/objective-axioms.pin byte for byte. Self-tested every run:
#             (a) a theorem planted in a scratch copy must appear and turn the diff red;
#             (b) a copy whose scan loop is deleted must fail its instrument floor.
#   (the front end -- identity, elaboration and parser cohorts, C4, preview cohort,
#   publication replay, examples, tutorial -- is scripts/check-objective-frontend.sh,
#   gate objective-frontend)
#   c         the C differential (native/objective-emit/differential.py) over the
#             packets of the preview cohort and native/objective-emit/extra-cohort.json:
#             runtime.c against runBounded, per case, State bytes included.
#
# usage: scripts/check-objective-proofs.sh [proofs|c|all] [--update]
#   --update rewrites the two snapshot files (proofs only); commit them with the change
#   they announce. Requires `bun` for c (BUN=/path/to/bun or on PATH):
#   absent, those gates are RED, never skipped. Logs: build-logs/objective/<gate>/.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
root_dir=$root
cd "$root"
export PATH=$HOME/.elan/bin:$PATH
lake=${LAKE:-lake}
what=${1:-all}
update=0
if [ "$what" = "--update" ]; then what=proofs; update=1; fi
if [ "${2:-}" = "--update" ]; then update=1; fi
statements=scripts/gates/objective-statements.snapshot
axioms=scripts/gates/objective-axioms.pin
logs=$root/build-logs/objective
mkdir -p "$logs"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/objective-proofs.XXXXXX")
trap 'rm -rf "$tmp"' EXIT

bun_bin() {
  local b=${BUN:-$(command -v bun || true)}
  if [ -z "$b" ] || [ ! -x "$b" ]; then
    echo "objective: bun not found (set BUN=); this gate is RED, not skipped" >&2; return 1
  fi
  echo "$b"
}

snapshot() { # snapshot <lean file> <out> <err>; prints exit status. Lean reports
  # errors on stdout: every non-row line of <out> is appended to <err>.
  set +e
  "$lake" env lean --root="$(dirname "$1")" "$1" >"$2" 2>"$3"
  local s=$?
  set -e
  grep -av '^[SA] ' "$2" >>"$3" || true
  echo "$s"
}

gate_proofs() {
  # every module scripts/ObjectiveSnapshot.lean imports
  local targets="ObjectiveProofs Theory.ObjectiveBendCheckpointRoundTrip Theory.ObjectiveBendExtensions Theory.ObjectiveBendDemandCapacity"
  echo "== lake build $targets"
  "$lake" build $targets
  local failed=0
  # (a) a planted theorem must appear and turn the comparison red
  python3 - scripts/ObjectiveSnapshot.lean "$tmp/plant.lean" <<'EOF'
import sys
src = open(sys.argv[1]).read()
anchor = "set_option maxHeartbeats 0 in\nrun_meta"
assert src.count(anchor) == 1, "self-test: run_meta anchor not found"
plant = "theorem Minidregg.ObjectiveSnapshot.Plant.planted (n : Nat) : n + 0 = n := rfl\n\n"
switch = "def includeLocal : Bool := false"
assert src.count(switch) == 1, "self-test: includeLocal switch not found"
src = src.replace(switch, "def includeLocal : Bool := true")
open(sys.argv[2], "w").write(src.replace(anchor, plant + anchor))
EOF
  local s; s=$(snapshot "$tmp/plant.lean" "$tmp/plant.out" "$tmp/plant.err")
  if [ "$s" = 0 ] && grep -q "^S theorem Minidregg.ObjectiveSnapshot.Plant.planted : ∀ (n : Nat), n + 0 = n$" "$tmp/plant.out" \
     && ! diff -q <(grep '^S ' "$tmp/plant.out") "$statements" >/dev/null 2>&1; then
    echo "self-test (a) planted theorem: PASS (row present; comparison red)"
  else
    echo "self-test (a) planted theorem: FAIL (exit $s)"; head -20 "$tmp/plant.err"; failed=1
  fi
  # (b) delete the scan; the instrument floor must fail the run
  python3 - scripts/ObjectiveSnapshot.lean "$tmp/noscan.lean" <<'EOF'
import sys
src = open(sys.argv[1]).read()
b, e = "  -- SCAN-BEGIN\n", "  -- SCAN-END\n"
assert src.count(b) == 1 and src.count(e) == 1, "self-test: scan markers not found"
i, j = src.index(b), src.index(e) + len(e)
open(sys.argv[2], "w").write(src[:i] + src[j:])
EOF
  s=$(snapshot "$tmp/noscan.lean" "$tmp/noscan.out" "$tmp/noscan.err")
  if [ "$s" != 0 ] && grep -q "objective-snapshot: instrument:" "$tmp/noscan.err"; then
    echo "self-test (b) scan deleted: PASS (exit $s; $(grep -m1 'objective-snapshot: instrument:' "$tmp/noscan.err"))"
  else
    echo "self-test (b) scan deleted: FAIL (exit $s)"; head -20 "$tmp/noscan.err"; failed=1
  fi
  # the real run
  s=$(snapshot scripts/ObjectiveSnapshot.lean "$tmp/real.out" "$tmp/real.err")
  grep -av "warning\|^Note:\|^$" "$tmp/real.err" || true
  if [ "$s" != 0 ]; then echo "objective-snapshot: FAILED (exit $s)"; return 1; fi
  grep '^S ' "$tmp/real.out" >"$tmp/statements"
  grep '^A ' "$tmp/real.out" >"$tmp/axioms"
  if [ "$update" = 1 ]; then
    cp "$tmp/statements" "$statements"; cp "$tmp/axioms" "$axioms"
    echo "objective-snapshot: UPDATED $statements ($(wc -l <"$statements") rows), $axioms ($(wc -l <"$axioms") rows); commit them with the change they announce"
  else
    local changed=0
    if ! diff -u "$statements" "$tmp/statements" >"$logs/statements.diff"; then
      echo "objective-snapshot: STATEMENTS CHANGED (unannounced):"; head -60 "$logs/statements.diff"; changed=1
    fi
    if ! diff -u "$axioms" "$tmp/axioms" >"$logs/axioms.diff"; then
      echo "objective-snapshot: AXIOM SETS CHANGED (unannounced):"; head -60 "$logs/axioms.diff"; changed=1
    fi
    [ "$changed" = 0 ] && echo "objective-snapshot: $(wc -l <"$statements") statements and $(wc -l <"$axioms") axiom sets unchanged"
    [ "$changed" = 0 ] || failed=1
  fi
  [ "$failed" = 0 ]
}

gate_c() {
  local bun; bun=$(bun_bin)
  # `lean --run Compiler/ObjectiveBendEmitCRun.lean` needs every import built; the packets come
  # from the Lean front end (Host/ObjectiveBendFrontEnd, run by tests/objective-bend-source/front.ts)
  "$lake" build Compiler.ObjectiveBendEmitCRun Host.ObjectiveBendFrontEnd
  LEAN=$("$lake" env which lean); LEAN_PATH=$("$lake" env printenv LEAN_PATH); export LEAN LEAN_PATH
  echo "== packets"
  "$bun" native/objective-emit/packets.ts "$tmp/packets" tests/objective-bend-source/preview-cohort.json \
    native/objective-emit/extra-cohort.json
  local failed=0 set total
  for set in packets fixtures; do
    local root=$tmp/packets; [ "$set" = fixtures ] && root=$root_dir/native/objective-emit/fixtures
    echo "== differential ($set)"
    python3 native/objective-emit/differential.py "$root" "$tmp/differential-$set" "$logs/differential-$set.log" || true
    total=$(grep '^# TOTAL' "$logs/differential-$set.log" || true)
    echo "differential ($set): ${total:-no TOTAL line}"
    if ! [[ "$total" =~ pass=([0-9]+)\ fail=0$ ]] || [ "${BASH_REMATCH[1]}" = 0 ]; then failed=1; fi
  done
  [ "$failed" = 0 ]
}

case "$what" in
  proofs) gate_proofs 2>&1 | tee "$logs/proofs.log"; exit "${PIPESTATUS[0]}" ;;
  c) gate_c 2>&1 | tee "$logs/c.log"; exit "${PIPESTATUS[0]}" ;;
  all)
    red=0
    for g in proofs c; do
      if "$0" "$g"; then echo "objective $g: PASS"; else echo "objective $g: RED"; red=$((red+1)); fi
    done
    exit "$red" ;;
  *) echo "usage: $0 [proofs|c|all] [--update]" >&2; exit 64 ;;
esac
