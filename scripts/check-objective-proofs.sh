#!/usr/bin/env bash
# check-objective-proofs.sh -- the Objective Bend Core4 gates.
#
#   proofs    `lake build ObjectiveProofs` (+ the checkpoint round trip), then the
#             statement/axiom snapshots. Two runs of one scanner (Verify/ObjectiveSnapshot.lean)
#             partition the repository modules of the ObjectiveProofs import closure:
#             scripts/ObjectiveSnapshot.lean covers the Theory.ObjectiveBend* modules in an
#             environment that refuses Mathlib (scripts/gates/objective-statements.snapshot,
#             scripts/gates/objective-axioms.pin); scripts/ObjectiveSnapshotMathlib.lean covers
#             every other one (Kernel, Compiler, Pred, Selvage, the rest of Theory) with Mathlib in
#             the environment (scripts/gates/objective-statements-mathlib.snapshot,
#             scripts/gates/objective-axioms-mathlib.pin). Each prints every declaration
#             (elaborated type; the body of a Prop-valued definition; a hash of any other
#             definition's body) and every theorem's exact axiom set; all four files must match
#             byte for byte. Self-tested every run, per run: (a) a theorem planted in a scratch
#             copy must appear and turn the diff red; (b) a copy whose scan is deleted must fail
#             its instrument floor; and once: (c) the measured defect -- `(_vacuous : False)`
#             planted on Kernel.ObjectiveBendAdmissionSemantics.admitted_source_semantics -- must
#             change that statement's row.
#   (the front end -- identity, elaboration and parser cohorts, C4, preview cohort,
#   publication replay, examples, tutorial -- is scripts/check-objective-frontend.sh,
#   gate objective-frontend)
#   c         the C differential (native/objective-emit/differential.py) over the
#             packets of the preview cohort and native/objective-emit/extra-cohort.json:
#             runtime.c against runBounded, per case, State bytes included.
#   cgen      the C differential over GENERATED programs: native/objective-emit
#             (Compiler/ObjectiveBendCDiffGen, a seeded, type-directed generator whose every program
#             is accepted by the real checker) writes seeds 0..999, and differential.py runs each
#             under the same cases as gate `c`. The fixed seed range makes a red reproducible
#             (`objective-cdiff-gen gen SEED 1 DIR`). Self-tested every run: two planted miscompiles of
#             runtime.c (native/objective-emit/cdiff-mutants.py) must each turn the same 1000 red,
#             and the mutation must have happened (the mutator refuses a no-op).
#   transparency  the checkpoint-transparency differential
#             (native/objective-emit/transparency.py + scripts/ObjectiveCheckpointTransparency.lean)
#             over every activity of the preview cohort and native/objective-emit/activity-cohort.json:
#             resuming what the kernel stores (the Plan extraction's state, settled and
#             collected) against resuming the machine's own yielded state, per segment:
#             outcome, Plan/result Data, kernel ticks <= lazy ticks; plus the growth leg
#             (TallyTwelve stored checkpoint has one byte count over segments 1..12, the twelve replies).
#             Executed evidence for the open premise ForcingTransparent, not a proof.
#             Self-tested every run: the planted `drop-stack-roots` checkpoint must go red.
#
# usage: scripts/check-objective-proofs.sh [proofs|c|cgen|transparency|all] [--update]
#   --update rewrites the four snapshot files (proofs only); commit them with the change
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
statements_mathlib=scripts/gates/objective-statements-mathlib.snapshot
axioms_mathlib=scripts/gates/objective-axioms-mathlib.pin
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

scratch_lean() { # scratch_lean <mode> <script> <out>: a scratch copy of a snapshot script.
  #   plant   the copy declares Minidregg.ObjectiveSnapshot.Plant.planted and counts it (includeLocal)
  #   noscan  the copy runs the scanner's source (Verify/ObjectiveSnapshot.lean, inlined) with its
  #           SCAN-BEGIN..SCAN-END region deleted
  python3 - "$1" "$2" Verify/ObjectiveSnapshot.lean "$3" <<'EOF'
import sys
mode, script, scanner, out = sys.argv[1:]
src = open(script).read()
if mode == "plant":
    anchor = "set_option maxHeartbeats 0 in\nrun_meta"
    assert src.count(anchor) == 1, "self-test: run_meta anchor not found"
    switch = "def includeLocal : Bool := false"
    assert src.count(switch) == 1, "self-test: includeLocal switch not found"
    plant = "theorem Minidregg.ObjectiveSnapshot.Plant.planted (n : Nat) : n + 0 = n := rfl\n\n"
    src = src.replace(switch, "def includeLocal : Bool := true").replace(anchor, plant + anchor)
else:
    # the import block: the lines starting `import ` right after the module doc comment
    assert src.startswith("/-") and src.count("\n-/\n") >= 1, "self-test: script doc comment not found"
    lines = src.split("\n")
    k = lines.index("-/") + 1
    imports = []
    while k < len(lines) and lines[k].startswith("import "):
        imports.append(k); k += 1
    assert imports and "import Verify.ObjectiveSnapshot" in [lines[i] for i in imports], "self-test: script imports not found"
    head = [lines[i] for i in imports if lines[i] != "import Verify.ObjectiveSnapshot"]
    body = "\n".join(lines[imports[-1] + 1:])
    scan = open(scanner).read()
    assert scan.count("\nimport Lean\n") == 1, "self-test: scanner import not found"
    scan = scan.split("\nimport Lean\n", 1)[1]
    b, e = "  -- SCAN-BEGIN\n", "  -- SCAN-END\n"
    assert scan.count(b) == 1 and scan.count(e) == 1, "self-test: scan markers not found"
    scan = scan[:scan.index(b)] + scan[scan.index(e) + len(e):]
    src = "\n".join(head) + "\nimport Lean\n" + scan + body
open(out, "w").write(src)
EOF
}

gate_proofs() {
  # every module the two snapshot scripts import (the scanner, Verify.ObjectiveSnapshot, is rooted by Verify)
  local targets="ObjectiveProofs Theory.ObjectiveBendCheckpointRoundTrip Theory.ObjectiveBendExtensions Theory.ObjectiveBendDemandCapacity Verify.ObjectiveSnapshot"
  echo "== lake build $targets"
  "$lake" build $targets
  local failed=0 run script stmts axs label plantrow s
  # Two runs partition the repository modules of the ObjectiveProofs closure (see the headers of
  # the two scripts): the Theory.ObjectiveBend* modules without Mathlib in the environment, the
  # rest with it. Each run is self-tested: (a) a planted theorem must appear and turn its diff red;
  # (b) a copy with the scan deleted must fail its instrument floor. The two runs execute in
  # parallel with their planted copies.
  for run in theory mathlib; do
    script=scripts/ObjectiveSnapshot.lean
    [ "$run" = mathlib ] && script=scripts/ObjectiveSnapshotMathlib.lean
    scratch_lean plant "$script" "$tmp/$run-plant.lean"
    scratch_lean noscan "$script" "$tmp/$run-noscan.lean"
    snapshot "$script" "$tmp/$run.out" "$tmp/$run.err" >"$tmp/$run.rc" &
    snapshot "$tmp/$run-plant.lean" "$tmp/$run-plant.out" "$tmp/$run-plant.err" >"$tmp/$run-plant.rc" &
    snapshot "$tmp/$run-noscan.lean" "$tmp/$run-noscan.out" "$tmp/$run-noscan.err" >"$tmp/$run-noscan.rc" &
    wait
  done
  for run in theory mathlib; do
    if [ "$run" = theory ]; then
      stmts=$statements; axs=$axioms; label=objective-snapshot
      plantrow='S theorem Minidregg.ObjectiveSnapshot.Plant.planted : ∀ (n : Nat), n + 0 = n'
    else
      stmts=$statements_mathlib; axs=$axioms_mathlib; label=objective-snapshot-mathlib
      plantrow='S theorem Minidregg.ObjectiveSnapshot.Plant.planted : ∀ (n : ℕ), n + 0 = n'
    fi
    s=$(cat "$tmp/$run-plant.rc")
    if [ "$s" = 0 ] && grep -qxF "$plantrow" "$tmp/$run-plant.out" \
       && ! diff -q <(grep '^S ' "$tmp/$run-plant.out") "$stmts" >/dev/null 2>&1; then
      echo "self-test ($run a) planted theorem: PASS (row present; comparison red)"
    else
      echo "self-test ($run a) planted theorem: FAIL (exit $s)"; head -20 "$tmp/$run-plant.err"; failed=1
    fi
    s=$(cat "$tmp/$run-noscan.rc")
    if [ "$s" != 0 ] && grep -q "^$label: instrument:" "$tmp/$run-noscan.err"; then
      echo "self-test ($run b) scan deleted: PASS (exit $s; $(grep -m1 "^$label: instrument:" "$tmp/$run-noscan.err"))"
    else
      echo "self-test ($run b) scan deleted: FAIL (exit $s)"; head -20 "$tmp/$run-noscan.err"; failed=1
    fi
    s=$(cat "$tmp/$run.rc")
    grep -av "warning\|^Note:\|^$" "$tmp/$run.err" || true
    if [ "$s" != 0 ]; then echo "$label: FAILED (exit $s)"; failed=1; continue; fi
    grep '^S ' "$tmp/$run.out" >"$tmp/$run.statements"
    grep '^A ' "$tmp/$run.out" >"$tmp/$run.axioms"
    if [ "$update" = 1 ]; then
      cp "$tmp/$run.statements" "$stmts"; cp "$tmp/$run.axioms" "$axs"
      echo "$label: UPDATED $stmts ($(wc -l <"$stmts") rows), $axs ($(wc -l <"$axs") rows); commit them with the change they announce"
    else
      local changed=0
      if ! diff -u "$stmts" "$tmp/$run.statements" >"$logs/$run-statements.diff"; then
        echo "$label: STATEMENTS CHANGED (unannounced):"; head -60 "$logs/$run-statements.diff"; changed=1
      fi
      if ! diff -u "$axs" "$tmp/$run.axioms" >"$logs/$run-axioms.diff"; then
        echo "$label: AXIOM SETS CHANGED (unannounced):"; head -60 "$logs/$run-axioms.diff"; changed=1
      fi
      [ "$changed" = 0 ] && echo "$label: $(wc -l <"$stmts") statements and $(wc -l <"$axs") axiom sets unchanged"
      [ "$changed" = 0 ] || failed=1
    fi
  done
  # (c) the measured defect, planted every run: an unused `(_vacuous : False)` premise on
  # admitted_source_semantics (W20-GATE-MUTATION left the gate green under exactly this). A scratch
  # copy of the module, mutated (the mutation is asserted to have happened), prints the row with the
  # scanner; it must be the pinned row with `False → ` inserted, and absent from the pin.
  local planted=1
  python3 - Kernel/ObjectiveBendAdmissionSemantics.lean "$tmp/premise.lean" <<'EOF' || planted=0
import sys
src = open(sys.argv[1]).read()
anchor = "    (admitted : Admitted prepared ingress writes guards) :\n    runBounded"
assert src.count(anchor) == 1, "self-test: admitted_source_semantics binder anchor not found"
mutated = src.replace(anchor, "    (admitted : Admitted prepared ingress writes guards) (_vacuous : False) :\n    runBounded")
assert mutated != src and mutated.count("(_vacuous : False)") == 1, "self-test: the premise was not planted"
lines = mutated.split("\n")
last = max(i for i, l in enumerate(lines) if l.startswith("import "))
lines.insert(last + 1, "import Verify.ObjectiveSnapshot")
open(sys.argv[2], "w").write("\n".join(lines) + "\nrun_meta Minidregg.ObjectiveSnapshot.printStatementRow "
  "`Minidregg.Kernel.ObjectiveBendAdmissionSemantics.admitted_source_semantics\n")
EOF
  s=-
  if [ "$planted" = 1 ]; then
    set +e
    "$lake" env lean --root=Kernel "$tmp/premise.lean" >"$tmp/premise.out" 2>&1
    s=$?
    set -e
  else
    echo "the premise could not be planted (see the assertion above)" >"$tmp/premise.out"
  fi
  if [ "$planted" = 1 ] && python3 - "$tmp/premise.out" "$statements_mathlib" <<'EOF'
import sys
rows = [l for l in open(sys.argv[1]).read().splitlines() if l.startswith("S ")]
pin = open(sys.argv[2]).read().splitlines()
assert len(rows) == 1, f"expected one row from the mutated module, got {len(rows)}"
row = rows[0]
assert row.count("False → ") == 1, "the planted premise is not in the row"
assert row not in pin, "the row with the planted premise is in the pin"
assert row.replace("False → ", "", 1) in pin, "the row minus the planted premise is not the pinned row"
EOF
  then
    echo "self-test (c) planted (_vacuous : False) on admitted_source_semantics: PASS (exit $s; row changed by exactly 'False → ', absent from the pin)"
  else
    echo "self-test (c) planted (_vacuous : False) on admitted_source_semantics: FAIL (exit $s)"; head -20 "$tmp/premise.out"; failed=1
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

gate_cgen() {
  local seeds=${CGEN_SEEDS:-1000} start=${CGEN_START:-0}
  # the differential's two drivers, natively compiled: the Lean machine (the reference side)
  # and the generator
  "$lake" build objective-cdiff objective-cdiff-gen
  local bin=$root/.lake/build/bin ed=$root/native/objective-emit failed=0 total
  # these runs use the same limits the burn job uses; a program that runs out of them is a case, not a skip
  local limits="--heap 20000 --stack 20000 --ticks 20000"
  local jobs=${CGEN_JOBS:-4}
  echo "== generate seeds $start..$((start + seeds - 1))"
  local summary; summary=$("$bin/objective-cdiff-gen" gen "$start" "$seeds" "$tmp/generated")
  echo "$summary"
  if ! grep -q "\"emitted\":$seeds," <<<"$summary" || ! grep -q '"genFailed":0,' <<<"$summary"; then
    echo "cgen: the generator did not emit all $seeds programs"; return 1
  fi
  local common="--jobs $jobs --serve --lean-bin $bin/objective-cdiff --precompile-runtime $limits"
  echo "== self-test: planted miscompiles of runtime.c must go red"
  local m
  for m in spec-apply-metadata add-carry; do
    python3 "$ed/cdiff-mutants.py" apply "$m" "$ed/runtime.c" "$tmp/runtime-$m.c" || { failed=1; continue; }
    python3 "$ed/differential.py" "$tmp/generated" "$tmp/mutant-$m" "$logs/cgen-mutant-$m.log" \
      $common --runtime "$tmp/runtime-$m.c" --max-fail 1 >/dev/null || true
    local first; first=$(grep '^# FIRST-FAIL' "$logs/cgen-mutant-$m.log" || true)
    if [ -n "$first" ]; then echo "self-test (mutant $m): PASS ($first)"
    else echo "self-test (mutant $m): FAIL (the planted miscompile survived $seeds generated programs)"; failed=1; fi
  done
  echo "== differential (generated seeds $start..$((start + seeds - 1)))"
  python3 "$ed/differential.py" "$tmp/generated" "$tmp/differential-cgen" "$logs/differential-cgen.log" \
    $common || true
  total=$(grep '^# TOTAL' "$logs/differential-cgen.log" || true)
  echo "differential (cgen): ${total:-no TOTAL line}"
  if ! [[ "$total" =~ pass=([0-9]+)\ fail=0$ ]] || [ "${BASH_REMATCH[1]}" = 0 ]; then failed=1; fi
  [ "$failed" = 0 ]
}

gate_transparency() {
  local bun; bun=$(bun_bin)
  # `lean --run scripts/ObjectiveCheckpointTransparency.lean` needs every import built
  "$lake" build Kernel.ObjectiveActivityWire Compiler.ObjectiveBendDataWire Theory.ObjectiveBendDemandCollect \
    Host.ObjectiveBendFrontEnd
  # packets.ts elaborates through the Lean front end, as in gate `c`; without these the
  # standalone `transparency` gate refused every packet ('capture failed') and only `all`
  # (which runs `c` first in the same shell) passed
  LEAN=$("$lake" env which lean); LEAN_PATH=$("$lake" env printenv LEAN_PATH); export LEAN LEAN_PATH
  # the preview cohort's activities (sources made absolute: packets.ts resolves them
  # against the cohort file's directory)
  python3 - tests/objective-bend-source/preview-cohort.json "$tmp/activities.json" <<'EOF'
import json, os, sys
cohort = os.path.abspath(sys.argv[1]); base = os.path.dirname(cohort)
items = [i for i in json.load(open(cohort)) if i.get("responses")]
for i in items:
    for m in i["modules"]: m["source"] = os.path.join(base, m["source"])
assert items, "no activity in the preview cohort"
json.dump(items, open(sys.argv[2], "w"))
EOF
  echo "== packets"
  "$bun" native/objective-emit/packets.ts "$tmp/activity-packets" "$tmp/activities.json" \
    native/objective-emit/activity-cohort.json
  local failed=0 total
  # the elaborated Tally the ForcingTransparent points (Kernel/ObjectiveResumeContract) read
  if cmp -s "$tmp/activity-packets/TallyTwelve/source.core.json" tests/objective-activity/TallyTwelve.core.json; then
    echo "fixture tests/objective-activity/TallyTwelve.core.json: fresh"
  else
    echo "fixture tests/objective-activity/TallyTwelve.core.json: STALE (the re-elaborated packet differs)"; failed=1
  fi
  echo "== self-test: the planted drop-stack-roots checkpoint must go red"
  if python3 native/objective-emit/transparency.py "$tmp/activity-packets" "$logs/transparency-mutant.log" \
       --mutant drop-stack-roots >/dev/null; then
    echo "self-test (mutant): FAIL (the planted checkpoint agreed)"; failed=1
  else
    total=$(grep '^# TOTAL' "$logs/transparency-mutant.log" || true)
    if [[ "$total" =~ fail=([0-9]+)$ ]] && [ "${BASH_REMATCH[1]}" != 0 ]; then
      echo "self-test (mutant): PASS ($total)"
    else
      echo "self-test (mutant): FAIL (no verdicts: ${total:-no TOTAL line})"; failed=1
    fi
  fi
  echo "== transparency"
  python3 native/objective-emit/transparency.py "$tmp/activity-packets" "$logs/transparency.log" \
    --growth TallyTwelve:1:12 || true
  total=$(grep '^# TOTAL' "$logs/transparency.log" || true)
  echo "transparency: ${total:-no TOTAL line}"
  if ! [[ "$total" =~ pass=([0-9]+)\ fail=0$ ]] || [ "${BASH_REMATCH[1]}" = 0 ]; then failed=1; fi
  [ "$failed" = 0 ]
}

case "$what" in
  proofs) gate_proofs 2>&1 | tee "$logs/proofs.log"; exit "${PIPESTATUS[0]}" ;;
  c) gate_c 2>&1 | tee "$logs/c.log"; exit "${PIPESTATUS[0]}" ;;
  cgen) gate_cgen 2>&1 | tee "$logs/cgen.log"; exit "${PIPESTATUS[0]}" ;;
  transparency) gate_transparency 2>&1 | tee "$logs/transparency-gate.log"; exit "${PIPESTATUS[0]}" ;;
  all)
    red=0
    for g in proofs c cgen transparency; do
      if "$0" "$g"; then echo "objective $g: PASS"; else echo "objective $g: RED"; red=$((red+1)); fi
    done
    exit "$red" ;;
  *) echo "usage: $0 [proofs|c|cgen|transparency|all] [--update]" >&2; exit 64 ;;
esac
