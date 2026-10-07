#!/usr/bin/env bash
# check-objective-proofs.sh -- the Objective Bend Core4 gates.
#
#   proofs    `lake build ObjectiveProofs` (+ the checkpoint round trip), then the contract
#             manifests. Two runs of one scanner (Verify/ObjectiveManifest.lean) partition the
#             repository modules of the ObjectiveProofs import closure: scripts/ObjectiveManifest.lean
#             covers the Theory.ObjectiveBend* modules in an environment that refuses Mathlib;
#             scripts/ObjectiveManifestMathlib.lean covers every other one (Kernel, Compiler, Pred,
#             Selvage, the rest of Theory) with Mathlib in the environment. Every declaration gets a
#             row: its statement, the SHA-256 Merkle hash of its statement's DEFINITION CLOSURE (the
#             bodies of every repository definition, inductive and constructor it reaches,
#             transitively), and its exact axiom set (scripts/objective-manifest.py has the hashing
#             and the cut). The rows are RATCHETED against the per-module manifests
#             scripts/gates/objective-manifest/<Module>.tsv: an added row passes; a removed row, a
#             restated statement, a redefined closure (`def Safe := True` under an unchanged
#             theorem) or a changed axiom set is RED unless scripts/gates/objective-contract-changes.txt
#             admits exactly that change (name, old contract, new contract, kind, commit, reason).
#             Self-tested every run: the ratchet logic on synthetic changes of the real rows; per
#             run (a) a planted theorem must appear as an admitted addition and every other row of
#             the planted run must equal the unplanted run's; (b) a copy whose scan is deleted must fail its instrument
#             floor; and once each: (c) the measured defect -- `(_vacuous : False)` planted on
#             Kernel.ObjectiveBendAdmissionSemantics.admitted_source_semantics -- must classify that
#             row `restated` and RED; (d) the redefinition defect -- in a copy of
#             Theory.ObjectiveBendOpenRecursion, `def Evaluates ... : Prop := True` with every
#             statement text unchanged -- must classify lazy_fixed_function `redefined` and RED,
#             naming Evaluates.
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
#             Executed cross-check of forcingTransparent_of_yieldedPlan (proved, Kernel/ObjectiveResumeContract).
#             Self-tested every run: the planted `drop-stack-roots` checkpoint must go red.
#
# usage: scripts/check-objective-proofs.sh [proofs|c|cgen|transparency|all] [--pin|--draft]
#   --pin    (proofs only) after a run whose every change is admitted, write the manifests: add the
#            new rows, apply the admitted changes and removals, refresh re-rendered text. It cannot
#            remove or change a row the ledger does not admit; commit the manifests it writes.
#   --draft  (proofs only) print a ledger line (reason TODO, which the ledger refuses) for every
#            unadmitted change, to review, give a commit and a reason, and append.
#   Requires `bun` for c (BUN=/path/to/bun or on PATH):
#   absent, those gates are RED, never skipped. Logs: build-logs/objective/<gate>/.
set -euo pipefail
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
root_dir=$root
cd "$root"
export PATH=$HOME/.elan/bin:$PATH
lake=${LAKE:-lake}
what=${1:-all}
mode=check
case "${2:-}" in
  --pin) mode=pin ;;
  --draft) mode=draft ;;
  "") ;;
  *) echo "usage: $0 [proofs|c|cgen|transparency|all] [--pin|--draft]" >&2; exit 64 ;;
esac
if [ "$mode" != check ] && [ "$what" != proofs ]; then echo "$0: ${2} is a proofs option" >&2; exit 64; fi
manifests=scripts/gates/objective-manifest
ledger=scripts/gates/objective-contract-changes.txt
manifest_tool=scripts/objective-manifest.py
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

manifest_run() { # manifest_run <lean file> <out> <err>: one scanner run; prints its exit status.
  # Lean reports errors on stdout; both streams go to <err>.
  set +e
  OBJECTIVE_MANIFEST_OUT="$2" "$lake" env lean --root="$(dirname "$1")" "$1" >"$3" 2>&1
  local s=$?
  set -e
  echo "$s"
}

scratch_lean() { # scratch_lean <mode> <script> <out>: a scratch copy of a manifest script.
  #   plant   the copy declares Minidregg.ObjectiveManifest.Plant.planted and covers it (localPrefix)
  #   noscan  the copy runs the scanner's source (Verify/ObjectiveManifest.lean, inlined) with its
  #           SCAN-BEGIN..SCAN-END region deleted
  python3 - "$1" "$2" Verify/ObjectiveManifest.lean "$3" <<'EOF'
import sys
mode, script, scanner, out = sys.argv[1:]
src = open(script).read()
if mode == "plant":
    anchor = "set_option maxHeartbeats 0 in\nrun_meta"
    assert src.count(anchor) == 1, "self-test: run_meta anchor not found"
    switch = "def localPrefix : Option Lean.Name := none"
    assert src.count(switch) == 1, "self-test: localPrefix switch not found"
    plant = "theorem Minidregg.ObjectiveManifest.Plant.planted (n : Nat) : n + 0 = n := rfl\n\n"
    src = src.replace(switch, "def localPrefix : Option Lean.Name := some `Minidregg.ObjectiveManifest.Plant")
    src = src.replace(anchor, plant + anchor)
else:
    # the import block: the lines starting `import ` right after the module doc comment
    assert src.startswith("/-") and src.count("\n-/\n") >= 1, "self-test: script doc comment not found"
    lines = src.split("\n")
    k = lines.index("-/") + 1
    imports = []
    while k < len(lines) and lines[k].startswith("import "):
        imports.append(k); k += 1
    assert imports and "import Verify.ObjectiveManifest" in [lines[i] for i in imports], "self-test: script imports not found"
    head = [lines[i] for i in imports if lines[i] != "import Verify.ObjectiveManifest"]
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

scratch_module() { # scratch_module <module file> <out> <old> <new> <namespace> <mustFind>: a copy of
  # one module with <old> replaced by <new> (asserted: exactly once, and the copy differs), scanned
  # by the manifest scanner over its own declarations.
  python3 - "$@" <<'EOF'
import sys
path, out, old, new, ns, must = sys.argv[1:]
src = open(path).read()
assert src.count(old) == 1, f"self-test: the plant anchor is not in {path} exactly once"
mutated = src.replace(old, new)
assert mutated != src and mutated.count(new) == 1, "self-test: the plant did not happen"
lines = mutated.split("\n")
last = max(i for i, l in enumerate(lines) if l.startswith("import "))
lines.insert(last + 1, "import Verify.ObjectiveManifest")
open(out, "w").write("\n".join(lines) + f"""
set_option maxHeartbeats 0 in
run_meta Minidregg.ObjectiveManifest.main {{
  label := "objective-manifest-plant", covers := fun _ => false, localPrefix := some `{ns},
  refuseMathlib := false, scanFloor := 1, mustFind := [`{must}] }}
""")
EOF
}

public_rows() { # public rows pinned for one module (the floor of a scratch copy of it)
  grep -v '^#' "$manifests/$1.tsv" | cut -f2 | grep -vc '^private ' || true
}

gate_proofs() {
  # every module the two manifest scripts import (the scanner, Verify.ObjectiveManifest, is rooted by Verify)
  local targets="ObjectiveProofs Theory.ObjectiveBendCheckpointRoundTrip Theory.ObjectiveBendExtensions Theory.ObjectiveBendDemandCapacity Verify.ObjectiveManifest"
  echo "== lake build $targets"
  "$lake" build $targets
  local failed=0 run script s
  local ns_c=Minidregg.Kernel.ObjectiveBendAdmissionSemantics ns_d=Minidregg.Theory.ObjectiveBendOpenRecursion
  for run in theory mathlib; do
    script=scripts/ObjectiveManifest.lean
    [ "$run" = mathlib ] && script=scripts/ObjectiveManifestMathlib.lean
    scratch_lean plant "$script" "$tmp/$run-plant.lean"
    scratch_lean noscan "$script" "$tmp/$run-noscan.lean"
  done
  # (c) the measured defect: an unused `(_vacuous : False)` premise on admitted_source_semantics
  # (W20-GATE-MUTATION left the old gate green under exactly this)
  local planted_c=1 planted_d=1
  scratch_module Kernel/ObjectiveBendAdmissionSemantics.lean "$tmp/premise.lean" \
    "    (admitted : Admitted prepared ingress writes guards) :
    runBounded" \
    "    (admitted : Admitted prepared ingress writes guards) (_vacuous : False) :
    runBounded" \
    "$ns_c" "$ns_c.admitted_source_semantics" || planted_c=0
  # (d) the redefinition defect: `Evaluates` (mentioned by lazy_fixed_function's statement, and
  # through DeepEvaluates' constructors by admitted_source_semantics') redefined to `True`; every
  # statement text stays byte-identical. The proofs that unfold it fail in the copy; the
  # declarations, with their statements, are still in its environment.
  scratch_module Theory/ObjectiveBendOpenRecursion.lean "$tmp/redefine.lean" \
    "def Evaluates (initial result : Term) : Prop := Steps initial result ∧ Value result" \
    "def Evaluates (initial result : Term) : Prop := True" \
    "$ns_d" "$ns_d.lazy_fixed_function" || planted_d=0
  # all scanner runs in parallel
  local jobs="theory mathlib theory-plant mathlib-plant theory-noscan mathlib-noscan"
  for run in $jobs; do
    script=$tmp/$run.lean
    [ "$run" = theory ] && script=scripts/ObjectiveManifest.lean
    [ "$run" = mathlib ] && script=scripts/ObjectiveManifestMathlib.lean
    manifest_run "$script" "$tmp/$run.out" "$tmp/$run.err" >"$tmp/$run.rc" &
  done
  [ "$planted_c" = 1 ] && manifest_run "$tmp/premise.lean" "$tmp/premise.out" "$tmp/premise.err" >"$tmp/premise.rc" &
  [ "$planted_d" = 1 ] && manifest_run "$tmp/redefine.lean" "$tmp/redefine.out" "$tmp/redefine.err" >"$tmp/redefine.rc" &
  wait
  local tool=(python3 "$manifest_tool" --pins "$manifests" --ledger "$ledger")
  for run in theory mathlib; do
    s=$(cat "$tmp/$run.rc")
    grep -av "warning\\|^Note:\\|^$" "$tmp/$run.err" || true
    if [ "$s" != 0 ] || [ ! -s "$tmp/$run.out" ]; then echo "objective-manifest ($run): FAILED (exit $s)"; failed=1; fi
  done
  [ "$failed" = 0 ] || return 1
  if "${tool[@]}" selftest "$tmp/theory.out" "$tmp/mathlib.out"; then :; else failed=1; fi
  for run in theory mathlib; do
    s=$(cat "$tmp/$run-plant.rc")
    if [ "$s" = 0 ] && "${tool[@]}" expect "$tmp/$run-plant.out" --plant Minidregg.ObjectiveManifest.Plant.planted --against "$tmp/$run.out" \
         --floor "$(grep -c '^R' "$tmp/$run.out" | awk '{print int($1 * 0.9)}')" >"$tmp/$run-plant.expect"; then
      echo "self-test ($run a) planted theorem: PASS ($(tail -1 "$tmp/$run-plant.expect"))"
    else
      echo "self-test ($run a) planted theorem: FAIL (exit $s)"; tail -20 "$tmp/$run-plant.expect" "$tmp/$run-plant.err" 2>/dev/null; failed=1
    fi
    s=$(cat "$tmp/$run-noscan.rc")
    if [ "$s" != 0 ] && grep -q "^objective-manifest[a-z-]*: instrument:" "$tmp/$run-noscan.err"; then
      echo "self-test ($run b) scan deleted: PASS (exit $s; $(grep -m1 "^objective-manifest[a-z-]*: instrument:" "$tmp/$run-noscan.err"))"
    else
      echo "self-test ($run b) scan deleted: FAIL (exit $s)"; head -20 "$tmp/$run-noscan.err"; failed=1
    fi
  done
  if [ "$planted_c" = 1 ] && [ -s "$tmp/premise.out" ] && "${tool[@]}" expect "$tmp/premise.out" \
       --changed "$ns_c.admitted_source_semantics=restated" \
       --floor "$(public_rows Kernel.ObjectiveBendAdmissionSemantics)" >"$tmp/premise.expect"; then
    echo "self-test (c) planted (_vacuous : False) on admitted_source_semantics: PASS ($(grep -m1 '^expect: ' "$tmp/premise.expect"))"
  else
    echo "self-test (c) planted (_vacuous : False) on admitted_source_semantics: FAIL"
    cat "$tmp/premise.expect" 2>/dev/null; head -20 "$tmp/premise.err" 2>/dev/null; failed=1
  fi
  if [ "$planted_d" = 1 ] && [ -s "$tmp/redefine.out" ] && "${tool[@]}" expect "$tmp/redefine.out" \
       --changed "$ns_d.lazy_fixed_function=redefined:$ns_d.Evaluates" --allow-downstream \
       --floor "$(public_rows Theory.ObjectiveBendOpenRecursion)" >"$tmp/redefine.expect"; then
    echo "self-test (d) redefined Evaluates := True under lazy_fixed_function: PASS ($(grep -m1 '^expect: ' "$tmp/redefine.expect"))"
  else
    echo "self-test (d) redefined Evaluates := True under lazy_fixed_function: FAIL"
    cat "$tmp/redefine.expect" 2>/dev/null; head -20 "$tmp/redefine.err" 2>/dev/null; failed=1
  fi
  if [ "$mode" = pin ] && [ "$failed" != 0 ]; then
    echo "objective-manifest: pin REFUSED: a self-test failed; nothing written"; return 1
  fi
  if "${tool[@]}" "$mode" "$tmp/theory.out" "$tmp/mathlib.out" | tee "$logs/manifest-$mode.log"; then :; else failed=1; fi
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
  *) echo "usage: $0 [proofs|c|cgen|transparency|all] [--pin|--draft]" >&2; exit 64 ;;
esac
