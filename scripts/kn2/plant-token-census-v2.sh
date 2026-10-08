#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

mode=${1:-}
case "$mode" in
  ignored-index|tautology|closed|unlisted-minter|positive|old-rule) ;;
  *)
    echo "usage: $0 {ignored-index|tautology|closed|unlisted-minter|positive|old-rule}" >&2
    exit 2
    ;;
esac

plant_tmp=$(mktemp -d)
cp TokenCensus.lean "$plant_tmp/TokenCensus.lean"
cp TokenCensus/Table.lean "$plant_tmp/Table.lean"

restore_sources() {
  cp "$plant_tmp/TokenCensus.lean" TokenCensus.lean
  cp "$plant_tmp/Table.lean" TokenCensus/Table.lean
  rm -r "$plant_tmp"
}
trap restore_sources EXIT

insert_after_positive() {
  local declaration=$1
  perl -0pi -e "s{#assert_axioms ProjectionWitness\.sound'\n}{#assert_axioms ProjectionWitness.sound'\n\n${declaration}\n}" TokenCensus.lean
}

select_witness() {
  local witness=$1
  perl -0pi -e "s{L1 Minidregg\.TokenCensus\.ProjectionWitness\.sound' \\|}{L1 ${witness} |}" TokenCensus/Table.lean
  grep -F "L1 ${witness} |" TokenCensus/Table.lean
}

expect_red() {
  local expected=$1
  local log="$plant_tmp/build.log"
  if lake build TokenCensus >"$log" 2>&1; then
    echo "plant unexpectedly stayed green: $mode" >&2
    exit 1
  fi
  grep -F "$expected" "$log"
}

case "$mode" in
  ignored-index)
    insert_after_positive "theorem ProjectionWitness.ignoresResult {request result : Nat}\n    (witness : ProjectionWitness request result) : request = 0 := witness.sound.1"
    select_witness "Minidregg.TokenCensus.ProjectionWitness.ignoresResult"
    grep -F "theorem ProjectionWitness.ignoresResult" TokenCensus.lean
    expect_red "ignores the bound token indices: [result]"
    ;;
  tautology)
    insert_after_positive "theorem ProjectionWitness.tautological {request result : Nat}\n    (witness : ProjectionWitness request result) : witness = witness := rfl"
    select_witness "Minidregg.TokenCensus.ProjectionWitness.tautological"
    grep -F "theorem ProjectionWitness.tautological" TokenCensus.lean
    expect_red "has a trivial conclusion"
    ;;
  closed)
    insert_after_positive "structure ClosedPlant where\n  private mk ::\n  payload : Nat\n\ntheorem ClosedPlant.w (_witness : ClosedPlant) : ∃ n : Nat, n = 5 := ⟨5, rfl⟩\n\n#assert_axioms ClosedPlant.w"
    perl -0pi -e 's{Minidregg\.Theory\.CanonicalReactiveView\.PreparedReaction\.mk}{Minidregg.TokenCensus.ClosedPlant.mk | TokenCensus | evidence | L1 Minidregg.TokenCensus.ClosedPlant.w | planted unindexed witness with a closed conclusion\nMinidregg.Theory.CanonicalReactiveView.PreparedReaction.mk}' TokenCensus/Table.lean
    grep -F "theorem ClosedPlant.w" TokenCensus.lean
    grep -F "Minidregg.TokenCensus.ClosedPlant.mk |" TokenCensus/Table.lean
    expect_red "ClosedPlant.mk: L1 witness Minidregg.TokenCensus.ClosedPlant.w has a conclusion closed over the bound inhabitant and its indices"
    ;;
  unlisted-minter)
    insert_after_positive "def ProjectionWitness.unlistedMinter : ProjectionWitness 0 0 := ⟨rfl, rfl⟩"
    grep -F "def ProjectionWitness.unlistedMinter" TokenCensus.lean
    expect_red "returns the bare evidence token Minidregg.TokenCensus.ProjectionWitness"
    ;;
  positive)
    grep -F "theorem ProjectionWitness.sound'" TokenCensus.lean
    grep -F "  witness.sound" TokenCensus.lean
    lake build TokenCensus
    echo "positive bare-projection witness accepted"
    ;;
  old-rule)
    perl -0pi -e 's{              for fault in ← l1WitnessFaults structName thm\.toName info do}{              let declared? : Option Expr := match info with
                | .thmInfo proved => some proved.value
                | .defnInfo definition => some definition.value
                | _ => none
              if let some value := declared? then
                let renamed ← lambdaTelescope value fun _ body => do
                  match body.consumeMData with
                  | .proj .. => pure true
                  | body =>
                      match body.getAppFn.constName? with
                      | some head => pure ((← getEnv).getProjectionFnInfo? head).isSome
                      | none => pure false
                if renamed then
                  faults := faults.push s!"{row.ctor}: L1 theorem {thm} is a renamed projection; name the proof field instead"
              for fault in ← l1WitnessFaults structName thm.toName info do}' TokenCensus.lean
    grep -F "is a renamed projection; name the proof field instead" TokenCensus.lean
    expect_red "ProjectionWitness.mk: L1 theorem Minidregg.TokenCensus.ProjectionWitness.sound' is a renamed projection"
    ;;
esac
