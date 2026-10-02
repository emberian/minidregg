/-
# Compiler.TurnCensusCoverage — the census rows track the admission constructors

`Kernel.TurnCensus` writes one row per `NativeHostReplay.NativeAdmission`
constructor in its own `Ctor` enumeration (it does not import the replay).
Nothing tied the two: `final-pay` and C3 added four constructors while
`every_admission_is_turn` still decided "all 33".  This module is the tie: it
fails to elaborate unless `TurnCensus.Ctor` and `NativeAdmission` have the same
constructor names (as sets; each list duplicate-free).  A new admission constructor therefore
cannot land without its census row, its negation and its refusal.

It is a build-time structural check over declaration names, not a theorem:
what it relates is the shape of two inductive types, which no proposition
about their values states.  It lives in `Compiler` because it is a `Lean`
metaprogram over Kernel declarations, and the import-tier table admits `Lean`
in Compiler (and Host), not in Kernel.
-/
import Lean
import Kernel.TurnCensus
import Kernel.NativeHostReplay

namespace Minidregg.Compiler.TurnCensusCoverage

open Lean Elab Command

/-- Fails unless the two inductives' constructor names agree as sets. -/
elab "#assert_census_covers_admissions" : command => do
  let env ← getEnv
  let ctorsOf (n : Name) : CommandElabM (List String) := do
    match env.find? n with
    | some (.inductInfo info) => pure (info.ctors.map fun c => c.getString!)
    | _ => throwError "#assert_census_covers_admissions: {n} is not an inductive"
  let admissions ← ctorsOf ``Minidregg.Kernel.NativeHostReplay.NativeAdmission
  let census ← ctorsOf ``Minidregg.Kernel.TurnCensus.Ctor
  unless admissions.length == census.length && admissions.all (· ∈ census) && census.all (· ∈ admissions) do
    let missing := admissions.filter (· ∉ census)
    let extra := census.filter (· ∉ admissions)
    throwError m!"TurnCensus.Ctor does not track NativeAdmission: missing rows {missing}, rows with no constructor {extra}, admissions {admissions.length}, census {census.length}"

#assert_census_covers_admissions

end Minidregg.Compiler.TurnCensusCoverage
