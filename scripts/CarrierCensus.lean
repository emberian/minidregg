/-
# scripts/CarrierCensus.lean -- the query ATLAS law 2 has always required

Law 2 asks for "declaration-level `satisfiable` + `teeth` + premise-inhabitation
(`∃ s : PremiseType`), CI-gated beside the axiom pin", and law 1 insists the
unrealized census is "a query, never a hand-count".  The axiom-pin half of that
gate exists (823 `#guard_msgs` pins).  This is the other half.

The question it answers, mechanically, over the whole environment:

> which `structure`s and `inductive`s declared in this tree are used as
> hypotheses somewhere, and are produced NOWHERE outside their own defining
> module?

Those are the carriers with no witness.  Every theorem quantified over one is
conditional on a type nobody has shown inhabited, which is the exact shape of
`VerifiedHistoryHead` before `d257fe9` and of all four `CellState.Schema`
materializers before `MaterializerCardinality` proved them empty.

**What this does and does not decide.**  It is a *reachability* query, not a
proof of emptiness.  An unwitnessed carrier may be perfectly inhabitable and
merely unbuilt; `MaterializerCardinality` had to prove emptiness separately.
What the census guarantees is that nobody has to get lucky to find the
candidates.  It reports; a human or a proof decides.

Run: `lake env lean scripts/CarrierCensus.lean`
-/
import Minidregg

open Lean Elab Meta

namespace Minidregg.CarrierCensus

/-- Names we own.  The census is about this tree, not Mathlib. -/
def ours (name : Name) : Bool := (`Minidregg).isPrefixOf name

/-- Declarations the census must ignore: the compiler-generated satellites of a
structure or inductive, which mention their own type for structural reasons and
would otherwise mask a genuinely unwitnessed carrier. -/
def generatedSuffix : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "ibelow", "binductionOn",
   "noConfusion", "noConfusionType", "ndrec", "ndrecOn", "sizeOf_spec",
   "injEq", "ofNat", "toCtorIdx", "ctorIdx", "eq_def", "match_1", "proof_1"]

def isGenerated (name : Name) : Bool :=
  match name with
  | .str _ tail => generatedSuffix.contains tail || tail.startsWith "match_"
      || tail.startsWith "proof_" || tail.startsWith "eq_" || tail.startsWith "_"
  | _ => false

/-- The head constant of a declaration's result type, after stripping binders. -/
def resultHead (type : Expr) : MetaM (Option Name) := do
  forallTelescopeReducing type fun _ body => do
    let body ← whnf body
    return body.getAppFn.constName?

/-- Every constant this declaration's type MENTIONS, which is how a carrier
appearing only in hypothesis position is detected. -/
def mentioned (type : Expr) : NameSet :=
  type.foldConsts ∅ fun name acc => acc.insert name

structure Report where
  carriers : Array Name := #[]
  producedOutside : NameSet := ∅
  usedAsHypothesis : NameSet := ∅
  homeModule : Std.HashMap Name Name := ∅
  /-- How many declarations quantify over this carrier.  A carrier nothing
  builds and nothing uses is not interesting; a carrier nothing builds and
  sixty theorems quantify over is the whole point. -/
  hypothesisCount : Std.HashMap Name Nat := ∅
  /-- Carriers with a nullary constructor are inhabited on sight; reporting
  them would be noise that hides the real answers. -/
  triviallyInhabited : NameSet := ∅

/-- Walk the environment once, classifying every declaration. -/
def survey : MetaM Report := do
  let env ← getEnv
  let mut report : Report := {}
  -- pass 1: the carriers we own, and where each lives
  for (name, info) in env.constants.toList do
    unless ours name && !isGenerated name do continue
    match info with
    | .inductInfo info =>
        report := { report with carriers := report.carriers.push name }
        -- a constructor whose type is the carrier itself, with no arguments,
        -- inhabits it immediately
        for ctor in info.ctors do
          if let some (.ctorInfo ci) := env.find? ctor then
            if ci.numFields == 0 then
              report := { report with
                triviallyInhabited := report.triviallyInhabited.insert name }
        if let some idx := env.getModuleIdxFor? name then
          if let some mod := env.header.moduleNames[idx.toNat]? then
            report := { report with homeModule := report.homeModule.insert name mod }
    | _ => pure ()
  let carrierSet : NameSet := report.carriers.foldl (fun acc n => acc.insert n) ∅
  -- pass 2: who produces a carrier, and from which module
  for (name, info) in env.constants.toList do
    unless ours name && !isGenerated name do continue
    let some head ← resultHead info.type | continue
    if carrierSet.contains head then
      let producerModule :=
        (env.getModuleIdxFor? name).bind fun idx => env.header.moduleNames[idx.toNat]?
      let carrierModule := report.homeModule[head]?
      -- a producer counts only if it lives outside the carrier's own module
      if producerModule != carrierModule then
        report := { report with producedOutside := report.producedOutside.insert head }
    -- anything the type merely mentions counts as hypothesis use
    for used in (mentioned info.type).toList do
      if carrierSet.contains used && used != head then
        report := { report with
          usedAsHypothesis := report.usedAsHypothesis.insert used
          hypothesisCount :=
            report.hypothesisCount.insert used
              ((report.hypothesisCount[used]?.getD 0) + 1) }
  return report

/-- **Teeth for the instrument itself.**  A census that silently stopped
detecting anything would look exactly like a clean tree, so it is pinned
against carriers whose answer is already known by construction: five that were
given witnesses on 2026-08-10, and one that was found unwitnessed by hand the
same night.  If any of these flips, the query is broken, not the tree. -/
def mustBeWitnessed : List Name :=
  [`Minidregg.Assurance.SemanticHistoryFamily.VerifiedHistoryHead,
   `Minidregg.Theory.CellState.ValidatedPatch,
   `Minidregg.Theory.TypedAuthorization.Authorized,
   `Minidregg.Theory.AcceptedCellEffect,
   `Minidregg.Kernel.MultiCellHyperedge.Commit]

def mustBeUnwitnessed : List Name :=
  [`Minidregg.Assurance.SemanticHistoryTower256CheckpointGame.JointGameFamily]

def selfTest (report : Report) (unwitnessed : NameSet) : MetaM Unit := do
  let mut failures : Array String := #[]
  for name in mustBeWitnessed do
    unless report.carriers.contains name do
      failures := failures.push s!"{name}: not a carrier at all (renamed?)"
    if unwitnessed.contains name then
      failures := failures.push s!"{name}: expected WITNESSED, census says unwitnessed"
  for name in mustBeUnwitnessed do
    unless report.carriers.contains name do
      failures := failures.push s!"{name}: not a carrier at all (renamed?)"
    unless unwitnessed.contains name do
      failures := failures.push s!"{name}: expected UNWITNESSED, census says witnessed"
  if failures.isEmpty then
    IO.println s!"self-test                   : PASS ({mustBeWitnessed.length} witnessed, {mustBeUnwitnessed.length} unwitnessed)"
  else
    for failure in failures do IO.eprintln s!"census self-test FAILED: {failure}"
    throwError "carrier census self-test failed"

def run : MetaM Unit := do
  let report ← survey
  let mut unwitnessed : Array (Nat × Name × Name) := #[]
  let mut trivialSkipped := 0
  for carrier in report.carriers do
    unless report.usedAsHypothesis.contains carrier
        && !report.producedOutside.contains carrier do continue
    if report.triviallyInhabited.contains carrier then
      trivialSkipped := trivialSkipped + 1
      continue
    unwitnessed := unwitnessed.push
      (report.hypothesisCount[carrier]?.getD 0, carrier,
       report.homeModule[carrier]?.getD `«?»)
  -- most load-bearing first: the ranking is the product, not the raw list
  let sorted := unwitnessed.qsort fun a b => a.1 > b.1
  let unwitnessedSet : NameSet :=
    unwitnessed.foldl (fun acc entry => acc.insert entry.2.1) ∅
  selfTest report unwitnessedSet
  IO.println s!"carriers declared           : {report.carriers.size}"
  IO.println s!"produced outside home       : {report.producedOutside.toList.length}"
  IO.println s!"skipped, nullary ctor       : {trivialSkipped}"
  IO.println s!"UNWITNESSED, load-bearing   : {sorted.size}"
  IO.println ""
  IO.println "rank by how many declarations quantify over the carrier:"
  IO.println ""
  for (count, carrier, mod) in sorted.toList.take 40 do
    IO.println s!"  {count}\t{carrier}    [{mod}]"

end Minidregg.CarrierCensus

run_meta Minidregg.CarrierCensus.run
