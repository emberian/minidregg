/-
# scripts/ObjectiveSnapshot.lean -- the Objective Bend statement and axiom snapshot

Prints, for every declaration of a module whose name starts with
`Theory.ObjectiveBend` (compiler-generated names excluded):

* `S <kind> <name> : <type>` -- the ELABORATED type, pretty-printed with full
  names at unbounded width, whitespace collapsed to single spaces.  For a
  definition whose type ends in `Prop` (a hypothesis, an invariant) the body
  follows as `:= <body>`: such a definition means its body.  For any other
  definition a structural hash of the body follows as `#<hash>`.
* `A <name> : <axioms>` -- the exact axiom set of every theorem and definition
  (sorted; `-` for none).

`scripts/check-objective-proofs.sh` writes the two kinds of line to
`scripts/gates/objective-statements.snapshot` and
`scripts/gates/objective-axioms.pin` and fails on any difference from the
checked-in copies.  An announced change is a commit that regenerates them
(`scripts/check-objective-proofs.sh --update`); the diff of the snapshot IS the
announcement.

Run: `lake env lean scripts/ObjectiveSnapshot.lean`

The environment is the Theory modules of the `ObjectiveProofs` target, imported one by one, not
the target itself: the rows are pretty-printed, and an imported Mathlib changes the rendering of
unchanged statements (`ℕ` for `Nat`, `∀ f ∈ fs,` for `∀ f, f ∈ fs →`, `f.2` for `f.snd`). The
target gained a Mathlib-importing Kernel module (Kernel.ObjectiveBendAdmissionSemantics, d67fd95d)
and 458 unchanged statements re-rendered. The scan refuses to run with any `Mathlib` module in
the environment, so that can never again pass for (or hide) a statement change.
-/
import Theory.ObjectiveBendDemandInvariant
import Theory.ObjectiveBendDemandTyping
import Theory.ObjectiveBendDemandPreservation
import Theory.ObjectiveBendDemandAdequacy
import Theory.ObjectiveBendDemandCompleteness
import Theory.ObjectiveBendDemandDataSoundness
import Theory.ObjectiveBendCheckpointRoundTrip
import Theory.ObjectiveBendExtensions
import Theory.ObjectiveBendDemandCapacity
import Theory.ObjectiveBendDemandCollectProofs

open Lean Meta

namespace Minidregg.ObjectiveSnapshot

def modulePrefix : String := "Theory.ObjectiveBend"

/-- Self-test switch (scripts/check-objective-proofs.sh flips it in a scratch
copy): count this file's own declarations as if they were in the prefix. -/
def includeLocal : Bool := false

/-- A working scan finds at least this many declarations, and these by name.
A scan that silently stopped walking lands under the floor. -/
def scanFloor : Nat := 1500
def mustFind : List Name :=
  [`Minidregg.Theory.ObjectiveBendDemandMachine.stepRaw,
   `Minidregg.Theory.ObjectiveBendDemandPreservation.typed_stepRaw_preserved,
   `Minidregg.Theory.ObjectiveBendDemandAdequacy.graph_stepRaw]

/-- Compiler-generated or lazily realized names: their presence depends on what
some proof happened to use, not on what the module states. -/
def generatedTails : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "ibelow", "binductionOn",
   "noConfusion", "noConfusionType", "ndrec", "ndrecOn", "sizeOf_spec", "injEq", "inj",
   "toCtorIdx", "ctorIdx", "eq_def", "congr_simp", "induct", "mutual_induct", "fun_cases",
   "induct_unfolding", "eq_unfold", "ctorElim", "ctorElimType"]

/-- `s` is `pre` followed by an upper-case letter (`instReprCell`, `decEqTerm`),
the shape of a derived instance or its helper. -/
def upperAfter (s pre : String) : Bool :=
  s.startsWith pre && match (s.toList.drop pre.length).head? with
    | some c => c.isUpper
    | none => false

def generatedComponent (s : String) : Bool :=
  generatedTails.contains s || s.startsWith "match_" || s.startsWith "proof_"
    || s.startsWith "_" || (s.startsWith "eq_" && (s.toList.drop 3).all Char.isDigit)
    || upperAfter s "inst" || upperAfter s "decEq" || upperAfter s "repr"

def generated (name : Name) : Bool :=
  let user := (privateToUserName? name).getD name
  user.isInternalDetail || user.components.any fun c => match c with
    | .str _ s => generatedComponent s
    | _ => false

def oneLine (s : String) : String :=
  " ".intercalate ((s.split Char.isWhitespace).toList.map (·.toString) |>.filter (!·.isEmpty))

def ppOneLine (e : Expr) : MetaM String := do
  return oneLine (toString (← ppExpr e))

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .axiomInfo _ => "axiom"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

def endsInProp (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun _ body => return body.isProp

def run : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array (String × String) := #[]
  let mut axiomRows : Array (String × String) := #[]
  let mut found : Array Name := #[]
  -- SCAN-BEGIN
  for (name, info) in env.constants.toList do
    let inPrefix := match env.getModuleIdxFor? name with
      | some idx => match env.header.moduleNames[idx.toNat]? with
        | some mod => mod.toString.startsWith modulePrefix
        | none => false
      | none => includeLocal && (`Minidregg.ObjectiveSnapshot.Plant).isPrefixOf name
    unless inPrefix do continue
    if generated name then continue
    let kind := kindOf info
    if kind == "rec" then continue
    let shown := match privateToUserName? name with
      | some user => s!"private {user}"
      | none => toString name
    let type ← ppOneLine info.type
    let mut line := s!"S {kind} {shown} : {type}"
    if let .defnInfo d := info then
      if ← endsInProp info.type then
        line := line ++ s!" := {← ppOneLine d.value}"
      else
        line := line ++ s!" #{d.value.hash}"
    rows := rows.push (shown, line)
    if kind == "theorem" || kind == "def" || kind == "opaque" then
      let axioms := (← collectAxioms name).map toString |>.qsort (· < ·)
      let shownAxioms := if axioms.isEmpty then "-" else ", ".intercalate axioms.toList
      axiomRows := axiomRows.push (shown, s!"A {shown} : {shownAxioms}")
    found := found.push name
  -- SCAN-END
  let mut failures : Array String := #[]
  if (← getEnv).header.moduleNames.any (fun m => (`Mathlib).isPrefixOf m) then
    failures := failures.push "instrument: a Mathlib module is in the snapshot environment; its delaborators change the rendering of unchanged statements"
  if rows.size < scanFloor then
    failures := failures.push s!"instrument: only {rows.size} declarations scanned (floor {scanFloor})"
  for n in mustFind do
    unless found.contains n do failures := failures.push s!"instrument: {n} not found"
  unless failures.isEmpty do
    for f in failures do IO.eprintln s!"objective-snapshot: {f}"
    throwError s!"objective-snapshot: {failures.size} instrument failure(s)"
  for (_, line) in rows.qsort (fun a b => a.1 < b.1) do IO.println line
  for (_, line) in axiomRows.qsort (fun a b => a.1 < b.1) do IO.println line
  IO.eprintln s!"objective-snapshot: {rows.size} declarations, {axiomRows.size} axiom rows"

def main : MetaM Unit :=
  withOptions (fun o => o |>.set `pp.fullNames true |>.set `format.width (1000000 : Nat)
    |>.set `pp.mvars false |>.set `pp.proofs true) run

end Minidregg.ObjectiveSnapshot

set_option maxHeartbeats 0 in
run_meta Minidregg.ObjectiveSnapshot.main
