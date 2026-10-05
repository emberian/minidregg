/-
# Verify/ObjectiveSnapshot.lean -- the scanner behind the Objective statement and axiom snapshots

One scanner, two environments (scripts/check-objective-proofs.sh `proofs`):

* scripts/ObjectiveSnapshot.lean -- the `Theory.ObjectiveBend*` modules, in an environment
  with no Mathlib module (refused: Mathlib re-renders unchanged statements).
  Pins scripts/gates/objective-statements.snapshot + objective-axioms.pin.
* scripts/ObjectiveSnapshotMathlib.lean -- every other module of this repository in the import
  closure of `ObjectiveProofs` (Kernel, Compiler, Pred, Selvage, the rest of Theory), in an
  environment that imports `ObjectiveProofs` and therefore Mathlib.
  Pins scripts/gates/objective-statements-mathlib.snapshot + objective-axioms-mathlib.pin.

Every declaration of a covered module (compiler-generated names excluded) prints as

* `S <kind> <name> : <type>` -- the ELABORATED type, pretty-printed with full names at
  unbounded width, whitespace collapsed.  A definition whose type ends in `Prop` (a
  hypothesis, an invariant) is followed by `:= <body>`: such a definition means its body.
  Any other definition is followed by `#<hash>` of its body.
* `A <name> : <axioms>` -- the exact axiom set of every theorem, definition and opaque
  (sorted; `-` for none).

The scan region is delimited by `SCAN-BEGIN`/`SCAN-END`: the gate's self-test deletes it in a
scratch copy and requires the instrument floor to fail the run.
-/
import Lean

open Lean Meta

namespace Minidregg.ObjectiveSnapshot

/-- What one snapshot run covers and what a working scan of it must find. -/
structure Config where
  /-- Prefix of every diagnostic line (`objective-snapshot`, `objective-snapshot-mathlib`). -/
  label : String
  /-- The modules whose declarations this run prints. -/
  covers : Name → Bool
  /-- Self-test switch: count the running file's own `Minidregg.ObjectiveSnapshot.Plant.*`
  declarations as covered. -/
  includeLocal : Bool
  /-- Refuse to run with any `Mathlib` module in the environment. -/
  refuseMathlib : Bool
  /-- A working scan prints at least this many declarations... -/
  scanFloor : Nat
  /-- ...and these by name. A scan that silently stopped walking lands under one of them. -/
  mustFind : List Name
  /-- Instrument failures the running script found before the scan (coverage checks). -/
  preFailures : Array String := #[]

/-- Compiler-generated or lazily realized names: their presence depends on what
some proof happened to use, not on what the module states. -/
def generatedTails : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "ibelow", "binductionOn",
   "noConfusion", "noConfusionType", "ndrec", "ndrecOn", "sizeOf_spec", "injEq", "inj",
   "toCtorIdx", "ctorIdx", "eq_def", "congr_simp", "induct", "mutual_induct", "fun_cases",
   "induct_unfolding", "fun_cases_unfolding", "eq_unfold", "ctorElim", "ctorElimType"]

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

def shownName (name : Name) : String :=
  match privateToUserName? name with
  | some user => s!"private {user}"
  | none => toString name

/-- The `S` row of one declaration. -/
def statementRow (name : Name) (info : ConstantInfo) : MetaM String := do
  let mut line := s!"S {kindOf info} {shownName name} : {← ppOneLine info.type}"
  if let .defnInfo d := info then
    if ← endsInProp info.type then
      line := line ++ s!" := {← ppOneLine d.value}"
    else
      line := line ++ s!" #{d.value.hash}"
  return line

/-- The `A` row of one declaration, if it has one. -/
def axiomRow? (name : Name) (info : ConstantInfo) : MetaM (Option String) := do
  let kind := kindOf info
  unless kind == "theorem" || kind == "def" || kind == "opaque" do return none
  let axioms := (← collectAxioms name).map toString |>.qsort (· < ·)
  let shownAxioms := if axioms.isEmpty then "-" else ", ".intercalate axioms.toList
  return some s!"A {shownName name} : {shownAxioms}"

/-- The `S` row of a named declaration of the current environment, printed alone
(the planted-premise self-test elaborates a mutated module and prints one row). -/
def printStatementRow (name : Name) : MetaM Unit :=
  withOptions (fun o => o |>.set `pp.fullNames true |>.set `format.width (1000000 : Nat)
      |>.set `pp.mvars false |>.set `pp.proofs true) do
    let some info := (← getEnv).find? name | throwError "objective-snapshot: {name} not in the environment"
    IO.println (← statementRow name info)

/-- The modules of `roots`' import closure, `roots` included, as recorded in the environment
header (a root absent from the environment contributes nothing). -/
def importClosure (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let idxOf : NameMap Nat := env.header.moduleNames.size.fold (init := {}) fun i _ m =>
    m.insert env.header.moduleNames[i] i
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  while true do
    match todo with
    | [] => break
    | m :: rest =>
      todo := rest
      if seen.contains m then continue
      let some i := idxOf.find? m | continue
      seen := seen.insert m
      if let some data := env.header.moduleData[i]? then
        todo := data.imports.toList.map (·.module) ++ todo
  return seen

def run (cfg : Config) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array (String × String) := #[]
  let mut axiomRows : Array (String × String) := #[]
  let mut found : Array Name := #[]
  -- SCAN-BEGIN
  for (name, info) in env.constants.toList do
    let covered := match env.getModuleIdxFor? name with
      | some idx => match env.header.moduleNames[idx.toNat]? with
        | some mod => cfg.covers mod
        | none => false
      | none => cfg.includeLocal && (`Minidregg.ObjectiveSnapshot.Plant).isPrefixOf name
    unless covered do continue
    if generated name then continue
    if kindOf info == "rec" then continue
    let shown := shownName name
    rows := rows.push (shown, ← statementRow name info)
    if let some a ← axiomRow? name info then axiomRows := axiomRows.push (shown, a)
    found := found.push name
  -- SCAN-END
  let mut failures := cfg.preFailures
  if cfg.refuseMathlib && env.header.moduleNames.any (fun m => (`Mathlib).isPrefixOf m) then
    failures := failures.push "instrument: a Mathlib module is in the snapshot environment; its delaborators change the rendering of unchanged statements"
  if rows.size < cfg.scanFloor then
    failures := failures.push s!"instrument: only {rows.size} declarations scanned (floor {cfg.scanFloor})"
  for n in cfg.mustFind do
    unless found.contains n do failures := failures.push s!"instrument: {n} not found"
  unless failures.isEmpty do
    for f in failures do IO.eprintln s!"{cfg.label}: {f}"
    throwError s!"{cfg.label}: {failures.size} instrument failure(s)"
  for (_, line) in rows.qsort (fun a b => a.1 < b.1) do IO.println line
  for (_, line) in axiomRows.qsort (fun a b => a.1 < b.1) do IO.println line
  IO.eprintln s!"{cfg.label}: {rows.size} declarations, {axiomRows.size} axiom rows"

def main (cfg : Config) : MetaM Unit :=
  withOptions (fun o => o |>.set `pp.fullNames true |>.set `format.width (1000000 : Nat)
    |>.set `pp.mvars false |>.set `pp.proofs true) (run cfg)

end Minidregg.ObjectiveSnapshot
