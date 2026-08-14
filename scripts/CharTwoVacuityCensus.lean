/-
# scripts/CharTwoVacuityCensus.lean -- the detector the char-2 traps needed

`Selvage.CharTwoWall` proves that `FoldingData`/`FoldingTower` are EMPTY at
characteristic two, and `Compiler.FriQueryVerifierAir` proves the same of the
`2 * half = 1` deployment label.  Those theorems answer a vacuous claim once it
is in front of you.  They do NOT notice one being written.

That is the whole failure mode: an agent ports the multiplicative proximity
cone "to a binary field", every file compiles, every `#print axioms` pin passes,
and 185 declarations become vacuously true with no diagnostic anywhere.  A
documented wound is not a detected one.  This is the detector.

**The question, mechanically, over the whole environment:**

> which declarations that we own mention a CHARACTERISTIC-TWO-DEAD name in
> their type, while also carrying characteristic-two evidence in that same
> type?

Any hit is a theorem that is true of nothing.  There are zero today, and the
allowlist is empty on purpose: this file FAILS on the first one.

**Teeth for the instrument itself.**  A detector that stopped detecting would
look exactly like a clean tree, so `selfTest` runs the classifier on synthetic
expressions built here — one that must fire, two that must not — before it
reports.  It also pins that every registered dead name still resolves, so a
rename silently emptying the registry is a failure and not a pass.

Run: `lake env lean scripts/CharTwoVacuityCensus.lean`
     (or `scripts/check-char2-vacuity.sh`)
-/
import Minidregg

open Lean Elab Meta

namespace Minidregg.CharTwoVacuityCensus

/-- Names we own.  The census is about this tree, not Mathlib. -/
def ours (name : Name) : Bool := (`Minidregg).isPrefixOf name

/-- Compiler-generated satellites, which mention their own type for structural
reasons and would mask nothing useful. -/
def isGenerated (name : Name) : Bool :=
  match name with
  | .str _ tail =>
      ["rec", "recOn", "casesOn", "below", "brecOn", "ibelow", "binductionOn",
       "noConfusion", "noConfusionType", "ndrec", "ndrecOn", "sizeOf_spec",
       "injEq", "ofNat", "toCtorIdx", "ctorIdx", "eq_def"].contains tail
      || tail.startsWith "match_" || tail.startsWith "proof_"
      || tail.startsWith "eq_" || tail.startsWith "_"
  | _ => false

/-- **The registry.**  Names whose every inhabitant is refuted at
characteristic two, each paired with the theorem that refutes it.  Extend this
when a new char-2 wall is proved; never extend it with a name whose emptiness
is only believed. -/
def charTwoDead : List (Name × Name) :=
  [(`Minidregg.Selvage.FoldingData,
    `Minidregg.Selvage.foldingData_charTwo_False),
   (`Minidregg.Selvage.FoldingTower,
    `Minidregg.Selvage.foldingTower_charTwo_False)]

def deadNames : List Name := charTwoDead.map Prod.fst

/-- Field constants whose characteristic is two by a proved theorem in this
tree.  A type mentioning one of these is characteristic-two evidence even when
no `CharP` binder is written out. -/
def binaryFields : List Name :=
  [`Minidregg.Theory.binaryTower,
   `Minidregg.Compiler.BinaryTower256Profile.Tower256]

/-- Every constant a type mentions. -/
def mentioned (type : Expr) : NameSet :=
  type.foldConsts ∅ fun name acc => acc.insert name

/-- Characteristic-two evidence in a type: an explicit `CharP` binder, or one
of the tree's proved binary fields. -/
def hasCharTwoEvidence (names : NameSet) : Bool :=
  names.contains `CharP || binaryFields.any names.contains

/-- A dead name mentioned by a type, if any. -/
def deadMention (names : NameSet) : Option Name :=
  deadNames.find? names.contains

/-- **The classifier.**  A type is a char-2 vacuity hit when it quantifies over
a refuted carrier AND carries characteristic-two evidence. -/
def isVacuityHit (type : Expr) : Option Name :=
  let names := mentioned type
  if hasCharTwoEvidence names then deadMention names else none

/-! ## Teeth: the classifier must fire, and must not over-fire -/

private def synthetic (consts : List Name) : Expr :=
  consts.foldl (fun acc name => .app acc (.const name [])) (.sort .zero)

def selfTest : MetaM Unit := do
  let env ← getEnv
  let mut failures : Array String := #[]
  -- every registered name and its evidence must still resolve
  for (carrier, evidence) in charTwoDead do
    unless env.contains carrier do
      failures := failures.push s!"{carrier}: registered dead carrier is absent (renamed?)"
    unless env.contains evidence do
      failures := failures.push s!"{carrier}: emptiness evidence {evidence} is absent"
  for field in binaryFields do
    unless env.contains field do
      failures := failures.push s!"{field}: registered binary field is absent (renamed?)"
  -- MUST FIRE: dead carrier + CharP in one type
  let positive := synthetic [`Minidregg.Selvage.FoldingData, `CharP]
  if (isVacuityHit positive).isNone then
    failures := failures.push "classifier did NOT fire on carrier + CharP"
  -- MUST FIRE: dead carrier + a proved binary field, no CharP binder
  let positiveField :=
    synthetic [`Minidregg.Selvage.FoldingTower, `Minidregg.Compiler.BinaryTower256Profile.Tower256]
  if (isVacuityHit positiveField).isNone then
    failures := failures.push "classifier did NOT fire on carrier + binary field"
  -- MUST NOT FIRE: the carrier alone (the whole multiplicative tree does this)
  if (isVacuityHit (synthetic [`Minidregg.Selvage.FoldingData])).isSome then
    failures := failures.push "classifier fired on a bare carrier"
  -- MUST NOT FIRE: characteristic two alone (the whole additive tree does this)
  if (isVacuityHit (synthetic [`CharP, `Minidregg.Compiler.BinaryTower256Profile.Tower256])).isSome then
    failures := failures.push "classifier fired on bare characteristic-two evidence"
  if failures.isEmpty then
    IO.println s!"self-test                   : PASS ({charTwoDead.length} dead carriers pinned, 4 classifier probes)"
  else
    for failure in failures do IO.eprintln s!"char2-vacuity self-test FAILED: {failure}"
    throwError "char-2 vacuity census self-test failed"

/-! ## The one exemption, and it is structural

The wall theorems themselves quantify over a refuted carrier at characteristic
two — that is exactly what `foldingData_charTwo_False` says, and it has to be
sayable somewhere.  So ONE module is exempt: the module whose entire job is
naming the emptiness.  The exemption is by home module, not by a list of
declaration names, so it cannot quietly grow to cover a real hit.

There is no allowlist beyond it.  A char-2 vacuous declaration anywhere else is
never a thing to grandfather: either it is refused (state it over the additive
carriers) or it is deleted. -/
def wallModule : Name := `Selvage.CharTwoWall

def homeModule (env : Environment) (name : Name) : Name :=
  ((env.getModuleIdxFor? name).bind fun idx =>
    env.header.moduleNames[idx.toNat]?).getD `«?»

def run : MetaM Unit := do
  let env ← getEnv
  selfTest
  let mut hits : Array (Name × Name × Name) := #[]
  let mut exempt := 0
  let mut scanned := 0
  for (name, info) in env.constants.toList do
    unless ours name && !isGenerated name do continue
    scanned := scanned + 1
    if let some carrier := isVacuityHit info.type then
      let home := homeModule env name
      if home == wallModule then
        exempt := exempt + 1
      else
        hits := hits.push (name, carrier, home)
  -- ⚑ Teeth on the exemption: the wall module must still CONTAIN wall theorems.
  -- Without this, deleting `Selvage/CharTwoWall.lean` would read as a clean run.
  if exempt == 0 then
    IO.eprintln s!"char2-vacuity FAILED: {wallModule} names no emptiness theorem"
    IO.eprintln "the wall was deleted or renamed; the exemption now covers nothing"
    throwError "char-2 vacuity wall module is empty"
  IO.println s!"declarations scanned        : {scanned}"
  IO.println s!"dead carriers registered    : {charTwoDead.length}"
  IO.println s!"exempt (the wall itself)    : {exempt} in {wallModule}"
  IO.println s!"CHAR-2 VACUOUS declarations : {hits.size}"
  if hits.isEmpty then
    IO.println ""
    IO.println "no declaration outside the wall quantifies over a characteristic-two-"
    IO.println "refuted carrier: the multiplicative and additive cones are disjoint."
  else
    IO.println ""
    for (name, carrier, home) in hits do
      IO.eprintln s!"  VACUOUS: {name}    [{home}]  quantifies over {carrier}"
    IO.eprintln ""
    IO.eprintln "Each of these is true of NOTHING.  See Selvage/CharTwoWall.lean:"
    IO.eprintln "state it over Selvage.AdditiveFriTower / AdditiveProximity instead."
    throwError "char-2 vacuity census found {hits.size} vacuous declaration(s)"

end Minidregg.CharTwoVacuityCensus

run_meta Minidregg.CharTwoVacuityCensus.run
