/-
# scripts/HypothesisLedger.lean -- the statement audit as an instrument

The scar this exists for: a theorem that is TRUE WITH AN EMPTY PREMISE.  A
soundness apex proved over a hypothesis no instance satisfies; a hypothesis
later proved outright while every consumer still binds it; an open hypothesis
nobody ever showed satisfiable.  `#assert_axioms` is blind to all three, and a
one-off reading is blind to the next one.  This query runs over the whole
environment on every invocation.

**Population.**  A *hypothesis family* is a constant we own (`Minidregg.*`, not
compiler-generated) that is a `def`/`abbrev`/`structure`/`class`/`inductive`
whose type ends in `Prop` (`D : Prop`, or `D : A → … → Prop` for a
parameterised hypothesis such as `HaboeckTheorem2`).

**Consumers.**  A theorem `T` consumes `D` when one of its leading binders
(explicit, implicit or instance) is a proposition with an atom `D …` -- the
binder type, after stripping its own `∀`s and splitting `∧`, has head `D`.
A binder of the form `¬ D …`, and a binder `D …` of a theorem concluding
`False`, are refutations, not consumption.

**Witnesses.**  The conclusion of every constant we own (theorems and
Prop-valued definitions) is split into atoms through `∧`, `∃` (the bound
variable becomes an existential witness), inner `∀` (variables and
hypotheses join the theorem's), and `¬`/`→ False` (polarity flips).  An atom
is `D args` with `D` fully applied.  It is

* **general** when its arguments are pairwise-distinct universally bound
  variables and the statement carries NO propositional hypothesis (explicit,
  instance or inner) -- it proves `∀ params, D params` (or its negation);
* an **instance** when it carries no propositional hypothesis but is not
  general (a concrete argument, a repeated variable, or an `∃`-bound one) --
  it exhibits a satisfying (or refuting) point -- AND every binder its
  arguments mention is shown inhabited (a type, an instance argument, a type
  with a `Nonempty` instance); `∀ a : Accepted, D (f a)` over a carrier nobody
  showed inhabited exhibits nothing and is conditional (D6, plant `Unshowable`);
* **conditional** when it carries a propositional hypothesis.  Listed, never
  counted: a witness that holds under an unexamined premise is the scar again.

**Status per family.**  PROVED: a general positive atom.  REFUTED: a general
negative atom.  (Both: INCONSISTENT.)  OPEN otherwise.

**Verdict per family with at least one consumer.**

| status  | verdict | meaning |
|---|---|---|
| REFUTED | VACUOUS (RED) | every consumer is true of nothing |
| any, a refutation COVERS a consumer | VACUOUS (RED) | that consumer is true of nothing (see `covers`) |
| PROVED  | STALE (yellow) | the consumers can drop the premise |
| OPEN, sat + ref instances | GREEN | the floor is satisfiable and refutable |
| OPEN, missing either | TOOTHLESS | no named instance shows the floor has teeth |
| INCONSISTENT | RED | the environment proves the family and its negation |

TOOTHLESS is RED for a family the tree names as an ASSUMPTION (`Assumption
tier`, below) and reported, not gated, for the remaining Prop-valued
definitions (predicates over data).  Families with no consumer are counted and
not ranked.

**Assumption tier.**  A family whose doc comment says it is a hypothesis
(`hypothesis`, `assumed`, `assumption`, `seam`, `premise`, `obligation`,
`not proved`, `unproved`, `conjectur`), or whose type is exactly `Prop`
(a closed statement can only be a claim, never a predicate over data).  The
tier is where `GameSlotBound`, `HaboeckTheorem2` and `HashEqHiding` live
(`PolishchukSpielmanCramer`, proved, has no consumer).  The rest are predicates over data; their TOOTHLESS count
is the honest frontier, printed but not a gate (red as a steady state hides
everything).

**Covered consumers.**  "Refuted only when refuted generally" let the
un-fixed Polishchuk--Spielman floor read OPEN while its keystone consumer sat
at `ZMod 5`, exactly where it was false.  A family refuted at any instance is
not thereby false everywhere (a floor must be refutable: `MaskedOpeningHiding`
is refuted at an F₅ triple by design), but a refutation that unifies with a
consumer's binder makes THAT consumer true of nothing: the family reads
VACUOUS (RED) and the row names the covered consumers (`covers`).

**Trivial hypothesis structures.**  A structure bound by a theorem whose
proof fields close when its predicate fields are constantly `True` (or
`False`), its `Option` fields `none` and other data `default`, for every
parameter at once, certifies nothing by itself (`PackedRefinement`, inhabited
for every network through the administrative stutter).  Each such structure
must be listed with a reason in `scripts/trivial-structure-allow.txt`
(`HYP_TRIVIAL_ALLOW`), a ratchet like the TOOTHLESS allowlist.

**The gate is on the instrument.**  The `Plant` namespace below carries five
families whose verdicts are known by construction (VACUOUS, STALE, TOOTHLESS,
GREEN, and the covered Polishchuk--Spielman regression) and two structures
(the `PackedRefinement` regression must read TRIVIAL, a total codec must not); if any comes out otherwise, or fewer than `scanFloor` families with a
consumer were found, the run fails whatever the tree says.  Plants never count
toward the real verdict.  Pinned real-tree rows (`mustBe`) fail the run if the
classification of a known family moves.

Run: `lake env lean scripts/HypothesisLedger.lean`
(or `scripts/check-hypothesis-ledger.sh`, which adds the allowlist.)
-/
import AxiomCensusResearch
import Selvage.PolishchukSpielmanRefutation
import Theory.ObjectiveBendDemandMachine
import Kernel.ObjectiveResumeContract
import Theory.ObjectiveBendLedgerPoles

open Lean Elab Meta

namespace Minidregg.HypothesisLedger

/-! ## The plants: the instrument's teeth -/

namespace Plant
/-- A planted family whose negation is proved: its consumer must read VACUOUS. -/
def Refuted : Prop := False
theorem refuted_false : ¬ Refuted := id
theorem refuted_consumer (h : Refuted) : True := trivial

/-- A planted family proved outright: its consumer must read STALE. -/
def Proved : Prop := True
theorem proved_holds : Proved := trivial
theorem proved_consumer (h : Proved) : True := trivial

/-- A planted assumption with neither instance: must read TOOTHLESS (RED). -/
def Toothless (n : Nat) : Prop := n = n + 1
theorem toothless_consumer (n : Nat) (h : Toothless n) : True := trivial

/-- A planted assumption with both poles named: must read GREEN. -/
def Teeth (n : Nat) : Prop := n = 0
theorem teeth_sat : Teeth 0 := rfl
theorem teeth_ref : ¬ Teeth 1 := by simp [Teeth]
theorem teeth_consumer (n : Nat) (h : Teeth n) : n = 0 := h

/-- REGRESSION (2026-10-03, D-0006): the un-fixed Polishchuk--Spielman floor,
verbatim from the deleted `Minidregg.Selvage.PolishchukSpielman F`, with the
deleted keystone's consumer at `ZMod 5` and the real refutation at that field.
The general-refutation-only rule read it OPEN (TOOTHLESS, allowlisted); a
refutation that covers a consumer must read VACUOUS. -/
def UnfixedPolishchukSpielman (F : Type) [Field F] : Prop :=
  ∀ (A B : Polynomial (Polynomial F)) (SX SZ : Finset F) (aX aZ bX bZ : ℕ),
    A.natDegree ≤ aX → Selvage.ZDegLE A aZ → B.natDegree ≤ bX → Selvage.ZDegLE B bZ →
    (∀ x ∈ SX, A.eval (Polynomial.C x) ∣ B.eval (Polynomial.C x)) →
    (∀ z ∈ SZ, A.map (Polynomial.evalRingHom z) ∣ B.map (Polynomial.evalRingHom z)) →
    aX + bX < SX.card → aZ + bZ < SZ.card →
    bX * SZ.card + bZ * SX.card < SX.card * SZ.card →
    A ∣ B
theorem unfixedPS_refuted_F5 : ¬ UnfixedPolishchukSpielman (ZMod 5) :=
  Selvage.PolishchukSpielmanRefutation.polishchukSpielman_unfixed_false_F5
theorem unfixedPS_keystone (h : UnfixedPolishchukSpielman (ZMod 5)) : True := trivial
theorem unfixedPS_general {F : Type} [Field F] (h : UnfixedPolishchukSpielman F) : True := trivial

/-- REGRESSION (2026-10-04, PACKED-REFINEMENT-AUDIT): `PackedRefinement` over
`stepRaw`'s macrostep, the network abstracted to its evaluation. The
administrative stutter admits `represents := fun _ _ => True` (and the empty
relation): the probe must read it TRIVIAL. -/
inductive Macrostep : Theory.ObjectiveBendDemandMachine.State →
    Theory.ObjectiveBendDemandMachine.State → Prop
  | administrative (state) : Macrostep state state
  | transition (state) : Macrostep state (Theory.ObjectiveBendDemandMachine.stepRaw state)
structure PackedRefinement (evaluate : Array Bool → Option (Array Bool)) where
  represents : Array Bool → Theory.ObjectiveBendDemandMachine.State → Prop
  acceptedStep : ∀ {input output state}, evaluate input = some output →
    output[0]? = some true → represents input state →
    ∃ next, Macrostep state next ∧ represents (output.extract 1 output.size) next
theorem packedRefinement_consumer (evaluate : Array Bool → Option (Array Bool))
    (refinement : PackedRefinement evaluate) : True := trivial

/-- REGRESSION (2026-10-04, D6): a "satisfying instance" quantified over a carrier
nobody has shown inhabited exhibits no point. `unshownSat` proves the floor at an
argument computed FROM such a carrier value (`∀ c : Unshown, Unshowable (c.width - c.width)`);
the old classifier never checked the binders an atom's arguments need, so it counted
that as a satisfying instance and read this family GREEN. It must read TOOTHLESS. -/
structure Unshown where
  width : Nat
  never : width ≠ width
/-- A planted assumption whose only satisfying "instance" ranges over `Unshown`. -/
def Unshowable (n : Nat) : Prop := n = 0
theorem unshownSat (c : Unshown) : Unshowable (c.width - c.width) := Nat.sub_self _
theorem unshowable_ref : ¬ Unshowable 1 := by simp [Unshowable]
theorem unshowable_consumer (n : Nat) (h : Unshowable n) : n = 0 := h

/-- The other side of D6: a carrier of DATA only (no proof field, no instance
declared) is shown inhabited by its constructor, so an instance over it still
counts: `DataProfile` must read GREEN. -/
structure DataCarrier where
  width : Nat
  height : Nat
def DataProfile (n : Nat) : Prop := n = 0
theorem dataProfile_sat (c : DataCarrier) : DataProfile (c.width - c.width) := Nat.sub_self _
theorem dataProfile_ref : ¬ DataProfile 1 := by simp [DataProfile]
theorem dataProfile_consumer (n : Nat) (h : DataProfile n) : n = 0 := h

/-- A codec with a totality obligation: `decode := none` cannot discharge it, so
the probe must NOT read it TRIVIAL. -/
structure TotalCodec where
  decode : Nat → Option Nat
  total : ∀ n, decode n = some n
theorem totalCodec_consumer (codec : TotalCodec) : True := trivial
end Plant

/-! ## Classification -/

def generatedSuffix : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "ibelow", "binductionOn",
   "noConfusion", "noConfusionType", "ndrec", "ndrecOn", "sizeOf_spec",
   "injEq", "inj", "ofNat", "toCtorIdx", "ctorIdx", "eq_def", "congr_simp"]

def isGenerated (name : Name) : Bool :=
  match name with
  | .str _ tail => generatedSuffix.contains tail || tail.startsWith "match_"
      || tail.startsWith "proof_" || tail.startsWith "eq_" || tail.startsWith "_"
      || tail.startsWith "instDecidable" || tail.startsWith "decEq"
  | _ => true

def userName (name : Name) : Name := (privateToUserName? name).getD name

/-- Names we own.  The plant is ours too: it must be found by the same scan. -/
def ours (name : Name) : Bool :=
  (`Minidregg).isPrefixOf (userName name) && !isGenerated name

def isPlant (name : Name) : Bool := (`Minidregg.HypothesisLedger.Plant).isPrefixOf (userName name)

inductive Kind | general | inst | conditional
  deriving BEq, Inhabited

structure Atom where
  positive : Bool
  family : Name
  kind : Kind
  deriving Inhabited

structure Row where
  consumers : Array Name := #[]
  proved : Array Name := #[]
  refuted : Array Name := #[]
  sat : Array Name := #[]
  ref : Array Name := #[]
  condSat : Array Name := #[]
  condRef : Array Name := #[]
  /-- consumers a refutation covers (true of nothing), and the refutations that do -/
  covered : Array Name := #[]
  coveredBy : Array Name := #[]
  deriving Inhabited

structure Ledger where
  families : Std.HashMap Name Nat := {}   -- family -> arity
  closed : NameSet := {}                  -- families whose type is exactly Prop
  assumptionDoc : NameSet := {}           -- families whose docstring names them a hypothesis
  parameterOnly : NameSet := {}           -- families over parameters only (types, instances, functions, scalars)
  rows : Std.HashMap Name Row := {}
  scannedTheorems : Nat := 0
  errors : Array Name := #[]

def Ledger.modify (l : Ledger) (fam : Name) (f : Row → Row) : Ledger :=
  { l with rows := l.rows.insert fam (f (l.rows.getD fam {})) }

def push (xs : Array Name) (n : Name) : Array Name := if xs.contains n then xs else xs.push n

/-- Words by which this tree's doc comments name a statement as assumed rather
than proved. -/
def assumptionWords : List String :=
  ["hypothesis", "assumed", "assumption", "seam", "premise", "obligation",
   "not proved", "unproved", "conjectur", "supplied", "undischarged"]

def docSaysAssumption (doc : String) : Bool :=
  let d := doc.toLower
  assumptionWords.any fun w => (d.splitOn w).length > 1

/-- `(head, args)` of an applied constant, if the head is a family we own and the
application is full. -/
def familyApp (families : Std.HashMap Name Nat) (e : Expr) : Option (Name × Array Expr) :=
  let e := e.consumeMData
  match e.getAppFn with
  | .const c _ =>
    match families[c]? with
    | some arity => if e.getAppNumArgs == arity then some (c, e.getAppArgs) else none
    | none => none
  | _ => none

/-- The binder atoms of a hypothesis type: strip its own `∀`s, split `∧`.  Only
positive atoms count as consumption. -/
partial def binderFamilies (families : Std.HashMap Name Nat) (e : Expr) : List Name :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then
    binderFamilies families e.appFn!.appArg! ++ binderFamilies families e.appArg!
  else if e.isForall then
    binderFamilies families e.getForallBody
  else match familyApp families e with
    | some (c, _) => [c]
    | none => []

/-- Context while walking a conclusion. -/
structure Ctx where
  universals : Array Expr := #[]   -- universally bound variables
  existentials : Array Expr := #[] -- ∃-bound variables
  propHyps : Nat := 0              -- propositional hypotheses in scope

/-- Is this type shown inhabited?  A type former; a type with a `Nonempty`
instance; or an unindexed inductive (a structure, an enumeration) with a
constructor whose fields are all DATA shown inhabited -- a proof field is a claim
nobody discharged, so `Accepted x y` (proof fields) is not shown inhabited while a
`Profile` of naturals is.  `fuel` bounds the descent through nested fields. -/
partial def shownInhabited (ty : Expr) (fuel : Nat := 3) : MetaM Bool := do
  if ← isTypeFormerType ty then return true
  let synthesized ← try
      let goal ← mkAppM ``Nonempty #[ty]
      pure ((← trySynthInstance goal) matches .some _)
    catch _ => pure false
  if synthesized then return true
  if fuel == 0 then return false
  let ty ← whnf ty
  let .const name levels := ty.getAppFn | return false
  let some (.inductInfo info) := (← getEnv).find? name | return false
  if info.numIndices != 0 || info.isRec || ty.getAppNumArgs != info.numParams then return false
  for ctorName in info.ctors do
    let some (.ctorInfo ctor) := (← getEnv).find? ctorName | continue
    let ctorType ← instantiateForall (ctor.type.instantiateLevelParams ctor.levelParams levels)
      ty.getAppArgs
    let ok ← forallTelescopeReducing ctorType fun fields _ => do
      for field in fields do
        let fieldType ← inferType field
        if ← isProp fieldType then return false
        unless ← shownInhabited fieldType (fuel - 1) do return false
      return true
    if ok then return true
  return false

/-- Can a binder of this type be left free without making the statement
conditional?  Instance arguments and types shown inhabited (`shownInhabited`: a
free `n : Nat` is a point of every instance; a free `a : Accepted x y` is a
carrier nobody has shown inhabited). -/
def harmlessBinder (u : Expr) : MetaM Bool := do
  let decl ← u.fvarId!.getDecl
  if decl.binderInfo.isInstImplicit then return true
  shownInhabited decl.type

/-- general / instance / conditional, per the header. -/
def kindOf (ctx : Ctx) (args : Array Expr) : MetaM Kind := do
  if ctx.propHyps > 0 then return .conditional
  -- the binders the atom's arguments mention, directly or through their types
  let mut needed : Array Expr := ctx.universals.filter fun u =>
    args.any (·.containsFVar u.fvarId!)
  let mut changed := true
  while changed do
    changed := false
    for u in ctx.universals do
      if needed.contains u then continue
      let mut use := false
      for n in needed do
        if (← inferType n).containsFVar u.fvarId! then use := true
      if use then
        needed := needed.push u
        changed := true
  for u in ctx.universals do
    if needed.contains u then continue
    unless ← harmlessBinder u do return .conditional
  let mut seen : Array Expr := #[]
  let mut general := true
  for a in args do
    if !(a.isFVar && ctx.universals.contains a) || seen.contains a then general := false
    seen := seen.push a
  if general then return .general
  -- An instance exhibits a point only if every binder its arguments need is shown
  -- inhabited: `∀ a : Accepted, D (f a)` names no point while `Accepted` may be empty.
  -- INHABITED-BEGIN
  for u in needed do
    unless ← harmlessBinder u do return .conditional
  -- INHABITED-END
  return .inst

/-- Walk a conclusion into atoms. -/
partial def conclusionAtoms (families : Std.HashMap Name Nat) (ctx : Ctx) (e : Expr)
    (positive : Bool := true) : MetaM (List Atom) := do
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then
    if !positive then return []   -- ¬(A ∧ B) is not ¬A
    return (← conclusionAtoms families ctx e.appFn!.appArg! positive)
      ++ (← conclusionAtoms families ctx e.appArg! positive)
  if e.isAppOfArity ``Not 1 then
    return ← conclusionAtoms families ctx e.appArg! (!positive)
  if e.isAppOfArity ``Exists 2 then
    if !positive then return []   -- ¬∃ is a ∀¬; leave it
    let p := e.appArg!
    let ty := e.appFn!.appArg!
    return ← withLocalDeclD `w ty fun w => do
      conclusionAtoms families { ctx with existentials := ctx.existentials.push w }
        (mkApp p w).headBeta positive
  if let .forallE _ dom body _ := e then
    if !body.hasLooseBVars && body.consumeMData.isConstOf ``False then
      return ← conclusionAtoms families ctx dom (!positive)
    if !positive then return []
    return ← forallTelescope e fun xs inner => do
      let mut ctx := ctx
      for x in xs do
        if ← isProp (← inferType x) then ctx := { ctx with propHyps := ctx.propHyps + 1 }
        else ctx := { ctx with universals := ctx.universals.push x }
      conclusionAtoms families ctx inner positive
  -- `decide (D …) = true / false`: the computed form of a pole
  if e.isAppOfArity ``Eq 3 then
    let lhs := e.appFn!.appArg!.consumeMData
    let rhs := e.appArg!.consumeMData
    if lhs.isAppOfArity ``Decidable.decide 2 then
      if rhs.isConstOf ``Bool.true then
        return ← conclusionAtoms families ctx lhs.appFn!.appArg! positive
      if rhs.isConstOf ``Bool.false then
        return ← conclusionAtoms families ctx lhs.appFn!.appArg! (!positive)
  match familyApp families e with
  | some (c, args) => return [{ positive, family := c, kind := ← kindOf ctx args }]
  | none => return []

/-- One constant's contribution: its consumption (theorems only) and its atoms. -/
def scanConstant (l : Ledger) (name : Name) (info : ConstantInfo) : MetaM Ledger := do
  let isThm := info matches .thmInfo _
  forallTelescope info.type fun xs body => do
    let mut ctx : Ctx := {}
    let mut propBinders : Array (Expr × Expr) := #[]
    for x in xs do
      let ty ← inferType x
      if ← isProp ty then
        ctx := { ctx with propHyps := ctx.propHyps + 1 }
        propBinders := propBinders.push (x, ty)
      else
        ctx := { ctx with universals := ctx.universals.push x }
    let mut l := l
    let body := body.consumeMData
    if body.isConstOf ``False then
      -- `D … → False` (and every other hypothesis): a refutation of `D` under the rest
      for (_, ty) in propBinders do
        let rest := { ctx with propHyps := ctx.propHyps - 1 }
        match familyApp l.families ty with
        | some (c, args) =>
          let kind ← kindOf rest args
          l := l.modify c fun r => match kind with
            | .general => { r with refuted := push r.refuted name }
            | .inst => { r with ref := push r.ref name }
            | .conditional => { r with condRef := push r.condRef name }
        | none => pure ()
      return l
    if isThm && !(← getEnv).isProjectionFn name then
      for (_, ty) in propBinders do
        for c in binderFamilies l.families ty do
          l := l.modify c fun r => { r with consumers := push r.consumers name }
    for a in ← conclusionAtoms l.families ctx body do
      if a.family == name then continue
      l := l.modify a.family fun r =>
        match a.positive, a.kind with
        | true, .general => { r with proved := push r.proved name }
        | false, .general => { r with refuted := push r.refuted name }
        | true, .inst => { r with sat := push r.sat name }
        | false, .inst => { r with ref := push r.ref name }
        | true, .conditional => { r with condSat := push r.condSat name }
        | false, .conditional => { r with condRef := push r.condRef name }
    return l

/-- A family is *over parameters only* when every explicit argument is a type,
an instance, a function or relation, or a scalar (`ℕ`, `ℤ`, `ℚ`, `ℝ`): a claim
about a choice of system, not a predicate over a state value. -/
def parametersOnly (type : Expr) : MetaM Bool :=
  forallTelescope type fun xs _ => do
    for x in xs do
      let decl ← x.fvarId!.getDecl
      if decl.binderInfo.isInstImplicit || !decl.binderInfo.isExplicit then continue
      if ← isTypeFormerType decl.type then continue
      let ty ← whnfR decl.type
      if ty.isForall then continue
      if ty.isConstOf ``Nat || ty.isConstOf ``Int || ty.isConstOf ``Rat || ty.isConstOf ``Real then continue
      return false
    return true

/-- Is `type` of the shape `A → … → Prop`?  Returns the arity. -/
def propArity (type : Expr) : MetaM (Option Nat) :=
  forallTelescope type fun xs body => do
    if body.consumeMData.isProp then return some xs.size else return none

/-! ## Covered consumers

A refutation `¬ D b⃗` (general or at an instance) COVERS a consumer binding
`D a⃗` when `D b⃗` unifies with `D a⃗`, the refutation's variables as
metavariables and the consumer's as rigid: the consumer is true of nothing at
exactly the point it assumes.  This is the sound form of "refuted at any
instance": a floor refuted at a point it is never assumed at (`Teeth`, refuted
at 1, consumed at a free `n`) keeps its teeth. -/

/-- The atoms `D …` of a hypothesis type (∧-split, not under ∀). -/
partial def binderAtomExprs (families : Std.HashMap Name Nat) (e : Expr) : List (Name × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``And 2 then
    binderAtomExprs families e.appFn!.appArg! ++ binderAtomExprs families e.appArg!
  else match familyApp families e with
    | some (c, _) => [(c, e)]
    | none => []

/-- The atoms of family `fam` a refutation refutes, its variables as metavariables:
`¬ D …`, `D … → False`, or a hypothesis `D …` of a theorem concluding `False`. -/
def refutedAtoms (families : Std.HashMap Name Nat) (fam refutation : Name) : MetaM (List Expr) := do
  let rconst ← mkConstWithFreshMVarLevels refutation
  let (mvars, _, body) ← forallMetaTelescope (← inferType rconst)
  let body := body.consumeMData
  let mut atoms : List Expr := []
  if body.isAppOfArity ``Not 1 then atoms := body.appArg! :: atoms
  if let .forallE _ dom inner _ := body then
    if !inner.hasLooseBVars && inner.consumeMData.isConstOf ``False then atoms := dom :: atoms
  if body.isConstOf ``False then
    for m in mvars do atoms := (← instantiateMVars (← inferType m)) :: atoms
  return atoms.filter fun a => match familyApp families a with
    | some (c, _) => c == fam
    | none => false

def covers (families : Std.HashMap Name Nat) (fam consumer refutation : Name) : MetaM Bool := do
  let cinfo ← getConstInfo consumer
  forallTelescope cinfo.type fun xs _ => do
    for x in xs do
      let ty ← inferType x
      unless ← isProp ty do continue
      for (c, atom) in binderAtomExprs families ty do
        unless c == fam do continue
        let hit ← withNewMCtxDepth <| withTransparency .instances do
          for p in ← refutedAtoms families fam refutation do
            if ← isDefEq p atom then return true
          return false
        if hit then return true
    return false

def scan : MetaM Ledger := do
  let env ← getEnv
  let mut ledger : Ledger := {}
  let consts := env.constants.toList.filter fun (n, _) => ours n
  -- the families
  for (name, info) in consts do
    let candidate := match info with
      | .defnInfo _ | .inductInfo _ | .opaqueInfo _ => true
      | _ => false
    unless candidate do continue
    if (← isInstance name) then continue
    if let some arity ← propArity info.type then
      ledger := { ledger with families := ledger.families.insert name arity }
      if arity == 0 then ledger := { ledger with closed := ledger.closed.insert name }
      else if ← parametersOnly info.type then
        ledger := { ledger with parameterOnly := ledger.parameterOnly.insert name }
      if let some doc ← findDocString? env name then
        if docSaysAssumption doc then
          ledger := { ledger with assumptionDoc := ledger.assumptionDoc.insert name }
  -- SCAN-BEGIN
  for (name, info) in consts do
    match info with
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .ctorInfo _ => pure ()
    | _ => continue
    if ledger.families.contains name then continue
    try
      ledger ← scanConstant ledger name info
      if info matches .thmInfo _ then
        ledger := { ledger with scannedTheorems := ledger.scannedTheorems + 1 }
    catch _ =>
      ledger := { ledger with errors := ledger.errors.push name }
  -- SCAN-END
  -- COVER-BEGIN covered consumers: only families with a refuting instance and a consumer
  for (fam, r) in ledger.rows.toList do
    if r.ref.isEmpty || r.consumers.isEmpty then continue
    for consumer in r.consumers do
      for refutation in r.ref do
        let hit ← try covers ledger.families fam consumer refutation catch _ => pure false
        if hit then
          ledger := ledger.modify fam fun r =>
            { r with covered := push r.covered consumer, coveredBy := push r.coveredBy refutation }
  -- COVER-END
  return ledger

/-! ## Verdicts -/

inductive Verdict | vacuous | inconsistent | stale | green | toothless | unconsumed
  deriving BEq, Inhabited, Repr

def Verdict.label : Verdict → String
  | .vacuous => "VACUOUS" | .inconsistent => "INCONSISTENT" | .stale => "STALE"
  | .green => "GREEN" | .toothless => "TOOTHLESS" | .unconsumed => "unconsumed"

def status (r : Row) : String :=
  if !r.proved.isEmpty && !r.refuted.isEmpty then "INCONSISTENT"
  else if !r.refuted.isEmpty then "REFUTED"
  else if !r.proved.isEmpty then "PROVED"
  else "OPEN"

def verdict (r : Row) : Verdict :=
  if r.consumers.isEmpty then .unconsumed
  else if !r.covered.isEmpty then .vacuous
  else match status r with
    | "INCONSISTENT" => .inconsistent
    | "REFUTED" => .vacuous
    | "PROVED" => .stale
    | _ => if !r.sat.isEmpty && !r.ref.isEmpty then .green else .toothless

/-- Pinned rows of the real tree.  If one of these moves, either the tree
changed (re-pin, in the same commit, with the reason) or the query broke. -/
def mustBe : List (Name × String) :=
  [(`Minidregg.Selvage.GameSlotBound, "PROVED"),
   (`Minidregg.Selvage.PolishchukSpielmanCramer, "PROVED"),
   (`Minidregg.Selvage.HaboeckTheorem2, "OPEN"),
   (`Minidregg.Pred.HashEqHiding, "OPEN")]

def plantMustBe : List (Name × Verdict) :=
  [(`Minidregg.HypothesisLedger.Plant.Refuted, .vacuous),
   (`Minidregg.HypothesisLedger.Plant.Proved, .stale),
   (`Minidregg.HypothesisLedger.Plant.Toothless, .toothless),
   (`Minidregg.HypothesisLedger.Plant.Teeth, .green),
   (`Minidregg.HypothesisLedger.Plant.UnfixedPolishchukSpielman, .vacuous),
   (`Minidregg.HypothesisLedger.Plant.Unshowable, .toothless),
   (`Minidregg.HypothesisLedger.Plant.DataProfile, .green)]

/-- The minimum number of families with a consumer a working scan finds.
Pinned below the 2026-10-01 count; a scan that silently stopped walking
theorems lands far under it. -/
def scanFloor : Nat := 400

def isAssumption (l : Ledger) (fam : Name) : Bool :=
  l.closed.contains fam || l.assumptionDoc.contains fam || l.parameterOnly.contains fam

def names (xs : Array Name) (k : Nat := 6) : String :=
  if xs.isEmpty then "-" else
  let shown := (xs.toList.take k).map toString
  ", ".intercalate shown ++ (if xs.size > k then s!" (+{xs.size - k})" else "")

/-- The allowlist: `family  reason`, one per line, supplied by the gate script
through `HYP_LEDGER_ALLOW` (a path).  An allowlisted TOOTHLESS assumption is
reported and not gated.  It is a ratchet, not a pardon: an entry with no reason,
an entry naming no family, an entry whose family is no longer TOOTHLESS (it
gained its teeth, or was proved -- delete the line), and an entry for a VACUOUS
or INCONSISTENT row all fail the run. -/
def readAllow (envVar : String := "HYP_LEDGER_ALLOW") : IO (List (Name × String)) := do
  let some path ← IO.getEnv envVar | return []
  if path.isEmpty then return []
  let text ← IO.FS.readFile path
  return text.splitOn "\n" |>.filterMap fun line =>
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then none
    else match line.splitOn " " with
      | name :: rest => some (name.toName, (" ".intercalate rest).trimAscii.toString)
      | [] => none

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]?.map toString).getD "?"
  | none => "(this file)"

/-! ## Trivial inhabitants

A hypothesis STRUCTURE (`PackedRefinement N`) is a premise whose content is its
proof fields.  If the structure is inhabited, for every parameter at once, with
its predicate fields constantly `True` (or constantly `False`), its
`Option`-valued fields `none` and other data `default`, then by itself it
certifies nothing: TRIVIAL.  The population is every structure we own that a
theorem we own binds and that has a proof field. -/

open Elab Tactic in
/-- Close `goal` with a fixed, cheap battery (no search). -/
def closeByBattery (goal : MVarId) : MetaM Bool := do
  let attempt : TermElabM Bool := do
    let tac ← `(tactic| (intros; first
      | contradiction | trivial | rfl
      | exact ⟨_, trivial⟩
      | exact ⟨_, by constructor, trivial⟩
      | (constructor <;> first | trivial | rfl | constructor)
      | (simp_all; done)))
    try
      let rest ← Lean.Elab.Tactic.run goal (Tactic.withoutRecover (evalTactic tac))
      -- error recovery may have closed a goal with `sorry`: that is a failure
      return rest.isEmpty && !(← instantiateMVars (mkMVar goal)).hasSorry
    catch _ => return false
  -- a failed attempt must leave no message behind (tactic errors are logged, not thrown)
  let saved := (← getThe Core.State).messages
  let ok ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 20000 * 1000 }) do
      Core.withCurrHeartbeats (Term.withoutErrToSorry attempt).run')
    (fun _ => pure false)
  modifyThe Core.State fun st => { st with messages := saved }
  return ok

/-- The degenerate value of a data field, or `none` when there is none to try. -/
def degenerate (type : Expr) (useTrue : Bool) : MetaM (Option Expr) :=
  forallTelescopeReducing type fun xs target => do
    let target ← whnfR target
    if target.isProp then
      return some (← mkLambdaFVars xs (mkConst (if useTrue then ``True else ``False)))
    if target.isAppOfArity ``Option 1 then
      return some (← mkLambdaFVars xs (← mkAppOptM ``Option.none #[target.appArg!]))
    try return some (← mkLambdaFVars xs (← mkAppOptM ``Inhabited.default #[target, none]))
    catch _ => return none

/-- `some strategy` when the structure is TRIVIAL (see above). -/
def probeTrivial (s : Name) : MetaM (Option String) := do
  let some (.inductInfo ind) := (← getEnv).find? s | return none
  let some ctorName := ind.ctors.head? | return none
  let ctor ← getConstInfoCtor ctorName
  for useTrue in [true, false] do
    let ok ← forallBoundedTelescope ctor.type ind.numParams fun _ fields => do
      let mut rest := fields
      let mut proofs := 0
      repeat
        match rest.consumeMData with
        | .forallE _ ty body _ =>
          let value? ← if ← isProp ty then do
              proofs := proofs + 1
              let goal ← mkFreshExprMVar (← Core.betaReduce (← instantiateMVars ty))
              if ← closeByBattery goal.mvarId! then pure (some goal) else pure none
            else degenerate ty useTrue
          match value? with
          | some v => rest := body.instantiate1 v
          | none => return false
        | _ => break
      return proofs > 0
    if ok then return some (if useTrue then "predicates := True" else "predicates := False")
  return none

/-- Structures we own bound by a theorem we own, with their consumers. -/
def boundStructures : MetaM (Std.HashMap Name (Array Name)) := do
  let env ← getEnv
  let mut bound : Std.HashMap Name (Array Name) := {}
  for (name, info) in env.constants.toList do
    unless ours name && info matches .thmInfo _ do continue
    -- a structure's own projections are its fields, not consumers
    if env.isProjectionFn name then continue
    let heads ← try forallTelescope info.type fun xs _ => do
        let mut hs : Array Name := #[]
        for x in xs do
          if let .const c _ := (← inferType x).getAppFn then
            if ours c && isStructure env c && !isClass env c && !hs.contains c then hs := hs.push c
        return hs
      catch _ => pure #[]
    for h in heads do bound := bound.insert h ((bound.getD h #[]).push name)
  return bound

def plantTrivialMustBe : List (Name × Bool) :=
  [(`Minidregg.HypothesisLedger.Plant.PackedRefinement, true),
   (`Minidregg.HypothesisLedger.Plant.TotalCodec, false)]

def run : MetaM Unit := do
  let env ← getEnv
  let l ← scan
  let allow ← readAllow
  let mut failures : Array String := #[]
  -- teeth on the instrument
  for (fam, want) in plantMustBe do
    let got := verdict (l.rows.getD fam {})
    unless got == want do
      failures := failures.push s!"instrument: plant {fam} expected {want.label}, got {got.label}"
  let consumed := l.families.toList.filter fun (f, _) =>
    !(l.rows.getD f {}).consumers.isEmpty
  if consumed.length < scanFloor then
    failures := failures.push s!"instrument: only {consumed.length} consumed families scanned (floor {scanFloor})"
  for (fam, want) in mustBe do
    unless l.families.contains fam do
      failures := failures.push s!"pin: {fam} is not a family (renamed?)"
    let got := status (l.rows.getD fam {})
    unless got == want do
      failures := failures.push s!"pin: {fam} expected {want}, got {got}"
  -- rows
  let real := consumed.filter fun (f, _) => !isPlant f
  let byVerdict (v : Verdict) := real.filter fun (f, _) => verdict (l.rows.getD f {}) == v
  let assumptions := real.filter fun (f, _) => isAssumption l f
  IO.println s!"theorems scanned              : {l.scannedTheorems}"
  IO.println s!"Prop-valued families          : {l.families.size}"
  IO.println s!"  with >= 1 consumer          : {consumed.length} (floor {scanFloor}; {consumed.length - real.length} plants)"
  IO.println s!"  of which assumption tier    : {assumptions.length}"
  let tierOf (p : Name → Bool) := (real.filter fun (f, _) => p f).length
  IO.println s!"    closed (type Prop)          : {tierOf l.closed.contains}"
  IO.println s!"    over parameters only        : {tierOf l.parameterOnly.contains}"
  IO.println s!"    doc names it an assumption  : {tierOf l.assumptionDoc.contains}"
  IO.println s!"scan errors                   : {l.errors.size}{if l.errors.isEmpty then "" else " " ++ names l.errors}"
  for v in [Verdict.vacuous, .inconsistent, .stale, .green, .toothless] do
    let all := byVerdict v
    let tier := all.filter fun (f, _) => isAssumption l f
    IO.println s!"  {v.label}\t: {all.length} ({tier.length} assumption tier)"
  IO.println ""
  IO.println "THE LEDGER (assumption tier, and every VACUOUS/INCONSISTENT/STALE row):"
  IO.println "family | status | verdict | #consumers | proved-by / refuted-by | sat | ref | conditional | consumers (RED/STALE)"
  let shown := real.filter fun (f, _) =>
    let v := verdict (l.rows.getD f {})
    isAssumption l f || v == .vacuous || v == .inconsistent || v == .stale
  let sorted := shown.toArray.qsort fun a b =>
    (l.rows.getD a.1 {}).consumers.size > (l.rows.getD b.1 {}).consumers.size
  for (fam, _) in sorted do
    let r := l.rows.getD fam {}
    let v := verdict r
    let tierRed := v == .vacuous || v == .inconsistent
      || (v == .toothless && isAssumption l fam)
    let allowed := allow.any (·.1 == fam)
    let mark := if tierRed then (if allowed && v == .toothless then "ALLOWED" else "RED") else
      if v == .stale then "yellow" else "ok"
    let showConsumers := tierRed || v == .stale
    IO.println s!"{fam} | {status r} | {v.label} [{mark}] | {r.consumers.size} | {names (r.proved ++ r.refuted)} | {names r.sat} | {names r.ref} | {names (r.condSat ++ r.condRef) 3} | {if !r.covered.isEmpty then s!"covered: {names r.covered 8} by {names r.coveredBy 3}" else if showConsumers then names r.consumers 8 else ""}  [{moduleOf env fam}]"
    if tierRed then
      if allowed && v == .toothless then pure ()
      else failures := failures.push s!"RED: {fam} is {v.label} with {r.consumers.size} consumer(s): {names r.consumers 4}"
  -- trivial inhabitants
  let bound ← boundStructures
  let trivialAllow ← readAllow "HYP_TRIVIAL_ALLOW"
  for (st, want) in plantTrivialMustBe do
    unless bound.contains st do
      failures := failures.push s!"instrument: plant {st} has no consumer"
    let got := (← tryCatchRuntimeEx (probeTrivial st) (fun _ => pure none)).isSome
    unless got == want do
      failures := failures.push s!"instrument: plant {st} expected TRIVIAL={want}, got {got}"
  let mut trivials : Array (Name × String) := #[]
  let mut probed := 0
  for (st, _) in bound.toList do
    if isPlant st then continue
    probed := probed + 1
    if let some how ← tryCatchRuntimeEx (probeTrivial st) (fun _ => pure none) then
      trivials := trivials.push (st, how)
  IO.println ""
  IO.println s!"TRIVIAL STRUCTURES (bound by a theorem; inhabited with degenerate fields for every parameter): {trivials.size} of {probed} probed"
  for (st, how) in trivials.qsort (fun a b => a.1.toString < b.1.toString) do
    let allowed := trivialAllow.any (·.1 == st)
    let consumers := bound.getD st #[]
    IO.println s!"  {st} [{if allowed then "ALLOWED" else "RED"}] {how}; {consumers.size} consumer(s): {names consumers 3}  [{moduleOf env st}]"
    unless allowed do
      failures := failures.push s!"RED: structure {st} is TRIVIAL ({how}); bound by {names consumers 3}"
  for (a, reason) in trivialAllow do
    if reason.isEmpty then
      failures := failures.push s!"trivial-allowlist: {a} carries no reason"
    -- Polarity (REVIEW-SCHOLAR-BREAD-META §2): DATA (the trivial inhabitant is a real value),
    -- PARAMETER (consumers quantify over it; `instance=` names an instance they are used at),
    -- PREMISE (the trivial inhabitant makes consumers vacuous: `field=` names a non-triviality
    -- field, or `instance=` and `theorem=` name an instance and a consumer instantiated at it).
    let words := (reason.splitOn " ").filter (· ≠ "")
    let named (key : String) : Option Name := words.findSome? fun word =>
      match word.splitOn "=" with
      | [k, v] => if k == key && v != "" then some v.toName else none
      | _ => none
    let present (key : String) : Bool := match named key with
      | some n => env.contains n
      | none => false
    for key in ["instance", "theorem", "field"] do
      if let some n := named key then
        unless env.contains n do
          failures := failures.push s!"trivial-allowlist: {a} names {key}={n}, which is not a declaration"
    match words.head? with
    | some "DATA" => pure ()
    | some "PARAMETER" =>
      unless present "instance" do
        failures := failures.push s!"trivial-allowlist: {a} PARAMETER names no instance (instance=<declaration>)"
    | some "PREMISE" =>
      unless present "field" || (present "instance" && present "theorem") do
        failures := failures.push s!"trivial-allowlist: {a} PREMISE has no non-triviality field and no instance with a theorem (field=<declaration> | instance=<declaration> theorem=<declaration>)"
    | _ =>
      failures := failures.push s!"trivial-allowlist: {a} names no polarity (DATA | PARAMETER | PREMISE)"
    unless trivials.any (·.1 == a) do
      failures := failures.push s!"trivial-allowlist: {a} is not a TRIVIAL bound structure -- delete the entry"
  for (a, reason) in allow do
    if reason.isEmpty then
      failures := failures.push s!"allowlist: {a} carries no reason"
    unless l.families.contains a do
      failures := failures.push s!"allowlist: {a} is not a family (stale entry)"
    let v := verdict (l.rows.getD a {})
    unless v == .toothless && isAssumption l a do
      failures := failures.push s!"allowlist: {a} is {v.label}, not a TOOTHLESS assumption -- delete the entry"
  IO.println ""
  let toothlessData := (byVerdict .toothless).filter fun (f, _) => !isAssumption l f
  IO.println s!"predicates over data with no named sat+ref pair (reported, not gated): {toothlessData.length}; top 25 by consumers:"
  let ranked := toothlessData.toArray.qsort fun a b =>
    (l.rows.getD a.1 {}).consumers.size > (l.rows.getD b.1 {}).consumers.size
  for (fam, _) in ranked.toList.take 25 do
    let r := l.rows.getD fam {}
    IO.println s!"  {r.consumers.size}\t{fam}  sat {r.sat.size} ref {r.ref.size} cond {r.condSat.size + r.condRef.size}"
  IO.println ""
  if failures.isEmpty then
    IO.println "hypothesis-ledger: PASS"
  else
    for f in failures do IO.eprintln s!"hypothesis-ledger: {f}"
    throwError s!"hypothesis-ledger: {failures.size} failure(s)"

end Minidregg.HypothesisLedger

set_option maxHeartbeats 0 in
run_meta Minidregg.HypothesisLedger.run
