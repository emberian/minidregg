/-
# Kernel.ReceivingLaw -- the Receiver judges every written cell's law

A receiving family proposes a patch: one canonical post image per written cell.
This module decides, once for every family, whether the laws of the written
cells admit it.  The family only PROJECTS: for each write it may supply the
policy step (`PolicyStepContext`, the old and new predicate states of the real
pre and post stores).  The Receiver JUDGES:

* the kind of the written cell comes from the write's own post bytes (or, for a
  retirement, the loaded pre cell), never from the family;
* the registry (`CanonicalCellRegistry.Kind.lawClass`, total, no default arm)
  says whether that kind is `lawBearing` or `kernelOnly writers`;
* a `kernelOnly` cell may be written only by a family its row names, and only
  without a step (a step offered for a kernel-only cell is a registry mismatch);
* a `lawBearing` cell is judged by ITS OWN committed law, resolved at the cell's
  id on the loaded state the family prepared against: the resolution must
  succeed, the compiler must be able to lower the law, every input the law
  reads must be in range, the field cast of those
  inputs must be injective, and `Pred.eval` must accept the step.  A refusal
  names the failing clause with `LawLeaf.of` on the same step;
* a `lawBearing` BIRTH (no live cell at the write's id in the loaded state) is
  judged by its EXPORT law instead (`resolveBirth`): the descendants law of the
  room the patch places it in (the authority cell's parent plane, written by the
  same patch, `birthRoom`) and its kind's structural restrictions (`exportRoots`),
  on the family's view of the birth, with the same verdicts.  A `kernelOnlyOrBorn`
  cell (a law source) is written in place only by its named writers and is
  otherwise born under that same export law;
* a write of an unclassifiable cell is refused.

Authorization (request binding, capability evidence: `ComposedPolicyAdmission.
admit`) stays in the family.  This is the other half: the law judges the step.

The law lookup is a `Laws` value over the loaded state.  The deployed one,
`Laws.physical`, resolves through `PhysicalLawResolution.judge` on
`PhysicalLawResolution.targetConfig` (`physical_resolve_some_iff`) -- the one
judgement the DRC's `authorizeLeg` calls too, on the same target configuration
(`policyConfigFromStep` is `targetConfig`); the capability portal the two carry
differs and the judgement does not read it
(`PhysicalLawResolution.judge_portal_irrelevant`).  `Kernel.Receiving` installs
it, so every family on `Receiving.Family` is judged by it
(`Receiving.Family.receiveLoaded_laws`).  The theorems here hold for every
`Laws`; the fixture at the end runs a fixture `Laws` at `Id` (the deployed
durable layer cannot be built in a closed term), and the physical side is
covered by the shared-resolver equation.
-/
import Compiler.PhysicalLawResolution
import Compiler.RefusalReason
import Compiler.CredentialAuthorityDomainReceiver

namespace Minidregg.Kernel.ReceivingLaw

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalCellRegistry (Kind FamilyId LawClass registry Deployment)
open Minidregg.Theory.LawComposition (PolicyRef)
open Minidregg.Compiler.CanonicalPolicyAdmission (PolicyStepContext PolicyCompilerProfile)
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

abbrev Durable := DurableReceiverIO.Loaded rootBytes

/-! ## What the Receiver judges with -/

/-- One written cell's committed law, resolved on its step: the predicate, the
compiler's verdicts on the step, and the cells the resolution read (they join
the record's read guards, so a concurrent law change conflicts). -/
structure ResolvedLaw where
  predicate : Minidregg.Pred.Pred
  inRange : Bool
  castsInjective : Bool
  /-- The compiler can lower the law: with the two verdicts above, `Pred.eval` is
  the compiled verdict (`PreparedLaw.verifies_iff_eval`). -/
  supported : Bool
  /-- The law has a root: a committed law, or an export law with at least one
  parent.  An unrooted (neutral) birth law admits a newborn only when a judged
  authorizer of the same patch names it (`judgeBearing`). -/
  rooted : Bool
  guards : List ReadGuard

/-- How the Receiver reads laws on a loaded state `S`.  Built by the host from
its deployment (`Laws.physical`); never supplied by a family or an ingress. -/
structure Laws (S : Type) where
  /-- The kind of the cell a write writes: its live post cell's, else its loaded pre cell's. -/
  kindOf : S → DataWrite → Option Kind
  /-- The write creates its cell: the loaded state holds no live cell at its id. -/
  birth : S → DataWrite → Bool
  /-- The committed law of `target` on `step`, at the loaded state. -/
  resolve : S → (target : Nat) → PolicyStepContext → Option ResolvedLaw
  /-- The EXPORT law of a birth in `patch`, on `step`: its birth room's descendants
  law and its kind's structural restrictions (`exportRoots`), read from the
  newborn's post and the patch, never from the family. -/
  resolveBirth : S → (patch : List DataWrite) → DataWrite → PolicyStepContext → Option ResolvedLaw

/-- Why a law-bearing write has no law to judge it. -/
inductive Unavailable where
  /-- The family supplied no step for a law-bearing cell. -/
  | noStep
  /-- The committed law (or, for a birth, the export law) did not resolve at the loaded state. -/
  | unresolved
  deriving DecidableEq, Repr

/-- Why the laws of the written cells refuse a patch. -/
inductive LawFault where
  | unclassified (cell : Nat)
  | lawUnavailable (cell : Nat) (why : Unavailable)
  | lawInputRange (cell : Nat)
  | lawCastAlias (cell : Nat)
  /-- The committed law uses a form the deployment's compiler cannot lower. -/
  | lawUnsupported (cell : Nat)
  /-- A neutral birth (no export root) that no judged authorizer of the patch names. -/
  | neutralBirthUnjudged (cell : Nat)
  /-- The committed law refused the step at this clause (`LawLeaf.of`). -/
  | lawDenied (cell : Nat) (leaf : LawLeaf)
  | kernelOnlyForeignWriter (cell : Nat) (kind : Kind) (family : FamilyId)
  /-- A family offered a law step for a kernel-only cell. -/
  | registryMismatch (cell : Nat) (kind : Kind)
  deriving DecidableEq, Repr

/-! ## The judgement -/

section Judge

variable {S : Type} (laws : Laws S) (family : FamilyId) (state : S)

/-- The law a law-bearing write is judged by: a birth's export law, else the
committed law at its id. -/
def lawOf (patch : List DataWrite) (write : DataWrite) (step : PolicyStepContext) :
    Option ResolvedLaw :=
  if laws.birth state write then laws.resolveBirth state patch write step
  else laws.resolve state write.cellId.value step

/-- The slot a step names a newborn by: `birth/<id>`. -/
def birthSlot (cell : Nat) : Minidregg.Pred.Slot := "birth/" ++ toString cell

/-- **A step names a newborn**: its new state holds `birth/<id>` = the newborn's
exact post root.  The root is the root of the newborn's whole post image, so a
step that names it names the cell, its kind and its content (a law source's law). -/
def namesBirth (step : PolicyStepContext) (write : DataWrite) : Bool :=
  step.newState.get (birthSlot write.cellId.value) == some (Int.ofNat write.exactPost.value)

/-- The verdicts of one resolved law on one step. -/
def judgeLaw (cell : Nat) (law? : Option ResolvedLaw) (step : PolicyStepContext) : Option LawFault :=
  match law? with
  | none => some (.lawUnavailable cell .unresolved)
  | some law =>
    if !law.supported then some (.lawUnsupported cell)
    else if !law.inRange then some (.lawInputRange cell)
    else if !law.castsInjective then some (.lawCastAlias cell)
    else (LawLeaf.of law.predicate step.oldState step.newState).map (.lawDenied cell)

/-- A law-bearing write's judgement: a step is required, and its law decides.  A
NEUTRAL law (a birth with no export root) admits nothing by itself: the newborn
must be named by the step of an authorizer the same patch writes (`authorizers`,
the steps of its non-birth, law-bearing writes, each judged by its own law in the
same pass), else it is refused `neutralBirthUnjudged`. -/
def judgeBearing (authorizers : List PolicyStepContext) (patch : List DataWrite) (write : DataWrite)
    (step : Option PolicyStepContext) : Option LawFault :=
  match step with
  | none => some (.lawUnavailable write.cellId.value .noStep)
  | some step =>
      if (lawOf laws state patch write step).any (fun law => !law.rooted) &&
          !(authorizers.any fun authorizer => namesBirth authorizer write) then
        some (.neutralBirthUnjudged write.cellId.value)
      else judgeLaw write.cellId.value (lawOf laws state patch write step) step

/-- A kernel-only write's judgement: no step, and a named writer. -/
def judgeKernel (write : DataWrite) (kind : Kind) (writers : List FamilyId)
    (step : Option PolicyStepContext) : Option LawFault :=
  match step with
  | some _ => some (.registryMismatch write.cellId.value kind)
  | none => if family ∈ writers then none else some (.kernelOnlyForeignWriter write.cellId.value kind family)

/-- The judgement of one write of `patch`, with the patch's authorizer steps. -/
def judgeWrite (authorizers : List PolicyStepContext) (patch : List DataWrite) (write : DataWrite)
    (step : Option PolicyStepContext) : Option LawFault :=
  match laws.kindOf state write with
  | none => some (.unclassified write.cellId.value)
  | some kind =>
    match kind.lawClass with
    | .kernelOnly writers => judgeKernel family write kind writers step
    | .lawBearing => judgeBearing laws state authorizers patch write step
    | .kernelOnlyOrBorn writers =>
        if laws.birth state write then judgeBearing laws state authorizers patch write step
        else judgeKernel family write kind writers step

/-- A write that can authorize a neutral birth: a non-birth write of a
law-bearing cell (judged by its own committed law). -/
def authorizes (write : DataWrite) : Bool :=
  (laws.kindOf state write).any (fun kind => kind.lawClass == LawClass.lawBearing) &&
    !laws.birth state write

/-- **The authorizers of a patch**: the steps of its non-birth, law-bearing
writes.  Each is judged by its own committed law in the same pass, so a newborn
one of them names was named by a step that law admitted. -/
def authorizerSteps (writes : List DataWrite)
    (step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext) :
    List PolicyStepContext :=
  writes.attach.filterMap fun ⟨write, member⟩ =>
    if authorizes laws state write then step write member
    else none

/-- The first fault among a patch's writes, in write order. -/
def lawFault (writes : List DataWrite)
    (step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext) : Option LawFault :=
  writes.attach.findSome? fun ⟨write, member⟩ =>
    judgeWrite laws family state (authorizerSteps laws state writes step) writes write (step write member)

/-- The read guards the judgement adds: the cells each law-bearing write's
resolution read (T5: the law is the one at the snapshot the family prepared
against, and a concurrent change to it conflicts). Kernel-only writes add none. -/
def writeGuards (patch : List DataWrite) (write : DataWrite) (step : Option PolicyStepContext) :
    List ReadGuard :=
  match laws.kindOf state write, step with
  | some kind, some step =>
      match kind.lawClass with
      | .lawBearing | .kernelOnlyOrBorn _ =>
          ((lawOf laws state patch write step).map ResolvedLaw.guards).getD []
      | .kernelOnly _ => []
  | _, _ => []

def lawGuards (writes : List DataWrite)
    (step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext) : List ReadGuard :=
  writes.attach.flatMap fun ⟨write, member⟩ => writeGuards laws state writes write (step write member)

private theorem findSome?_attach {α β : Type} (l : List α) (f : α → Option β) :
    l.attach.findSome? (fun x => f x.1) = l.findSome? f := by
  have h := List.findSome?_map (f := Subtype.val) (p := f) (l := l.attach)
  rw [List.attach_map_subtype_val] at h
  exact h.symm

private theorem flatMap_attach {α β : Type} (l : List α) (f : α → List β) :
    l.attach.flatMap (fun x => f x.1) = l.flatMap f := by
  have h := List.flatMap_map (f := Subtype.val) (g := f) (l := l.attach)
  rw [List.attach_map_subtype_val] at h
  exact h.symm

private theorem filterMap_attach {α β : Type} (l : List α) (f : α → Option β) :
    l.attach.filterMap (fun x => f x.1) = l.filterMap f := by
  have h := List.filterMap_map (f := Subtype.val) (g := f) (l := l.attach)
  rw [List.attach_map_subtype_val] at h
  exact h.symm

/-- The authorizers of a family whose step does not depend on the membership proof. -/
def authorizerStepsOf (writes : List DataWrite) (step : DataWrite → Option PolicyStepContext) :
    List PolicyStepContext :=
  writes.filterMap fun write =>
    if authorizes laws state write then step write
    else none

theorem authorizerSteps_uniform (writes : List DataWrite) (step : DataWrite → Option PolicyStepContext) :
    authorizerSteps laws state writes (fun write _ => step write) =
      authorizerStepsOf laws state writes step :=
  filterMap_attach writes fun write => if authorizes laws state write then step write else none

/-- A family whose step does not depend on the membership proof is judged write by write. -/
theorem lawFault_uniform (writes : List DataWrite) (step : DataWrite → Option PolicyStepContext) :
    lawFault laws family state writes (fun write _ => step write) =
      writes.findSome? fun write =>
        judgeWrite laws family state (authorizerStepsOf laws state writes step) writes write (step write) := by
  unfold lawFault
  rw [authorizerSteps_uniform]
  exact findSome?_attach writes fun write =>
    judgeWrite laws family state (authorizerStepsOf laws state writes step) writes write (step write)

theorem lawGuards_uniform (writes : List DataWrite) (step : DataWrite → Option PolicyStepContext) :
    lawGuards laws state writes (fun write _ => step write) =
      writes.flatMap fun write => writeGuards laws state writes write (step write) :=
  flatMap_attach writes fun write => writeGuards laws state writes write (step write)

/-- The three compiler verdicts true and `Pred.eval` accepting `step`. -/
def Admits (law : ResolvedLaw) (step : PolicyStepContext) : Prop :=
  law.supported = true ∧ law.inRange = true ∧ law.castsInjective = true ∧
    Minidregg.Pred.eval law.predicate step.oldState step.newState = true

/-- **A newborn named by a judged authorizer**: some non-birth, law-bearing write
of the same patch resolved its committed law on a step that admits it and that
names the newborn (`namesBirth`). -/
def Named (patch : List DataWrite) (write : DataWrite) : Prop :=
  ∃ authorizer ∈ patch, laws.birth state authorizer = false ∧
    (∃ kind, laws.kindOf state authorizer = some kind ∧ kind.lawClass = .lawBearing) ∧
    ∃ step law, laws.resolve state authorizer.cellId.value step = some law ∧ Admits law step ∧
      namesBirth step write = true

/-- A law-bearing write was judged and admitted under `named`: it carried a step,
its law (`lawOf`) resolved, the law is rooted (a committed law or a non-empty
export law) or the newborn is `named`, and the law admits the step. -/
def JudgedBy (named : DataWrite → Prop) (patch : List DataWrite) (write : DataWrite)
    (step : Option PolicyStepContext) : Prop :=
  ∃ s law, step = some s ∧ lawOf laws state patch write s = some law ∧
    (law.rooted = true ∨ named write) ∧ Admits law s

/-- What it means for one write of `patch` to be lawful under `named`. -/
def LawfulBy (named : DataWrite → Prop) (patch : List DataWrite) (write : DataWrite)
    (step : Option PolicyStepContext) : Prop :=
  ∃ kind, laws.kindOf state write = some kind ∧
    ((kind.lawClass = .lawBearing ∧ JudgedBy laws state named patch write step) ∨
      (∃ writers, kind.lawClass = .kernelOnly writers ∧ family ∈ writers ∧ step = none) ∨
      (∃ writers, kind.lawClass = .kernelOnlyOrBorn writers ∧
        ((laws.birth state write = true ∧ JudgedBy laws state named patch write step) ∨
          (laws.birth state write = false ∧ family ∈ writers ∧ step = none))))

/-- **Judged**: by a rooted law, or, for a neutral birth, `Named` by a judged authorizer. -/
abbrev Judged (patch : List DataWrite) (write : DataWrite) (step : Option PolicyStepContext) : Prop :=
  JudgedBy laws state (Named laws state patch) patch write step

/-- **What it means for one write of `patch` to be lawful.** -/
abbrev Lawful (patch : List DataWrite) (write : DataWrite) (step : Option PolicyStepContext) : Prop :=
  LawfulBy laws family state (Named laws state patch) patch write step

theorem LawfulBy.mono {named named' : DataWrite → Prop} (weaker : ∀ write, named write → named' write)
    {patch : List DataWrite} {write : DataWrite} {step : Option PolicyStepContext}
    (lawful : LawfulBy laws family state named patch write step) :
    LawfulBy laws family state named' patch write step := by
  have judged : JudgedBy laws state named patch write step → JudgedBy laws state named' patch write step := by
    rintro ⟨s, law, stepEq, resolved, rooted, admits⟩
    exact ⟨s, law, stepEq, resolved, rooted.imp_right (weaker write), admits⟩
  obtain ⟨kind, kindEq, rest⟩ := lawful
  refine ⟨kind, kindEq, ?_⟩
  rcases rest with ⟨bearing, j⟩ | kernel | ⟨writers, row, (⟨birth, j⟩ | other)⟩
  · exact Or.inl ⟨bearing, judged j⟩
  · exact Or.inr (Or.inl kernel)
  · exact Or.inr (Or.inr ⟨writers, row, Or.inl ⟨birth, judged j⟩⟩)
  · exact Or.inr (Or.inr ⟨writers, row, Or.inr other⟩)

theorem judgeLaw_none_iff (cell : Nat) (law? : Option ResolvedLaw) (step : PolicyStepContext) :
    judgeLaw cell law? step = none ↔ ∃ law, law? = some law ∧ Admits law step := by
  unfold judgeLaw Admits
  cases law? with
  | none => simp
  | some law =>
    cases lowerable : law.supported <;> cases inRange : law.inRange <;>
      cases casts : law.castsInjective <;>
      simp [lowerable, inRange, casts, Option.map_eq_none_iff, LawLeaf.of_none_iff]

theorem judgeBearing_none_iff (authorizers : List PolicyStepContext) (patch : List DataWrite)
    (write : DataWrite) (step : Option PolicyStepContext) :
    judgeBearing laws state authorizers patch write step = none ↔
      JudgedBy laws state (fun write => authorizers.any (fun a => namesBirth a write) = true)
        patch write step := by
  unfold judgeBearing JudgedBy
  cases step with
  | none => simp
  | some s =>
    cases resolved : lawOf laws state patch write s with
    | none => simp [resolved, judgeLaw]
    | some law =>
      cases rooted : law.rooted <;>
        cases named : authorizers.any (fun a => namesBirth a write) <;>
        simp [resolved, rooted, named, judgeLaw_none_iff]

theorem judgeKernel_none_iff (write : DataWrite) (kind : Kind) (writers : List FamilyId)
    (step : Option PolicyStepContext) :
    judgeKernel family write kind writers step = none ↔ family ∈ writers ∧ step = none := by
  unfold judgeKernel
  cases step with
  | some s => simp
  | none => by_cases named : family ∈ writers <;> simp [named]

/-- **One write is judged exactly**, with the patch's authorizer steps. -/
theorem judgeWrite_none_iff (authorizers : List PolicyStepContext) (patch : List DataWrite)
    (write : DataWrite) (step : Option PolicyStepContext) :
    judgeWrite laws family state authorizers patch write step = none ↔
      LawfulBy laws family state (fun write => authorizers.any (fun a => namesBirth a write) = true)
        patch write step := by
  unfold judgeWrite LawfulBy
  cases kindEq : laws.kindOf state write with
  | none => simp
  | some kind =>
    simp only [Option.some.injEq, exists_eq_left']
    cases classEq : kind.lawClass with
    | kernelOnly writers =>
        rw [judgeKernel_none_iff]
        simp
    | lawBearing =>
        rw [judgeBearing_none_iff]
        simp
    | kernelOnlyOrBorn writers =>
        cases birthEq : laws.birth state write with
        | true =>
            simp only [if_true]
            rw [judgeBearing_none_iff]
            simp
        | false =>
            simp only [Bool.false_eq_true, if_false]
            rw [judgeKernel_none_iff]
            simp

/-- **The patch is judged exactly**: no fault iff every write is lawful under the
patch's own authorizer steps. -/
theorem lawFault_none_iff (writes : List DataWrite)
    (step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext) :
    lawFault laws family state writes step = none ↔
      ∀ write (member : write ∈ writes),
        LawfulBy laws family state
          (fun write => (authorizerSteps laws state writes step).any (fun a => namesBirth a write) = true)
          writes write (step write member) := by
  unfold lawFault
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro none_ write member
    exact (judgeWrite_none_iff laws family state _ writes write (step write member)).1
      (none_ ⟨write, member⟩ (List.mem_attach _ _))
  · rintro all ⟨write, member⟩ -
    exact (judgeWrite_none_iff laws family state _ writes write (step write member)).2 (all write member)

/-- **An authorizer's naming is a judged naming**: in a patch with no fault, a
newborn named by one of the patch's authorizer steps is `Named` -- by a
non-birth, law-bearing write of the patch whose committed law admitted that
very step. -/
theorem named_of_authorizer {writes : List DataWrite}
    {step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext}
    (lawful : lawFault laws family state writes step = none) {write : DataWrite}
    (named : (authorizerSteps laws state writes step).any (fun a => namesBirth a write) = true) :
    Named laws state writes write := by
  obtain ⟨s, member, names⟩ := List.any_eq_true.1 named
  unfold authorizerSteps at member
  obtain ⟨⟨authorizer, inPatch⟩, -, produced⟩ := List.mem_filterMap.1 member
  dsimp only at produced
  split at produced
  · rename_i gate
    simp only [authorizes, Bool.and_eq_true, Option.any_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at gate
    obtain ⟨⟨kind, kindEq, bearing⟩, notBirth⟩ := gate
    have judged := (lawFault_none_iff laws family state writes step).1 lawful authorizer inPatch
    obtain ⟨kind', kindEq', rest⟩ := judged
    rw [kindEq] at kindEq'
    cases kindEq'
    rcases rest with ⟨-, ⟨s', law, stepEq, resolvedOf, -, admits⟩⟩ | ⟨writers, row, -⟩ |
        ⟨writers, row, -⟩
    · rw [produced] at stepEq
      cases stepEq
      have resolved : laws.resolve state authorizer.cellId.value s = some law := by
        unfold lawOf at resolvedOf
        rw [notBirth] at resolvedOf
        simpa using resolvedOf
      exact ⟨authorizer, inPatch, notBirth, ⟨kind, kindEq, bearing⟩, s, law, resolved, admits, names⟩
    · rw [row] at bearing; cases bearing
    · rw [row] at bearing; cases bearing
  · cases produced

/-- **Every write of a fault-free patch is lawful**: rooted-law writes are
admitted by their law, a neutral birth is `Named` by a judged authorizer, a
kernel-only write is by a named writer. -/
theorem lawful_of_lawFault {writes : List DataWrite}
    {step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext}
    (lawful : lawFault laws family state writes step = none) :
    ∀ write (member : write ∈ writes), Lawful laws family state writes write (step write member) :=
  fun write member =>
    LawfulBy.mono laws family state (fun _ named => named_of_authorizer laws family state lawful named)
      ((lawFault_none_iff laws family state writes step).1 lawful write member)

theorem judgeLaw_lawDenied {cell : Nat} {law? : Option ResolvedLaw} {s : PolicyStepContext}
    {cell' : Nat} {leaf : LawLeaf} (denied : judgeLaw cell law? s = some (.lawDenied cell' leaf)) :
    cell' = cell ∧ ∃ law, law? = some law ∧
      law.predicate.subterm leaf.path = some leaf.clause ∧ leaf.clause.isLeaf = true ∧
      Minidregg.Pred.eval leaf.clause s.oldState s.newState = false ∧
      Minidregg.Pred.eval law.predicate s.oldState s.newState = false := by
  unfold judgeLaw at denied
  cases law? with
  | none => simp at denied
  | some law =>
    cases lowerable : law.supported
    · simp [lowerable] at denied
    cases inRange : law.inRange
    · simp [lowerable, inRange] at denied
    cases casts : law.castsInjective
    · simp [lowerable, inRange, casts] at denied
    cases named : LawLeaf.of law.predicate s.oldState s.newState with
    | none => simp [lowerable, inRange, casts, named] at denied
    | some found =>
      simp [lowerable, inRange, casts, named] at denied
      obtain ⟨rfl, rfl⟩ := denied
      obtain ⟨at_, isLeaf, fails⟩ := LawLeaf.of_fails _ _ _ _ named
      have rejects : Minidregg.Pred.eval law.predicate s.oldState s.newState = false := by
        cases evaluated : Minidregg.Pred.eval law.predicate s.oldState s.newState
        · rfl
        · rw [(LawLeaf.of_none_iff _ _ _).2 evaluated] at named; cases named
      exact ⟨rfl, law, rfl, at_, isLeaf, fails, rejects⟩

theorem judgeBearing_lawDenied {authorizers : List PolicyStepContext} {patch : List DataWrite}
    {write : DataWrite}
    {step : Option PolicyStepContext} {cell : Nat} {leaf : LawLeaf}
    (denied : judgeBearing laws state authorizers patch write step = some (.lawDenied cell leaf)) :
    cell = write.cellId.value ∧ ∃ s law, step = some s ∧ lawOf laws state patch write s = some law ∧
      law.predicate.subterm leaf.path = some leaf.clause ∧ leaf.clause.isLeaf = true ∧
      Minidregg.Pred.eval leaf.clause s.oldState s.newState = false ∧
      Minidregg.Pred.eval law.predicate s.oldState s.newState = false := by
  unfold judgeBearing at denied
  cases step with
  | none => simp at denied
  | some s =>
    dsimp only at denied
    by_cases neutral : ((lawOf laws state patch write s).any (fun law => !law.rooted) &&
        !(authorizers.any fun authorizer => namesBirth authorizer write)) = true
    · rw [if_pos neutral] at denied; cases denied
    · rw [if_neg neutral] at denied
      obtain ⟨same, law, resolved, rest⟩ := judgeLaw_lawDenied denied
      exact ⟨same, s, law, rfl, resolved, rest⟩

theorem judgeKernel_not_lawDenied {write : DataWrite} {kind : Kind} {writers : List FamilyId}
    {step : Option PolicyStepContext} {cell : Nat} {leaf : LawLeaf} :
    judgeKernel family write kind writers step ≠ some (.lawDenied cell leaf) := by
  unfold judgeKernel
  cases step with
  | some _ => simp
  | none => by_cases named : family ∈ writers <;> simp [named]

/-- **A denial names the clause that failed, on the step it failed.**  The
named clause sits in the law the write was judged by (`lawOf`: its committed law,
or a birth's export law) at its path, is a leaf, and is false on the same old and
new states the law was evaluated on. -/
theorem judgeWrite_lawDenied {authorizers : List PolicyStepContext} {patch : List DataWrite}
    {write : DataWrite}
    {step : Option PolicyStepContext} {cell : Nat} {leaf : LawLeaf}
    (denied : judgeWrite laws family state authorizers patch write step = some (.lawDenied cell leaf)) :
    cell = write.cellId.value ∧ ∃ s law, step = some s ∧ lawOf laws state patch write s = some law ∧
      law.predicate.subterm leaf.path = some leaf.clause ∧ leaf.clause.isLeaf = true ∧
      Minidregg.Pred.eval leaf.clause s.oldState s.newState = false ∧
      Minidregg.Pred.eval law.predicate s.oldState s.newState = false := by
  unfold judgeWrite at denied
  cases kindEq : laws.kindOf state write with
  | none => simp [kindEq] at denied
  | some kind =>
    simp only [kindEq] at denied
    cases classEq : kind.lawClass with
    | kernelOnly writers =>
        simp only [classEq] at denied
        exact absurd denied (judgeKernel_not_lawDenied family)
    | lawBearing =>
        simp only [classEq] at denied
        exact judgeBearing_lawDenied laws state denied
    | kernelOnlyOrBorn writers =>
        simp only [classEq] at denied
        cases birthEq : laws.birth state write with
        | true =>
            simp only [birthEq, if_true] at denied
            exact judgeBearing_lawDenied laws state denied
        | false =>
            simp only [birthEq, Bool.false_eq_true, if_false] at denied
            exact absurd denied (judgeKernel_not_lawDenied family)

/-- **Only the named families write a kernel-only cell.** -/
theorem kernelOnly_writers {writes : List DataWrite}
    {step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext}
    (lawful : lawFault laws family state writes step = none)
    {write : DataWrite} (member : write ∈ writes) {kind : Kind} {writers : List FamilyId}
    (kindEq : laws.kindOf state write = some kind) (row : kind.lawClass = .kernelOnly writers) :
    family ∈ writers := by
  obtain ⟨kind', kindEq', judged⟩ := lawful_of_lawFault laws family state lawful write member
  rw [kindEq] at kindEq'
  cases kindEq'
  rcases judged with ⟨bearing, -⟩ | ⟨writers', row', named, -⟩ | ⟨writers', row', -⟩
  · rw [row] at bearing; cases bearing
  · rw [row] at row'; cases row'; exact named
  · rw [row] at row'; cases row'

/-- **A law source is written in place only by its named writers, and otherwise
only born, judged** (`kernelOnlyOrBorn`): in a fault-free patch such a write is
a step-free write by a family its row names (PolicyInstall); or a birth whose
NON-EMPTY export law (`rooted`) resolved and admitted the step; or a birth
`Named` by a judged authorizer -- a non-birth, law-bearing write of the same
patch whose committed law admitted a step naming the newborn's id and post root. -/
theorem kernelOnlyOrBorn_written_or_born {writes : List DataWrite}
    {step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext}
    (lawful : lawFault laws family state writes step = none)
    {write : DataWrite} (member : write ∈ writes) {kind : Kind} {writers : List FamilyId}
    (kindEq : laws.kindOf state write = some kind) (row : kind.lawClass = .kernelOnlyOrBorn writers) :
    (laws.birth state write = false ∧ family ∈ writers ∧ step write member = none) ∨
      (laws.birth state write = true ∧ ∃ s law, step write member = some s ∧
        lawOf laws state writes write s = some law ∧ Admits law s ∧
        (law.rooted = true ∨ Named laws state writes write)) := by
  obtain ⟨kind', kindEq', judged⟩ := lawful_of_lawFault laws family state lawful write member
  rw [kindEq] at kindEq'
  cases kindEq'
  rcases judged with ⟨bearing, -⟩ | ⟨writers', row', -⟩ | ⟨writers', row', either⟩
  · rw [row] at bearing; cases bearing
  · rw [row] at row'; cases row'
  · rw [row] at row'; cases row'
    rcases either with ⟨birth, s, law, stepEq, resolved, rooted, admits⟩ | other
    · exact Or.inr ⟨birth, s, law, stepEq, resolved, admits, rooted⟩
    · exact Or.inl other

end Judge

/-! ## The deployed law source -/

/-- The kind of a written cell on the loaded durable state: the live post
cell's kind; for a retirement, the kind of the cell the directory holds. -/
def physicalKind (durable : Durable) (write : DataWrite) : Option Kind :=
  match (LifecycleImage.codec registry).decode write.canonicalPostBytes with
  | some (.live cell) => some cell.kind
  | _ =>
    match loadDirectory durable with
    | none => none
    | some directory =>
      match directory.directory.slots write.cellId.value with
      | .present cell => some cell.kind
      | _ => none

/-- A write creates its cell exactly when the loaded state holds no live cell at
its id (a fresh or retired image, or none). -/
def physicalBirth (durable : Durable) (write : DataWrite) : Bool :=
  match (LifecycleImage.codec registry).decode (durable.snapshot.canonicalBytes write.cellId) with
  | some (.live _) => false
  | _ => true

/-- The live cell a write's post image holds. -/
def livePost (write : DataWrite) : Option (Minidregg.Theory.CellRegistry.PackedCell registry) :=
  match (LifecycleImage.codec registry).decode write.canonicalPostBytes with
  | some (.live cell) => some cell
  | _ => none

/-- A write whose post bytes are a live cell's image holds that cell. -/
theorem livePost_live {write : DataWrite} {cell : Minidregg.Theory.CellRegistry.PackedCell registry}
    (bytes : write.canonicalPostBytes = LifecycleImage.bytes registry (.live cell)) :
    livePost write = some cell := by
  unfold livePost
  rw [bytes, show LifecycleImage.bytes registry (.live cell) =
      (LifecycleImage.codec registry).encode (.live cell) from rfl,
    LifecycleImage.decode_encode]

/-- **A write to a cell the loaded directory holds is no birth.** -/
theorem physicalBirth_false_of_present {durable : Durable} (directory : LoadedDirectory durable)
    {write : DataWrite} {cell : Minidregg.Theory.CellRegistry.PackedCell registry}
    (present : directory.directory.slots write.cellId.value = .present cell) :
    physicalBirth durable write = false := by
  unfold physicalBirth
  rw [show durable.snapshot.canonicalBytes write.cellId =
      durable.snapshot.canonicalBytes ⟨write.cellId.value⟩ from rfl,
    ← directory.bytes_exact write.cellId.value]
  simp only [LifecycleImage.view, present]
  rw [show LifecycleImage.bytes registry (.live cell) =
      (LifecycleImage.codec registry).encode (.live cell) from rfl,
    LifecycleImage.decode_encode]

/-- **A newborn's birth parent**: the room `patch` places it in, its entry in the
append-only `parent` plane of the authority cell the patch writes. -/
def birthRoom (deployment : Deployment) (patch : List DataWrite) (newborn : Nat) : Option Nat := do
  let authorityWrite ← patch.find? fun write => write.cellId.value == deployment.authorityCellId
  match (LifecycleImage.codec registry).decode authorityWrite.canonicalPostBytes with
  | some (.live ⟨.authority, payload⟩) => payload.logical ⟨.parent, newborn⟩
  | _ => none

/-- **The export law's roots**: the birth room's descendants law, then the
structural restrictions the newborn's kind carries (a world instance's world kind)
-- the same composition as `BirthExportAdmission.roots` over a birth item whose
parent is the room. -/
def exportRoots (deployment : Deployment) (patch : List DataWrite) (newborn : Nat)
    (structural : WorldKindLawDependencies.Dependencies) : List PolicyRef :=
  ((birthRoom deployment patch newborn).toList.map fun room => ⟨⟨room⟩, .descendants, .head⟩) ++
    structural.additional

/-- **The export law of a birth on `step`**, before the Receiver's guards: the
composed law of `roots` with the three compiler verdicts
(`PhysicalLawResolution.judgeRoots`) and the source cells it read.  With no roots
the birth is NEUTRAL -- the conjunction of no parent law, `all []`, unrooted: the
Receiver admits it only when a judged authorizer of the same patch names the
newborn (`judgeBearing`, `Named`). -/
def exportLaw {Fld : Type} [Field Fld] [DecidableEq Fld] (profile : PolicyCompilerProfile Fld)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Minidregg.Theory.CellRegistry.Directory Nat registry) (roots : List PolicyRef)
    (step : PolicyStepContext) : Option ResolvedLaw :=
  match roots with
  | [] => some ⟨.all [], true, true, true, false, []⟩
  | _ :: _ => (PhysicalLawResolution.judgeRoots profile snapshot directory roots step).map fun judged =>
      ⟨judged.predicate, judged.inRange, judged.castsInjective, judged.supported, true,
        judged.law.sourceGuards.map fun (cell, root) => (⟨⟨cell⟩, root⟩ : ReadGuard)⟩

/-- A neutral birth's export law is the unrooted `all []`. -/
theorem exportLaw_nil {Fld : Type} [Field Fld] [DecidableEq Fld] (profile : PolicyCompilerProfile Fld)
    (snapshot : CredentialAuthorityDomain.Snapshot) (directory : Minidregg.Theory.CellRegistry.Directory Nat registry)
    (step : PolicyStepContext) :
    exportLaw profile snapshot directory [] step = some ⟨.all [], true, true, true, false, []⟩ := rfl

/-- A parented birth's export law is exactly the composed roots' judgement. -/
theorem exportLaw_cons_some_iff {Fld : Type} [Field Fld] [DecidableEq Fld]
    (profile : PolicyCompilerProfile Fld) (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Minidregg.Theory.CellRegistry.Directory Nat registry) (root : PolicyRef) (rest : List PolicyRef)
    (step : PolicyStepContext) (law : ResolvedLaw) :
    exportLaw profile snapshot directory (root :: rest) step = some law ↔
      ∃ judged, PhysicalLawResolution.judgeRoots profile snapshot directory (root :: rest) step =
          some judged ∧
        law = ⟨judged.predicate, judged.inRange, judged.castsInjective, judged.supported, true,
          judged.law.sourceGuards.map fun (cell, root) => (⟨⟨cell⟩, root⟩ : ReadGuard)⟩ := by
  simp only [exportLaw, Option.map_eq_some_iff]
  constructor
  · rintro ⟨judged, hj, rfl⟩; exact ⟨judged, hj, rfl⟩
  · rintro ⟨judged, hj, rfl⟩; exact ⟨judged, hj, rfl⟩

/-- The base portal of the Receiver's law configurations.  It supplies only the
capability faces, which law resolution never reads: `Config.resolve?` reads the
snapshot, the source store, the profile's semantics, the target and the
structural restrictions. -/
def lawPortal (snapshot : CredentialAuthorityDomain.Snapshot) :=
  CredentialAuthorityPolicyRegistry.sourceCapabilityPortal snapshot 0

/-- **The deployed law source**: load the directory and the authority cell of
the same durable state, then `PhysicalLawResolution.judge` on
`PhysicalLawResolution.targetConfig` -- the sequence the DRC's `authorizeLeg`
runs.  The guards are the authority cell (policy heads and parentage), the
law's source cells and its structural (world-kind) cells. -/
def Laws.physical {Fld : Type} [Field Fld] [DecidableEq Fld]
    (profile : PolicyCompilerProfile Fld) (deployment : Deployment) : Laws Durable where
  kindOf := physicalKind
  birth := physicalBirth
  resolveBirth durable patch write step := do
    let directory ← loadDirectory durable
    let authority ← loadDeployment deployment durable.snapshot
    let newborn ← livePost write
    let structural ← WorldKindLawDependencies.loadNewborn deployment directory.directory
      write.cellId.value newborn
    let law ← exportLaw profile authority.snapshot directory.directory
      (exportRoots deployment patch write.cellId.value structural) step
    pure { law with guards := authority.readGuards ++ law.guards ++
      structural.readGuards.map fun (cell, root) => (⟨⟨cell⟩, root⟩ : ReadGuard) }
  resolve durable target step := do
    let directory ← loadDirectory durable
    let authority ← loadDeployment deployment durable.snapshot
    let structural ← WorldKindLawDependencies.loadTarget deployment directory.directory target
    let sources ← PhysicalLawResolution.readGuards authority.snapshot directory.directory
      profile.semantics target structural.additional
    let judged ← PhysicalLawResolution.judge (PhysicalLawResolution.targetConfig deployment profile
      authority.snapshot directory.directory (lawPortal authority.snapshot) step target)
    pure ⟨judged.law.predicate, judged.inRange, judged.castsInjective, judged.supported, true,
      authority.readGuards ++ (sources ++ structural.readGuards).map fun (cell, root) =>
        (⟨⟨cell⟩, root⟩ : ReadGuard)⟩

/-- **The deployed law is the DRC's law.**  `Laws.physical` resolves a target's
law exactly when the directory and authority cell load, the structural
restrictions and source guards load, and `PhysicalLawResolution.judge` -- the
judgement `authorizeLeg` runs -- resolves it on the target configuration; the
predicate and the three compiler verdicts are that judgement's, and the guards are
the authority cell, the sources and the structural cells. -/
theorem physical_resolve_some_iff {Fld : Type} [Field Fld] [DecidableEq Fld]
    (profile : PolicyCompilerProfile Fld) (deployment : Deployment) (durable : Durable)
    (target : Nat) (step : PolicyStepContext) (law : ResolvedLaw) :
    (Laws.physical profile deployment).resolve durable target step = some law ↔
      ∃ directory authority structural sources judged,
        loadDirectory durable = some directory ∧
        loadDeployment deployment durable.snapshot = some authority ∧
        WorldKindLawDependencies.loadTarget deployment directory.directory target = some structural ∧
        PhysicalLawResolution.readGuards authority.snapshot directory.directory profile.semantics
          target structural.additional = some sources ∧
        PhysicalLawResolution.judge (PhysicalLawResolution.targetConfig deployment profile
          authority.snapshot directory.directory (lawPortal authority.snapshot) step target) =
            some judged ∧
        law = ⟨judged.law.predicate, judged.inRange, judged.castsInjective, judged.supported, true,
          authority.readGuards ++ (sources ++ structural.readGuards).map fun (cell, root) =>
            (⟨⟨cell⟩, root⟩ : ReadGuard)⟩ := by
  simp only [Laws.physical, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq]
  constructor
  · rintro ⟨directory, hd, authority, ha, structural, hs, sources, hg, judged, hj, rfl⟩
    exact ⟨directory, authority, structural, sources, judged, hd, ha, hs, hg, hj, rfl⟩
  · rintro ⟨directory, authority, structural, sources, judged, hd, ha, hs, hg, hj, rfl⟩
    exact ⟨directory, hd, authority, ha, structural, hs, sources, hg, judged, hj, rfl⟩

/-- **A birth is judged by its export law, read by the Receiver.**  The deployed
law of a birth resolves exactly when the directory and authority load, the
newborn's post is a live cell whose structural restrictions load, and its
export law (`exportLaw`) resolves on the export roots -- its room's descendants
law, from the parent plane of the authority cell the SAME patch writes, and its
kind's structural restrictions -- on the family's step: their composed judgement
(`exportLaw_cons_some_iff`), or, with no root, the neutral law (`exportLaw_nil`).  Nothing the family
chose enters but the step and the patch it writes. -/
theorem physical_resolveBirth_some_iff {Fld : Type} [Field Fld] [DecidableEq Fld]
    (profile : PolicyCompilerProfile Fld) (deployment : Deployment) (durable : Durable)
    (patch : List DataWrite) (write : DataWrite) (step : PolicyStepContext) (law : ResolvedLaw) :
    (Laws.physical profile deployment).resolveBirth durable patch write step = some law ↔
      ∃ directory authority newborn structural exported,
        loadDirectory durable = some directory ∧
        loadDeployment deployment durable.snapshot = some authority ∧
        livePost write = some newborn ∧
        WorldKindLawDependencies.loadNewborn deployment directory.directory write.cellId.value
          newborn = some structural ∧
        exportLaw profile authority.snapshot directory.directory
          (exportRoots deployment patch write.cellId.value structural) step = some exported ∧
        law = { exported with guards := authority.readGuards ++ exported.guards ++
          structural.readGuards.map fun (cell, root) => (⟨⟨cell⟩, root⟩ : ReadGuard) } := by
  simp only [Laws.physical, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq]
  constructor
  · rintro ⟨directory, hd, authority, ha, newborn, hn, structural, hs, judged, hj, rfl⟩
    exact ⟨directory, authority, newborn, structural, judged, hd, ha, hn, hs, hj, rfl⟩
  · rintro ⟨directory, authority, newborn, structural, judged, hd, ha, hn, hs, hj, rfl⟩
    exact ⟨directory, hd, authority, ha, newborn, hn, structural, hs, judged, hj, rfl⟩

#assert_axioms judgeWrite_none_iff
#assert_axioms lawFault_none_iff
#assert_axioms judgeWrite_lawDenied
#assert_axioms kernelOnly_writers
#assert_axioms kernelOnlyOrBorn_written_or_born
#assert_axioms judgeLaw_none_iff
#assert_axioms judgeBearing_none_iff
#assert_axioms physical_resolve_some_iff
#assert_axioms physical_resolveBirth_some_iff
#assert_axioms exportLaw_cons_some_iff
#assert_axioms livePost_live
#assert_axioms physicalBirth_false_of_present

end Minidregg.Kernel.ReceivingLaw
