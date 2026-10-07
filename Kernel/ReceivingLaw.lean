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

/-- The verdicts of one resolved law on one step. -/
def judgeLaw (cell : Nat) (law? : Option ResolvedLaw) (step : PolicyStepContext) : Option LawFault :=
  match law? with
  | none => some (.lawUnavailable cell .unresolved)
  | some law =>
    if !law.supported then some (.lawUnsupported cell)
    else if !law.inRange then some (.lawInputRange cell)
    else if !law.castsInjective then some (.lawCastAlias cell)
    else (LawLeaf.of law.predicate step.oldState step.newState).map (.lawDenied cell)

/-- A law-bearing write's judgement: a step is required, and its law decides. -/
def judgeBearing (patch : List DataWrite) (write : DataWrite) (step : Option PolicyStepContext) :
    Option LawFault :=
  match step with
  | none => some (.lawUnavailable write.cellId.value .noStep)
  | some step => judgeLaw write.cellId.value (lawOf laws state patch write step) step

/-- A kernel-only write's judgement: no step, and a named writer. -/
def judgeKernel (write : DataWrite) (kind : Kind) (writers : List FamilyId)
    (step : Option PolicyStepContext) : Option LawFault :=
  match step with
  | some _ => some (.registryMismatch write.cellId.value kind)
  | none => if family ∈ writers then none else some (.kernelOnlyForeignWriter write.cellId.value kind family)

/-- The judgement of one write of `patch`. -/
def judgeWrite (patch : List DataWrite) (write : DataWrite) (step : Option PolicyStepContext) :
    Option LawFault :=
  match laws.kindOf state write with
  | none => some (.unclassified write.cellId.value)
  | some kind =>
    match kind.lawClass with
    | .kernelOnly writers => judgeKernel family write kind writers step
    | .lawBearing => judgeBearing laws state patch write step
    | .kernelOnlyOrBorn writers =>
        if laws.birth state write then judgeBearing laws state patch write step
        else judgeKernel family write kind writers step

/-- The first fault among a patch's writes, in write order. -/
def lawFault (writes : List DataWrite)
    (step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext) : Option LawFault :=
  writes.attach.findSome? fun ⟨write, member⟩ =>
    judgeWrite laws family state writes write (step write member)

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

/-- A family whose step does not depend on the membership proof is judged write by write. -/
theorem lawFault_uniform (writes : List DataWrite) (step : DataWrite → Option PolicyStepContext) :
    lawFault laws family state writes (fun write _ => step write) =
      writes.findSome? fun write => judgeWrite laws family state writes write (step write) :=
  findSome?_attach writes fun write => judgeWrite laws family state writes write (step write)

theorem lawGuards_uniform (writes : List DataWrite) (step : DataWrite → Option PolicyStepContext) :
    lawGuards laws state writes (fun write _ => step write) =
      writes.flatMap fun write => writeGuards laws state writes write (step write) :=
  flatMap_attach writes fun write => writeGuards laws state writes write (step write)

/-- A law-bearing write was judged and admitted: it carried a step, its law
(`lawOf`: a birth's export law, else its committed law) resolved, the three
compiler verdicts are true and `Pred.eval` accepts the step. -/
def Judged (patch : List DataWrite) (write : DataWrite) (step : Option PolicyStepContext) : Prop :=
  ∃ s law, step = some s ∧ lawOf laws state patch write s = some law ∧
    law.supported = true ∧ law.inRange = true ∧ law.castsInjective = true ∧
    Minidregg.Pred.eval law.predicate s.oldState s.newState = true

/-- What it means for one write of `patch` to be lawful. -/
def Lawful (patch : List DataWrite) (write : DataWrite) (step : Option PolicyStepContext) : Prop :=
  ∃ kind, laws.kindOf state write = some kind ∧
    ((kind.lawClass = .lawBearing ∧ Judged laws state patch write step) ∨
      (∃ writers, kind.lawClass = .kernelOnly writers ∧ family ∈ writers ∧ step = none) ∨
      (∃ writers, kind.lawClass = .kernelOnlyOrBorn writers ∧
        ((laws.birth state write = true ∧ Judged laws state patch write step) ∨
          (laws.birth state write = false ∧ family ∈ writers ∧ step = none))))

theorem judgeLaw_none_iff (cell : Nat) (law? : Option ResolvedLaw) (step : PolicyStepContext) :
    judgeLaw cell law? step = none ↔
      ∃ law, law? = some law ∧ law.supported = true ∧ law.inRange = true ∧
        law.castsInjective = true ∧ Minidregg.Pred.eval law.predicate step.oldState step.newState = true := by
  unfold judgeLaw
  cases law? with
  | none => simp
  | some law =>
    cases lowerable : law.supported <;> cases inRange : law.inRange <;>
      cases casts : law.castsInjective <;>
      simp [lowerable, inRange, casts, Option.map_eq_none_iff, LawLeaf.of_none_iff]

theorem judgeBearing_none_iff (patch : List DataWrite) (write : DataWrite)
    (step : Option PolicyStepContext) :
    judgeBearing laws state patch write step = none ↔ Judged laws state patch write step := by
  unfold judgeBearing Judged
  cases step with
  | none => simp
  | some s =>
    rw [judgeLaw_none_iff]
    constructor
    · rintro ⟨law, resolved, verdicts⟩
      exact ⟨s, law, rfl, resolved, verdicts⟩
    · rintro ⟨s', law, same, resolved, verdicts⟩
      cases same
      exact ⟨law, resolved, verdicts⟩

theorem judgeKernel_none_iff (write : DataWrite) (kind : Kind) (writers : List FamilyId)
    (step : Option PolicyStepContext) :
    judgeKernel family write kind writers step = none ↔ family ∈ writers ∧ step = none := by
  unfold judgeKernel
  cases step with
  | some s => simp
  | none => by_cases named : family ∈ writers <;> simp [named]

/-- **One write is judged exactly.** -/
theorem judgeWrite_none_iff (patch : List DataWrite) (write : DataWrite)
    (step : Option PolicyStepContext) :
    judgeWrite laws family state patch write step = none ↔ Lawful laws family state patch write step := by
  unfold judgeWrite Lawful
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

/-- **The patch is judged exactly**: no fault iff every write is lawful. -/
theorem lawFault_none_iff (writes : List DataWrite)
    (step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext) :
    lawFault laws family state writes step = none ↔
      ∀ write (member : write ∈ writes), Lawful laws family state writes write (step write member) := by
  unfold lawFault
  rw [List.findSome?_eq_none_iff]
  constructor
  · intro none_ write member
    exact (judgeWrite_none_iff laws family state writes write (step write member)).1
      (none_ ⟨write, member⟩ (List.mem_attach _ _))
  · rintro all ⟨write, member⟩ -
    exact (judgeWrite_none_iff laws family state writes write (step write member)).2 (all write member)

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

theorem judgeBearing_lawDenied {patch : List DataWrite} {write : DataWrite}
    {step : Option PolicyStepContext} {cell : Nat} {leaf : LawLeaf}
    (denied : judgeBearing laws state patch write step = some (.lawDenied cell leaf)) :
    cell = write.cellId.value ∧ ∃ s law, step = some s ∧ lawOf laws state patch write s = some law ∧
      law.predicate.subterm leaf.path = some leaf.clause ∧ leaf.clause.isLeaf = true ∧
      Minidregg.Pred.eval leaf.clause s.oldState s.newState = false ∧
      Minidregg.Pred.eval law.predicate s.oldState s.newState = false := by
  unfold judgeBearing at denied
  cases step with
  | none => simp at denied
  | some s =>
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
theorem judgeWrite_lawDenied {patch : List DataWrite} {write : DataWrite}
    {step : Option PolicyStepContext} {cell : Nat} {leaf : LawLeaf}
    (denied : judgeWrite laws family state patch write step = some (.lawDenied cell leaf)) :
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
  obtain ⟨kind', kindEq', judged⟩ := (lawFault_none_iff laws family state writes step).1 lawful write member
  rw [kindEq] at kindEq'
  cases kindEq'
  rcases judged with ⟨bearing, -⟩ | ⟨writers', row', named, -⟩ | ⟨writers', row', -⟩
  · rw [row] at bearing; cases bearing
  · rw [row] at row'; cases row'; exact named
  · rw [row] at row'; cases row'

/-- **A law source is written in place only by its named writers, and otherwise
only born under its export law** (`kernelOnlyOrBorn`): in a lawful patch, such a
write is either a birth whose export law resolved and admitted the step, or a
step-free write by a family its row names. -/
theorem kernelOnlyOrBorn_written_or_born {writes : List DataWrite}
    {step : (write : DataWrite) → write ∈ writes → Option PolicyStepContext}
    (lawful : lawFault laws family state writes step = none)
    {write : DataWrite} (member : write ∈ writes) {kind : Kind} {writers : List FamilyId}
    (kindEq : laws.kindOf state write = some kind) (row : kind.lawClass = .kernelOnlyOrBorn writers) :
    (laws.birth state write = true ∧ Judged laws state writes write (step write member)) ∨
      (laws.birth state write = false ∧ family ∈ writers ∧ step write member = none) := by
  obtain ⟨kind', kindEq', judged⟩ := (lawFault_none_iff laws family state writes step).1 lawful write member
  rw [kindEq] at kindEq'
  cases kindEq'
  rcases judged with ⟨bearing, -⟩ | ⟨writers', row', -⟩ | ⟨writers', row', either⟩
  · rw [row] at bearing; cases bearing
  · rw [row] at row'; cases row'
  · rw [row] at row'; cases row'; exact either

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
the birth is NEUTRAL -- the conjunction of no parent law, `all []`, which every step
satisfies -- as `BirthExportAdmission.checkNeutral` admits an unparented birth whose
kind carries no restriction. -/
def exportLaw {Fld : Type} [Field Fld] [DecidableEq Fld] (profile : PolicyCompilerProfile Fld)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Minidregg.Theory.CellRegistry.Directory Nat registry) (roots : List PolicyRef)
    (step : PolicyStepContext) : Option ResolvedLaw :=
  match roots with
  | [] => some ⟨.all [], true, true, true, []⟩
  | _ :: _ => (PhysicalLawResolution.judgeRoots profile snapshot directory roots step).map fun judged =>
      ⟨judged.predicate, judged.inRange, judged.castsInjective, judged.supported,
        judged.law.sourceGuards.map fun (cell, root) => (⟨⟨cell⟩, root⟩ : ReadGuard)⟩

/-- A neutral birth's export law admits every step. -/
theorem exportLaw_nil {Fld : Type} [Field Fld] [DecidableEq Fld] (profile : PolicyCompilerProfile Fld)
    (snapshot : CredentialAuthorityDomain.Snapshot) (directory : Minidregg.Theory.CellRegistry.Directory Nat registry)
    (step : PolicyStepContext) :
    exportLaw profile snapshot directory [] step = some ⟨.all [], true, true, true, []⟩ := rfl

/-- A parented birth's export law is exactly the composed roots' judgement. -/
theorem exportLaw_cons_some_iff {Fld : Type} [Field Fld] [DecidableEq Fld]
    (profile : PolicyCompilerProfile Fld) (snapshot : CredentialAuthorityDomain.Snapshot)
    (directory : Minidregg.Theory.CellRegistry.Directory Nat registry) (root : PolicyRef) (rest : List PolicyRef)
    (step : PolicyStepContext) (law : ResolvedLaw) :
    exportLaw profile snapshot directory (root :: rest) step = some law ↔
      ∃ judged, PhysicalLawResolution.judgeRoots profile snapshot directory (root :: rest) step =
          some judged ∧
        law = ⟨judged.predicate, judged.inRange, judged.castsInjective, judged.supported,
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
    pure ⟨judged.law.predicate, judged.inRange, judged.castsInjective, judged.supported,
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
        law = ⟨judged.law.predicate, judged.inRange, judged.castsInjective, judged.supported,
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

end Minidregg.Kernel.ReceivingLaw
