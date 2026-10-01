/-
One-old-image preparation for a grain-backed birth. The birth factory, Book,
allocation and combined authority work is prepared first from a single
loaded durable image. Both existing grain targets are then prepared from that
same directory and old authority, before any policy or native signature can
be accepted. This is not a receiving endpoint.
-/
import Kernel.GrainResourceBirthFamilies

namespace Minidregg.Kernel.GrainResourceBirthTransaction

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CellState
open Minidregg.Kernel
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler.ResourceBirthCodec

set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

abbrev Source := GrainResourceBirthController.Source
abbrev Tariff := GrainResourceBirthController.Tariff
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DeclaredResourceController.Durable
abbrev Ambient := DeclaredResourceController.Ambient

structure PreparedTargets
    (deployment : Deployment)
    (directory : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (snapshot : CredentialAuthorityDomain.Snapshot)
    (semantics : Digest) (ambient : Ambient)
    (command : DeclaredResourceController.Command) where
  private mk ::
  targets : (i : DeclaredResourceController.TargetIndex command) →
    DeclaredResourceController.PreparedTarget deployment directory snapshot
      semantics ambient command command.targets[i]

def prepareTargets {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (pins : ResourceBirth.FactoryPins) (durable : Durable) (ambient : Ambient)
    (tariff : Tariff) (source : Source)
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source) :
    Except DeclaredResourceController.Reject
      (PreparedTargets deployment birth.prepared.pre.directory.directory
        birth.prepared.pre.authority.snapshot profile.semantics ambient
        (source.grainCommand tariff)) := do
  let command := source.grainCommand tariff
  let targets ← DeclaredResourceController.collect command.targets
    (DeclaredResourceController.prepareTarget deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient command)
  return ⟨targets⟩

/-- Birth's four classes of incidences and the two existing grain cells share
one authority incidence. The grain list remains indexed by the exact derived
command so neither target can be silently omitted. -/
abbrev Incidence (tariff : Tariff) (source : Source) :=
  ResourceBirthPolicyController.Concrete.Legs source.birth ⊕
    DeclaredResourceController.TargetIndex (source.grainCommand tariff)

def layout {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (_grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) : CellLayout (Incidence tariff source) where
  storeLayout
    | .inl .factory => EffectDeclaration.effectLayout
    | .inl .book => CanonicalResourceKernel.layout
    | .inl .authority => CredentialAuthorityState.layout
    | .inl (.allocation _) => LifecycleSlot.layout CanonicalCellRegistry.registry
    | .inr index => (source.grainCommand tariff).targets[index].layout
  materializer
    | .inl .factory => DeclaredEffectCell.materializer
    | .inl .book => CanonicalResourcePageMaterializer.materializer
    | .inl .authority => CredentialAuthorityCell.materializer
    | .inl (.allocation _) => LifecycleSlot.materializer CanonicalCellRegistry.registry
    | .inr index => (source.grainCommand tariff).targets[index].materializer
  projectAuthority := fun _ _ => birth.prepared.pre.authority.snapshot.authState
  cellId
    | .inl .factory => ⟨deployment.factoryId⟩
    | .inl .book => ⟨deployment.resourceBookId⟩
    | .inl .authority => CredentialAuthorityDomainReceiver.cellIdOf deployment
    | .inl (.allocation index) =>
        ⟨(ResourceBirthPolicyController.Concrete.creation source.birth index).cellId⟩
    | .inr index => ⟨(source.grainCommand tariff).targets[index].target⟩

def resourceContexts {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (height : Height) (position : Nat) : CanonicalResourceEffect.RequestContext :=
  let operation := source.birth.resourceBatch.operations[position]?
  let authority := birth.prepared.pre.authority.snapshot.authState
  let policyId : PolicyId :=
    ⟨(operation.map fun op => op.posting.source).getD source.birth.fee.payer⟩
  { domain := pins.domain
    semantics := pins.semantics
    federation := pins.federation
    subject := source.birth.creator
    subjectKeyEpoch := authority.subjectKeyEpoch source.birth.creator
    nonce := source.birth.nonce
    height := height
    policyId := policyId
    policyEpoch := authority.policyEpoch policyId
    policyRevision := authority.policyRevision policyId }

def rawLeg {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) (height : Height) (_ : Unit) :
    (incidence : Incidence tariff source) → CandidateLegData (layout birth grain) incidence
  | .inl .factory =>
      { pre := birth.prepared.pre.factory.payload
        patch := ResourceBirthPolicyController.factoryPatch birth.prepared.pre.factory.payload
        request := ⟨.object, source.factoryRequest tariff pins
          CanonicalCellRegistry.sourceEncoding birth.prepared.pre.authority.snapshot.authState
          birth.prepared.pre.factory.payload.root height⟩
        Postcondition := fun post => post = birth.prepared.pre.factory.payload.logical }
  | .inl .book =>
      { pre := birth.prepared.pre.book.payload
        patch := source.birth.resourceBatch.patch birth.prepared.pre.book.payload
        request := ⟨.account, CanonicalResourceEffect.birthRequest
          CanonicalCellRegistry.sourceEncoding birth.prepared.pre.book.payload
          (resourceContexts birth height) source.birth⟩
        Postcondition := fun post =>
          (source.birth.resourceBatch.patch birth.prepared.pre.book.payload).ResultAt
            birth.prepared.pre.book.payload.logical post ∧
          CanonicalResourceKernel.logicalBook post = source.birth.resourceBatch.apply
            (CanonicalResourceKernel.logicalBook birth.prepared.pre.book.payload.logical) }
  | .inl .authority =>
      { pre := birth.prepared.pre.authority.snapshot.cell
        patch := source.authorityPatch birth.prepared.pre.authority.snapshot
        request := ⟨.object, source.factoryRequest tariff pins
          CanonicalCellRegistry.sourceEncoding birth.prepared.pre.authority.snapshot.authState
          birth.prepared.pre.authority.snapshot.cell.root height⟩
        Postcondition := fun post =>
          (source.authorityPatch birth.prepared.pre.authority.snapshot).ResultAt
              birth.prepared.pre.authority.snapshot.cell.logical post }
  | .inl (.allocation index) =>
      { pre := ResourceBirthController.allocationPre birth.prepared.pre.directory.directory
          (ResourceBirthPolicyController.Concrete.creation source.birth index)
        patch := ResourceBirthController.allocationPatch
          (ResourceBirthPolicyController.Concrete.creation source.birth index)
        request := ⟨.object, ResourceBirthController.allocationRequest pins
          CanonicalCellRegistry.sourceEncoding birth.prepared.pre.authority.snapshot.authState
          birth.prepared.pre.directory.directory
          (ResourceBirthPolicyController.Concrete.creation source.birth index)
          height source.birth⟩
        Postcondition := fun post => post = LifecycleSlot.state CanonicalCellRegistry.registry
          (.live (ResourceBirthPolicyController.Concrete.creation source.birth index).cell) }
  | .inr index =>
      { pre := (grain.targets index).pre
        patch := DeclaredResourceController.targetPatch birth.prepared.pre.authority.snapshot
          profile.semantics ambient (source.grainCommand tariff)
          (source.grainCommand tariff).targets[index] (grain.targets index).pre
        request := ⟨(source.grainCommand tariff).targets[index].kind,
          DeclaredResourceController.requestFor birth.prepared.pre.authority.snapshot
            profile.semantics ambient (source.grainCommand tariff)
            (source.grainCommand tariff).targets[index] (grain.targets index).pre.root⟩
        Postcondition := fun post =>
          (DeclaredResourceController.targetPatch birth.prepared.pre.authority.snapshot
            profile.semantics ambient (source.grainCommand tariff)
            (source.grainCommand tariff).targets[index] (grain.targets index).pre).ResultAt
              (grain.targets index).pre.logical post }

def bindFamily {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) (height : Height)
    (_ : Unit) (portals : Incidence tariff source → Portal) :
    (incidence : Incidence tariff source) →
      SemanticLegBinding (rawLeg birth grain height () incidence)
  | .inl .factory =>
      { Nullifier := Unit
        family := GrainResourceBirthFamilies.factoryFamily tariff source pins
          CanonicalCellRegistry.sourceEncoding birth.prepared.pre.authority.snapshot.authState
          birth.prepared.pre.factory.payload height
        declaration := (), outcome := ()
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }
  | .inl .book =>
      { Nullifier := Unit
        family := GrainResourceBirthFamilies.birthFamily tariff source pins
          CanonicalCellRegistry.sourceEncoding (portals (.inl .factory)) (portals (.inl .book))
          birth.prepared.pre.authority.snapshot.authState
          birth.prepared.pre.factory.payload.root height birth.prepared.pre.book.payload
          (resourceContexts birth height)
        declaration := (), outcome := ()
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }
  | .inl .authority =>
      { Nullifier := Nat
        family := GrainResourceBirthFamilies.authorityFamily tariff source pins
          CanonicalCellRegistry.sourceEncoding birth.prepared.pre.authority.snapshot
          profile.semantics height
        declaration := (), outcome := ()
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }
  | .inl (.allocation index) =>
      { Nullifier := Nat
        family := ResourceBirthController.allocationFamily pins
          CanonicalCellRegistry.sourceEncoding birth.prepared.pre.authority.snapshot.authState
          birth.prepared.pre.directory.directory
          (ResourceBirthPolicyController.Concrete.creation source.birth index) height
        declaration := source.birth, outcome := ()
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }
  | .inr index =>
      { Nullifier := Nat
        family := by
          change SemanticEffectFamily (source.grainCommand tariff).targets[index].layout
            (source.grainCommand tariff).targets[index].materializer Nat
          exact DeclaredResourceController.targetFamily deployment
            birth.prepared.pre.authority.snapshot profile.semantics ambient
            (source.grainCommand tariff) (source.grainCommand tariff).targets[index]
            (grain.targets index).pre
        declaration := (), outcome := (grain.targets index).post
        preExact := rfl, requestExact := rfl, effectsExact := by
          simp only [rawLeg, DeclaredResourceController.targetFamily,
            DeclaredResourceController.requestFor_eq_reference,
            DeclaredResourceController.requestForReference, id_eq]
        patchExact := rfl, postconditionExact := fun _ => Iff.rfl }

def plan {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) (height : Height) :
    PreparationPlan (layout birth grain) Unit where
  leg := rawLeg birth grain height
  jointDigest := fun _ => CanonicalCellRegistry.sourceEncoding.hashBytes
    ("DREGG/GRAIN-RESOURCE-BIRTH/JOINT/v1".toUTF8.toList ++ source.canonicalBytes tariff)
  legEffectsDigest := fun _ incidence =>
    (rawLeg birth grain height () incidence).request.2.effectsDigest
  bindFamily := bindFamily birth grain height

/-- Every allocated identity was fresh in the loaded directory: the allocator
accepted the whole birth descriptor. -/
theorem allocationFresh {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (index : Fin source.birth.createRequests.length) :
    LifecycleImage.view CanonicalCellRegistry.registry birth.prepared.pre.directory.directory
      (ResourceBirthPolicyController.Concrete.creation source.birth index).cellId = .fresh :=
  birth.prepared.post.allocated.fresh_pre _ (List.get_mem _ _)

theorem validated {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) (height : Height) :
    (incidence : Incidence tariff source) →
      ValidatedPatch ((layout birth grain).materializer incidence)
        (rawLeg birth grain height () incidence).pre
        (rawLeg birth grain height () incidence).request.2.preStateRoot
        (rawLeg birth grain height () incidence).patch
  | .inl .factory => ResourceBirthPolicyController.factoryValidated birth.prepared.pre.factory.payload
  | .inl .book => birth.prepared.post.resources.validated
  | .inl .authority => birth.authorityValidated
  | .inl (.allocation index) =>
      ResourceBirthController.allocationValidated birth.prepared.pre.directory.directory
        (ResourceBirthPolicyController.Concrete.creation source.birth index)
        (allocationFresh birth index)
  | .inr index => (grain.targets index).candidate.validated

theorem postconditions {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) (height : Height) :
    ∀ incidence, (rawLeg birth grain height () incidence).Postcondition
      (validated birth grain height incidence).apply.logical := by
  intro incidence
  cases incidence with
  | inl leg =>
      cases leg with
      | factory =>
          exact ResourceBirthPolicyController.factoryCandidate_preserves_control_cell pins
            CanonicalCellRegistry.sourceEncoding birth.prepared.pre.authority.snapshot.authState
            birth.prepared.pre.factory.payload height source.birth
      | book =>
          exact ⟨birth.prepared.post.resources.validated.resultAt,
            birth.prepared.post.resources.post_logicalBook⟩
      | authority => exact birth.authorityValidated.resultAt
      | allocation index =>
          exact ResourceBirthController.allocation_post_exact
            birth.prepared.pre.directory.directory
            (ResourceBirthPolicyController.Concrete.creation source.birth index)
            (allocationFresh birth index)
  | inr index => exact (grain.targets index).candidate.postcondition

/-- A complete joint tuple has one old state, one authority incidence, and
separate physical IDs for every newborn slot and both grain cells. Its height
comes from the same ambient used by grain preparation and its primary portal
is always the factory. -/
def prepareTuple {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) :
    Option (PreparedTuple (plan birth grain ambient.height)) :=
  if distinct : Function.Injective (layout birth grain).cellId then
    some
      { source := (), primary := .inl .factory
        validated := validated birth grain ambient.height
        postconditions := postconditions birth grain ambient.height
        cellIdsDistinct := distinct
        requestEffects := by
          intro incidence
          cases incidence with
          | inl leg => cases leg <;> rfl
          | inr index => rfl }
  else none

/-- Every physical grain write is derived from the same prepared target that
entered the joint semantic tuple. -/
def targetWrite {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff))
    (index : DeclaredResourceController.TargetIndex (source.grainCommand tariff)) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite (source.grainCommand tariff).targets[index].target
    (grain.targets index).before
    (DeclaredResourceController.packTarget (source.grainCommand tariff).targets[index]
      (grain.targets index).candidate.post)

def writes {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) : List DataWrite :=
  birth.prepared.writes ++
    (List.finRange (source.grainCommand tariff).targets.length).map (targetWrite birth grain)

/-- Every byte image in the coalesced birth-and-grain write set hashes to its
exact planned post root. The grain target branch uses the existing packed-write
constructor, while the birth branch retains its proved source lowering. -/
theorem writes_roots_bound {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) (write : DataWrite)
    (member : write ∈ writes birth grain) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  rcases List.mem_append.mp member with birthWrite | target
  · rcases List.mem_append.mp birthWrite with front | authority
    · rcases List.mem_append.mp front with allocation | native
      · obtain ⟨request, _, rfl⟩ := List.mem_map.mp allocation
        exact ResourceBirthController.birthWrite_root_bound request
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at native
        rcases native with rfl | rfl <;> rfl
    · simp only [GrainResourceBirthAuthority.Prepared.writes,
        CredentialAuthorityDomainReceiver.Loaded.writes, List.mem_singleton] at authority
      subst write
      exact birth.prepared.pre.authority.write_root_bound _
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp target
    rfl

def targetSourceGuards {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) : List ReadGuard :=
  (List.finRange (source.grainCommand tariff).targets.length).map fun index =>
    ⟨⟨(grain.targets index).source.readGuard.1⟩,
      (grain.targets index).source.readGuard.2⟩

def readGuards {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) : List ReadGuard :=
  birth.prepared.readGuards ++ targetSourceGuards birth grain

/-- This is one union physical shape, not independent successful birth and
grain shapes. It checks collisions and current roots across both write sets
and all old policy-source guards before a composite DataIntent is possible. -/
def PhysicalShape {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) : Prop :=
  ((writes birth grain).map DataWrite.cellId).Nodup ∧
  (∀ write ∈ writes birth grain,
    write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
  (∀ write ∈ writes birth grain,
    ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
  (∀ guard ∈ readGuards birth grain,
    guard.cellId ∉ (writes birth grain).map DataWrite.cellId) ∧
  (∀ guard ∈ readGuards birth grain,
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) : Decidable (PhysicalShape birth grain) := by
  unfold PhysicalShape
  infer_instance

theorem readGuards_readonly {F : Type} [Field F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    (birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source)
    (grain : PreparedTargets deployment birth.prepared.pre.directory.directory
      birth.prepared.pre.authority.snapshot profile.semantics ambient
      (source.grainCommand tariff)) (shape : PhysicalShape birth grain) :
    ∀ guard ∈ readGuards birth grain,
      guard.cellId ∉ (writes birth grain).map DataWrite.cellId := shape.2.2.2.1

end Minidregg.Kernel.GrainResourceBirthTransaction
