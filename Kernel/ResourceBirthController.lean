/-
# Kernel.ResourceBirthController -- lifecycle lifting for an accepted joint turn

This is the shared physical projection used by the birth receiving controller.
It lifts the existing checked fresh allocator into typed lifecycle-slot
candidates, and prepares a concrete birth from one restored physical snapshot:
allocation writes, the pinned factory and Book, and the one authority cell.

The complete birth application must select its authority and Book families in
source, construct their accepted incidences from the same Descriptor, and bind
the old authority cell. Nothing here manufactures those semantic proofs or calls
a host verdict; it is not a public raw-DataIntent endpoint.
-/
import Compiler.ResourceBirthCodec
import Compiler.CredentialAuthorityReplay
import Compiler.CredentialAuthorityDomainReceiver
import Compiler.GrainResourceBirthAuthority
import Theory.ResourceBirthAuthority
import Kernel.CanonicalResourceEffect
import Kernel.DurableDataIntent

namespace Minidregg.Kernel.ResourceBirthController

open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

/-! ## Checked allocation, retaining the exact executor equality -/

structure Allocated (registry : TypeRegistry Digest) (before : Directory Nat registry)
    (descriptor : Descriptor registry) where
  after : Directory Nat registry
  accepted : ResourceBirth.allocate registry before descriptor.createRequests = .ok after

def allocate? (registry : TypeRegistry Digest) (before : Directory Nat registry)
    (descriptor : Descriptor registry) :
    Except CellRegistry.RejectReason (Allocated registry before descriptor) :=
  match checked : ResourceBirth.allocate registry before descriptor.createRequests with
  | .error reason => .error reason
  | .ok after => .ok ⟨after, checked⟩

def birthWrite {registry : TypeRegistry Digest}
    (request : CreateRequest (CellId := Nat) registry) : DataWrite where
  cellId := ⟨request.cellId⟩
  expectedPre := physicalRoot (LifecycleImage.fresh (registry := registry))
  exactPost := physicalRoot (.live request.cell)
  canonicalPostBytes := LifecycleImage.bytes registry (.live request.cell)

def allocationWrites {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : List DataWrite :=
  descriptor.createRequests.map birthWrite

theorem birthWrite_root_bound {registry : TypeRegistry Digest}
    (request : CreateRequest (CellId := Nat) registry) :
    rootBytes (birthWrite request).canonicalPostBytes = (birthWrite request).exactPost := rfl

theorem Allocated.fresh_pre {registry : TypeRegistry Digest}
    {before : Directory Nat registry} {descriptor : Descriptor registry}
    (allocated : Allocated registry before descriptor)
    (request : CreateRequest (CellId := Nat) registry)
    (member : request ∈ descriptor.createRequests) :
    LifecycleImage.view registry before request.cellId = .fresh :=
  LifecycleImage.accepted_fresh_before registry before allocated.after
    descriptor.createRequests allocated.accepted request member

theorem Allocated.exact_post {registry : TypeRegistry Digest}
    {before : Directory Nat registry} {descriptor : Descriptor registry}
    (allocated : Allocated registry before descriptor)
    (request : CreateRequest (CellId := Nat) registry)
    (member : request ∈ descriptor.createRequests) :
    LifecycleImage.view registry allocated.after request.cellId = .live request.cell :=
  LifecycleImage.accepted_live_after registry before allocated.after
    descriptor.createRequests allocated.accepted request member

/-! ## Allocation is an actual typed candidate in the joint policy input -/

def allocationPre {registry : TypeRegistry Digest}
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry) :=
  LifecycleSlot.cell registry (LifecycleImage.view registry before request.cellId)

/-- This mode is derived only from the existing allocator. In particular,
an absent but permanently used identity cannot mint an allocation candidate. -/
def AllocationMode {registry : TypeRegistry Digest}
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry)
    (descriptor : Descriptor registry) : Prop :=
  request ∈ descriptor.createRequests ∧
    ∃ after, ResourceBirth.allocate registry before descriptor.createRequests = .ok after

/-- A fresh allocation of the lifecycle slot.  It is enabled only at an absent
slot, so it cannot validate over a live or retired identity. -/
def allocationPatch {registry : TypeRegistry Digest}
    (request : CreateRequest (CellId := Nat) registry) :
    Patch (LifecycleSlot.layout registry) :=
  [.allocate () () (some request.cell)]

theorem allocationPatch_valid_iff {registry : TypeRegistry Digest}
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry) :
    Patch.ValidFrom (allocationPre before request).logical (allocationPatch request) ↔
      LifecycleImage.view registry before request.cellId = .fresh := by
  change ((.allocate () () (some request.cell) : Op (LifecycleSlot.layout registry)).Enabled
      (LifecycleSlot.state registry (LifecycleImage.view registry before request.cellId)) ∧ True) ↔ _
  cases view : LifecycleImage.view registry before request.cellId with
  | fresh => simp [Op.Enabled, Store.Fresh, LifecycleSlot.state]
  | retired =>
      simp [Op.Enabled, Store.Fresh, LifecycleSlot.state, LifecycleSlot.slotAddress]
  | live cell =>
      simp [Op.Enabled, Store.Fresh, LifecycleSlot.state, LifecycleSlot.slotAddress]

theorem allocationValidated {registry : TypeRegistry Digest}
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry)
    (fresh : LifecycleImage.view registry before request.cellId = .fresh) :
    CellState.ValidatedPatch (LifecycleSlot.materializer registry)
      (allocationPre before request) (allocationPre before request).root
      (allocationPatch request) :=
  (CellState.validate_accepts _ _ _ _ rfl
    ((allocationPatch_valid_iff before request).mpr fresh)).choose

/-- Refuting pole: a retired or live identity admits no allocation. -/
theorem allocation_not_valid_of_used {registry : TypeRegistry Digest}
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry)
    (used : LifecycleImage.view registry before request.cellId ≠ .fresh) :
    ¬ Patch.ValidFrom (allocationPre before request).logical (allocationPatch request) :=
  fun valid => used ((allocationPatch_valid_iff before request).mp valid)

theorem allocation_post_exact {registry : TypeRegistry Digest}
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry)
    (fresh : LifecycleImage.view registry before request.cellId = .fresh) :
    (allocationValidated before request fresh).apply.logical =
      LifecycleSlot.state registry (.live request.cell) := by
  rw [CellState.ValidatedPatch.apply_logical]
  change (LifecycleSlot.state registry (LifecycleImage.view registry before request.cellId)).set
      ⟨(), ()⟩ (some (some request.cell)) = _
  rw [fresh]
  rfl

def allocationRequest {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (oldAuthority : AuthState)
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry)
    (height : Height) (descriptor : Descriptor registry) : Request .object :=
  { factoryRequest pins encoding oldAuthority (allocationPre before request).root height descriptor with
    argsDigest := encoding.hashBytes
      ("DREGG.RESOURCE.BIRTH.ALLOCATION.ARGS/v2".toUTF8.toList ++
        Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.nat.encode request.cellId ++
        encoding.codec.encode descriptor) }

/-- The allocation coordinate and full descriptor jointly supply the signed
argument commitment. A fresh root alone cannot identify a particular slot. -/
theorem allocationRequest_args_source {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (oldAuthority : AuthState)
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry)
    (height : Height) (descriptor : Descriptor registry) :
    (allocationRequest pins encoding oldAuthority before request height descriptor).argsDigest =
      encoding.hashBytes
        ("DREGG.RESOURCE.BIRTH.ALLOCATION.ARGS/v2".toUTF8.toList ++
          Minidregg.Compiler.Tower256ConcreteBackend.StreamCodec.nat.encode request.cellId ++
          encoding.codec.encode descriptor) := rfl

def allocationFamily {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (oldAuthority : AuthState)
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry)
    (height : Height) :
    SemanticEffectFamily (LifecycleSlot.layout registry) (LifecycleSlot.materializer registry)
      Nat where
  pre := allocationPre before request
  Declaration := Descriptor registry
  declarationCodec := encoding.codec
  request descriptor := ⟨.object,
    allocationRequest pins encoding oldAuthority before request height descriptor⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => CredentialAuthorityEffects.unitCodec
  ModeEvidence := fun descriptor _ => PLift (AllocationMode before request descriptor)
  Postcondition := fun _ _ logical => logical = LifecycleSlot.state registry (.live request.cell)
  effectDigest := encoding.effectsDigest
  patch := fun _ _ => allocationPatch request
  nullifier := fun _ _ => none
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => CredentialAuthorityEffects.sealedOnly

def allocationCandidate {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (oldAuthority : AuthState)
    {before : Directory Nat registry} {descriptor : Descriptor registry}
    (allocated : Allocated registry before descriptor)
    (request : CreateRequest (CellId := Nat) registry)
    (member : request ∈ descriptor.createRequests) (height : Height) :
    PolicyInstall.Candidate
      (allocationFamily pins encoding oldAuthority before request height)
      (allocationPre before request) descriptor () where
  preStateBound := rfl
  modeEvidence := ⟨member, allocated.after, allocated.accepted⟩
  validated := allocationValidated before request (allocated.fresh_pre request member)
  postcondition := allocation_post_exact before request (allocated.fresh_pre request member)

theorem allocation_candidate_physical_pre {registry : TypeRegistry Digest}
    {before : Directory Nat registry} {descriptor : Descriptor registry}
    (allocated : Allocated registry before descriptor)
    (request : CreateRequest (CellId := Nat) registry)
    (member : request ∈ descriptor.createRequests) :
    (allocationPre before request).bytes = [] := by
  rw [allocationPre, allocated.fresh_pre request member]
  exact LifecycleSlot.fresh_bytes registry

/-- The candidate post is already the actual physical envelope. Native cell
packing would add an erroneous second envelope and is not used here. -/
theorem allocation_candidate_physical_post {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (oldAuthority : AuthState)
    {before : Directory Nat registry} {descriptor : Descriptor registry}
    (allocated : Allocated registry before descriptor)
    (request : CreateRequest (CellId := Nat) registry)
    (member : request ∈ descriptor.createRequests) (height : Height) :
    (allocationCandidate pins encoding oldAuthority allocated request member height).post.bytes =
      (birthWrite request).canonicalPostBytes := by
  change (LifecycleSlot.materializer registry).codec.encode
    (allocationValidated before request (allocated.fresh_pre request member)).apply.logical = _
  rw [allocation_post_exact _ _ (allocated.fresh_pre request member)]
  exact LifecycleSlot.bytes_exact registry (.live request.cell)

theorem no_allocation_mode_of_retired {registry : TypeRegistry Digest}
    {before : Directory Nat registry} {request : CreateRequest (CellId := Nat) registry}
    {descriptor : Descriptor registry} (used : request.cellId ∈ before.used) :
    ¬AllocationMode before request descriptor := by
  rintro ⟨member, after, accepted⟩
  exact ResourceBirth.allocate_success_fresh registry before after descriptor.createRequests
    accepted request member used

/-! ## Durable execution is all-or-nothing -/

/-- Any install attempt exposes the complete old snapshot or the complete
data-bearing installation, including on either modeled crash boundary. -/
theorem settlement_no_partial (schedule : Schedule) (before : DataSnapshot rootBytes)
    (intent : DataIntent rootBytes) :
    (DurableDataIntent.execute schedule before intent).storeAfter before = before ∨
      (DurableDataIntent.execute schedule before intent).storeAfter before =
        DataSnapshot.install before intent :=
  execute_no_partial_data_commit schedule before intent

/-! ## Concrete source-owned preparation from one restored physical snapshot -/

namespace Concrete

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission

variable {F : Type} [Field F] {profile : PolicyCompilerProfile F}

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes

structure ObservedCell (deployment : Deployment) (directory : Directory Nat Registry)
    (identifier : Nat) (kind : CanonicalCellRegistry.Kind) where
  payload : CellState.Materialized (CanonicalCellRegistry.materializer kind)
  present : directory.slots identifier = .present ⟨kind, payload⟩
  law : CanonicalCellRegistry.CellLaw deployment identifier ⟨kind, payload⟩

/-- The kind is selected by receiver code. Merely presenting a valid Book or
factory elsewhere in the directory cannot select it for this deployment. -/
def observeCell (deployment : Deployment) (directory : Directory Nat Registry)
    (identifier : Nat) (kind : CanonicalCellRegistry.Kind) :
    Option (ObservedCell deployment directory identifier kind) := by
  cases observed : directory.slots identifier with
  | absent => exact none
  | present packed =>
      rcases packed with ⟨actualKind, payload⟩
      by_cases same : actualKind = kind
      · subst actualKind
        exact if law : CanonicalCellRegistry.CellLaw deployment identifier ⟨kind, payload⟩ then
          some ⟨payload, observed, law⟩ else none
      · exact none

def createsCodec : IndexedProgram.LawfulCodec
    (List (CreateRequest (CellId := Nat) Registry)) :=
  (Tower256ConcreteBackend.StreamCodec.list (createRequestStream Registry)).toLawful

/-- Equality is checked on complete canonical source bytes, not a hash. -/
def sameCreates (left right : List (CreateRequest (CellId := Nat) Registry)) : Bool :=
  createsCodec.encode left == createsCodec.encode right

theorem sameCreates_iff (left right : List (CreateRequest (CellId := Nat) Registry)) :
    sameCreates left right = true ↔ left = right := by
  simp only [sameCreates, beq_iff_eq]
  exact (lawful_encode_injective createsCodec).eq_iff

def packedWrite (identifier : Nat) (before after : PackedCell Registry) : DataWrite where
  cellId := ⟨identifier⟩
  expectedPre := physicalRoot (.live before)
  exactPost := physicalRoot (.live after)
  canonicalPostBytes := LifecycleImage.bytes Registry (.live after)

/-- Each source has one physical owner: allocation emits every new envelope;
the authority update emits its one cell; the pinned Book emits one final
ordered batch result. -/
def planWrites (deployment : Deployment) (descriptor : Descriptor Registry)
    (factory : CellState.Materialized Compiler.DeclaredEffectCell.materializer)
    (bookBefore bookAfter : CellState.Materialized
      Compiler.CanonicalResourcePageMaterializer.materializer)
    (authorityWrites : List DataWrite) : List DataWrite :=
  allocationWrites descriptor ++
    [packedWrite deployment.factoryId ⟨.declaredObject, factory⟩ ⟨.declaredObject, factory⟩,
     packedWrite deployment.resourceBookId ⟨.resourceBook, bookBefore⟩
       ⟨.resourceBook, bookAfter⟩] ++ authorityWrites

def PhysicalPostLaw (deployment : Deployment) (write : DataWrite) : Prop :=
  match (LifecycleImage.codec Registry).decode write.canonicalPostBytes with
  | some (.live cell) => CanonicalCellRegistry.CellLaw deployment write.cellId.value cell
  | _ => False

instance physicalPostLawDecidable (deployment : Deployment) (write : DataWrite) :
    Decidable (PhysicalPostLaw deployment write) := by
  unfold PhysicalPostLaw
  split <;> infer_instance

def PinsBound (deployment : Deployment) (pins : FactoryPins) : Prop :=
  pins.factory.value = deployment.factoryId ∧ pins.domain = deployment.domain

instance pinsBoundDecidable (deployment : Deployment) (pins : FactoryPins) :
    Decidable (PinsBound deployment pins) := by unfold PinsBound; infer_instance

/-- The compiler profile comes from the receiver source. Its exact semantic
identity, including field and arithmetic behavior, is the factory's pin. -/
def ProfileBound (profile : PolicyCompilerProfile F) (pins : FactoryPins) : Prop :=
  pins.semantics = profile.semantics ∧ profile.descriptor?.isSome = true

instance profileBoundDecidable (profile : PolicyCompilerProfile F) (pins : FactoryPins) :
    Decidable (ProfileBound profile pins) := by unfold ProfileBound; infer_instance

/-- A creator owns one stable source coordinate within the actual deployment
and compatible runtime. Neither a payload revision nor new observed roots
changes it; those changes must conflict under the same retry identity. -/
def sourceIdentity (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (creator : SubjectId) (nonce : Nat) : Digest :=
  CredentialAuthorityReplay.birthIdentity deployment.domain profile.semantics
    ⟨deployment.factoryId⟩ creator nonce

def IdentityBound (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (descriptor : Descriptor Registry) : Prop :=
  descriptor.transactionId = sourceIdentity profile deployment descriptor.creator descriptor.nonce ∧
    descriptor.authorityNullifier =
      (sourceIdentity profile deployment descriptor.creator descriptor.nonce).value

instance identityBoundDecidable (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (descriptor : Descriptor Registry) : Decidable (IdentityBound profile deployment descriptor) := by
  unfold IdentityBound
  infer_instance

private instance initialPoliciesBoundDecidable (descriptor : Descriptor Registry) :
    Decidable descriptor.InitialPoliciesBound := by
  unfold Descriptor.InitialPoliciesBound
  infer_instance

inductive PreparationReject where
  | deployment
  | compilerProfile
  | identity
  | directory
  | initialPayload
  | initialPolicy
  | factory
  | resourceBook
  | authorityDomain
  | authorityBatch
  | auxiliaryCreates
  | allocation
  | resourceBatch
  | physicalShape
  | finalCellLaw
  deriving DecidableEq, Repr

/-- Every component is obtained from this one restored image and the fixed
production registry. The private constructor prevents a host from supplying
an arbitrary authority snapshot, Book, allocation result or post-state.

This is preparation, not acceptance: no policy authorization has been created.
The upper receiving controller evaluates these exact candidates and retains
all family modes and authorizations before exposing their physical intent. -/
structure PreparedBirth (profile : PolicyCompilerProfile F) (deployment : Deployment) (pins : FactoryPins)
    (durable : Durable) (descriptor : Descriptor Registry) where
  private mk ::
  deploymentValid : deployment.Valid
  pinsBound : PinsBound deployment pins
  profileBound : ProfileBound profile pins
  identityBound : IdentityBound profile deployment descriptor
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  initials : CanonicalCellRegistry.BirthsAdmissible deployment descriptor
  policiesBound : descriptor.InitialPoliciesBound
  factory : ObservedCell deployment directory.directory deployment.factoryId .declaredObject
  book : ObservedCell deployment directory.directory deployment.resourceBookId .resourceBook
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  grants : CredentialAuthorityDomainReceiver.PreparedGrantBatch profile deployment authority descriptor
  auxiliaryExact : descriptor.auxiliaryCreates = grants.auxiliaryCreates
  allocated : Allocated Registry directory.directory descriptor
  resources : CanonicalResourceKernel.AcceptedBatch book.payload descriptor.resourceBatch
  writesUnique : ((planWrites deployment descriptor factory.payload book.payload
    resources.post grants.writes).map DataWrite.cellId).Nodup
  writePreExact : ∀ write ∈ planWrites deployment descriptor factory.payload book.payload
      resources.post grants.writes,
    write.expectedPre = durable.snapshot.model.roots write.cellId
  finalCells : ∀ write ∈ planWrites deployment descriptor factory.payload book.payload
      resources.post grants.writes, PhysicalPostLaw deployment write

private def requirePreparation (condition : Prop) [Decidable condition]
    (reason : PreparationReject) : Except PreparationReject (PLift condition) :=
  if accepted : condition then .ok ⟨accepted⟩ else .error reason

private def fromOption {α : Type} (value : Option α) (reason : PreparationReject) :
    Except PreparationReject α := match value with
  | none => .error reason
  | some result => .ok result

/-- Common old-image preparation for bare and grain-backed births. This ends
before authority edits, so neither route may use newly created grants to
authorize its own source. The existing bare receiver retains its exact check
order and rejection meanings. -/
structure PreparedPreAuthority (profile : PolicyCompilerProfile F)
    (deployment : Deployment) (pins : FactoryPins) (durable : Durable)
    (descriptor : Descriptor Registry) where
  private mk ::
  deploymentValid : deployment.Valid
  pinsBound : PinsBound deployment pins
  profileBound : ProfileBound profile pins
  identityBound : IdentityBound profile deployment descriptor
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  initials : CanonicalCellRegistry.BirthsAdmissible deployment descriptor
  policiesBound : descriptor.InitialPoliciesBound
  factory : ObservedCell deployment directory.directory deployment.factoryId .declaredObject
  book : ObservedCell deployment directory.directory deployment.resourceBookId .resourceBook
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot

def preparePreAuthority (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable) (descriptor : Descriptor Registry) :
    Except PreparationReject (PreparedPreAuthority profile deployment pins durable descriptor) := do
  let valid ← requirePreparation (deployment.Valid ∧ PinsBound deployment pins) .deployment
  let profileBound ← requirePreparation (ProfileBound profile pins) .compilerProfile
  let identityBound ← requirePreparation (IdentityBound profile deployment descriptor) .identity
  let directory ← fromOption (CredentialAuthorityDomainReceiver.loadDirectory durable) .directory
  let initials ← requirePreparation
    (CanonicalCellRegistry.BirthsAdmissible deployment descriptor) .initialPayload
  let policiesBound ← requirePreparation descriptor.InitialPoliciesBound .initialPolicy
  let factory ← fromOption
    (observeCell deployment directory.directory deployment.factoryId .declaredObject) .factory
  let book ← fromOption
    (observeCell deployment directory.directory deployment.resourceBookId .resourceBook) .resourceBook
  let authority ← fromOption
    (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot) .authorityDomain
  .ok ⟨valid.down.1, valid.down.2, profileBound.down, identityBound.down, directory,
    initials.down, policiesBound.down, factory, book, authority⟩

/-- Common post-authority physical checks. The authority route supplies only
its already checked physical writes; allocation, conserved Book application,
old-root equality and final cell law stay identical for both birth modes. -/
structure PreparedPostAuthority {profile : PolicyCompilerProfile F}
    {deployment : Deployment} {pins : FactoryPins} {durable : Durable}
    {descriptor : Descriptor Registry}
    (pre : PreparedPreAuthority profile deployment pins durable descriptor)
    (authorityWrites : List DataWrite) where
  private mk ::
  allocated : Allocated Registry pre.directory.directory descriptor
  resources : CanonicalResourceKernel.AcceptedBatch pre.book.payload descriptor.resourceBatch
  writesUnique : ((planWrites deployment descriptor pre.factory.payload pre.book.payload
    resources.post authorityWrites).map DataWrite.cellId).Nodup
  writePreExact : ∀ write ∈ planWrites deployment descriptor pre.factory.payload pre.book.payload
      resources.post authorityWrites,
    write.expectedPre = durable.snapshot.model.roots write.cellId
  finalCells : ∀ write ∈ planWrites deployment descriptor pre.factory.payload pre.book.payload
      resources.post authorityWrites, PhysicalPostLaw deployment write

def preparePostAuthority {profile : PolicyCompilerProfile F}
    {deployment : Deployment} {pins : FactoryPins} {durable : Durable}
    {descriptor : Descriptor Registry}
    (pre : PreparedPreAuthority profile deployment pins durable descriptor)
    (authorityWrites : List DataWrite) :
    Except PreparationReject (PreparedPostAuthority pre authorityWrites) := do
  let allocated ← match allocate? Registry pre.directory.directory descriptor with
    | .error _ => .error PreparationReject.allocation
    | .ok allocated => .ok allocated
  let admission ← requirePreparation
    (descriptor.resourceBatch.Admission (CanonicalResourceKernel.logicalBook pre.book.payload.logical))
    .resourceBatch
  let resources := CanonicalResourceKernel.AcceptedBatch.ofAdmission admission.down
  let writes := planWrites deployment descriptor pre.factory.payload pre.book.payload
    resources.post authorityWrites
  let shape ← requirePreparation
    ((writes.map DataWrite.cellId).Nodup ∧
      ∀ write ∈ writes, write.expectedPre = durable.snapshot.model.roots write.cellId)
    .physicalShape
  let finalCells ← requirePreparation (∀ write ∈ writes, PhysicalPostLaw deployment write) .finalCellLaw
  .ok ⟨allocated, resources, shape.down.1, shape.down.2, finalCells.down⟩

/-- The actual fail-closed receiving preparation. Even the auxiliary create
list and every final payload are checked before policy evaluation. No step
mutates the source image or installs a prefix of the birth. -/
def prepareBirth (profile : PolicyCompilerProfile F) (deployment : Deployment) (pins : FactoryPins)
    (durable : Durable) (descriptor : Descriptor Registry) :
    Except PreparationReject (PreparedBirth profile deployment pins durable descriptor) := do
  let pre ← preparePreAuthority profile deployment pins durable descriptor
  let grants ← fromOption
    (CredentialAuthorityDomainReceiver.prepareGrantBatch profile deployment
      pre.authority descriptor)
    .authorityBatch
  let aux ← requirePreparation
    (sameCreates descriptor.auxiliaryCreates grants.auxiliaryCreates = true)
    .auxiliaryCreates
  let post ← preparePostAuthority pre grants.writes
  .ok ⟨pre.deploymentValid, pre.pinsBound, pre.profileBound, pre.identityBound,
    pre.directory, pre.initials, pre.policiesBound, pre.factory, pre.book, pre.authority,
    grants, (sameCreates_iff _ _).mp aux.down, post.allocated, post.resources,
    post.writesUnique, post.writePreExact, post.finalCells⟩

/-- Preparation for the composite route retains a single old-image authority
post covering initial grants and both replay markers. `operationMarker` here is
only a preparation coordinate; the receiving source must prove it equals the
canonical signed grain command's marker before any admission or commit. -/
structure PreparedGrainBirth (profile : PolicyCompilerProfile F)
    (deployment : Deployment) (pins : FactoryPins) (durable : Durable)
    (descriptor : Descriptor Registry) (operationMarker : Nat) where
  private mk ::
  pre : PreparedPreAuthority profile deployment pins durable descriptor
  authorityCombined : GrainResourceBirthAuthority.Prepared profile deployment
    pre.authority descriptor operationMarker
  auxiliaryExact : descriptor.auxiliaryCreates = authorityCombined.auxiliaryCreates
  post : PreparedPostAuthority pre authorityCombined.writes

def prepareGrainBirth (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable) (descriptor : Descriptor Registry)
    (operationMarker : Nat) :
    Except PreparationReject
      (PreparedGrainBirth profile deployment pins durable descriptor operationMarker) := do
  let pre ← preparePreAuthority profile deployment pins durable descriptor
  let combined ← fromOption
    (GrainResourceBirthAuthority.prepare profile deployment pre.authority
      descriptor operationMarker) .authorityBatch
  let aux ← requirePreparation
    (sameCreates descriptor.auxiliaryCreates combined.auxiliaryCreates = true)
    .auxiliaryCreates
  let post ← preparePostAuthority pre combined.writes
  .ok ⟨pre, combined, (sameCreates_iff _ _).mp aux.down, post⟩

def PreparedGrainBirth.writes {profile : PolicyCompilerProfile F}
    {deployment : Deployment} {pins : FactoryPins} {durable : Durable}
    {descriptor : Descriptor Registry} {operationMarker : Nat}
    (prepared : PreparedGrainBirth profile deployment pins durable descriptor operationMarker) :
    List DataWrite :=
  planWrites deployment descriptor prepared.pre.factory.payload prepared.pre.book.payload
    prepared.post.resources.post prepared.authorityCombined.writes

def PreparedGrainBirth.readGuards {profile : PolicyCompilerProfile F}
    {deployment : Deployment} {pins : FactoryPins} {durable : Durable}
    {descriptor : Descriptor Registry} {operationMarker : Nat}
    (prepared : PreparedGrainBirth profile deployment pins durable descriptor operationMarker) :
    List ReadGuard :=
  prepared.pre.authority.readGuards.filter fun guard =>
    guard.cellId ∉ prepared.writes.map DataWrite.cellId

/-- The user draft has no auxiliary creates; only the initial policy sources are
filled in. The complete descriptor returned here is the one that must be signed. -/
structure PreparedGrainDraft (profile : PolicyCompilerProfile F)
    (deployment : Deployment) (pins : FactoryPins) (durable : Durable)
    (draft : Descriptor Registry) (operationMarker : Nat) where
  private mk ::
  noAuxiliaryInput : draft.auxiliaryCreates = []
  descriptor : Descriptor Registry
  sourceExact : descriptor = { draft with auxiliaryCreates := descriptor.auxiliaryCreates }
  prepared : PreparedGrainBirth profile deployment pins durable descriptor operationMarker

def prepareGrainDraft (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable) (draft : Descriptor Registry)
    (operationMarker : Nat) :
    Except PreparationReject
      (PreparedGrainDraft profile deployment pins durable draft operationMarker) := do
  let empty ← requirePreparation (draft.auxiliaryCreates = []) .auxiliaryCreates
  let authority ← fromOption
    (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot) .authorityDomain
  let combined ← fromOption
    (GrainResourceBirthAuthority.prepare profile deployment authority
      draft operationMarker) .authorityBatch
  let descriptor := { draft with auxiliaryCreates := combined.auxiliaryCreates }
  let prepared ← prepareGrainBirth profile deployment pins durable descriptor operationMarker
  .ok ⟨empty.down, descriptor, rfl, prepared⟩

def PreparedBirth.writes {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) : List DataWrite :=
  planWrites deployment descriptor prepared.factory.payload prepared.book.payload
    prepared.resources.post prepared.grants.writes

def PreparedBirth.readGuards {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) : List ReadGuard :=
  prepared.authority.readGuards.filter fun guard =>
    guard.cellId ∉ prepared.writes.map DataWrite.cellId

def PreparedBirth.oldAuthority {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) : AuthState :=
  prepared.authority.snapshot.authState

theorem PreparedBirth.transaction_identity {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) :
    descriptor.transactionId = sourceIdentity profile deployment descriptor.creator descriptor.nonce :=
  prepared.identityBound.1

theorem PreparedBirth.authority_marker_identity {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) :
    descriptor.authorityNullifier =
      (sourceIdentity profile deployment descriptor.creator descriptor.nonce).value :=
  prepared.identityBound.2

/-- Chosen global journal identifiers never become prepared receiving effects.
This requires no assumption that two different hash inputs have different hashes. -/
theorem no_prepared_of_wrong_transaction {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (wrong : descriptor.transactionId ≠
      sourceIdentity profile deployment descriptor.creator descriptor.nonce) :
    ¬Nonempty (PreparedBirth profile deployment pins durable descriptor) := by
  rintro ⟨prepared⟩
  exact wrong prepared.transaction_identity

theorem no_prepared_of_wrong_marker {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (wrong : descriptor.authorityNullifier ≠
      (sourceIdentity profile deployment descriptor.creator descriptor.nonce).value) :
    ¬Nonempty (PreparedBirth profile deployment pins durable descriptor) := by
  rintro ⟨prepared⟩
  exact wrong prepared.authority_marker_identity

/-- A user draft has no auxiliary creates. Only the source-owned lowering may
fill that field; every other source field remains exactly the draft's value.
The resulting descriptor is the complete object to review, sign and submit. -/
structure PreparedDraft (profile : PolicyCompilerProfile F) (deployment : Deployment) (pins : FactoryPins)
    (durable : Durable) (draft : Descriptor Registry) where
  private mk ::
  noAuxiliaryInput : draft.auxiliaryCreates = []
  descriptor : Descriptor Registry
  sourceExact : descriptor = { draft with auxiliaryCreates := descriptor.auxiliaryCreates }
  prepared : PreparedBirth profile deployment pins durable descriptor

def prepareDraft (profile : PolicyCompilerProfile F) (deployment : Deployment) (pins : FactoryPins)
    (durable : Durable) (draft : Descriptor Registry) :
    Except PreparationReject (PreparedDraft profile deployment pins durable draft) := do
  let empty ← requirePreparation (draft.auxiliaryCreates = []) .auxiliaryCreates
  let authority ← fromOption
    (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot) .authorityDomain
  let grants ← fromOption
    (CredentialAuthorityDomainReceiver.prepareGrantBatch profile deployment authority draft)
    .authorityBatch
  let descriptor := { draft with auxiliaryCreates := grants.auxiliaryCreates }
  let prepared ← prepareBirth profile deployment pins durable descriptor
  .ok ⟨empty.down, descriptor, rfl, prepared⟩

theorem PreparedDraft.user_source_preserved {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {draft : Descriptor Registry}
    (prepared : PreparedDraft profile deployment pins durable draft) :
    prepared.descriptor.births = draft.births ∧
      prepared.descriptor.grants = draft.grants ∧
      prepared.descriptor.initialPolicies = draft.initialPolicies ∧
      prepared.descriptor.funding = draft.funding ∧
      prepared.descriptor.fee = draft.fee ∧
      prepared.descriptor.transactionId = draft.transactionId := by
  rw [prepared.sourceExact]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PreparedBirth.write_roots_bound {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (write : DataWrite) (member : write ∈ prepared.writes) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  rcases List.mem_append.mp member with front | authority
  · rcases List.mem_append.mp front with allocation | native
    · obtain ⟨request, _, rfl⟩ := List.mem_map.mp allocation
      exact birthWrite_root_bound request
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at native
      rcases native with rfl | rfl <;> rfl
  · simp only [CredentialAuthorityDomainReceiver.PreparedGrantBatch.writes,
      CredentialAuthorityDomainReceiver.Loaded.writes, List.mem_singleton] at authority
    subst write
    exact prepared.authority.write_root_bound _

theorem PreparedBirth.readGuards_readonly {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (guard : ReadGuard) (member : guard ∈ prepared.readGuards) :
    guard.cellId ∉ prepared.writes.map DataWrite.cellId :=
  by simpa using (List.mem_filter.mp member).2

theorem PreparedBirth.readGuards_exact {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (guard : ReadGuard) (member : guard ∈ prepared.readGuards) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId :=
  prepared.authority.readGuards_exact guard (List.mem_filter.mp member).1

/-- The authority cell's read is covered: it is written under its old root, or
it remains a read guard. -/
theorem PreparedBirth.authority_reads_covered {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (guard : ReadGuard) (member : guard ∈ prepared.authority.readGuards) :
    guard.cellId ∈ prepared.writes.map DataWrite.cellId ∨ guard ∈ prepared.readGuards := by
  by_cases written : guard.cellId ∈ prepared.writes.map DataWrite.cellId
  · exact Or.inl written
  · exact Or.inr (List.mem_filter.mpr ⟨member, by simpa using written⟩)

theorem PreparedBirth.fresh_before {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (request : CreateRequest (CellId := Nat) Registry)
    (member : request ∈ descriptor.createRequests) :
    durable.snapshot.canonicalBytes ⟨request.cellId⟩ = [] := by
  rw [← prepared.directory.bytes_exact, prepared.allocated.fresh_pre request member]
  rfl

theorem PreparedBirth.authority_post_exact {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) :
    prepared.grants.post =
      ResourceBirthAuthority.post prepared.authority.snapshot.cell descriptor := rfl

/-- The authority cell's one write carries exactly the batch's post, guarded at
the loaded root of that cell. -/
theorem PreparedBirth.authority_write_member {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) :
    prepared.authority.write prepared.grants.post ∈ prepared.writes := by
  simp [PreparedBirth.writes, planWrites, CredentialAuthorityDomainReceiver.PreparedGrantBatch.writes,
    CredentialAuthorityDomainReceiver.Loaded.writes]

/-- Checked source records are actual allocator participants, not staging
receipts or entries in an unrelated in-memory payload store. -/
theorem PreparedBirth.initial_source_member {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (record : PolicyRecord) (member : record ∈ prepared.grants.initialSources.records) :
    CanonicalCellRegistry.policySourceCreate deployment.domain record ∈ descriptor.createRequests := by
  unfold Descriptor.createRequests
  apply List.mem_append_right
  rw [prepared.auxiliaryExact]
  exact List.mem_map.mpr ⟨record, member, rfl⟩

theorem PreparedBirth.initial_source_created {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (record : PolicyRecord) (member : record ∈ prepared.grants.initialSources.records) :
    prepared.allocated.after.slots
        (CanonicalCellRegistry.policySourceCreate deployment.domain record).cellId =
      .present (CanonicalCellRegistry.policySourceCell record) :=
  ResourceBirth.allocate_success_created Registry prepared.directory.directory
    prepared.allocated.after descriptor.createRequests prepared.allocated.accepted _
      (prepared.initial_source_member record member)

/-- The same physical intent that installs the new policy heads contains
each exact source cell. No later payload upload is needed for first use. -/
theorem PreparedBirth.initial_source_write {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (record : PolicyRecord) (member : record ∈ prepared.grants.initialSources.records) :
    birthWrite (CanonicalCellRegistry.policySourceCreate deployment.domain record) ∈ prepared.writes := by
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨_, prepared.initial_source_member record member, rfl⟩

/-- Each submitted initial policy resolves to its exact checked source in
the allocated result. The address equality is decoder evidence, not a free
hash equality interpreted as equality of different source records. -/
theorem PreparedBirth.initial_policy_created {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (initial : InitialPolicy) (member : initial ∈ descriptor.initialPolicies) :
    ∃ record,
      PolicyRecordCodec.decode initial.canonicalBytes = some record ∧
      PolicySourceCell.InitialFacts deployment.domain profile initial record ∧
      prepared.allocated.after.slots (PolicySourceCell.physicalId deployment.domain initial.address) =
        .present (CanonicalCellRegistry.policySourceCell record) := by
  obtain ⟨record, inRecords, decoded, facts⟩ :=
    prepared.grants.initialSources.record_of_member initial member
  have created := prepared.initial_source_created record inRecords
  change prepared.allocated.after.slots
    (PolicySourceCell.physicalId deployment.domain (PolicyRecordCodec.digest record)) = _ at created
  rw [facts.2.2.1] at created
  exact ⟨record, decoded, facts, created⟩

theorem PreparedBirth.user_initial_law {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (item : BirthItem Registry) (member : item ∈ descriptor.births) :
    CanonicalCellRegistry.UserInitial deployment item.create.cellId item.create.cell :=
  prepared.initials item member

theorem PreparedBirth.conserves {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) (asset : Nat) :
    (CanonicalResourceKernel.logicalBook prepared.resources.post.logical).totalAsset asset =
      (CanonicalResourceKernel.logicalBook prepared.book.payload.logical).totalAsset asset :=
  prepared.resources.conserves asset

theorem PreparedBirth.no_user_book {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (item : BirthItem Registry) (member : item ∈ descriptor.births) :
    item.create.cell.kind ≠ .resourceBook := by
  intro forbidden
  have initial := prepared.user_initial_law item member
  cases packed : item.create.cell with
  | mk kind payload =>
      rw [packed] at forbidden initial
      cases forbidden
      exact CanonicalCellRegistry.no_user_book_birth deployment item.create.cellId payload initial

end Concrete

/-! ## Axiom accounting for the source and receiving laws -/

/-- info: 'Minidregg.Kernel.ResourceBirthController.allocation_not_valid_of_used' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.allocation_not_valid_of_used

/-- info: 'Minidregg.Kernel.ResourceBirthController.settlement_no_partial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.settlement_no_partial

/-- info: 'Minidregg.Kernel.ResourceBirthController.allocation_post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.allocation_post_exact

/-- info: 'Minidregg.Kernel.ResourceBirthController.allocation_candidate_physical_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.allocation_candidate_physical_post

/-- info: 'Minidregg.Kernel.ResourceBirthController.no_allocation_mode_of_retired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.no_allocation_mode_of_retired

/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.sameCreates_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.sameCreates_iff

/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedDraft.user_source_preserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedDraft.user_source_preserved

/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.write_roots_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.write_roots_bound

/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.authority_reads_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.authority_reads_covered

/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.fresh_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.fresh_before

/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.authority_post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.authority_post_exact

/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.conserves

/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.no_user_book' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.no_user_book

end Minidregg.Kernel.ResourceBirthController
