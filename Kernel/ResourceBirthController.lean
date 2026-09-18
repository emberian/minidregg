/-
# Kernel.ResourceBirthController -- lifecycle lifting for an accepted joint turn

This is the shared physical projection used by the birth receiving controller.
It combines the existing checked fresh allocator with an existing complete
MultiCellHyperedge. Native cell pre/post values become exact lifecycle images;
native roots are never equated with the outer storage root.

The complete birth application must select its authority and Book families in
source, construct their accepted incidences from the same Descriptor, and bind
all old authority dependencies. The generic lift below does not manufacture
those semantic proofs or call a host verdict. In particular, it is not a public
raw-DataIntent endpoint. Sharded authority needs its source-owned materialization
refinement in addition to the one-native-cell/one-physical-cell lift here.
-/
import Compiler.ResourceBirthCodec
import Compiler.CredentialAuthorityDomainReceiver
import Theory.ResourceBirthAuthority
import Kernel.CanonicalResourceEffect
import Kernel.MultiCellHyperedge
import Kernel.DurableDataIntent

namespace Minidregg.Kernel.ResourceBirthController

open Minidregg.Theory
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

def allocationPatch {registry : TypeRegistry Digest}
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry) :
    CellState.Patch (LifecycleSlot.schema registry) Digest where
  expectedPreRoot := (allocationPre before request).root
  fieldWrites := [{ field := (), value := some (some request.cell) }]
  resourceWrites := []
  fieldFootprint := {()}
  resourceFootprint := ∅

private theorem validatedExact {S : CellState.Schema}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {pre : CellState.Materialized M}
    (patch : CellState.Patch S Digest)
    (rootExact : patch.expectedPreRoot = pre.root)
    (fieldsExact : patch.fieldFootprint = patch.namedFields)
    (resourcesExact : patch.resourceFootprint = patch.namedResources) :
    CellState.ValidatedPatch M pre patch := by
  generalize checked : CellState.validate M pre patch = result
  cases result with
  | accepted validated => exact validated
  | rejected reason =>
      simp [CellState.validate, rootExact, fieldsExact, resourcesExact] at checked

theorem allocationValidated {registry : TypeRegistry Digest}
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry) :
    CellState.ValidatedPatch (LifecycleSlot.materializer registry)
      (allocationPre before request) (allocationPatch before request) := by
  exact validatedExact (allocationPatch before request) rfl rfl rfl

theorem allocation_post_exact {registry : TypeRegistry Digest}
    (before : Directory Nat registry) (request : CreateRequest (CellId := Nat) registry) :
    (allocationValidated before request).apply.logical =
      LifecycleSlot.state registry (.live request.cell) := by
  calc
    _ = LifecycleSlot.state registry (LifecycleSlot.image registry
        (allocationValidated before request).apply.logical) :=
      (LifecycleSlot.state_image registry _).symm
    _ = _ := by
      congr 1

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
    SemanticEffectFamily (LifecycleSlot.schema registry) (LifecycleSlot.materializer registry)
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
  patch := fun _ _ => allocationPatch before request
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
  validated := allocationValidated before request
  postcondition := allocation_post_exact before request

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
    (allocationValidated before request).apply.logical = _
  rw [allocation_post_exact]
  exact LifecycleSlot.bytes_exact registry (.live request.cell)

theorem no_allocation_mode_of_retired {registry : TypeRegistry Digest}
    {before : Directory Nat registry} {request : CreateRequest (CellId := Nat) registry}
    {descriptor : Descriptor registry} (used : request.cellId ∈ before.used) :
    ¬AllocationMode before request descriptor := by
  rintro ⟨member, after, accepted⟩
  exact ResourceBirth.allocate_success_fresh registry before after descriptor.createRequests
    accepted request member used

/-! ## An existing native MultiCellHyperedge, packed without schema erasure -/

/-- The receiving deployment fixes the schema and authority view of each
native incidence. Its physical identity is the existing natural resource id
in the common Digest carrier, rather than a second independently supplied id. -/
structure Layout (registry : TypeRegistry Digest) (count : Nat) where
  kind : Fin count -> registry.Kind
  fieldEq : (i : Fin count) -> DecidableEq (registry.schema (kind i)).Field
  resourceEq : (i : Fin count) -> DecidableEq (registry.schema (kind i)).Resource
  portal : Fin count -> Portal
  projectAuthority : (i : Fin count) ->
    CellState.LogicalState (registry.schema (kind i)) -> AuthState
  cellId : Fin count -> Nat

def Layout.cells {registry : TypeRegistry Digest} {count : Nat}
    (layout : Layout registry count) : MultiCellHyperedge.CellFamily (Fin count) where
  schema i := registry.schema (layout.kind i)
  fieldDecidableEq := layout.fieldEq
  resourceDecidableEq := layout.resourceEq
  materializer i := registry.materializer (layout.kind i)
  portal := layout.portal
  projectAuthority := layout.projectAuthority
  cellId i := ⟨layout.cellId i⟩

local instance layoutFieldEq {registry : TypeRegistry Digest} {count : Nat}
    (layout : Layout registry count) (i : Fin count) :
    DecidableEq (layout.cells.schema i).Field := layout.fieldEq i

local instance layoutResourceEq {registry : TypeRegistry Digest} {count : Nat}
    (layout : Layout registry count) (i : Fin count) :
    DecidableEq (layout.cells.schema i).Resource := layout.resourceEq i

def nativePre {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count}
    (declaration : MultiCellHyperedge.Declaration layout.cells)
    (i : Fin count) : PackedCell registry :=
  ⟨layout.kind i, declaration.pre i⟩

def nativePost {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count}
    (declaration : MultiCellHyperedge.Declaration layout.cells)
    (accepted : declaration.AcceptedLegs) (i : Fin count) : PackedCell registry :=
  ⟨layout.kind i, declaration.post accepted i⟩

def nativeWrite {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count}
    (declaration : MultiCellHyperedge.Declaration layout.cells)
    (accepted : declaration.AcceptedLegs) (i : Fin count) : DataWrite where
  cellId := ⟨layout.cellId i⟩
  expectedPre := physicalRoot (.live (nativePre declaration i))
  exactPost := physicalRoot (.live (nativePost declaration accepted i))
  canonicalPostBytes := LifecycleImage.bytes registry (.live (nativePost declaration accepted i))

def nativeWrites {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count}
    (declaration : MultiCellHyperedge.Declaration layout.cells)
    (accepted : declaration.AcceptedLegs) : List DataWrite :=
  (List.finRange count).map (nativeWrite declaration accepted)

theorem nativeWrite_root_bound {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count}
    (declaration : MultiCellHyperedge.Declaration layout.cells)
    (accepted : declaration.AcceptedLegs) (i : Fin count) :
    rootBytes (nativeWrite declaration accepted i).canonicalPostBytes =
      (nativeWrite declaration accepted i).exactPost := rfl

/-- The semantic post is the accepted patch's actual post, never caller bytes. -/
theorem nativePost_exact {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count}
    (declaration : MultiCellHyperedge.Declaration layout.cells)
    (accepted : declaration.AcceptedLegs) (i : Fin count) :
    (nativePost declaration accepted i).payload = (accepted i).validated.apply := rfl

def NativeObserved {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count} (before : Directory Nat registry)
    (declaration : MultiCellHyperedge.Declaration layout.cells) : Prop :=
  ∀ i, before.slots (layout.cellId i) = .present (nativePre declaration i)

theorem native_observed_outer_pre {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count} {before : Directory Nat registry}
    {declaration : MultiCellHyperedge.Declaration layout.cells}
    (observed : NativeObserved before declaration)
    (accepted : declaration.AcceptedLegs) (i : Fin count) :
    (nativeWrite declaration accepted i).expectedPre =
      physicalRoot (LifecycleImage.view registry before (layout.cellId i)) := by
  rw [(LifecycleImage.view_live_iff registry before (layout.cellId i)
    (nativePre declaration i)).mpr (observed i)]
  rfl

/-- Actual initial absence and actual observed presence make an allocator/native
write alias impossible. No digest injectivity assumption is involved. -/
theorem allocated_native_disjoint {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count} {before : Directory Nat registry}
    {descriptor : Descriptor registry}
    (allocated : Allocated registry before descriptor)
    {declaration : MultiCellHyperedge.Declaration layout.cells}
    (observed : NativeObserved before declaration)
    (request : CreateRequest (CellId := Nat) registry)
    (member : request ∈ descriptor.createRequests) (i : Fin count) :
    request.cellId ≠ layout.cellId i := by
  intro same
  have fresh := ResourceBirth.allocate_success_fresh registry before allocated.after
    descriptor.createRequests allocated.accepted request member
  apply fresh
  rw [same]
  exact before.present_used (observed i)

/-! ## One existing durable intent, with exact outer bytes -/

def readGuard {registry : TypeRegistry Digest}
    (before : Directory Nat registry) (cellId : Nat) : ReadGuard where
  cellId := ⟨cellId⟩
  expectedRoot := physicalRoot (LifecycleImage.view registry before cellId)

/-- Source-owned projection of all native eager nullifiers. Event payload is
always the complete birth descriptor and cannot be replaced by a host string.
The quote is the receiver's metering charge, separate from the actual Book fee. -/
structure SettlementConfig (registry : TypeRegistry Digest) (Nullifier : Type) where
  encoding : SourceEncoding registry
  eventDomain : Digest
  nullifier : Nullifier -> StableNullifier
  charge : Descriptor registry -> Charge

def birthEvent {registry : TypeRegistry Digest} {Nullifier : Type}
    (config : SettlementConfig registry Nullifier) (descriptor : Descriptor registry) : StableEvent where
  codecVersion := 1
  domain := config.eventDomain
  eventId := config.encoding.effectsDigest descriptor
  canonicalBytes := config.encoding.codec.encode descriptor

def combinedWrites {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count} (descriptor : Descriptor registry)
    (declaration : MultiCellHyperedge.Declaration layout.cells)
    (accepted : declaration.AcceptedLegs) : List DataWrite :=
  allocationWrites descriptor ++ nativeWrites declaration accepted

/-- Canonical executable incidence order for the existing joint-nullifier
carrier. This avoids extracting the noncomputable `Finset.toList` order used
by the abstract hyperedge without dropping or adding eager nullifiers. -/
def nativeNullifiers {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count}
    {declaration : MultiCellHyperedge.Declaration layout.cells}
    (accepted : declaration.AcceptedLegs) :
    List (MultiCellHyperedge.JointNullifier accepted) :=
  (List.finRange count).filterMap fun i =>
    match (declaration.legs i).family.nullifier
      (declaration.legs i).declaration (declaration.legs i).outcome with
    | none => none
    | some nullifier => some ⟨i, nullifier⟩

theorem nativeNullifiers_retains {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count}
    {declaration : MultiCellHyperedge.Declaration layout.cells}
    (accepted : declaration.AcceptedLegs) (i : Fin count)
    (nullifier : (declaration.legs i).Nullifier)
    (eager : (declaration.legs i).family.nullifier
      (declaration.legs i).declaration (declaration.legs i).outcome = some nullifier) :
    (⟨i, nullifier⟩ : MultiCellHyperedge.JointNullifier accepted) ∈
      nativeNullifiers accepted := by
  apply List.mem_filterMap.mpr
  exact ⟨i, by simp, by rw [eager]; rfl⟩

theorem combinedWrites_bound {registry : TypeRegistry Digest} {count : Nat}
    {layout : Layout registry count} (descriptor : Descriptor registry)
    (declaration : MultiCellHyperedge.Declaration layout.cells)
    (accepted : declaration.AcceptedLegs) :
    ∀ write ∈ combinedWrites descriptor declaration accepted,
      rootBytes write.canonicalPostBytes = write.exactPost := by
  intro write member
  rcases List.mem_append.mp member with born | native
  · obtain ⟨request, _, rfl⟩ := List.mem_map.mp born
    exact birthWrite_root_bound request
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp native
    exact nativeWrite_root_bound declaration accepted i

/-- This adapter receives a complete existing hyperedge commit and a checked
allocation. The caller is the source-owned birth family join, not an untrusted
wire handler. It retains every accepted native nullifier and exact descriptor
bytes in the same DataIntent that carries all post bytes.

Read dependency completeness and sharded materialization are properties of
that source join; this generic single-cell projection cannot invent them. -/
def ofAllocatedHyperedge
    {registry : TypeRegistry Digest} {count : Nat} {layout : Layout registry count}
    {before : Directory Nat registry} {descriptor : Descriptor registry}
    (_allocated : Allocated registry before descriptor)
    {declaration : MultiCellHyperedge.Declaration layout.cells}
    {accepted : declaration.AcceptedLegs}
    {law : MultiCellHyperedge.ResourceLaw declaration Nat Int}
    {boundary : MultiCellHyperedge.HandlerBoundary declaration}
    (_commit : MultiCellHyperedge.Commit law accepted boundary)
    (_observed : NativeObserved before declaration)
    (_turnIdBound : declaration.header.turnId = descriptor.transactionId)
    (config : SettlementConfig registry (MultiCellHyperedge.JointNullifier accepted))
    (_effectsBound : ∀ i, (declaration.legs i).request.effectsDigest =
      config.encoding.effectsDigest descriptor)
    (readIds : List Nat)
    (readOnly : ∀ id ∈ readIds,
      (⟨id⟩ : Digest) ∉ (combinedWrites descriptor declaration accepted).map DataWrite.cellId) :
    DataIntent rootBytes where
  transactionId := descriptor.transactionId
  writes := combinedWrites descriptor declaration accepted
  readGuards := readIds.map (readGuard before)
  nullifiers := (nativeNullifiers accepted).map config.nullifier
  exactCharge := config.charge descriptor
  event := birthEvent config descriptor
  postRootsBound := combinedWrites_bound descriptor declaration accepted
  guardsReadOnly := by
    intro guard member
    obtain ⟨identifier, inReads, rfl⟩ := List.mem_map.mp member
    exact readOnly identifier inReads

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
the authority lowering emits only existing shards and its existing catalogue;
the pinned Book emits one final ordered batch result. -/
def planWrites (deployment : Deployment) (descriptor : Descriptor Registry)
    (factory : CellState.Materialized Compiler.DeclaredEffectPageMaterializer.materializer)
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

private instance initialPoliciesBoundDecidable (descriptor : Descriptor Registry) :
    Decidable descriptor.InitialPoliciesBound := by
  unfold Descriptor.InitialPoliciesBound
  infer_instance

inductive PreparationReject where
  | deployment
  | compilerProfile
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
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  initials : CanonicalCellRegistry.BirthsAdmissible deployment descriptor
  policiesBound : descriptor.InitialPoliciesBound
  factory : ObservedCell deployment directory.directory deployment.factoryId .declaredObject
  book : ObservedCell deployment directory.directory deployment.resourceBookId .resourceBook
  authority : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot
  grants : CredentialAuthorityDomainReceiver.PreparedGrantBatch profile deployment directory authority descriptor
  auxiliaryExact : descriptor.auxiliaryCreates = grants.auxiliaryCreates
  allocated : Allocated Registry directory.directory descriptor
  resources : CanonicalResourceKernel.AcceptedBatch book.payload descriptor.resourceBatch
  writesUnique : ((planWrites deployment descriptor factory.payload book.payload
    resources.post grants.physical.writes).map DataWrite.cellId).Nodup
  writePreExact : ∀ write ∈ planWrites deployment descriptor factory.payload book.payload
      resources.post grants.physical.writes,
    write.expectedPre = durable.snapshot.model.roots write.cellId
  finalCells : ∀ write ∈ planWrites deployment descriptor factory.payload book.payload
      resources.post grants.physical.writes, PhysicalPostLaw deployment write

private def requirePreparation (condition : Prop) [Decidable condition]
    (reason : PreparationReject) : Except PreparationReject (PLift condition) :=
  if accepted : condition then .ok ⟨accepted⟩ else .error reason

private def fromOption {α : Type} (value : Option α) (reason : PreparationReject) :
    Except PreparationReject α := match value with
  | none => .error reason
  | some result => .ok result

/-- The actual fail-closed receiving preparation. Even the auxiliary create
list and every final payload are checked before policy evaluation. No step
mutates the source image or installs a prefix of the birth. -/
def prepareBirth (profile : PolicyCompilerProfile F) (deployment : Deployment) (pins : FactoryPins)
    (durable : Durable) (descriptor : Descriptor Registry) :
    Except PreparationReject (PreparedBirth profile deployment pins durable descriptor) := do
  let valid ← requirePreparation (deployment.Valid ∧ PinsBound deployment pins) .deployment
  let profileBound ← requirePreparation (ProfileBound profile pins) .compilerProfile
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
  let grants ← fromOption
    (CredentialAuthorityDomainReceiver.prepareGrantBatch profile deployment directory authority descriptor)
    .authorityBatch
  let aux ← requirePreparation
    (sameCreates descriptor.auxiliaryCreates grants.auxiliaryCreates = true)
    .auxiliaryCreates
  let allocated ← match allocate? Registry directory.directory descriptor with
    | .error _ => .error PreparationReject.allocation
    | .ok allocated => .ok allocated
  let admission ← requirePreparation
    (descriptor.resourceBatch.Admission (CanonicalResourceKernel.logicalBook book.payload.logical))
    .resourceBatch
  let resources := CanonicalResourceKernel.AcceptedBatch.ofAdmission admission.down
  let writes := planWrites deployment descriptor factory.payload book.payload
    resources.post grants.physical.writes
  let shape ← requirePreparation
    ((writes.map DataWrite.cellId).Nodup ∧
      ∀ write ∈ writes, write.expectedPre = durable.snapshot.model.roots write.cellId)
    .physicalShape
  let finalCells ← requirePreparation (∀ write ∈ writes, PhysicalPostLaw deployment write) .finalCellLaw
  .ok ⟨valid.down.1, valid.down.2, profileBound.down, directory, initials.down,
    policiesBound.down, factory, book, authority,
    grants, (sameCreates_iff _ _).mp aux.down, allocated, resources,
    shape.down.1, shape.down.2, finalCells.down⟩

def PreparedBirth.writes {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) : List DataWrite :=
  planWrites deployment descriptor prepared.factory.payload prepared.book.payload
    prepared.resources.post prepared.grants.physical.writes

def PreparedBirth.readGuards {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) : List ReadGuard :=
  CredentialAuthorityDomainReceiver.readonlyGuards prepared.grants.physical.readGuards prepared.writes

def PreparedBirth.oldAuthority {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor) : AuthState :=
  prepared.authority.snapshot.authState

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
  let directory ← fromOption (CredentialAuthorityDomainReceiver.loadDirectory durable) .directory
  let authority ← fromOption
    (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot) .authorityDomain
  let grants ← fromOption
    (CredentialAuthorityDomainReceiver.prepareGrantBatch profile deployment directory authority draft)
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
  · exact CredentialAuthorityDomainReceiver.planWrites_roots_bound
      deployment.authorityAnchor durable.snapshot prepared.authority.snapshot.catalogue
      prepared.grants.prepared.postPages prepared.grants.physical.placement write authority

theorem PreparedBirth.readGuards_readonly {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (guard : ReadGuard) (member : guard ∈ prepared.readGuards) :
    guard.cellId ∉ prepared.writes.map DataWrite.cellId :=
  of_decide_eq_true (List.mem_filter.mp member).2

theorem PreparedBirth.readGuards_exact {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (guard : ReadGuard) (member : guard ∈ prepared.readGuards) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId :=
  prepared.grants.physical.readGuards_exact guard (List.mem_filter.mp member).1

/-- Every originally read authority shard and the catalogue remain guarded:
a changed cell carries its old root in its unique write; an unchanged one
remains a read guard. Newly allocated shards occur only in allocation writes. -/
theorem PreparedBirth.authority_reads_covered {deployment : Deployment} {pins : FactoryPins}
    {durable : Durable} {descriptor : Descriptor Registry}
    (prepared : PreparedBirth profile deployment pins durable descriptor)
    (guard : ReadGuard) (member : guard ∈ prepared.authority.readGuards) :
    guard.cellId ∈ prepared.writes.map DataWrite.cellId ∨ guard ∈ prepared.readGuards := by
  rcases prepared.grants.physical.every_read_covered guard member with written | readonly
  · exact Or.inl (by
      simp only [PreparedBirth.writes, planWrites, List.map_append, List.mem_append]
      exact Or.inr written)
  · by_cases written : guard.cellId ∈ prepared.writes.map DataWrite.cellId
    · exact Or.inl written
    · exact Or.inr (List.mem_filter.mpr ⟨readonly, by simpa using written⟩)

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
    prepared.grants.physical.post.cell =
      ResourceBirthAuthority.post prepared.authority.snapshot.cell descriptor :=
  prepared.grants.post_exact

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
  exact List.mem_append_left _ (List.mem_map.mpr ⟨record, member, rfl⟩)

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

/-- info: 'Minidregg.Kernel.ResourceBirthController.allocated_native_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.allocated_native_disjoint

/-- info: 'Minidregg.Kernel.ResourceBirthController.nativeNullifiers_retains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.nativeNullifiers_retains

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
