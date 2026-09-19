/-
# Theory.ResourceBirth -- atomic fresh allocation for a resource birth

The lifecycle authority is `CellRegistry.create`: actual absence, permanent
identifier freshness, and the exact absent-slot root. This module sequences
that existing operation without exposing a partially created directory on a
failure. It introduces no alternative directory or persistence model.

Statement-first contract for this component:
* success retains every requested exact typed payload, changes no other slot,
  and adds exactly the requested identifiers to the permanent allocation set;
* accepted identifiers were all fresh in the original directory and distinct;
* rejection exposes the original directory, including on a failed later item;
* fresh, distinct, correctly rooted requests supply the positive pole.

This is the allocation component of resource birth, not the complete birth
admission. Owner/participant authority, the conserved creation payment, and
the exact physical transaction must join this component in the existing
`MultiCellHyperedge`/`DurableDataIntent` consumer. No semantic or durable
completion claim follows merely from this allocator succeeding.
-/
import Theory.CellSlot
import Theory.CanonicalResourceKernel

namespace Minidregg.Theory.ResourceBirth

open Minidregg.Theory.CellRegistry

set_option autoImplicit false

universe uRoot uCell

variable {Root : Type uRoot} {CellId : Type uCell}
variable [DecidableEq Root] [DecidableEq CellId]
variable (registry : TypeRegistry Root)

/-- A list of births runs the existing checked lifecycle operation in order.
An error retains no intermediate directory in the return type. -/
def allocate (before : Directory CellId registry) :
    List (CreateRequest (CellId := CellId) registry) ->
      Except CellRegistry.RejectReason (Directory CellId registry)
  | [] => .ok before
  | request :: rest =>
      match CellRegistry.create registry before request with
      | .error reason => .error reason
      | .ok next => allocate next rest

/-- Exact candidate post used in specifications. Admission still occurs only
through `allocate`, which calls `CellRegistry.create` at every step. -/
def inserted (before : Directory CellId registry) :
    List (CreateRequest (CellId := CellId) registry) -> Directory CellId registry
  | [] => before
  | request :: rest =>
      inserted (Directory.insert registry before request.cellId request.cell) rest

/-- An outcome exposes one complete result or the original directory. -/
def logicalPost (before : Directory CellId registry) :
    Except CellRegistry.RejectReason (Directory CellId registry) ->
      Directory CellId registry
  | .ok after => after
  | .error _ => before

omit [DecidableEq Root] in
@[simp] theorem rejected_atomic (before : Directory CellId registry)
    (reason : CellRegistry.RejectReason) :
    logicalPost registry before (.error reason) = before := rfl

/-- Extract the actual checks from the sole single-create executor. No root
injectivity premise turns a root comparison into absence or freshness. -/
theorem create_success_iff
    (before after : Directory CellId registry)
    (request : CreateRequest (CellId := CellId) registry) :
    CellRegistry.create registry before request = .ok after ↔
      before.slots request.cellId = .absent ∧
      request.cellId ∉ before.used ∧
      request.expectedPreRoot = CellSlot.root registry .absent ∧
      after = Directory.insert registry before request.cellId request.cell := by
  cases slot : before.slots request.cellId with
  | absent =>
      by_cases used : request.cellId ∈ before.used
      · simp [CellRegistry.create, slot, used]
      · by_cases root : request.expectedPreRoot = CellSlot.root registry .absent
        · simp [CellRegistry.create, slot, used, root, eq_comm]
        · have root' : request.expectedPreRoot ≠
              registry.rootBytes ((CellSlot.codec registry).encode .absent) := root
          simp [CellRegistry.create, slot, used, root']
  | present cell => simp [CellRegistry.create, slot]

theorem allocate_success_post
    (before after : Directory CellId registry)
    (requests : List (CreateRequest (CellId := CellId) registry))
    (success : allocate registry before requests = .ok after) :
    after = inserted registry before requests := by
  induction requests generalizing before with
  | nil => exact (Except.ok.inj success).symm
  | cons request rest induction =>
      simp only [allocate] at success
      cases head : CellRegistry.create registry before request with
      | error reason => simp [head] at success
      | ok next =>
          have checks := (create_success_iff registry before next request).mp head
          have tail := induction next (by simpa [head] using success)
          simpa [inserted, checks.2.2.2] using tail

/-- Permanent allocation grows by exactly the request identifiers. -/
theorem allocate_success_used
    (before after : Directory CellId registry)
    (requests : List (CreateRequest (CellId := CellId) registry))
    (success : allocate registry before requests = .ok after) :
    after.used = before.used ∪ (requests.map CreateRequest.cellId).toFinset := by
  induction requests generalizing before with
  | nil =>
      have same := Except.ok.inj success
      subst after
      simp
  | cons request rest induction =>
      simp only [allocate] at success
      cases head : CellRegistry.create registry before request with
      | error reason => simp [head] at success
      | ok next =>
          have checks := (create_success_iff registry before next request).mp head
          have tail := induction next (by simpa [head] using success)
          rw [tail, checks.2.2.2]
          ext cellId
          simp [Directory.insert]

/-- An accepted birth cannot change another logical slot. -/
theorem allocate_frame
    (before after : Directory CellId registry)
    (requests : List (CreateRequest (CellId := CellId) registry))
    (success : allocate registry before requests = .ok after)
    (cellId : CellId)
    (outside : cellId ∉ requests.map CreateRequest.cellId) :
    after.slots cellId = before.slots cellId := by
  induction requests generalizing before with
  | nil =>
      have same := Except.ok.inj success
      subst after
      rfl
  | cons request rest induction =>
      simp only [List.map_cons, List.mem_cons, not_or] at outside
      simp only [allocate] at success
      cases head : CellRegistry.create registry before request with
      | error reason => simp [head] at success
      | ok next =>
          have checks := (create_success_iff registry before next request).mp head
          rw [induction next (by simpa [head] using success) outside.2,
            checks.2.2.2]
          simp [Directory.insert, Function.update, outside.1]

/-- Every accepted identifier was unused before the whole batch began. -/
theorem allocate_success_fresh
    (before after : Directory CellId registry)
    (requests : List (CreateRequest (CellId := CellId) registry))
    (success : allocate registry before requests = .ok after) :
    ∀ request ∈ requests, request.cellId ∉ before.used := by
  induction requests generalizing before with
  | nil => simp
  | cons request rest induction =>
      simp only [allocate] at success
      cases head : CellRegistry.create registry before request with
      | error reason => simp [head] at success
      | ok next =>
          have checks := (create_success_iff registry before next request).mp head
          have tail := induction next (by simpa [head] using success)
          intro candidate member
          rcases List.mem_cons.mp member with rfl | inRest
          · exact checks.2.1
          · have fresh := tail candidate inRest
            rw [checks.2.2.2] at fresh
            simp only [Directory.insert, Finset.mem_union, not_or] at fresh
            exact fresh.1

/-- Permanent freshness also prevents a duplicate identifier inside a batch. -/
theorem allocate_success_distinct
    (before after : Directory CellId registry)
    (requests : List (CreateRequest (CellId := CellId) registry))
    (success : allocate registry before requests = .ok after) :
    (requests.map CreateRequest.cellId).Nodup := by
  induction requests generalizing before with
  | nil => simp
  | cons request rest induction =>
      simp only [allocate] at success
      cases head : CellRegistry.create registry before request with
      | error reason => simp [head] at success
      | ok next =>
          have checks := (create_success_iff registry before next request).mp head
          have tailSuccess : allocate registry next rest = .ok after := by
            simpa [head] using success
          have tailFresh := allocate_success_fresh registry next after rest tailSuccess
          refine List.nodup_cons.mpr ⟨?_, induction next tailSuccess⟩
          intro member
          obtain ⟨candidate, inRest, same⟩ := List.mem_map.mp member
          have fresh := tailFresh candidate inRest
          apply fresh
          rw [same, checks.2.2.2]
          simp [Directory.insert]

/-- Each requested exact typed payload survives the complete accepted batch. -/
theorem allocate_success_created
    (before after : Directory CellId registry)
    (requests : List (CreateRequest (CellId := CellId) registry))
    (success : allocate registry before requests = .ok after) :
    ∀ request ∈ requests, after.slots request.cellId = .present request.cell := by
  have distinct := allocate_success_distinct registry before after requests success
  induction requests generalizing before with
  | nil => simp
  | cons request rest induction =>
      have distinctRest := List.nodup_cons.mp distinct
      simp only [allocate] at success
      cases head : CellRegistry.create registry before request with
      | error reason => simp [head] at success
      | ok next =>
          have checks := (create_success_iff registry before next request).mp head
          have tailSuccess : allocate registry next rest = .ok after := by
            simpa [head] using success
          intro candidate member
          rcases List.mem_cons.mp member with rfl | inRest
          · rw [allocate_frame registry next after rest tailSuccess
              candidate.cellId distinctRest.1, checks.2.2.2]
            simp
          · exact induction next tailSuccess distinctRest.2 candidate inRest

/-- The complete positive pole: checks against one initial directory suffice
for a distinct fresh batch, and the returned post is the exact insertion fold.
Intermediate validation is still performed by the existing create operation. -/
theorem allocate_of_fresh
    (before : Directory CellId registry)
    (requests : List (CreateRequest (CellId := CellId) registry))
    (distinct : (requests.map CreateRequest.cellId).Nodup)
    (fresh : ∀ request ∈ requests,
      before.slots request.cellId = .absent ∧ request.cellId ∉ before.used)
    (roots : ∀ request ∈ requests,
      request.expectedPreRoot = CellSlot.root registry .absent) :
    allocate registry before requests = .ok (inserted registry before requests) := by
  induction requests generalizing before with
  | nil => rfl
  | cons request rest induction =>
      have headFresh := fresh request (by simp)
      have headRoot := roots request (by simp)
      have distinctParts := List.nodup_cons.mp distinct
      have nextFresh : ∀ candidate ∈ rest,
          (Directory.insert registry before request.cellId request.cell).slots
              candidate.cellId = .absent ∧
          candidate.cellId ∉
            (Directory.insert registry before request.cellId request.cell).used := by
        intro candidate member
        have wasFresh := fresh candidate (by simp [member])
        have different : candidate.cellId ≠ request.cellId := by
          intro same
          apply distinctParts.1
          exact List.mem_map.mpr ⟨candidate, member, same⟩
        constructor
        · simpa [Directory.insert, Function.update, different] using wasFresh.1
        · simp [Directory.insert, wasFresh.2, different]
      have nextRoots : ∀ candidate ∈ rest,
          candidate.expectedPreRoot = CellSlot.root registry .absent := by
        intro candidate member
        exact roots candidate (by simp [member])
      simp only [allocate,
        CellRegistry.create_of_fresh registry before request
          headFresh.1 headFresh.2 headRoot, inserted]
      exact induction _ distinctParts.2 nextFresh nextRoots

/-- Failure on any item exposes the initial directory, not an allocated prefix. -/
theorem allocate_failure_atomic
    (before : Directory CellId registry)
    (requests : List (CreateRequest (CellId := CellId) registry))
    (reason : CellRegistry.RejectReason)
    (failed : allocate registry before requests = .error reason) :
    logicalPost registry before (allocate registry before requests) = before := by
  rw [failed]
  rfl

/-- A real heterogeneous payload can be born from the fresh empty directory.
No test-only permissive allocator or assumed successful run is used. -/
theorem empty_birth_succeeds (cellId : CellId) (cell : PackedCell registry) :
    allocate registry (Directory.empty registry)
      [{ cellId := cellId
         expectedPreRoot := CellSlot.root registry .absent
         cell := cell }] =
      .ok (Directory.insert registry (Directory.empty registry) cellId cell) := by
  apply allocate_of_fresh
  · simp
  · intro request member
    simp only [List.mem_singleton] at member
    subst request
    simp
  · intro request member
    simp only [List.mem_singleton] at member
    subst request
    rfl

/-- A second birth with the same identifier rejects the entire batch even
though the first internal create succeeded. The caller observes no prefix. -/
theorem duplicate_birth_refused
    (before : Directory CellId registry)
    (first second : CreateRequest (CellId := CellId) registry)
    (sameId : second.cellId = first.cellId)
    (absent : before.slots first.cellId = .absent)
    (fresh : first.cellId ∉ before.used)
    (root : first.expectedPreRoot = CellSlot.root registry .absent) :
    allocate registry before [first, second] =
      .error CellRegistry.RejectReason.duplicateCreate := by
  rw [allocate, CellRegistry.create_of_fresh registry before first absent fresh root]
  simp [allocate, CellRegistry.create, Directory.insert, sameId]

/-- Retirement remains permanent inside the batch allocator. -/
theorem retired_birth_refused
    (before : Directory CellId registry)
    (first retry : CreateRequest (CellId := CellId) registry)
    (sameId : retry.cellId = first.cellId) :
    allocate registry
      (Directory.retire registry
        (Directory.insert registry before first.cellId first.cell) first.cellId)
      [retry] = .error CellRegistry.RejectReason.retiredIdentifier := by
  rw [allocate, CellRegistry.recreate_after_retire_rejected
    registry before first retry sameId]

end Minidregg.Theory.ResourceBirth

namespace Minidregg.Theory.ResourceBirth

open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

/-! ## One complete descriptor and its derived resource batch -/

/-- A birth's kind is checked against the pinned schema catalog by the
receiving controller. The owner belongs to this exact created identity. -/
structure BirthItem (registry : TypeRegistry Digest) where
  create : CreateRequest (CellId := Nat) registry
  resourceKind : ResourceKind
  owner : SubjectId

/-- Full canonical capability content, not a grant bit or host permissions map.
The authority adapter validates and installs these exact stored capabilities. -/
structure AuthorityGrant where
  kind : ResourceKind
  capability : StoredCapability kind

/-- Candidate-independent initial policy source. The compiler must decode
these exact bytes as its existing canonical policy record, check the content
address and source metadata, and preserve them durably in the same birth.
The authority transition installs generation zero and source revision zero; no candidate AST enters
the Theory import boundary. -/
structure InitialPolicy where
  policyId : PolicyId
  address : Digest
  canonicalBytes : List UInt8
  deriving DecidableEq, Repr

structure InitialFunding where
  source : CanonicalResourceKernel.AccountId
  destination : CanonicalResourceKernel.AccountId
  asset : CanonicalResourceKernel.AssetId
  amount : Nat
  deriving DecidableEq, Repr

def InitialFunding.operation (funding : InitialFunding) :
    CanonicalResourceKernel.Operation :=
  .transfer funding.source funding.destination funding.asset funding.amount

/-- The creation payment is an actual conserved fee operation. A separate
metering quote cannot substitute for the debit and collector credit. -/
structure CreationFee where
  payer : CanonicalResourceKernel.AccountId
  collector : CanonicalResourceKernel.AccountId
  asset : CanonicalResourceKernel.AssetId
  amount : Nat
  deriving DecidableEq, Repr

def CreationFee.operation (fee : CreationFee) : CanonicalResourceKernel.Operation :=
  .fee fee.payer fee.collector fee.asset fee.amount

/-- Creation pricing uses only source-owned data that precedes the payment.
It does not recursively price the serialization of the fee it is calculating.
The receiving deployment pins the complete tariff in its factory semantics. -/
structure CreationTariff where
  base : Nat
  perBirth : Nat
  perGrant : Nat
  perInitialPayloadByte : Nat
  collector : CanonicalResourceKernel.AccountId
  asset : CanonicalResourceKernel.AssetId
  deriving DecidableEq, Repr

/-- All effects of one proposed birth share this one source descriptor.
Neither grants, initial funding, nor fee may be silently supplied afterward. -/
structure Descriptor (registry : TypeRegistry Digest) where
  factory : ResourceId .object
  creator : SubjectId
  transactionId : Digest
  nonce : Nat
  births : List (BirthItem registry)
  /-- Internal shard/cell allocation is a checked lowering result. The actual
  controller recomputes it from the complete old directory and semantic
  domain update before authorizing these bytes. It is never an unchecked
  extension point of a user-facing birth request. -/
  auxiliaryCreates : List (CreateRequest (CellId := Nat) registry)
  grants : List AuthorityGrant
  initialPolicies : List InitialPolicy := []
  authorityNullifier : Nat
  funding : List InitialFunding
  fee : CreationFee

def Descriptor.createRequests {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : List (CreateRequest (CellId := Nat) registry) :=
  descriptor.births.map BirthItem.create ++ descriptor.auxiliaryCreates

def Descriptor.registeredAccounts {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : List CanonicalResourceKernel.AccountId :=
  descriptor.births.filterMap fun item =>
    match item.resourceKind with
    | .account => some item.create.cellId
    | _ => none

/-- Registration IDs and value movements are projected from the exact birth;
there is no separately supplied resource batch to relabel. -/
def Descriptor.resourceBatch {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : CanonicalResourceKernel.Batch where
  registrations := descriptor.registeredAccounts
  operations := descriptor.funding.map InitialFunding.operation ++
    [descriptor.fee.operation]

def Descriptor.quotedFee {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) (tariff : CreationTariff) : Nat :=
  tariff.base + tariff.perBirth * descriptor.births.length +
    tariff.perGrant * descriptor.grants.length +
    tariff.perInitialPayloadByte *
    (descriptor.births.map fun item =>
        (PackedCell.bytes registry item.create.cell).length).sum +
    tariff.perInitialPayloadByte *
      (descriptor.initialPolicies.map fun policy => policy.canonicalBytes.length).sum

def Descriptor.FeeBound {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) (tariff : CreationTariff) : Prop :=
  descriptor.fee.amount = descriptor.quotedFee tariff ∧
    descriptor.fee.collector = tariff.collector ∧
    descriptor.fee.asset = tariff.asset

/-- A resource capability governs the resource's actual kind and selects its
target-derived initial policy. More detailed holder/issuer/role bounds remain
source-owned factory-template checks. -/
def AuthorityGrant.NativeForBirth {registry : TypeRegistry Digest}
    (grant : AuthorityGrant) (item : BirthItem registry) : Prop :=
  grant.kind = item.resourceKind ∧
    grant.capability.head.scope.targets = {⟨item.create.cellId⟩} ∧
    grant.capability.head.policyId.value = item.create.cellId ∧
    grant.capability.head.policyEpoch = 0

/-- Policy installation requires a distinct, actually program-typed
capability. Object/account authority is never coerced into install authority.
The current policy-install consumer requests precisely this typed target. -/
def AuthorityGrant.PolicyControlForBirth {registry : TypeRegistry Digest}
    (grant : AuthorityGrant) (item : BirthItem registry) : Prop :=
  match grant with
  | ⟨.program, capability⟩ =>
      capability.head.scope.targets = {⟨item.create.cellId⟩} ∧
        capability.head.scope.verbs = {Verb.installPolicy, Verb.revokeCapability} ∧
        capability.head.policyId.value = item.create.cellId ∧
        capability.head.policyEpoch = 0
  | _ => False

def AuthorityGrant.ForBirth {registry : TypeRegistry Digest}
    (grant : AuthorityGrant) (item : BirthItem registry) : Prop :=
  grant.NativeForBirth item ∨ grant.PolicyControlForBirth item

def Descriptor.OwnerGrantsBound {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : Prop :=
  ∀ item ∈ descriptor.births, ∃ grant ∈ descriptor.grants,
    grant.NativeForBirth item ∧ grant.capability.head.holder = .subject item.owner ∧
      ∃ control ∈ descriptor.grants,
        control.PolicyControlForBirth item ∧
          control.capability.head.holder = .subject item.owner ∧
          control.capability.head.id ≠ grant.capability.head.id

/-- Every requested grant belongs to a newborn resource; adding a correct
owner grant cannot conceal an extra grant over an existing resource. -/
def Descriptor.AllGrantsBound {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : Prop :=
  ∀ grant ∈ descriptor.grants, ∃ item ∈ descriptor.births, grant.ForBirth item

def Descriptor.GrantIdsDistinct {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : Prop :=
  (descriptor.grants.map fun grant => grant.capability.head.id).Nodup

/-- Each born resource receives one target-derived initial governing policy.
No unrelated or duplicate policy can be installed under a birth permission.
The actual source bytes and metadata are validated by the fixed compiler. -/
def Descriptor.InitialPoliciesBound {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : Prop :=
  (descriptor.initialPolicies.map InitialPolicy.policyId).Nodup ∧
    (∀ item ∈ descriptor.births, ∃ policy ∈ descriptor.initialPolicies,
      policy.policyId.value = item.create.cellId) ∧
    (∀ policy ∈ descriptor.initialPolicies, ∃ item ∈ descriptor.births,
      policy.policyId.value = item.create.cellId)

def Descriptor.FundingBound {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : Prop :=
  ∀ funding ∈ descriptor.funding,
    funding.destination ∈ descriptor.registeredAccounts

/-! ## Pinned old-factory authorization -/

/-- Source-owned deployment data. `policyAddress` is checked against the actual
old authority selection; possession of generic mutate authority is not a
substitute for the specifically selected factory policy. -/
structure FactoryPins where
  factory : ResourceId .object
  domain : Digest
  semantics : Digest
  federation : FederationId
  policyId : PolicyId
  policyAddress : Digest
  tariff : CreationTariff

/-- A deployment must supply a practical codec and its actual digest function.
Both commitments below are computed from the full same descriptor bytes.
The receiving service fixes this value; it is not part of a user request. -/
structure SourceEncoding (registry : TypeRegistry Digest) where
  codec : LawfulCodec (Descriptor registry)
  hashBytes : List UInt8 -> Digest
  resourceKindOf : registry.Kind -> ResourceKind

def SourceEncoding.argsDigest {registry : TypeRegistry Digest}
    (encoding : SourceEncoding registry) (descriptor : Descriptor registry) : Digest :=
  encoding.hashBytes ([68, 82, 69, 71, 71, 47, 66, 73, 82, 84, 72, 47, 65, 82, 71, 83, 1] ++
    encoding.codec.encode descriptor)

def SourceEncoding.effectsDigest {registry : TypeRegistry Digest}
    (encoding : SourceEncoding registry) (descriptor : Descriptor registry) : Digest :=
  encoding.hashBytes ([68, 82, 69, 71, 71, 47, 66, 73, 82, 84, 72, 47, 69, 70, 70, 69, 67, 84, 83, 1] ++
    encoding.codec.encode descriptor)

/-- The factory pre-root belongs to the actual factory cell. It is not the
resource Book's pre-root; the receiving joint intent binds both observations.
Epochs are taken from the old canonical authority projection. -/
def factoryRequest {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (oldAuthority : AuthState) (factoryPreRoot : Digest) (height : Height)
    (descriptor : Descriptor registry) : Request .object where
  domain := pins.domain
  semantics := pins.semantics
  federation := pins.federation
  subject := descriptor.creator
  subjectKeyEpoch := oldAuthority.subjectKeyEpoch descriptor.creator
  target := pins.factory
  verb := .mutateObject
  argsDigest := encoding.argsDigest descriptor
  effectsDigest := encoding.effectsDigest descriptor
  nonce := descriptor.nonce
  height := height
  preStateRoot := factoryPreRoot
  policyId := pins.policyId
  policyEpoch := oldAuthority.policyEpoch pins.policyId
  policyRevision := oldAuthority.policyRevision pins.policyId
  cost := descriptor.fee.amount

/-- Authorization is obtained before any newborn authority or account exists.
This token binds the complete descriptor, the exact selected old factory
policy, the source-computed tariff, and the declared owners. It is not by
itself allocation, capability issuance, resource admission, or installation. -/
structure FactoryAuthorization {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (portal : Portal) (oldAuthority : AuthState)
    (factoryPreRoot : Digest) (height : Height) (descriptor : Descriptor registry) where
  factoryExact : descriptor.factory = pins.factory
  birthsPresent : descriptor.births ≠ []
  policyPinned : oldAuthority.policyAddress pins.policyId
    (oldAuthority.policyRevision pins.policyId) = pins.policyAddress
  feeBound : descriptor.FeeBound pins.tariff
  feeNontrivial : descriptor.fee.amount = 0 ∨
    descriptor.fee.payer ≠ descriptor.fee.collector
  kindsBound : ∀ item ∈ descriptor.births,
    item.resourceKind = encoding.resourceKindOf item.create.cell.kind
  ownersBound : descriptor.OwnerGrantsBound
  allGrantsBound : descriptor.AllGrantsBound
  grantIdsDistinct : descriptor.GrantIdsDistinct
  policiesBound : descriptor.InitialPoliciesBound
  fundingBound : descriptor.FundingBound
  authorized : Authorized portal oldAuthority
    (factoryRequest pins encoding oldAuthority factoryPreRoot height descriptor)

theorem no_factoryAuthorization_of_wrong_factory
    {registry : TypeRegistry Digest} {pins : FactoryPins}
    {encoding : SourceEncoding registry} {portal : Portal}
    {oldAuthority : AuthState} {factoryPreRoot : Digest} {height : Height}
    {descriptor : Descriptor registry}
    (wrong : descriptor.factory ≠ pins.factory) :
    IsEmpty (FactoryAuthorization pins encoding portal oldAuthority factoryPreRoot
      height descriptor) :=
  ⟨fun accepted => wrong accepted.factoryExact⟩

theorem no_factoryAuthorization_of_wrong_policy
    {registry : TypeRegistry Digest} {pins : FactoryPins}
    {encoding : SourceEncoding registry} {portal : Portal}
    {oldAuthority : AuthState} {factoryPreRoot : Digest} {height : Height}
    {descriptor : Descriptor registry}
    (wrong : oldAuthority.policyAddress pins.policyId
      (oldAuthority.policyRevision pins.policyId) ≠ pins.policyAddress) :
    IsEmpty (FactoryAuthorization pins encoding portal oldAuthority factoryPreRoot
      height descriptor) :=
  ⟨fun accepted => wrong accepted.policyPinned⟩

theorem no_factoryAuthorization_of_wrong_fee
    {registry : TypeRegistry Digest} {pins : FactoryPins}
    {encoding : SourceEncoding registry} {portal : Portal}
    {oldAuthority : AuthState} {factoryPreRoot : Digest} {height : Height}
    {descriptor : Descriptor registry}
    (wrong : descriptor.fee.amount ≠ descriptor.quotedFee pins.tariff) :
    IsEmpty (FactoryAuthorization pins encoding portal oldAuthority factoryPreRoot
      height descriptor) :=
  ⟨fun accepted => wrong accepted.feeBound.1⟩

/-- A positive charge cannot be erased by making its payer the collector. -/
theorem no_factoryAuthorization_of_positive_self_fee
    {registry : TypeRegistry Digest} {pins : FactoryPins}
    {encoding : SourceEncoding registry} {portal : Portal}
    {oldAuthority : AuthState} {factoryPreRoot : Digest} {height : Height}
    {descriptor : Descriptor registry}
    (positive : descriptor.fee.amount ≠ 0)
    (same : descriptor.fee.payer = descriptor.fee.collector) :
    IsEmpty (FactoryAuthorization pins encoding portal oldAuthority factoryPreRoot
      height descriptor) :=
  ⟨fun accepted => accepted.feeNontrivial.elim positive (fun distinct => distinct same)⟩

/-- The resource kind is fixed by the schema catalog, not a caller label. -/
theorem no_factoryAuthorization_of_wrong_schema_kind
    {registry : TypeRegistry Digest} {pins : FactoryPins}
    {encoding : SourceEncoding registry} {portal : Portal}
    {oldAuthority : AuthState} {factoryPreRoot : Digest} {height : Height}
    {descriptor : Descriptor registry} {item : BirthItem registry}
    (member : item ∈ descriptor.births)
    (wrong : item.resourceKind ≠ encoding.resourceKindOf item.create.cell.kind) :
    IsEmpty (FactoryAuthorization pins encoding portal oldAuthority factoryPreRoot
      height descriptor) :=
  ⟨fun accepted => wrong (accepted.kindsBound item member)⟩

/-! ## Axiom accounting for the source and receiving laws -/

/-- info: 'Minidregg.Theory.ResourceBirth.allocate_success_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirth.allocate_success_post

/-- info: 'Minidregg.Theory.ResourceBirth.allocate_success_used' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirth.allocate_success_used

/-- info: 'Minidregg.Theory.ResourceBirth.allocate_success_created' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirth.allocate_success_created

/-- info: 'Minidregg.Theory.ResourceBirth.allocate_of_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirth.allocate_of_fresh

/-- info: 'Minidregg.Theory.ResourceBirth.allocate_failure_atomic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirth.allocate_failure_atomic

/-- info: 'Minidregg.Theory.ResourceBirth.duplicate_birth_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirth.duplicate_birth_refused

/-- info: 'Minidregg.Theory.ResourceBirth.retired_birth_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirth.retired_birth_refused

/-- info: 'Minidregg.Theory.ResourceBirth.no_factoryAuthorization_of_positive_self_fee' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirth.no_factoryAuthorization_of_positive_self_fee

end Minidregg.Theory.ResourceBirth
