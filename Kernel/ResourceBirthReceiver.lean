/-
# Kernel.ResourceBirthReceiver -- accepted birth to one durable data intent

The policy controller owns signed ingress admission. This module connects its
complete accepted heterogeneous turn to the exact source-prepared physical
writes, without executing a second allocator, authority updater or resource
program. Policy-source read dependencies join the existing complete authority
guards. The native receiver remains the existing exact-byte journal/CAS loop.

Stable replay identity retains exact ingress bytes and the complete descriptor;
matching a recorded ingress precedes any new nullifier or state-root admission.
A replay returns the recorded receipt and performs no new semantic execution.
-/
import Kernel.ResourceBirthPolicyController
import Compiler.DurableReceiverIO
import Compiler.CredentialAuthorityReplay

namespace Minidregg.Kernel.ResourceBirthReceiver

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ResourceBirthPolicyController.Concrete

set_option autoImplicit false

-- Keep typeclass inference from trying to invert the concrete cSHAKE profile.
-- Runtime computation and the source identity equations remain unchanged.
attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

variable {F : Type} [Field F] {profile : CanonicalRuntimeProfile.Profile F}
variable {deployment : CanonicalCellRegistry.Deployment} {pins : FactoryPins}
variable {durable : ResourceBirthController.Concrete.Durable}
variable {descriptor : Descriptor CanonicalCellRegistry.registry}

local instance fieldEq
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (incidence : Legs descriptor) : DecidableEq ((layout prepared).schema incidence).Field :=
  (layout prepared).fieldDecidableEq incidence

local instance resourceEq
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (incidence : Legs descriptor) : DecidableEq ((layout prepared).schema incidence).Resource :=
  (layout prepared).resourceDecidableEq incidence

/-! ## Exact semantic and physical post correspondence -/

theorem tuple_source_exact
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height)) :
    tuple.source = ⟨descriptor, rfl⟩ :=
  Subtype.ext tuple.source.property

/-- Every tuple under this concrete plan has the same source-computed final
cells. Validation proofs do not choose values or supply independent readouts. -/
theorem tuple_post_exact
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (incidence : Legs descriptor) :
    tuple.post incidence = (validated prepared height incidence).apply := by
  apply CellState.Materialized.ext
  simp only [PreparedTuple.post, CellState.ValidatedPatch.apply]
  rw [tuple_source_exact prepared height tuple]
  rfl

/-- All deferred mode evidence and authorizations are required here. The
accepted post is exactly the source result already used by policy evaluation. -/
theorem accepted_post_exact
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (portals : Legs descriptor → Portal)
    (evidence : tuple.AdmissionEvidence portals) (incidence : Legs descriptor) :
    (tuple.toDeclaration portals
      (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor)).post
      (tuple.accept portals (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor) evidence)
      incidence = (validated prepared height incidence).apply :=
  (tuple.accepted_posts_exact portals _ evidence incidence).trans
    (tuple_post_exact prepared height tuple incidence)

theorem accepted_book_post
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (portals : Legs descriptor → Portal) (evidence : tuple.AdmissionEvidence portals) :
    (tuple.toDeclaration portals
      (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor)).post
      (tuple.accept portals (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor) evidence)
      .book = prepared.resources.post :=
  accepted_post_exact prepared height tuple portals evidence .book

/-- The authority incidence is virtual. Its actual post is represented by
the computed complete domain after the grouped shard/catalogue update; it is
never packed as an invented full-authority physical cell. -/
theorem accepted_authority_post
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (portals : Legs descriptor → Portal) (evidence : tuple.AdmissionEvidence portals) :
    (tuple.toDeclaration portals
      (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor)).post
      (tuple.accept portals (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor) evidence)
      .authority = prepared.grants.physical.post.cell :=
  (accepted_post_exact prepared height tuple portals evidence .authority).trans
    prepared.authority_post_exact.symm

/-- Allocation posts are already physical lifecycle envelopes. The equality
prevents double wrapping and preserves the exact signed typed payload. -/
theorem accepted_allocation_bytes
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (portals : Legs descriptor → Portal) (evidence : tuple.AdmissionEvidence portals)
    (index : Fin descriptor.createRequests.length) :
    ((tuple.toDeclaration portals
      (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor)).post
      (tuple.accept portals (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor) evidence)
      (.allocation index)).bytes =
      (ResourceBirthController.birthWrite (creation descriptor index)).canonicalPostBytes := by
  rw [accepted_post_exact prepared height tuple portals evidence (.allocation index)]
  change (LifecycleSlot.materializer CanonicalCellRegistry.registry).codec.encode
    (ResourceBirthController.allocationValidated prepared.directory.directory
      (creation descriptor index)).apply.logical = _
  rw [ResourceBirthController.allocation_post_exact]
  simpa only [LifecycleSlot.cell, CellState.materialize, CellState.Materialized.bytes,
    ResourceBirthController.birthWrite] using
    LifecycleSlot.bytes_exact CanonicalCellRegistry.registry (.live (creation descriptor index).cell)

theorem accepted_book_conserves
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (portals : Legs descriptor → Portal) (evidence : tuple.AdmissionEvidence portals)
    (asset : Nat) :
    (CanonicalResourceKernel.logicalBook
      ((tuple.toDeclaration portals
        (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor)).post
        (tuple.accept portals (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor) evidence)
        .book).logical).totalAsset asset =
      (CanonicalResourceKernel.logicalBook prepared.book.payload.logical).totalAsset asset := by
  rw [accepted_book_post prepared height tuple portals evidence]
  exact prepared.conserves asset

/-! ## Stable identity and one source-owned accounting vector -/

/-- Birth consumes the same domain/marker key as every other operation over
the canonical authority nullifier map. -/
def birthNullifier (domain : Digest) (identifier : Nat) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain identifier

theorem birthNullifier_eq_iff (domainLeft domainRight : Digest) (left right : Nat) :
    birthNullifier domainLeft left = birthNullifier domainRight right ↔
      domainLeft = domainRight ∧ left = right :=
  CredentialAuthorityReplay.nullifier_eq_iff domainLeft domainRight left right

variable [DecidableEq F]

private def guardOfPair (guard : Nat × Digest) : ReadGuard :=
  ⟨⟨guard.1⟩, guard.2⟩

def sourceReadGuards {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) : List ReadGuard :=
  accepted.sourceReadGuards.map guardOfPair

/-- Duplicate observations retain their exact source roots. If a dependency
is already a guarded write, it does not become a second read-only participant. -/
def readGuards {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) : List ReadGuard :=
  accepted.prepared.readGuards ++
    CredentialAuthorityDomainReceiver.readonlyGuards (sourceReadGuards accepted)
      accepted.prepared.writes

private theorem branch_read_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (branch : Branch accepted.descriptor) :
    (accepted.branches branch).readGuard.2 =
      durable.snapshot.model.roots ⟨(accepted.branches branch).readGuard.1⟩ := by
  rw [BranchAccepted.readGuard_eq_source]
  exact (accepted.branches branch).source.readGuard_exact.trans
    ((congrArg rootBytes (accepted.prepared.directory.bytes_exact _)).trans
      (durable.snapshot.coherent _))

theorem sourceReadGuards_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (guard : ReadGuard) (member : guard ∈ sourceReadGuards accepted) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId := by
  change guard ∈
    (ResourceBirthPolicyController.Concrete.AcceptedBirth.sourceReadGuards accepted).map guardOfPair
    at member
  obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp member
  unfold ResourceBirthPolicyController.Concrete.AcceptedBirth.sourceReadGuards at inPairs
  rcases List.mem_append.mp inPairs with first | sources
  · rcases List.mem_append.mp first with native | allocations
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at native
      rcases native with rfl | rfl
      · exact branch_read_exact accepted .factory
      · exact branch_read_exact accepted .authority
    · obtain ⟨index, _, rfl⟩ := List.mem_map.mp allocations
      exact branch_read_exact accepted (.allocation index)
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp sources
    exact branch_read_exact accepted (.source index)

theorem readGuards_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId := by
  rcases List.mem_append.mp member with authority | source
  · exact accepted.prepared.readGuards_exact guard authority
  · exact sourceReadGuards_exact accepted guard (List.mem_filter.mp source).1

theorem readGuards_readonly {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.cellId ∉ accepted.prepared.writes.map DataWrite.cellId := by
  rcases List.mem_append.mp member with authority | source
  · exact accepted.prepared.readGuards_readonly guard authority
  · exact of_decide_eq_true (List.mem_filter.mp source).2

theorem source_reads_covered {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (guard : ReadGuard) (member : guard ∈ sourceReadGuards accepted) :
    guard.cellId ∈ accepted.prepared.writes.map DataWrite.cellId ∨ guard ∈ readGuards accepted := by
  by_cases written : guard.cellId ∈ accepted.prepared.writes.map DataWrite.cellId
  · exact Or.inl written
  · exact Or.inr (List.mem_append_right _ (List.mem_filter.mpr
      ⟨member, by simpa using written⟩))

/-- The strict signed ingress contains the complete frame-two descriptor and
all exact native envelopes in source order. It is retained privately for replay,
not returned as a receipt. Historical equality needs no new authorization. -/
def event (domain : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 2
  domain := domain
  eventId := commitmentBytes
    ("DREGG.RESOURCE.BIRTH.EVENT/v2".toUTF8.toList ++
      digestStream.encode domain ++ ingress.bytes)
  canonicalBytes := ingress.bytes

theorem event_retains_descriptor (domain : Digest) (ingress : DecodedIngress) :
    (event domain ingress).canonicalBytes = ingressCodec.encode ingress.ingress ∧
      ingress.ingress.descriptorBytes =
        CanonicalCellRegistry.sourceEncoding.codec.encode ingress.descriptor :=
  ⟨rfl, ingress.descriptorCanonical.symm⟩

/-- Source-defined admission units: verification work counts source-selected
policy checks, bytes count canonical committed inputs/posts, and the fee lane
is the actual Book transfer amount. This one vector is checked and debited by
the durable preflight; no caller supplies a competing charge projection. -/
def charge {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) : Charge
  | .incidences => 3 + accepted.descriptor.createRequests.length
  | .turnBytes => accepted.ingress.bytes.length
  | .memoryTouches => accepted.prepared.writes.length + (readGuards accepted).length
  | .witnessBytes => (credentialBundleStream.encode accepted.ingress.ingress.credentials).length
  | .proofWork => 2 + accepted.descriptor.createRequests.length +
      accepted.descriptor.resourceBatch.operations.length
  | .storageBytes =>
      (accepted.prepared.writes.map fun write => write.canonicalPostBytes.length).sum +
        accepted.ingress.bytes.length
  | .sideEffectCount => 1
  | .feeDebit => accepted.descriptor.fee.amount
  | .networkBytes | .leaseByteBlocks => 0

theorem charge_fee {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) :
    charge accepted .feeDebit = accepted.descriptor.fee.amount := rfl

/-- Only the concrete private native-admitted carrier reaches this emitter.
There is no decoded DataIntent, arbitrary portal or freely chosen write list. -/
def intent {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) : DataIntent rootBytes where
  transactionId := accepted.descriptor.transactionId
  writes := accepted.prepared.writes
  readGuards := readGuards accepted
  nullifiers := [birthNullifier deployment.domain accepted.descriptor.authorityNullifier]
  exactCharge := charge accepted
  event := event deployment.domain accepted.ingress
  postRootsBound := accepted.prepared.write_roots_bound
  guardsReadOnly := readGuards_readonly accepted

/-- The admitted constructor with its finite charge evaluated once. No
receiver or encoder needs to retain and rerun charge-producing source work. -/
def materializedIntent {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) : DataIntent rootBytes where
  transactionId := accepted.descriptor.transactionId
  writes := accepted.prepared.writes
  readGuards := readGuards accepted
  nullifiers := [birthNullifier deployment.domain accepted.descriptor.authorityNullifier]
  exactCharge := (Charge.materialize (charge accepted)).toCharge
  event := event deployment.domain accepted.ingress
  postRootsBound := accepted.prepared.write_roots_bound
  guardsReadOnly := readGuards_readonly accepted

/-- Exact complete intent equality, including all roots, guards and charges. -/
theorem materializedIntent_eq {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) :
    materializedIntent accepted = intent accepted := by
  simp only [materializedIntent, intent, Charge.materialize_eq]

/-- The actual receiving and semantic-replay constructor uses finite values;
the source definition remains the specification for all existing consumers. -/
@[csimp] theorem intent_eq_materializedIntent : @intent = @materializedIntent := by
  funext F instF profile deployment pins durable instEq height accepted
  exact (materializedIntent_eq accepted).symm

theorem materializedIntent_record_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) :
    DurableReceiver.IntentRecord.ofIntent (materializedIntent accepted) =
      DurableReceiver.IntentRecord.ofIntent (intent accepted) := by
  rw [materializedIntent_eq]

/-- The original canonical record codec emits exactly the same bytes. -/
theorem materializedIntent_record_bytes_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) :
    DurableReceiverCodec.intentStream.encode
        (DurableReceiver.IntentRecord.ofIntent (materializedIntent accepted)) =
      DurableReceiverCodec.intentStream.encode
        (DurableReceiver.IntentRecord.ofIntent (intent accepted)) := by
  rw [materializedIntent_record_exact]

/-- info: 'Minidregg.Kernel.ResourceBirthReceiver.intent_eq_materializedIntent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intent_eq_materializedIntent

/-- info: 'Minidregg.Kernel.ResourceBirthReceiver.materializedIntent_record_bytes_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materializedIntent_record_bytes_exact

theorem intent_exact_source {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) :
    (intent accepted).writes = accepted.prepared.writes ∧
      (intent accepted).exactCharge = charge accepted ∧
      (intent accepted).event.canonicalBytes = accepted.ingress.bytes ∧
      (intent accepted).transactionId = accepted.descriptor.transactionId :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Both global durable coordinates come from the receiving source's same
creator-scoped birth identity; neither can be chosen independently by ingress. -/
theorem intent_derived_identity {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) :
    (intent accepted).transactionId = ResourceBirthController.Concrete.sourceIdentity
        profile.compilerProfile deployment accepted.descriptor.creator accepted.descriptor.nonce ∧
      (intent accepted).nullifiers =
        [birthNullifier deployment.domain
          (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile deployment
            accepted.descriptor.creator accepted.descriptor.nonce).value] := by
  constructor
  · exact accepted.prepared.transaction_identity
  · change [birthNullifier deployment.domain accepted.ingress.descriptor.authorityNullifier] = _
    rw [accepted.prepared.authority_marker_identity]
    rfl

/-- Every exact planned post is installed by the existing data installer.
Uniqueness comes from actual receiving preparation, not a pick-last rule. -/
theorem installed_write_bytes {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (write : DataWrite) (member : write ∈ accepted.prepared.writes) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes write.cellId =
      write.canonicalPostBytes :=
  DataSnapshot.install_canonicalBytes_of_member durable.snapshot (intent accepted)
    accepted.prepared.writesUnique write member

/-- Initial source bytes are in the same atomic installed image as their new
heads and owner grants. There is no external source-staging success premise. -/
theorem installed_policy_source_bytes {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (record : PolicyRecord)
    (member : record ∈ accepted.prepared.grants.initialSources.records) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
        ⟨(CanonicalCellRegistry.policySourceCreate deployment.domain record).cellId⟩ =
      LifecycleImage.bytes CanonicalCellRegistry.registry
        (.live (CanonicalCellRegistry.policySourceCell record)) :=
  installed_write_bytes accepted
    (ResourceBirthController.birthWrite (CanonicalCellRegistry.policySourceCreate deployment.domain record))
    (accepted.prepared.initial_source_write record member)

theorem installed_initial_policy_source {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (initial : InitialPolicy) (member : initial ∈ accepted.descriptor.initialPolicies) :
    ∃ record,
      PolicyRecordCodec.decode initial.canonicalBytes = some record ∧
      PolicySourceCell.InitialFacts deployment.domain profile.compilerProfile initial record ∧
      (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
          ⟨PolicySourceCell.physicalId deployment.domain initial.address⟩ =
        LifecycleImage.bytes CanonicalCellRegistry.registry
          (.live (CanonicalCellRegistry.policySourceCell record)) := by
  obtain ⟨record, inRecords, decoded, facts⟩ :=
    accepted.prepared.grants.initialSources.record_of_member initial member
  have installed := installed_policy_source_bytes accepted record inRecords
  change (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
      ⟨PolicySourceCell.physicalId deployment.domain (PolicyRecordCodec.digest record)⟩ = _ at installed
  rw [facts.2.2.1] at installed
  exact ⟨record, decoded, facts, installed⟩

/-! ## Complete authority survives every role in the final physical write set -/

private theorem observed_native_bytes {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    {identifier : Nat} {kind : CanonicalCellRegistry.Kind}
    (observed : ResourceBirthController.Concrete.ObservedCell deployment
      accepted.prepared.directory.directory identifier kind) :
    durable.snapshot.canonicalBytes ⟨identifier⟩ =
      LifecycleImage.bytes CanonicalCellRegistry.registry (.live ⟨kind, observed.payload⟩) := by
  rw [← accepted.prepared.directory.bytes_exact]
  rw [(LifecycleImage.view_live_iff CanonicalCellRegistry.registry
    accepted.prepared.directory.directory identifier _).mpr observed.present]

private theorem live_bytes_kind_exact
    (left right : CellRegistry.PackedCell CanonicalCellRegistry.registry)
    (same : LifecycleImage.bytes CanonicalCellRegistry.registry (.live left) =
      LifecycleImage.bytes CanonicalCellRegistry.registry (.live right)) :
    left.kind = right.kind := by
  have encoded : (LifecycleImage.codec CanonicalCellRegistry.registry).encode (.live left) =
      (LifecycleImage.codec CanonicalCellRegistry.registry).encode (.live right) := same
  have images := lawful_encode_injective (LifecycleImage.codec CanonicalCellRegistry.registry) encoded
  exact congrArg CellRegistry.PackedCell.kind (LifecycleImage.live.inj images)

private theorem shard_ne_native {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    {identifier : Nat} {kind : CanonicalCellRegistry.Kind}
    (observed : ResourceBirthController.Concrete.ObservedCell deployment
      accepted.prepared.directory.directory identifier kind)
    (different : kind ≠ .authorityShard)
    (cellId : DurableDataIntent.CellId) (page : CredentialAuthorityPageMaterializer.Page)
    (physical : durable.snapshot.canonicalBytes cellId =
      CredentialAuthorityDomainReceiver.shardBytes page) :
    cellId ≠ ⟨identifier⟩ := by
  intro same
  subst cellId
  have bytes := (observed_native_bytes accepted observed).symm.trans physical
  exact different (live_bytes_kind_exact _ _ bytes)

/-- The whole birth cannot overwrite an authority page that its own authority
lowering leaves unchanged. Fresh allocations conflict with its actual live
bytes; the factory and Book conflict with its actual decoded schema kind.
Filtered read guards alone would not establish this property. -/
theorem unchanged_authority_shard_unwritten {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (cellId : DurableDataIntent.CellId) (page : CredentialAuthorityPageMaterializer.Page)
    (physical : durable.snapshot.canonicalBytes cellId =
      CredentialAuthorityDomainReceiver.shardBytes page)
    (authorityUnwritten : cellId ∉
      accepted.prepared.grants.physical.writes.map DataWrite.cellId) :
    cellId ∉ accepted.prepared.writes.map DataWrite.cellId := by
  intro member
  obtain ⟨write, member, same⟩ := List.mem_map.mp member
  rcases List.mem_append.mp member with front | authority
  · rcases List.mem_append.mp front with allocation | native
    · obtain ⟨request, inRequests, rfl⟩ := List.mem_map.mp allocation
      have fresh := accepted.prepared.fresh_before request inRequests
      change (⟨request.cellId⟩ : DurableDataIntent.CellId) = cellId at same
      rw [same] at fresh
      have impossible := fresh.symm.trans physical
      cases impossible
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at native
      rcases native with rfl | rfl
      · exact shard_ne_native accepted accepted.prepared.factory (by decide) cellId page
          physical same.symm
      · exact shard_ne_native accepted accepted.prepared.book (by decide) cellId page
          physical same.symm
  · exact authorityUnwritten (List.mem_map.mpr ⟨write, authority, same⟩)

private theorem installed_authority_page {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (reference : CredentialAuthorityDomain.Ref) (page : CredentialAuthorityPageMaterializer.Page)
    (represented : CredentialAuthorityDomainReceiver.PostPageRepresented durable.snapshot
      accepted.prepared.grants.physical.writes accepted.prepared.grants.physical.readGuards
      accepted.prepared.grants.physical.placement.auxiliaryCreates reference page) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes reference.cellId =
      CredentialAuthorityDomainReceiver.shardBytes page := by
  rcases represented.2 with written | created | unchanged
  · obtain ⟨write, member, same, bytes⟩ := written
    have installed := installed_write_bytes accepted write (List.mem_append_right _ member)
    rw [same, bytes] at installed
    exact installed
  · obtain ⟨request, member, same, bytes⟩ := created
    have inRequests : request ∈ accepted.descriptor.createRequests := by
      unfold Descriptor.createRequests
      apply List.mem_append_right
      change request ∈ accepted.ingress.descriptor.auxiliaryCreates
      rw [accepted.prepared.auxiliaryExact]
      exact List.mem_append_right _ member
    have inWrites : ResourceBirthController.birthWrite request ∈ accepted.prepared.writes :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨request, inRequests, rfl⟩))
    have installed := installed_write_bytes accepted _ inWrites
    change (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
      ⟨request.cellId⟩ = LifecycleImage.bytes CanonicalCellRegistry.registry (.live request.cell)
      at installed
    rw [same, bytes] at installed
    exact installed
  · obtain ⟨bytes, guard, member, same⟩ := unchanged
    have localFrame := accepted.prepared.grants.physical.readGuards_readonly guard member
    rw [same] at localFrame
    have frame := unchanged_authority_shard_unwritten accepted reference.cellId page bytes localFrame
    change (DataSnapshot.lookupPostBytes reference.cellId accepted.prepared.writes).getD
      (durable.snapshot.canonicalBytes reference.cellId) = _
    rw [DurableReceiver.lookupPostBytes_missing _ _ frame]
    exact bytes

/-- Every page of the complete semantic authority post has its exact bytes
in the actual installed snapshot, including old unchanged pages and freshly
allocated shards. No page/root equality assumption is supplied by a caller. -/
theorem installed_authority_pages {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) :
    List.Forall₂
      (fun (reference : CredentialAuthorityDomain.Ref)
          (page : CredentialAuthorityPageMaterializer.Page) =>
        (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes reference.cellId =
          CredentialAuthorityDomainReceiver.shardBytes page)
      accepted.prepared.grants.physical.post.catalogue.pages
      accepted.prepared.grants.physical.post.pages := by
  exact accepted.prepared.grants.physical.represented.imp
    (fun reference page represented => installed_authority_page accepted reference page represented)

theorem installed_authority_catalogue {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
        deployment.authorityAnchor.catalogueCellId =
      CredentialAuthorityDomainReceiver.catalogueBytes
        accepted.prepared.grants.physical.post.catalogue := by
  let write := CredentialAuthorityDomainReceiver.catalogueWrite deployment.authorityAnchor
    durable.snapshot (CredentialAuthorityDomainReceiver.placedCatalogue
      accepted.prepared.authority.snapshot.catalogue accepted.prepared.grants.physical.placement)
  have member : write ∈ accepted.prepared.writes :=
    List.mem_append_right _ (List.mem_append_right _ (by simp [write]))
  have installed := installed_write_bytes accepted write member
  change (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
    deployment.authorityAnchor.catalogueCellId = _ at installed
  rw [accepted.prepared.grants.physical.postCatalogue]
  exact installed

theorem refusal_no_mutation {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (reason : DurableDataIntent.RejectReason)
    (refused : DurableDataIntent.execute .complete durable.snapshot (intent accepted) =
      .rejected reason) :
    (DurableDataIntent.execute .complete durable.snapshot (intent accepted)).storeAfter durable.snapshot =
      durable.snapshot := by rw [refused]; rfl

theorem no_partial_commit {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) (schedule : Schedule) :
    (DurableDataIntent.execute schedule durable.snapshot (intent accepted)).storeAfter durable.snapshot =
        durable.snapshot ∨
      (DurableDataIntent.execute schedule durable.snapshot (intent accepted)).storeAfter durable.snapshot =
        DataSnapshot.install durable.snapshot (intent accepted) :=
  execute_no_partial_data_commit schedule durable.snapshot (intent accepted)

/-! ## Replay before fresh admission, with sealed receipts -/

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

inductive Reject where
  | malformedIngress
  | transactionConflict
  | admission (reason : ResourceBirthPolicyController.Reject)
  | durable (reason : DurableDataIntent.RejectReason)

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receipt (domain : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨ingress.descriptor.transactionId, (event domain ingress).eventId⟩

/-- Return a historical receipt only for the exact original canonical signed
ingress and the same semantic marker. Roots, nullifier freshness, policy epoch
and time are deliberately not re-admitted after this historical match. -/
def replay (domain : Digest) (durable : ResourceBirthController.Concrete.Durable)
    (ingress : DecodedIngress) : Option (Except Reject Receipt) :=
  match Snapshot.lookupRecorded ingress.descriptor.transactionId durable.snapshot.model.journal with
  | none => none
  | some recorded =>
      if recorded.transactionId = ingress.descriptor.transactionId ∧
          recorded.event.event = event domain ingress ∧
          recorded.nullifiers = [birthNullifier domain ingress.descriptor.authorityNullifier] then
        some (.ok (receipt domain ingress))
      else some (.error .transactionConflict)

/-- Historical success retains the original canonical signed ingress and
the exact shared authority marker. An occupied transaction identifier alone
cannot authorize a replay or substitute a different event. -/
theorem replay_only_exact (domain : Digest)
    (durable : ResourceBirthController.Concrete.Durable) (ingress : DecodedIngress)
    (result : Receipt) (accepted : replay domain durable ingress = some (.ok result)) :
    result = receipt domain ingress ∧
      ∃ recorded,
        Snapshot.lookupRecorded ingress.descriptor.transactionId durable.snapshot.model.journal =
            some recorded ∧
        recorded.transactionId = ingress.descriptor.transactionId ∧
        recorded.event.event = event domain ingress ∧
        recorded.nullifiers = [birthNullifier domain ingress.descriptor.authorityNullifier] := by
  unfold replay at accepted
  split at accepted
  · cases accepted
  · rename_i recorded found
    split at accepted
    · rename_i exactRecord
      have same : receipt domain ingress = result := by simpa using accepted
      exact ⟨same.symm, recorded, found, exactRecord⟩
    · cases accepted

/-- A recorded transaction with a different source event refuses without
running any new authority or state transition. -/
theorem replay_wrong_event_refused (domain : Digest)
    (durable : ResourceBirthController.Concrete.Durable) (ingress : DecodedIngress)
    (recorded : DurableCommitProtocol.Intent TransactionId
      DurableDataIntent.CellId StableNullifier ReplayEnvelope)
    (found : Snapshot.lookupRecorded ingress.descriptor.transactionId
      durable.snapshot.model.journal = some recorded)
    (different : recorded.event.event ≠ event domain ingress) :
    replay domain durable ingress = some (.error .transactionConflict) := by
  simp [replay, found, different]

/-- Admit against the exact snapshot already validated by the host. The native
receiver performs one compare-and-swap against this image and returns contention
if it changed; it never silently rebases an accepted birth onto a later image. -/
def receiveLoaded
    (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : CanonicalCellRegistry.Deployment) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (durable : ResourceBirthController.Concrete.Durable)
    (height : Height) (bytes : List UInt8) : IO Result := do
  match decodeIngress bytes with
  | none => return .rejected .malformedIngress
  | some ingress =>
      match replay deployment.domain durable ingress with
      | some (.ok recorded) => return .confirmed .replayed recorded
      | some (.error reason) => return .rejected reason
      | none =>
          match ← admitDecodedNative profile deployment pins native durable height ingress with
          | .error reason => return .rejected (.admission reason)
          | .ok accepted =>
              match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
              | .confirmed kind _ => return .confirmed kind (receipt deployment.domain ingress)
              | .rejected reason => return .rejected (.durable reason)
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail
              | .uncertain detail => return .uncertain detail

/-- This is the concrete external input boundary. It accepts only strict
signed ingress, never an intent or an authority verdict. Storage readback is
the existing native receiver's success criterion; only receipt IDs escape.
The compatibility attempt parameter does not authorize rebasing admission. -/
def receive
    (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : CanonicalCellRegistry.Deployment) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (height : Height) (bytes : List UInt8) (attempts : Nat := 4) : IO Result := do
  let _ := attempts
  match decodeIngress bytes with
  | none => return .rejected .malformedIngress
  | some _ =>
      match ← DurableReceiverIO.load transport rootBytes with
      | .error detail => return .unavailable detail
      | .ok durable => receiveLoaded profile deployment pins native transport durable height bytes

end Minidregg.Kernel.ResourceBirthReceiver
