/-
# Kernel.CapabilityRevocationReceiver — atomic publication of resource-authorized revocation

Only the private native accepted controller result reaches this boundary.
The complete old authority, unchanged resource and selected policy source are
guarded together; the source-created revocation and operation marker publish in one
exact-image CAS. Exact historical ingress replays before fresh key/expiry checks.
-/
import Kernel.CapabilityRevocationController

namespace Minidregg.Kernel.CapabilityRevocationReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.CapabilityRevocationController
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

structure Ingress where
  commandBytes : List UInt8
  envelopeBytes : List UInt8

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.envelopeBytes))
    (fun (command, envelope) => ⟨command, envelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressFrame : List UInt8 := "DREGG/CAPABILITY/REVOKE/SIGNED-INGRESS".toUTF8.toList ++ [1]

def rawIngressCodec : LawfulCodec Ingress where
  encode ingress := ingressFrame ++ ingressStream.encode ingress
  decode bytes := if bytes.take ingressFrame.length = ingressFrame then
    ingressStream.toLawful.decode (bytes.drop ingressFrame.length) else none
  decode_encode := by
    intro ingress
    have decoded := ingressStream.toLawful.decode_encode ingress
    change ingressStream.toLawful.decode (ingressStream.encode ingress) = some ingress at decoded
    simp [decoded]

def ingressCodec : LawfulCodec Ingress := strictCodec rawIngressCodec

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : PackedCommand
  commandExact : commandCodec.encode command = ingress.commandBytes
  envelope : CredentialSignedEnvelopeController.SignedEnvelope
  envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.envelopeBytes = some envelope

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command =>
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.envelopeBytes with
    | none => none
    | some envelope =>
      some ⟨ingress, command, command_decode_canonical commandExact, envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 := ingressCodec.encode ingress.ingress

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨operationMarker domain semantics ingress.command.2⟩

def event (domain semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := effectsDigest domain semantics ingress.command.2 (declaration domain semantics ingress.command.2)
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (operationMarker domain semantics ingress.command.2)

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {kind : ResourceKind} {command : Command kind}

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  prepared.physical.writes ++ prepared.physical.placement.auxiliaryCreates.map ResourceBirthController.birthWrite

def resourceGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨command.target.value⟩,
    rootBytes (LifecycleImage.bytes Registry (.live prepared.target.before))⟩

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  resourceGuard prepared :: policyGuard prepared :: readonlyGuards prepared.authority.readGuards (writes prepared)

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (resourceGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound (prepared : Prepared deployment profile ambient durable command)
    (write : DataWrite) (member : write ∈ writes prepared) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  rcases List.mem_append.mp member with authority | allocation
  · exact planWrites_roots_bound deployment.authorityAnchor durable.snapshot
      prepared.authority.snapshot.catalogue prepared.update.postPages prepared.physical.placement write authority
  · obtain ⟨request, _, rfl⟩ := List.mem_map.mp allocation
    exact ResourceBirthController.birthWrite_root_bound request

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | rest
  · exact shape.2.2.2.1
  · rcases List.mem_cons.mp rest with rfl | authority
    · exact shape.2.2.2.2.1
    · exact of_decide_eq_true (List.mem_filter.mp authority).2

structure AcceptedRevocation [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command.2
  accepted : Accepted prepared ingress.ingress.envelopeBytes
  physical : PhysicalShape prepared

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedRevocation deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command.2 with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress.ingress.envelopeBytes with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedRevocation deployment profile ambient durable ingress) : ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelopeBytes.length
  | .proofWork => 3
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedRevocation deployment profile ambient durable ingress) : DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := charge accepted
  event := event deployment.domain profile.semantics ingress
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

/-- Source-derived semantic and physical posts agree exactly. -/
theorem accepted_authority_post (accepted : AcceptedRevocation deployment profile ambient durable ingress) :
    accepted.accepted.semantic.prepared.post.logical = accepted.prepared.physical.post.logical := by
  change accepted.prepared.candidate.validated.apply.logical = _
  rw [← accepted.prepared.postExact]
  change CredentialAuthorityDomain.logicalOfPages accepted.prepared.update.postPages =
    CredentialAuthorityDomain.logicalOfPages accepted.prepared.physical.post.pages
  rw [accepted.prepared.physical.postPages]

/-- Every source-owned write has its exact bytes in the complete installed
snapshot. The accepted physical shape supplies global, not per-page uniqueness. -/
theorem installed_write_bytes (accepted : AcceptedRevocation deployment profile ambient durable ingress)
    (write : DataWrite) (member : write ∈ writes accepted.prepared) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes write.cellId =
      write.canonicalPostBytes :=
  DataSnapshot.install_canonicalBytes_of_member durable.snapshot (intent accepted)
    accepted.physical.1 write member

/-- An existing authority shard omitted by the authority writer cannot be
clobbered by an internal allocation: all allocated identities were unused in
the actual loaded directory, while this shard has a live canonical envelope. -/
theorem unchanged_authority_shard_unwritten
    (accepted : AcceptedRevocation deployment profile ambient durable ingress)
    (cellId : DurableDataIntent.CellId) (page : CredentialAuthorityPageMaterializer.Page)
    (physical : durable.snapshot.canonicalBytes cellId = shardBytes page)
    (authorityUnwritten : cellId ∉ accepted.prepared.physical.writes.map DataWrite.cellId) :
    cellId ∉ (writes accepted.prepared).map DataWrite.cellId := by
  intro member
  obtain ⟨write, member, same⟩ := List.mem_map.mp member
  rcases List.mem_append.mp member with authority | allocation
  · exact authorityUnwritten (List.mem_map.mpr ⟨write, authority, same⟩)
  · obtain ⟨request, inCreates, rfl⟩ := List.mem_map.mp allocation
    have unused := (accepted.prepared.physical.fresh.2 request inCreates).1
    have absent : accepted.prepared.directory.directory.slots request.cellId = .absent := by
      cases slot : accepted.prepared.directory.directory.slots request.cellId with
      | absent => rfl
      | present cell =>
          exact False.elim (unused (accepted.prepared.directory.directory.present_used slot))
    have view := (LifecycleImage.view_fresh_iff Registry accepted.prepared.directory.directory
      request.cellId).mpr ⟨absent, unused⟩
    have freshBytes : durable.snapshot.canonicalBytes ⟨request.cellId⟩ = [] := by
      rw [← accepted.prepared.directory.bytes_exact, view]
      rfl
    change (⟨request.cellId⟩ : DurableDataIntent.CellId) = cellId at same
    rw [same] at freshBytes
    have impossible := freshBytes.symm.trans physical
    cases impossible

private theorem installed_authority_page
    (accepted : AcceptedRevocation deployment profile ambient durable ingress)
    (reference : CredentialAuthorityDomain.Ref) (page : CredentialAuthorityPageMaterializer.Page)
    (represented : PostPageRepresented durable.snapshot accepted.prepared.physical.writes
      accepted.prepared.physical.readGuards accepted.prepared.physical.placement.auxiliaryCreates reference page) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes reference.cellId = shardBytes page := by
  rcases represented.2 with written | created | unchanged
  · obtain ⟨write, member, same, bytes⟩ := written
    have installed := installed_write_bytes accepted write (List.mem_append_left _ member)
    rw [same, bytes] at installed
    exact installed
  · obtain ⟨request, member, same, bytes⟩ := created
    have inWrites : ResourceBirthController.birthWrite request ∈ writes accepted.prepared :=
      List.mem_append_right _ (List.mem_map.mpr ⟨request, member, rfl⟩)
    have installed := installed_write_bytes accepted _ inWrites
    change (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
      ⟨request.cellId⟩ = LifecycleImage.bytes Registry (.live request.cell) at installed
    rw [same, bytes] at installed
    exact installed
  · obtain ⟨bytes, guard, member, same⟩ := unchanged
    have localFrame := accepted.prepared.physical.readGuards_readonly guard member
    rw [same] at localFrame
    have frame := unchanged_authority_shard_unwritten accepted reference.cellId page bytes localFrame
    change (DataSnapshot.lookupPostBytes reference.cellId (writes accepted.prepared)).getD
      (durable.snapshot.canonicalBytes reference.cellId) = _
    rw [DurableReceiver.lookupPostBytes_missing _ _ frame]
    exact bytes

/-- Every page of the whole accepted semantic authority post is represented in
the actual installation, including retained pages and newly allocated shards. -/
theorem installed_authority_pages
    (accepted : AcceptedRevocation deployment profile ambient durable ingress) :
    List.Forall₂
      (fun (reference : CredentialAuthorityDomain.Ref)
          (page : CredentialAuthorityPageMaterializer.Page) =>
        (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes reference.cellId = shardBytes page)
      accepted.prepared.physical.post.catalogue.pages accepted.prepared.physical.post.pages :=
  accepted.prepared.physical.represented.imp
    (fun reference page represented => installed_authority_page accepted reference page represented)

theorem installed_authority_catalogue
    (accepted : AcceptedRevocation deployment profile ambient durable ingress) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
        deployment.authorityAnchor.catalogueCellId =
      catalogueBytes accepted.prepared.physical.post.catalogue := by
  let write := catalogueWrite deployment.authorityAnchor durable.snapshot
    (placedCatalogue accepted.prepared.authority.snapshot.catalogue accepted.prepared.physical.placement)
  have member : write ∈ writes accepted.prepared :=
    List.mem_append_left _ (List.mem_append_right _ (by simp [write]))
  have installed := installed_write_bytes accepted write member
  change (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
    deployment.authorityAnchor.catalogueCellId = _ at installed
  rw [accepted.prepared.physical.postCatalogue]
  exact installed

/-- Revocation publishes authority only; the resource whose policy authorized
it retains its exact complete old payload, not merely an equal root. -/
theorem installed_target_unchanged
    (accepted : AcceptedRevocation deployment profile ambient durable ingress) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
        ⟨ingress.command.2.target.value⟩ =
      durable.snapshot.canonicalBytes ⟨ingress.command.2.target.value⟩ := by
  change (DataSnapshot.lookupPostBytes _ (writes accepted.prepared)).getD _ = _
  have frame := accepted.physical.2.2.2.1
  change (⟨ingress.command.2.target.value⟩ : Digest) ∉
    (writes accepted.prepared).map DataWrite.cellId at frame
  rw [DurableReceiver.lookupPostBytes_missing _ _ frame]
  rfl

/-- The immutable source evaluated on the complete pre/post authority tuple is
also framed exactly through the installation. -/
theorem installed_source_unchanged
    (accepted : AcceptedRevocation deployment profile ambient durable ingress) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
        ⟨accepted.prepared.source.readGuard.1⟩ =
      durable.snapshot.canonicalBytes ⟨accepted.prepared.source.readGuard.1⟩ := by
  change (DataSnapshot.lookupPostBytes _ (writes accepted.prepared)).getD _ = _
  have frame := accepted.physical.2.2.2.2.1
  change (⟨accepted.prepared.source.readGuard.1⟩ : Digest) ∉
    (writes accepted.prepared).map DataWrite.cellId at frame
  rw [DurableReceiver.lookupPostBytes_missing _ _ frame]
  rfl

theorem no_partial_commit (accepted : AcceptedRevocation deployment profile ambient durable ingress)
    (schedule : Minidregg.Kernel.DurableCommitProtocol.Schedule) :
    (DurableDataIntent.execute schedule durable.snapshot (intent accepted)).storeAfter durable.snapshot = durable.snapshot ∨
      (DurableDataIntent.execute schedule durable.snapshot (intent accepted)).storeAfter durable.snapshot =
        DataSnapshot.install durable.snapshot (intent accepted) :=
  execute_no_partial_data_commit schedule durable.snapshot (intent accepted)

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded (transactionId domain semantics ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers = [nullifier domain semantics ingress] then
      some (.ok (receipt domain semantics ingress))
    else some (.error ())

theorem replay_only_original (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress)
    (result : Receipt) (accepted : replay domain semantics durable ingress = some (.ok result)) :
    result = receipt domain semantics ingress ∧
      ∃ recorded,
        DurableCommitProtocol.Snapshot.lookupRecorded (transactionId domain semantics ingress) durable.snapshot.model.journal = some recorded ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers = [nullifier domain semantics ingress] := by
  unfold replay at accepted
  split at accepted
  · cases accepted
  · rename_i recorded found
    split at accepted
    · rename_i exactRecord
      have same : receipt domain semantics ingress = result := by simpa using accepted
      exact ⟨same.symm, recorded, found, exactRecord.2⟩
    · cases accepted

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | transactionConflict
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveLoaded (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable) (bytes : List UInt8) : IO Result := do
  match decodeIngress bytes with
  | none => return .rejected .malformedCommand
  | some ingress =>
    match replay deployment.domain profile.semantics durable ingress with
    | some (.ok receipt) => return .confirmed .replayed receipt
    | some (.error _) => return .transactionConflict
    | none =>
      match ← admitDecodedNative deployment profile ambient durable native ingress with
      | .error reason => return .rejected reason
      | .ok accepted =>
        match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
        | .confirmed kind _ => return .confirmed kind (receipt deployment.domain profile.semantics ingress)
        | .rejected reason => return .durableRejected reason
        | .contention => return .contention
        | .unavailable detail => return .unavailable detail
        | .uncertain detail => return .uncertain detail

def receive (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (bytes : List UInt8) : IO Result := do
  match ← DurableReceiverIO.load transport rootBytes with
  | .error detail => return .unavailable detail
  | .ok durable => receiveLoaded deployment profile ambient native transport durable bytes

/-- info: 'Minidregg.Kernel.CapabilityRevocationReceiver.accepted_authority_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_authority_post

/-- info: 'Minidregg.Kernel.CapabilityRevocationReceiver.installed_authority_pages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms installed_authority_pages

/-- info: 'Minidregg.Kernel.CapabilityRevocationReceiver.installed_authority_catalogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms installed_authority_catalogue

/-- info: 'Minidregg.Kernel.CapabilityRevocationReceiver.no_partial_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_partial_commit

/-- info: 'Minidregg.Kernel.CapabilityRevocationReceiver.replay_only_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms replay_only_original

end Minidregg.Kernel.CapabilityRevocationReceiver
