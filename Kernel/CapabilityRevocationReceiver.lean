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
  prepared.authority.writes prepared.authorityPost

def resourceGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨command.target.value⟩,
    rootBytes (LifecycleImage.bytes Registry (.live prepared.target.before))⟩

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  resourceGuard prepared :: policyGuard prepared ::
    (prepared.authority.readGuards ++
      ((lawReadGuards prepared).getD []).map (fun (cellIdValue, root) => (⟨⟨cellIdValue⟩, root⟩ : Minidregg.Kernel.DurableDataIntent.ReadGuard))).filter
      fun guard => guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (resourceGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId) ∧
    (lawReadGuards prepared).isSome = true

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound (prepared : Prepared deployment profile ambient durable command)
    (write : DataWrite) (member : write ∈ writes prepared) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, Loaded.writes, List.mem_singleton] at member
  subst write
  exact prepared.authority.write_root_bound _

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | rest
  · exact shape.2.2.2.1
  · rcases List.mem_cons.mp rest with rfl | authority
    · exact shape.2.2.2.2.1
    · simpa using (List.mem_filter.mp authority).2

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
  subject := some ingress.command.2.subject
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

/-- The written authority cell is the accepted revocation's own post. -/
theorem accepted_authority_post (accepted : AcceptedRevocation deployment profile ambient durable ingress) :
    accepted.accepted.semantic.prepared.post.logical = accepted.prepared.authorityPost.logical := rfl

/-- Every source-owned write has its exact bytes in the complete installed
snapshot. The accepted physical shape supplies global, not per-page uniqueness. -/
theorem installed_write_bytes (accepted : AcceptedRevocation deployment profile ambient durable ingress)
    (write : DataWrite) (member : write ∈ writes accepted.prepared) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes write.cellId =
      write.canonicalPostBytes :=
  DataSnapshot.install_canonicalBytes_of_member durable.snapshot (intent accepted)
    accepted.physical.1 write member

/-- The installed image holds exactly the post authority cell at the pinned
identifier. There is one authority write and no shard or catalogue. -/
theorem installed_authority_cell (accepted : AcceptedRevocation deployment profile ambient durable ingress) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes (cellIdOf deployment) =
      cellBytes accepted.prepared.authorityPost :=
  installed_write_bytes accepted (accepted.prepared.authority.write accepted.prepared.authorityPost)
    (List.mem_singleton.mpr rfl)

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

/-- info: 'Minidregg.Kernel.CapabilityRevocationReceiver.installed_authority_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms installed_authority_cell

/-- info: 'Minidregg.Kernel.CapabilityRevocationReceiver.no_partial_commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_partial_commit

/-- info: 'Minidregg.Kernel.CapabilityRevocationReceiver.replay_only_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms replay_only_original

end Minidregg.Kernel.CapabilityRevocationReceiver
