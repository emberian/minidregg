/-
# Kernel.CapabilityDelegationReceiver — atomic publication of delegated authority

Only the private native accepted controller result reaches this boundary.
The complete old authority, unchanged resource and selected policy source are
guarded together; the source-created child and operation marker publish in one
exact-image CAS. Exact historical ingress replays before fresh key/expiry checks.
-/
import Kernel.CapabilityDelegationController

namespace Minidregg.Kernel.CapabilityDelegationReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.CapabilityDelegationController
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

def ingressFrame : List UInt8 := "DREGG/CAPABILITY/DELEGATE/SIGNED-INGRESS".toUTF8.toList ++ [1]

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
  eventId := effectsDigest domain semantics ingress.command.2 ingress.command.2.declaration
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (operationMarker domain semantics ingress.command.2)

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {ground : Ground deployment}
  {kind : ResourceKind} {command : Command kind}

def writes (prepared : Prepared deployment profile ambient ground command) : List DataWrite :=
  ground.authorityWrites prepared.authorityPost

def resourceGuard (prepared : Prepared deployment profile ambient ground command) : ReadGuard :=
  ⟨⟨command.declaration.target.value⟩,
    rootBytes (LifecycleImage.bytes Registry (.live prepared.target.before))⟩

def policyGuard (prepared : Prepared deployment profile ambient ground command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient ground command) : List ReadGuard :=
  resourceGuard prepared :: policyGuard prepared ::
    (ground.authorityReadGuards ++
      ((lawReadGuards prepared).getD []).map (fun (cellIdValue, root) => (⟨⟨cellIdValue⟩, root⟩ : Minidregg.Kernel.DurableDataIntent.ReadGuard))).filter
      fun guard => guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient ground command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = ground.view.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (resourceGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = ground.view.model.roots guard.cellId) ∧
    (lawReadGuards prepared).isSome = true

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient ground command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound (prepared : Prepared deployment profile ambient ground command)
    (write : DataWrite) (member : write ∈ writes prepared) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, ServedBasis.Ground.authorityWrites, List.mem_singleton] at member
  subst write
  exact ground.authorityWrite_root_bound _

theorem readGuards_readonly (prepared : Prepared deployment profile ambient ground command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | rest
  · exact shape.2.2.2.1
  · rcases List.mem_cons.mp rest with rfl | authority
    · exact shape.2.2.2.2.1
    · simpa using (List.mem_filter.mp authority).2

structure AcceptedDelegation [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (ground : Ground deployment)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient ground ingress.command.2
  accepted : Accepted prepared ingress.ingress.envelopeBytes
  physical : PhysicalShape prepared

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (ground : Ground deployment)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedDelegation deployment profile ambient ground ingress)) := do
  match prepare deployment profile ambient ground ingress.command.2 with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress.ingress.envelopeBytes with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedDelegation deployment profile ambient ground ingress) : ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelopeBytes.length
  | .proofWork => 3
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedDelegation deployment profile ambient ground ingress) : DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := charge accepted
  event := event deployment.domain profile.semantics ingress
  subject := some ingress.command.2.subject
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

/-- The marker installed by the semantic authority family is exactly the
caller-scoped transaction coordinate retained by the durable receiving journal. -/
theorem intent_authority_marker
    (accepted : AcceptedDelegation deployment profile ambient ground ingress) :
    ingress.command.2.declaration.operationNullifier =
      (transactionId deployment.domain profile.semantics ingress).value := by
  have identity := accepted.prepared.identity
  rw [ground.authorityDomain] at identity
  exact identity

theorem accepted_authority_post (accepted : AcceptedDelegation deployment profile ambient ground ingress) :
    (accepted.accepted.declaration.post accepted.accepted.legs ()).logical =
      accepted.prepared.authorityPost.logical :=
  accepted.accepted.post_exact

/-- Every source-owned write has its exact bytes in the complete installed
snapshot. The accepted physical shape supplies global, not per-page uniqueness. -/
theorem installed_write_bytes (accepted : AcceptedDelegation deployment profile ambient ground ingress)
    (write : DataWrite) (member : write ∈ writes accepted.prepared) :
    (DataSnapshot.install ground.view (intent accepted)).canonicalBytes write.cellId =
      write.canonicalPostBytes :=
  DataSnapshot.install_canonicalBytes_of_member ground.view (intent accepted)
    accepted.physical.1 write member

/-- The installed image holds exactly the post authority cell at the pinned
identifier. There is one authority write and no shard or catalogue. -/
theorem installed_authority_cell (accepted : AcceptedDelegation deployment profile ambient ground ingress) :
    (DataSnapshot.install ground.view (intent accepted)).canonicalBytes (cellIdOf deployment) =
      cellBytes accepted.prepared.authorityPost :=
  installed_write_bytes accepted (ground.authorityWrite accepted.prepared.authorityPost)
    (List.mem_singleton.mpr rfl)

/-- Delegation publishes authority only; the resource whose policy authorized
it retains its exact complete old payload, not merely an equal root. -/
theorem installed_target_unchanged
    (accepted : AcceptedDelegation deployment profile ambient ground ingress) :
    (DataSnapshot.install ground.view (intent accepted)).canonicalBytes
        ⟨ingress.command.2.declaration.target.value⟩ =
      ground.view.canonicalBytes ⟨ingress.command.2.declaration.target.value⟩ := by
  change (DataSnapshot.lookupPostBytes _ (writes accepted.prepared)).getD _ = _
  have frame := accepted.physical.2.2.2.1
  change (⟨ingress.command.2.declaration.target.value⟩ : Digest) ∉
    (writes accepted.prepared).map DataWrite.cellId at frame
  rw [DurableReceiver.lookupPostBytes_missing _ _ frame]
  rfl

/-- The immutable source evaluated on the complete pre/post authority tuple is
also framed exactly through the installation. -/
theorem installed_source_unchanged
    (accepted : AcceptedDelegation deployment profile ambient ground ingress) :
    (DataSnapshot.install ground.view (intent accepted)).canonicalBytes
        ⟨accepted.prepared.source.readGuard.1⟩ =
      ground.view.canonicalBytes ⟨accepted.prepared.source.readGuard.1⟩ := by
  change (DataSnapshot.lookupPostBytes _ (writes accepted.prepared)).getD _ = _
  have frame := accepted.physical.2.2.2.2.1
  change (⟨accepted.prepared.source.readGuard.1⟩ : Digest) ∉
    (writes accepted.prepared).map DataWrite.cellId at frame
  rw [DurableReceiver.lookupPostBytes_missing _ _ frame]
  rfl

theorem no_partial_commit (accepted : AcceptedDelegation deployment profile ambient ground ingress)
    (schedule : Minidregg.Kernel.DurableCommitProtocol.Schedule) :
    (DurableDataIntent.execute schedule ground.view (intent accepted)).storeAfter ground.view = ground.view ∨
      (DurableDataIntent.execute schedule ground.view (intent accepted)).storeAfter ground.view =
        DataSnapshot.install ground.view (intent accepted) :=
  execute_no_partial_data_commit schedule ground.view (intent accepted)

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

/-- The keys a delegation consults beyond the state: its transaction id (the
replay lookup) and its marker's replay nullifier (the spent check). -/
def keys (domain semantics : Digest) (ingress : DecodedIngress) : DurableView.Keys :=
  ⟨[transactionId domain semantics ingress], [nullifier domain semantics ingress]⟩

/-- The recorded intent under this delegation's transaction id is exactly its own. -/
def exactRecord (domain semantics : Digest) (ingress : DecodedIngress)
    (recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope) : Bool :=
  decide (recorded.transactionId = transactionId domain semantics ingress ∧
    recorded.event.event = event domain semantics ingress ∧
    recorded.nullifiers = [nullifier domain semantics ingress])

/-- The replay verdict on a ground, read only through its answer for the
transaction id (`ServedBasis.Ground.replayOf`): an undeclared id is `undeclared`. -/
def replay (domain semantics : Digest) (ground : Ground deployment) (ingress : DecodedIngress) :
    ServedBasis.Ground.Replay Receipt :=
  ground.replayOf (transactionId domain semantics ingress) (exactRecord domain semantics ingress)
    (receipt domain semantics ingress)

theorem replay_only_original (domain semantics : Digest) (ground : Ground deployment) (ingress : DecodedIngress)
    (result : Receipt) (accepted : replay domain semantics ground ingress = .original result) :
    result = receipt domain semantics ingress ∧
      ∃ recorded,
        DurableCommitProtocol.Snapshot.lookupRecorded (transactionId domain semantics ingress) ground.view.model.journal = some recorded ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers = [nullifier domain semantics ingress] := by
  obtain ⟨same, recorded, found, isExact⟩ := ServedBasis.Ground.replayOf_original ground _ _ _ result accepted
  simp only [exactRecord, decide_eq_true_eq] at isExact
  exact ⟨same, recorded, found, isExact.2⟩

/-- **A changed ingress under a recorded transaction id is refused as a conflict**:
the ground's journal answer for this ingress's transaction id is an intent whose
event differs from this ingress's event, so the verdict is `conflict` — never
`fresh` (a second admission) and never `original` (a receipt). -/
theorem replay_changed_ingress_refused (domain semantics : Digest) (ground : Ground deployment) (ingress : DecodedIngress)
    {recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope}
    (found : ground.recorded (transactionId domain semantics ingress) = some (some recorded))
    (different : recorded.event.event ≠ event domain semantics ingress) :
    replay domain semantics ground ingress = .conflict :=
  ServedBasis.Ground.replayOf_conflict ground _ _ _ found (by simp [exactRecord, different])

#assert_axioms replay_changed_ingress_refused

/-- **An undeclared transaction id is refused by name** (the plant's pole): on a
light basis that did not declare it, the verdict is `undeclared`, never "not
recorded". -/
theorem replay_undeclared (domain semantics : Digest) {store : DurableHistory.StoreIdentity}
    (basis : ServedBasis.Basis deployment store) (ingress : DecodedIngress)
    (undeclared : transactionId domain semantics ingress ∉ basis.keys.transactions) :
    replay domain semantics (ServedBasis.Ground.ofBasis basis) ingress = .undeclared :=
  ServedBasis.Ground.replayOf_undeclared basis _ _ _ undeclared

#assert_axioms replay_only_original
#assert_axioms replay_undeclared

/-- info: 'Minidregg.Kernel.CapabilityDelegationReceiver.installed_authority_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms installed_authority_cell

end Minidregg.Kernel.CapabilityDelegationReceiver
