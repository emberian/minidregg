/- A canonical new signing principal and operation marker publish in one CAS. -/
module

public import Compiler.DurableReceiverIO
public import Kernel.ParticipantKeyEnrollment

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.ParticipantKeyEnrollmentReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.ParticipantKeyEnrollment
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

/-- The event id is a digest of the retained signed ingress, never of the
unsigned command (K-RECEIPT-HIDE, `Kernel.ReceiptEventHiding`). -/
def eventIdOfIngress (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PARTICIPANT.KEY-ENROLLMENT.EVENT/v2".toUTF8.toList bytes).digest

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent :=
  StableEvent.retained 1 domain eventIdOfIngress ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  prepared.authority.writes prepared.authorityPost

def resourceGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨deployment.factoryId⟩,
    rootBytes (LifecycleImage.bytes Registry (.live prepared.factory.before))⟩

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  let written := (writes prepared).map DataWrite.cellId
  resourceGuard prepared :: policyGuard prepared ::
    (prepared.authority.readGuards ++
      ((lawReadGuards prepared).getD []).map (fun (cellIdValue, root) => (⟨⟨cellIdValue⟩, root⟩ : Minidregg.Kernel.DurableDataIntent.ReadGuard))).filter fun guard => guard.cellId ∉ written

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

structure AcceptedEnrollment [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  accepted : ParticipantKeyEnrollment.Accepted prepared ingress
  physical : PhysicalShape prepared
theorem AcceptedEnrollment.sound [DecidableEq F] {ingress : DecodedIngress}
    (accepted : AcceptedEnrollment deployment profile ambient durable ingress) :
    accepted.accepted.receipt.envelopeBytes = ingress.ingress.sponsorEnvelope ∧
      Nonempty (Authorized (ParticipantKeyEnrollment.policyConfig accepted.prepared).portal
        accepted.prepared.authority.snapshot.authState
        (ParticipantKeyEnrollment.request deployment accepted.prepared.authority.snapshot profile.semantics ambient
          ingress.command)) ∧
      PhysicalShape accepted.prepared :=
  ⟨accepted.accepted.envelopeExact, ⟨accepted.accepted.semantic.authorization⟩, accepted.physical⟩

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedEnrollment deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedEnrollment deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => DeployedCharge.storageCharge durable.snapshot
      (writes accepted.prepared)
      (event deployment.domain profile.semantics ingress)
  | .witnessBytes => ingress.ingress.sponsorEnvelope.length +
      ingress.ingress.possessionSignature.length + ingress.ingress.nextPublicKey.length +
      ingress.ingress.nextPossessionSignature.length
  | .proofWork => 3
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedEnrollment deployment profile ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := (Minidregg.Theory.ResourceCost.Charge.materialize (charge accepted)).toCharge
  event := event deployment.domain profile.semantics ingress
  subject := some ingress.command.sponsor
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers = [nullifier domain semantics ingress] then
      some (.ok (receipt domain semantics ingress))
    else some (.error ())

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
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes
    | return .rejected .malformedIngress
  match replay deployment.domain profile.semantics durable ingress with
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment profile ambient durable native ingress with
    | .error reason => return .rejected reason
    | .ok accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
      | .confirmed kind _ =>
          return .confirmed kind (receipt deployment.domain profile.semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ParticipantKeyEnrollmentReceiver
