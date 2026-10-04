/- Explicit current-key authorization to establish its first next-key commitment.
The current and next key sign different frames over the complete command.
Neither a sponsor nor a carry operator can invent this authority. -/
import Kernel.Receivers.SubjectKeyRotation
import Theory.KeyCommitmentAdoption

namespace Minidregg.Kernel.SubjectKeyCommitmentAdoption
open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer
abbrev Registry := CanonicalCellRegistry.registry

structure Command where
  subject : SubjectId
  nonce : Nat
  expectedCurrent : KeyRecord
  nextPublicKey : List UInt8
  deriving DecidableEq, Repr

def Command.adoption (command : Command) : KeyCommitmentAdoption.Adoption :=
  ⟨command.subject, command.expectedCurrent, command.nextPublicKey⟩

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product CredentialSigningKeyCodec.keyRecordStream bytesStream)))
    (fun command => (command.subject, command.nonce, command.expectedCurrent, command.nextPublicKey))
    (fun (subject, nonce, current, next) => ⟨subject, nonce, current, next⟩)
    (by intro command; cases command; rfl)

def commandFrame : List UInt8 := "DREGG/SUBJECT-KEY/ADOPT-NEXT/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := ParticipantKeyEnrollment.framed commandFrame commandStream

structure Ingress where
  commandBytes : List UInt8
  currentSignature : List UInt8
  nextPossessionSignature : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream))
    (fun ingress => (ingress.commandBytes, ingress.currentSignature, ingress.nextPossessionSignature))
    (fun (command, current, next) => ⟨command, current, next⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  ParticipantKeyEnrollment.framed "DREGG/SUBJECT-KEY/ADOPT-NEXT/SIGNED/v1".toUTF8.toList ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command => some ⟨ingress, command,
      ResourceBirthCodec.strictCodec_canonical
        (ParticipantKeyEnrollment.framedRaw commandFrame commandStream) commandExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 := ingressCodec.encode ingress.ingress

/-- The marker excludes signatures and binds the current key epoch plus nonce.
Changing the proposed commitment under the same marker is a conflict. -/
def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.SUBJECT-KEY.ADOPT-NEXT.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        (StreamCodec.product StreamCodec.nat StreamCodec.nat)))).encode
      (domain, semantics, command.subject, command.expectedCurrent.keyEpoch, command.nonce))).digest.value

def authorizationFrame (domain semantics : Digest) (command : Command) : List UInt8 :=
  "DREGG/SUBJECT-KEY/ADOPT-NEXT/AUTHORIZE/v1".toUTF8.toList ++
    (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, commandCodec.encode command)

def possessionFrame (domain semantics : Digest) (command : Command) : List UInt8 :=
  "DREGG/SUBJECT-KEY/ADOPT-NEXT/POSSESSION/v1".toUTF8.toList ++
    (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, commandCodec.encode command)

inductive Reject where
  | malformedIngress | authorityUnavailable | ineligible | publicKeyExists
  | replayedMarker | validation | physicalPreparation | invalidCurrentSignature | invalidNextPossession
  | signature (reason : CredentialSignatureIO.Error)
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

structure Prepared (deployment : Deployment) (semantics : Digest) (durable : Durable)
    (command : Command) where
  private mk ::
  authority : Loaded deployment durable.snapshot
  eligible : KeyCommitmentAdoption.Eligible authority.snapshot.logical authority.snapshot.revision command.adoption
  /-- Every key row, including historical and revoked versions, participates. -/
  nextFresh : ParticipantKeyEnrollment.allKeys authority.snapshot.logical
    (fun key => key.publicKey != command.nextPublicKey) = true
  unspent : authority.snapshot.spent (marker authority.snapshot.domain semantics command) = false
  validated : CellState.ValidatedPatch AuthorityMaterializer authority.snapshot.cell
    authority.snapshot.cell.root (KeyCommitmentAdoption.patch ParticipantKeyEnrollment.nextKeyDigest command.adoption)

def prepare (deployment : Deployment) (semantics : Digest) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment semantics durable command) := do
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let snapshot := authority.snapshot
  if eligible : KeyCommitmentAdoption.Eligible snapshot.logical snapshot.revision command.adoption then
    if fresh : ParticipantKeyEnrollment.allKeys snapshot.logical
        (fun key => key.publicKey != command.nextPublicKey) then
      if unspent : snapshot.spent (marker snapshot.domain semantics command) = false then
        match validate AuthorityMaterializer snapshot.cell snapshot.cell.root
            (KeyCommitmentAdoption.patch ParticipantKeyEnrollment.nextKeyDigest command.adoption) with
        | .rejected _ => throw .validation
        | .accepted validated => pure ⟨authority, eligible, fresh, unspent, validated⟩
      else throw .replayedMarker
    else throw .publicKeyExists
  else throw .ineligible

variable {deployment : Deployment} {semantics : Digest} {durable : Durable} {command : Command}

def Prepared.authorityPost (prepared : Prepared deployment semantics durable command) :
    CredentialAuthorityDomain.Cell := prepared.validated.apply

structure Accepted (prepared : Prepared deployment semantics durable command) (ingress : DecodedIngress) where
  private mk ::
  commandExact : ingress.command = command
  currentVerified : Bool
  currentTrue : currentVerified = true
  nextVerified : Bool
  nextTrue : nextVerified = true

def admitNative (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment semantics durable command) (ingress : DecodedIngress) :
    IO (Except Reject (Accepted prepared ingress)) := do
  if commandExact : ingress.command = command then
    match ← CredentialSignatureIO.verify native command.expectedCurrent.publicKey
        (authorizationFrame prepared.authority.snapshot.domain semantics command) ingress.ingress.currentSignature with
    | .error reason => return .error (.signature reason)
    | .ok currentVerified =>
      if currentTrue : currentVerified = true then
        match ← CredentialSignatureIO.verify native command.nextPublicKey
            (possessionFrame prepared.authority.snapshot.domain semantics command) ingress.ingress.nextPossessionSignature with
        | .error reason => return .error (.signature reason)
        | .ok nextVerified =>
          if nextTrue : nextVerified = true then
            return .ok ⟨commandExact, currentVerified, currentTrue, nextVerified, nextTrue⟩
          else return .error .invalidNextPossession
      else return .error .invalidCurrentSignature
  else return .error .malformedIngress

theorem Accepted.gated {prepared : Prepared deployment semantics durable command} {ingress : DecodedIngress}
    (accepted : Accepted prepared ingress) :
    KeyCommitmentAdoption.gate prepared.authority.snapshot.logical prepared.authority.snapshot.revision
      command.adoption (fun _ => accepted.currentVerified) (fun _ => accepted.nextVerified) = .ok () :=
  (KeyCommitmentAdoption.gate_ok_iff _ _ _ _ _).2 ⟨prepared.eligible, accepted.currentTrue, accepted.nextTrue⟩

/-- Both native signature checks belong to this exact, still-current record. -/
theorem Accepted.current_authorized {prepared : Prepared deployment semantics durable command} {ingress : DecodedIngress}
    (accepted : Accepted prepared ingress) :
    currentSigningKey prepared.authority.snapshot.logical command.subject = some command.expectedCurrent ∧
      command.expectedCurrent.nextKeyDigest = none ∧ accepted.currentVerified = true ∧ accepted.nextVerified = true :=
  ⟨prepared.eligible.1, prepared.eligible.2.1, accepted.currentTrue, accepted.nextTrue⟩

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.SUBJECT-KEY.ADOPT-NEXT.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, ingress.bytes))).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

def writes (prepared : Prepared deployment semantics durable command) : List DataWrite :=
  prepared.authority.writes prepared.authorityPost

def readGuards (prepared : Prepared deployment semantics durable command) : List ReadGuard :=
  prepared.authority.readGuards.filter fun guard =>
    guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment semantics durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable (prepared : Prepared deployment semantics durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound (prepared : Prepared deployment semantics durable command)
    (write : DataWrite) (member : write ∈ writes prepared) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, Loaded.writes, List.mem_singleton] at member
  subst write
  exact prepared.authority.write_root_bound _

theorem readGuards_readonly (prepared : Prepared deployment semantics durable command)
    (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  simpa using (List.mem_filter.mp member).2

structure AcceptedAdoption (deployment : Deployment) (semantics : Digest) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment semantics durable ingress.command
  accepted : Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative (deployment : Deployment) (semantics : Digest) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedAdoption deployment semantics durable ingress)) := do
  match prepare deployment semantics durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable {ingress : DecodedIngress}

def charge (accepted : AcceptedAdoption deployment semantics durable ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.currentSignature.length + ingress.ingress.nextPossessionSignature.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedAdoption deployment semantics durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain semantics ingress
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain semantics ingress]
  exactCharge := charge accepted
  event := event deployment.domain semantics ingress
  -- Both signatures authorize only the first commitment; the current key stays current.
  subject := some ingress.command.subject
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared

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

def receiveLoaded (deployment : Deployment) (semantics : Digest)
    (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes
    | return .rejected .malformedIngress
  match replay deployment.domain semantics durable ingress with
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment semantics durable native ingress with
    | .error reason => return .rejected reason
    | .ok accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
      | .confirmed kind _ =>
          return .confirmed kind (receipt deployment.domain semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail


structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  currentAuthorizationHeader : List UInt8
  nextPossessionHeader : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream bytesStream))))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes,
      plan.currentAuthorizationHeader, plan.nextPossessionHeader))
    (fun (domain, semantics, command, current, next) => ⟨domain, semantics, command, current, next⟩)
    (by intro plan; cases plan; rfl)

def signingPlanCodec : LawfulCodec SigningPlan :=
  ParticipantKeyEnrollment.framed "DREGG/SUBJECT-KEY/ADOPT-NEXT/PLAN/v1".toUTF8.toList signingPlanStream

end Minidregg.Kernel.SubjectKeyCommitmentAdoption
