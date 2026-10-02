/-
# Kernel.SubjectKeyRotation -- a pre-rotated subject rotates its signing key

The host face of `Theory.KeyPreRotation`.  A rotation command names the
subject and its complete successor key record; the ingress carries that command
and one signature, by the NEW key, over the rotation's possession frame.  No
sponsor, capability or current-key signature participates: the authority is
the commitment the current record already holds.  Admission is
`KeyPreRotation.gate` at the loaded authority cell, instantiated with
`nextKeyDigest` (cSHAKE256, `Compiler.Sp800185Cshake256`, under the tag
`DREGG.SIGNING-KEY.NEXT/v1`), and with the signature oracle that verifies
the one presented signature under the new key only (`presented`).

The patch is `KeyPreRotation.patch`: the subject's key rows only.  The
operation marker is a durable nullifier, so an exact rotation is admitted once;
a second rotation needs the next commitment, so a replayed ingress fails the
gate as well as the nullifier.
-/
import Kernel.ParticipantKeyEnrollment
import Theory.KeyPreRotation

namespace Minidregg.Kernel.SubjectKeyRotation

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

/-! ## The next-key digest

One definition, `ParticipantKeyEnrollment.nextKeyDigest`: enrollment commits
to it and checks the next key's possession against it; a rotation opens it. -/

export Minidregg.Kernel.ParticipantKeyEnrollment (nextKeyDigest nextKeyDigestTag)

/-! ## Command, ingress, frames -/

structure Command where
  subject : SubjectId
  nonce : Nat
  key : KeyRecord
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat CredentialSigningKeyCodec.keyRecordStream))
    (fun command => (command.subject, command.nonce, command.key))
    (fun (subject, nonce, key) => ⟨subject, nonce, key⟩)
    (by intro command; cases command; rfl)

def commandFrame : List UInt8 := "DREGG/SUBJECT-KEY/ROTATE/v1".toUTF8.toList

def commandCodec : LawfulCodec Command :=
  ParticipantKeyEnrollment.framed commandFrame commandStream

def Command.rotation (command : Command) : KeyPreRotation.Rotation :=
  ⟨command.subject, command.key⟩

structure Ingress where
  commandBytes : List UInt8
  possessionSignature : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.possessionSignature))
    (fun (command, possession) => ⟨command, possession⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  ParticipantKeyEnrollment.framed "DREGG/SUBJECT-KEY/ROTATE/SIGNED/v1".toUTF8.toList ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command =>
      some ⟨ingress, command,
        ResourceBirthCodec.strictCodec_canonical
          (ParticipantKeyEnrollment.framedRaw commandFrame commandStream) commandExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

/-- The operation marker: the durable nullifier and the transaction id. -/
def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.SUBJECT-KEY.ROTATE.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        (StreamCodec.product StreamCodec.nat StreamCodec.nat)))).encode
      (domain, semantics, command.subject, command.key.keyEpoch, command.nonce))).digest.value

/-- The exact bytes the NEW key signs. -/
def possessionFrame (domain semantics : Digest) (command : Command) : List UInt8 :=
  "DREGG/SUBJECT-KEY/ROTATE/POSSESSION/v1".toUTF8.toList ++
    (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, commandCodec.encode command)

/-- The signature oracle of one presented possession signature: it vouches for
the new key exactly when the native verifier accepted it under that key, and
for no other key. -/
def presented (command : Command) (verified : Bool) : List UInt8 → Bool :=
  fun publicKey => decide (publicKey = command.key.publicKey) && verified

/-- The oracle a plan assumes: the possession signature, once made, verifies. -/
def assumed (command : Command) : List UInt8 → Bool := presented command true

/-! ## Preparation (everything but the signature) -/

inductive Reject where
  | malformedIngress | authorityUnavailable
  | gate (reason : KeyPreRotation.Reject)
  | publicKeyExists | malformedKey | replayedMarker | validation | physicalPreparation
  | possession (reason : CredentialSignatureIO.Error)
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

structure Prepared (deployment : Deployment) (semantics : Digest) (durable : Durable)
    (command : Command) where
  private mk ::
  authority : Loaded deployment durable.snapshot
  current : KeyRecord
  gated : KeyPreRotation.gate nextKeyDigest authority.snapshot.logical command.rotation
    (assumed command) = .ok current
  publicKeyFresh : ParticipantKeyEnrollment.allKeys authority.snapshot.logical
    (fun key => key.publicKey != command.key.publicKey) = true
  keyShape : command.key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
    command.key.publicKey.length = 32 ∧
    command.key.activeFrom ≤ authority.snapshot.revision + 1 ∧
    authority.snapshot.revision + 1 ≤ command.key.activeUntil
  unspent : authority.snapshot.spent (marker authority.snapshot.domain semantics command) = false
  validated : CellState.ValidatedPatch AuthorityMaterializer authority.snapshot.cell
    authority.snapshot.cell.root
    (KeyPreRotation.patch authority.snapshot.logical current command.rotation)

def prepare (deployment : Deployment) (semantics : Digest) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment semantics durable command) := do
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let snapshot := authority.snapshot
  match gated : KeyPreRotation.gate nextKeyDigest snapshot.logical command.rotation
      (assumed command) with
  | .error reason => throw (.gate reason)
  | .ok current =>
    if publicKeyFresh : ParticipantKeyEnrollment.allKeys snapshot.logical
        (fun key => key.publicKey != command.key.publicKey) then
      if keyShape : command.key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
          command.key.publicKey.length = 32 ∧
          command.key.activeFrom ≤ snapshot.revision + 1 ∧
          snapshot.revision + 1 ≤ command.key.activeUntil then
        if unspent : snapshot.spent (marker snapshot.domain semantics command) = false then
          match validate AuthorityMaterializer snapshot.cell snapshot.cell.root
              (KeyPreRotation.patch snapshot.logical current command.rotation) with
          | .rejected _ => throw .validation
          | .accepted validated =>
              pure ⟨authority, current, gated, publicKeyFresh, keyShape, unspent, validated⟩
        else throw .replayedMarker
      else throw .malformedKey
    else throw .publicKeyExists

variable {deployment : Deployment} {semantics : Digest} {durable : Durable} {command : Command}

/-- The authority cell after rotation: the validated patch applied. -/
def Prepared.authorityPost (prepared : Prepared deployment semantics durable command) :
    CredentialAuthorityDomain.Cell :=
  prepared.validated.apply

/-! ## Admission: the possession signature and the gate it feeds -/

structure Accepted (prepared : Prepared deployment semantics durable command)
    (ingress : DecodedIngress) where
  private mk ::
  commandExact : ingress.command = command
  verified : Bool
  gated : KeyPreRotation.gate nextKeyDigest prepared.authority.snapshot.logical command.rotation
    (presented command verified) = .ok prepared.current

def admitNative (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment semantics durable command)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  if commandExact : ingress.command = command then
    match ← CredentialSignatureIO.verify native command.key.publicKey
        (possessionFrame prepared.authority.snapshot.domain semantics command)
        ingress.ingress.possessionSignature with
    | .error reason => return .error (.possession reason)
    | .ok verified =>
        match gated : KeyPreRotation.gate nextKeyDigest prepared.authority.snapshot.logical
            command.rotation (presented command verified) with
        | .error reason => return .error (.gate reason)
        | .ok current =>
            if same : current = prepared.current then
              return .ok ⟨commandExact, verified, same ▸ gated⟩
            else return .error .validation
  else return .error .malformedIngress

/-- An accepted rotation opened the commitment: the new key's digest is the
current record's `nextKeyDigest`. -/
theorem Accepted.precommitted {prepared : Prepared deployment semantics durable command}
    {ingress : DecodedIngress} (accepted : Accepted prepared ingress) :
    prepared.current.nextKeyDigest = some (nextKeyDigest command.key.publicKey) :=
  (KeyPreRotation.rotation_requires_precommitted_key accepted.gated).2

/-- An accepted rotation carried a verified signature by the new key. -/
theorem Accepted.possession {prepared : Prepared deployment semantics durable command}
    {ingress : DecodedIngress} (accepted : Accepted prepared ingress) :
    accepted.verified = true := by
  have signed := ((KeyPreRotation.gate_ok_iff nextKeyDigest _ _ _ _).1 accepted.gated).2.2.2.2
  simpa [presented, KeyPreRotation.Rotation.key, Command.rotation] using signed

/-! ## Durable intent -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.SUBJECT-KEY.ROTATE.EFFECT/v1".toUTF8.toList
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

structure AcceptedRotation (deployment : Deployment) (semantics : Digest) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment semantics durable ingress.command
  accepted : Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative (deployment : Deployment) (semantics : Digest) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedRotation deployment semantics durable ingress)) := do
  match prepare deployment semantics durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable {ingress : DecodedIngress}

def charge (accepted : AcceptedRotation deployment semantics durable ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.possessionSignature.length
  | .proofWork => 1
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedRotation deployment semantics durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain semantics ingress
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain semantics ingress]
  exactCharge := charge accepted
  event := event deployment.domain semantics ingress
  -- The rotation is signed by the subject's NEXT key, on the subject's behalf.
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

/-! ## Plan and status (no secret, no signature) -/

/-- What the new key signs, authored by the host after the rotation prepares. -/
structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  possessionHeader : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream bytesStream)))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes, plan.possessionHeader))
    (fun (domain, semantics, command, possession) => ⟨domain, semantics, command, possession⟩)
    (by intro plan; cases plan; rfl)

def signingPlanCodec : LawfulCodec SigningPlan :=
  ParticipantKeyEnrollment.framed "DREGG/SUBJECT-KEY/ROTATE/PLAN/v1".toUTF8.toList signingPlanStream

/-- A subject's key status as seen by someone holding one public key: the
current epoch and key line, whether a next key is committed, and whether the
presented key is the current key or the committed next key.  It discloses no
key the asker does not already hold. -/
structure Status where
  epoch : Nat
  keyId : Nat
  prerotated : Bool
  isCurrent : Bool
  isCommittedNext : Bool
  currentRevoked : Bool
  deriving DecidableEq, Repr

def status (logical : Store CredentialAuthorityState.layout) (subject : SubjectId)
    (publicKey : List UInt8) : Option Status := do
  let current ← currentSigningKey logical subject
  pure ⟨current.keyEpoch, current.keyId, current.nextKeyDigest.isSome,
    decide (current.publicKey = publicKey),
    decide (current.nextKeyDigest = some (nextKeyDigest publicKey)),
    (logical ⟨.revoked, signingKeyRevocation current⟩).isSome⟩

end Minidregg.Kernel.SubjectKeyRotation
