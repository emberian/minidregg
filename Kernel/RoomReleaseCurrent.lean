/- SAME Prepared room release checks. Every recipient's encryption record and
offline room read entitlement are checked against the actual mutation's loaded
authority/directory/clock. This module does not by itself certify latest lineage,
activate a native route or authorize ciphertext transmission. Those require the
typed chronological head and the durable event67 Applied producer. -/
import Kernel.NativeCurrentSigningKey
import Compiler.RoomKeyReleaseCodec
import Kernel.RecipientReadEntitlement

namespace Minidregg.Kernel.RoomReleaseCurrent
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {ground : Ground deployment} {command : Command}

def marker (request : RoomKeyReleaseCodec.Request) : Nat :=
  (Sp800185Cshake256.hash "DREGG.PRIVATE.ROOM.RELEASE.CONTEXT/v1".toUTF8.toList
    (RoomKeyReleaseCodec.encode request)).digest.value

def context (prepared : PreparedInvocation deployment profile ambient ground command) :
    ResourceObservationAdmission.Context deployment :=
  ⟨prepared.directory,prepared.authority⟩

def roomRoot (prepared : PreparedInvocation deployment profile ambient ground command)
    (request : RoomKeyReleaseCodec.Request) : Option Digest :=
  match ground.directory.slots request.room with
  | .absent => none
  | .present cell => some cell.payload.root

def wanted (prepared : PreparedInvocation deployment profile ambient ground command)
    (request : RoomKeyReleaseCodec.Request) (delivery : RoomKeyReleaseCodec.Delivery)
    (root : Digest) : Request .object where
  domain := deployment.domain
  semantics := profile.semantics
  federation := ambient.federation
  subject := ⟨delivery.member⟩
  subjectKeyEpoch := ground.authority.authState.subjectKeyEpoch ⟨delivery.member⟩
  target := ⟨request.room⟩
  verb := .observeObject
  argsDigest := ⟨marker request⟩
  effectsDigest := ⟨marker request⟩
  nonce := marker request
  height := ambient.height
  preStateRoot := root
  policyId := ⟨request.room⟩
  policyEpoch := ground.authority.authState.policyEpoch ⟨request.room⟩
  policyRevision := ground.authority.authState.policyRevision ⟨request.room⟩
  cost := (RoomKeyReleaseCodec.encode request).length

def entry (request : RoomKeyReleaseCodec.Request) (delivery : RoomKeyReleaseCodec.Delivery)
    (claim : CurrentRecipientRecord.Claim) : Minidregg.Theory.ObjectAudienceRoster.Entry :=
  ⟨delivery.member,delivery.roomCapability,request.keysCell,claim.epoch,0⟩

structure Recipient (genesisHeight : Nat)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (request : RoomKeyReleaseCodec.Request) (delivery : RoomKeyReleaseCodec.Delivery) where
  private mk ::
  claim : CurrentRecipientRecord.Claim
  decoded : CurrentRecipientRecord.decode ⟨delivery.member⟩ delivery.record = some claim
  scope : claim.room = request.room ∧ claim.keysCell = request.keysCell
  recordSignature : NativeCurrentSigningKey.Verified prepared.authority claim.member claim.epoch
    claim.signingKey (CurrentRecipientRecord.statement claim) claim.signature
  root : Digest
  rootExact : roomRoot prepared request = some root
  observation : ResourceObservationAdmission.Prepared (context prepared) profile
    (wanted prepared request delivery root) (marker request) ⟨delivery.roomCapability⟩
    (RoomKeyReleaseCodec.encode request)
  entitlement : RecipientReadEntitlement.Checked genesisHeight observation (entry request delivery claim)
  /-- This profile uses source-derived offline entitlement. A nonempty live
  envelope cannot be silently ignored or mistaken for the record signature. -/
  offline : delivery.entitlementEnvelope = []

def checkRecipient (native : CredentialSignatureIO.NativeConfig) (genesisHeight : Nat)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (request : RoomKeyReleaseCodec.Request) (delivery : RoomKeyReleaseCodec.Delivery) :
    IO (Except String (Recipient genesisHeight prepared request delivery)) := do
  if offline : delivery.entitlementEnvelope = [] then
    match decoded : CurrentRecipientRecord.decode ⟨delivery.member⟩ delivery.record with
    | none => return .error "invalid room recipient record"
    | some claim =>
      if scope : claim.room = request.room ∧ claim.keysCell = request.keysCell then
        match ← NativeCurrentSigningKey.verify native prepared.authority claim.member claim.epoch
            claim.signingKey (CurrentRecipientRecord.statement claim) claim.signature with
        | .error reason => return .error reason
        | .ok recordSignature =>
          match rootExact : roomRoot prepared request with
          | none => return .error "room is absent"
          | some root =>
            match ResourceObservationAdmission.prepare (context prepared) profile
                (wanted prepared request delivery root) (marker request) ⟨delivery.roomCapability⟩
                (RoomKeyReleaseCodec.encode request) with
            | .error _ => return .error "room read preparation refused"
            | .ok observation =>
              match RecipientReadEntitlement.check genesisHeight observation (entry request delivery claim) with
              | none => return .error "recipient lacks current complete room read entitlement"
              | some entitlement =>
                return .ok ⟨claim,decoded,scope,recordSignature,root,rootExact,observation,entitlement,offline⟩
      else return .error "recipient record is for another room or keys cell"
  else return .error "unsupported live entitlement envelope"

def checkRecipients (native : CredentialSignatureIO.NativeConfig) (genesisHeight : Nat)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (request : RoomKeyReleaseCodec.Request) :
    IO (Except String ((i : Fin request.deliveries.length) →
      Recipient genesisHeight prepared request request.deliveries[i])) :=
  DeclaredResourceController.collectIO (fun i =>
    checkRecipient native genesisHeight prepared request request.deliveries[i])

def dependencies (genesisHeight : Nat)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (request : RoomKeyReleaseCodec.Request)
    (recipients : (i : Fin request.deliveries.length) →
      Recipient genesisHeight prepared request request.deliveries[i]) : List ReadGuard :=
  (List.finRange request.deliveries.length).flatMap (fun i => (recipients i).entitlement.guards)

def guardHeld (intent : DataIntent ResourceBirthCodec.rootBytes) (guard : ReadGuard) : Prop :=
  guard ∈ intent.readGuards ∨ ∃ write ∈ intent.writes,
    write.cellId = guard.cellId ∧ write.expectedPre = guard.expectedRoot

instance (intent : DataIntent ResourceBirthCodec.rootBytes) (guard : ReadGuard) :
    Decidable (guardHeld intent guard) := by unfold guardHeld; infer_instance

structure Bound (genesisHeight : Nat)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (request : RoomKeyReleaseCodec.Request) (signed : SignedCommand)
    (shape : PhysicalShape prepared) (accepted : AcceptedInvocation prepared signed) where
  private mk ::
  recipients : (i : Fin request.deliveries.length) →
    Recipient genesisHeight prepared request request.deliveries[i]
  authorityExact : prepared.authority.readGuard.expectedRoot = request.authorityRoot
  authorityHeld : guardHeld (accepted.dataIntent shape) prepared.authority.readGuard
  retained : ∀ guard ∈ dependencies genesisHeight prepared request recipients,
    guardHeld (accepted.dataIntent shape) guard

/-- Refuse a decision whose ordinary accepted intent omitted a recipient-law
dependency. The next event67 builder may retain extra read-only dependencies;
this entry point accepts only when the one actual native intent already holds
them (by read guard or by a write checking the identical physical pre-root). -/
def bind (native : CredentialSignatureIO.NativeConfig) (genesisHeight : Nat)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (request : RoomKeyReleaseCodec.Request) (signed : SignedCommand)
    (shape : PhysicalShape prepared) (accepted : AcceptedInvocation prepared signed) :
    IO (Except String (Bound genesisHeight prepared request signed shape accepted)) := do
  match ← checkRecipients native genesisHeight prepared request with
  | .error reason => return .error reason
  | .ok recipients =>
    if authorityExact : prepared.authority.readGuard.expectedRoot = request.authorityRoot then
      if authorityHeld : guardHeld (accepted.dataIntent shape) prepared.authority.readGuard then
        if retained : ∀ guard ∈ dependencies genesisHeight prepared request recipients,
            guardHeld (accepted.dataIntent shape) guard then
          return .ok ⟨recipients,authorityExact,authorityHeld,retained⟩
        else return .error "room release intent omitted a recipient-law dependency"
      else return .error "room release intent omitted authority root"
    else return .error "room release authority root is stale"

theorem recipient_current (genesisHeight : Nat)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (request : RoomKeyReleaseCodec.Request) (delivery : RoomKeyReleaseCodec.Delivery)
    (recipient : Recipient genesisHeight prepared request delivery) :
    CredentialAuthorityState.currentSigningKey ground.authority.logical
      recipient.claim.member = some recipient.recordSignature.selected.key :=
  recipient.recordSignature.selected.current

theorem all_recipient_dependencies_retained (genesisHeight : Nat)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (request : RoomKeyReleaseCodec.Request) (signed : SignedCommand)
    (shape : PhysicalShape prepared) (accepted : AcceptedInvocation prepared signed)
    (bound : Bound genesisHeight prepared request signed shape accepted)
    (guard : ReadGuard) (member : guard ∈ dependencies genesisHeight prepared request bound.recipients) :
    guardHeld (accepted.dataIntent shape) guard := bound.retained guard member

#assert_axioms recipient_current
#assert_axioms all_recipient_dependencies_retained
end Minidregg.Kernel.RoomReleaseCurrent
