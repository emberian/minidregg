/- Room-key release is a two-phase governed operation. A request transmits
only delivery commitments, not ciphertext for an already used key. Only a
source-applied release decision permits the ciphertext publication. This codec
binds every field canonically; it neither grants authority nor enables a route.
The registered native statement/controller must consume this exact body. -/
import Compiler.CurrentRecipientRecord
import Compiler.Sp800185Cshake256
import Compiler.ResourceBirthCodec

namespace Minidregg.Compiler.RoomKeyReleaseCodec
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false

structure Epoch where
  room : Nat
  keysCell : Nat
  epoch : Nat
  parent : List UInt8
  keyCommitment : List UInt8
  signer : SubjectId
  signerEpoch : Nat
  signerPublic : List UInt8
  signature : List UInt8
  deriving DecidableEq

/-- Exact Rust v1 epoch wire. Numeric width refusal precedes publication. -/
def Epoch.bounded (e : Epoch) : Prop := e.room < 2^64 ∧ e.keysCell < 2^64 ∧
  e.epoch < 2^31 ∧ e.parent.length = 32 ∧ e.keyCommitment.length = 32 ∧
  e.signer.value < 2^64 ∧ e.signerEpoch < 2^32 ∧ e.signerPublic.length = 32 ∧
  e.signature.length = 64
instance (e : Epoch) : Decidable e.bounded := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def Epoch.body (e : Epoch) : List UInt8 :=
  CurrentRecipientRecord.bigEndian 8 e.room ++ CurrentRecipientRecord.bigEndian 8 e.keysCell ++
  CurrentRecipientRecord.bigEndian 4 e.epoch ++ e.parent ++ e.keyCommitment ++
  CurrentRecipientRecord.bigEndian 8 e.signer.value ++
  CurrentRecipientRecord.bigEndian 4 e.signerEpoch ++ e.signerPublic

def Epoch.statement (e : Epoch) : List UInt8 :=
  "DREGG/PRIVATE-ROOM-EPOCH/v1".toUTF8.toList ++ [1] ++ e.body

def Epoch.bytes (e : Epoch) : List UInt8 := e.body ++ e.signature

def lineageDigest (parts : List (List UInt8)) : List UInt8 :=
  (Sp800185Cshake256.hash "DREGG.PRIVATE-ROOM.LINEAGE/v1".toUTF8.toList
    (parts.flatMap fun part => CurrentRecipientRecord.bigEndian 8 part.length ++ part)).bytes

def Epoch.identity (e : Epoch) : List UInt8 := lineageDigest [e.statement]

def decodeEpoch (bytes : List UInt8) : Option Epoch := do
  if bytes.length != 192 then none else
  let e : Epoch := ⟨CurrentRecipientRecord.readBigEndian (bytes.take 8),
    CurrentRecipientRecord.readBigEndian ((bytes.drop 8).take 8),
    CurrentRecipientRecord.readBigEndian ((bytes.drop 16).take 4),
    (bytes.drop 20).take 32,(bytes.drop 52).take 32,
    ⟨CurrentRecipientRecord.readBigEndian ((bytes.drop 84).take 8)⟩,
    CurrentRecipientRecord.readBigEndian ((bytes.drop 92).take 4),
    (bytes.drop 96).take 32,bytes.drop 128⟩
  if e.bounded ∧ e.bytes = bytes then some e else none

structure Delivery where
  member : Nat
  /-- The complete member-signed 148-byte record, checked against the SAME
  Prepared credential snapshot by the source release controller. -/
  record : List UInt8
  roomCapability : Nat
  /-- Independent recipient entitlement envelope when demanded by the source
  audience law. The recipient-key signature is NOT an observe signature. -/
  entitlementEnvelope : List UInt8
  /-- cSHAKE lineage-domain digest of the exact complete 444-byte delivery.
  Ciphertext stays local until the release transition is source Applied. -/
  ciphertextCommitment : List UInt8
  atom : Nat
  deriving DecidableEq

def deliveryStream : StreamCodec Delivery :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream
    (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream
    (StreamCodec.product bytesStream StreamCodec.nat)))))
    (fun d => (d.member,d.record,d.roomCapability,d.entitlementEnvelope,d.ciphertextCommitment,d.atom))
    (fun (m,r,rc,re,c,a) => ⟨m,r,rc,re,c,a⟩) (by intro d; cases d; rfl)

structure Request where
  room : Nat
  keysCell : Nat
  /-- An ordinary governed durable content resource for the release decision.
  Its creation and mutation require actual current source rights. -/
  decisionCell : Nat
  keysRoot : Digest
  decisionRoot : Digest
  authorityRoot : Digest
  priorEpoch : Option Nat
  priorIdentity : List UInt8
  certificate : List UInt8
  actor : SubjectId
  capability : Nat
  operation : List UInt8
  deliveries : List Delivery
  deriving DecidableEq

/-- Structural admission is separate from signature/law/current-head checks.
An existing epoch retains its exact certificate identity; rotation advances
exactly once and names that identity as its parent. -/
def Request.shape (r : Request) (e : Epoch) : Prop :=
  e.bounded ∧ e.bytes = r.certificate ∧ e.room = r.room ∧ e.keysCell = r.keysCell ∧
  r.room < 2^64 ∧ r.keysCell < 2^64 ∧ r.actor.value < 2^64 ∧
  r.operation.length = 32 ∧ r.priorIdentity.length = 32 ∧
  r.decisionCell = r.keysCell ∧ r.deliveries.length > 0 ∧ r.deliveries.length ≤ 64 ∧
  (r.deliveries.map Delivery.member).Nodup ∧
  (r.deliveries.map Delivery.atom).Nodup ∧
  (match r.priorEpoch with
   | none => e.epoch = 0 ∧ e.parent = List.replicate 32 0 ∧
       r.priorIdentity = List.replicate 32 0 ∧ e.signer = r.actor
   | some prior =>
       (e.epoch = prior ∧ e.identity = r.priorIdentity) ∨
       (e.epoch = prior + 1 ∧ e.parent = r.priorIdentity ∧ e.signer = r.actor)) ∧
  (∀ d ∈ r.deliveries, d.member < 2^64 ∧ d.ciphertextCommitment.length = 32 ∧
    ∃ claim, CurrentRecipientRecord.decode ⟨d.member⟩ d.record = some claim ∧
      claim.room = r.room ∧ claim.keysCell = r.keysCell ∧
      d.atom = (e.epoch + 1) * 2^96 + claim.epoch * 2^64 + d.member)

/-- A request carries no room key and no delivery ciphertext. It identifies
one decision resource/CAS, one prior lineage and every exact release scope. -/
def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product (StreamCodec.option StreamCodec.nat) (StreamCodec.product bytesStream
    (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product bytesStream
    (StreamCodec.list deliveryStream)))))))))))))
    (fun r => (r.room,r.keysCell,r.decisionCell,r.keysRoot,r.decisionRoot,r.authorityRoot,
      r.priorEpoch,r.priorIdentity,r.certificate,r.actor.value,r.capability,r.operation,r.deliveries))
    (fun (room,keys,decision,kr,dr,ar,pe,pi,c,actor,cap,op,ds) =>
      ⟨room,keys,decision,kr,dr,ar,pe,pi,c,⟨actor⟩,cap,op,ds⟩)
    (by intro r; cases r; rfl)

def frame : List UInt8 := "DREGG/PRIVATE-ROOM/RELEASE-REQUEST".toUTF8.toList ++ [1]
def rawCodec : LawfulCodec Request where
  encode r := frame ++ requestStream.encode r
  decode bytes := if bytes.take frame.length = frame then
    requestStream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro r
    have exact := requestStream.toLawful.decode_encode r
    change requestStream.toLawful.decode (requestStream.encode r) = some r at exact
    simp [exact]

def codec : LawfulCodec Request := ResourceBirthCodec.strictCodec rawCodec
abbrev encode := codec.encode
abbrev decode := codec.decode

@[simp] theorem decode_encode (r : Request) : decode (encode r) = some r := codec.decode_encode r

theorem encode_injective {left right : Request} (same : encode left = encode right) : left = right := by
  have decoded := congrArg decode same
  simpa only [decode_encode,Option.some.injEq] using decoded

theorem decoded_canonical {bytes : List UInt8} {r : Request}
    (accepted : decode bytes = some r) : encode r = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCodec accepted

/-- Canonical equality binds recipients/records/ciphertext commitments together
with authority/key roots and the exact retained operation. It does not assert
collision resistance, current authority, or native Applied from parsed bytes. -/
theorem same_bytes_bind_release {left right : Request} (same : encode left = encode right) :
    left.authorityRoot = right.authorityRoot ∧ left.keysRoot = right.keysRoot ∧
    left.certificate = right.certificate ∧ left.operation = right.operation ∧
    left.deliveries = right.deliveries := by
  cases encode_injective same
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

#assert_axioms decode_encode
#assert_axioms encode_injective
#assert_axioms decoded_canonical
#assert_axioms same_bytes_bind_release
end Minidregg.Compiler.RoomKeyReleaseCodec
