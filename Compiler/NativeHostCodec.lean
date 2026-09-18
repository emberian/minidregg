/-
Strict source-owned host framing. These are transport products over actual
controller bytes, not a second executor or an authority assertion. Each
operation's existing strict receiving codec still decodes its inner payload.
No raw DataIntent, supplied height, profile, or post-state is a call variant.
-/
import Compiler.NativeHostProfile
import Kernel.DeclaredResourceController
import Kernel.PolicyInstallReceiver
import Kernel.ResourceBirthReceiver
import Kernel.CapabilityDelegationReceiver

namespace Minidregg.Compiler.NativeHostCodec

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel

set_option autoImplicit false

/-- One source-owned commitment for host receipts and observation challenges.
No caller chooses a replacement image summary or a digest algorithm. -/
def imageBoundary (domain semantics : Digest) (image : DurableReceiver.Image) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.IMAGE-BOUNDARY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, DurableReceiverCodec.encode image))).digest

def framed {α : Type} (frame : List UInt8) (stream : StreamCodec α) : LawfulCodec α :=
  ResourceBirthCodec.strictCodec
    { encode value := frame ++ stream.encode value
      decode bytes := if bytes.take frame.length = frame then
        stream.toLawful.decode (bytes.drop frame.length) else none
      decode_encode := by
        intro value
        have exact := stream.toLawful.decode_encode value
        change stream.toLawful.decode (stream.encode value) = some value at exact
        simp [exact] }

theorem framed_canonical {α : Type} (frame : List UInt8) (stream : StreamCodec α)
    {bytes : List UInt8} {value : α}
    (decoded : (framed frame stream).decode bytes = some value) :
    (framed frame stream).encode value = bytes :=
  ResourceBirthCodec.strictCodec_canonical _ decoded

def signedInvocationStream : StreamCodec DeclaredResourceController.SignedCommand :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product bytesStream bytesStream))
    (fun value => (value.commandBytes, value.targetEnvelope, value.authorityEnvelope))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro value; cases value; rfl)

inductive SignedCall where
  | birth (ingress : List UInt8)
  | invoke (ingress : DeclaredResourceController.SignedCommand)
  | install (ingress : List UInt8)
  | delegate (ingress : List UInt8)

abbrev CallWire := Sum (List UInt8)
  (Sum DeclaredResourceController.SignedCommand (Sum (List UInt8) (List UInt8)))

def SignedCall.toWire : SignedCall → CallWire
  | .birth bytes => .inl bytes
  | .invoke signed => .inr (.inl signed)
  | .install bytes => .inr (.inr (.inl bytes))
  | .delegate bytes => .inr (.inr (.inr bytes))

def SignedCall.ofWire : CallWire → SignedCall
  | .inl bytes => .birth bytes
  | .inr (.inl signed) => .invoke signed
  | .inr (.inr (.inl bytes)) => .install bytes
  | .inr (.inr (.inr bytes)) => .delegate bytes

def callStream : StreamCodec SignedCall :=
  StreamCodec.xmap (StreamCodec.sum bytesStream
    (StreamCodec.sum signedInvocationStream (StreamCodec.sum bytesStream bytesStream)))
    SignedCall.toWire SignedCall.ofWire (by intro value; cases value <;> rfl)

def callCodec : LawfulCodec SignedCall :=
  framed "DREGG/NATIVE-HOST/SIGNED-CALL/v1".toUTF8.toList callStream

/-- The capability choices are supplied for the ordered conserved debit legs;
all request coordinates and physical auxiliary allocations are source-derived. -/
inductive Draft where
  | birth (descriptor : List UInt8) (sourceCapabilities : List CapabilityId)
  | invoke (command : List UInt8)
  | install (subject : SubjectId) (control : CapabilityId) (declaration : List UInt8)
  | delegate (command : List UInt8)
  deriving DecidableEq, Repr

abbrev DraftWire := Sum (List UInt8 × List CapabilityId)
  (Sum (List UInt8) (Sum (SubjectId × CapabilityId × List UInt8) (List UInt8)))

def Draft.toWire : Draft → DraftWire
  | .birth bytes capabilities => .inl (bytes, capabilities)
  | .invoke bytes => .inr (.inl bytes)
  | .install subject control bytes => .inr (.inr (.inl (subject, control, bytes)))
  | .delegate bytes => .inr (.inr (.inr bytes))

def Draft.ofWire : DraftWire → Draft
  | .inl (bytes, capabilities) => .birth bytes capabilities
  | .inr (.inl bytes) => .invoke bytes
  | .inr (.inr (.inl (subject, control, bytes))) => .install subject control bytes
  | .inr (.inr (.inr bytes)) => .delegate bytes

def draftStream : StreamCodec Draft :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.product bytesStream
      (StreamCodec.list CredentialAuthorityEntryCodec.capabilityIdStream))
      (StreamCodec.sum bytesStream
        (StreamCodec.sum (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
          (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream bytesStream)) bytesStream)))
    Draft.toWire Draft.ofWire (by intro value; cases value <;> rfl)

def draftCodec : LawfulCodec Draft :=
  framed "DREGG/NATIVE-HOST/DRAFT/v1".toUTF8.toList draftStream

/-- `role,index` is an ordered incidence label, not a user-selected authority.
The exact canonical header names the chosen key and full typed request. -/
structure SigningSlot where
  role : Nat
  index : Nat
  header : List UInt8
  deriving DecidableEq, Repr

def signingSlotStream : StreamCodec SigningSlot :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat bytesStream))
    (fun value => (value.role, value.index, value.header))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩) (by intro value; cases value; rfl)

structure SigningPlan where
  domain : Digest
  semantics : Digest
  imageBoundary : Digest
  height : Nat
  finalizedDraft : Draft
  slots : List SigningSlot

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
        (StreamCodec.product draftStream (StreamCodec.list signingSlotStream))))))
    (fun value => (value.domain, value.semantics, value.imageBoundary, value.height,
      value.finalizedDraft, value.slots))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2⟩) (by intro value; cases value; rfl)

def signingPlanCodec : LawfulCodec SigningPlan :=
  framed "DREGG/NATIVE-HOST/SIGNING-PLAN/v1".toUTF8.toList signingPlanStream

structure Receipt where
  transactionId : Digest
  eventId : Digest
  /-- Number of accepted entries through this transaction, not the current tip. -/
  acceptedCount : Nat
  imageBoundary : Digest
  deriving DecidableEq, Repr

def receiptStream : StreamCodec Receipt :=
  StreamCodec.xmap (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat digestStream)))
    (fun value => (value.transactionId, value.eventId, value.acceptedCount, value.imageBoundary))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro value; cases value; rfl)

def confirmationStream : StreamCodec DurableReceiverIO.Confirmation :=
  StreamCodec.xmap (StreamCodec.sum StreamCodec.bool StreamCodec.bool)
    (fun value => match value with
      | .installed => .inl false
      | .recoveredAfterUncertainResponse => .inl true
      | .replayed => .inr false)
    (fun wire => match wire with
      | .inl false => .installed
      | .inl true => .recoveredAfterUncertainResponse
      | .inr _ => .replayed)
    (by intro value; cases value <;> rfl)

/-- Refusal payload is a stable source-selected phase plus a diagnostic. It
does not contain internal snapshots, journals, capability records or intents. -/
inductive Outcome where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | refused (phase : List UInt8) (detail : List UInt8)
  | contention
  | unavailable (detail : List UInt8)
  | uncertain (detail : List UInt8)
  | absent

abbrev OutcomeWire := Sum (DurableReceiverIO.Confirmation × Receipt)
  (Sum (List UInt8 × List UInt8) (Sum Bool (Sum (List UInt8) (List UInt8))))

def Outcome.toWire : Outcome → OutcomeWire
  | .confirmed kind receipt => .inl (kind, receipt)
  | .refused phase detail => .inr (.inl (phase, detail))
  | .contention => .inr (.inr (.inl false))
  | .absent => .inr (.inr (.inl true))
  | .unavailable detail => .inr (.inr (.inr (.inl detail)))
  | .uncertain detail => .inr (.inr (.inr (.inr detail)))

def Outcome.ofWire : OutcomeWire → Outcome
  | .inl (kind, receipt) => .confirmed kind receipt
  | .inr (.inl (phase, detail)) => .refused phase detail
  | .inr (.inr (.inl false)) => .contention
  | .inr (.inr (.inl true)) => .absent
  | .inr (.inr (.inr (.inl detail))) => .unavailable detail
  | .inr (.inr (.inr (.inr detail))) => .uncertain detail

def outcomeStream : StreamCodec Outcome :=
  StreamCodec.xmap
    (StreamCodec.sum (StreamCodec.product confirmationStream receiptStream)
      (StreamCodec.sum (StreamCodec.product bytesStream bytesStream)
        (StreamCodec.sum StreamCodec.bool (StreamCodec.sum bytesStream bytesStream))))
    Outcome.toWire Outcome.ofWire (by intro value; cases value <;> rfl)

def outcomeCodec : LawfulCodec Outcome :=
  framed "DREGG/NATIVE-HOST/OUTCOME/v1".toUTF8.toList outcomeStream

@[simp] theorem call_roundtrip (value : SignedCall) :
    callCodec.decode (callCodec.encode value) = some value := callCodec.decode_encode value

@[simp] theorem plan_roundtrip (value : SigningPlan) :
    signingPlanCodec.decode (signingPlanCodec.encode value) = some value :=
  signingPlanCodec.decode_encode value

@[simp] theorem outcome_roundtrip (value : Outcome) :
    outcomeCodec.decode (outcomeCodec.encode value) = some value := outcomeCodec.decode_encode value

theorem call_canonical {bytes : List UInt8} {value : SignedCall}
    (decoded : callCodec.decode bytes = some value) : callCodec.encode value = bytes :=
  framed_canonical _ _ decoded

theorem plan_canonical {bytes : List UInt8} {value : SigningPlan}
    (decoded : signingPlanCodec.decode bytes = some value) : signingPlanCodec.encode value = bytes :=
  framed_canonical _ _ decoded

theorem outcome_canonical {bytes : List UInt8} {value : Outcome}
    (decoded : outcomeCodec.decode bytes = some value) : outcomeCodec.encode value = bytes :=
  framed_canonical _ _ decoded

end Minidregg.Compiler.NativeHostCodec
