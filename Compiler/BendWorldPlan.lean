/- Common method result ABI. Ordered native typed payloads are reused wholesale:
content, append, definitions and world actions do not get separate language
interpreters. Authority remains the actual receiver's current checks. -/
import Kernel.ResourceTransaction
import Compiler.BendWorldProgramCodec

namespace Minidregg.Compiler.BendWorldPlan
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

structure Effect where
  target : Nat
  payload : Payload
  deriving DecidableEq, Repr

/-- An independent return slot. Its plaintext schema and encrypted encoding are
distinct. A backend must establish their correspondence; opaque ciphertext
storage by itself does not prove a Boolean or any other plaintext predicate. -/
structure ReturnSlot where
  name : String
  valueSchema : Digest
  encoding : Digest
  recipient : SubjectId
  keyEpoch : Digest
  audience : Digest
  generation : Nat
  bytes : List UInt8
  deriving DecidableEq, Repr

structure Plan where
  effects : List Effect
  returns : List ReturnSlot
  /-- Declared computation reads; actual admission also retains all implicit
  authority, source, schema, tariff and audience roots. -/
  reads : List ReadGuard

def effectStream : StreamCodec Effect :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat payloadStream)
    (fun e => (e.target, e.payload)) (fun e => ⟨e.1, e.2⟩)
    (by intro e; cases e; rfl)

def returnStream : StreamCodec ReturnSlot :=
  StreamCodec.xmap (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat bytesStream)))))))
    (fun r => (r.name, r.valueSchema, r.encoding, r.recipient, r.keyEpoch,
      r.audience, r.generation, r.bytes))
    (fun r => ⟨r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2.1,
      r.2.2.2.2.2.1, r.2.2.2.2.2.2.1, r.2.2.2.2.2.2.2⟩)
    (by intro r; cases r; rfl)

def returnFrame : List UInt8 := "DREGG/BEND/RETURN-SLOT/v1".toUTF8.toList
def encodeReturn (r : ReturnSlot) : List UInt8 := returnFrame ++ returnStream.encode r
def decodeReturn (bytes : List UInt8) : Option ReturnSlot :=
  NockProgramCodec.framedDecode returnFrame returnStream bytes

def returnId (r : ReturnSlot) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.RETURN/v1".toUTF8.toList (encodeReturn r)).digest

/-- Monetary consent fields authorize the batch, while the source program
produces the complete semantic Book operation sequence. Their full signed legs
remain in native admission, read/authority guards and the accepted trace. -/
def moneyEffect (target : Nat) (consent : ResourceMoneyWire.Consent) : Option Effect :=
  consent.batch.map fun batch => ⟨target, .moneyConsent ⟨some batch, [], none⟩⟩

theorem exact_money_batch (target : Nat) (consent : ResourceMoneyWire.Consent)
    (batch : ResourceMoneyWire.ApplicationBatch) (present : consent.batch = some batch) :
    moneyEffect target consent = some ⟨target, .moneyConsent ⟨some batch, [], none⟩⟩ := by
  simp [moneyEffect, present]

/-- Compute the exact ordered application effects from a native command.
Observation and validated accounting legs are not arbitrary application writes. -/
def effectsOf (command : Command) : List Effect :=
  (List.finRange command.targets.length).filterMap fun index =>
    match command.targets[index].payload with
    | .read | .kindRead | .computeFunding _ => none
    | .moneyConsent consent => moneyEffect index.val consent
    | payload => some ⟨index.val, payload⟩

def matchesCommand (plan : Plan) (command : Command) : Bool :=
  decide (plan.effects = effectsOf command) &&
  decide ((plan.returns.map ReturnSlot.name).Nodup) &&
  plan.returns.all (fun r => BendWorldSource.nameValid r.name)

theorem ordered_payloads_exact {plan : Plan} {command : Command}
    (h : matchesCommand plan command = true) : plan.effects = effectsOf command := by
  simp only [matchesCommand, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem return_roundtrip (r : ReturnSlot) : decodeReturn (encodeReturn r) = some r :=
  NockProgramCodec.framedDecode_encode returnFrame returnStream r

theorem return_canonical {bytes : List UInt8} {r : ReturnSlot}
    (h : decodeReturn bytes = some r) : encodeReturn r = bytes :=
  NockProgramCodec.framedDecode_canonical h

end Minidregg.Compiler.BendWorldPlan
