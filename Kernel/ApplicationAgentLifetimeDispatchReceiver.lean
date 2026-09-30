/-
Fresh event26 delivery authority. The historical ticket, grant, and reserve
must be joined by Replay, then the caller must win this exact physical CAS and
validate the complete successor. A recovered/already-present exact image is
receipt evidence, never another fd3 delivery permit.
-/
import Kernel.ApplicationAgentLifetimeDispatchProjection

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Permit (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationAgentLifetimeDispatchIngress.Ingress
  admitted : NativeHostReplay.LifetimeDispatchAt config old.opened ingress
  projection : ApplicationAgentLifetimeDispatchProjection.Paid
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
  freshCas : Bool
  freshInstalled : freshCas = true
  confirmation : DurableReceiverIO.Confirmation

def Permit.verified {config : Config} (permit : Permit config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate permit.old
        permit.readback.derived permit.readback.ready) :=
  NativeHostReplay.extendExact permit.old permit.readback

def Permit.receipt {config : Config} (permit : Permit config) : NativeHostCodec.Receipt :=
  let candidate := NativeHostReplay.exactCandidate permit.old
    permit.readback.derived permit.readback.ready
  ⟨permit.readback.derived.intent.transactionId,
    permit.readback.derived.intent.event.eventId,
    permit.old.opened.durable.image.accepted.length + 1,
    candidate.worldRoot⟩

theorem Permit.postRecord_exact {config : Config} (permit : Permit config) :
    permit.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent permit.readback.derived.intent) :=
  NativeHostReplay.extendExact_physicalRecord permit.old permit.readback

private def permitCodec : LawfulCodec
    (ApplicationAgentLifetimeDispatchProjection.Paid × NativeHostCodec.Receipt) :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-COMMITTED-PERMIT/v3".toUTF8.toList
    (StreamCodec.product ApplicationAgentLifetimeDispatchProjection.paidStream
      NativeHostCodec.receiptStream)

/-- This parser does not prove a CAS. It may inspect only the exact bytes
returned by the private source-owned receiver. -/
def inspectCommittedBytes (bytes : List UInt8) :
    Option (ApplicationAgentLifetimeDispatchProjection.Paid × NativeHostCodec.Receipt) :=
  permitCodec.decode bytes

private def Permit.canonicalBytes {config : Config} (permit : Permit config) : List UInt8 :=
  permitCodec.encode (permit.projection, permit.receipt)

/-- Point-in-time handoff; physical worker ownership and hard-disconnect
fences are still checked by the runtime before fd3 delivery. -/
def Permit.withFreshTip {config : Config} {α : Type} (permit : Permit config)
    (handoff : List UInt8 → IO α) : IO (Except String α) := do
  let .ok current ← DurableReceiverIO.tipIs config.transport
      permit.readback.appended.next.image.accepted.length permit.readback.appended.entry
    | return .error "lifetime dispatch physical tip unavailable before handoff"
  if current then
    return .ok (← handoff permit.canonicalBytes)
  else return .error "lifetime dispatch physical tip changed before handoff"

inductive Result (config : Config) where
  | permitted (permit : Permit config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationAgentLifetimeDispatchIngress.codec.decode bytes
    | return .rejected "noncanonical lifetime agent dispatch ingress"
  let .agent _ _ := ingress.dispatch.dispatch.dispatch.session.origin
    | return .rejected "lifetime dispatch requires agent-origin session"
  let .ok admitted ← NativeHostReplay.admitLifetimeDispatchVerified old ingress
    | return .rejected "lifetime dispatch history/current admission refused"
  let some projection := ApplicationAgentLifetimeDispatchProjection.ofLifetimeDispatchAt
      admitted
    | return .rejected "lifetime dispatch physical projection refused"
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "lifetime dispatch transaction identity already used"
  let (fresh, result) ← DurableReceiverIO.receiveLoadedDetailedWithFresh
    config.transport ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      if freshInstalled : fresh = true then
        match NativeHostReplay.ExactReadback.ofAppended old derived appended with
        | .error detail => return .uncertain s!"lifetime dispatch post-image validation: {detail}"
        | .ok ⟨proof, proofDerived⟩ =>
              return .permitted ⟨target, old, ingress, admitted, projection,
                proof, ((congrArg NativeHostReplay.Derived.intent proofDerived).trans admitted.toDerived_intent), fresh, freshInstalled, kind⟩
      else return .uncertain "lifetime dispatch exact readback without fresh CAS winner"
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "lifetime dispatch confirmation lacks fresh exact post-CAS readback"
      | .rejected _ => return .rejected "durable lifetime dispatch refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchReceiver
