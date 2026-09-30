/-
Fresh paid agent dispatch. An event21 permit exists only after same-tip native
admission, one durable CAS, exact complete post-image readback and validation.
Decoding a candidate or an old receipt cannot mint delivery authority.
-/
import Kernel.ApplicationDispatchAgentProjection

namespace Minidregg.Kernel.ApplicationDispatchAgentReceiver

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
  ingress : ApplicationDispatchAgentIngress.Ingress
  admitted : NativeHostReplay.AgentDispatchAt config old.opened ingress
  projection : ApplicationDispatchAgentProjection.Paid
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
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
    worldRoot config candidate.image⟩

theorem Permit.postBytes_exact {config : Config} (permit : Permit config) :
    permit.verified.opened.durable.bytes = permit.readback.physicalBytes :=
  NativeHostReplay.extendExact_physicalBytes permit.old permit.readback

private def permitCodec : LawfulCodec
    (ApplicationDispatchAgentProjection.Paid × NativeHostCodec.Receipt) :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-DISPATCH-COMMITTED-PERMIT/v2".toUTF8.toList
    (StreamCodec.product ApplicationDispatchAgentProjection.paidStream
      NativeHostCodec.receiptStream)

/-- Strict frame inspection is read-only; it does not prove a CAS. Host may
inspect only the exact bytes received from its private op46 process. -/
def inspectCommittedBytes (bytes : List UInt8) :
    Option (ApplicationDispatchAgentProjection.Paid × NativeHostCodec.Receipt) :=
  permitCodec.decode bytes

private def Permit.canonicalBytes {config : Config} (permit : Permit config) : List UInt8 :=
  permitCodec.encode (permit.projection, permit.receipt)

/-- A point-in-time native response handoff, not a lease across the later
physical fd3 hop. Host must also check the live parent/purse process fences. -/
def Permit.withFreshTip {config : Config} {α : Type} (permit : Permit config)
    (handoff : List UInt8 → IO α) : IO (Except String α) := do
  let .ok (some current) ← config.storage.transport.read
    | return .error "agent dispatch physical tip unavailable before handoff"
  if exact : current.toByteArray == permit.readback.physicalBytes.toByteArray then
    have _currentExact : current = permit.readback.physicalBytes :=
      (DurableReceiverIO.byteArray_beq_exact _ _).mp exact
    return .ok (← handoff permit.canonicalBytes)
  else return .error "agent dispatch physical tip changed before handoff"

inductive Result (config : Config) where
  | permitted (permit : Permit config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationDispatchAgentIngress.codec.decode bytes
    | return .rejected "noncanonical paid agent dispatch ingress"
  let .agent _ _ := ingress.dispatch.dispatch.dispatch.session.origin
    | return .rejected "paid agent dispatch requires agent-origin session"
  let .ok admitted ← NativeHostReplay.admitAgentDispatchVerified old ingress
    | return .rejected "agent dispatch native admission or prior reserve refused"
  let some projection := ApplicationDispatchAgentProjection.ofAgentDispatchAt admitted
    | return .rejected "agent dispatch physical projection refused"
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "agent dispatch transaction identity already used"
  let result ← DurableReceiverIO.receiveLoadedDetailed config.storage.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind ready preparedEq readback readbackExact =>
      let candidate := NativeHostReplay.exactCandidate old derived ready
      match validated : validateLoaded config candidate with
      | .error detail => return .uncertain s!"agent dispatch post-image validation: {detail}"
      | .ok after =>
          if afterExact : after.durable.bytes.toByteArray == candidate.bytes.toByteArray then
            let proof : NativeHostReplay.ExactReadback config old :=
              { derived := derived
                ready := ready
                prepared := preparedEq
                physicalBytes := readback
                exactBytes := readbackExact
                after := after
                validated := validated
                afterExact := (DurableReceiverIO.byteArray_beq_exact _ _).mp afterExact }
            return .permitted ⟨target, old, ingress, admitted, projection,
              proof, admitted.toDerived_intent, kind⟩
          else return .uncertain "agent dispatch validated successor bytes changed"
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "agent dispatch confirmation lacks exact fresh post-CAS readback"
      | .rejected _ => return .rejected "durable agent dispatch refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationDispatchAgentReceiver
