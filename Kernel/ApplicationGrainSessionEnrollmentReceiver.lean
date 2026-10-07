/- One event28 CAS and receipt-only recovery, after the verifier's original event22 ticket join. -/
import Kernel.NativeHost

namespace Minidregg.Kernel.ApplicationGrainSessionEnrollmentReceiver

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource

set_option autoImplicit false

private def transaction (config : Config) (ingress : Ingress) :
    Option Minidregg.Theory.TypedAuthorization.Digest := do
  let (domain, semantics, signed) ←
    DeclaredResourceController.decodeSignedBytes ingress.signedBytes
  if domain != config.deployment.domain || semantics != config.profile.semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  some (DeclaredResourceController.transactionId domain semantics command)

/-- A missing transaction may be submitted once. Any occupied transaction
whose complete event or receipt differs is a conflict, never a retry signal. -/
def lookupVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (ingress : Ingress) :
    Option (Except String Receipt) := do
  let some tx := transaction config ingress
    | some (.error "noncanonical enrollment signed command")
  let some index := verified.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == tx)
    | none
  let some record := verified.opened.durable.image.accepted[index]?
    | some (.error "enrollment original record unavailable")
  let some receipt := verified.receipts[index]?
    | some (.error "enrollment original receipt unavailable")
  let event := ApplicationGrainSessionEnrollmentSource.event config.deployment.domain ingress
  if record.event == event && receipt.transactionId == tx &&
      receipt.eventId == event.eventId && receipt.acceptedCount == index + 1 then
    some (.ok receipt)
  else some (.error "enrollment transaction has a different original")

structure Confirmed (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : Ingress
  admitted : NativeHostReplay.SessionEnrollmentAt config old.opened ingress
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
  confirmation : DurableReceiverIO.Confirmation

def Confirmed.verified {config : Config} (confirmed : Confirmed config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate confirmed.old
        confirmed.readback.derived confirmed.readback.ready) :=
  NativeHostReplay.extendExact confirmed.old confirmed.readback

def Confirmed.receipt {config : Config} (confirmed : Confirmed config) : Receipt :=
  let old := confirmed.old
  let candidate := NativeHostReplay.exactCandidate old
    confirmed.readback.derived confirmed.readback.ready
  ⟨confirmed.readback.derived.intent.transactionId,
    confirmed.readback.derived.intent.event.eventId,
    old.opened.durable.height + 1,
    candidate.worldRoot⟩

theorem Confirmed.postRecord_exact {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent confirmed.readback.derived.intent) :=
  NativeHostReplay.extendExact_physicalRecord confirmed.old confirmed.readback

inductive Result (config : Config) where
  | confirmed (confirmed : Confirmed config)
  | historical (receipt : Receipt)
  | rejected (detail : String)
  | transactionConflict
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveVerified {config : Config} {target : Durable}
    (verified : NativeHostReplay.Verified config target) (bytes : List UInt8) :
    IO (Result config) := do
  let some ingress := ingressCodec.decode bytes
    | return .rejected "noncanonical enrollment ingress"
  unless ingress.canonicalBytes.toByteArray == bytes.toByteArray do
    return .rejected "noncanonical enrollment ingress"
  match lookupVerified verified ingress with
  | some (.ok receipt) => return .historical receipt
  | some (.error _) => return .transactionConflict
  | none =>
      let admitted ← match ← NativeHostReplay.admitSessionEnrollmentVerified verified ingress with
        | .error detail => return .rejected detail
        | .ok admitted => pure admitted
      let derived := admitted.toDerived
      let result ← DurableReceiverIO.receiveLoadedDetailed config.transport
        rootBytes verified.opened.durable derived.intent
      match result with
      | .exact kind appended =>
          match NativeHostReplay.ExactReadback.ofAppended verified derived appended with
          | .error detail => return .uncertain s!"enrollment post-image: {detail}"
          | .ok ⟨proof, proofDerived⟩ =>
                return .confirmed ⟨target, verified, ingress, admitted, proof,
                  ((congrArg NativeHostReplay.Derived.intent proofDerived).trans admitted.toDerived_intent), kind⟩
      | .ordinary ordinary =>
          match ordinary with
          | .confirmed _ _ => return .uncertain "enrollment lacks exact post-CAS readback"
          | .rejected _ => return .rejected "durable enrollment refused"
          | .contention => return .contention
          | .unavailable detail => return .unavailable detail
          | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationGrainSessionEnrollmentReceiver
