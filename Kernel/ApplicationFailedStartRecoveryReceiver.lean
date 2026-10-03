/- Receive one governed failed START reconciliation against a verified native tip. Exact post-CAS readback is required for confirmation; an uncertain reply is recovered by receipt-only same-ingress lookup. -/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationFailedStartRecoveryReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Confirmed (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationFailedStartRecoveryIngress.Ingress
  admitted : NativeHostReplay.FailedStartRecoveryAt config old.opened ingress
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
  confirmation : DurableReceiverIO.Confirmation

def Confirmed.verified {config : Config} (confirmed : Confirmed config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate confirmed.old
        confirmed.readback.derived confirmed.readback.ready) :=
  NativeHostReplay.extendExact confirmed.old confirmed.readback

def Confirmed.receipt {config : Config} (confirmed : Confirmed config) :
    NativeHostCodec.Receipt :=
  let old := confirmed.old
  let candidate := NativeHostReplay.exactCandidate old
    confirmed.readback.derived confirmed.readback.ready
  ⟨confirmed.readback.derived.intent.transactionId,
    confirmed.readback.derived.intent.event.eventId,
    old.opened.durable.image.accepted.length + 1,
    candidate.worldRoot⟩

theorem Confirmed.event_exact {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.derived.intent.event =
      ApplicationFailedStartRecoveryIngress.event confirmed.ingress := by
  rw [confirmed.derivedExact]
  exact ApplicationFailedStartRecoveryCore.intent_event confirmed.admitted.conditional

theorem Confirmed.postRecord_exact {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent confirmed.readback.derived.intent) :=
  NativeHostReplay.extendExact_physicalRecord confirmed.old confirmed.readback

inductive Result (config : Config) where
  | confirmed (confirmed : Confirmed config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationFailedStartRecoveryIngress.codec.decode bytes
    | return .rejected "noncanonical checked lifecycle failed START recovery ingress"
  let admitted ← match ← NativeHostReplay.admitFailedStartRecoveryVerified old ingress with
    | .error detail => return .rejected detail
    | .ok admitted => pure admitted
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "checked lifecycle failed START recovery transaction identity already used"
  let result ← DurableReceiverIO.receiveLoadedDetailed config.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      match NativeHostReplay.ExactReadback.ofAppended old derived appended with
      | .error detail => return .uncertain s!"checked lifecycle failed START recovery post-image: {detail}"
      | .ok ⟨proof, proofDerived⟩ =>
            return .confirmed ⟨target, old, ingress, admitted, proof,
              ((congrArg NativeHostReplay.Derived.intent proofDerived).trans admitted.toDerived_intent), kind⟩
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "checked lifecycle failed START recovery lacks exact post-CAS readback"
      | .rejected _ => return .rejected "durable checked lifecycle failed START recovery refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationFailedStartRecoveryReceiver
