/-
Fresh launch-bound physical lifecycle completion. The original v3 claim is bound
to the same native-admitted chronological Replay context, the host custodian
report and current law are checked, and the exact event-25 intent is submitted
once through one CAS with complete physical post-image readback.
-/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleCompletionV2Receiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Confirmed (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationLifecycleCompletionV2Ingress.Ingress
  admitted : NativeHostReplay.CompletionAtV2 config old.opened ingress
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
    worldRoot config candidate.image⟩

theorem Confirmed.event_exact {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.derived.intent.event =
      ApplicationLifecycleCompletionV2Ingress.event confirmed.ingress := by
  rw [confirmed.derivedExact]
  exact ApplicationLifecycleCompletionV2Core.intent_event confirmed.admitted.conditional

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
  let some ingress := ApplicationLifecycleCompletionV2Ingress.codec.decode bytes
    | return .rejected "noncanonical checked lifecycle completion ingress"
  let admitted ← match ← NativeHostReplay.admitCompletionV2Verified old ingress with
    | .error detail => return .rejected detail
    | .ok admitted => pure admitted
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "checked lifecycle completion transaction identity already used"
  let result ← DurableReceiverIO.receiveLoadedDetailed config.storage.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      match NativeHostReplay.ExactReadback.ofAppended old derived appended with
      | .error detail => return .uncertain s!"checked lifecycle completion post-image: {detail}"
      | .ok ⟨proof, proofDerived⟩ =>
            return .confirmed ⟨target, old, ingress, admitted, proof,
              ((congrArg NativeHostReplay.Derived.intent proofDerived).trans admitted.toDerived_intent), kind⟩
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "checked lifecycle completion lacks exact post-CAS readback"
      | .rejected _ => return .rejected "durable checked lifecycle completion refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationLifecycleCompletionV2Receiver
