/-
Exact-CAS receiving for the versioned repeat-CREATE BEGIN (event69). It
records a durable pending operation after a governed failed-START recovery,
not physical execution. The recovery is selected from the Verified walk's own
admitted chronology; the v3 first-attempt marker is never cleared.
-/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleRetryBeginV4Receiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Confirmed (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationLifecycleRetryBeginV4Ingress.Ingress
  admitted : NativeHostReplay.BeginAtV4 config old.opened ingress
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
  confirmation : DurableReceiverIO.Confirmation
  store : DurableHistory.StoreIdentity
  reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store

def Confirmed.verified {config : Config} (confirmed : Confirmed config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate confirmed.old
        confirmed.readback.derived confirmed.readback.ready) :=
  NativeHostReplay.extendExact confirmed.reader confirmed.old confirmed.readback

def Confirmed.receipt {config : Config} (confirmed : Confirmed config) :
    NativeHostCodec.Receipt :=
  let candidate := NativeHostReplay.exactCandidate confirmed.old
    confirmed.readback.derived confirmed.readback.ready
  ⟨confirmed.readback.derived.intent.transactionId,
    confirmed.readback.derived.intent.event.eventId,
    confirmed.old.opened.durable.height + 1,
    candidate.worldRoot⟩

theorem Confirmed.event_exact {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.derived.intent.event =
      ApplicationLifecycleRetryBeginV4Admission.event confirmed.ingress := by
  rw [confirmed.derivedExact]
  rfl

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
  let some ingress := ApplicationLifecycleRetryBeginV4Ingress.codec.decode bytes
    | return .rejected "noncanonical retry BEGIN ingress"
  let admitted ← match ← NativeHostReplay.admitRetryBeginV4Verified old ingress with
    | .error detail => return .rejected detail
    | .ok admitted => pure admitted
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "retry BEGIN transaction identity already used"
  let result ← DurableReceiverIO.receiveLoadedDetailed config.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      match NativeHostReplay.ExactReadback.ofAppended old derived appended with
      | .error detail => return .uncertain s!"retry BEGIN post-image: {detail}"
      | .ok ⟨proof, proofDerived⟩ =>
            match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes appended.next with
            | .error detail => return .uncertain s!"post-append history reader: {detail}"
            | .ok ⟨_, reader⟩ =>
              return .confirmed ⟨target, old, ingress, admitted, proof,
                ((congrArg NativeHostReplay.Derived.intent proofDerived).trans
                  admitted.toDerived_intent), kind, _, reader⟩
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "retry BEGIN lacks exact post-CAS readback"
      | .rejected _ => return .rejected "durable retry BEGIN refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationLifecycleRetryBeginV4Receiver
