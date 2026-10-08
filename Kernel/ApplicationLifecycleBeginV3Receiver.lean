/-
Exact-CAS receiving for launch-bound lifecycle BEGIN. Event23 records a durable
pending operation, not physical execution. Continue admission is gated by the
Verified original completed-create certificate in NativeHostReplay.
-/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleBeginV3Receiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Confirmed (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationLifecycleBeginV3Ingress.Ingress
  readback : NativeHostReplay.ExactReadback config old
  eventExact : readback.derived.intent.event =
    ApplicationLifecycleBeginV3Ingress.event ingress
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
  let some ingress := ApplicationLifecycleBeginV3Ingress.codec.decode bytes
    | return .rejected "noncanonical launch-bound lifecycle BEGIN"
  let .ok derived ← NativeHostReplay.admitBeginV3Verified old ingress
    | return .rejected "current launch-bound lifecycle BEGIN refused"
  if eventExact : derived.intent.event = ApplicationLifecycleBeginV3Ingress.event ingress then
    if old.opened.durable.image.accepted.findIdx?
        (fun record => record.transactionId == derived.intent.transactionId) != none then
      return .rejected "launch-bound BEGIN transaction identity already used"
    let result ← DurableReceiverIO.receiveLoadedDetailed config.transport
      ResourceBirthCodec.rootBytes old.opened.durable derived.intent
    match result with
    | .exact kind appended =>
        match NativeHostReplay.ExactReadback.ofAppended old derived appended with
        | .error detail => return .uncertain s!"v3 lifecycle BEGIN post-image: {detail}"
        | .ok ⟨proof, proofDerived⟩ =>
              match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes appended.next with
              | .error detail => return .uncertain s!"post-append history reader: {detail}"
              | .ok ⟨_, reader⟩ =>
                return .confirmed ⟨target, old, ingress, proof, (by rw [proofDerived]; exact eventExact), kind, _, reader⟩
    | .ordinary ordinary =>
        match ordinary with
        | .confirmed _ _ =>
            return .uncertain "v3 lifecycle BEGIN lacks exact post-CAS readback"
        | .rejected _ => return .rejected "durable v3 lifecycle BEGIN refused"
        | .contention => return .contention
        | .unavailable detail => return .unavailable detail
        | .uncertain detail => return .uncertain detail
  else return .rejected "source-admitted v3 BEGIN event differs from ingress"

end Minidregg.Kernel.ApplicationLifecycleBeginV3Receiver
