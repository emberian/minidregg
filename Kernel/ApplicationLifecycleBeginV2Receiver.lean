/-
Fresh exact-CAS receiving for descriptor-bound lifecycle BEGIN. A confirmed
BEGIN records pending physical work only. It never emits a launch permit.
Historical v1 BEGIN remains a replay grammar, not a fresh submit path here.
-/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleBeginV2Receiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Confirmed (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationLifecycleBeginV2Ingress.Ingress
  accepted : ApplicationLifecycleBeginV2Admission.Accepted
    config.deployment config.profile
    ⟨config.federation, logicalHeight config old.opened.durable⟩
    old.opened.ground ingress
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = accepted.intent
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
  let old := confirmed.old
  let candidate := NativeHostReplay.exactCandidate old
    confirmed.readback.derived confirmed.readback.ready
  ⟨confirmed.readback.derived.intent.transactionId,
    confirmed.readback.derived.intent.event.eventId,
    old.opened.durable.height + 1,
    candidate.worldRoot⟩

theorem Confirmed.event_exact {config : Config} (confirmed : Confirmed config) :
    confirmed.readback.derived.intent.event =
      ApplicationLifecycleBeginV2Ingress.event confirmed.ingress := by
  rw [confirmed.derivedExact]
  exact confirmed.accepted.intent_event

inductive Result (config : Config) where
  | confirmed (confirmed : Confirmed config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationLifecycleBeginV2Ingress.codec.decode bytes
    | return .rejected "noncanonical descriptor-bound lifecycle BEGIN"
  let .ok accepted ← NativeHostReplay.admitBeginV2Verified old ingress
    | return .rejected "current descriptor-bound lifecycle BEGIN refused"
  let derived := NativeHostReplay.beginV2Derived old accepted
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "lifecycle BEGIN transaction identity already used"
  let result ← DurableReceiverIO.receiveLoadedDetailed config.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      match NativeHostReplay.ExactReadback.ofAppended old derived appended with
      | .error detail => return .uncertain s!"v2 lifecycle BEGIN post-image: {detail}"
      | .ok ⟨proof, proofDerived⟩ =>
            match ← DurableHistoryStore.readerOf config.transport ResourceBirthCodec.rootBytes appended.next with
            | .error detail => return .uncertain s!"post-append history reader: {detail}"
            | .ok ⟨_, reader⟩ =>
              return .confirmed ⟨target, old, ingress, accepted,
                proof, ((congrArg NativeHostReplay.Derived.intent proofDerived).trans
                  (NativeHostReplay.beginV2Derived_intent old accepted)), kind, _, reader⟩
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "v2 lifecycle BEGIN lacks exact post-CAS readback"
      | .rejected _ => return .rejected "durable v2 lifecycle BEGIN refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationLifecycleBeginV2Receiver
