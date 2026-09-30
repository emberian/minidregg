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

def Confirmed.verified {config : Config} (confirmed : Confirmed config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate confirmed.old
        confirmed.readback.derived confirmed.readback.ready) :=
  NativeHostReplay.extendExact confirmed.old confirmed.readback

def Confirmed.receipt {config : Config} (confirmed : Confirmed config) :
    NativeHostCodec.Receipt :=
  let candidate := NativeHostReplay.exactCandidate confirmed.old
    confirmed.readback.derived confirmed.readback.ready
  ⟨confirmed.readback.derived.intent.transactionId,
    confirmed.readback.derived.intent.event.eventId,
    confirmed.old.opened.durable.image.accepted.length + 1,
    worldRoot config candidate.image⟩

theorem Confirmed.postBytes_exact {config : Config} (confirmed : Confirmed config) :
    confirmed.verified.opened.durable.bytes = confirmed.readback.physicalBytes :=
  NativeHostReplay.extendExact_physicalBytes confirmed.old confirmed.readback

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
    let result ← DurableReceiverIO.receiveLoadedDetailed config.storage.transport
      ResourceBirthCodec.rootBytes old.opened.durable derived.intent
    match result with
    | .exact kind ready preparedEq readback readbackExact =>
        let candidate := NativeHostReplay.exactCandidate old derived ready
        match validated : validateLoaded config candidate with
        | .error detail => return .uncertain s!"v3 lifecycle BEGIN post-image: {detail}"
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
              return .confirmed ⟨target, old, ingress, proof, eventExact, kind⟩
            else return .uncertain "v3 lifecycle BEGIN successor bytes changed"
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
