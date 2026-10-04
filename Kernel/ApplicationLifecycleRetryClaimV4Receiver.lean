/-
Exact-CAS reservation for the one-use repeat-CREATE claim (event70). The
fresh-tip handoff carries the versioned committed projection; a replayed or
recovered receipt never carries launch power.
-/
import Kernel.ApplicationLifecycleRetryClaimV4Projection
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Receiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Reservation (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationLifecycleRetryClaimV4Ingress.Ingress
  admitted : NativeHostReplay.ClaimAtV4 config old.opened ingress
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
  confirmation : DurableReceiverIO.Confirmation
  /-- True only when this attempt observed native CAS `.installed`. Exact
  readback following `.alreadyPresent` is receipt recovery, not launch power. -/
  freshCasWinner : Bool

def Reservation.verified {config : Config} (reservation : Reservation config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate reservation.old
        reservation.readback.derived reservation.readback.ready) :=
  NativeHostReplay.extendExact reservation.old reservation.readback

def Reservation.receipt {config : Config} (reservation : Reservation config) :
    NativeHostCodec.Receipt :=
  let old := reservation.old
  let candidate := NativeHostReplay.exactCandidate old
    reservation.readback.derived reservation.readback.ready
  ⟨reservation.readback.derived.intent.transactionId,
    reservation.readback.derived.intent.event.eventId,
    old.opened.durable.image.accepted.length + 1,
    candidate.worldRoot⟩

theorem Reservation.postRecord_exact {config : Config}
    (reservation : Reservation config) :
    reservation.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent reservation.readback.derived.intent) :=
  NativeHostReplay.extendExact_physicalRecord reservation.old reservation.readback

def Reservation.projection {config : Config} (reservation : Reservation config) :
    ApplicationLifecycleRetryClaimV4Projection.Committed :=
  let source := reservation.ingress.base.source
  let tip := reservation.verified.opened.durable
  { core :=
      { source := source
        originalTransaction := reservation.admitted.prior.record.transactionId
        originalEvent := reservation.admitted.prior.record.event.eventId
        originalNullifier :=
          (ApplicationLifecycleBegin.stableNullifier config.deployment.domain
            config.profile.semantics source.begin.source).nullifierId
        claimReceipt := reservation.receipt
        claimNullifier :=
          (ApplicationLifecycleClaim.stableNullifier config.deployment.domain
            config.profile.semantics source).nullifierId
        appPhysicalRoot := tip.snapshot.model.roots ⟨source.begin.source.app⟩
        packagePhysicalRoot :=
          tip.snapshot.model.roots ⟨source.begin.source.packageManifest⟩
        authorityPhysicalRoot :=
          tip.snapshot.model.roots ⟨config.deployment.authorityCellId⟩
        postWorldRoot := reservation.receipt.worldRoot }
    originalClaim := reservation.ingress }

def Reservation.withFreshTip {config : Config} {α : Type}
    (reservation : Reservation config) (handoff : List UInt8 → IO α) :
    IO (Except String α) := do
  unless reservation.confirmation == .installed && reservation.freshCasWinner do
    return .error "retry claim was not freshly installed"
  let .ok current ← DurableReceiverIO.tipIs config.transport
      reservation.readback.appended.next.image.accepted.length reservation.readback.appended.entry
    | return .error "retry claim physical tip unavailable before handoff"
  if current then
    return .ok (← handoff reservation.projection.canonicalBytes)
  else return .error "retry claim physical tip changed before handoff"

inductive Result (config : Config) where
  | reserved (reservation : Reservation config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationLifecycleRetryClaimV4Ingress.codec.decode bytes
    | return .rejected "noncanonical retry claim ingress"
  let .ok admitted ← NativeHostReplay.admitRetryClaimV4Verified old ingress
    | return .rejected "retry BEGIN absent or current retry claim authority refused"
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "retry claim transaction identity already used"
  let (freshCasWinner, result) ← DurableReceiverIO.receiveLoadedDetailedWithFresh
    config.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      match NativeHostReplay.ExactReadback.ofAppended old derived appended with
      | .error detail => return .uncertain s!"retry claim post-image: {detail}"
      | .ok ⟨proof, proofDerived⟩ =>
            return .reserved ⟨target, old, ingress, admitted,
              proof, ((congrArg NativeHostReplay.Derived.intent proofDerived).trans
                admitted.toDerived_intent), kind, freshCasWinner⟩
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "retry claim lacks exact post-CAS readback"
      | .rejected _ => return .rejected "durable retry claim refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationLifecycleRetryClaimV4Receiver
