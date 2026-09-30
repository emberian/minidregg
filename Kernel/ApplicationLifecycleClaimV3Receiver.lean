/-
Exact-CAS reservation for a launch-bound lifecycle claim. V1 claims can
remain in historical replay but never produce this SPK launch handoff.
-/
import Kernel.ApplicationLifecycleClaimV3Projection
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleClaimV3Receiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Reservation (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationLifecycleClaimV3Ingress.Ingress
  admitted : NativeHostReplay.ClaimAtV3 config old.opened ingress
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
    imageBoundary config candidate.image⟩

theorem Reservation.postRecord_exact {config : Config}
    (reservation : Reservation config) :
    reservation.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent reservation.readback.derived.intent) :=
  NativeHostReplay.extendExact_physicalRecord reservation.old reservation.readback

def Reservation.projection {config : Config} (reservation : Reservation config) :
    ApplicationLifecycleClaimV3Projection.Committed :=
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
        postImageBoundary := reservation.receipt.imageBoundary }
    originalClaim := reservation.ingress }

def Reservation.withFreshTip {config : Config} {α : Type}
    (reservation : Reservation config) (handoff : List UInt8 → IO α) :
    IO (Except String α) := do
  unless reservation.confirmation == .installed && reservation.freshCasWinner do
    return .error "launch-bound claim was not freshly installed"
  let .ok current ← DurableReceiverIO.tipIs config.storage.transport
      reservation.readback.appended.next.image.accepted.length reservation.readback.appended.entry
    | return .error "launch-bound claim physical tip unavailable before handoff"
  if current then
    return .ok (← handoff reservation.projection.canonicalBytes)
  else return .error "launch-bound claim physical tip changed before handoff"

inductive Result (config : Config) where
  | reserved (reservation : Reservation config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationLifecycleClaimV3Ingress.codec.decode bytes
    | return .rejected "noncanonical launch-bound lifecycle claim ingress"
  let .ok admitted ← NativeHostReplay.admitClaimV3Verified old ingress
    | return .rejected "launch-bound BEGIN absent or current claim authority refused"
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "launch-bound claim transaction identity already used"
  let (freshCasWinner, result) ← DurableReceiverIO.receiveLoadedDetailedWithFresh
    config.storage.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      match NativeHostReplay.ExactReadback.ofAppended old derived appended with
      | .error detail => return .uncertain s!"launch-bound claim post-image: {detail}"
      | .ok ⟨proof, proofDerived⟩ =>
            return .reserved ⟨target, old, ingress, admitted,
              proof, ((congrArg NativeHostReplay.Derived.intent proofDerived).trans admitted.toDerived_intent), kind, freshCasWinner⟩
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "launch-bound claim lacks exact post-CAS readback"
      | .rejected _ => return .rejected "durable launch-bound claim refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationLifecycleClaimV3Receiver
