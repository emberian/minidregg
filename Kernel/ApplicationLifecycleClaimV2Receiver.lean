/-
Exact-CAS reservation for a descriptor-bound lifecycle claim. V1 claims can
remain in historical replay but never produce this SPK launch handoff.
-/
import Kernel.ApplicationLifecycleClaimProjection
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.ApplicationLifecycleClaimV2Receiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Reservation (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationLifecycleClaimV2Ingress.Ingress
  admitted : NativeHostReplay.ClaimAtV2 config old.opened ingress
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
  confirmation : DurableReceiverIO.Confirmation

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

theorem Reservation.postBytes_exact {config : Config}
    (reservation : Reservation config) :
    reservation.verified.opened.durable.bytes = reservation.readback.physicalBytes :=
  NativeHostReplay.extendExact_physicalBytes reservation.old reservation.readback

def Reservation.projection {config : Config} (reservation : Reservation config) :
    ApplicationLifecycleClaimProjection.CommittedV2 :=
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
          tip.snapshot.model.roots ⟨config.deployment.authorityCatalogueId⟩
        postImageBoundary := reservation.receipt.imageBoundary }
    descriptor := reservation.ingress.originalBegin.descriptor }

/-- The full descriptor root is the signed package digest. This is only a
current Mini reservation; the host must separately compare the descriptor to
one verified signed SPK parse and fence actual process identity. -/
theorem Reservation.projection_package_root {config : Config}
    (reservation : Reservation config) :
    reservation.projection.core.source.begin.source.packageDigest =
      reservation.projection.descriptor.root := by
  have bound := reservation.admitted.conditional.originalAccepted.descriptorBound
  simp only [ApplicationLifecycleBeginV2Ingress.descriptorBound,
    Bool.and_eq_true, decide_eq_true_eq] at bound
  have sameBegin : reservation.ingress.base.source.begin =
      reservation.ingress.originalBegin.base := by
    exact (decide_eq_true_eq).mp reservation.admitted.conditional.sourceExact
  change reservation.ingress.base.source.begin.source.packageDigest =
    reservation.ingress.originalBegin.descriptor.root
  rw [sameBegin]
  exact bound.2

theorem Reservation.projection_valid {config : Config}
    (reservation : Reservation config) :
    reservation.projection.valid = true := by
  have bound := reservation.admitted.conditional.originalAccepted.descriptorBound
  simp only [ApplicationLifecycleBeginV2Ingress.descriptorBound,
    Bool.and_eq_true] at bound
  have valid : reservation.ingress.originalBegin.descriptor.valid = true := by
    simp only [ApplicationSpkPackageIdentity.Descriptor.matchesManifest,
      Bool.and_eq_true] at bound
    aesop
  simp only [ApplicationLifecycleClaimProjection.CommittedV2.valid,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨valid, reservation.projection_package_root⟩

def Reservation.withFreshTip {config : Config} {α : Type}
    (reservation : Reservation config) (handoff : List UInt8 → IO α) :
    IO (Except String α) := do
  let .ok (some current) ← config.storage.transport.read
    | return .error "descriptor-bound claim physical tip unavailable before handoff"
  if exact : current.toByteArray == reservation.readback.physicalBytes.toByteArray then
    have _currentExact : current = reservation.readback.physicalBytes :=
      (DurableReceiverIO.byteArray_beq_exact _ _).mp exact
    return .ok (← handoff reservation.projection.canonicalBytes)
  else return .error "descriptor-bound claim physical tip changed before handoff"

inductive Result (config : Config) where
  | reserved (reservation : Reservation config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationLifecycleClaimV2Ingress.codec.decode bytes
    | return .rejected "noncanonical descriptor-bound lifecycle claim ingress"
  let .ok admitted ← NativeHostReplay.admitClaimV2Verified old ingress
    | return .rejected "descriptor-bound BEGIN absent or current claim authority refused"
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "descriptor-bound claim transaction identity already used"
  let result ← DurableReceiverIO.receiveLoadedDetailed config.storage.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind ready preparedEq readback readbackExact =>
      let candidate := NativeHostReplay.exactCandidate old derived ready
      match validated : validateLoaded config candidate with
      | .error detail => return .uncertain s!"descriptor-bound claim post-image: {detail}"
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
            return .reserved ⟨target, old, ingress, admitted,
              proof, admitted.toDerived_intent, kind⟩
          else return .uncertain "descriptor-bound claim successor bytes changed"
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "descriptor-bound claim lacks exact post-CAS readback"
      | .rejected _ => return .rejected "durable descriptor-bound claim refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationLifecycleClaimV2Receiver
