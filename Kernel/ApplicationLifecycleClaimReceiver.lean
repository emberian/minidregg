/-
Fresh receiving of a one-shot application lifecycle claim. A successful exact
CAS reserves the generation-specific launch attempt in Mini. This is not a
physical launch, completion attestation, or permission to retry an uncertain
host effect. A historical BEGIN receipt or a merely conditional claim cannot
construct `Reservation`.
-/
import Kernel.ApplicationLifecycleClaimVerified
import Kernel.ApplicationLifecycleClaimProjection

namespace Minidregg.Kernel.ApplicationLifecycleClaimReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Reservation (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationLifecycleClaimIngress.Ingress
  admitted : NativeHostReplay.ClaimAt config old.opened ingress
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

theorem Reservation.receipt_in_verified {config : Config}
    (reservation : Reservation config) :
    reservation.verified.receipts =
      reservation.old.receipts ++ [reservation.receipt] :=
  NativeHostReplay.extendExact_receipts reservation.old reservation.readback

theorem Reservation.postBytes_exact {config : Config}
    (reservation : Reservation config) :
    reservation.verified.opened.durable.bytes = reservation.readback.physicalBytes :=
  NativeHostReplay.extendExact_physicalBytes reservation.old reservation.readback

/-- Every projected coordinate is selected from the exact claimed post-image
or from the source ingress admitted by the same one-shot claim. The raw SPK
SHA-256 mapping is intentionally absent until a separate descriptor/install
admission proves it. -/
def Reservation.projection {config : Config} (reservation : Reservation config) :
    ApplicationLifecycleClaimProjection.Committed :=
  let source := reservation.ingress.source
  let tip := reservation.verified.opened.durable
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

theorem Reservation.projection_source {config : Config}
    (reservation : Reservation config) :
    reservation.projection.source = reservation.ingress.source := rfl

/-- The host receives a reservation only while a fresh physical read still
equals the exact CAS post-image. This is a point-in-time check, not a durable
lease: the host must fence the generation and recheck before exposure. -/
def Reservation.withFreshTip {config : Config} {α : Type}
    (reservation : Reservation config) (handoff : List UInt8 → IO α) :
    IO (Except String α) := do
  let .ok (some current) ← config.storage.transport.read
    | return .error "lifecycle claim physical tip unavailable before handoff"
  if exact : current.toByteArray == reservation.readback.physicalBytes.toByteArray then
    have _currentExact : current = reservation.readback.physicalBytes :=
      (DurableReceiverIO.byteArray_beq_exact _ _).mp exact
    return .ok (← handoff reservation.projection.canonicalBytes)
  else return .error "lifecycle claim physical tip changed before handoff"

inductive Result (config : Config) where
  | reserved (reservation : Reservation config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- Warm receiving consumes only the exact verified tip's private chronological
BEGIN certificates. An exact post-CAS physical readback is required; ordinary
`confirmed` (which may cover a concurrent suffix) remains uncertain. -/
def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationLifecycleClaimIngress.codec.decode bytes
    | return .rejected "noncanonical special lifecycle claim ingress"
  let .ok admitted ← NativeHostReplay.admitClaimVerified old ingress
    | return .rejected "lifecycle BEGIN absent or current claim authority refused"
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "lifecycle claim transaction identity already used"
  let result ← DurableReceiverIO.receiveLoadedDetailed config.storage.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind ready preparedEq readback readbackExact =>
      let candidate := NativeHostReplay.exactCandidate old derived ready
      match validated : validateLoaded config candidate with
      | .error detail => return .uncertain s!"lifecycle claim post-image validation: {detail}"
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
          else return .uncertain "lifecycle claim validated successor bytes changed"
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "lifecycle claim confirmation lacks exact fresh post-CAS readback"
      | .rejected _ => return .rejected "durable lifecycle claim refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationLifecycleClaimReceiver
