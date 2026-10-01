/-
One durable event for a grain-backed app ticket issue. A bare birth, a plain
grain birth and the older bare share-issue event have different retained
carriers and nullifier sets. Historical lookup selects only the exact event;
semantic replay must re-admit this receiver at its original prefix.
-/
import Kernel.ApplicationShareIssueGrainAdmission
import Kernel.GrainResourceBirthReceiver

namespace Minidregg.Kernel.ApplicationShareIssueGrainReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ApplicationShareIssueGrainAdmission
open Minidregg.Kernel.ApplicationShareIssueGrainSource

set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] NativeHost.Config.profile
  CanonicalRuntimeProfile.Profile.compilerProfile

variable {F : Type} [Field F] [DecidableEq F]
variable {profile : CanonicalRuntimeProfile.Profile F}
  {config : NativeHost.Config} {pins : FactoryPins}
  {durable : ResourceBirthController.Concrete.Durable}
  {ambient : DeclaredResourceController.Ambient}
  {ingress : Ingress}

def event (domain : Digest) (ingress : Ingress) : StableEvent where
  codecVersion := 22
  domain := domain
  eventId := commitmentBytes
    ("DREGG/APPLICATION/GRAIN-SHARE-ISSUE-EVENT/v1".toUTF8.toList ++
      digestStream.encode domain ++ ingress.canonicalBytes)
  canonicalBytes := ingress.canonicalBytes

theorem event_retains_full_ingress (domain : Digest) (ingress : Ingress) :
    (event domain ingress).canonicalBytes = ingress.canonicalBytes := rfl

def nullifiers (domain : Digest) (ingress : Ingress)
    (grain : GrainResourceBirthPolicyController.DecodedIngress)
    (tariff : GrainResourceBirthController.Tariff) : List StableNullifier :=
  (grain.source.replayMarkers domain grain.grain.2.1 tariff).map
    (CredentialAuthorityReplay.nullifier domain) ++
    [CredentialAuthorityReplay.nullifier domain
      (ApplicationShareIssueSource.issueMarker ingress.spec grain.source.birth)]

def writes (accepted : Accepted profile config pins durable ambient ingress) :
    List DataWrite := accepted.atomic.writes

def readGuards (accepted : Accepted profile config pins durable ambient ingress) :
    List ReadGuard :=
  accepted.grainAccepted.readGuards ++
    [ApplicationShareIssueDelegation.readGuard accepted.appPrepared]

theorem readGuards_readonly
    (accepted : Accepted profile config pins durable ambient ingress)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.cellId ∉ (writes accepted).map DataWrite.cellId := by
  rcases List.mem_append.mp member with grain | app
  · exact accepted.atomic.readonly guard
      (accepted.grainAccepted.readGuards_readonly guard grain)
  · simp only [List.mem_singleton] at app
    subst guard
    exact accepted.atomic.readonly _ accepted.appReadOnly

theorem readGuards_exact
    (accepted : Accepted profile config pins durable ambient ingress)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId := by
  rcases List.mem_append.mp member with grain | app
  · exact accepted.grainAccepted.readGuards_exact guard grain
  · simp only [List.mem_singleton] at app
    subst guard
    exact ApplicationShareIssueDelegation.readGuard_current accepted.appPrepared

theorem writes_roots_bound
    (accepted : Accepted profile config pins durable ambient ingress) :
    ∀ write ∈ writes accepted,
      rootBytes write.canonicalPostBytes = write.exactPost :=
  accepted.atomic.roots_bound
    (GrainResourceBirthTransaction.writes_roots_bound accepted.birth accepted.grain)

def charge (accepted : Accepted profile config pins durable ambient ingress) : Charge
  | .incidences => GrainResourceBirthReceiver.charge accepted.grainAccepted .incidences + 1
  | .turnBytes => GrainResourceBirthReceiver.charge accepted.grainAccepted .turnBytes +
      ingress.canonicalBytes.length +
      (ApplicationShareIssueAtomicBirth.initializedWrite accepted.sourceReady).canonicalPostBytes.length
  | .memoryTouches => GrainResourceBirthReceiver.charge accepted.grainAccepted .memoryTouches + 1
  | .witnessBytes => GrainResourceBirthReceiver.charge accepted.grainAccepted .witnessBytes +
      ingress.appEnvelope.length +
      (ApplicationShareIssueAtomicBirth.initializedWrite accepted.sourceReady).canonicalPostBytes.length
  | .proofWork => GrainResourceBirthReceiver.charge accepted.grainAccepted .proofWork + 1
  | .storageBytes => GrainResourceBirthReceiver.charge accepted.grainAccepted .storageBytes +
      ingress.canonicalBytes.length +
      (ApplicationShareIssueAtomicBirth.initializedWrite accepted.sourceReady).canonicalPostBytes.length
  | .sideEffectCount => GrainResourceBirthReceiver.charge accepted.grainAccepted .sideEffectCount + 1
  | .feeDebit => GrainResourceBirthReceiver.charge accepted.grainAccepted .feeDebit
  | .networkBytes | .leaseByteBlocks => 0

theorem charge_fee_source_quoted
    (accepted : Accepted profile config pins durable ambient ingress) :
    charge accepted .feeDebit = accepted.decoded.source.birth.quotedFee
      (accepted.sourceReady.effectiveTariff config.tariff) := by
  change accepted.decoded.source.birth.fee.amount = _
  exact accepted.special_fee_bound

def intent (accepted : Accepted profile config pins durable ambient ingress) :
    DataIntent rootBytes where
  transactionId := accepted.decoded.source.birth.transactionId
  writes := writes accepted
  readGuards := readGuards accepted
  nullifiers := nullifiers config.deployment.domain ingress accepted.decoded accepted.tariff
  exactCharge := charge accepted
  event := event config.deployment.domain ingress
  subject := some accepted.decoded.source.birth.creator
  postRootsBound := writes_roots_bound accepted
  guardsReadOnly := readGuards_readonly accepted

theorem intent_event_version
    (accepted : Accepted profile config pins durable ambient ingress) :
    (intent accepted).event.codecVersion = 22 := rfl

theorem intent_retains_full_ingress
    (accepted : Accepted profile config pins durable ambient ingress) :
    (intent accepted).event.canonicalBytes = ingress.canonicalBytes := rfl

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | historical (receipt : Receipt)
  | rejected (reason : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receipt (domain : Digest) (ingress : Ingress)
    (grain : GrainResourceBirthPolicyController.DecodedIngress) : Receipt :=
  ⟨grain.source.birth.transactionId, (event domain ingress).eventId⟩

def replay (durable : ResourceBirthController.Concrete.Durable)
    (domain : Digest) (ingress : Ingress)
    (grain : GrainResourceBirthPolicyController.DecodedIngress)
    (tariff : GrainResourceBirthController.Tariff) :
    Option (Except String Receipt) :=
  match Snapshot.lookupRecorded grain.source.birth.transactionId
      durable.snapshot.model.journal with
  | none => none
  | some recorded =>
      if recorded.transactionId = grain.source.birth.transactionId ∧
          recorded.event.event = event domain ingress ∧
          recorded.nullifiers = nullifiers domain ingress grain tariff then
        some (.ok (receipt domain ingress grain))
      else some (.error "grain share issue transaction identity conflict")

/-- A historical exact lookup never submits. Fresh admission combines the
existing grain birth and current app delegation before one durable CAS. -/
def receiveLoaded (config : NativeHost.Config) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport)
    (durable : ResourceBirthController.Concrete.Durable)
    (ambient : DeclaredResourceController.Ambient)
    (bytes : List UInt8) : IO Result := do
  let some outer := ApplicationShareIssueGrainSource.codec.decode bytes
    | return .rejected "noncanonical grain share issue ingress"
  let some grain := outer.decodeGrain
    | return .rejected "noncanonical grain-backed birth ingress"
  let .ok tariff := config.grainBirthTariffValue
    | return .rejected "grain-backed tariff unavailable"
  match replay durable config.deployment.domain outer grain tariff with
  | some (.ok historical) => return .historical historical
  | some (.error reason) => return .rejected reason
  | none =>
      match ← ApplicationShareIssueGrainAdmission.admitNative config.profile config pins
          native durable ambient bytes with
      | .error reason => return .rejected reason
      | .ok ⟨acceptedIngress, accepted⟩ =>
          match ← DurableReceiverIO.receiveLoaded transport rootBytes durable
              (intent accepted) with
          | .confirmed kind _ =>
              return .confirmed kind
                (receipt config.deployment.domain acceptedIngress accepted.decoded)
          | .rejected _ => return .rejected "durable grain share issue refused"
          | .contention => return .contention
          | .unavailable detail => return .unavailable detail
          | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationShareIssueGrainReceiver
