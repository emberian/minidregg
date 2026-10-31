/-
One replay-aware durable intent for the admitted grain-backed resource birth.
The birth Book fee, factory authorization, both current grain incidences, and
the coalesced authority post all come from the same old loaded image.
-/
module

public import Kernel.GrainResourceBirthAdmission
public import Kernel.ResourceBirthReceiver

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.GrainResourceBirthReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Compiler.ServedBasis (Ground)

set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

abbrev Source := GrainResourceBirthController.Source
abbrev Tariff := GrainResourceBirthController.Tariff
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DeclaredResourceController.Durable
abbrev Ambient := DeclaredResourceController.Ambient

/-- The separate frame and version ensure a recorded bare birth cannot be
replayed as a composite under the same creator-scoped transaction identity. -/
def event (domain : Digest)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress) : StableEvent where
  codecVersion := 3
  domain := domain
  eventId := commitmentBytes
    ("DREGG/GRAIN-RESOURCE-BIRTH/EVENT/v1".toUTF8.toList ++
      Tower256ConcreteBackend.digestStream.encode domain ++ ingress.bytes)
  canonicalBytes := ingress.bytes

/-- Cost accounting is defined here from the entire exact signed carrier and
write/read set. The permission-unit tariff in the grain settlement is a
separate trusted profile input, not the conserved Book fee. -/
def charge {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {ground : Ground deployment}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins ground profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      ground.directory ground.authority
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : GrainResourceBirthAdmission.Accepted profile deployment pins ground
      ambient tariff source birth grain ingress) : Charge
  | .incidences => (GrainResourceBirthAdmission.branches tariff source).length + 2
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (GrainResourceBirthTransaction.writes birth grain).length +
      accepted.readGuards.length
  | .witnessBytes => ingress.bytes.length
  | .proofWork => (GrainResourceBirthAdmission.branches tariff source).length + 2 +
      source.birth.resourceBatch.operations.length
  | .storageBytes => DeployedCharge.storageCharge ground.view
      (GrainResourceBirthTransaction.writes birth grain)
      (event deployment.domain ingress)
  | .sideEffectCount => 1
  | .feeDebit => source.birth.fee.amount
  | .networkBytes | .leaseByteBlocks => 0

def intent {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {ground : Ground deployment}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins ground profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      ground.directory ground.authority
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : GrainResourceBirthAdmission.Accepted profile deployment pins ground
      ambient tariff source birth grain ingress) : DataIntent rootBytes where
  transactionId := source.birth.transactionId
  writes := GrainResourceBirthTransaction.writes birth grain
  readGuards := accepted.readGuards
  nullifiers := (source.replayMarkers deployment.domain profile.semantics tariff).map
    (CredentialAuthorityReplay.nullifier deployment.domain)
  exactCharge := (Minidregg.Theory.ResourceCost.Charge.materialize (charge accepted)).toCharge
  event := event deployment.domain ingress
  subject := some source.birth.creator
  postRootsBound := GrainResourceBirthTransaction.writes_roots_bound birth grain
  guardsReadOnly := accepted.readGuards_readonly

/-- The retained finite charge is exactly the specified charge, lane by lane. -/
theorem intent_exactCharge {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {ground : Ground deployment}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins ground profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      ground.directory ground.authority
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : GrainResourceBirthAdmission.Accepted profile deployment pins ground
      ambient tariff source birth grain ingress) :
    (intent accepted).exactCharge = charge accepted :=
  Minidregg.Theory.ResourceCost.Charge.materialize_eq _

/-- **The committed grain births are named**: every write of the intent that creates
its cell is named by the admitted factory step (`Accepted.births_named`). -/
theorem intent_births_named {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {ground : Ground deployment}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins ground profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      ground.directory ground.authority
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : GrainResourceBirthAdmission.Accepted profile deployment pins ground
      ambient tariff source birth grain ingress) :
    ∀ write ∈ (intent accepted).writes, ResourceBirthController.Concrete.bornIn write = true →
      ReceivingLaw.namesBirth (accepted.pending.branchStep (.inl .factory)) write = true :=
  accepted.births_named.1

#assert_axioms intent_births_named

theorem intent_markers_exact {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {ground : Ground deployment}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins ground profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      ground.directory ground.authority
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : GrainResourceBirthAdmission.Accepted profile deployment pins ground
      ambient tariff source birth grain ingress) :
    (intent accepted).nullifiers =
      [CredentialAuthorityReplay.nullifier deployment.domain source.birth.authorityNullifier,
        CredentialAuthorityReplay.nullifier deployment.domain
          (GrainResourceBirthAdmission.useMarker profile deployment tariff source)] := rfl

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

inductive Reject where
  | malformedIngress
  | transactionConflict
  | tariffUnavailable
  | birthPreparation (reason : ResourceBirthController.Concrete.PreparationReject)
  | grainPreparation (reason : DeclaredResourceController.Reject)
  | admission (reason : GrainResourceBirthAdmission.Reject)
  | durable (reason : DurableDataIntent.RejectReason)
  /-- The ground does not answer the birth's transaction id (a light basis that
  did not declare it): refused by name, never read as "not recorded". -/
  | undeclaredTransaction

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | historical (receipt : Receipt)
  | rejected (reason : Reject)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receipt (domain : Digest)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress) : Receipt :=
  ⟨ingress.birth.descriptor.transactionId, (event domain ingress).eventId⟩

/-- The keys a composite birth consults beyond the state: the birth's transaction
id (replay detection, `replay`) and both replay markers' nullifiers (the birth's
authority marker and the signed grain command's operation marker; their spent
bits are read by the preparation, `ResourceBirthController.Concrete.MarkerDeclared`).
A light basis for a composite birth declares at least these. -/
def grainKeys (domain semantics : Digest)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress) : DurableView.Keys :=
  ⟨[ingress.birth.descriptor.transactionId],
    [CredentialAuthorityReplay.nullifier domain ingress.birth.descriptor.authorityNullifier,
      CredentialAuthorityReplay.nullifier domain
        (DeclaredResourceController.operationMarker domain semantics ingress.command)]⟩

/-- A recorded intent is this composite ingress's own: the same transaction id,
the exact complete composite event and both domain-bound replay nullifiers. -/
def recordedExact (ingress : GrainResourceBirthPolicyController.DecodedIngress)
    (recorded : Intent TransactionId DurableDataIntent.CellId StableNullifier ReplayEnvelope) : Bool :=
  decide (recorded.transactionId = ingress.birth.descriptor.transactionId ∧
    recorded.event.event = event ingress.grain.1 ingress ∧
    recorded.nullifiers =
      [CredentialAuthorityReplay.nullifier ingress.grain.1
          ingress.birth.descriptor.authorityNullifier,
        CredentialAuthorityReplay.nullifier ingress.grain.1
          (DeclaredResourceController.operationMarker ingress.grain.1
            ingress.grain.2.1 ingress.command)])

/-- An occupied birth transaction ID is a replay only for the exact complete
composite event and both domain-bound replay nullifiers. A historical bare
birth or a different grain command under the same ID is a conflict. The one
journal read goes through `Ground.replayOf`: an undeclared transaction id is
`undeclared`, never `fresh`. -/
def replay {deployment : Deployment} (ground : Ground deployment)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress) :
    Minidregg.Compiler.ServedBasis.Ground.Replay Receipt :=
  ground.replayOf ingress.birth.descriptor.transactionId (recordedExact ingress)
    (receipt ingress.grain.1 ingress)

theorem replay_only_exact {deployment : Deployment} (ground : Ground deployment)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress)
    (result : Receipt) (accepted : replay ground ingress = .original result) :
    result = receipt ingress.grain.1 ingress ∧
      ∃ recorded,
        Snapshot.lookupRecorded ingress.birth.descriptor.transactionId
            ground.view.model.journal = some recorded ∧
        recorded.transactionId = ingress.birth.descriptor.transactionId ∧
        recorded.event.event = event ingress.grain.1 ingress ∧
        recorded.nullifiers =
          [CredentialAuthorityReplay.nullifier ingress.grain.1
              ingress.birth.descriptor.authorityNullifier,
            CredentialAuthorityReplay.nullifier ingress.grain.1
              (DeclaredResourceController.operationMarker ingress.grain.1
                ingress.grain.2.1 ingress.command)] := by
  obtain ⟨same, recorded, found, isExact⟩ :=
    Minidregg.Compiler.ServedBasis.Ground.replayOf_original ground _ _ _ _ accepted
  exact ⟨same, recorded, found, of_decide_eq_true isExact⟩

/-- **An undeclared transaction id is refused by name** on a light basis. -/
theorem replay_undeclared {deployment : Deployment} {store : Minidregg.Compiler.DurableHistory.StoreIdentity}
    (basis : Minidregg.Compiler.ServedBasis.Basis deployment store)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress)
    (undeclared : ingress.birth.descriptor.transactionId ∉ basis.keys.transactions) :
    replay (Ground.ofBasis basis) ingress = .undeclared :=
  Minidregg.Compiler.ServedBasis.Ground.replayOf_undeclared basis _ _ _ undeclared

#assert_axioms replay_only_exact replay_undeclared

/-- Fresh admission of a composite birth on a ground: the source birth and the
grain targets prepared on it, the joint admission, and the accepted intent handed
to `commit`. The full and light receives share it; only the commit differs. -/
def admitOn {F : Type} [Field F] [DecidableEq F] {R : Type}
    (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : Deployment) (pins : ResourceBirth.FactoryPins)
    (tariff : Option Tariff) (ambient : Ambient)
    (native : CredentialSignatureIO.NativeConfig) (ground : Ground deployment)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress)
    (refuse : Reject → IO R)
    (commit : DataIntent rootBytes → IO R) : IO R := do
  let source := ingress.source
  let some tariff := tariff
    | refuse .tariffUnavailable
  match GrainResourceBirthController.prepareSourceBirth profile.compilerProfile
      profile.disabledEvaluators deployment pins ground profile.semantics tariff source
      ambient.height with
  | .error reason => refuse (.birthPreparation reason)
  | .ok birth =>
      match GrainResourceBirthTransaction.prepareTargets profile deployment pins
          ground ambient tariff source birth with
      | .error reason => refuse (.grainPreparation reason)
      | .ok grain =>
          match ← GrainResourceBirthAdmission.admitDecodedNative profile deployment
              pins ground ambient tariff source birth grain native ingress with
          | .error reason => refuse (.admission reason)
          | .ok accepted => commit (intent accepted)

/-- A historical result names only the exact recorded ingress; it does not
re-admit the current tariff. For a fresh call the caller pins `tariff` and
`ambient`; source comes only from the canonical outer ingress, is matched
to both signed components, and both targets use this loaded snapshot (the
full shape: the ratchet-listed callers). -/
def receiveLoaded {F : Type} [Field F] [DecidableEq F]
    (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : Deployment) (pins : ResourceBirth.FactoryPins)
    (tariff : Option Tariff) (ambient : Ambient)
    (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (bytes : List UInt8) : IO Result := do
  let ground : Ground deployment := .ofLoaded durable directory authority
  match GrainResourceBirthPolicyController.decodeIngress bytes with
  | none => return .rejected .malformedIngress
  | some ingress =>
      match replay ground ingress with
      | .original recorded => return .historical recorded
      | .conflict => return .rejected .transactionConflict
      | .undeclared => return .rejected .undeclaredTransaction
      | .fresh =>
          admitOn profile deployment pins tariff ambient native ground ingress
            (fun reason => return .rejected reason) fun intent => do
              match ← DurableReceiverIO.receiveLoaded transport rootBytes durable intent with
              | .confirmed kind _ => return .confirmed kind (receipt deployment.domain ingress)
              | .rejected reason => return .rejected (.durable reason)
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail
              | .uncertain detail => return .uncertain detail

/-- **The light composite birth receive.** The birth's keys (`grainKeys`) are read
from the authenticated history into a basis (`basisOf`); the tariff is the
basis's platform record's (`grainTariffAt`); replay, preparation and admission run
on `Ground.ofBasis`; the commit is `DurableServed.receiveServed` on the light
opening. The admission height is `genesisHeight + basis.height`. -/
def receiveServed {F : Type} [Field F] [DecidableEq F]
    (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : Deployment) (pins : ResourceBirth.FactoryPins)
    (federation : FederationId) (genesisHeight : Nat)
    (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (opening : DurableServed.Opening rootBytes)
    (basisOf : DurableView.Keys →
      IO (Except String (Minidregg.Compiler.ServedBasis.Basis deployment opening.store)))
    (bytes : List UInt8) : IO Result := do
  match GrainResourceBirthPolicyController.decodeIngress bytes with
  | none => return .rejected .malformedIngress
  | some ingress =>
      match ← basisOf (grainKeys deployment.domain profile.semantics ingress) with
      | .error detail => return .unavailable detail
      | .ok basis =>
          let ground : Ground deployment := .ofBasis basis
          match replay ground ingress with
          | .original recorded => return .historical recorded
          | .conflict => return .rejected .transactionConflict
          | .undeclared => return .rejected .undeclaredTransaction
          | .fresh =>
              let tariff := GrainResourceBirthAdmission.grainTariffAt deployment ground.view
              let ambient : Ambient := ⟨federation, genesisHeight + basis.height⟩
              let issued := receipt deployment.domain ingress
              admitOn profile deployment pins tariff ambient native ground ingress
                (fun reason => return .rejected reason) fun intent => do
                  match ← DurableServed.receiveServed transport rootBytes opening intent with
                  | .appended kind .. => return .confirmed kind issued
                  | .replayed _ => return .confirmed .replayed issued
                  | .rejected reason => return .rejected (.durable reason)
                  | .contention => return .contention
                  | .unavailable detail => return .unavailable detail
                  | .uncertain detail => return .uncertain detail

def receive {F : Type} [Field F] [DecidableEq F]
    (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : Deployment) (pins : ResourceBirth.FactoryPins)
    (tariff : Option Tariff) (ambient : Ambient)
    (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (bytes : List UInt8) : IO Result := do
  match GrainResourceBirthPolicyController.decodeIngress bytes with
  | none => return .rejected .malformedIngress
  | some _ =>
      match ← DurableReceiverIO.load transport rootBytes with
      | .error detail => return .unavailable detail
      | .ok durable =>
          match CredentialAuthorityDomainReceiver.loadDirectory durable with
          | none => return .rejected (.birthPreparation .directory)
          | some directory =>
              match CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot with
              | none => return .rejected (.birthPreparation .authorityDomain)
              | some authority =>
                  receiveLoaded profile deployment pins tariff ambient native transport durable
                    directory authority bytes

end Minidregg.Kernel.GrainResourceBirthReceiver
