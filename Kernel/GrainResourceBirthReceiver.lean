/-
One replay-aware durable intent for the admitted grain-backed resource birth.
The birth Book fee, factory authorization, both current grain incidences, and
the coalesced authority post all come from the same old loaded image.
-/
import Kernel.GrainResourceBirthAdmission
import Kernel.ResourceBirthReceiver

namespace Minidregg.Kernel.GrainResourceBirthReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol

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
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : GrainResourceBirthAdmission.Accepted profile deployment pins durable
      ambient tariff source birth grain ingress) : Charge
  | .incidences => (GrainResourceBirthAdmission.branches tariff source).length + 2
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (GrainResourceBirthTransaction.writes birth grain).length +
      accepted.readGuards.length
  | .witnessBytes => ingress.bytes.length
  | .proofWork => (GrainResourceBirthAdmission.branches tariff source).length + 2 +
      source.birth.resourceBatch.operations.length
  | .storageBytes =>
      ((GrainResourceBirthTransaction.writes birth grain).map
        fun write => write.canonicalPostBytes.length).sum + ingress.bytes.length
  | .sideEffectCount => 1
  | .feeDebit => source.birth.fee.amount
  | .networkBytes | .leaseByteBlocks => 0

def intent {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : GrainResourceBirthAdmission.Accepted profile deployment pins durable
      ambient tariff source birth grain ingress) : DataIntent rootBytes where
  transactionId := source.birth.transactionId
  writes := GrainResourceBirthTransaction.writes birth grain
  readGuards := accepted.readGuards
  nullifiers := (source.replayMarkers deployment.domain profile.semantics tariff).map
    (CredentialAuthorityReplay.nullifier deployment.domain)
  exactCharge := charge accepted
  event := event deployment.domain ingress
  postRootsBound := GrainResourceBirthTransaction.writes_roots_bound birth grain
  guardsReadOnly := accepted.readGuards_readonly

theorem intent_markers_exact {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment}
    {pins : ResourceBirth.FactoryPins} {durable : Durable}
    {ambient : Ambient} {tariff : Tariff} {source : Source}
    {birth : GrainResourceBirthController.PreparedSourceBirth profile.compilerProfile
      deployment pins durable profile.semantics tariff source}
    {grain : GrainResourceBirthTransaction.PreparedTargets deployment
      birth.prepared.pre.directory.directory birth.prepared.pre.authority.snapshot
      profile.semantics ambient (source.grainCommand tariff)}
    {ingress : GrainResourceBirthPolicyController.DecodedIngress}
    (accepted : GrainResourceBirthAdmission.Accepted profile deployment pins durable
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

/-- An occupied birth transaction ID is a replay only for the exact complete
composite event and both domain-bound replay nullifiers. A historical bare
birth or a different grain command under the same ID is a conflict. -/
def replay (durable : Durable)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress) :
    Option (Except Reject Receipt) :=
  match Snapshot.lookupRecorded ingress.birth.descriptor.transactionId
      durable.snapshot.model.journal with
  | none => none
  | some recorded =>
      if recorded.transactionId = ingress.birth.descriptor.transactionId ∧
          recorded.event.event = event ingress.grain.1 ingress ∧
          recorded.nullifiers =
            [CredentialAuthorityReplay.nullifier ingress.grain.1
                ingress.birth.descriptor.authorityNullifier,
              CredentialAuthorityReplay.nullifier ingress.grain.1
                (DeclaredResourceController.operationMarker ingress.grain.1
                  ingress.grain.2.1 ingress.command)] then
        some (.ok (receipt ingress.grain.1 ingress))
      else some (.error .transactionConflict)

theorem replay_only_exact (durable : Durable)
    (ingress : GrainResourceBirthPolicyController.DecodedIngress)
    (result : Receipt) (accepted : replay durable ingress = some (.ok result)) :
    result = receipt ingress.grain.1 ingress ∧
      ∃ recorded,
        Snapshot.lookupRecorded ingress.birth.descriptor.transactionId
            durable.snapshot.model.journal = some recorded ∧
        recorded.transactionId = ingress.birth.descriptor.transactionId ∧
        recorded.event.event = event ingress.grain.1 ingress ∧
        recorded.nullifiers =
          [CredentialAuthorityReplay.nullifier ingress.grain.1
              ingress.birth.descriptor.authorityNullifier,
            CredentialAuthorityReplay.nullifier ingress.grain.1
              (DeclaredResourceController.operationMarker ingress.grain.1
                ingress.grain.2.1 ingress.command)] := by
  unfold replay at accepted
  split at accepted
  · cases accepted
  · rename_i recorded found
    split at accepted
    · rename_i exactRecord
      have same : receipt ingress.grain.1 ingress = result := by simpa using accepted
      exact ⟨same.symm, recorded, found, exactRecord⟩
    · cases accepted

/-- A historical result names only the exact recorded ingress; it does not
re-admit the current tariff. For a fresh call the caller pins `tariff` and
`ambient`; source comes only from the canonical outer ingress, is matched
to both signed components, and both targets use this loaded snapshot. -/
def receiveLoaded {F : Type} [Field F] [DecidableEq F]
    (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : Deployment) (pins : ResourceBirth.FactoryPins)
    (tariff : Option Tariff) (ambient : Ambient)
    (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (bytes : List UInt8) : IO Result := do
  match GrainResourceBirthPolicyController.decodeIngress bytes with
  | none => return .rejected .malformedIngress
  | some ingress =>
      let source := ingress.source
      match replay durable ingress with
      | some (.ok recorded) => return .historical recorded
      | some (.error reason) => return .rejected reason
      | none =>
          let some tariff := tariff
            | return .rejected .tariffUnavailable
          match GrainResourceBirthController.prepareSourceBirth profile.compilerProfile
              deployment pins durable profile.semantics tariff source with
          | .error reason => return .rejected (.birthPreparation reason)
          | .ok birth =>
              match GrainResourceBirthTransaction.prepareTargets profile deployment pins
                  durable ambient tariff source birth with
              | .error reason => return .rejected (.grainPreparation reason)
              | .ok grain =>
                  match ← GrainResourceBirthAdmission.admitDecodedNative profile deployment
                      pins durable ambient tariff source birth grain native ingress with
                  | .error reason => return .rejected (.admission reason)
                  | .ok accepted =>
                      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable
                          (intent accepted) with
                      | .confirmed kind _ =>
                          return .confirmed kind (receipt deployment.domain ingress)
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
          return ← receiveLoaded profile deployment pins tariff ambient native
            transport durable bytes

end Minidregg.Kernel.GrainResourceBirthReceiver
