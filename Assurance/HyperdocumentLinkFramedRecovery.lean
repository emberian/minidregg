/-
# Assurance.HyperdocumentLinkFramedRecovery -- one link through guarded bytes

This module instantiates the payload-bearing durable path for the exact linear
link publication built by `HyperdocumentLinkPublicationWitness`.  The existing
accepted content and event effects are sufficient to construct the exact
`PublishedOperation`; no negotiation, promise, or history evidence is
fabricated.

Two byte boundaries are exercised:

* `FramedWalRefinement` persists the erased atomic intent through an explicit
  record-local codec and abstract sync transition;
* `FramedWalRecoveryController` decodes the payload-bearing `DataIntent` and
  rechecks its authority guard before installing canonical bytes.

The distinction matters.  The generic framed WAL cannot interpret a read
guard hidden inside `ReplayEnvelope`.  `GuardedSyncReady` below therefore joins
the WAL's `SyncReady` evidence with the exact data preflight.  The stale tooth
is stated at that stronger boundary and at the recovery controller.  Neither
an opaque reader nor an operating-system `fsync` is refined here.
-/
import Assurance.HyperdocumentGuardedDurable
import Assurance.HyperdocumentLinkPublicationWitness
import Compiler.FramedWalRecoveryController
import Kernel.FramedWalRefinement

namespace Minidregg.Assurance.HyperdocumentLinkFramedRecovery

open Minidregg.Compiler.FramedWalRecoveryController
open Minidregg.Kernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.FramedWalRefinement
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

open Minidregg.Assurance.HyperdocumentLinkPublicationWitness
open Minidregg.Assurance.HyperdocumentGuardedDurable

/-! ## Exact accepted publication and guarded durable plan -/

/-- The witness already contains every field required by `PublishedOperation`.
This packages those exact values; it does not replay the agent negotiation or
invent a second accepted effect. -/
noncomputable def publishedOperation :
    HyperdocumentAgentOperation.PublishedOperation eventAccepted
      header contentCellId eventCellId boundary where
  finalizedContent := linkAccepted.accepted
  finalizedExact := rfl
  publication := commit
  contentPostExact := rfl
  eventPostContains := atomic_event_append
  eventReplayRejected := event_replay_rejected

def authorityCellId : Digest := ⟨905⟩

def stableEvent : StableEvent where
  codecVersion := 1
  domain := ⟨910⟩
  eventId := header.turnId
  canonicalBytes := [108, 105, 110, 107, 45, 112, 117, 98]

def stableNullifier :
    MultiCellHyperedge.JointNullifier
      (HyperdocumentPublication.acceptedLegs linkAccepted
        eventAccepted header contentCellId eventCellId) →
      StableNullifier
  | ⟨.content, value⟩ =>
      { codecVersion := 1
        domain := ⟨911⟩
        nullifierId := ⟨2 * (show Nat from value)⟩
        canonicalBytes := [0, UInt8.ofNat (show Nat from value)] }
  | ⟨.eventLog, value⟩ =>
      { codecVersion := 1
        domain := ⟨911⟩
        nullifierId := ⟨2 * (show Nat from value) + 1⟩
        canonicalBytes := [1, UInt8.ofNat (show Nat from value)] }

def wire : GuardedDurableCommit.WireProjection
    (MultiCellHyperedge.JointNullifier
      (HyperdocumentPublication.acceptedLegs linkAccepted
        eventAccepted header contentCellId eventCellId)) where
  nullifier := stableNullifier
  event := stableEvent

def costPolicy : MultiCellCostPolicy
    (MultiCellHyperedge.JointNullifier
      (HyperdocumentPublication.acceptedLegs linkAccepted
        eventAccepted header contentCellId eventCellId))
    StableEvent where
  base := fun _ => 0
  rootWriteBytes := 32
  nullifierBytes := fun nullifier =>
    (stableNullifier nullifier).canonicalBytes.length
  eventBytes := fun event => event.canonicalBytes.length

noncomputable def bounded :
    BoundedMultiCellCommit commit StableEvent stableEvent where
  policy := costPolicy
  upper := costPolicy.exact 2 (multiCellMemoryTouches commit)
    commit.nullifiers stableEvent
  exact_le_upper := le_rfl

def digestAgreement : GuardedDurableCommit.SharedDigestAgreement
    Genesis.documentMaterializer Genesis.authorityMaterializer
      eventRepresentation where
  eventRootFunction := rfl
  authorityRootFunction := rfl

noncomputable def plan :
    PublicationPlan publishedOperation authorityCellId where
  wire := wire
  bounded := bounded
  digestAgreement := digestAgreement
  authorityDistinctContent := by decide
  authorityDistinctEvent := by decide

abbrev rootBytes : List UInt8 → Digest :=
  Minidregg.Theory.DeployedMaterializerWitness.lengthRoot

abbrev intent : DataIntent rootBytes := plan.toDataIntent

@[simp] theorem document_rootBytes_exact :
    Genesis.documentMaterializer.rootBytes = rootBytes := rfl

@[simp] theorem event_rootBytes_exact :
    eventRepresentation.cellMaterializer.rootBytes = rootBytes := rfl

@[simp] theorem authority_rootBytes_exact :
    Genesis.authorityMaterializer.rootBytes = rootBytes := rfl

@[simp] theorem plan_publication_exact :
    plan.publication = commit := rfl

@[simp] theorem intent_authority_guard_exact :
    intent.readGuards =
      [{ cellId := authorityCellId, expectedRoot := Genesis.authorityPre.root }] :=
  plan.intent_readGuards

@[simp] theorem intent_payloads_exact :
    intent.writes =
      [{ cellId := contentCellId
         expectedPre := genesisPost.root
         exactPost := (commit.post .content).root
         canonicalPostBytes := (commit.post .content).bytes },
       { cellId := eventCellId
         expectedPre := eventAccepted.accepted.prepared.preRoot
         exactPost := (commit.post .eventLog).root
         canonicalPostBytes := (commit.post .eventLog).bytes }] :=
  plan.intent_writes

/-! ## Concrete coherent checkpoint -/

noncomputable def checkpointBytes (cellId : Digest) : List UInt8 :=
  if cellId = contentCellId then genesisPost.bytes
  else if cellId = eventCellId then eventLogPre.{0, 0}.bytes
  else if cellId = authorityCellId then Genesis.authorityPre.bytes
  else []

noncomputable def checkpointModel :
    Snapshot TransactionId CellId StableNullifier ReplayEnvelope where
  roots := fun cellId => rootBytes (checkpointBytes cellId)
  consumed := fun _ => false
  available := fun lane => intent.exactCharge lane + 1
  history := []
  journal := []

noncomputable def checkpoint : DataSnapshot rootBytes where
  model := checkpointModel
  canonicalBytes := checkpointBytes
  coherent := fun _ => rfl

@[simp] theorem checkpoint_content_root :
    checkpoint.model.roots contentCellId =
      genesisPost.root := by
  change rootBytes genesisPost.bytes =
    Genesis.documentMaterializer.rootBytes genesisPost.bytes
  rw [document_rootBytes_exact]

@[simp] theorem checkpoint_event_root :
    checkpoint.model.roots eventCellId = eventLogPre.root := by rfl

@[simp] theorem checkpoint_authority_root :
    checkpoint.model.roots authorityCellId =
      Genesis.authorityPre.root := by
  change rootBytes Genesis.authorityPre.bytes =
    Genesis.authorityMaterializer.rootBytes Genesis.authorityPre.bytes
  rw [authority_rootBytes_exact]

theorem stableNullifier_injective : Function.Injective stableNullifier := by
  intro left right equal
  rcases left with ⟨incidence, value⟩
  rcases right with ⟨incidence', value'⟩
  cases incidence <;> cases incidence' <;>
    simp [stableNullifier] at equal ⊢
  all_goals cases equal.1; rfl

theorem publication_nullifiers_nodup : commit.nullifiers.Nodup := by
  unfold MultiCellHyperedge.Commit.nullifiers
  unfold MultiCellHyperedge.jointNullifiers
  apply List.Nodup.filterMap
  · intro incidence incidence' nullifier present present'
    cases incidence <;> cases incidence' <;>
      simp [HyperdocumentPublication.declaration,
        HyperdocumentOperations.family,
        HyperdocumentVersionEffects.family] at present present' ⊢
    all_goals
      change some _ = some nullifier at present
      change some _ = some nullifier at present'
      injection present with left
      injection present' with right
      have impossible := left.trans right.symm
      cases impossible
  · exact Finset.nodup_toList
      (Finset.univ : Finset HyperdocumentPublication.Incidence)

theorem erased_nullifiers_nodup : intent.erase.nullifiers.Nodup := by
  change (commit.nullifiers.map stableNullifier).Nodup
  exact publication_nullifiers_nodup.map stableNullifier_injective

@[simp] theorem erased_roots_match :
    intent.erase.rootsMatchCheck checkpoint.model = true := by
  rw [Intent.rootsMatchCheck_eq_true_iff]
  intro write member
  rw [DataIntent.erase_rootWrites, intent_payloads_exact] at member
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl
  · exact checkpoint_content_root
  · exact checkpoint_event_root

@[simp] theorem erased_nullifiers_fresh :
    intent.erase.nullifiersFreshCheck checkpoint.model = true := by
  rw [Intent.nullifiersFreshCheck_eq_true_iff]
  simp [checkpoint, checkpointModel]

@[simp] theorem erased_charge_funded :
    Charge.fundedCheck intent.erase.exactCharge
      checkpoint.model.available = true := by
  rw [Charge.fundedCheck_eq_true_iff]
  intro lane
  exact Nat.le_add_right _ 1

@[simp] theorem erased_preflight_checkpoint :
    intent.erase.preflight checkpoint.model = .ok () := by
  unfold Intent.preflight
  split
  · rename_i empty
    have nonempty : intent.erase.rootWrites ≠ [] := by
      rw [DataIntent.erase_rootWrites, intent_payloads_exact]
      simp
    exact (nonempty empty).elim
  · split
    · rename_i duplicate
      have duplicateIds : contentCellId = eventCellId := by
        rw [DataIntent.erase_rootWrites, intent_payloads_exact] at duplicate
        simpa using duplicate
      exact False.elim ((by decide : contentCellId ≠ eventCellId) duplicateIds)
    · simp only [erased_nullifiers_nodup, decide_true, Bool.not_true,
        Bool.false_eq_true, if_false, erased_roots_match,
        erased_nullifiers_fresh, erased_charge_funded]

theorem ready : intent.preflight checkpoint = .ok () := by
  have guards : intent.readGuardsMatchCheck checkpoint = true := by
    rw [DataIntent.readGuardsMatchCheck_eq_true_iff]
    intro guard member
    rw [intent_authority_guard_exact] at member
    simp only [List.mem_singleton] at member
    subst guard
    exact checkpoint_authority_root
  unfold DataIntent.preflight
  rw [guards]
  simp only [Bool.not_true, Bool.false_eq_true, if_false,
    erased_preflight_checkpoint]

@[simp] theorem complete_install :
    Minidregg.Kernel.DurableDataIntent.execute .complete checkpoint intent =
      .accepted (DataSnapshot.install checkpoint intent) := by
  apply PublicationPlan.complete_ready plan checkpoint
  · rfl
  · exact ready

@[simp] theorem installed_link_post_bytes :
    (DataSnapshot.install checkpoint intent).canonicalBytes contentCellId =
      (commit.post .content).bytes := by
  simp [DataSnapshot.install, DataSnapshot.lookupPostBytes]

/-! ## Record-local framed WAL and explicit guarded sync -/

def payloadBytes : List UInt8 := [72, 89, 80, 69, 82, 76, 78, 75]

def checksum (bytes : List UInt8) : UInt8 :=
  bytes.foldl (fun total byte => total + byte) 0

noncomputable def walFrameCodec : FrameCodec
    (Intent TransactionId CellId StableNullifier ReplayEnvelope) where
  magic := 216
  version := 1
  encodePayload := fun _ => payloadBytes
  decodePayload := fun payload =>
    if payload = payloadBytes then some intent.erase else none
  checksum := checksum

theorem wal_roundTrips : walFrameCodec.RoundTrips intent.erase := by
  simp [FrameCodec.RoundTrips, FrameCodec.encodeFrame, FrameCodec.decodeFrame,
    walFrameCodec, payloadBytes, checksum]

noncomputable def stagedDevice :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope where
  checkpoint := checkpoint.model
  durableFrames := []
  tornTail := none
  cache := some (walFrameCodec.encodeFrame intent.erase)

theorem erased_ready : intent.erase.preflight checkpoint.model = .ok () := by
  have dataReady := ready
  unfold DataIntent.preflight at dataReady
  split at dataReady
  · contradiction
  · split at dataReady
    next reason failed => contradiction
    next ok => exact ok

noncomputable def walSyncReady :
    SyncReady walFrameCodec stagedDevice intent.erase where
  records := []
  clean := rfl
  noTornTail := rfl
  staged := rfl
  roundTrip := wal_roundTrips
  unrecorded := rfl
  preflighted := erased_ready

/-- The stronger admission needed when the framed carrier stores an erased
intent: the exact data snapshot and its authority-guarded preflight accompany
the generic WAL evidence. -/
structure GuardedSyncReady
    (dataCheckpoint : DataSnapshot rootBytes)
    (device : DeviceState TransactionId CellId StableNullifier ReplayEnvelope) :
    Prop where
  recoveredModel : DeviceState.recovered walFrameCodec device = dataCheckpoint.model
  dataPreflighted : intent.preflight dataCheckpoint = .ok ()
  walReady : Nonempty (SyncReady walFrameCodec device intent.erase)

theorem guardedSyncReady : GuardedSyncReady checkpoint stagedDevice := by
  refine ⟨rfl, ready, ⟨walSyncReady⟩⟩

noncomputable def syncedDevice :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope :=
  { stagedDevice with
      durableFrames := [walFrameCodec.encodeFrame intent.erase]
      tornTail := none
      cache := none }

noncomputable def syncStep :
    DeviceStep walFrameCodec stagedDevice intent.erase syncedDevice :=
  .sync stagedDevice intent.erase walSyncReady

/-- A crash before the abstract sync point loses only volatile staging. -/
@[simp] theorem crash_before_sync_reopens_checkpoint :
    DeviceState.recovered walFrameCodec { stagedDevice with cache := none } =
      checkpoint.model := rfl

/-- After the explicit abstract sync transition, cold recovery reconstructs
the exact atomic root/journal installation. -/
@[simp] theorem reopen_after_sync :
    DeviceState.recovered walFrameCodec syncedDevice =
      Snapshot.install checkpoint.model intent.erase := by
  exact recovered_after_sync walFrameCodec stagedDevice intent.erase walSyncReady

/-! ## Lean-owned payload recovery controller -/

noncomputable def dataFrameCodec : FrameCodec (DataIntent rootBytes) where
  magic := 216
  version := 1
  encodePayload := fun _ => payloadBytes
  decodePayload := fun payload =>
    if payload = payloadBytes then some intent else none
  checksum := checksum

def pins : Pins where
  controllerId := 162
  domainId := 74
  codecId := 30
  frameMagic := 216
  frameVersion := 1
  frameWidth := 11

noncomputable def controller : Controller rootBytes where
  pins := pins
  frameCodec := dataFrameCodec
  frameWidthPositive := by decide
  magicPinned := rfl
  versionPinned := rfl

def wireHeader : List UInt8 :=
  [pins.controllerId, pins.domainId, pins.codecId]

noncomputable def recoveryBytes : List UInt8 :=
  wireHeader ++ dataFrameCodec.encodeFrame intent

noncomputable def reader (_ : Unit) : Except Unit (List UInt8) :=
  .ok recoveryBytes

@[simp] theorem controller_decodes_exact_intent :
    controller.decodeWire recoveryBytes = .ok [intent] := by
  rfl

@[simp] theorem controller_replays_install :
    replayAll checkpoint [intent] =
      .ok (DataSnapshot.install checkpoint intent) := by
  unfold replayAll replayOne
  rw [complete_install]
  rfl

noncomputable def verifiedRecovery : VerifiedRecovery controller checkpoint where
  returnedBytes := recoveryBytes
  intents := [intent]
  snapshot := DataSnapshot.install checkpoint intent
  decoded := controller_decodes_exact_intent
  replayed := controller_replays_install

@[simp] theorem controller_run_recovers :
    run controller checkpoint reader () = .ok verifiedRecovery := by
  unfold run reader
  simp only
  split
  next reason failed =>
    rw [controller_decodes_exact_intent] at failed
    contradiction
  next intents decoded =>
    have intentsExact : intents = [intent] := by
      rw [controller_decodes_exact_intent] at decoded
      exact (Except.ok.inj decoded).symm
    subst intents
    split
    next reason failed =>
      rw [controller_replays_install] at failed
      contradiction
    next snapshot replayed =>
      have snapshotExact : snapshot = DataSnapshot.install checkpoint intent := by
        rw [controller_replays_install] at replayed
        exact (Except.ok.inj replayed).symm
      subst snapshot
      rfl

@[simp] theorem recovered_link_post_bytes :
    verifiedRecovery.snapshot.canonicalBytes contentCellId =
      (commit.post .content).bytes :=
  installed_link_post_bytes

/-- Re-reading the exact frame after recovery is an idempotent replay, not a
second history append or data installation. -/
@[simp] theorem idempotent_retry :
    replayAll (DataSnapshot.install checkpoint intent) [intent] =
      .ok (DataSnapshot.install checkpoint intent) := by
  change replayAll (DataSnapshot.install checkpoint plan.toDataIntent)
      [plan.toDataIntent] =
    .ok (DataSnapshot.install checkpoint plan.toDataIntent)
  have retry := PublicationPlan.retry_after_install plan .complete checkpoint
  have one : replayOne (DataSnapshot.install checkpoint plan.toDataIntent)
        plan.toDataIntent =
      .ok (DataSnapshot.install checkpoint plan.toDataIntent) := by
    unfold replayOne
    generalize execution :
        Minidregg.Kernel.DurableDataIntent.execute .complete
          (DataSnapshot.install checkpoint plan.toDataIntent)
          plan.toDataIntent = outcome at retry ⊢
    cases outcome <;> simp_all
  simp only [replayAll, one]

/-! ## Authority rotation rejection at the guarded boundaries -/

noncomputable def staleCheckpointBytes (cellId : Digest) : List UInt8 :=
  if cellId = authorityCellId then checkpointBytes cellId ++ [0]
  else checkpointBytes cellId

noncomputable def staleCheckpointModel :
    Snapshot TransactionId CellId StableNullifier ReplayEnvelope where
  roots := fun cellId => rootBytes (staleCheckpointBytes cellId)
  consumed := checkpoint.model.consumed
  available := checkpoint.model.available
  history := checkpoint.model.history
  journal := checkpoint.model.journal

noncomputable def staleCheckpoint : DataSnapshot rootBytes where
  model := staleCheckpointModel
  canonicalBytes := staleCheckpointBytes
  coherent := fun _ => rfl

theorem authority_moved :
    staleCheckpoint.model.roots authorityCellId ≠
      Genesis.authorityPre.root := by
  change
    Minidregg.Theory.DeployedMaterializerWitness.lengthRoot
        (Genesis.authorityPre.bytes ++ [0]) ≠
      Minidregg.Theory.DeployedMaterializerWitness.lengthRoot
        Genesis.authorityPre.bytes
  simp [Minidregg.Theory.DeployedMaterializerWitness.lengthRoot]

@[simp] theorem stale_authority_preflight_rejected :
    intent.preflight staleCheckpoint = .error .staleReadGuard :=
  PublicationPlan.stale_authority_rejected plan staleCheckpoint
    authority_moved

@[simp] theorem stale_authority_controller_rejected :
    replayAll staleCheckpoint [intent] =
      .error (.rejected .staleReadGuard) := by
  have unrecorded :
      Snapshot.lookupRecorded intent.transactionId
          staleCheckpoint.model.journal = none := rfl
  have rejected :
      Minidregg.Kernel.DurableDataIntent.execute .complete
          staleCheckpoint intent = .rejected .staleReadGuard := by
    unfold Minidregg.Kernel.DurableDataIntent.execute
    rw [unrecorded, stale_authority_preflight_rejected]
  unfold replayAll replayOne
  rw [rejected]

/-- No authority-stale checkpoint can produce the stronger guarded sync
evidence.  This is the exact obligation absent from the generic erased WAL. -/
theorem stale_authority_has_no_guarded_sync
    (device : DeviceState TransactionId CellId StableNullifier ReplayEnvelope)
    (_recovered : DeviceState.recovered walFrameCodec device =
      staleCheckpoint.model) :
    ¬ GuardedSyncReady staleCheckpoint device := by
  rintro guarded
  have accepted := guarded.dataPreflighted
  rw [stale_authority_preflight_rejected] at accepted
  contradiction

end


end Minidregg.Assurance.HyperdocumentLinkFramedRecovery

/-! Assurance-facing theorem audit. -/

/-- info: 'Minidregg.Assurance.HyperdocumentLinkFramedRecovery.installed_link_post_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.HyperdocumentLinkFramedRecovery.installed_link_post_bytes
/-- info: 'Minidregg.Assurance.HyperdocumentLinkFramedRecovery.reopen_after_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.HyperdocumentLinkFramedRecovery.reopen_after_sync
/-- info: 'Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller_run_recovers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller_run_recovers
/-- info: 'Minidregg.Assurance.HyperdocumentLinkFramedRecovery.idempotent_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.HyperdocumentLinkFramedRecovery.idempotent_retry
/-- info: 'Minidregg.Assurance.HyperdocumentLinkFramedRecovery.stale_authority_has_no_guarded_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.HyperdocumentLinkFramedRecovery.stale_authority_has_no_guarded_sync
