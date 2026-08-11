/-
# Assurance.HyperdocumentMergeDurableFinalityWitness -- recover and finalize the merge

The two-parent kernel witness already publishes exact content and event-log
posts, and the history witness retains the resulting merge event and conflict
opening.  This module joins those exact values to the durable and replicated
settlement carriers:

* the payload-bearing intent contains the exact two canonical post images and
  an exact read-only authority guard;
* guard checking and framed-WAL readiness are bundled, so the generic WAL
  layer cannot silently forget the authority observation;
* one checked frame survives sync, crash, a torn successor, and retry;
* a concrete intersecting quorum finalizes the exact erased replay envelope;
* recovered and finalized meaning retain the committed `ConflictRecord`, the
  merge history entry, and both canonical post byte images.

This is a closed semantic witness.  `DeviceStep.sync` remains an abstract
device action, quorum votes are Lean data rather than authenticated network
messages, the length digest is not collision resistant, and neither storage
nor network liveness is derived.  A physical implementation must still refine
its I/O, voting, transport, and progress mechanisms to these carriers.
-/
import Assurance.HyperdocumentTwoParentHistoryWitness
import Kernel.GuardedDurableCommit
import Kernel.FramedWalRefinement
import Kernel.ReplicatedSettlementFinality

namespace Minidregg.Assurance.HyperdocumentMergeDurableFinalityWitness

open Minidregg.Assurance.HyperdocumentHistoryAdmission
open Minidregg.Kernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.FramedWalRefinement
open Minidregg.Kernel.GuardedDurableCommit
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

namespace Merge
export Minidregg.Kernel.HyperdocumentTwoParentWitness
  (durableIntent contentCellId eventCellId commit baseCell logCell
    stale_authority_rejects)
noncomputable def authorityPre :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.authorityPre
end Merge

namespace History
export Minidregg.Assurance.HyperdocumentTwoParentHistoryWitness
  (head mergeEntry mergePosition mergeEventDeclaration conflictId conflictRecord
    committed_conflict_survives)
end History

set_option autoImplicit false

noncomputable section

abbrev WalIntent := Intent TransactionId CellId StableNullifier ReplayEnvelope

noncomputable def rootBytes : List UInt8 → Digest :=
  Minidregg.Kernel.DurableDataIntent.Witness.lengthRoot

noncomputable def authorityCellId : CellId := ⟨905⟩

noncomputable def authorityGuard : ReadGuard where
  cellId := authorityCellId
  expectedRoot := Merge.authorityPre.root

/-! ## Exact guarded bytes -/

@[simp] theorem durable_writes_exact :
    Merge.durableIntent.writes =
      [({ cellId := Merge.contentCellId
          expectedPre := Merge.baseCell.root
          exactPost := (Merge.commit.post .content).root
          canonicalPostBytes := (Merge.commit.post .content).bytes } : DataWrite),
       ({ cellId := Merge.eventCellId
          expectedPre := Merge.logCell.root
          exactPost := (Merge.commit.post .eventLog).root
          canonicalPostBytes := (Merge.commit.post .eventLog).bytes } : DataWrite)] :=
  rfl

@[simp] theorem durable_authority_guard_exact :
    Merge.durableIntent.readGuards = [authorityGuard] :=
  rfl

theorem install_preserves_exact_authority
    (before : DataSnapshot rootBytes) :
    (DataSnapshot.install before Merge.durableIntent).model.roots
          authorityCellId = before.model.roots authorityCellId /\
      (DataSnapshot.install before Merge.durableIntent).canonicalBytes
          authorityCellId = before.canonicalBytes authorityCellId := by
  exact install_preserves_read_guard before Merge.durableIntent authorityGuard
    (by simp)

/-! ## A coherent exact pre-snapshot -/

noncomputable def beforeBytes (cellId : CellId) : List UInt8 :=
  if cellId = Merge.contentCellId then Merge.baseCell.bytes
  else if cellId = Merge.eventCellId then Merge.logCell.bytes
  else if cellId = authorityCellId then Merge.authorityPre.bytes
  else []

noncomputable def beforeModel :
    Snapshot TransactionId CellId StableNullifier ReplayEnvelope where
  roots := fun cellId => rootBytes (beforeBytes cellId)
  consumed := fun _ => false
  available := fun _ => 0
  history := []
  journal := []

noncomputable def before : DataSnapshot rootBytes where
  model := beforeModel
  canonicalBytes := beforeBytes
  coherent := fun _ => rfl

@[simp] theorem before_content_root :
    before.model.roots Merge.contentCellId = Merge.baseCell.root := by
  rfl

@[simp] theorem before_event_root :
    before.model.roots Merge.eventCellId = Merge.logCell.root := by
  rfl

@[simp] theorem before_authority_root :
    before.model.roots authorityCellId = Merge.authorityPre.root := by
  rfl

theorem content_event_cells_distinct :
    Merge.contentCellId ≠ Merge.eventCellId := by decide

@[simp] theorem erased_roots_match :
    Merge.durableIntent.erase.rootsMatchCheck before.model = true := by
  rw [Intent.rootsMatchCheck_eq_true_iff]
  intro write member
  change write ∈
    [({ cellId := Merge.contentCellId
        expectedPre := Merge.baseCell.root
        exactPost := (Merge.commit.post .content).root } : RootWrite CellId),
     ({ cellId := Merge.eventCellId
        expectedPre := Merge.logCell.root
        exactPost := (Merge.commit.post .eventLog).root } : RootWrite CellId)] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact before_content_root
  · exact before_event_root

@[simp] theorem erased_nullifiers_fresh :
    Merge.durableIntent.erase.nullifiersFreshCheck before.model = true := by
  rw [Intent.nullifiersFreshCheck_eq_true_iff]
  simp [Merge.durableIntent]

@[simp] theorem erased_charge_funded :
    Charge.fundedCheck Merge.durableIntent.erase.exactCharge
      before.model.available = true := by
  rw [Charge.fundedCheck_eq_true_iff]
  intro lane
  rfl

@[simp] theorem erased_preflight_before_model :
    Merge.durableIntent.erase.preflight before.model = .ok () := by
  unfold Intent.preflight
  split
  · rename_i empty
    have nonempty : Merge.durableIntent.erase.rootWrites ≠ [] := by
      simp [Merge.durableIntent, DataIntent.erase]
    exact (nonempty empty).elim
  · split
    · rename_i duplicate
      have duplicateIds : Merge.contentCellId = Merge.eventCellId := by
        simpa [Merge.durableIntent, DataIntent.erase] using duplicate
      exact (content_event_cells_distinct duplicateIds).elim
    · have nullifierNodup : Merge.durableIntent.erase.nullifiers.Nodup := by
        simp [Merge.durableIntent, DataIntent.erase]
      simp only [nullifierNodup, decide_true, Bool.not_true,
        Bool.false_eq_true, if_false, erased_roots_match,
        erased_nullifiers_fresh, erased_charge_funded]

@[simp] theorem data_preflight_ready :
    Merge.durableIntent.preflight before = .ok () := by
  have guards : Merge.durableIntent.readGuardsMatchCheck before = true := by
    rw [DataIntent.readGuardsMatchCheck_eq_true_iff]
    intro guard member
    rw [durable_authority_guard_exact] at member
    simp only [List.mem_singleton] at member
    subst guard
    exact before_authority_root
  unfold DataIntent.preflight
  rw [guards]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  have mapped := congrArg
    (fun outcome : Except DurableCommitProtocol.RejectReason Unit =>
      match outcome with
      | .error reason => Except.error (RejectReason.durable reason)
      | .ok () => Except.ok ())
    erased_preflight_before_model
  exact mapped

@[simp] theorem data_complete_installs :
    Minidregg.Kernel.DurableDataIntent.execute .complete before
      Merge.durableIntent =
        .accepted (DataSnapshot.install before Merge.durableIntent) := by
  apply Minidregg.Kernel.DurableDataIntent.execute_complete_ready
  · rfl
  · exact data_preflight_ready

@[simp] theorem installed_content_bytes :
    (DataSnapshot.install before Merge.durableIntent).canonicalBytes
        Merge.contentCellId = (Merge.commit.post .content).bytes := by
  rfl

@[simp] theorem installed_event_bytes :
    (DataSnapshot.install before Merge.durableIntent).canonicalBytes
        Merge.eventCellId = (Merge.commit.post .eventLog).bytes := by
  rfl

/-! ## Exact framed WAL, crash, and retry -/

/-- A deliberately narrow frame codec which accepts the one exact erased
merge intent.  Its checksum/version framing is real; its payload codec is an
inhabitation witness, not a production serialization or CR claim. -/
noncomputable def frameCodec : FrameCodec WalIntent where
  magic := 219
  version := 1
  encodePayload := fun _ => [77, 69, 82, 71, 69]
  decodePayload := fun payload =>
    if payload = [77, 69, 82, 71, 69]
    then some Merge.durableIntent.erase else none
  checksum := fun bytes => bytes.foldl (fun acc byte => acc + byte) 0

@[simp] theorem frame_roundTrips :
    frameCodec.RoundTrips Merge.durableIntent.erase := by
  rfl

noncomputable def beforeDevice :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope where
  checkpoint := before.model
  durableFrames := []
  tornTail := none
  cache := some (frameCodec.encodeFrame Merge.durableIntent.erase)

@[simp] theorem erased_preflight_ready :
    Merge.durableIntent.erase.preflight
      (DeviceState.recovered frameCodec beforeDevice) = .ok () := by
  exact erased_preflight_before_model

noncomputable def framedReady : SyncReady frameCodec beforeDevice
    Merge.durableIntent.erase where
  records := []
  clean := rfl
  noTornTail := rfl
  staged := rfl
  roundTrip := frame_roundTrips
  unrecorded := rfl
  preflighted := erased_preflight_ready

/-- A guarded sync proof keeps the payload-bearing read-guard check adjacent
to the exact generic frame readiness.  This is the missing condition the
erased WAL intent cannot reconstruct by itself. -/
structure GuardedSyncReady
    (device : DeviceState TransactionId CellId StableNullifier ReplayEnvelope)
    (data : DataSnapshot rootBytes) : Type where
  recoveredModelExact : data.model = DeviceState.recovered frameCodec device
  guardAndDataReady : Merge.durableIntent.preflight data = .ok ()
  framed : SyncReady frameCodec device Merge.durableIntent.erase

noncomputable def guardedReady : GuardedSyncReady beforeDevice before where
  recoveredModelExact := rfl
  guardAndDataReady := data_preflight_ready
  framed := framedReady

noncomputable def syncedDevice :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope where
  checkpoint := before.model
  durableFrames := [frameCodec.encodeFrame Merge.durableIntent.erase]
  tornTail := none
  cache := none

noncomputable def syncStep : DeviceStep frameCodec beforeDevice
    Merge.durableIntent.erase syncedDevice :=
  .sync beforeDevice Merge.durableIntent.erase framedReady

@[simp] theorem recovered_after_sync_exact :
    DeviceState.recovered frameCodec syncedDevice =
      Snapshot.install before.model Merge.durableIntent.erase := by
  exact recovered_after_sync frameCodec beforeDevice Merge.durableIntent.erase
    framedReady

noncomputable def crashedWithTornSuccessor :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope where
  checkpoint := syncedDevice.checkpoint
  durableFrames := syncedDevice.durableFrames
  tornTail := some ((frameCodec.encodeFrame Merge.durableIntent.erase).take 3)
  cache := none

@[simp] theorem torn_successor_preserves_recovery :
    DeviceState.recovered frameCodec crashedWithTornSuccessor =
      Snapshot.install before.model Merge.durableIntent.erase := by
  rw [show DeviceState.recovered frameCodec crashedWithTornSuccessor =
      DeviceState.recovered frameCodec syncedDevice from rfl]
  exact recovered_after_sync_exact

@[simp] theorem retry_after_crash_replays :
    Minidregg.Kernel.DurableCommitProtocol.execute .complete
      (DeviceState.recovered frameCodec crashedWithTornSuccessor)
      Merge.durableIntent.erase = .replayed Merge.durableIntent.erase := by
  rw [torn_successor_preserves_recovery]
  exact execute_retry_after_install .complete before.model
    Merge.durableIntent.erase

@[simp] theorem recovered_history_exact :
    (DeviceState.recovered frameCodec crashedWithTornSuccessor).history =
      [Merge.durableIntent.erase.event] := by
  rw [torn_successor_preserves_recovery]
  rfl

theorem recovered_retains_exact_post_bytes :
    ∃ envelope ∈
        (DeviceState.recovered frameCodec crashedWithTornSuccessor).history,
      ∃ contentWrite ∈ envelope.writes,
        contentWrite.cellId = Merge.contentCellId /\
        contentWrite.canonicalPostBytes = (Merge.commit.post .content).bytes /\
      ∃ eventWrite ∈ envelope.writes,
        eventWrite.cellId = Merge.eventCellId /\
        eventWrite.canonicalPostBytes = (Merge.commit.post .eventLog).bytes := by
  refine ⟨Merge.durableIntent.erase.event, ?_, ?_⟩
  · simp
  · refine ⟨Merge.durableIntent.writes[0], ?_, rfl, rfl, ?_⟩
    · simp [durable_writes_exact]
    · refine ⟨Merge.durableIntent.writes[1], ?_, rfl, rfl⟩
      simp [durable_writes_exact]

/-- Recovery retains not just roots: the replay envelope carries both exact
post byte images, and the semantic witnesses identify the surviving conflict
and exact merge entry in the verified head. -/
theorem recovered_retains_conflict_and_history_entry :
    (∃ envelope ∈
        (DeviceState.recovered frameCodec crashedWithTornSuccessor).history,
      envelope = Merge.durableIntent.erase.event) /\
      lookup (Merge.commit.post .content).logical .conflicts History.conflictId =
        some History.conflictRecord /\
      Nonempty (EntryAt History.head History.mergeEntry) := by
  refine ⟨?_, History.committed_conflict_survives, ⟨History.mergePosition⟩⟩
  exact ⟨Merge.durableIntent.erase.event, by simp, rfl⟩

/-! ## Stale authority cannot cross the guarded sync boundary -/

theorem stale_authority_rejects_guarded_sync
    (device : DeviceState TransactionId CellId StableNullifier ReplayEnvelope)
    (current : DataSnapshot rootBytes)
    (authorityMoved :
      current.model.roots authorityCellId ≠ Merge.authorityPre.root) :
    ¬ Nonempty (GuardedSyncReady device current) := by
  rintro ⟨ready⟩
  have stale := Merge.stale_authority_rejects current authorityMoved
  have impossible := ready.guardAndDataReady.symm.trans stale
  cases impossible

/-! ## One exact finalized quorum and failover replica -/

abbrev Replica := Fin 3

noncomputable def quorumCore : Finset Replica := {0, 1}

noncomputable def quorums : QuorumSystem Replica where
  isQuorum voters := quorumCore ⊆ voters
  intersects := by
    intro left right leftQuorum rightQuorum
    refine ⟨0, leftQuorum ?_, rightQuorum ?_⟩ <;> simp [quorumCore]

noncomputable def candidate : Candidate TransactionId CellId StableNullifier
    ReplayEnvelope :=
  Candidate.ofData 1 [] Merge.durableIntent

noncomputable def voteBook : VoteBook (Node := Replica)
    (TxId := TransactionId) (CellId := CellId)
    (Nullifier := StableNullifier) (Event := ReplayEnvelope) :=
  fun _ => [candidate]

noncomputable def discipline : PrefixDiscipline voteBook where
  compatible := by
    intro node left right leftVote rightVote
    simp only [voteBook, List.mem_singleton] at leftVote rightVote
    subst left
    subst right
    exact .inl List.prefix_rfl

noncomputable def finalized : Finalized quorums voteBook candidate where
  voters := quorumCore
  quorum := fun _ member => member
  voted := by simp [voteBook]

@[simp] theorem finalized_intent_exact :
    candidate.intent = Merge.durableIntent.erase := rfl

noncomputable def replica :
    DurableReplica frameCodec before.model candidate where
  device := crashedWithTornSuccessor
  checkpoint_exact := rfl
  decoded_exact := by
    change DeviceState.decodeAll frameCodec
      [frameCodec.encodeFrame Merge.durableIntent.erase] =
        some [Merge.durableIntent.erase]
    simp only [DeviceState.decodeAll]
    rw [frame_roundTrips]
    rfl

@[simp] theorem finalized_failover_recovery :
    DeviceState.recovered frameCodec replica.device =
      candidate.log.foldl Snapshot.install before.model :=
  replica.recovered_exact

@[simp] theorem finalized_retry_is_idempotent :
    Minidregg.Kernel.DurableCommitProtocol.execute .complete
      (DeviceState.recovered frameCodec replica.device) candidate.intent =
        .replayed candidate.intent :=
  replica.retry_after_failover_replays

/-- The finalized candidate's exact payload is the same recovered merge whose
content conflict and proof-relevant history entry were already established. -/
theorem finalized_retains_conflict_and_history_entry :
    candidate.intent = Merge.durableIntent.erase /\
      lookup (Merge.commit.post .content).logical .conflicts History.conflictId =
        some History.conflictRecord /\
      Nonempty (EntryAt History.head History.mergeEntry) :=
  ⟨finalized_intent_exact, History.committed_conflict_survives,
    ⟨History.mergePosition⟩⟩

/-- Quorum intersection plus the concrete vote-book prefix discipline rejects
any other finalized payload at this exact slot. -/
theorem conflicting_same_slot_finalize_rejected
    {other : Candidate TransactionId CellId StableNullifier ReplayEnvelope}
    (otherFinal : Finalized quorums voteBook other)
    (sameSlot : other.slot = candidate.slot)
    (different : other.intent ≠ candidate.intent) : False := by
  have safe := no_conflicting_finalized_transactions discipline finalized otherFinal
  apply safe
  exact ⟨sameSlot.symm, fun equal => different equal.symm⟩

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentMergeDurableFinalityWitness.recovered_after_sync_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recovered_after_sync_exact
/-- info: 'Minidregg.Assurance.HyperdocumentMergeDurableFinalityWitness.recovered_retains_conflict_and_history_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recovered_retains_conflict_and_history_entry
/-- info: 'Minidregg.Assurance.HyperdocumentMergeDurableFinalityWitness.stale_authority_rejects_guarded_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_authority_rejects_guarded_sync
/-- info: 'Minidregg.Assurance.HyperdocumentMergeDurableFinalityWitness.finalized_retains_conflict_and_history_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finalized_retains_conflict_and_history_entry
/-- info: 'Minidregg.Assurance.HyperdocumentMergeDurableFinalityWitness.conflicting_same_slot_finalize_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conflicting_same_slot_finalize_rejected

end


end Minidregg.Assurance.HyperdocumentMergeDurableFinalityWitness
