/-
# Assurance.ZkmlMatmulFramedWal — checked output through framed recovery

The exact matmul audit turn already joins a proof-bearing byte check to one
payload-bearing `DataIntent`.  This module carries that same erased intent
through the existing physical-boundary model:

* a distinct versioned, checksummed frame contains the transaction, output
  write, checked output bytes, and audit bytes of the exact turn;
* the one admitted record has an exhibited codec round trip;
* a torn pre-sync frame recovers the old checkpoint;
* the abstract sync barrier recovers the exact atomic install;
* a later torn successor cannot erase the committed prefix; and
* cold-start retry returns the exact journaled replay envelope, which still
  contains the output bytes derived from the proof-bearing checker branch.

The ceiling is deliberate.  The payload decoder below admits exactly this
closed v1 record, rather than claiming a production registry or general wire
codec.  `DeviceStep.sync` is an abstract device transition.  Nothing here is
a theorem about POSIX `fsync`, a filesystem, a disk controller, stable media,
or liveness; a deployment must refine its actual I/O to `DeviceStep`.
-/
import Assurance.ZkmlMatmulAuditTurn
import Kernel.FramedWalRefinement

namespace Minidregg.Assurance.ZkmlMatmulFramedWal

open Minidregg.Assurance.ZkmlMatmulAuditTurn
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.FramedWalRefinement

set_option autoImplicit false

noncomputable section

abbrev WalIntent := Intent TransactionId CellId StableNullifier ReplayEnvelope

/-! ## One exact versioned record -/

/-- Closed v1 payload layout:

`tx || write-count || cell || pre-root || post-root-u16le || output-length ||
 output || guard-count || audit-length || audit`.

All values are the exact bounded matmul turn.  The surrounding `FrameCodec`
adds a distinct magic byte, framing version, and checksum. -/
def payloadV1 : List UInt8 :=
  [200, 1, 201, 8, 156, 1, 4] ++ outputBytes ++
    [0, 10] ++ auditEventBytes

@[simp] theorem payload_checked_output_exact :
    (payloadV1.drop 7).take 4 =
      ZkmlMatmulChecker.canonicalBytes.drop 16 := by
  decide

@[simp] theorem payload_audit_exact :
    payloadV1.drop 13 = auditEventBytes := by
  decide

/-- A deliberately closed payload codec.  Encoding any other logical intent
produces an unadmitted payload; decoding accepts only this exact record. -/
noncomputable def frameCodec : FrameCodec WalIntent where
  magic := 221
  version := 1
  encodePayload := fun intent =>
    if intent = durableIntent.erase then payloadV1 else []
  decodePayload := fun payload =>
    if payload = payloadV1 then some durableIntent.erase else none
  checksum := fun bytes => bytes.foldl (fun acc byte => acc + byte) 0

@[simp] theorem frame_roundTrips :
    frameCodec.RoundTrips durableIntent.erase := by
  rfl

theorem wrong_version_refused :
    frameCodec.decodeFrame
        (frameCodec.magic :: 2 :: payloadV1 ++ [0]) = none := by
  apply FrameCodec.decodeFrame_wrongVersion
  decide

/-- The valid checksum is 90; replacing it by 91 fails before payload decode. -/
def corruptFrame : List UInt8 :=
  [frameCodec.magic, frameCodec.version] ++ payloadV1 ++ [91]

@[simp] theorem corrupt_frame_refused :
    frameCodec.decodeFrame corruptFrame = none := by
  decide

/-! ## Stage, tear, sync, recover, retry -/

noncomputable def beforeDevice :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope where
  checkpoint := durableBefore.model
  durableFrames := []
  tornTail := none
  cache := some (frameCodec.encodeFrame durableIntent.erase)

@[simp] theorem erased_preflight_ready :
    durableIntent.erase.preflight
      (DeviceState.recovered frameCodec beforeDevice) = .ok () := by
  decide

noncomputable def syncReady :
    SyncReady frameCodec beforeDevice durableIntent.erase where
  records := []
  clean := rfl
  noTornTail := rfl
  staged := rfl
  roundTrip := frame_roundTrips
  unrecorded := rfl
  preflighted := erased_preflight_ready

/-- A strict prefix written before sync never enters recovered meaning. -/
noncomputable def tornBeforeSync :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope where
  checkpoint := beforeDevice.checkpoint
  durableFrames := beforeDevice.durableFrames
  tornTail := some ((frameCodec.encodeFrame durableIntent.erase).take 7)
  cache := none

noncomputable def tornBeforeSyncStep :
    DeviceStep frameCodec beforeDevice durableIntent.erase tornBeforeSync :=
  .tear beforeDevice durableIntent.erase rfl 7 (by decide)

@[simp] theorem torn_before_sync_recovers_old :
    DeviceState.recovered frameCodec tornBeforeSync = durableBefore.model := by
  rfl

@[simp] theorem torn_before_sync_reports_tail :
    DeviceState.recoveryStatus frameCodec tornBeforeSync =
      .ignoredTornTail := by
  rfl

noncomputable def syncedDevice :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope where
  checkpoint := durableBefore.model
  durableFrames := [frameCodec.encodeFrame durableIntent.erase]
  tornTail := none
  cache := none

noncomputable def syncStep :
    DeviceStep frameCodec beforeDevice durableIntent.erase syncedDevice :=
  .sync beforeDevice durableIntent.erase syncReady

/-- The byte-device sync is not a second commit semantics: it recovers the
exact install already defined by the atomic durable protocol. -/
@[simp] theorem recovered_after_sync_exact :
    DeviceState.recovered frameCodec syncedDevice =
      Snapshot.install durableBefore.model durableIntent.erase := by
  exact recovered_after_sync frameCodec beforeDevice durableIntent.erase syncReady

/-- The complete device transition system for this codec inherits the generic
WAL-to-atomic-protocol simulation. -/
noncomputable def refinement :
    ImplementationRefinement TransactionId CellId StableNullifier ReplayEnvelope
      (DeviceState TransactionId CellId StableNullifier ReplayEnvelope)
      (DeviceStep frameCodec) (Represents frameCodec) :=
  deviceRefinement frameCodec

/-- A torn frame after the committed frame is kept outside the durable segment
list and cannot erase the recovered atomic install. -/
noncomputable def committedWithTornSuccessor :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope where
  checkpoint := syncedDevice.checkpoint
  durableFrames := syncedDevice.durableFrames
  tornTail := some ((frameCodec.encodeFrame durableIntent.erase).take 5)
  cache := none

@[simp] theorem torn_successor_preserves_install :
    DeviceState.recovered frameCodec committedWithTornSuccessor =
      Snapshot.install durableBefore.model durableIntent.erase := by
  rw [show DeviceState.recovered frameCodec committedWithTornSuccessor =
      DeviceState.recovered frameCodec syncedDevice from rfl]
  exact recovered_after_sync_exact

@[simp] theorem retry_after_reopen_replays :
    Minidregg.Kernel.DurableCommitProtocol.execute .complete
      (DeviceState.recovered frameCodec committedWithTornSuccessor)
      durableIntent.erase = .replayed durableIntent.erase := by
  rw [torn_successor_preserves_install]
  exact execute_retry_after_install .complete durableBefore.model
    durableIntent.erase

@[simp] theorem recovered_history_exact :
    (DeviceState.recovered frameCodec committedWithTornSuccessor).history =
      [durableIntent.erase.event] := by
  rw [torn_successor_preserves_install]
  rfl

/-- The cold-start journal retains the exact output derived by the checker,
not merely its post root or an executor-supplied acceptance bit. -/
theorem recovered_retains_checked_output :
    (∃ checked,
      ZkmlMatmulChecker.check ZkmlMatmulChecker.expected
          ZkmlMatmulChecker.canonicalBytes = .ok checked ∧
        checked.candidate.output =
          ZkmlMatmulChecker.contraction checked.candidate.left
            checked.candidate.right) ∧
    ∃ envelope ∈
        (DeviceState.recovered frameCodec committedWithTornSuccessor).history,
      ∃ write ∈ envelope.writes,
        write.cellId = computationCell ∧
        write.canonicalPostBytes =
          ZkmlMatmulChecker.canonicalBytes.drop 16 := by
  refine ⟨candidate_checked, durableIntent.erase.event, ?_, resultWrite, ?_, rfl, ?_⟩
  · simp
  · simp [durableIntent]
  · exact candidate_output_bytes_exact.symm

/-! ## Corruption and stale-root teeth -/

noncomputable def corruptedDevice :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope where
  checkpoint := durableBefore.model
  durableFrames := [corruptFrame]
  tornTail := none
  cache := none

@[simp] theorem corruption_reports_fault :
    DeviceState.recoveryStatus frameCodec corruptedDevice = .corruptFrame := by
  decide

@[simp] theorem corruption_fails_closed_to_checkpoint :
    DeviceState.recovered frameCodec corruptedDevice = durableBefore.model := by
  simp [DeviceState.recovered, DeviceState.decodeAll, corruptedDevice]

noncomputable def staleDevice :
    DeviceState TransactionId CellId StableNullifier ReplayEnvelope where
  checkpoint :=
    { durableBefore.model with
      roots := fun cell => if cell = computationCell then ⟨9⟩
        else durableBefore.model.roots cell }
  durableFrames := []
  tornTail := none
  cache := some (frameCodec.encodeFrame durableIntent.erase)

@[simp] theorem stale_preflight :
    durableIntent.erase.preflight
      (DeviceState.recovered frameCodec staleDevice) =
        .error .stalePreRoot := by
  decide

theorem stale_cannot_sync :
    ¬ Nonempty (SyncReady frameCodec staleDevice durableIntent.erase) :=
  no_sync_of_preflight_error frameCodec staleDevice durableIntent.erase
    .stalePreRoot stale_preflight

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.ZkmlMatmulFramedWal.recovered_after_sync_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recovered_after_sync_exact
/-- info: 'Minidregg.Assurance.ZkmlMatmulFramedWal.refinement' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms refinement
/-- info: 'Minidregg.Assurance.ZkmlMatmulFramedWal.recovered_retains_checked_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recovered_retains_checked_output
/-- info: 'Minidregg.Assurance.ZkmlMatmulFramedWal.stale_cannot_sync' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms stale_cannot_sync

end


end Minidregg.Assurance.ZkmlMatmulFramedWal
