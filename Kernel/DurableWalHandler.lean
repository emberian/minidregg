/-
# Kernel.DurableWalHandler -- the first inhabitant of `ImplementationRefinement`

`DurableCommitProtocol` ends by exposing `ImplementationRefinement` as the
premise a real handler owes, and then deliberately constructs no instance.
Until something inhabits it, every durable claim in this tree rests on a
structure nobody has shown is satisfiable by a machine that stores anything.

This module supplies one: a write-ahead log with a volatile staging slot, a
durable append-only committed region, and a compacting checkpoint.  Recovery is
a fold, a crash drops exactly the volatile slot, and compaction is proved
invisible to recovery.  `walRefinement` is a real `ImplementationRefinement`.

**What this is not.**  `WalState` is a model of a log device, not a device.
There is no `fsync`, no torn or partially-written record, no byte codec, no
page cache, no replication, no fault-domain, no clock, and no liveness or
availability claim.  A physical implementation must exhibit ITS state as a
`WalState` and ITS transitions as `WalStep`s, and that obligation is untouched
here.  What is now settled is narrower and was previously open: the refinement
premise is satisfiable by a handler that stages, commits, crashes, and
compacts -- so the durable model is not vacuously refinable-in-principle only.

The load-bearing direction is the negative one.  `commit` carries the
protocol's own fail-closed guards as fields, and
`unguarded_append_breaks_refinement` shows why: drop the idempotency guard and
a re-submitted transaction produces a durable state that NO schedule of the
model represents.  The guard is not decoration on the happy path; it is the
step's admissibility.
-/
import Kernel.DurableCommitProtocol

namespace Minidregg.Kernel.DurableWalHandler

open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Theory

set_option autoImplicit false

universe u v w x

variable {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}

/-! ## The device model -/

/-- One write-ahead log.  `committed` is the durable append-only region, oldest
first; `staged` is the volatile slot a record occupies after preparation and
before its commit marker reaches the device.  `checkpoint` is the compacted
prefix a cold start would read before replaying `committed`. -/
structure WalState
    (TxId : Type u) (CellId : Type v) (Nullifier : Type w) (Event : Type x) where
  checkpoint : Snapshot TxId CellId Nullifier Event
  committed : List (Intent TxId CellId Nullifier Event)
  staged : Option (Intent TxId CellId Nullifier Event)

namespace WalState

variable [DecidableEq CellId] [DecidableEq Nullifier]

/-- Cold-start recovery: replay the durable region over the checkpoint.  The
volatile slot contributes nothing, which is the whole point of a commit
marker. -/
def recovered (device : WalState TxId CellId Nullifier Event) :
    Snapshot TxId CellId Nullifier Event :=
  device.committed.foldl Snapshot.install device.checkpoint

/-- Staging touches no durable region, so it cannot move recovery. -/
@[simp] theorem recovered_stage (device : WalState TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    recovered { device with staged := some intent } = recovered device := rfl

/-- Neither does losing the volatile slot.  This is the crash. -/
@[simp] theorem recovered_dropStaged
    (device : WalState TxId CellId Nullifier Event) :
    recovered { device with staged := none } = recovered device := rfl

/-- **The commit marker is exactly one install.**  Appending a record to the
durable region moves recovery by the model's single atomic operation and
nothing else. -/
@[simp] theorem recovered_append (device : WalState TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (slot : Option (Intent TxId CellId Nullifier Event)) :
    recovered { checkpoint := device.checkpoint
                committed := device.committed ++ [intent]
                staged := slot } =
      Snapshot.install device.recovered intent := by
  simp [recovered, List.foldl_append]

/-- **Compaction is invisible to recovery.**  Folding the oldest durable record
into the checkpoint and dropping it from the log leaves the recovered snapshot
identical -- the property that makes a checkpoint a checkpoint rather than a
second source of truth. -/
@[simp] theorem recovered_checkpointOne
    (device : WalState TxId CellId Nullifier Event)
    (oldest : Intent TxId CellId Nullifier Event)
    (rest : List (Intent TxId CellId Nullifier Event))
    (region : device.committed = oldest :: rest) :
    recovered { checkpoint := Snapshot.install device.checkpoint oldest
                committed := rest
                staged := device.staged } = device.recovered := by
  rw [recovered, recovered, region]
  rfl

end WalState

/-! ## The handler's transitions -/

/-- The device's admissible steps.  Every constructor is a physical action a
log-backed handler actually takes, and `commit` carries the protocol's own
fail-closed guards because appending without them is not a correct step (see
`unguarded_append_breaks_refinement`). -/
inductive WalStep
    [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
    [DecidableEq Event] :
    WalState TxId CellId Nullifier Event ->
      Intent TxId CellId Nullifier Event ->
      WalState TxId CellId Nullifier Event -> Type (max u v w x)
  /-- Write the record into the volatile slot.  Nothing durable happens. -/
  | stage (device : WalState TxId CellId Nullifier Event)
      (intent : Intent TxId CellId Nullifier Event) :
      WalStep device intent { device with staged := some intent }
  /-- The commit marker reaches the device.  Admissible only for a staged
  record that the recovered snapshot has not already journaled and that passes
  the complete fail-closed preflight against that same snapshot. -/
  | commit (device : WalState TxId CellId Nullifier Event)
      (intent : Intent TxId CellId Nullifier Event)
      (isStaged : device.staged = some intent)
      (unrecorded : Snapshot.lookupRecorded intent.transactionId
        device.recovered.journal = none)
      (preflighted : intent.preflight device.recovered = .ok ()) :
      WalStep device intent
        { checkpoint := device.checkpoint
          committed := device.committed ++ [intent]
          staged := none }
  /-- Power loss.  The volatile slot is gone; the durable region is not. -/
  | crash (device : WalState TxId CellId Nullifier Event)
      (intent : Intent TxId CellId Nullifier Event) :
      WalStep device intent { device with staged := none }
  /-- Background compaction of the oldest durable record. -/
  | checkpointOne (device : WalState TxId CellId Nullifier Event)
      (intent : Intent TxId CellId Nullifier Event)
      (oldest : Intent TxId CellId Nullifier Event)
      (rest : List (Intent TxId CellId Nullifier Event))
      (region : device.committed = oldest :: rest) :
      WalStep device intent
        { checkpoint := Snapshot.install device.checkpoint oldest
          committed := rest
          staged := device.staged }
  /-- The handler declines the request.  The device is untouched. -/
  | decline (device : WalState TxId CellId Nullifier Event)
      (intent : Intent TxId CellId Nullifier Event) :
      WalStep device intent device

/-- The device represents a model snapshot exactly when a cold start would
read that snapshot.  Nothing weaker: the volatile slot is not allowed to hold
meaning the model already believes. -/
def Represents [DecidableEq CellId] [DecidableEq Nullifier]
    (device : WalState TxId CellId Nullifier Event)
    (model : Snapshot TxId CellId Nullifier Event) : Prop :=
  device.recovered = model

/-! ## Every schedule-invariant step lands on the old snapshot -/

variable [DecidableEq TxId] [DecidableEq CellId] [DecidableEq Nullifier]
  [DecidableEq Event]

/-- The crash-before schedule is the model's universal identity: whatever the
journal and preflight say, its observed store is the snapshot it started from.
This is what lets a device step that changed no durable region be simulated
without knowing whether the model would have accepted the intent. -/
theorem crashBefore_storeAfter (model : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    (execute (.crash .beforeAtomicInstall) model intent).storeAfter model =
      model := by
  simp only [execute]
  split
  · split <;> simp [Outcome.storeAfter]
  · split <;> simp [Outcome.storeAfter]

/-! ## The refinement -/

/-- **The premise is satisfiable.**  Every admissible device step is simulated
by an explicit model schedule: staging, crashing, compacting, and declining by
`crash beforeAtomicInstall`, and the commit marker by `complete`.

The compaction case is worth reading carefully rather than skimming: it is
simulated by the crash-before schedule not because compaction is a crash, but
because `crash beforeAtomicInstall` is the model's name for "the observed
durable store did not move".  Compaction rewrites the device's internal
division of labour between checkpoint and log and moves the recovered snapshot
by nothing, which is exactly that. -/
theorem walRefinement :
    ImplementationRefinement TxId CellId Nullifier Event
      (WalState TxId CellId Nullifier Event)
      (fun device intent after => WalStep device intent after)
      Represents where
  simulates := by
    rintro deviceBefore deviceAfter model intent represented step
    rw [Represents] at represented
    cases step with
    | stage =>
        exact ⟨.crash .beforeAtomicInstall, by
          rw [crashBefore_storeAfter]; exact represented⟩
    | commit isStaged unrecorded preflighted =>
        refine ⟨.complete, ?_⟩
        subst represented
        simp [Represents, execute, unrecorded, preflighted, Outcome.storeAfter]
    | crash =>
        exact ⟨.crash .beforeAtomicInstall, by
          rw [crashBefore_storeAfter]; exact represented⟩
    | checkpointOne oldest rest region =>
        refine ⟨.crash .beforeAtomicInstall, ?_⟩
        rw [crashBefore_storeAfter, Represents, ← represented]
        exact WalState.recovered_checkpointOne deviceBefore oldest rest region
    | decline =>
        exact ⟨.crash .beforeAtomicInstall, by
          rw [crashBefore_storeAfter]; exact represented⟩

/-- The conditional atomicity theorem now fires on a constructed handler
rather than on an assumed one. -/
theorem wal_no_partial_commit
    {deviceBefore deviceAfter : WalState TxId CellId Nullifier Event}
    {model : Snapshot TxId CellId Nullifier Event}
    {intent : Intent TxId CellId Nullifier Event}
    (represented : Represents deviceBefore model)
    (stepped : WalStep deviceBefore intent deviceAfter) :
    exists modelAfter,
      Represents deviceAfter modelAfter /\
        (modelAfter = model \/ modelAfter = Snapshot.install model intent) :=
  physical_step_no_partial_commit walRefinement represented stepped

/-! ## Teeth -- the guards are the step, not decoration

The refinement above would be equally provable for a handler that never wrote
anything.  These say the constructed one is not that handler, and that its
guards cannot be dropped. -/

/-- Installation always changes the model: the journal grows by one record.
Used below so the counterexample needs no side condition. -/
theorem install_ne (model : Snapshot TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    Snapshot.install model intent ≠ model := by
  intro collapsed
  have lengths := congrArg (fun snapshot => snapshot.journal.length) collapsed
  simp [Snapshot.install] at lengths

/-- **The idempotency guard is load-bearing.**  Append a record whose
transaction the recovered snapshot has already journaled, and the durable state
that results is represented by NO schedule of the model: every schedule replays,
so every observed store is the old snapshot, while the device has installed
again.  This is precisely the double-charge a retried request would cause. -/
theorem unguarded_append_breaks_refinement
    (device : WalState TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (alreadyRecorded : Snapshot.lookupRecorded intent.transactionId
      device.recovered.journal = some intent)
    (schedule : Schedule) :
    ¬Represents { device with committed := device.committed ++ [intent] }
        ((execute schedule device.recovered intent).storeAfter
          device.recovered) := by
  intro represented
  rw [Represents, WalState.recovered_append] at represented
  rw [show (execute schedule device.recovered intent).storeAfter
      device.recovered = device.recovered by
    simp [execute, alreadyRecorded, Outcome.storeAfter]] at represented
  exact install_ne device.recovered intent represented

/-- **The device really writes.**  Whenever the model would accept an intent,
the two-step sequence stage-then-commit exists and moves recovery by exactly
one install -- so `walRefinement` is not being carried by a no-op handler. -/
def stageThenCommit (device : WalState TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event)
    (unrecorded : Snapshot.lookupRecorded intent.transactionId
      device.recovered.journal = none)
    (preflighted : intent.preflight device.recovered = .ok ()) :
    WalStep { device with staged := some intent } intent
      { checkpoint := device.checkpoint
        committed := device.committed ++ [intent]
        staged := none } :=
  .commit { device with staged := some intent } intent rfl
    (by simpa using unrecorded) (by simpa using preflighted)

/-- And its effect is the exact atomic installation. -/
theorem stageThenCommit_recovered
    (device : WalState TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    WalState.recovered
        { checkpoint := device.checkpoint
          committed := device.committed ++ [intent]
          staged := none } =
      Snapshot.install device.recovered intent :=
  WalState.recovered_append device intent none

/-- **A crash between staging and the commit marker loses the record.**  The
durable region is unchanged, so recovery returns the old snapshot and the
installation did not happen -- the model's `crash beforeAtomicInstall`, made
physical. -/
theorem crash_before_marker_loses_record
    (device : WalState TxId CellId Nullifier Event)
    (intent : Intent TxId CellId Nullifier Event) :
    WalState.recovered
        { device with staged := (none : Option (Intent TxId CellId Nullifier Event)) } =
        device.recovered ∧
      WalState.recovered
        { device with staged := (none : Option (Intent TxId CellId Nullifier Event)) } ≠
        Snapshot.install device.recovered intent :=
  ⟨rfl, fun collapsed => install_ne device.recovered intent collapsed.symm⟩

/-! ## Premise inhabitation at a closed instance

The generic witnesses above still quantify over the model's type parameters.
This one is closed: concrete identifiers, a concrete snapshot, and a concrete
intent whose preflight succeeds, so `stageThenCommit` is constructible with
every premise discharged by computation. -/

namespace ClosedInstance

/-- A blank device: all cells at digest `0`, nothing consumed, ten units in
every lane, empty history and journal. -/
def device : WalState Nat Nat Nat Nat where
  checkpoint :=
    { roots := fun _ => ⟨0⟩
      consumed := fun _ => false
      available := fun _ => 10
      history := []
      journal := [] }
  committed := []
  staged := none

/-- One transaction: cell `0` moves from digest `0` to digest `1`, nullifier
`7` is consumed, one unit is charged in every lane. -/
def intent : Intent Nat Nat Nat Nat where
  transactionId := 0
  rootWrites := [{ cellId := 0, expectedPre := ⟨0⟩, exactPost := ⟨1⟩ }]
  nullifiers := [7]
  exactCharge := fun _ => 1
  event := 42

theorem recovered_device : device.recovered = device.checkpoint := rfl

/-- Computed: the transaction is unrecorded in the recovered snapshot. -/
theorem unrecorded :
    Snapshot.lookupRecorded intent.transactionId device.recovered.journal =
      none := rfl

/-- Computed: the complete fail-closed preflight succeeds. -/
theorem preflighted : intent.preflight device.recovered = .ok () := by
  decide

/-- **Inhabited**: the commit step exists at a closed instance with every
premise discharged, so `WalStep.commit` is not an empty constructor. -/
def committedStep :
    WalStep { device with staged := some intent } intent
      { checkpoint := device.checkpoint
        committed := device.committed ++ [intent]
        staged := none } :=
  stageThenCommit device intent unrecorded preflighted

/-- The device after the commit marker. -/
def afterCommit : WalState Nat Nat Nat Nat where
  checkpoint := device.checkpoint
  committed := device.committed ++ [intent]
  staged := none

/-- **The retry is idempotent at closed data.**  Re-submitting the same
transaction against the recovered snapshot replays under the ordinary complete
schedule -- computed, not argued. -/
theorem retry_replays :
    execute .complete afterCommit.recovered intent =
      Outcome.replayed intent := by
  rw [show afterCommit.recovered = Snapshot.install device.recovered intent from
    WalState.recovered_append device intent none]
  exact execute_retry_after_install .complete device.recovered intent

/-- Background compaction folds the one durable record into the checkpoint. -/
def afterCheckpoint : WalState Nat Nat Nat Nat where
  checkpoint := Snapshot.install afterCommit.checkpoint intent
  committed := []
  staged := afterCommit.staged

/-- **Compaction is invisible at closed data too.**  The log is now empty and
the checkpoint has absorbed the record, and a cold start reads exactly the same
snapshot. -/
theorem checkpoint_preserves_recovery :
    afterCheckpoint.recovered = afterCommit.recovered :=
  WalState.recovered_checkpointOne afterCommit intent [] rfl

/-- And the retry stays idempotent after compaction: the journal survived the
fold, so a replayed request is still recognized. -/
theorem retry_replays_after_checkpoint :
    execute .complete afterCheckpoint.recovered intent =
      Outcome.replayed intent := by
  rw [checkpoint_preserves_recovery]
  exact retry_replays

/-- And the resulting device recovers to a snapshot that differs from where it
started -- the record is really durable. -/
theorem committedStep_changes :
    WalState.recovered
        { checkpoint := device.checkpoint
          committed := device.committed ++ [intent]
          staged := none } ≠
      device.recovered := by
  rw [stageThenCommit_recovered]
  exact install_ne device.recovered intent

end ClosedInstance

#print axioms WalState.recovered_append
#print axioms WalState.recovered_checkpointOne
#print axioms crashBefore_storeAfter
#print axioms walRefinement
#print axioms wal_no_partial_commit
#print axioms install_ne
#print axioms unguarded_append_breaks_refinement
#print axioms crash_before_marker_loses_record
#print axioms ClosedInstance.preflighted
#print axioms ClosedInstance.retry_replays
#print axioms ClosedInstance.checkpoint_preserves_recovery
#print axioms ClosedInstance.retry_replays_after_checkpoint
#print axioms ClosedInstance.committedStep_changes

end Minidregg.Kernel.DurableWalHandler
