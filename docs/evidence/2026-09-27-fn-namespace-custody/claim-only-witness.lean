import Kernel.DurableReceiver

/- Narrow, source-level witness for a guarded claim-only durable commit.
It is not a native Host or SQLite acceptance. -/
open Minidregg.Kernel
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableDataIntent.Witness

set_option autoImplicit false

theorem claim_only_seed_ready :
    claimOnlyIntent.preflight (Witness.seed.snapshot lengthRoot) = .ok () := by decide

theorem claim_only_accepted :
    DurableDataIntent.execute .complete (Witness.seed.snapshot lengthRoot) claimOnlyIntent =
      .accepted (DurableDataIntent.DataSnapshot.install
        (Witness.seed.snapshot lengthRoot) claimOnlyIntent) := by
  apply DurableDataIntent.execute_complete_ready
  · rfl
  · exact claim_only_seed_ready

theorem claim_only_append_reopens :
    (Witness.image.append claimOnlyIntent).restore lengthRoot =
      some (DurableDataIntent.DataSnapshot.install
        (Witness.seed.snapshot lengthRoot) claimOnlyIntent) :=
  DurableReceiver.exactAppend lengthRoot Witness.image _ _ claimOnlyIntent
    Witness.seed_represents claim_only_accepted

theorem claim_only_retry_replayed :
    DurableDataIntent.execute .complete
      (DurableDataIntent.DataSnapshot.install
        (Witness.seed.snapshot lengthRoot) claimOnlyIntent) claimOnlyIntent =
      .replayed claimOnlyIntent.erase := by
  simp [DurableDataIntent.execute, DurableDataIntent.DataSnapshot.install,
    DurableCommitProtocol.Snapshot.lookupRecorded,
    DurableCommitProtocol.Intent.sameCheck_self]

theorem claim_only_prepare_ready :
    ∃ ready, DurableReceiver.prepare Witness.image
      (Witness.seed.snapshot lengthRoot) Witness.seed_represents claimOnlyIntent = .inl ready := by
  let ready : DurableReceiver.Ready lengthRoot Witness.image
      (Witness.seed.snapshot lengthRoot) claimOnlyIntent :=
    ⟨DurableDataIntent.DataSnapshot.install (Witness.seed.snapshot lengthRoot) claimOnlyIntent,
      claim_only_accepted, claim_only_append_reopens⟩
  refine ⟨ready, ?_⟩
  unfold DurableReceiver.prepare
  split
  next next executed =>
    have same := claim_only_accepted
    rw [executed] at same
    cases same
    rfl
  next absurd =>
    exact False.elim (absurd _ claim_only_accepted)

/-- info: 'claim_only_accepted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms claim_only_accepted
/-- info: 'claim_only_append_reopens' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms claim_only_append_reopens
/-- info: 'claim_only_retry_replayed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms claim_only_retry_replayed
/-- info: 'claim_only_prepare_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms claim_only_prepare_ready
