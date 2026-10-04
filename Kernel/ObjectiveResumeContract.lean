/- The kernel stores only well-typed checkpoints (ObjectiveProofs).

`Kernel.ObjectiveActivity` stores an activity's exact yielded machine state as
checkpoint bytes and resumes it with an outcome the actual checker typed at the
program's declared response type. This module proves, from the existing
preservation theorems (`typed_stepRaw_preserved`, `typed_resume_preserved`,
`checked_initial_state`) and the codec round trip (`state_roundTrip`):

* `birth_checkpoint_typed`: the checkpoint a birth stores decodes to exactly
  the state its first segment yielded, and that state is typed at the
  instantiated program's own checked type;
* `delivery_checkpoint_typed`: if the checkpoint a delivery decoded was typed
  (what the two theorems establish for every checkpoint the kernel wrote), the
  checkpoint it stores decodes to exactly its new yielded state, again typed.

So the before-root check of a kernel checkpoint is codec validity and the digest
binding (Scribe note B3): no executable machine-state checker is needed for
states the kernel produced, and no foreign checkpoint is ever admitted (a
delivery decodes only the record cell's own bytes). -/
import Kernel.ObjectiveActivity
import Theory.ObjectiveBendDemandPreservation
import Theory.ObjectiveBendCheckpointRoundTrip

namespace Minidregg.Kernel.ObjectiveResumeContract
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Theory.ObjectiveBendTypes (Ty)
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandTyping
open Minidregg.Theory.ObjectiveBendDemandPreservation
set_option autoImplicit false

/-- The checkpoint bytes decode to exactly the state they encode. -/
theorem decodeCheckpoint_checkpointBytes (state : State) :
    decodeCheckpoint (checkpointBytes state) = some state := by
  unfold decodeCheckpoint
  rw [checkpointBytes_tokens]
  exact ObjectiveBendCheckpointRoundTrip.state_roundTrip state

/-- Typing survives the bounded executor up to a yield. -/
theorem typed_runBounded_yielded {assumptions : Assumptions} {types : AddressTypes}
    {state : State} {result : Ty} (typed : StateTyping assumptions types state result)
    (limits : Limits) (ticks : Nat) {plan : Address} {retained : State}
    (ran : runBounded limits ticks state = .yielded plan retained) :
    ∃ after, Nonempty (StateTyping assumptions after retained result) := by
  induction ticks generalizing types state with
  | zero =>
      cases control : state.control <;> simp only [runBounded, control] at ran <;> try cases ran
      exact ⟨types, ⟨typed⟩⟩
  | succ ticks ih =>
      cases control : state.control <;> simp only [runBounded, step, control] at ran <;> try cases ran
      all_goals first
        | exact ⟨types, ⟨typed⟩⟩
        | (by_cases fits : (stepRaw state).heap.size ≤ limits.heap ∧ (stepRaw state).stack.length ≤ limits.stack
           · obtain ⟨_, _, ⟨next⟩⟩ := typed_stepRaw_preserved typed
             exact ih next (by simpa [fits] using ran)
           · simp [fits] at ran)

/-- A segment that yielded came from the bounded executor's yield. -/
theorem runSegment_yielded {config : Config} {ticks : Nat} {start state : State} {plan : PlanAwait}
    (ran : runSegment config ticks start = .ok (.yielded state plan)) :
    ∃ address, runBounded config.limits ticks start = .yielded address state := by
  unfold runSegment at ran
  split at ran
  · rename_i address yielded equation
    split at ran
    · simp only [bind, Except.bind] at ran
      split at ran
      · cases ran
      · cases ran; exact ⟨address, equation⟩
    · cases ran
  · split at ran <;> cases ran
  · cases ran
  · cases ran
  · cases ran

/-- A yielded segment's commit always exists when it was admitted. -/
theorem segmentCommit_yielded {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {transaction : TransactionId} {cell object : CellId}
    {generation : Nat} {state : State} {plan : PlanAwait} {committed : Option YieldCommit}
    (ok : segmentCommit config snapshot height transaction cell object generation (.yielded state plan) =
      .ok committed) :
    ∃ yielded, committed = some yielded := by
  simp only [segmentCommit, bind, Except.bind] at ok
  split at ok
  · cases ok
  · cases ok; exact ⟨_, rfl⟩

/-- The record that ends a yielded segment stores exactly its yielded state. -/
theorem nextRecord_checkpoint (base : Record) (escrow : Escrow) (generation : Nat) (state : State)
    (plan : PlanAwait) (yielded : YieldCommit) :
    (nextRecord base escrow generation (.yielded state plan) (some yielded)).checkpoint =
      checkpointBytes state := rfl

/-- **A birth stores a well-typed checkpoint.** -/
theorem birth_checkpoint_typed {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : BirthRequest} (birth : Birth config snapshot height request)
    {state : State} {plan : PlanAwait} (yieldedSegment : birth.segment = .yielded state plan) :
    decodeCheckpoint birth.record.checkpoint = some state ∧
      ∃ types, Nonempty (StateTyping birth.program.assumptions types state birth.program.checked.type) := by
  have commit := birth.yieldedExact
  rw [yieldedSegment] at commit
  obtain ⟨yielded, someYielded⟩ := segmentCommit_yielded commit
  refine ⟨?_, ?_⟩
  · rw [birth.recordExact, yieldedSegment, someYielded, nextRecord_checkpoint]
    exact decodeCheckpoint_checkpointBytes state
  · have ran := birth.segmentExact
    rw [yieldedSegment] at ran
    obtain ⟨_, executed⟩ := runSegment_yielded ran
    exact typed_runBounded_yielded
      (checked_initial_state birth.program.applied birth.program.checked) config.limits request.ticks executed

/-- **A delivery stores a well-typed checkpoint.** If the checkpoint it decoded
from the record cell was typed at the program's checked type (as every
checkpoint a birth or a delivery stores is), the response it resumed with is
typed by the actual checker at the program's response type, so the resumed
state is typed (`typed_resume_preserved`), the segment keeps it typed, and the
record it stores decodes to exactly that state. -/
theorem delivery_checkpoint_typed {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : DeliverRequest}
    (delivery : Delivery config snapshot height request)
    (prior : ∃ types, Nonempty (StateTyping delivery.program.assumptions types delivery.state
      delivery.program.checked.type))
    {state : State} {plan : PlanAwait} (yieldedSegment : delivery.segment = .yielded state plan) :
    decodeCheckpoint delivery.next.checkpoint = some state ∧
      ∃ types, Nonempty (StateTyping delivery.program.assumptions types state delivery.program.checked.type) := by
  have commit := delivery.yieldedExact
  rw [yieldedSegment] at commit
  obtain ⟨yielded, someYielded⟩ := segmentCommit_yielded commit
  refine ⟨?_, ?_⟩
  · rw [delivery.nextExact, yieldedSegment, someYielded, nextRecord_checkpoint]
    exact decodeCheckpoint_checkpointBytes state
  · obtain ⟨types, ⟨typed⟩⟩ := prior
    have computation := delivery.program.typeExact
    rw [computation] at typed
    obtain ⟨address, waiting⟩ := resume_requires_yield _ _ (by rw [delivery.resumeExact]; rfl)
    have resumedTyped := typed_resume_preserved typed waiting delivery.response.typed delivery.resumeExact
    obtain ⟨resumedState⟩ := resumedTyped
    have ran := delivery.segmentExact
    rw [yieldedSegment] at ran
    obtain ⟨_, executed⟩ := runSegment_yielded ran
    rw [computation]
    exact typed_runBounded_yielded resumedState config.limits delivery.envelope executed

#assert_axioms decodeCheckpoint_checkpointBytes
#assert_axioms typed_runBounded_yielded
#assert_axioms runSegment_yielded
#assert_axioms segmentCommit_yielded
#assert_axioms birth_checkpoint_typed
#assert_axioms delivery_checkpoint_typed
end Minidregg.Kernel.ObjectiveResumeContract
