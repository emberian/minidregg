/- Source typing at the concrete response-injection boundary.
An authorized external response begins a fresh pure segment. It is not an Eval
edge from the prior yielded Plan/continuation pair. The Activity layer must bind
the ABI and continuation typing to the exact pending request it consumes. -/
import Theory.BendClosureResponse
import Theory.BendClosureSimulation

namespace Minidregg.Theory.BendClosureResponse
open BendTT BendClosureArena BendClosureMachine BendClosureSimulation
set_option autoImplicit false

/-- This consumes the actual successful resume result, exact retained source
continuation, and its source response type. A schema hash does not supply the
typing premise. The finite enum ABI here is explicitly [false,true]. -/
theorem resume_source_typed {book : Book} (limits : Limits) (program : Program)
    (abi : ABI) (before : State) (bit : Bool) (resumed : Resumed program before abi bit)
    (_ran : resume limits program abi before bit = .ok resumed)
    (continuation resultType : Term)
    (exact : Denotes program before.heap abi.continuation continuation)
    (value : Value book continuation)
    (typed : Typed book [] continuation (.All .Q1 responseType resultType)) :
    StateDenotes book program resumed.state (.App .Q1 continuation (responseTerm bit)) ∧
      Typed book [] (.App .Q1 continuation (responseTerm bit))
        (Term.inst resultType (responseTerm bit)) := by
  constructor
  · apply StateDenotes.exact (contexts := [])
    · rw [resumed.controlExact]
      exact .apply (continuation_retained resumed exact) resumed.inputExact
        value (fun _ => response_value book bit)
    · rw [resumed.emptyStack]
      exact .nil
    · intro pointer impossible
      rw [resumed.controlExact] at impossible
      cases impossible
  · exact .app typed (response_typed book bit)

/-- The new segment starts with a genuine zero-step reflexive source trace.
Prior source/physical counts belong to the retained Activity history; this
theorem never resets a paused segment or fabricates a response Eval rule. -/
theorem resume_new_segment {program : Program} {before : State} {abi : ABI}
    {bit : Bool} (book : Book) (resumed : Resumed program before abi bit)
    (continuation : Term) :
    BendLiveMachine.Trace book resumed.state.sourceSteps
      (.App .Q1 continuation (responseTerm bit))
      (.App .Q1 continuation (responseTerm bit)) := by
  rw [resumed.newSegment]
  exact .refl _

/-- The actual checked Book supplies both WellTyped and Live, and the response
has the continuation's exact source input type. This is source progress only:
it does not imply an adequate controller heap/tick bound or source termination
without the separate resumed-term closed/live obligations. -/
theorem resume_source_progress {book : Book} (limits : Limits) (program : Program)
    (abi : ABI) (before : State) (bit : Bool) (resumed : Resumed program before abi bit)
    (ran : resume limits program abi before bit = .ok resumed)
    (continuation resultType : Term)
    (exact : Denotes program before.heap abi.continuation continuation)
    (value : Value book continuation)
    (typed : Typed book [] continuation (.All .Q1 responseType resultType))
    (checked : Book.check book = .ok ()) :
    Value book (.App .Q1 continuation (responseTerm bit)) ∨
      ∃ next, Eval book (.App .Q1 continuation (responseTerm bit)) next := by
  obtain ⟨wellTyped, live⟩ := BendTT.book_check book checked
  exact BendTT.progress book _ _ wellTyped live
    (resume_source_typed limits program abi before bit resumed ran continuation resultType
      exact value typed).2

#assert_axioms resume_source_typed
#assert_axioms resume_new_segment
#assert_axioms resume_source_progress
end Minidregg.Theory.BendClosureResponse

