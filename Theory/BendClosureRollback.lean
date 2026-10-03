/- Uniform rollback of the actual StateT/Except controller. selectedWork is
only a transparent view of Machine.step's existing dispatch; rfl ties that view
to the implementation. No alternative evaluator or assumed poststate is used.
Physical preprocessing/correlation ownership is external and is NOT rolled back. -/
import Theory.BendClosureRefusalPrefix

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

def selectedWork (limits : Limits) (library : Library) (state : State) : Work Unit :=
  match state.control with
  | .evaluate pc environment => evaluate limits library pc environment
  | .lookup index environment resume => lookup limits index environment resume
  | .returned pointer => returnValue limits library pointer
  | .apply q function argument => BendClosureMachine.apply limits library q function argument
  | .unspine pointer original args => unspine limits library pointer original args
  | .walk pc environment original args => startWalk limits library pc environment original args
  | .classify pc environment original cursor args => classify limits library pc environment original cursor args
  | .reverseArguments pc environment remaining reversed => reverseArguments pc environment remaining reversed
  | .installArguments pc environment remaining => installArguments limits pc environment remaining
  | .complete _ | .refused _ => pure ()

theorem step_selectedWork (limits : Limits) (library : Library) (state : State) :
    step limits library state = match (selectedWork limits library state).run state with
      | .ok (_,next) => next
      | .error reason => {state with control := .refused reason} := rfl

/-- Any literal selected handler error restores every old state component,
including source count, captures, intermediate allocations and stack. -/
theorem selected_work_rollback (limits : Limits) (library : Library) (state : State) (reason : Failure)
    (failed : (selectedWork limits library state).run state = .error reason) :
    step limits library state = {state with control := .refused reason} := by
  rw [step_selectedWork,failed]

theorem selected_work_payload (limits : Limits) (library : Library) (state : State) (reason : Failure)
    (failed : (selectedWork limits library state).run state = .error reason) :
    (step limits library state).heap = state.heap ∧
    (step limits library state).data = state.data ∧
    (step limits library state).stack = state.stack ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  rw [selected_work_rollback limits library state reason failed]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem selected_work_refusal_prefix {book : Book} (limits : Limits) (library : Library)
    (state : State) (origin : Term) (initialCount : Nat) (reason : Failure)
    (initial : SourceInvariant book library.program origin initialCount state)
    (failed : (selectedWork limits library state).run state = .error reason) :
    RefusalInvariant book library.program origin initialCount (step limits library state) :=
  ⟨reason,state,selected_work_rollback limits library state reason failed,initial⟩

theorem selected_work_refusal_padding (limits : Limits) (library : Library)
    (state : State) (reason : Failure) (padding : Nat)
    (failed : (selectedWork limits library state).run state = .error reason) :
    run limits library (padding + 1) state = {state with control := .refused reason} := by
  rw [run,selected_work_rollback limits library state reason failed]
  exact refusal_padding limits library _ reason rfl padding

/-- All selected-handler failures, including failures after tentative writes,
retain the verified source prefix. Coverage is still required for earlier ticks;
this theorem neither invents it nor treats rejection as successful evaluation. -/
theorem covered_run_any_refusal {book : Book} (limits : Limits) (library : Library)
    (ticks : Nat) (state : State) (origin : Term) (initialCount : Nat) (reason : Failure)
    (initial : SourceInvariant book library.program origin initialCount state)
    (coverage : Covered book limits library ticks state)
    (failed : (selectedWork limits library (run limits library ticks state)).run
      (run limits library ticks state) = .error reason) :
    RefusalInvariant book library.program origin initialCount (run limits library (ticks + 1) state) := by
  rw [run_add limits library ticks 1 state]
  exact selected_work_refusal_prefix limits library _ origin initialCount reason
    (initial.run ticks coverage) failed

#assert_axioms step_selectedWork
#assert_axioms selected_work_rollback
#assert_axioms selected_work_payload
#assert_axioms selected_work_refusal_prefix
#assert_axioms selected_work_refusal_padding
#assert_axioms covered_run_any_refusal
end Minidregg.Theory.BendClosureSimulation
