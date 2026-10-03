/- Reification of the controller's direct source-value branch. -/
import Theory.BendClosureControlSteps
import Theory.BendClosureCache

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

def directValue : Code → Bool
  | .typ .. | .all .. | .lam .. | .sig .. | .prj .. | .enu ..
  | .lab .. | .mat .. | .efq | .eql .. | .rfl => true
  | _ => false

def directData : Code → Bool
  | .lab .. | .rfl => true
  | _ => false

theorem direct_value_source {book : Book} {program : Program} {pc : Nat}
    {source : Term} {instruction : Code}
    (exact : CodeDenotes program pc source)
    (found : program.code[pc]? = some instruction)
    (direct : directValue instruction = true) (substitution : Subst) :
    Value book (Term.sub substitution source) := by
  cases exact <;> simp_all [directValue, Term.sub]
  all_goals constructor

theorem step_direct_value (limits : Limits) (library : Library) (state : State)
    (pc environment pointer : Nat) (instruction : Code) (heap : Heap)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some instruction)
    (direct : directValue instruction = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure pc environment) = .ok (pointer, heap)) :
    step limits library state =
      {allocationState state heap pointer (directData instruction) with control := .returned pointer} := by
  cases instruction <;> simp_all [directValue, directData, step, evaluate,
    BendClosureMachine.allocate, closure, code, go, allocationState]
  all_goals rfl

theorem direct_value_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment pointer : Nat) (instruction : Code) (heap : Heap)
    (source : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some instruction)
    (direct : directValue instruction = true)
    (sourceExact : CodeDenotes library.program pc source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure pc environment) = .ok (pointer, heap)) :
    let residual := plug contexts (Term.sub (Env.sub values) source)
    StateDenotes book library.program state residual ∧
      StateDenotes book library.program (step limits library state) residual ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact evaluate_state control (.exact sourceExact captured) stack
  · rw [step_direct_value limits library state pc environment pointer instruction heap
      control found direct allocated]
    apply StateDenotes.exact (contexts := contexts)
    · exact .returned (allocate_term (.closure sourceExact captured) allocated)
        (direct_value_source sourceExact found direct _)
    · exact stack.extends (allocate_extends allocated)
    · intro next impossible
      cases impossible
  · rw [step_direct_value limits library state pc environment pointer instruction heap
      control found direct allocated]

#assert_axioms direct_value_source
#assert_axioms step_direct_value
#assert_axioms direct_value_stutter
end Minidregg.Theory.BendClosureSimulation

