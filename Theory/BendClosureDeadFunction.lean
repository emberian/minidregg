/- Returning a function to a Q0 application captures, but does not evaluate,
its argument. This completes the successful return-frame branch family. -/
import Theory.BendClosureDeadSteps
import Theory.BendClosureReturnSteps

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem step_return_function_dead (limits : Limits) (library : Library) (state : State)
    (function argument environment pointer : Nat) (instruction : Code) (heap : Heap)
    (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned function)
    (stack : state.stack = .function .Q0 argument environment :: rest)
    (found : library.program.code[argument]? = some instruction)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure argument environment) = .ok (pointer,heap)) :
    step limits library state =
      {allocationState state heap pointer (directData instruction) with
        stack := rest, control := .apply .Q0 function pointer} := by
  cases instruction <;> simp [step, control, returnValue, stack, Quan.live, closure,
    BendClosureMachine.allocate, code, found, allocated, directData, allocationState, go] <;> rfl

theorem return_function_dead_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument environment pointer : Nat) (instruction : Code) (heap : Heap)
    (rest : List BendClosureMachine.Frame) (f x : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .returned function)
    (stackShape : state.stack = .function .Q0 argument environment :: rest)
    (found : library.program.code[argument]? = some instruction)
    (argumentExact : CodeDenotes library.program argument x)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (functionExact : Denotes library.program state.heap function f) (functionValue : Value book f)
    (stack : StackDenotes book library.program state.heap rest contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure argument environment) = .ok (pointer,heap)) :
    let source := plug contexts (.App .Q0 f (Term.sub (Env.sub values) x))
    StateDenotes book library.program state source ∧
      StateDenotes book library.program (step limits library state) source ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  have extension := allocate_extends allocated
  refine ⟨?_, ?_, ?_⟩
  · exact returned_state (contexts := .function .Q0 (Term.sub (Env.sub values) x) :: contexts)
      control functionExact functionValue
      (by rw [stackShape]; exact .cons (.function (.exact argumentExact captured)) stack)
  · rw [step_return_function_dead limits library state function argument environment pointer instruction heap
      rest control stackShape found allocated]
    exact StateDenotes.exact
      (.apply (functionExact.extends extension) (allocate_term (.closure argumentExact captured) allocated)
        functionValue (by intro impossible; cases impossible)) (stack.extends extension)
      (by intro next impossible; cases impossible)
  · rw [step_return_function_dead limits library state function argument environment pointer instruction heap
      rest control stackShape found allocated]
    rfl

#assert_axioms step_return_function_dead
#assert_axioms return_function_dead_source
end Minidregg.Theory.BendClosureSimulation
