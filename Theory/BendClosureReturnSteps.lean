/- Exact source contexts when a live argument returns to its application. -/
import Theory.BendClosureControlSteps

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem returned_state {book : Book} {program : Program} {state : State}
    {pointer : Nat} {source : Term} {contexts : List (Context book)}
    (control : state.control = .returned pointer)
    (focus : Denotes program state.heap pointer source) (value : Value book source)
    (stack : StackDenotes book program state.heap state.stack contexts) :
    StateDenotes book program state (plug contexts source) :=
  .exact (by rw [control]; exact .returned focus value) stack
    (by intro next impossible; rw [control] at impossible; cases impossible)

theorem step_return_argument (limits : Limits) (library : Library) (state : State)
    (pointer function : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned pointer)
    (stack : state.stack = .argument q function :: rest) :
    step limits library state =
      {state with stack := rest, control := .apply q function pointer} := by
  simp [step, control, returnValue, stack, go]
  rfl

theorem return_argument_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pointer function : Nat) (q : Quan)
    (rest : List BendClosureMachine.Frame) (contexts : List (Context book))
    (argumentSource functionSource : Term)
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .argument q function :: rest)
    (argumentExact : Denotes library.program state.heap pointer argumentSource)
    (argumentValue : Value book argumentSource)
    (functionExact : Denotes library.program state.heap function functionSource)
    (functionValue : Value book functionSource) (live : q.live = true)
    (stack : StackDenotes book library.program state.heap rest contexts) :
    let source := plug contexts (.App q functionSource argumentSource)
    StateDenotes book library.program state source ∧
      StateDenotes book library.program (step limits library state) source ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact returned_state (contexts := .argument q functionSource functionValue live :: contexts)
      control argumentExact argumentValue (by rw [stackShape]; exact .cons (.argument functionExact functionValue live) stack)
  · rw [step_return_argument limits library state pointer function q rest control stackShape]
    apply StateDenotes.exact (contexts := contexts)
    · exact .apply functionExact argumentExact functionValue (fun _ => argumentValue)
    · exact stack
    · intro next impossible
      cases impossible
  · rw [step_return_argument limits library state pointer function q rest control stackShape]

theorem step_return_function_live (limits : Limits) (library : Library) (state : State)
    (pointer argument environment : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned pointer)
    (stack : state.stack = .function q argument environment :: rest)
    (live : q.live = true) (room : rest.length < limits.frames) :
    step limits library state =
      {state with stack := .argument q pointer :: rest, control := .evaluate argument environment} := by
  simp [step, control, returnValue, stack, live, push, Nat.not_le_of_lt room, go]
  rfl

theorem return_function_live_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pointer argument environment : Nat) (q : Quan)
    (rest : List BendClosureMachine.Frame) (contexts : List (Context book))
    (functionSource argumentSource : Term)
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .function q argument environment :: rest)
    (live : q.live = true) (room : rest.length < limits.frames)
    (functionExact : Denotes library.program state.heap pointer functionSource)
    (functionValue : Value book functionSource)
    (argumentExact : ClosureDenotes library.program state.heap argument environment argumentSource)
    (stack : StackDenotes book library.program state.heap rest contexts) :
    let source := plug contexts (.App q functionSource argumentSource)
    StateDenotes book library.program state source ∧
      StateDenotes book library.program (step limits library state) source ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact returned_state (contexts := .function q argumentSource :: contexts)
      control functionExact functionValue (by rw [stackShape]; exact .cons (.function argumentExact) stack)
  · rw [step_return_function_live limits library state pointer argument environment q rest control stackShape live room]
    exact evaluate_state (contexts := .argument q functionSource functionValue live :: contexts)
      rfl argumentExact (.cons (.argument functionExact functionValue live) stack)
  · rw [step_return_function_live limits library state pointer argument environment q rest control stackShape live room]

theorem return_empty_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pointer : Nat) (source : Term)
    (control : state.control = .returned pointer) (empty : state.stack = [])
    (exact : Denotes library.program state.heap pointer source) (value : Value book source) :
    StateDenotes book library.program state source ∧
      StateDenotes book library.program (step limits library state) source ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_, ?_, ?_⟩
  · exact returned_state (contexts := []) control exact value (by rw [empty]; exact .nil)
  · rw [step_return_empty limits library state pointer control empty]
    exact StateDenotes.exact (contexts := []) (.complete exact value)
      (by rw [empty]; exact .nil) (fun _ _ => empty)
  · rw [step_return_empty limits library state pointer control empty]

#assert_axioms return_empty_stutter
#assert_axioms step_return_function_live
#assert_axioms return_function_live_stutter
#assert_axioms returned_state
#assert_axioms step_return_argument
#assert_axioms return_argument_stutter
end Minidregg.Theory.BendClosureSimulation
