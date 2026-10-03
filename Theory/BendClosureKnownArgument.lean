/- Retained arguments are reopened through the actual controller. A captured
closure may be a dead thunk; it is never promoted to Value by residency. -/
import Theory.BendClosureReturnFrames
import Theory.BendClosureReadiness

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem step_known_closure (limits : Limits) (library : Library) (state : State)
    (function argument pc environment : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned function)
    (stack : state.stack = .knownArgument q argument :: rest)
    (live : q.live = true) (room : rest.length < limits.frames)
    (rowFound : state.heap.get? argument = some (.closure pc environment)) :
    step limits library state =
      {state with
        stack := .argument q function :: rest, control := .evaluate pc environment} := by
  simp [step, control, returnValue, stack, live, push, Nat.not_le_of_lt room,
    evaluatePointer, row, rowFound, go]
  rfl

theorem step_known_pair (limits : Limits) (library : Library) (state : State)
    (function argument first second : Nat) (q r : Quan) (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned function)
    (stack : state.stack = .knownArgument q argument :: rest)
    (live : q.live = true) (room : rest.length < limits.frames)
    (rowFound : state.heap.get? argument = some (.pair r first second)) :
    step limits library state =
      {state with
        stack := .argument q function :: rest, control := .returned argument} := by
  simp [step, control, returnValue, stack, live, push, Nat.not_le_of_lt room,
    evaluatePointer, row, rowFound, go]
  rfl

theorem step_known_application (limits : Limits) (library : Library) (state : State)
    (function argument left right : Nat) (q r : Quan) (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned function)
    (stack : state.stack = .knownArgument q argument :: rest)
    (live : q.live = true) (room : rest.length < limits.frames)
    (rowFound : state.heap.get? argument = some (.application r left right)) :
    step limits library state =
      {state with
        stack := .argument q function :: rest, control := .returned argument} := by
  simp [step, control, returnValue, stack, live, push, Nat.not_le_of_lt room,
    evaluatePointer, row, rowFound, go]
  rfl

theorem known_live_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (f x : Term) (contexts : List (Context book))
    (control : state.control = .returned function)
    (stackShape : state.stack = .knownArgument q argument :: rest)
    (live : q.live = true) (room : rest.length < limits.frames)
    (functionExact : Denotes library.program state.heap function f) (functionValue : Value book f)
    (argumentReady : ReadyPointer book library.program state.heap argument x)
    (stack : StackDenotes book library.program state.heap rest contexts) :
    StateDenotes book library.program state (plug contexts (.App q f x)) ∧
      StateDenotes book library.program (step limits library state) (plug contexts (.App q f x)) ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_, ?_⟩
  · exact returned_state (contexts := .function q x :: contexts) control functionExact functionValue
      (by rw [stackShape]; exact .cons (.knownArgument argumentReady.1) stack)
  · have exact := argumentReady.1
    cases exact with
    | closure rowFound code captured =>
      rw [step_known_closure limits library state function argument _ _ q rest
        control stackShape live room rowFound]
      exact ⟨evaluate_state (contexts := .argument q f functionValue live :: contexts) rfl
        (.exact code captured) (.cons (.argument functionExact functionValue live) stack), rfl⟩
    | pair rowFound first second =>
      have value := ready_fast_value argumentReady (by
        intro pc environment impossible; rw [rowFound] at impossible; cases impossible)
      rw [step_known_pair limits library state function argument _ _ q _ rest
        control stackShape live room rowFound]
      exact ⟨returned_state (contexts := .argument q f functionValue live :: contexts) rfl
        (.pair rowFound first second) value (.cons (.argument functionExact functionValue live) stack), rfl⟩
    | application rowFound left right =>
      have value := ready_fast_value argumentReady (by
        intro pc environment impossible; rw [rowFound] at impossible; cases impossible)
      rw [step_known_application limits library state function argument _ _ q _ rest
        control stackShape live room rowFound]
      exact ⟨returned_state (contexts := .argument q f functionValue live :: contexts) rfl
        (.application rowFound left right) value (.cons (.argument functionExact functionValue live) stack), rfl⟩

theorem step_known_dead (limits : Limits) (library : Library) (state : State)
    (function argument : Nat) (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned function)
    (stack : state.stack = .knownArgument .Q0 argument :: rest) :
    step limits library state = {state with stack := rest, control := .apply .Q0 function argument} := by
  simp [step, control, returnValue, stack, Quan.live, go]
  rfl

theorem known_dead_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument : Nat) (rest : List BendClosureMachine.Frame)
    (f x : Term) (contexts : List (Context book))
    (control : state.control = .returned function)
    (stackShape : state.stack = .knownArgument .Q0 argument :: rest)
    (functionExact : Denotes library.program state.heap function f) (functionValue : Value book f)
    (argumentExact : Denotes library.program state.heap argument x)
    (stack : StackDenotes book library.program state.heap rest contexts) :
    StateDenotes book library.program state (plug contexts (.App .Q0 f x)) ∧
      StateDenotes book library.program (step limits library state) (plug contexts (.App .Q0 f x)) ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_, ?_, ?_⟩
  · exact returned_state (contexts := .function .Q0 x :: contexts) control functionExact functionValue
      (by rw [stackShape]; exact .cons (.knownArgument argumentExact) stack)
  · rw [step_known_dead limits library state function argument rest control stackShape]
    exact StateDenotes.exact
      (.apply functionExact argumentExact functionValue (by intro impossible; cases impossible)) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_known_dead limits library state function argument rest control stackShape]

#assert_axioms step_known_closure
#assert_axioms step_known_pair
#assert_axioms step_known_application
#assert_axioms known_live_source
#assert_axioms step_known_dead
#assert_axioms known_dead_source
end Minidregg.Theory.BendClosureSimulation
