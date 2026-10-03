/- Actual projection and rewrite transitions. These consume source values
and concrete old rows; neither an asserted source step nor a successor
interpretation is accepted as a premise. -/
import Theory.BendClosureReturnFrames

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem step_projection (limits : Limits) (library : Library) (state : State)
    (function argument pc environment handler first second : Nat) (q r : Quan)
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.prj handler))
    (argumentRow : state.heap.get? argument = some (.pair r first second))
    (live : q.live = true) (room : state.stack.length + 1 < limits.frames) :
    step limits library state =
      {state with
        stack := .knownArgument (Quan.fld r q) first :: .knownArgument q second :: state.stack,
        control := .evaluate handler environment, sourceSteps := state.sourceSteps + 1} := by
  have firstRoom : state.stack.length < limits.frames := by omega
  simp [step, control, BendClosureMachine.apply, row, functionRow, code, instruction,
    argumentRow, live, push, Nat.not_le_of_lt firstRoom, Nat.not_le_of_lt room, sourceStep, go]
  rfl

theorem projection_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument pc environment handler first second : Nat) (q r : Quan)
    (h a b : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.prj handler))
    (argumentRow : state.heap.get? argument = some (.pair r first second))
    (handlerExact : CodeDenotes library.program handler h)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (firstExact : Denotes library.program state.heap first a)
    (secondExact : Denotes library.program state.heap second b)
    (pairValue : Value book (.Tup r a b))
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (live : q.live = true) (room : state.stack.length + 1 < limits.frames) :
    let beforeSource := plug contexts (.App q (.Prj (Term.sub (Env.sub values) h)) (.Tup r a b))
    let afterSource := plug contexts (.App q (.App (Quan.fld r q) (Term.sub (Env.sub values) h) a) b)
    StateDenotes book library.program state beforeSource ∧
      StateDenotes book library.program (step limits library state) afterSource ∧
      Eval book beforeSource afterSource ∧
      (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply StateDenotes.exact (contexts := contexts)
    · rw [control]
      exact .apply (.closure functionRow (.prj instruction handlerExact) captured)
        (.pair argumentRow firstExact secondExact) .prj (fun _ => pairValue)
    · exact stack
    · intro pointer impossible
      rw [control] at impossible
      cases impossible
  · rw [step_projection limits library state function argument pc environment handler first second q r
      control functionRow instruction argumentRow live room]
    exact evaluate_state
      (contexts := .function (Quan.fld r q) a :: .function q b :: contexts)
      rfl (.exact handlerExact captured)
      (.cons (.knownArgument firstExact) (.cons (.knownArgument secondExact) stack))
  · exact plug_eval contexts (.split live pairValue)
  · rw [step_projection limits library state function argument pc environment handler first second q r
      control functionRow instruction argumentRow live room]

theorem step_return_rewrite (limits : Limits) (library : Library) (state : State)
    (pointer pc evidenceEnvironment body environment : Nat) (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned pointer)
    (stack : state.stack = .rewrite body environment :: rest)
    (evidenceRow : state.heap.get? pointer = some (.closure pc evidenceEnvironment))
    (instruction : library.program.code[pc]? = some .rfl) :
    step limits library state =
      {state with
        stack := rest, control := .evaluate body environment,
        sourceSteps := state.sourceSteps + 1} := by
  simp [step, control, returnValue, stack, row, evidenceRow, code, instruction, sourceStep, go]
  rfl

theorem return_rewrite_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pointer pc evidenceEnvironment body environment : Nat) (rest : List BendClosureMachine.Frame)
    (motive result : Term) (evidenceValues : Env) (contexts : List (Context book))
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .rewrite body environment :: rest)
    (evidenceRow : state.heap.get? pointer = some (.closure pc evidenceEnvironment))
    (instruction : library.program.code[pc]? = some .rfl)
    (evidenceCaptured : EnvironmentDenotes library.program state.heap evidenceEnvironment evidenceValues)
    (bodyExact : ClosureDenotes library.program state.heap body environment result)
    (stack : StackDenotes book library.program state.heap rest contexts) :
    StateDenotes book library.program state (plug contexts (.Rwt .Rfl motive result)) ∧
      StateDenotes book library.program (step limits library state) (plug contexts result) ∧
      Eval book (plug contexts (.Rwt .Rfl motive result)) (plug contexts result) ∧
      (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  refine ⟨?_, ?_, plug_eval contexts .cast, ?_⟩
  · exact returned_state (contexts := .rewrite motive result :: contexts) control
      (.closure evidenceRow (.rfl instruction) evidenceCaptured) .rfl
      (by rw [stackShape]; exact .cons (.rewrite bodyExact) stack)
  · rw [step_return_rewrite limits library state pointer pc evidenceEnvironment body environment rest
      control stackShape evidenceRow instruction]
    exact evaluate_state (contexts := contexts) rfl bodyExact stack
  · rw [step_return_rewrite limits library state pointer pc evidenceEnvironment body environment rest
      control stackShape evidenceRow instruction]

#assert_axioms step_projection
#assert_axioms projection_source
#assert_axioms step_return_rewrite
#assert_axioms return_rewrite_source
end Minidregg.Theory.BendClosureSimulation
