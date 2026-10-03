/- Actual matching compares source label names, not numeric ROM positions.
Hit and miss use the real lookup helpers and emitted source-step update. -/
import Theory.BendClosureProjectionSteps
import Theory.BendClosureCallLookup

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem labelOf_view (library : Library) (pointer : Nat) :
    labelOfFn library pointer = (do
      match ← row pointer with
      | .closure pc _ =>
        match ← code library pc with
        | .lab label =>
          match library.program.names[label]? with
          | some name => pure name
          | none => throw Failure.labelPointer
        | _ => throw Failure.labelRequired
      | _ => throw Failure.labelRequired) := rfl

theorem step_match_hit (limits : Limits) (library : Library) (state : State)
    (function argument pc environment label yes no argumentPC argumentEnvironment actualLabel : Nat)
    (q : Quan) (name : String)
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.mat label yes no))
    (argumentRow : state.heap.get? argument = some (.closure argumentPC argumentEnvironment))
    (argumentCode : library.program.code[argumentPC]? = some (.lab actualLabel))
    (wanted : library.program.names[label]? = some name)
    (actual : library.program.names[actualLabel]? = some name)
    (live : q.live = true) :
    step limits library state =
      {state with control := .evaluate yes environment, sourceSteps := state.sourceSteps + 1} := by
  simp [step, control, BendClosureMachine.apply, row, functionRow, code, instruction,
    live, labelOf_eq, labelOf_view, argumentRow, argumentCode, actual,
    labelName_eq, label_name_ok library label name wanted, sourceStep, go]
  rfl

theorem step_match_miss (limits : Limits) (library : Library) (state : State)
    (function argument pc environment label yes no argumentPC argumentEnvironment actualLabel : Nat)
    (q : Quan) (wantedName actualName : String)
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.mat label yes no))
    (argumentRow : state.heap.get? argument = some (.closure argumentPC argumentEnvironment))
    (argumentCode : library.program.code[argumentPC]? = some (.lab actualLabel))
    (wanted : library.program.names[label]? = some wantedName)
    (actual : library.program.names[actualLabel]? = some actualName)
    (different : actualName ≠ wantedName)
    (live : q.live = true) (room : state.stack.length < limits.frames) :
    step limits library state =
      {state with
        stack := .knownArgument q argument :: state.stack, control := .evaluate no environment,
        sourceSteps := state.sourceSteps + 1} := by
  simp [step, control, BendClosureMachine.apply, row, functionRow, code, instruction,
    live, labelOf_eq, labelOf_view, argumentRow, argumentCode, actual,
    labelName_eq, label_name_ok library label wantedName wanted, different,
    sourceStep, push, Nat.not_le_of_lt room, go]
  rfl

theorem match_hit_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument pc environment label yes no argumentPC argumentEnvironment actualLabel : Nat)
    (q : Quan) (name : String) (h m : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.mat label yes no))
    (argumentRow : state.heap.get? argument = some (.closure argumentPC argumentEnvironment))
    (argumentCode : library.program.code[argumentPC]? = some (.lab actualLabel))
    (wanted : library.program.names[label]? = some name)
    (actual : library.program.names[actualLabel]? = some name)
    (yesExact : CodeDenotes library.program yes h) (noExact : CodeDenotes library.program no m)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (argumentExact : Denotes library.program state.heap argument (.Lab name))
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (live : q.live = true) :
    let beforeSource := plug contexts (.App q (Term.sub (Env.sub values) (.Mat name h m)) (.Lab name))
    let afterSource := plug contexts (Term.sub (Env.sub values) h)
    StateDenotes book library.program state beforeSource ∧
      StateDenotes book library.program (step limits library state) afterSource ∧
      Eval book beforeSource afterSource ∧
      (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  dsimp only
  refine ⟨?_, ?_, plug_eval contexts (.hit live), ?_⟩
  · apply StateDenotes.exact (contexts := contexts)
    · rw [control]
      exact .apply (.closure functionRow (.mat instruction wanted yesExact noExact) captured)
        argumentExact .mat (fun _ => .lab)
    · exact stack
    · intro pointer impossible; rw [control] at impossible; cases impossible
  · rw [step_match_hit limits library state function argument pc environment label yes no argumentPC
      argumentEnvironment actualLabel q name control functionRow instruction argumentRow argumentCode wanted actual live]
    exact evaluate_state (contexts := contexts) rfl (.exact yesExact captured) stack
  · rw [step_match_hit limits library state function argument pc environment label yes no argumentPC
      argumentEnvironment actualLabel q name control functionRow instruction argumentRow argumentCode wanted actual live]

theorem match_miss_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument pc environment label yes no argumentPC argumentEnvironment actualLabel : Nat)
    (q : Quan) (wantedName actualName : String) (h m : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.mat label yes no))
    (argumentRow : state.heap.get? argument = some (.closure argumentPC argumentEnvironment))
    (argumentCode : library.program.code[argumentPC]? = some (.lab actualLabel))
    (wanted : library.program.names[label]? = some wantedName)
    (actual : library.program.names[actualLabel]? = some actualName)
    (different : actualName ≠ wantedName)
    (yesExact : CodeDenotes library.program yes h) (noExact : CodeDenotes library.program no m)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (argumentExact : Denotes library.program state.heap argument (.Lab actualName))
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (live : q.live = true) (room : state.stack.length < limits.frames) :
    let beforeSource := plug contexts (.App q (Term.sub (Env.sub values) (.Mat wantedName h m)) (.Lab actualName))
    let afterSource := plug contexts (.App q (Term.sub (Env.sub values) m) (.Lab actualName))
    StateDenotes book library.program state beforeSource ∧
      StateDenotes book library.program (step limits library state) afterSource ∧
      Eval book beforeSource afterSource ∧
      (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  dsimp only
  refine ⟨?_, ?_, plug_eval contexts (.miss live different), ?_⟩
  · apply StateDenotes.exact (contexts := contexts)
    · rw [control]
      exact .apply (.closure functionRow (.mat instruction wanted yesExact noExact) captured)
        argumentExact .mat (fun _ => .lab)
    · exact stack
    · intro pointer impossible; rw [control] at impossible; cases impossible
  · rw [step_match_miss limits library state function argument pc environment label yes no argumentPC
      argumentEnvironment actualLabel q wantedName actualName control functionRow instruction argumentRow
      argumentCode wanted actual different live room]
    exact evaluate_state (contexts := .function q (.Lab actualName) :: contexts) rfl
      (.exact noExact captured) (.cons (.knownArgument argumentExact) stack)
  · rw [step_match_miss limits library state function argument pc environment label yes no argumentPC
      argumentEnvironment actualLabel q wantedName actualName control functionRow instruction argumentRow
      argumentCode wanted actual different live room]

#assert_axioms labelOf_view
#assert_axioms step_match_hit
#assert_axioms step_match_miss
#assert_axioms match_hit_source
#assert_axioms match_miss_source
end Minidregg.Theory.BendClosureSimulation
