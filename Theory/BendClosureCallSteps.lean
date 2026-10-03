/- Actual case-tree classifier edges retain the original source call.
These ticks do not perform Eval.call; that occurs only after a complete Walk
exposes its leaf. Source node classification follows the pinned unspine law. -/
import Theory.BendClosureSimulation

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem step_walk_classify (limits : Limits) (library : Library) (state : State)
    (pc environment original function argument index : Nat) (q : Quan)
    (args : List (Quan × Nat))
    (control : state.control = .walk pc environment original args)
    (found : library.program.code[pc]? = some (.app q function argument))
    (variableCode : library.program.code[argument]? = some (.var index)) :
    step limits library state =
      {state with control := .classify pc environment original function args} := by
  simp [step, control, startWalk, code, found, variableCode, go]
  rfl

theorem step_classify_application (limits : Limits) (library : Library) (state : State)
    (pc environment original cursor function argument : Nat) (q : Quan)
    (args : List (Quan × Nat))
    (control : state.control = .classify pc environment original cursor args)
    (found : library.program.code[cursor]? = some (.app q function argument)) :
    step limits library state =
      {state with control := .classify pc environment original function args} := by
  simp [step, control, classify, code, found, go]
  rfl

theorem application_head (q : Quan) (function argument : Term) :
    (Term.unspine (.App q function argument) []).1 = (Term.unspine function []).1 := by
  change (Term.unspine function [(q, argument)]).1 = _
  rw [BendTT.unspine_app]

theorem walk_classify_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment original function argument index : Nat) (q : Quan)
    (args : List (Quan × Nat)) (f origin : Term) (values : Env) (arguments : List Arg)
    (contexts : List (Context book))
    (control : state.control = .walk pc environment original args)
    (found : library.program.code[pc]? = some (.app q function argument))
    (variableCode : library.program.code[argument]? = some (.var index))
    (functionExact : CodeDenotes library.program function f)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin (.App q f (.Var index)) values arguments)
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
    StateDenotes book library.program state (plug contexts origin) ∧
      StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  have codeExact := CodeDenotes.app found functionExact (CodeDenotes.var variableCode)
  refine ⟨?_, ?_, ?_⟩
  · apply StateDenotes.exact (contexts := contexts)
    · rw [control]
      exact .walk codeExact captured originalExact argsExact walkPrefix
    · exact stack
    · intro pointer impossible
      rw [control] at impossible
      cases impossible
  · rw [step_walk_classify limits library state pc environment original function argument index q args control found variableCode]
    exact StateDenotes.exact (contexts := contexts)
      (.classify codeExact functionExact rfl captured originalExact argsExact walkPrefix) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_walk_classify limits library state pc environment original function argument index q args control found variableCode]

theorem classify_application_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment original cursor function argument : Nat) (q : Quan)
    (args : List (Quan × Nat)) (source f x origin : Term) (values : Env) (arguments : List Arg)
    (contexts : List (Context book))
    (control : state.control = .classify pc environment original cursor args)
    (found : library.program.code[cursor]? = some (.app q function argument))
    (sourceExact : CodeDenotes library.program pc source)
    (functionExact : CodeDenotes library.program function f)
    (argumentExact : CodeDenotes library.program argument x)
    (classification : Term.node source = Term.takes (Term.unspine (.App q f x) []).1)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin source values arguments)
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
    StateDenotes book library.program state (plug contexts origin) ∧
      StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  have cursorExact := CodeDenotes.app found functionExact argumentExact
  refine ⟨?_, ?_, ?_⟩
  · apply StateDenotes.exact (contexts := contexts)
    · rw [control]
      exact .classify sourceExact cursorExact classification captured originalExact argsExact walkPrefix
    · exact stack
    · intro pointer impossible
      rw [control] at impossible
      cases impossible
  · rw [step_classify_application limits library state pc environment original cursor function argument q args control found]
    have classified : Term.node source = Term.takes (Term.unspine f []).1 := by
      simpa only [application_head] using classification
    exact StateDenotes.exact (contexts := contexts)
      (.classify sourceExact functionExact classified captured originalExact argsExact walkPrefix) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_classify_application limits library state pc environment original cursor function argument q args control found]

#assert_axioms step_walk_classify
#assert_axioms step_classify_application
#assert_axioms application_head
#assert_axioms walk_classify_stutter
#assert_axioms classify_application_stutter
end Minidregg.Theory.BendClosureSimulation
