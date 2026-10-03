/- Administrative decomposition of the actual Bend closure controller.
These laws operate on Machine.step and its literal stack updates. Source
reification is unchanged; these physical ticks do not charge an Eval step. -/
import Theory.BendClosureSimulation

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem evaluate_state {book : Book} {program : Program} {state : State}
    {pc environment : Nat} {source : Term} {contexts : List (Context book)}
    (control : state.control = .evaluate pc environment)
    (focus : ClosureDenotes program state.heap pc environment source)
    (stack : StackDenotes book program state.heap state.stack contexts) :
    StateDenotes book program state (plug contexts source) :=
  .exact (by rw [control]; exact .evaluate focus) stack
    (by intro pointer impossible; rw [control] at impossible; cases impossible)

theorem step_application (limits : Limits) (library : Library) (state : State)
    (pc environment function argument : Nat) (q : Quan)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.app q function argument))
    (room : state.stack.length < limits.frames) :
    step limits library state =
      {state with stack := .function q argument environment :: state.stack, control := .evaluate function environment} := by
  simp [step, control, evaluate, code, found, push, Nat.not_le_of_lt room, go]
  rfl

theorem step_live_let (limits : Limits) (library : Library) (state : State)
    (pc environment value body : Nat) (q : Quan)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.lett q value body))
    (live : q.live = true) (room : state.stack.length < limits.frames) :
    step limits library state =
      {state with stack := .lett q body environment :: state.stack, control := .evaluate value environment} := by
  simp [step, control, evaluate, code, found, live, push, Nat.not_le_of_lt room, go]
  rfl

theorem step_live_pair (limits : Limits) (library : Library) (state : State)
    (pc environment first second : Nat) (q : Quan)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.tup q first second))
    (live : q.live = true) (room : state.stack.length < limits.frames) :
    step limits library state =
      {state with stack := .first q second environment :: state.stack, control := .evaluate first environment} := by
  simp [step, control, evaluate, code, found, live, push, Nat.not_le_of_lt room, go]
  rfl

theorem step_rewrite (limits : Limits) (library : Library) (state : State)
    (pc environment evidence motive body : Nat)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.rwt evidence motive body))
    (room : state.stack.length < limits.frames) :
    step limits library state =
      {state with stack := .rewrite body environment :: state.stack, control := .evaluate evidence environment} := by
  simp [step, control, evaluate, code, found, push, Nat.not_le_of_lt room, go]
  rfl

/-- Evaluating the function of an application changes only the physical focus
and continuation. The exact source expression and source-step count survive. -/
theorem application_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment function argument : Nat) (q : Quan)
    (f x : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.app q function argument))
    (functionExact : CodeDenotes library.program function f)
    (argumentExact : CodeDenotes library.program argument x)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : state.stack.length < limits.frames) :
    let source := plug contexts (Term.sub (Env.sub values) (.App q f x))
    StateDenotes book library.program state source ∧
      StateDenotes book library.program (step limits library state) source ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  refine ⟨evaluate_state control (.exact (.app found functionExact argumentExact) captured) stack, ?_, ?_⟩
  · rw [step_application limits library state pc environment function argument q control found room]
    exact evaluate_state (contexts := .function q (Term.sub (Env.sub values) x) :: contexts) rfl (.exact functionExact captured)
      (.cons (.function (.exact argumentExact captured)) stack)
  · rw [step_application limits library state pc environment function argument q control found room]

theorem live_let_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment value body : Nat) (q : Quan)
    (v f : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.lett q value body))
    (valueExact : CodeDenotes library.program value v)
    (bodyExact : CodeDenotes library.program body f)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (live : q.live = true) (room : state.stack.length < limits.frames) :
    let source := plug contexts (Term.sub (Env.sub values) (.Let q v f))
    StateDenotes book library.program state source ∧
      StateDenotes book library.program (step limits library state) source ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  refine ⟨evaluate_state control (.exact (.lett found valueExact bodyExact) captured) stack, ?_, ?_⟩
  · rw [step_live_let limits library state pc environment value body q control found live room]
    exact evaluate_state (contexts := .lett q (Term.sub (Subst.up (Env.sub values)) f) live :: contexts) rfl (.exact valueExact captured)
      (.cons (.lett (.exact bodyExact captured) live) stack)
  · rw [step_live_let limits library state pc environment value body q control found live room]

theorem live_pair_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment first second : Nat) (q : Quan)
    (a b : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.tup q first second))
    (firstExact : CodeDenotes library.program first a)
    (secondExact : CodeDenotes library.program second b)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (live : q.live = true) (room : state.stack.length < limits.frames) :
    let source := plug contexts (Term.sub (Env.sub values) (.Tup q a b))
    StateDenotes book library.program state source ∧
      StateDenotes book library.program (step limits library state) source ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  refine ⟨evaluate_state control (.exact (.tup found firstExact secondExact) captured) stack, ?_, ?_⟩
  · rw [step_live_pair limits library state pc environment first second q control found live room]
    exact evaluate_state (contexts := .first q (Term.sub (Env.sub values) b) live :: contexts) rfl (.exact firstExact captured)
      (.cons (.first (.exact secondExact captured) live) stack)
  · rw [step_live_pair limits library state pc environment first second q control found live room]

/-- Rewrite evidence remains live. The erased motive survives in the exact
ghost context with its two source binders, while the real controller runs e. -/
theorem rewrite_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment evidence motive body : Nat)
    (e p f : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.rwt evidence motive body))
    (evidenceExact : CodeDenotes library.program evidence e)
    (motiveExact : CodeDenotes library.program motive p)
    (bodyExact : CodeDenotes library.program body f)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : state.stack.length < limits.frames) :
    let source := plug contexts (Term.sub (Env.sub values) (.Rwt e p f))
    StateDenotes book library.program state source ∧
      StateDenotes book library.program (step limits library state) source ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  refine ⟨evaluate_state control (.exact (.rwt found evidenceExact motiveExact bodyExact) captured) stack, ?_, ?_⟩
  · rw [step_rewrite limits library state pc environment evidence motive body control found room]
    exact evaluate_state (contexts := .rewrite (Term.sub (Subst.up (Subst.up (Env.sub values))) p) (Term.sub (Env.sub values) f) :: contexts) rfl (.exact evidenceExact captured)
      (.cons (.rewrite (.exact bodyExact captured)) stack)
  · rw [step_rewrite limits library state pc environment evidence motive body control found room]

#assert_axioms evaluate_state
#assert_axioms step_application
#assert_axioms step_live_let
#assert_axioms step_live_pair
#assert_axioms step_rewrite
#assert_axioms application_stutter
#assert_axioms live_let_stutter
#assert_axioms live_pair_stutter
#assert_axioms rewrite_stutter
end Minidregg.Theory.BendClosureSimulation

