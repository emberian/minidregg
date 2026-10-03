/- The actual case-tree leaf commit performs exactly one upstream Eval.call.
Capacity is checked before that source step. Argument reversal and installation
remain separate physical ticks, already represented by the source spine. -/
import Theory.BendClosureCallSteps

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

def directLeaf : Code → Bool
  | .lam .. | .prj .. | .mat .. | .efq | .app .. => false
  | _ => true

theorem bounded_arguments_ok (limits : Limits) (args : List (Quan × Nat))
    (room : args.length ≤ limits.arguments) :
    boundedArgsFn limits args = (pure () : Work Unit) := by
  change (if args.length ≤ limits.arguments then (pure () : Work Unit)
    else throw Failure.argumentCapacity) = _
  simp [room]

theorem direct_leaf_source {program : Program} {pc : Nat} {source : Term}
    {instruction : Code} (exact : CodeDenotes program pc source)
    (found : program.code[pc]? = some instruction) (leaf : directLeaf instruction = true) :
    Term.node source = false := by
  cases exact <;> simp_all [directLeaf, Term.node, Term.takes]
  all_goals subst_vars
  all_goals simp_all [directLeaf, Term.node, Term.takes]

set_option maxHeartbeats 800000 in
theorem step_walk_leaf (limits : Limits) (library : Library) (state : State)
    (pc environment original : Nat) (args : List (Quan × Nat)) (instruction : Code)
    (control : state.control = .walk pc environment original args)
    (found : library.program.code[pc]? = some instruction)
    (leaf : directLeaf instruction = true)
    (argumentsRoom : args.length ≤ limits.arguments)
    (framesRoom : state.stack.length + args.length ≤ limits.frames) :
    step limits library state =
      {state with control := .reverseArguments pc environment args [], sourceSteps := state.sourceSteps + 1} := by
  have bounded := bounded_arguments_ok limits args argumentsRoom
  have space : ¬ limits.frames < state.stack.length + args.length := Nat.not_lt.mpr framesRoom
  cases instruction <;> simp only [directLeaf] at leaf <;> try contradiction
  all_goals simp [step, control, startWalk, walk, code, found, boundedArgs_eq, bounded, sourceStep, go, space]
  all_goals rfl

theorem walk_leaf_source {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment original : Nat) (args : List (Quan × Nat))
    (instruction : Code) (source origin : Term) (values : Env) (arguments : List Arg)
    (contexts : List (Context book))
    (control : state.control = .walk pc environment original args)
    (found : library.program.code[pc]? = some instruction)
    (leaf : directLeaf instruction = true)
    (sourceExact : CodeDenotes library.program pc source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin source values arguments)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (argumentsRoom : args.length ≤ limits.arguments)
    (framesRoom : state.stack.length + args.length ≤ limits.frames) :
    let nextSource := plug contexts (Term.spine (Term.sub (Env.sub values) source) arguments)
    StateDenotes book library.program state (plug contexts origin) ∧
      StateDenotes book library.program (step limits library state) nextSource ∧
      Eval book (plug contexts origin) nextSource ∧
      (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply StateDenotes.exact (contexts := contexts)
    · rw [control]
      exact .walk sourceExact captured originalExact argsExact walkPrefix
    · exact stack
    · intro pointer impossible
      rw [control] at impossible
      cases impossible
  · rw [step_walk_leaf limits library state pc environment original args instruction control found leaf argumentsRoom framesRoom]
    exact StateDenotes.exact (contexts := contexts)
      (.reverseArguments (.exact sourceExact captured) argsExact .nil) stack
      (by intro pointer impossible; cases impossible)
  · exact plug_eval contexts (walkPrefix.leaf (direct_leaf_source sourceExact found leaf))
  · rw [step_walk_leaf limits library state pc environment original args instruction control found leaf argumentsRoom framesRoom]

#assert_axioms bounded_arguments_ok
#assert_axioms direct_leaf_source
#assert_axioms step_walk_leaf
#assert_axioms walk_leaf_source
end Minidregg.Theory.BendClosureSimulation
