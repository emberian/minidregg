/- Applications whose argument is not a syntactic variable are leaves of the
Bend case-tree grammar. This literal ROM path bypasses the spine classifier. -/
import Theory.BendClosureClassifierExit

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

def nonVariable : Code → Bool
  | .var _ => false
  | _ => true

theorem nonvariable_application_leaf {program : Program} {argument : Nat} {x : Term} {instruction : Code}
    (exact : CodeDenotes program argument x) (found : program.code[argument]? = some instruction)
    (notVariable : nonVariable instruction = true) (q : Quan) (f : Term) :
    Term.node (.App q f x) = false := by
  cases exact <;> simp_all [nonVariable,Term.node,Term.takes]
  all_goals subst_vars
  all_goals simp_all [nonVariable,Term.node,Term.takes]

theorem step_walk_application_leaf (limits : Limits) (library : Library) (state : State)
    (pc environment original function argument : Nat) (q : Quan) (args : List (Quan × Nat))
    (instruction : Code)
    (control : state.control = .walk pc environment original args)
    (found : library.program.code[pc]? = some (.app q function argument))
    (argumentFound : library.program.code[argument]? = some instruction)
    (notVariable : nonVariable instruction = true)
    (room : args.length ≤ limits.arguments)
    (framesRoom : state.stack.length + args.length ≤ limits.frames) :
    step limits library state =
      {state with control := .reverseArguments pc environment args [], sourceSteps := state.sourceSteps + 1} := by
  have bounded := bounded_arguments_ok limits args room
  have space : ¬ limits.frames < state.stack.length + args.length := Nat.not_lt.mpr framesRoom
  cases instruction <;> simp only [nonVariable] at notVariable <;> try contradiction
  all_goals simp [step,control,startWalk,code,found,argumentFound,walk,boundedArgs_eq,bounded,space,sourceStep,go]
  all_goals rfl

theorem walk_application_leaf_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment original function argument : Nat) (q : Quan) (args : List (Quan × Nat))
    (instruction : Code) (f x origin : Term) (values : Env) (arguments : List Arg) (contexts : List (Context book))
    (control : state.control = .walk pc environment original args)
    (found : library.program.code[pc]? = some (.app q function argument))
    (argumentFound : library.program.code[argument]? = some instruction)
    (notVariable : nonVariable instruction = true)
    (functionExact : CodeDenotes library.program function f)
    (argumentExact : CodeDenotes library.program argument x)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin (.App q f x) values arguments)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : args.length ≤ limits.arguments)
    (framesRoom : state.stack.length + args.length ≤ limits.frames) :
    let nextSource := plug contexts (Term.spine (Term.sub (Env.sub values) (.App q f x)) arguments)
    StateDenotes book library.program state (plug contexts origin) ∧
    StateDenotes book library.program (step limits library state) nextSource ∧
    Eval book (plug contexts origin) nextSource ∧
    (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  dsimp only
  have sourceExact := CodeDenotes.app found functionExact argumentExact
  have leaf := nonvariable_application_leaf argumentExact argumentFound notVariable q f
  refine ⟨?_,?_,plug_eval contexts (walkPrefix.leaf leaf),?_⟩
  · exact StateDenotes.exact
      (by rw [control]; exact .walk sourceExact captured originalExact argsExact walkPrefix) stack
      (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_walk_application_leaf limits library state pc environment original function argument q args instruction
      control found argumentFound notVariable room framesRoom]
    exact StateDenotes.exact
      (.reverseArguments (.exact sourceExact captured) argsExact .nil) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_walk_application_leaf limits library state pc environment original function argument q args instruction
      control found argumentFound notVariable room framesRoom]

#assert_axioms nonvariable_application_leaf
#assert_axioms step_walk_application_leaf
#assert_axioms walk_application_leaf_source
end Minidregg.Theory.BendClosureSimulation
