/- The classifier follows the actual ROM spine, then either enters a case
argument lookup or commits the complete leaf. Its source flag is derived from
CodeDenotes and the retained head-classification equality. -/
import Theory.BendClosureWalkMatching

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem direct_takes_head {program : Program} {pc : Nat} {source : Term} {instruction : Code}
    (exact : CodeDenotes program pc source) (found : program.code[pc]? = some instruction)
    (takes : directTakes instruction = true) : Term.takes (Term.unspine source []).1 = true := by
  cases exact <;> simp_all [directTakes,Term.unspine,Term.takes]
  all_goals subst_vars
  all_goals simp_all [directTakes,Term.unspine,Term.takes]

theorem direct_leaf_head {program : Program} {pc : Nat} {source : Term} {instruction : Code}
    (exact : CodeDenotes program pc source) (found : program.code[pc]? = some instruction)
    (leaf : directLeaf instruction = true) : Term.takes (Term.unspine source []).1 = false := by
  cases exact <;> simp_all [directLeaf,Term.unspine,Term.takes]
  all_goals subst_vars
  all_goals simp_all [directLeaf,Term.unspine,Term.takes]

theorem step_classifier_argument (limits : Limits) (library : Library) (state : State)
    (pc environment original cursor function argument index : Nat) (q : Quan)
    (args : List (Quan × Nat)) (instruction : Code)
    (control : state.control = .classify pc environment original cursor args)
    (cursorFound : library.program.code[cursor]? = some instruction)
    (takes : directTakes instruction = true)
    (found : library.program.code[pc]? = some (.app q function argument))
    (variableCode : library.program.code[argument]? = some (.var index))
    (room : args.length ≤ limits.arguments) :
    step limits library state =
      {state with control := .lookup index environment (.walkArgument q function environment original args)} := by
  have bounded := bounded_arguments_ok limits args room
  cases instruction <;> simp only [directTakes] at takes <;> try contradiction
  all_goals simp [step,control,classify,code,cursorFound,walk,boundedArgs_eq,bounded,found,variableCode,go]
  all_goals rfl

theorem classifier_argument_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment original cursor function argument index : Nat) (q : Quan)
    (args : List (Quan × Nat)) (instruction : Code) (f cursorSource origin : Term)
    (values : Env) (arguments : List Arg) (contexts : List (Context book))
    (control : state.control = .classify pc environment original cursor args)
    (cursorFound : library.program.code[cursor]? = some instruction)
    (takes : directTakes instruction = true)
    (found : library.program.code[pc]? = some (.app q function argument))
    (variableCode : library.program.code[argument]? = some (.var index))
    (functionExact : CodeDenotes library.program function f)
    (cursorExact : CodeDenotes library.program cursor cursorSource)
    (classification : Term.node (.App q f (.Var index)) = Term.takes (Term.unspine cursorSource []).1)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin (.App q f (.Var index)) values arguments)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : args.length ≤ limits.arguments) :
    StateDenotes book library.program state (plug contexts origin) ∧
    StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  have sourceExact := CodeDenotes.app found functionExact (CodeDenotes.var variableCode)
  have node : Term.node (.App q f (.Var index)) = true :=
    classification.trans (direct_takes_head cursorExact cursorFound takes)
  refine ⟨?_,?_,?_⟩
  · exact StateDenotes.exact
      (by rw [control]; exact .classify sourceExact cursorExact classification captured originalExact argsExact walkPrefix)
      stack (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_classifier_argument limits library state pc environment original cursor function argument index q args
      instruction control cursorFound takes found variableCode room]
    exact StateDenotes.exact
      (.lookupWalk functionExact captured captured originalExact argsExact (walkPrefix.app node)) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_classifier_argument limits library state pc environment original cursor function argument index q args
      instruction control cursorFound takes found variableCode room]

theorem step_classifier_leaf (limits : Limits) (library : Library) (state : State)
    (pc environment original cursor : Nat) (args : List (Quan × Nat)) (instruction originalInstruction : Code)
    (control : state.control = .classify pc environment original cursor args)
    (cursorFound : library.program.code[cursor]? = some instruction)
    (leaf : directLeaf instruction = true)
    (found : library.program.code[pc]? = some originalInstruction)
    (room : args.length ≤ limits.arguments)
    (framesRoom : state.stack.length + args.length ≤ limits.frames) :
    step limits library state =
      {state with control := .reverseArguments pc environment args [], sourceSteps := state.sourceSteps + 1} := by
  have bounded := bounded_arguments_ok limits args room
  have space : ¬ limits.frames < state.stack.length + args.length := Nat.not_lt.mpr framesRoom
  cases instruction <;> simp only [directLeaf] at leaf <;> try contradiction
  all_goals simp [step,control,classify,code,cursorFound,walk,boundedArgs_eq,bounded,found,space,sourceStep,go]
  all_goals rfl

theorem classifier_leaf_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment original cursor : Nat) (args : List (Quan × Nat)) (instruction originalInstruction : Code)
    (source cursorSource origin : Term) (values : Env) (arguments : List Arg) (contexts : List (Context book))
    (control : state.control = .classify pc environment original cursor args)
    (cursorFound : library.program.code[cursor]? = some instruction)
    (leaf : directLeaf instruction = true)
    (found : library.program.code[pc]? = some originalInstruction)
    (sourceExact : CodeDenotes library.program pc source)
    (cursorExact : CodeDenotes library.program cursor cursorSource)
    (classification : Term.node source = Term.takes (Term.unspine cursorSource []).1)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin source values arguments)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : args.length ≤ limits.arguments)
    (framesRoom : state.stack.length + args.length ≤ limits.frames) :
    let nextSource := plug contexts (Term.spine (Term.sub (Env.sub values) source) arguments)
    StateDenotes book library.program state (plug contexts origin) ∧
    StateDenotes book library.program (step limits library state) nextSource ∧
    Eval book (plug contexts origin) nextSource ∧
    (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  dsimp only
  have notNode := classification.trans (direct_leaf_head cursorExact cursorFound leaf)
  refine ⟨?_,?_,plug_eval contexts (walkPrefix.leaf notNode),?_⟩
  · exact StateDenotes.exact
      (by rw [control]; exact .classify sourceExact cursorExact classification captured originalExact argsExact walkPrefix)
      stack (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_classifier_leaf limits library state pc environment original cursor args instruction originalInstruction
      control cursorFound leaf found room framesRoom]
    exact StateDenotes.exact
      (.reverseArguments (.exact sourceExact captured) argsExact .nil) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_classifier_leaf limits library state pc environment original cursor args instruction originalInstruction
      control cursorFound leaf found room framesRoom]

#assert_axioms direct_takes_head
#assert_axioms direct_leaf_head
#assert_axioms step_classifier_argument
#assert_axioms classifier_argument_source
#assert_axioms step_classifier_leaf
#assert_axioms classifier_leaf_source
end Minidregg.Theory.BendClosureSimulation
