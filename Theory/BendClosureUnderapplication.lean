/- Named functions underapplied at a direct case node become source Values
by completing the retained Walk with need. Value is derived, not assumed. -/
import Theory.BendClosureWalkLeaf

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

def directTakes : Code → Bool
  | .lam .. | .prj .. | .mat .. | .efq => true
  | _ => false

theorem direct_takes_source {program : Program} {pc : Nat} {source : Term}
    {instruction : Code} (exact : CodeDenotes program pc source)
    (found : program.code[pc]? = some instruction) (takes : directTakes instruction = true) :
    Term.takes source = true := by
  cases exact <;> simp_all [directTakes, Term.takes]
  all_goals subst_vars
  all_goals simp_all [directTakes, Term.takes]

theorem step_walk_underapplication (limits : Limits) (library : Library) (state : State)
    (pc environment original : Nat) (instruction : Code)
    (control : state.control = .walk pc environment original [])
    (found : library.program.code[pc]? = some instruction)
    (takes : directTakes instruction = true) :
    step limits library state = {state with control := .returned original} := by
  have bounded := bounded_arguments_ok limits [] (Nat.zero_le _)
  cases instruction <;> simp only [directTakes] at takes <;> try contradiction
  all_goals simp [step, control, startWalk, walk, code, found, boundedArgs_eq, bounded, go]
  all_goals rfl

theorem walk_underapplication_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment original : Nat) (instruction : Code) (source origin : Term)
    (values : Env) (contexts : List (Context book))
    (control : state.control = .walk pc environment original [])
    (found : library.program.code[pc]? = some instruction)
    (takes : directTakes instruction = true)
    (sourceExact : CodeDenotes library.program pc source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (originalExact : Denotes library.program state.heap original origin)
    (walkPrefix : WalkPrefix book origin source values [])
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
    StateDenotes book library.program state (plug contexts origin) ∧
      StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
      Value book origin ∧ (step limits library state).sourceSteps = state.sourceSteps := by
  have value := walkPrefix.need (direct_takes_source sourceExact found takes)
  refine ⟨?_, ?_, value, ?_⟩
  · exact StateDenotes.exact (by rw [control]; exact .walk sourceExact captured originalExact .nil walkPrefix)
      stack (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_walk_underapplication limits library state pc environment original instruction control found takes]
    exact StateDenotes.exact (.returned originalExact value) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_walk_underapplication limits library state pc environment original instruction control found takes]

#assert_axioms direct_takes_source
#assert_axioms step_walk_underapplication
#assert_axioms walk_underapplication_source
end Minidregg.Theory.BendClosureSimulation
