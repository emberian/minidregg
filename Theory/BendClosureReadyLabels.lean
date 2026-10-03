/- A retained label query either identifies actual source-named ROM/heap rows
or returns the literal runtime refusal. No caller supplies successful lookup. -/
import Theory.BendClosureReadyEvaluateOutcome

namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false

theorem CodeDenotes.label_name_exists {program : Program} {pc : Nat} {source : Term}
    (label : Nat) (exact : CodeDenotes program pc source)
    (found : program.code[pc]? = some (.lab label)) : ∃ name, program.names[label]? = some name := by
  cases exact <;> simp_all

theorem CodeDenotes.match_name_exists {program : Program} {pc : Nat} {source : Term}
    (label yes no : Nat) (exact : CodeDenotes program pc source)
    (found : program.code[pc]? = some (.mat label yes no)) : ∃ name, program.names[label]? = some name := by
  cases exact <;> simp_all

end Minidregg.Theory.BendClosureArena

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem RetainedReady.label_observation {book : Book} (library : Library) (state : State)
    (pointer : Nat) (source : Term) (ready : RetainedReady book library.program state.heap pointer source) :
    (∃ pc environment label name, state.heap.get? pointer = some (.closure pc environment) ∧
      library.program.code[pc]? = some (.lab label) ∧ library.program.names[label]? = some name) ∨
    labelOfFn library pointer state = .error .labelRequired := by
  cases ready with
  | closure found sourceCode captured =>
    obtain ⟨instruction,instructionFound⟩ := sourceCode.code_exists
    cases instruction with
    | lab label =>
      obtain ⟨name,named⟩ := sourceCode.label_name_exists label instructionFound
      exact .inl ⟨_,_,label,name,found,instructionFound,named⟩
    | _ =>
      right
      simp [labelOf_view,row,found,code,instructionFound]
      rfl
  | pair found first second value =>
    right
    simp [labelOf_view,row,found]
    rfl
  | application found function argument value =>
    right
    simp [labelOf_view,row,found]
    rfl

#assert_axioms CodeDenotes.label_name_exists
#assert_axioms CodeDenotes.match_name_exists
#assert_axioms RetainedReady.label_observation
end Minidregg.Theory.BendClosureSimulation
