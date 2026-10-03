/- Complete classifier dispatch over every admitted ROM instruction. Capacity
and original App/Var structure are derived internally from current readiness. -/
import Theory.BendClosureReadyUnspineOutcome

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem instruction_classification (instruction : Code) :
    (∃ q f x, instruction = .app q f x) ∨ directTakes instruction = true ∨ directLeaf instruction = true := by
  cases instruction <;> simp [directTakes,directLeaf]

theorem variable_application_code {program : Program} {pc index : Nat} {q : Quan} {f : Term}
    (exact : CodeDenotes program pc (.App q f (.Var index))) :
    ∃ function argument, program.code[pc]? = some (.app q function argument) ∧
      program.code[argument]? = some (.var index) := by
  cases exact with
  | app found functionCode argumentCode =>
    cases argumentCode with
    | var variableCode => exact ⟨_,_,found,variableCode⟩

theorem ReadyState.classifier_total {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original cursor : Nat) (args : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .classify pc environment original cursor args) :
    StepOutcome book limits library state source := by
  have prior := ready
  have refused {reason : Failure} (failed : step limits library state = {state with control := .refused reason}) :
      StepOutcome book limits library state source := .inr ⟨reason,failed⟩
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | classify code cursorCode application classification captured originalReady argsReady walkPrefix =>
      obtain ⟨instruction,cursorFound⟩ := cursorCode.code_exists
      rcases instruction_classification instruction with ⟨q,function,argument,same⟩ | takes | leaf
      · subst instruction
        exact .inl ⟨_,prior.classify_application limits library state _ pc environment original cursor function argument q args control cursorFound,.inl rfl⟩
      · obtain ⟨q,f,index,sourceShape⟩ := application
        cases sourceShape
        obtain ⟨function,argument,found,variableCode⟩ := variable_application_code code
        by_cases room : args.length ≤ limits.arguments
        · exact .inl ⟨_,prior.classifier_argument limits library state _ pc environment original cursor function argument index q args instruction
            control cursorFound takes found variableCode room,.inl rfl⟩
        · have bounded := bounded_arguments_failure limits args room
          exact refused (reason := .argumentCapacity) (by
            cases instruction <;> simp only [directTakes] at takes <;> try contradiction
            all_goals simp [step,control,classify,BendClosureMachine.code,cursorFound,walk,boundedArgs_eq,bounded]
            all_goals rfl)
      · obtain ⟨originalInstruction,found⟩ := code.code_exists
        by_cases room : args.length ≤ limits.arguments
        · have bounded := bounded_arguments_ok limits args room
          by_cases framesRoom : state.stack.length + args.length ≤ limits.frames
          · obtain ⟨nextSource,nextReady,sourceStep⟩ := prior.classifier_leaf limits library state _ pc environment original cursor args
              instruction originalInstruction control cursorFound leaf found room framesRoom
            exact .inl ⟨nextSource,nextReady,.inr sourceStep⟩
          · have full : limits.frames < state.stack.length + args.length := Nat.lt_of_not_ge framesRoom
            exact refused (reason := .continuationCapacity) (by
              cases instruction <;> simp only [directLeaf] at leaf <;> try contradiction
              all_goals simp [step,control,classify,BendClosureMachine.code,cursorFound,walk,boundedArgs_eq,bounded,found,full]
              all_goals rfl)
        · have bounded := bounded_arguments_failure limits args room
          exact refused (reason := .argumentCapacity) (by
            cases instruction <;> simp only [directLeaf] at leaf <;> try contradiction
            all_goals simp [step,control,classify,BendClosureMachine.code,cursorFound,walk,boundedArgs_eq,bounded]
            all_goals rfl)

#assert_axioms instruction_classification
#assert_axioms variable_application_code
#assert_axioms ReadyState.classifier_total
end Minidregg.Theory.BendClosureSimulation
