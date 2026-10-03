/- Complete unspine handler, including capacity, malformed-head and missing
named-definition refusal. Every premise refers to the admitted old state and
compiler-produced Library correspondence. -/
import Theory.BendClosureReadyReturnOutcome
import Theory.BendClosureReadyNamedCall

namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false

theorem CodeDenotes.reference_name_exists {program : Program} {pointer : Nat} {source : Term}
    (index : Nat) (exact : CodeDenotes program pointer source)
    (found : program.code[pointer]? = some (.ref index)) :
    ∃ name, program.names[index]? = some name := by
  cases exact <;> simp_all

#assert_axioms CodeDenotes.reference_name_exists
end Minidregg.Theory.BendClosureArena

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem bounded_arguments_failure (limits : Limits) (args : List (Quan × Nat))
    (full : ¬ args.length ≤ limits.arguments) :
    boundedArgsFn limits args = (throw Failure.argumentCapacity : Work Unit) := by
  change (if args.length ≤ limits.arguments then (pure () : Work Unit) else throw Failure.argumentCapacity) = _
  rw [if_neg full]

theorem definition_lookup_failure (library : Library) (index : Nat) (name : String)
    (named : library.program.names[index]? = some name)
    (missing : library.lookupName name = none) :
    definitionFn library index = (throw Failure.unknownDefinition : Work Nat) := by
  change (do
    let wanted ← labelNameFn library index
    match library.lookupName wanted with
    | some body => (pure body : Work Nat)
    | none => throw Failure.unknownDefinition) = _
  rw [label_name_ok library index name named]
  change (match library.lookupName name with
    | some body => (pure body : Work Nat)
    | none => throw Failure.unknownDefinition) = _
  rw [missing]

theorem ReadyState.unspine_total {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer original : Nat) (args : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (correspondence : library.SourceCorrespondence book)
    (control : state.control = .unspine pointer original args) :
    AdministrativeOutcome book limits library state source := by
  have prior := ready
  have refused {reason : Failure} (failed : step limits library state = {state with control := .refused reason}) :
      AdministrativeOutcome book limits library state source := .inr ⟨reason,failed⟩
  by_cases room : args.length ≤ limits.arguments
  · have bounded := bounded_arguments_ok limits args room
    cases ready with
    | exact focus stack cache empty complete =>
      rw [control] at focus
      cases focus with
      | basic impossible => cases impossible
      | unspine head originalReady argsReady identity values =>
        have meaning := head.denotes
        cases meaning with
        | pair row first second =>
          exact refused (reason := .callHead) (by
            simp [step,control,unspine,boundedArgs_eq,bounded,BendClosureMachine.row,row]
            rfl)
        | @application _ q function argument f x row functionMeaning argumentMeaning =>
          by_cases expanded : ((q,argument) :: args).length ≤ limits.arguments
          · exact .inl (prior.unspine_application limits library state _ pointer original function argument q args control row room expanded)
          · have expandedFailure := bounded_arguments_failure limits ((q,argument) :: args) expanded
            exact refused (reason := .argumentCapacity) (by
              simp [step,control,unspine,boundedArgs_eq,bounded,expandedFailure,BendClosureMachine.row,row]
              rfl)
        | @closure _ pc environment term env row codeMeaning captured =>
          obtain ⟨instruction,found⟩ := codeMeaning.code_exists
          cases instruction with
          | ref index =>
            obtain ⟨name,named⟩ := codeMeaning.reference_name_exists index found
            cases selected : library.lookupName name with
            | none =>
              have missing := definition_lookup_failure library index name named selected
              exact refused (reason := .unknownDefinition) (by
                simp [step,control,unspine,boundedArgs_eq,bounded,BendClosureMachine.row,row,code,found,definition_eq,missing]
                rfl)
            | some body =>
              exact .inl (prior.unspine_reference limits library state _ pointer original pc environment index body args name
                correspondence control row found named selected room)
          | _ =>
            exact refused (reason := .callHead) (by
              simp [step,control,unspine,boundedArgs_eq,bounded,BendClosureMachine.row,row,code,found]
              rfl)
  · have bounded := bounded_arguments_failure limits args room
    exact refused (reason := .argumentCapacity) (by
      simp [step,control,unspine,boundedArgs_eq,bounded]
      rfl)

#assert_axioms bounded_arguments_failure
#assert_axioms definition_lookup_failure
#assert_axioms ReadyState.unspine_total
end Minidregg.Theory.BendClosureSimulation
