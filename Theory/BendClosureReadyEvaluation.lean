/- Preservation of the full readiness invariant by actual evaluator branches.
Unlike the branch-source adapters, these consume one ReadyState and derive the
poststate invariant without separately supplied future frame/capture facts. -/
import Theory.BendClosureReachability
import Theory.BendClosureVariableSteps

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.direct_value {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment pointer : Nat) (instruction : Code) (heap : Heap)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some instruction)
    (direct : directValue instruction = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure pc environment) = .ok (pointer,heap)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceExact captured =>
        obtain ⟨nextFocus,nextStack,nextCache⟩ := direct_value_retains limits library state pc environment pointer
          instruction heap _ _ _ control found direct sourceExact captured stack cache allocated
        refine ReadyState.exact (.basic nextFocus) nextStack nextCache ?_ ?_
        · rw [step_direct_value limits library state pc environment pointer instruction heap control found direct allocated]
          exact (allocate_extends allocated) 0 .nil empty
        · intro result impossible
          rw [step_direct_value limits library state pc environment pointer instruction heap control found direct allocated] at impossible
          cases impossible

theorem ReadyState.reference {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment index pointer : Nat) (heap : Heap) (name : String)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.ref index))
    (named : library.program.names[index]? = some name)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure pc environment) = .ok (pointer,heap)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceExact captured =>
        have exactRef : CodeDenotes library.program pc (.Ref name) := .ref found named
        have same := CodeDenotes.functional sourceExact exactRef
        cases same
        have extension := allocate_extends allocated
        have newCaptured := captured.extends extension
        have headRow := allocate_reads_new allocated
        have retained := allocate_closure_ready exactRef captured allocated
        have certified := closure_allocation_certified limits library state pc environment pointer (.ref index)
          heap _ found (.closure exactRef captured.denotes) cache allocated
        rw [step_reference limits library state pc environment index pointer heap control found allocated]
        exact ReadyState.exact
          (.unspine (.reference headRow exactRef newCaptured) (.retained retained) .nil rfl .nil)
          (stack.extends extension) certified (extension 0 .nil empty)
          (by intro result impossible; cases impossible)

theorem ReadyState.variable {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment index : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.var index)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceExact captured =>
        have same := CodeDenotes.functional sourceExact (.var found)
        cases same
        rw [step_variable limits library state pc environment index control found]
        exact ReadyState.exact (.lookupValue captured) stack cache empty
          (by intro result impossible; cases impossible)

#assert_axioms ReadyState.direct_value
#assert_axioms ReadyState.reference
#assert_axioms ReadyState.variable
end Minidregg.Theory.BendClosureSimulation
