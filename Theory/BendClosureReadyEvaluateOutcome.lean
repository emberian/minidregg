/- Complete evaluator dispatch from current recursive readiness. Allocation and
capacity refusal are decided inside the proof over the literal implementation. -/
import Theory.BendClosureReadyClassifierOutcome

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem ReadyState.evaluate_total {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment) :
    StepOutcome book limits library state source := by
  have prior := ready
  have refused {reason : Failure} (failed : step limits library state = {state with control := .refused reason}) :
      StepOutcome book limits library state source := .inr ⟨reason,failed⟩
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceCode captured =>
        obtain ⟨instruction,found⟩ := sourceCode.code_exists
        cases instruction with
        | var index => exact .inl ⟨_,prior.variable limits library state _ pc environment index control found,.inl rfl⟩
        | ref index =>
          obtain ⟨name,named⟩ := sourceCode.reference_name_exists index found
          cases allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap (.closure pc environment) with
          | error reason =>
            exact refused (reason := .arena reason) (by
              simp [step,control,evaluate,code,found,closure,BendClosureMachine.allocate,allocated]
              rfl)
          | ok result =>
            rcases result with ⟨pointer,heap⟩
            exact .inl ⟨_,prior.reference limits library state _ pc environment index pointer heap name control found named allocated,.inl rfl⟩
        | ann value type =>
          obtain ⟨nextSource,nextReady,sourceStep⟩ := prior.annotation limits library state _ pc environment value type control found
          exact .inl ⟨nextSource,nextReady,.inr sourceStep⟩
        | app q function argument =>
          by_cases room : state.stack.length < limits.frames
          · exact .inl ⟨_,prior.application limits library state _ pc environment function argument q control found room,.inl rfl⟩
          · exact refused (reason := .continuationCapacity) (by
              simp [step,control,evaluate,code,found,push,Nat.le_of_not_gt room]
              rfl)
        | lett q value body =>
          by_cases live : q.live = true
          · by_cases room : state.stack.length < limits.frames
            · exact .inl ⟨_,prior.live_let limits library state _ pc environment value body q control found live room,.inl rfl⟩
            · exact refused (reason := .continuationCapacity) (by
                simp [step,control,evaluate,code,found,live,push,Nat.le_of_not_gt room]
                rfl)
          · have dead : q = .Q0 := by cases q <;> simp_all only [Quan.live,Bool.false_eq_true,not_true_eq_false]
            subst q
            obtain ⟨v,b,same,valueCode,bodyCode⟩ := sourceCode.let_fields .Q0 value body found
            obtain ⟨valueInstruction,valueFound⟩ := valueCode.code_exists
            cases allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap (.closure value environment) with
            | error reason =>
              exact refused (reason := .arena reason) (by
                cases valueInstruction <;> simp [step,control,evaluate,code,found,Quan.live,closure,
                  BendClosureMachine.allocate,valueFound,allocated] <;> rfl)
            | ok result =>
              rcases result with ⟨pointer,middle⟩
              cases installed : BendClosureArena.allocate limits.heap library.program.code.size middle (.environment pointer environment) with
              | error reason =>
                exact refused (reason := .arena reason) (by
                  cases valueInstruction <;> simp [step,control,evaluate,code,found,Quan.live,closure,
                    BendClosureMachine.allocate,valueFound,allocated,BendClosureMachine.bind,isData,installed] <;> rfl)
              | ok result =>
                rcases result with ⟨nextEnvironment,heap⟩
                obtain ⟨nextSource,nextReady,sourceStep⟩ := prior.dead_let limits library state _ pc environment value body pointer nextEnvironment middle heap
                  control found allocated installed
                exact .inl ⟨nextSource,nextReady,.inr sourceStep⟩
        | tup q first second =>
          by_cases live : q.live = true
          · by_cases room : state.stack.length < limits.frames
            · exact .inl ⟨_,prior.live_pair limits library state _ pc environment first second q control found live room,.inl rfl⟩
            · exact refused (reason := .continuationCapacity) (by
                simp [step,control,evaluate,code,found,live,push,Nat.le_of_not_gt room]
                rfl)
          · have dead : q = .Q0 := by cases q <;> simp_all only [Quan.live,Bool.false_eq_true,not_true_eq_false]
            subst q
            obtain ⟨a,b,same,firstCode,secondCode⟩ := sourceCode.pair_fields .Q0 first second found
            obtain ⟨firstInstruction,firstFound⟩ := firstCode.code_exists
            cases allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap (.closure first environment) with
            | error reason =>
              exact refused (reason := .arena reason) (by
                cases firstInstruction <;> simp [step,control,evaluate,code,found,Quan.live,closure,
                  BendClosureMachine.allocate,firstFound,allocated] <;> rfl)
            | ok result =>
              rcases result with ⟨pointer,heap⟩
              by_cases room : state.stack.length < limits.frames
              · exact .inl ⟨_,prior.dead_pair limits library state _ pc environment first second pointer heap control found allocated room,.inl rfl⟩
              · exact refused (reason := .continuationCapacity) (by
                  cases firstInstruction <;> simp [step,control,evaluate,code,found,Quan.live,closure,
                    BendClosureMachine.allocate,firstFound,allocated,push,Nat.le_of_not_gt room] <;> rfl)
        | rwt evidence motive body =>
          by_cases room : state.stack.length < limits.frames
          · exact .inl ⟨_,prior.rewrite limits library state _ pc environment evidence motive body control found room,.inl rfl⟩
          · exact refused (reason := .continuationCapacity) (by
              simp [step,control,evaluate,code,found,push,Nat.le_of_not_gt room]
              rfl)
        | _ =>
          cases allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap (.closure pc environment) with
          | error reason =>
            exact refused (reason := .arena reason) (by
              simp [step,control,evaluate,code,found,closure,BendClosureMachine.allocate,allocated]
              rfl)
          | ok result =>
            rcases result with ⟨pointer,heap⟩
            exact .inl ⟨_,prior.direct_value limits library state _ pc environment pointer _ heap control found rfl allocated,.inl rfl⟩

#assert_axioms ReadyState.evaluate_total
end Minidregg.Theory.BendClosureSimulation
