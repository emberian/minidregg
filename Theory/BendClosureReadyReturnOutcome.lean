/- Complete return dispatch: every recursively ready return either preserves
readiness with zero/one source step, or restores the whole old payload on
refusal. Runtime guards and allocation outcomes are split internally. -/
import Theory.BendClosureReadyRewrite
import Theory.BendClosureReadyOutcome

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

def SuccessfulOutcome (book : Book) (limits : Limits) (library : Library) (state : State) (source : Term) : Prop :=
  ∃ nextSource, ReadyState book library.program (step limits library state) nextSource ∧
    (source = nextSource ∨ Eval book source nextSource)

def StepOutcome (book : Book) (limits : Limits) (library : Library) (state : State) (source : Term) : Prop :=
  SuccessfulOutcome book limits library state source ∨
    ∃ reason, step limits library state = {state with control := .refused reason}

theorem ReadyState.returned_total {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned pointer) :
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
      | returned pointerReady value =>
        cases shape : state.stack with
        | nil => exact .inl ⟨_,prior.return_empty limits library state _ pointer control shape,.inl rfl⟩
        | cons frame rest =>
          rw [shape] at stack
          cases stack with
          | cons frameReady tail =>
            cases frameReady with
            | @argument q function f functionReady functionValue live =>
              exact .inl ⟨_,prior.return_argument limits library state _ pointer function q rest control shape,.inl rfl⟩
            | @function q argument environment x values argumentCode captured =>
              by_cases live : q.live = true
              · by_cases room : rest.length < limits.frames
                · exact .inl ⟨_,prior.return_function_live limits library state _ pointer argument environment q rest control shape live room,.inl rfl⟩
                · exact (refused (reason := .continuationCapacity) (by
                    simp [step,control,returnValue,shape,live,push,Nat.le_of_not_gt room]
                    rfl))
              · have dead : q = .Q0 := by cases q <;> simp_all only [Quan.live, Bool.false_eq_true, not_true_eq_false]
                subst q
                obtain ⟨instruction,found⟩ := argumentCode.code_exists
                cases allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap (.closure argument environment) with
                | error reason =>
                  exact (refused (reason := .arena reason) (by
                    cases instruction <;> simp [step,control,returnValue,shape,Quan.live,closure,
                      BendClosureMachine.allocate,code,found,allocated] <;> rfl))
                | ok result =>
                  rcases result with ⟨result,heap⟩
                  exact .inl ⟨_,prior.return_function_dead limits library state _ pointer argument environment result heap rest control shape allocated,.inl rfl⟩
            | @knownArgument q argument x argumentReady =>
              by_cases live : q.live = true
              · by_cases room : rest.length < limits.frames
                · exact .inl ⟨_,prior.return_known_live limits library state _ pointer argument q rest control shape live room,.inl rfl⟩
                · exact (refused (reason := .continuationCapacity) (by
                    simp [step,control,returnValue,shape,live,push,Nat.le_of_not_gt room]
                    rfl))
              · have dead : q = .Q0 := by cases q <;> simp_all only [Quan.live, Bool.false_eq_true, not_true_eq_false]
                subst q
                exact .inl ⟨_,prior.return_known_dead limits library state _ pointer argument rest control shape,.inl rfl⟩
            | @first q second environment b values secondCode captured live =>
              by_cases room : rest.length < limits.frames
              · exact .inl ⟨_,prior.return_first limits library state _ pointer second environment q rest control shape room,.inl rfl⟩
              · exact (refused (reason := .continuationCapacity) (by
                  simp [step,control,returnValue,shape,push,Nat.le_of_not_gt room]
                  rfl))
            | @second q first a firstReady firstValue =>
              cases allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap (.pair q first pointer) with
              | error reason =>
                exact (refused (reason := .arena reason) (by
                  simp [step,control,returnValue,shape,BendClosureMachine.allocate,allocated]
                  rfl))
              | ok result =>
                rcases result with ⟨result,heap⟩
                exact .inl ⟨_,prior.return_second limits library state _ pointer first result q heap rest control shape allocated,.inl rfl⟩
            | @lett q body environment f values bodyCode captured live =>
              by_cases copied : q = .Q2 → state.data[pointer]?.getD false = true
              · cases allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap (.environment pointer environment) with
                | error reason =>
                  exact (refused (reason := .arena reason) (by
                    cases q <;> simp [step,control,returnValue,shape,BendClosureMachine.bind,isData,
                      BendClosureMachine.allocate,allocated,copied] <;> rfl))
                | ok result =>
                  rcases result with ⟨nextEnvironment,heap⟩
                  obtain ⟨nextSource,nextReady,sourceStep⟩ := prior.return_let limits library state _ pointer body environment nextEnvironment q heap rest control shape copied allocated
                  exact .inl ⟨nextSource,nextReady,.inr sourceStep⟩
              · have q2 : q = .Q2 := by
                  by_cases same : q = .Q2
                  · exact same
                  · exact False.elim (copied (fun proof => False.elim (same proof)))
                subst q
                have bit : state.data[pointer]?.getD false = false := by
                  cases h : state.data[pointer]?.getD false
                  · rfl
                  · exact False.elim (copied (fun _ => h))
                exact (refused (reason := .notData) (by
                  simp [step,control,returnValue,shape,BendClosureMachine.bind,isData,bit]
                  rfl))
            | @rewrite body environment f motive values bodyCode captured =>
              cases pointerReady with
              | pair row first second pairValue =>
                exact (refused (reason := .rewriteEvidence) (by
                  simp [step,control,returnValue,shape,BendClosureMachine.row,row]
                  rfl))
              | application row function argument appValue =>
                exact (refused (reason := .rewriteEvidence) (by
                  simp [step,control,returnValue,shape,BendClosureMachine.row,row]
                  rfl))
              | @closure _ pc evidenceEnvironment term evidenceValues row evidenceCode evidenceCaptured =>
                obtain ⟨instruction,found⟩ := evidenceCode.code_exists
                cases instruction with
                | rfl =>
                  obtain ⟨nextSource,nextReady,sourceStep⟩ := prior.return_rewrite limits library state _ pointer pc evidenceEnvironment body environment rest control shape row found
                  exact .inl ⟨nextSource,nextReady,.inr sourceStep⟩
                | _ =>
                  exact (refused (reason := .rewriteEvidence) (by
                    simp [step,control,returnValue,shape,BendClosureMachine.row,row,code,found]
                    rfl))

theorem ReadyState.returned_outcome {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned pointer)
    (notRefused : ∀ reason, (step limits library state).control ≠ .refused reason) :
    SuccessfulOutcome book limits library state source := by
  rcases ready.returned_total limits library state source pointer control with success | ⟨reason,failed⟩
  · exact success
  · exact False.elim (notRefused reason (congrArg State.control failed))

#assert_axioms ReadyState.returned_total
#assert_axioms ReadyState.returned_outcome
end Minidregg.Theory.BendClosureSimulation
