/- Complete ordinary application handler. Quantity, Data, row-shape, label,
allocation and frame guards are decided from the actual retained state. -/
import Theory.BendClosureReadyLabels

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem ReadyState.apply_total {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (q : Quan) (function argument : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .apply q function argument) :
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
      | apply functionReady argumentReady functionValue argumentValue =>
        cases functionReady with
        | pair functionRow first second value =>
          exact refused (reason := .functionRequired) (by
            simp [step,control,BendClosureMachine.apply,row,functionRow]
            rfl)
        | @application _ left right r f x functionRow leftReady rightReady value =>
          cases allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap (.application q function argument) with
          | error reason =>
            exact refused (reason := .arena reason) (by
              simp [step,control,BendClosureMachine.apply,row,functionRow,BendClosureMachine.allocate,allocated]
              rfl)
          | ok result =>
            rcases result with ⟨original,heap⟩
            exact .inl ⟨_,prior.apply_residual_application limits library state _ function argument left right original q r heap control functionRow allocated,.inl rfl⟩
        | @closure _ pc environment f values functionRow sourceCode captured =>
          obtain ⟨instruction,found⟩ := sourceCode.code_exists
          cases instruction with
          | lam binder body =>
            by_cases compatible : binder.live = q.live
            · by_cases copied : binder = .Q2 → state.data[argument]?.getD false = true
              · cases allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap (.environment argument environment) with
                | error reason =>
                  exact refused (reason := .arena reason) (by
                    cases binder <;> simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,compatible,
                      BendClosureMachine.bind,isData,BendClosureMachine.allocate,allocated,copied] <;> rfl)
                | ok result =>
                  rcases result with ⟨nextEnvironment,heap⟩
                  obtain ⟨nextSource,nextReady,sourceStep⟩ := prior.beta limits library state _ function argument pc environment body nextEnvironment heap binder q
                    control functionRow found compatible copied allocated
                  exact .inl ⟨nextSource,nextReady,.inr sourceStep⟩
              · have q2 : binder = .Q2 := by
                  by_cases same : binder = .Q2
                  · exact same
                  · exact False.elim (copied (fun proof => False.elim (same proof)))
                subst binder
                have notData : state.data[argument]?.getD false = false := by
                  cases data : state.data[argument]?.getD false
                  · rfl
                  · exact False.elim (copied (fun _ => data))
                exact refused (reason := .notData) (by
                  simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,compatible,
                    BendClosureMachine.bind,isData,notData]
                  rfl)
            · exact refused (reason := .quantity) (by
                simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,compatible]
                rfl)
          | prj handler =>
            by_cases live : q.live = true
            · cases argumentReady with
              | closure argumentRow argumentCode capturedArgument =>
                exact refused (reason := .pairRequired) (by
                  simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,live,argumentRow]
                  rfl)
              | application argumentRow left right value =>
                exact refused (reason := .pairRequired) (by
                  simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,live,argumentRow]
                  rfl)
              | @pair _ first second r a b argumentRow firstReady secondReady value =>
                by_cases room : state.stack.length + 1 < limits.frames
                · obtain ⟨nextSource,nextReady,sourceStep⟩ := prior.projection limits library state _ function argument pc environment handler first second q r
                    control functionRow found argumentRow live room
                  exact .inl ⟨nextSource,nextReady,.inr sourceStep⟩
                · exact refused (reason := .continuationCapacity) (by
                    by_cases firstRoom : state.stack.length < limits.frames
                    · simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,live,argumentRow,
                        push,Nat.not_le_of_gt firstRoom,Nat.le_of_not_gt room]
                      rfl
                    · simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,live,argumentRow,
                        push,Nat.le_of_not_gt firstRoom]
                      rfl)
            · exact refused (reason := .liveArgument) (by
                simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,live]
                rfl)
          | mat label yes no =>
            by_cases live : q.live = true
            · obtain ⟨wantedName,wanted⟩ := sourceCode.match_name_exists label yes no found
              rcases argumentReady.label_observation library state argument _ with ⟨argumentPC,argumentEnvironment,actualLabel,actualName,argumentRow,argumentCode,actual⟩ | badLabel
              · by_cases room : actualName ≠ wantedName → state.stack.length < limits.frames
                · obtain ⟨nextSource,nextReady,sourceStep⟩ := prior.matching limits library state _ function argument pc environment label yes no argumentPC argumentEnvironment actualLabel q wantedName actualName
                    control functionRow found argumentRow argumentCode wanted actual live room
                  exact .inl ⟨nextSource,nextReady,.inr sourceStep⟩
                · have different : actualName ≠ wantedName := by
                    intro same
                    exact room (fun unequal => False.elim (unequal same))
                  have full : limits.frames ≤ state.stack.length := by
                    apply Nat.le_of_not_gt
                    intro small
                    exact room (fun _ => small)
                  exact refused (reason := .continuationCapacity) (by
                    simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,live,
                      labelOf_eq,labelOf_view,argumentRow,argumentCode,actual,labelName_eq,label_name_ok library label wantedName wanted,
                      different,push,sourceStep,full]
                    rfl)
              · exact refused (reason := .labelRequired) (by
                  simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,live,labelOf_eq]
                  change (match (do
                    let actual ← labelOfFn library argument state
                    let wanted ← labelNameFn library label actual.2
                    let updated ← sourceStep wanted.2
                    (if actual.1 == wanted.1 then go (.evaluate yes environment)
                     else do push limits (.knownArgument q argument); go (.evaluate no environment)) updated.2) with
                    | .ok (_,next) => next | .error reason => {state with control := .refused reason}) = _
                  rw [badLabel]
                  rfl)
            · exact refused (reason := .liveArgument) (by
                simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,live]
                rfl)
          | _ =>
            cases allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap (.application q function argument) with
            | error reason =>
              exact refused (reason := .arena reason) (by
                simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,BendClosureMachine.allocate,allocated]
                rfl)
            | ok result =>
              rcases result with ⟨original,heap⟩
              exact .inl ⟨_,prior.apply_residual_closure limits library state _ function argument pc environment original q _ heap
                control functionRow found rfl allocated,.inl rfl⟩

#assert_axioms ReadyState.apply_total
end Minidregg.Theory.BendClosureSimulation
