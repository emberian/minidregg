/- Whole readiness through actual beta and pair projection. Q2 duplication is
justified from the computed Data cache and the retained source denotation. -/
import Theory.BendClosureReadyWalk

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.beta {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (function argument pc environment body nextEnvironment : Nat)
    (heap : Heap) (binder quantity : Quan)
    (ready : ReadyState book library.program state source)
    (control : state.control = .apply quantity function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.lam binder body))
    (compatible : binder.live = quantity.live)
    (copied : binder = .Q2 → state.data[argument]?.getD false = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.environment argument environment) = .ok (nextEnvironment,heap)) :
    ∃ nextSource, ReadyState book library.program (step limits library state) nextSource ∧ Eval book source nextSource := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | apply functionReady argumentReady functionValue argumentValue =>
        cases functionReady with
        | pair other first second value => rw [functionRow] at other; cases other
        | application other left right value => rw [functionRow] at other; cases other
        | closure other code captured =>
          rw [functionRow] at other
          cases other
          obtain ⟨f,same,bodyCode⟩ := code.lambda_fields binder body instruction
          cases same
          have extension := allocate_extends allocated
          have newCaptured := allocate_environment_ready argumentReady captured allocated
          have certified := cache.allocate false allocated (by intro impossible; cases impossible)
          have sourceStep := (beta_source limits library state function argument pc environment body nextEnvironment heap
            _ _ _ _ binder quantity control functionRow instruction bodyCode captured.denotes argumentReady.denotes
            argumentValue compatible copied cache stack.denotes allocated).2.2.1
          refine ⟨_,?_,sourceStep⟩
          rw [step_beta limits library state function argument pc environment body nextEnvironment heap binder quantity
            control functionRow instruction compatible copied allocated]
          exact ReadyState.exact (.basic (.evaluate bodyCode newCaptured)) (stack.extends extension) certified
            (extension 0 .nil empty) (by intro result impossible; cases impossible)

theorem ReadyState.projection {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (function argument pc environment handler first second : Nat) (q r : Quan)
    (ready : ReadyState book library.program state source)
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.prj handler))
    (argumentRow : state.heap.get? argument = some (.pair r first second))
    (live : q.live = true) (room : state.stack.length + 1 < limits.frames) :
    ∃ nextSource, ReadyState book library.program (step limits library state) nextSource ∧ Eval book source nextSource := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | apply functionReady argumentReady functionValue argumentValue =>
        cases functionReady with
        | pair other left right value => rw [functionRow] at other; cases other
        | application other left right value => rw [functionRow] at other; cases other
        | closure other code captured =>
          rw [functionRow] at other
          cases other
          obtain ⟨f,same,handlerCode⟩ := code.projection_fields handler instruction
          cases same
          obtain ⟨a,b,argumentSame,firstReady,secondReady,pairValue⟩ := argumentReady.pair_fields argumentRow
          cases argumentSame
          have sourceStep := (projection_source limits library state function argument pc environment handler first second q r
            _ _ _ _ _ control functionRow instruction argumentRow handlerCode captured.denotes firstReady.denotes
            secondReady.denotes pairValue stack.denotes live room).2.2.1
          refine ⟨_,?_,sourceStep⟩
          rw [step_projection limits library state function argument pc environment handler first second q r
            control functionRow instruction argumentRow live room]
          exact ReadyState.exact (contexts := .function (Quan.fld r q) a :: .function q b :: _)
            (.basic (.evaluate handlerCode captured)) (.cons (.knownArgument firstReady) (.cons (.knownArgument secondReady) stack))
            cache empty (by intro result impossible; cases impossible)

#assert_axioms ReadyState.beta
#assert_axioms ReadyState.projection
end Minidregg.Theory.BendClosureSimulation
