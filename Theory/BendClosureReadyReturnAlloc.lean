/- Return-time allocation and thunk reopening preserve whole-state readiness. -/
import Theory.BendClosureReadyReturn

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.return_second {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer first result : Nat) (q : Quan) (heap : Heap) (rest : List BendClosureMachine.Frame)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .second q first :: rest)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.pair q first pointer) = .ok (result,heap)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | returned pointerReady value =>
        rw [stackShape] at stack
        cases stack with
        | cons frame tail =>
          cases frame with
          | second firstReady firstValue =>
            have newReady := allocate_pair_ready firstReady pointerReady (.tup firstValue value) allocated
            have certified := (pair_allocation_sound limits library state q first pointer result heap _ cache
              (.pair firstReady.denotes pointerReady.denotes) allocated).2.2
            rw [step_return_second limits library state pointer first result q heap rest control stackShape allocated]
            exact ReadyState.exact (focus := .Tup q _ _) (.basic (.returned newReady (.tup firstValue value)))
              (RetainedStack.extends (allocate_extends allocated) tail) certified (allocate_extends allocated 0 .nil empty)
              (by intro next impossible; cases impossible)

theorem ReadyState.return_function_dead {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (function argument environment pointer : Nat) (heap : Heap) (rest : List BendClosureMachine.Frame)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned function)
    (stackShape : state.stack = .function .Q0 argument environment :: rest)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure argument environment) = .ok (pointer,heap)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | returned functionReady value =>
        rw [stackShape] at stack
        cases stack with
        | cons frame tail =>
          cases frame with
          | function argumentCode captured =>
            obtain ⟨instruction,found⟩ := argumentCode.code_exists
            have extension := allocate_extends allocated
            have argumentReady := allocate_closure_ready argumentCode captured allocated
            have certified := closure_allocation_certified limits library state argument environment pointer instruction
              heap _ found (.closure argumentCode captured.denotes) cache allocated
            rw [step_return_function_dead limits library state function argument environment pointer instruction heap rest
              control stackShape found allocated]
            exact ReadyState.exact (focus := .App .Q0 _ _)
              (.basic (.apply (q := .Q0) (functionReady.extends extension) argumentReady value (by intro h; cases h)))
              (RetainedStack.extends extension tail) certified (extension 0 .nil empty)
              (by intro next impossible; cases impossible)

theorem ReadyState.return_let {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer body environment nextEnvironment : Nat) (q : Quan) (heap : Heap)
    (rest : List BendClosureMachine.Frame)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .lett q body environment :: rest)
    (copied : q = .Q2 → state.data[pointer]?.getD false = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.environment pointer environment) = .ok (nextEnvironment,heap)) :
    ∃ nextSource, ReadyState book library.program (step limits library state) nextSource ∧ Eval book source nextSource := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | returned pointerReady value =>
        rw [stackShape] at stack
        cases stack with
        | cons frame tail =>
          cases frame with
          | lett bodyCode captured live =>
            have extension := allocate_extends allocated
            have newCaptured := allocate_environment_ready pointerReady captured allocated
            have certified := cache.allocate false allocated (by intro impossible; cases impossible)
            have sourceStep := (return_let_source limits library state pointer body environment nextEnvironment q heap rest
              _ _ _ _ control stackShape pointerReady.denotes value bodyCode captured.denotes live copied cache (RetainedStack.denotes tail) allocated).2.2.1
            refine ⟨_,?_,sourceStep⟩
            rw [step_return_let limits library state pointer body environment nextEnvironment q heap rest control stackShape copied allocated]
            exact ReadyState.exact (.basic (.evaluate bodyCode newCaptured)) (RetainedStack.extends extension tail) certified
              (extension 0 .nil empty) (by intro next impossible; cases impossible)

theorem ReadyState.return_known_live {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (function argument : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned function)
    (stackShape : state.stack = .knownArgument q argument :: rest)
    (live : q.live = true) (room : rest.length < limits.frames) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | returned functionReady value =>
        rw [stackShape] at stack
        cases stack with
        | cons frame tail =>
          cases frame with
          | knownArgument argumentReady =>
            cases argumentReady with
            | closure row code captured =>
              rw [step_known_closure limits library state function argument _ _ q rest control stackShape live room row]
              exact ReadyState.exact (contexts := .argument q _ value live :: _) (.basic (.evaluate code captured))
                (.cons (.argument functionReady value live) tail) cache empty (by intro next impossible; cases impossible)
            | pair row first second argumentValue =>
              rw [step_known_pair limits library state function argument _ _ q _ rest control stackShape live room row]
              exact ReadyState.exact (contexts := .argument q _ value live :: _)
                (.basic (.returned (.pair row first second argumentValue) argumentValue))
                (.cons (.argument functionReady value live) tail) cache empty (by intro next impossible; cases impossible)
            | application row left right argumentValue =>
              rw [step_known_application limits library state function argument _ _ q _ rest control stackShape live room row]
              exact ReadyState.exact (contexts := .argument q _ value live :: _)
                (.basic (.returned (.application row left right argumentValue) argumentValue))
                (.cons (.argument functionReady value live) tail) cache empty (by intro next impossible; cases impossible)

#assert_axioms ReadyState.return_second
#assert_axioms ReadyState.return_function_dead
#assert_axioms ReadyState.return_let
#assert_axioms ReadyState.return_known_live
end Minidregg.Theory.BendClosureSimulation
