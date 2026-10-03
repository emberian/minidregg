/- Actual continuation transitions derive future readiness from the prestate
and the runtime stack. These are preservation theorems, not output oracles. -/
import Theory.BendClosureReadyCapture
import Theory.BendClosureReadyLookup

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.return_empty {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer : Nat) (ready : ReadyState book library.program state source)
    (control : state.control = .returned pointer) (stackShape : state.stack = []) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | returned pointerReady value =>
        rw [stackShape] at stack
        cases stack
        rw [step_return_empty limits library state pointer control stackShape]
        exact ReadyState.exact (.basic (.complete pointerReady value))
          (by rw [stackShape]; exact .nil) cache empty
          (by intro result same; exact stackShape)

theorem ReadyState.return_argument {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer function : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .argument q function :: rest) :
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
          | argument functionReady functionValue live =>
            rw [step_return_argument limits library state pointer function q rest control stackShape]
            exact ReadyState.exact (focus := .App q _ _) (.basic (.apply functionReady pointerReady functionValue (fun _ => value)))
              tail cache empty (by intro result impossible; cases impossible)

theorem ReadyState.return_function_live {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer argument environment : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .function q argument environment :: rest)
    (live : q.live = true) (room : rest.length < limits.frames) :
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
          | function code captured =>
            rw [step_return_function_live limits library state pointer argument environment q rest control stackShape live room]
            exact ReadyState.exact (contexts := .argument q _ value live :: _)
              (.basic (.evaluate code captured)) (.cons (.argument pointerReady value live) tail)
              cache empty (by intro result impossible; cases impossible)

theorem ReadyState.return_first {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer second environment : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .first q second environment :: rest)
    (room : rest.length < limits.frames) :
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
          | first code captured live =>
            rw [step_return_first limits library state pointer second environment q rest control stackShape room]
            exact ReadyState.exact (contexts := .second q _ (fun _ => value) :: _)
              (.basic (.evaluate code captured)) (.cons (.second pointerReady (fun _ => value)) tail)
              cache empty (by intro result impossible; cases impossible)

theorem ReadyState.return_known_dead {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (function argument : Nat) (rest : List BendClosureMachine.Frame)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned function)
    (stackShape : state.stack = .knownArgument .Q0 argument :: rest) :
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
          | knownArgument argumentReady =>
            rw [step_known_dead limits library state function argument rest control stackShape]
            exact ReadyState.exact (focus := .App .Q0 _ _) (.basic (.apply (q := .Q0) pointerReady argumentReady value (by intro h; cases h)))
              tail cache empty (by intro result impossible; cases impossible)

theorem ReadyState.complete {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer : Nat) (ready : ReadyState book library.program state source)
    (control : state.control = .complete pointer) :
    ReadyState book library.program (step limits library state) source := by
  simpa only [step, control] using ready

#assert_axioms ReadyState.return_empty
#assert_axioms ReadyState.return_argument
#assert_axioms ReadyState.return_function_live
#assert_axioms ReadyState.return_first
#assert_axioms ReadyState.return_known_dead
#assert_axioms ReadyState.complete
end Minidregg.Theory.BendClosureSimulation
