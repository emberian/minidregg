/- Live equality evidence is checked against the actual closure/ROM before
committing the source cast; it is not erased from the operational argument. -/
import Theory.BendClosureReadyReturnAlloc

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.return_rewrite {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer pc evidenceEnvironment body environment : Nat)
    (rest : List BendClosureMachine.Frame)
    (ready : ReadyState book library.program state source)
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .rewrite body environment :: rest)
    (evidenceRow : state.heap.get? pointer = some (.closure pc evidenceEnvironment))
    (instruction : library.program.code[pc]? = some .rfl) :
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
        | @cons _ _ _ contexts frame tail =>
          cases frame with
          | rewrite bodyCode captured =>
            cases pointerReady with
            | pair other first second pairValue => rw [evidenceRow] at other; cases other
            | application other function argument appValue => rw [evidenceRow] at other; cases other
            | closure other evidenceCode evidenceCaptured =>
              rw [evidenceRow] at other
              cases other
              have same := CodeDenotes.functional evidenceCode (.rfl instruction)
              cases same
              refine ⟨_,?_,plug_eval contexts .cast⟩
              rw [step_return_rewrite limits library state pointer pc evidenceEnvironment body environment rest
                control stackShape evidenceRow instruction]
              exact ReadyState.exact (.basic (.evaluate bodyCode captured)) tail cache empty
                (by intro result impossible; cases impossible)

#assert_axioms ReadyState.return_rewrite
end Minidregg.Theory.BendClosureSimulation
