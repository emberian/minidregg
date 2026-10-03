/- Whole readiness preservation for compound evaluator entry. The actual
source children are recovered from the certified ROM, not supplied by a caller. -/
import Theory.BendClosureReadyEvaluation
import Theory.BendClosureCodeCases

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.application {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment function argument : Nat) (q : Quan)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.app q function argument))
    (room : state.stack.length < limits.frames) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceExact captured =>
        obtain ⟨f,x,same,functionCode,argumentCode⟩ := sourceExact.application_fields q function argument found
        cases same
        rw [step_application limits library state pc environment function argument q control found room]
        exact ReadyState.exact (.basic (.evaluate functionCode captured))
          (.cons (.function argumentCode captured) stack) cache empty
          (by intro result impossible; cases impossible)

theorem ReadyState.live_let {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment value body : Nat) (q : Quan)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.lett q value body))
    (live : q.live = true) (room : state.stack.length < limits.frames) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceExact captured =>
        obtain ⟨v,f,same,valueCode,bodyCode⟩ := sourceExact.let_fields q value body found
        cases same
        rw [step_live_let limits library state pc environment value body q control found live room]
        exact ReadyState.exact (.basic (.evaluate valueCode captured))
          (.cons (.lett bodyCode captured live) stack) cache empty
          (by intro result impossible; cases impossible)

theorem ReadyState.live_pair {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment first second : Nat) (q : Quan)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.tup q first second))
    (live : q.live = true) (room : state.stack.length < limits.frames) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceExact captured =>
        obtain ⟨a,b,same,firstCode,secondCode⟩ := sourceExact.pair_fields q first second found
        cases same
        rw [step_live_pair limits library state pc environment first second q control found live room]
        exact ReadyState.exact (.basic (.evaluate firstCode captured))
          (.cons (.first secondCode captured live) stack) cache empty
          (by intro result impossible; cases impossible)

theorem ReadyState.rewrite {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment evidence motive body : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.rwt evidence motive body))
    (room : state.stack.length < limits.frames) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceExact captured =>
        obtain ⟨e,p,f,same,evidenceCode,motiveCode,bodyCode⟩ := sourceExact.rewrite_fields evidence motive body found
        cases same
        rw [step_rewrite limits library state pc environment evidence motive body control found room]
        exact ReadyState.exact (.basic (.evaluate evidenceCode captured))
          (.cons (.rewrite bodyCode captured) stack) cache empty
          (by intro result impossible; cases impossible)

theorem ReadyState.annotation {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment value type : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.ann value type)) :
    ∃ nextSource, ReadyState book library.program (step limits library state) nextSource ∧
      Eval book source nextSource := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceExact captured =>
        obtain ⟨x,t,same,valueCode,typeCode⟩ := sourceExact.annotation_fields value type found
        cases same
        refine ⟨_,?_,plug_eval _ .ann⟩
        rw [step_annotation limits library state pc environment value type control found]
        exact ReadyState.exact (.basic (.evaluate valueCode captured)) stack cache empty
          (by intro result impossible; cases impossible)

#assert_axioms ReadyState.application
#assert_axioms ReadyState.live_let
#assert_axioms ReadyState.live_pair
#assert_axioms ReadyState.rewrite
#assert_axioms ReadyState.annotation
end Minidregg.Theory.BendClosureSimulation
