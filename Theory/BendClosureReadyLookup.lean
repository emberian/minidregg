/- Environment lookup preserves recursive readiness from its prestate alone.
No caller supplies the looked-up value or its captured environment invariant. -/
import Theory.BendClosureReadyEvaluation

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.lookup_zero {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (environment pointer tail : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .lookup 0 environment .evaluateValue)
    (found : state.heap.get? environment = some (.environment pointer tail)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | lookupValue captured =>
      cases captured with
      | nil other => rw [found] at other; cases other
      | cons other head captured =>
        rw [found] at other
        cases other
        cases head with
        | closure row code capturedHead =>
          rw [step_lookup_zero_closure limits library state environment pointer tail _ _ control found row]
          exact ReadyState.exact (.basic (.evaluate code capturedHead)) stack cache empty
            (by intro result impossible; cases impossible)
        | pair row first second value =>
          rw [step_lookup_zero_pair limits library state environment pointer tail _ _ _ control found row]
          exact ReadyState.exact (.basic (.returned (.pair row first second value) value)) stack cache empty
            (by intro result impossible; cases impossible)
        | application row function argument value =>
          rw [step_lookup_zero_application limits library state environment pointer tail _ _ _ control found row]
          exact ReadyState.exact (.basic (.returned (.application row function argument value) value)) stack cache empty
            (by intro result impossible; cases impossible)

theorem ReadyState.lookup_successor {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (index environment pointer tail : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .lookup (index+1) environment .evaluateValue)
    (found : state.heap.get? environment = some (.environment pointer tail)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | lookupValue captured =>
      cases captured with
      | nil other => rw [found] at other; cases other
      | cons other head captured =>
        rw [found] at other
        cases other
        rw [step_lookup_succ limits library state index environment pointer tail .evaluateValue control found]
        exact ReadyState.exact (.lookupValue captured) stack cache empty
          (by intro result impossible; cases impossible)

#assert_axioms ReadyState.lookup_zero
#assert_axioms ReadyState.lookup_successor
end Minidregg.Theory.BendClosureSimulation
