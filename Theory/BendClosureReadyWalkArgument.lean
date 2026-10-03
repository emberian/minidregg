/- Actual case-argument lookup preserves its original call and recursively
ready captured environment; source Env.sub handles the exact Q0 slot positions. -/
import Theory.BendClosureReadyNamedCall
import Theory.BendClosureWalkArgument

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.walk_argument_zero {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (cursor pointer tail function environment original : Nat) (q : Quan) (args : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .lookup 0 cursor (.walkArgument q function environment original args))
    (found : state.heap.get? cursor = some (.environment pointer tail))
    (room : ((q,pointer) :: args).length ≤ limits.arguments) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | lookupWalk code captured cursorReady originalReady argsReady walkPrefix =>
      cases cursorReady with
      | nil other => rw [found] at other; cases other
      | cons other head tailReady =>
        rw [found] at other
        cases other
        rw [step_walk_argument_zero limits library state cursor pointer tail function environment original q args control found room]
        exact ReadyState.exact (.walk code captured originalReady (.cons ⟨rfl,head⟩ argsReady) walkPrefix)
          stack cache empty (by intro result impossible; cases impossible)

theorem ReadyState.walk_argument_successor {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (index cursor pointer tail function environment original : Nat) (q : Quan) (args : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .lookup (index+1) cursor (.walkArgument q function environment original args))
    (found : state.heap.get? cursor = some (.environment pointer tail)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | lookupWalk code captured cursorReady originalReady argsReady walkPrefix =>
      cases cursorReady with
      | nil other => rw [found] at other; cases other
      | cons other head tailReady =>
        rw [found] at other
        cases other
        rw [step_lookup_succ limits library state index cursor pointer tail (.walkArgument q function environment original args) control found]
        exact ReadyState.exact (.lookupWalk code captured tailReady originalReady argsReady walkPrefix)
          stack cache empty (by intro result impossible; cases impossible)

#assert_axioms ReadyState.walk_argument_zero
#assert_axioms ReadyState.walk_argument_successor
end Minidregg.Theory.BendClosureSimulation
