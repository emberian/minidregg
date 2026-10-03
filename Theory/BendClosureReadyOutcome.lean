/- Guard-free preservation/refusal for complete administrative control families.
The disjunction is about the literal Machine.step output. No selected branch,
future readiness, source equality, or Covered witness is accepted as input. -/
import Theory.BendClosureReadyClassifier
import Theory.BendClosureReadyAdministrative

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

def AdministrativeOutcome (book : Book) (limits : Limits) (library : Library) (state : State) (source : Term) : Prop :=
  ReadyState book library.program (step limits library state) source ∨
    ∃ reason, step limits library state = {state with control := .refused reason}

theorem ReadyState.lookup_value_outcome {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (index environment : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .lookup index environment .evaluateValue) :
    AdministrativeOutcome book limits library state source := by
  have prior := ready
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | lookupValue captured =>
      cases captured with
      | nil found =>
        right
        refine ⟨.unbound,?_⟩
        simp [step,control,lookup,row,found]
        rfl
      | cons found head tail =>
        cases index with
        | zero => exact .inl (prior.lookup_zero limits library state _ environment _ _ control found)
        | succ index => exact .inl (prior.lookup_successor limits library state _ index environment _ _ control found)

theorem ReadyState.lookup_walk_outcome {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (index cursor function environment original : Nat) (q : Quan) (args : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .lookup index cursor (.walkArgument q function environment original args)) :
    AdministrativeOutcome book limits library state source := by
  have prior := ready
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | lookupWalk code captured cursorReady originalReady argsReady walkPrefix =>
      cases cursorReady with
      | nil found =>
        right
        refine ⟨.unbound,?_⟩
        simp [step,control,lookup,row,found]
        rfl
      | @cons _ pointer tail _ _ found head tailReady =>
        cases index with
        | zero =>
          by_cases room : ((q,pointer) :: args).length ≤ limits.arguments
          · exact .inl (prior.walk_argument_zero limits library state _ cursor pointer tail function environment original q args control found room)
          · right
            refine ⟨.argumentCapacity,?_⟩
            have bounded : boundedArgsFn limits ((q,pointer) :: args) = (throw Failure.argumentCapacity : Work Unit) := by
              change (if ((q,pointer) :: args).length ≤ limits.arguments then (pure () : Work Unit)
                else throw Failure.argumentCapacity) = _
              rw [if_neg room]
            simp [step,control,lookup,row,found,boundedArgs_eq,bounded]
            rfl
        | succ index =>
          exact .inl (prior.walk_argument_successor limits library state _ index cursor pointer tail function environment original q args control found)

theorem ReadyState.reverse_outcome {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment : Nat) (remaining reversed : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .reverseArguments pc environment remaining reversed) :
    AdministrativeOutcome book limits library state source := by
  cases remaining with
  | nil => exact .inl (ready.reverse_nil limits library state source pc environment reversed control)
  | cons head tail => exact .inl (ready.reverse_cons limits library state source pc environment head tail reversed control)

theorem ReadyState.install_outcome {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment : Nat) (remaining : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .installArguments pc environment remaining) :
    AdministrativeOutcome book limits library state source := by
  cases remaining with
  | nil => exact .inl (ready.install_nil limits library state source pc environment control)
  | cons head tail =>
    rcases head with ⟨q,pointer⟩
    by_cases room : state.stack.length < limits.frames
    · exact .inl (ready.install_cons limits library state source pc environment q pointer tail control room)
    · right
      refine ⟨.continuationCapacity,?_⟩
      simp [step,control,installArguments,push,Nat.le_of_not_gt room]
      rfl

#assert_axioms ReadyState.lookup_value_outcome
#assert_axioms ReadyState.lookup_walk_outcome
#assert_axioms ReadyState.reverse_outcome
#assert_axioms ReadyState.install_outcome
end Minidregg.Theory.BendClosureSimulation
