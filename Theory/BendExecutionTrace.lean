import Theory.BendLiveMachine

/- General endpoint facts for the exact pinned source trace. These theorems do
not assert a byte decoder, heap refinement, circuit, or proof-system verifier. -/
namespace Minidregg.Theory.BendExecutionTrace
open BendTT BendLiveMachine
set_option autoImplicit false

variable {book : Book} {first middle last ty : Term} {count tail : Nat}

theorem append (left : Trace book count first middle)
    (right : Trace book tail middle last) :
    Trace book (count + tail) first last := by
  induction left with
  | refl => simpa using right
  | step transition rest ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.step transition (ih right)

theorem parallel (closed : Book.Closed book) (trace : Trace book count first last) :
    Pars book first last := by
  induction trace with
  | refl => exact .refl
  | step transition rest ih => exact pars_trans (eval_pars closed transition) ih

theorem typed (wellTyped : Book.WellTyped book) (closed : Book.Closed book)
    (initial : Typed book [] first ty) (trace : Trace book count first last) :
    Typed book [] last ty := pars_sr wellTyped initial (parallel closed trace)

theorem closed_live (live : Book.Live book) (initialClosed : Term.Closed first)
    (initialLive : Term.Live book first) (trace : Trace book count first last) :
    Term.Closed last ∧ Term.Live book last := by
  revert initialClosed initialLive
  induction trace with
  | refl => exact fun hc hl => ⟨hc, hl⟩
  | step transition rest ih =>
    intro hc hl
    have next := eval_decreases live hc hl transition
    exact ih next.1 next.2.1

/-- A completed execution must end in a value. Padded states must preserve that
value; a refusal is deliberately not a constructor of this acceptance relation. -/
structure Completed (book : Book) (initial result : Term) where
  steps : Nat
  trace : Trace book steps initial result
  value : Value book result

theorem complete_typed (wellTyped : Book.WellTyped book) (closed : Book.Closed book)
    (initial : Typed book [] first ty) (completed : Completed book first last) :
    Typed book [] last ty := typed wellTyped closed initial completed.trace

theorem value_cannot_step (value : Value book last) : ¬ Eval book last middle :=
  fun transition => eval_value transition value

/-- The upstream theorems imply existence of a finite source trace to a value
for every closed/live typed invocation. This is not an implementation bound:
no numeric capacity or classifier completeness is inferred from accessibility. -/
theorem source_completion (wellTyped : Book.WellTyped book) (live : Book.Live book)
    (initialClosed : Term.Closed first) (initialLive : Term.Live book first)
    (initialTyped : Typed book [] first ty) :
    ∃ result count, Trace book count first result ∧ Value book result := by
  have terminate := halts book first live initialClosed initialLive
  have reach : ∀ term, Acc (fun next current => Eval book current next) term →
      Typed book [] term ty →
      ∃ result count, Trace book count term result ∧ Value book result := by
    intro term accessible
    induction accessible with
    | intro term smaller ih =>
      intro typedTerm
      rcases progress book term ty wellTyped live typedTerm with value | ⟨next, transition⟩
      · exact ⟨term, 0, .refl term, value⟩
      · have nextTyped := pars_sr wellTyped typedTerm (eval_pars live.1 transition)
        obtain ⟨result, count, trace, value⟩ := ih next transition nextTyped
        exact ⟨result, count + 1, .step transition trace, value⟩
  exact reach first terminate initialTyped

#assert_axioms source_completion

#assert_axioms append
#assert_axioms parallel
#assert_axioms typed
#assert_axioms closed_live
#assert_axioms complete_typed
#assert_axioms value_cannot_step
end Minidregg.Theory.BendExecutionTrace
