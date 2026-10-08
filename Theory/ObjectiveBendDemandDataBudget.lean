/- Executable witnesses for remaining budgets, including failed forcing. -/
import Theory.ObjectiveBendDemandData

namespace Minidregg.Theory.ObjectiveBendDemandData
open ObjectiveBendDemandMachine

private def lazyPlan (term : ObjectiveBendOpenRecursion.Term) : State :=
  ⟨#[.suspended ⟨term, []⟩], .yielded 0, []⟩

/-- Exhausting ticks returns the exhausted allowance rather than discarding it. -/
theorem yielded_tick_failure_remaining :
    match yieldedPlan ⟨20, 20⟩ ⟨20, 2, 100⟩ (lazyPlan (.nat 7)) with
    | .error (.tickExhausted, _, remaining) => remaining.ticks = 0
    | _ => False := by change 0 = 0; rfl

/-- Successful forcing reports a nonzero actual spend and unused ticks. -/
theorem yielded_success_remaining :
    match yieldedPlan ⟨20, 20⟩ ⟨20, 10, 100⟩ (lazyPlan (.nat 7)) with
    | .ok result => 0 < result.remaining.ticks ∧ result.remaining.ticks < 10
    | _ => False := by change 0 < 6 ∧ 6 < 10; decide

/-- A semantic failure after forcing still reports the work already consumed. -/
theorem yielded_semantic_failure_remaining :
    match yieldedPlan ⟨20, 20⟩ ⟨20, 10, 100⟩ (lazyPlan (.lam (.nat 7))) with
    | .error (.executableValue, _, remaining) => 0 < remaining.ticks ∧ remaining.ticks < 10
    | _ => False := by change 0 < 6 ∧ 6 < 10; decide

/-- The full-ceiling behavior can consume more ticks than the turn has left. -/
theorem full_ceiling_exceeds_remaining :
    match yieldedPlan ⟨20, 20⟩ ⟨20, 10, 100⟩ (lazyPlan (.nat 7)) with
    | .ok result => 2 < 10 - result.remaining.ticks
    | _ => False := by change 2 < 10 - 6; decide

/-- Policy/capacity suspension is not tick exhaustion: it retains unused ticks. -/
theorem capacity_failure_remaining :
    match yieldedPlanWith (fun _ => false) ⟨20, 20⟩ ⟨20, 10, 100⟩ (lazyPlan (.nat 7)) with
    | .error (.suspended, _, remaining) => remaining.ticks = 10
    | _ => False := by change 10 = 10; rfl

private def resultFields : State :=
  ⟨#[.suspended ⟨.nat 1, []⟩, .suspended ⟨.lam (.nat 7), []⟩],
    .complete (.record [("x", 0), ("y", 1)]), []⟩

/-- A failure in the second result field keeps the spend of both fields. -/
theorem complete_later_failure_remaining :
    match complete ⟨20, 20⟩ ⟨20, 10, 100⟩ resultFields with
    | .error (.executableValue, _, remaining) => remaining.ticks = 2
    | _ => False := by change 2 = 2; rfl

/-- The same result stops forcing when its shared allowance is exhausted. -/
theorem complete_tick_failure_remaining :
    match complete ⟨20, 20⟩ ⟨20, 6, 100⟩ resultFields with
    | .error (.tickExhausted, _, remaining) => remaining.ticks = 0
    | _ => False := by change 0 = 0; rfl

#assert_axioms yielded_tick_failure_remaining yielded_success_remaining yielded_semantic_failure_remaining
#assert_axioms full_ceiling_exceeds_remaining capacity_failure_remaining complete_later_failure_remaining
#assert_axioms complete_tick_failure_remaining

end Minidregg.Theory.ObjectiveBendDemandData
