/- Exact source-prefix meaning of actual continuation-capacity refusals.
No failure is rewritten into a source Value or a successful source step. -/
import Theory.BendClosureSupportedRun

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

/-- Precisely the evaluate branches which push before any other heap or
source-step effect. Other refusal branches require their own proofs. -/
def needsFrame : Code → Bool
  | .app .. | .rwt .. => true
  | .lett q .. | .tup q .. => q.live
  | _ => false

theorem step_frame_refusal (limits : Limits) (library : Library) (state : State)
    (pc environment : Nat) (instruction : Code)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some instruction)
    (required : needsFrame instruction = true)
    (full : limits.frames ≤ state.stack.length) :
    step limits library state = {state with control := .refused .continuationCapacity} := by
  cases instruction <;> simp_all [needsFrame, step, evaluate, code, push]
  all_goals rfl

/-- The exact pre-failure reification is retained as ghost evidence.
The actual diagnostic state differs only in control; no source term is forged
from an arbitrary refused heap. -/
def RefusalInvariant (book : Book) (program : Program) (origin : Term)
    (initialCount : Nat) (state : State) : Prop :=
  ∃ reason previous, state = {previous with control := .refused reason} ∧
    SourceInvariant book program origin initialCount previous

theorem RefusalInvariant.source_prefix {book : Book} {program : Program}
    {origin : Term} {initialCount : Nat} {state : State}
    (invariant : RefusalInvariant book program origin initialCount state) :
    ∃ count residual, BendLiveMachine.Trace book count origin residual ∧
      state.sourceSteps = initialCount + count := by
  obtain ⟨reason, previous, same, count, residual, trace, represented, counter⟩ := invariant
  exact ⟨count, residual, trace, by simpa only [same] using counter⟩

theorem covered_run_frame_refusal {book : Book} (limits : Limits) (library : Library)
    (ticks : Nat) (state : State) (origin : Term) (initialCount : Nat)
    (pc environment : Nat) (instruction : Code)
    (initial : SourceInvariant book library.program origin initialCount state)
    (coverage : Covered book limits library ticks state)
    (control : (run limits library ticks state).control = .evaluate pc environment)
    (found : library.program.code[pc]? = some instruction)
    (required : needsFrame instruction = true)
    (full : limits.frames ≤ (run limits library ticks state).stack.length) :
    RefusalInvariant book library.program origin initialCount
      (run limits library (ticks + 1) state) := by
  have prefixExact := initial.run ticks coverage
  have refusal := step_frame_refusal limits library (run limits library ticks state)
    pc environment instruction control found required full
  rw [run_add limits library ticks 1 state]
  exact ⟨.continuationCapacity, run limits library ticks state, refusal, prefixExact⟩

#assert_axioms step_frame_refusal
#assert_axioms RefusalInvariant.source_prefix
#assert_axioms covered_run_frame_refusal
end Minidregg.Theory.BendClosureSimulation
