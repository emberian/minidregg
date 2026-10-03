/- Persistence transports the actual controller source invariant. It does not
prove that arbitrary checkpoint bytes are reachable or admitted, and does not
replace the open whole-controller simulation theorem.
-/
import Compiler.BendClosureContinuationCodec
import Theory.BendClosureSimulation

namespace Minidregg.Assurance.BendContinuationSourceJoin
open Minidregg.Theory
open BendTT BendClosureArena BendClosureMachine BendClosureSimulation
open Minidregg.Compiler.BendClosureContinuationCodec
set_option autoImplicit false

/-- Exact serialization preserves source reification, Data-cache soundness and
source-step count together, not merely the focused term or final output. -/
theorem source_at_restore (checkpoint : Checkpoint) (maximumBytes : Nat)
    (fits : (encode checkpoint).length ≤ maximumBytes)
    (book : Book) (program : Program) (source : Term)
    (represented : StateDenotes book program checkpoint.state source)
    (cache : DataCacheSound program checkpoint.state) :
    ∃ restored, restore maximumBytes checkpoint.contextBytes checkpoint.generation
      (encode checkpoint) = some restored ∧
      StateDenotes book program restored source ∧ DataCacheSound program restored ∧
      restored.sourceSteps = checkpoint.state.sourceSteps :=
  ⟨checkpoint.state, restore_encode checkpoint maximumBytes fits, represented, cache, rfl⟩

/-- When the retained source invariant already proves completion, restoration
retains its exact source value certificate; no execution oracle is consulted. -/
theorem completed_at_restore (checkpoint : Checkpoint) (maximumBytes : Nat)
    (fits : (encode checkpoint).length ≤ maximumBytes)
    (book : Book) (program : Program) (source : Term) (pointer : Nat)
    (represented : StateDenotes book program checkpoint.state source)
    (done : checkpoint.state.control = .complete pointer) :
    ∃ restored, restore maximumBytes checkpoint.contextBytes checkpoint.generation
      (encode checkpoint) = some restored ∧
      Denotes program restored.heap pointer source ∧ Value book source :=
  ⟨checkpoint.state, restore_encode checkpoint maximumBytes fits,
    represented.complete done⟩

#assert_axioms source_at_restore
#assert_axioms completed_at_restore
end Minidregg.Assurance.BendContinuationSourceJoin
