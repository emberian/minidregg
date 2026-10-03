import Compiler.BendCommittedRun

/- Arithmetic acceptance of the complete shared graph yields both embedded
relations AND the constrained execution/commitment success bits. The first
public input is independently fixed to one; proof-supplied labels cannot
replace either relation. PCS acceptance -> arithmetic acceptance remains a
separate cryptographic theorem, as does actual source/codec/hash refinement. -/
namespace Minidregg.Compiler.BendCommittedRunSound
open ObliviousNetwork BendTraceConstraints BendCommittedRun
set_option autoImplicit false

 theorem direct_forces_both_success {F : Type} [Field F]
    {execution commitment : Network}
    (prepared : BendCommittedNetwork.Prepared execution commitment)
    (executionHandled commitmentValid : Nat) (remainingPins : List Nat)
    (valid : (requireBoth prepared.candidate.whole executionHandled commitmentValid).valid = true)
    (assignment publicInputs : Nat → F) (publicSuccess : publicInputs 0 = 1)
    (accepted : (BendTraceDirect.lower
      (constraints (requireBoth prepared.candidate.whole executionHandled commitmentValid))
      ((requireBoth prepared.candidate.whole executionHandled commitmentValid).inputCount +
        (requireBoth prepared.candidate.whole executionHandled commitmentValid).gates.size)
      ((prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) :: remainingPins)).Holds
        assignment publicInputs) :
    ∃ wires : Nat → Bool,
      BooleanGraph execution
        (fun i => wires (prepared.candidate.execution.wire execution.inputCount i)) ∧
      BooleanGraph commitment
        (fun i => wires (prepared.candidate.commitment.wire commitment.inputCount i)) ∧
      wires executionHandled = true ∧ wires commitmentValid = true := by
  let network := requireBoth prepared.candidate.whole executionHandled commitmentValid
  have forced := BendTraceDirect.network_forces network
    ((prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) :: remainingPins)
    assignment publicInputs accepted
  obtain ⟨wires, graph, same⟩ := BendTraceSound.holds_extract network valid assignment forced.1
  have pinned : assignment (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) = 1 := by
    have member : (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size, 0) ∈
        ((prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) :: remainingPins).zipIdx := by simp
    exact (forced.2 _ member).trans publicSuccess
  have success : wires (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) = true := by
    apply (bit_injective (F := F) _ true).mp
    rw [same _ (by simp [network, requireBoth])]
    exact pinned
  have both := requireBoth_success prepared.candidate.whole executionHandled commitmentValid wires graph success
  have embedded := prepared.restricts wires both.1
  exact ⟨wires, embedded.1, embedded.2, both.2⟩

#assert_axioms direct_forces_both_success
end Minidregg.Compiler.BendCommittedRunSound
