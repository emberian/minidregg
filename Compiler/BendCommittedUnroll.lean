import Compiler.BendCommittedRunSound

/- Whole-run arithmetic receiving: both committed success and every actual
unrolled controller tick follow from ONE arbitrary satisfying field row. Input
identity is explicit and independent; the public wire-range premises concern
the actual checked structural embedding, not secret execution semantics. -/
namespace Minidregg.Compiler.BendCommittedUnroll
open ObliviousNetwork ObliviousUnroll BendTraceConstraints BendCommittedRun
set_option autoImplicit false

theorem accepted_run {F : Type} [Field F]
    (original : Network) (ticks : Nat) (commitment : Network)
    (valid : original.valid = true) (width : original.outputs.size = original.inputCount + 1)
    (prepared : BendCommittedNetwork.Prepared (build original ticks).network commitment)
    (commitmentValid : Nat) (remainingPins : List Nat)
    (wholeValid : (requireBoth prepared.candidate.whole
      (prepared.candidate.execution.wire (build original ticks).network.inputCount
        (build original ticks).handledWire) commitmentValid).valid = true)
    (inputs : Array Bool) (shape : inputs.size = original.inputCount)
    (assignment publicInputs : Nat → F) (publicSuccess : publicInputs 0 = 1)
    (inputBounds : ∀ index < original.inputCount,
      prepared.candidate.execution.wire (build original ticks).network.inputCount index <
        prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size + 1)
    (inputPinned : ∀ index < original.inputCount,
      assignment (prepared.candidate.execution.wire (build original ticks).network.inputCount index) =
        bit (F := F) (inputs[index]?.getD false))
    (accepted : (BendTraceDirect.lower
      (constraints (requireBoth prepared.candidate.whole
        (prepared.candidate.execution.wire (build original ticks).network.inputCount
          (build original ticks).handledWire) commitmentValid))
      (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size + 1)
      ((prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) :: remainingPins)).Holds
      assignment publicInputs) :
    ∃ wholeWires : Nat → Bool,
      AcceptedRun original ticks inputs
        (stateValues (fun i => wholeWires (prepared.candidate.execution.wire
          (build original ticks).network.inputCount i)) (build original ticks)) ∧
      BooleanGraph commitment (fun i => wholeWires
        (prepared.candidate.commitment.wire commitment.inputCount i)) ∧
      wholeWires commitmentValid = true := by
  let executionHandled := prepared.candidate.execution.wire (build original ticks).network.inputCount
    (build original ticks).handledWire
  let network := requireBoth prepared.candidate.whole executionHandled commitmentValid
  have fieldRelation := BendTraceDirect.network_forces network
    ((prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) :: remainingPins)
    assignment publicInputs (by simpa [network, requireBoth, executionHandled, Nat.add_assoc] using accepted)
  obtain ⟨wires, graph, same⟩ := BendTraceSound.holds_extract network wholeValid assignment fieldRelation.1
  have pinned : assignment (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) = 1 := by
    have member : (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size, 0) ∈
        ((prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) :: remainingPins).zipIdx := by simp
    exact (fieldRelation.2 _ member).trans publicSuccess
  have success : wires (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) = true := by
    apply (bit_injective (F := F) _ true).mp
    rw [same _ (by simp [network, requireBoth])]
    exact pinned
  have both := requireBoth_success prepared.candidate.whole executionHandled commitmentValid wires graph success
  have embedded := prepared.restricts wires both.1
  let localWires := fun i => wires (prepared.candidate.execution.wire (build original ticks).network.inputCount i)
  have initial : (Array.range original.inputCount).map localWires = inputs := by
    apply Array.ext
    · simp [shape]
    · intro index leftBound rightBound
      have bounded : index < original.inputCount := by simpa using leftBound
      have atIndex : localWires index = inputs[index]?.getD false := by
        apply (bit_injective (F := F) _ _).mp
        have bound := inputBounds index bounded
        exact (same _ (by simpa [network, requireBoth, Nat.add_assoc] using bound)).trans
          (inputPinned index bounded)
      simpa [Array.getElem?_eq_getElem rightBound] using atIndex
  have run := build_success original ticks valid width localWires embedded.1 both.2.1
  rw [initial] at run
  exact ⟨wires, run, embedded.2, both.2.2⟩

#assert_axioms accepted_run
end Minidregg.Compiler.BendCommittedUnroll
