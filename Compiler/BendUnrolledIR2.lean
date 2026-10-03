import Compiler.BendTraceSound
import Compiler.ObliviousUnrollSemantics

/- One IR2 local row constrains the ENTIRE fixed-tick unrolled DAG. No cross-row
transition constraint is assumed from the native local-row backend. Native PCS
soundness and source/controller refinement remain separate explicit joins. -/
namespace Minidregg.Compiler.BendUnrolledIR2
open ObliviousNetwork ObliviousUnroll BendTraceConstraints BendTraceSound
set_option autoImplicit false
variable {F : Type} [Field F]

/-- Arbitrary field witnesses force every raw controller block in sequence.
All handled bits are constrained by the generated cumulative AND, whose output
must be pinned to one by the admitted statement relation. -/
theorem accepted_run (original : Network) (ticks : Nat)
    (valid : original.valid = true) (width : original.outputs.size = original.inputCount + 1)
    (wholeValid : (build original ticks).network.valid = true)
    (inputs : Array Bool) (shape : inputs.size = original.inputCount)
    (publicCount : Nat) (assignment publicInputs : Nat → F)
    (accepted : (BendTraceIR2.lower (descriptor (build original ticks).network publicCount)).Holds
      assignment publicInputs)
    (inputPinned : ∀ index < original.inputCount,
      assignment index = bit (F := F) (inputs[index]?.getD false))
    (handledPinned : assignment (build original ticks).handledWire = 1) :
    ∃ wires : Nat → Bool,
      (∀ index < (build original ticks).network.inputCount + (build original ticks).network.gates.size,
        bit (F := F) (wires index) = assignment index) ∧
      AcceptedRun original ticks inputs (stateValues wires (build original ticks)) ∧
      (∀ index < publicCount, assignment index = publicInputs index) := by
  have relation := ir2_forces (build original ticks).network publicCount assignment publicInputs accepted
  obtain ⟨wires, graph, same⟩ := holds_extract (build original ticks).network wholeValid assignment relation.1
  have outputBounds : ∀ wire ∈ (build original ticks).network.outputs,
      wire < (build original ticks).network.inputCount + (build original ticks).network.gates.size := by
    have parts := wholeValid
    simp only [Network.valid, Bool.and_eq_true] at parts
    simpa only [Array.all_eq_true_iff_forall_mem, decide_eq_true_eq] using parts.2
  have handledBound := outputBounds (build original ticks).handledWire (by simp [build])
  have handled : wires (build original ticks).handledWire = true := by
    apply (bit_injective (F := F) _ _).mp
    simpa [bit] using (same _ handledBound).trans handledPinned
  have pinned : (Array.range original.inputCount).map wires = inputs := by
    apply Array.ext
    · simp [shape]
    · intro index leftBound rightBound
      have bounded : index < original.inputCount := by simpa using leftBound
      have value : wires index = inputs[index]?.getD false := by
        apply (bit_injective (F := F) _ _).mp
        exact (same index (by rw [build_inputCount]; omega)).trans (inputPinned index bounded)
      simpa [Array.getElem?_eq_getElem rightBound] using value
  refine ⟨wires, same, ?_, relation.2⟩
  rw [← pinned]
  exact build_success original ticks valid width wires graph handled

#assert_axioms accepted_run
end Minidregg.Compiler.BendUnrolledIR2
