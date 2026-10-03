import Compiler.BendTraceConstraints

/- Arbitrary satisfying DAG witnesses agree with the existing shared network
interpreter. This is not a second evaluator or a Bend controller refinement. -/
namespace Minidregg.Compiler.BendTraceEvaluation
open ObliviousNetwork BendTraceConstraints
set_option autoImplicit false

private theorem op_congr (op : Op) (left right : Nat → Bool) (bound : Nat)
    (fits : op.fits bound = true) (same : ∀ i < bound, left i = right i) :
    opValue left op = opValue right op := by
  cases op with
  | constant value => rfl
  | xor a b =>
    have h : a < bound ∧ b < bound := by simpa [Op.fits] using fits
    simp only [opValue, same a h.1, same b h.2]
  | and a b =>
    have h : a < bound ∧ b < bound := by simpa [Op.fits] using fits
    simp only [opValue, same a h.1, same b h.2]

/-- EVERY satisfying Boolean graph agrees at every finite wire with the actual
fold used by Network.evaluate, when original inputs and valid references agree. -/
theorem evaluateWires_forced (network : Network) (inputs : Array Bool)
    (valid : network.valid = true) (shape : inputs.size = network.inputCount)
    (witness : Nat → Bool) (graph : BooleanGraph network witness)
    (pinned : ∀ i < network.inputCount, inputs[i]?.getD false = witness i) :
    (network.evaluateWires inputs).size = network.inputCount + network.gates.size ∧
    ∀ i < network.inputCount + network.gates.size,
      (network.evaluateWires inputs)[i]?.getD false = witness i := by
  have validParts :
      (network.gates.toList.zipIdx).all
        (fun row => row.1.fits (network.inputCount + row.2)) = true ∧
      network.outputs.all (· < network.inputCount + network.gates.size) = true := by
    simpa only [Network.valid, Bool.and_eq_true] using valid
  have fits : ∀ row ∈ network.gates.toList.zipIdx,
      row.1.fits (network.inputCount + row.2) = true := by
    simpa only [List.all_eq_true] using validParts.1
  unfold Network.evaluateWires
  apply Array.foldl_induction
    (motive := fun count wires => wires.size = network.inputCount + count ∧
      ∀ i < network.inputCount + count, wires[i]?.getD false = witness i)
  · exact ⟨by simpa using shape, by simpa using pinned⟩
  · intro index wires invariant
    have member : (network.gates[index], index.val) ∈ network.gates.toList.zipIdx := by
      apply List.mk_mem_zipIdx_iff_getElem?.mpr
      simp
    have sameOp := op_congr (network.gates[index])
      (fun i => wires[i]?.getD false) witness (network.inputCount + index.val)
      (fits _ member) invariant.2
    have equation :
        (match network.gates[index] with
          | .constant value => value
          | .xor a b => xor (wires[a]?.getD false) (wires[b]?.getD false)
          | .and a b => wires[a]?.getD false && wires[b]?.getD false) =
        witness (network.inputCount + index.val) := by
      simpa only [opValue] using sameOp.trans (graph _ member).symm
    constructor
    · simp only [Array.size_push, invariant.1]
      omega
    · intro i hi
      by_cases last : i = wires.size
      · simp only [Array.getElem?_push, last, if_pos, Option.getD_some]
        rw [equation, ← invariant.1, ← last]
      · have earlier : i < network.inputCount + index.val := by omega
        simpa only [Array.getElem?_push, last, if_false] using invariant.2 i earlier

#assert_axioms evaluateWires_forced
end Minidregg.Compiler.BendTraceEvaluation
