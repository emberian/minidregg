import Compiler.BendTraceEvaluation

/- Arbitrary arithmetic witnesses, not just supplied Boolean witnesses, force
the actual shared DAG's output. Concrete PCS verification implies the IR2
relation only after its separate cryptographic soundness qualification. -/
namespace Minidregg.Compiler.BendTraceSound
open ObliviousNetwork BendTraceConstraints BendTraceEvaluation
set_option autoImplicit false
variable {F : Type} [Field F]

private theorem opExpr_congr (op : Op) (bound : Nat) (fits : op.fits bound = true)
    (left right : Nat → F) (same : ∀ index < bound, left index = right index) :
    eval left (opExpr op) = eval right (opExpr op) := by
  rw [← eval_agrees_exec, ← eval_agrees_exec]
  cases op with
  | constant value => rfl
  | xor a b =>
    have bounds : a < bound ∧ b < bound := by simpa [Op.fits] using fits
    simp [opExpr, evalExec, add', mul', vr, cst, same a bounds.1, same b bounds.2]
  | and a b =>
    have bounds : a < bound ∧ b < bound := by simpa [Op.fits] using fits
    simp [opExpr, evalExec, mul', vr, same a bounds.1, same b bounds.2]

/-- Every field witness satisfying the actual arithmetic graph has a Boolean
reading at ALL finite wires, and that reading obeys every shared DAG operation.
Nothing assumes that an adversary supplied honest Boolean intermediates. -/
theorem holds_extract (network : Network) (valid : network.valid = true)
    (assignment : Nat → F) (accepted : Holds network assignment) :
    ∃ wires : Nat → Bool, BooleanGraph network wires ∧
      ∀ index < network.inputCount + network.gates.size,
        bit (F := F) (wires index) = assignment index := by
  classical
  let wires : Nat → Bool := fun index => decide (assignment index = 1)
  have same : ∀ index < network.inputCount + network.gates.size,
      bit (F := F) (wires index) = assignment index := by
    intro index bounded
    rcases accepted.1 index bounded with zero | one
    · simp [wires, bit, zero]
    · simp [wires, bit, one]
  have gateFits : ∀ row ∈ network.gates.toList.zipIdx,
      row.1.fits (network.inputCount + row.2) = true := by
    have parts := valid
    simp only [Network.valid, Bool.and_eq_true] at parts
    simpa only [List.all_eq_true] using parts.1
  refine ⟨wires, ?_, same⟩
  intro row member
  have indexed : network.gates.toList[row.2]? = some row.1 :=
    List.mk_mem_zipIdx_iff_getElem?.mp member
  have indexBound : row.2 < network.gates.size := by
    simpa only [Array.length_toList] using (List.getElem?_eq_some_iff.mp indexed).1
  have outputBound : network.inputCount + row.2 < network.inputCount + network.gates.size := by omega
  have expression := opExpr_congr row.1 (network.inputCount + row.2) (gateFits row member)
    assignment (fun i => bit (F := F) (wires i)) (by
      intro index bounded
      exact (same index (by omega)).symm)
  apply (bit_injective (F := F) _ _).mp
  calc
    bit (F := F) (wires (network.inputCount + row.2)) = assignment (network.inputCount + row.2) :=
      same _ outputBound
    _ = eval assignment (opExpr row.1) := accepted.2 row member
    _ = eval (fun i => bit (F := F) (wires i)) (opExpr row.1) := expression
    _ = bit (F := F) (opValue wires row.1) := opExpr_correct wires row.1

/-- Complete arithmetic-row-to-actual-network direction. The input boundary
is independently pinned; result wires and public field pins are forced by the
accepted relation rather than copied from a proof-carried output label. -/
theorem ir2_evaluates (network : Network) (valid : network.valid = true)
    (inputs : Array Bool) (shape : inputs.size = network.inputCount)
    (publicCount : Nat) (assignment publicInputs : Nat → F)
    (accepted : (BendTraceIR2.lower (descriptor network publicCount)).Holds assignment publicInputs)
    (inputPinned : ∀ index < network.inputCount,
      assignment index = bit (F := F) (inputs[index]?.getD false)) :
    ∃ wires : Nat → Bool,
      (∀ index < network.inputCount + network.gates.size,
        bit (F := F) (wires index) = assignment index) ∧
      network.evaluate inputs = some (network.outputs.map wires) ∧
      (∀ index < publicCount, assignment index = publicInputs index) := by
  have relation := ir2_forces network publicCount assignment publicInputs accepted
  obtain ⟨wires, graph, same⟩ := holds_extract network valid assignment relation.1
  refine ⟨wires, same, evaluate_forced network inputs valid shape wires graph ?_, relation.2⟩
  intro index bounded
  apply (bit_injective (F := F) _ _).mp
  exact (inputPinned index bounded).symm.trans (same index (by omega)).symm

#assert_axioms holds_extract
#assert_axioms ir2_evaluates
end Minidregg.Compiler.BendTraceSound
