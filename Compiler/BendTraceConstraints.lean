import Compiler.ObliviousNetwork
import Compiler.BendTraceIR2
import Theory.AssertAxioms

/- The same constant/XOR/AND DAG used by the oblivious backend is lowered to
Lean's existing arithmetic DSL. This file does not invent a Bend controller.
A future source refinement must connect the actual closure controller to Eval.
All wire assignments below are arbitrary, not just the generated witness. -/
namespace Minidregg.Compiler.BendTraceConstraints
open ObliviousNetwork
set_option autoImplicit false
variable {F : Type} [Field F]

abbrev Expr (F : Type) := Term (AirSig F Nat)

def bit (value : Bool) : F := if value then 1 else 0

def opValue (wires : Nat → Bool) : Op → Bool
  | .constant value => value
  | .xor left right => xor (wires left) (wires right)
  | .and left right => wires left && wires right

/-- Algebraic reading of the actual DAG operation. XOR = a+b-2ab is valid in
any field, including characteristic two, for Boolean operands. -/
def opExpr : Op → Expr F
  | .constant value => cst (bit value)
  | .xor left right => add' (add' (vr left) (vr right))
      (mul' (cst (-2)) (mul' (vr left) (vr right)))
  | .and left right => mul' (vr left) (vr right)

def gateConstraint (output : Nat) (op : Op) : Expr F :=
  add' (vr output) (mul' (cst (-1)) (opExpr op))

theorem opExpr_correct (wires : Nat → Bool) (op : Op) :
    eval (fun i => bit (F := F) (wires i)) (opExpr op) = bit (opValue wires op) := by
  rw [← eval_agrees_exec]
  cases op with
  | constant value => rfl
  | xor left right =>
    cases hl : wires left <;> cases hr : wires right <;>
      norm_num [opExpr, opValue, evalExec, add', mul', vr, cst, bit, hl, hr]
  | and left right =>
    cases hl : wires left <;> cases hr : wires right <;>
      norm_num [opExpr, opValue, evalExec, add', mul', vr, cst, bit, hl, hr]

theorem gateConstraint_correct (assignment : Nat → F) (output : Nat) (op : Op) :
    accepts assignment (gateConstraint output op) ↔
      assignment output = eval assignment (opExpr op) := by
  rw [accepts_iff_semHolds]
  change assignment output + (-1) * evalExec assignment (opExpr op) = 0 ↔ _
  rw [eval_agrees_exec]
  simp only [neg_one_mul, ← sub_eq_add_neg, sub_eq_zero]

theorem gateConstraint_bits (wires : Nat → Bool) (output : Nat) (op : Op) :
    accepts (fun i => bit (F := F) (wires i)) (gateConstraint output op) ↔
      bit (F := F) (wires output) = bit (F := F) (opValue wires op) := by
  rw [gateConstraint_correct, opExpr_correct]

/-- One Booleanity constraint per wire, followed by constraints generated from
all DAG gates. Intermediate output i is exactly inputCount+i. -/
def constraints (network : Network) : ConstraintSystem F Nat :=
  (List.range (network.inputCount + network.gates.size)).map boolGadget ++
  (network.gates.toList.zipIdx.map fun row =>
    gateConstraint (network.inputCount + row.2) row.1)

/-- Arithmetic relation over arbitrary wires. Original input/public boundary
pinning belongs to the invocation statement, not to a witness generator. -/
def Holds (network : Network) (assignment : Nat → F) : Prop :=
  (∀ i < network.inputCount + network.gates.size, assignment i = 0 ∨ assignment i = 1) ∧
  ∀ row ∈ network.gates.toList.zipIdx,
    assignment (network.inputCount + row.2) = eval assignment (opExpr row.1)

theorem constraints_correct (network : Network) (assignment : Nat → F) :
    systemAccepts assignment (constraints network) ↔ Holds network assignment := by
  simp only [constraints, systemAccepts, List.forall_mem_append, List.forall_mem_map]
  simp [Holds, boolGadget_correct, gateConstraint_correct]

/-- The graph relation is over exactly the shared DAG's operation values. -/
def BooleanGraph (network : Network) (wires : Nat → Bool) : Prop :=
  ∀ row ∈ network.gates.toList.zipIdx,
    wires (network.inputCount + row.2) = opValue wires row.1

theorem bit_injective (left right : Bool) :
    bit (F := F) left = bit (F := F) right ↔ left = right := by
  cases left <;> cases right <;> simp [bit]

theorem bit_boolean (value : Bool) :
    bit (F := F) value = 0 ∨ bit (F := F) value = 1 := by
  cases value <;> simp [bit]

/-- Every Boolean wire assignment, including adversarial intermediate values,
satisfies the emitted system exactly when every actual DAG operation holds.
The next refinement proves forced graph wires equal Network.evaluate after
pinning inputs and checking the network's backward-only references. -/
theorem constraints_bits_iff (network : Network) (wires : Nat → Bool) :
    systemAccepts (fun i => bit (F := F) (wires i)) (constraints network) ↔
      BooleanGraph network wires := by
  rw [constraints_correct]
  constructor
  · intro satisfied row member
    have equation := satisfied.2 row member
    rw [opExpr_correct] at equation
    exact (bit_injective _ _).mp equation
  · intro graph
    refine ⟨fun i _ => bit_boolean (wires i), ?_⟩
    intro row member
    rw [opExpr_correct]
    change bit (F := F) (wires (network.inputCount + row.2)) = _
    rw [graph row member]

private theorem opValue_congr {left right : Nat → Bool} {bound : Nat} (op : Op)
    (fits : op.fits bound = true) (same : ∀ i < bound, left i = right i) :
    opValue left op = opValue right op := by
  cases op with
  | constant value => rfl
  | xor a b =>
    have bounds : a < bound ∧ b < bound := by simpa [Op.fits] using fits
    simp only [opValue, same a bounds.1, same b bounds.2]
  | and a b =>
    have bounds : a < bound ∧ b < bound := by simpa [Op.fits] using fits
    simp only [opValue, same a bounds.1, same b bounds.2]

/-- Backward-only SSA references and pinned inputs force ALL circuit wires.
This applies to arbitrary witnesses, not an honest-witness sample. -/
theorem graph_unique (network : Network) (valid : network.valid = true)
    (left right : Nat → Bool) (leftGraph : BooleanGraph network left)
    (rightGraph : BooleanGraph network right)
    (inputs : ∀ i < network.inputCount, left i = right i) :
    ∀ i < network.inputCount + network.gates.size, left i = right i := by
  have validParts :
      (network.gates.toList.zipIdx).all
        (fun row => row.1.fits (network.inputCount + row.2)) = true ∧
      network.outputs.all (· < network.inputCount + network.gates.size) = true := by
    simpa only [Network.valid, Bool.and_eq_true] using valid
  have gateFits : ∀ row ∈ network.gates.toList.zipIdx,
      row.1.fits (network.inputCount + row.2) = true := by
    simpa only [List.all_eq_true] using validParts.1
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro inRange
    by_cases original : i < network.inputCount
    · exact inputs i original
    · let index := i - network.inputCount
      have indexBound : index < network.gates.toList.length := by
        simp only [Array.length_toList]
        omega
      let op := network.gates.toList[index]
      have member : (op, index) ∈ network.gates.toList.zipIdx := by
        apply List.mk_mem_zipIdx_iff_getElem?.mpr
        simp [op, indexBound]
      have output : network.inputCount + index = i := by omega
      have leftEquation := leftGraph (op, index) member
      have rightEquation := rightGraph (op, index) member
      simp only [output] at leftEquation rightEquation
      rw [leftEquation, rightEquation]
      apply opValue_congr op
      · simpa only [output] using gateFits (op, index) member
      · intro previous earlier
        exact ih previous earlier (by omega)

/-- Use the existing compiler and SSA aux allocation, not a native gate writer. -/
def descriptor (network : Network) (publicCount : Nat) : ConstraintDescriptor F :=
  emit id publicCount (network.inputCount + network.gates.size) (constraints network)

/-- Arbitrary accepted descriptor wires force the original DAG relation.
This direction does not need a finite index embedding assumption: all readback
uses the original total wire vector. Completeness/well-formedness additionally
need the network's bounded-variable/validity proof and publicCount bound. -/
theorem descriptor_forces (network : Network) (publicCount : Nat) (wires : Nat → F)
    (accepted : descriptorHolds (descriptor network publicCount) wires) :
    Holds network wires := by
  have flat := (emit_faithful id publicCount
    (network.inputCount + network.gates.size) (constraints network) wires).mp accepted
  exact (constraints_correct network wires).mp (flattenSystem_forces wires
    (readAux (network.inputCount + network.gates.size) wires) (constraints network)
    0 flat.1 flat.2)

/-- The actual IR2 row subset retains both graph forcing and every public pin.
PCS verification implies this only after the concrete backend soundness join. -/
theorem ir2_forces (network : Network) (publicCount : Nat) (wires publicInputs : Nat → F)
    (accepted : (BendTraceIR2.lower (descriptor network publicCount)).Holds wires publicInputs) :
    Holds network wires ∧ (∀ i < publicCount, wires i = publicInputs i) := by
  have original := (BendTraceIR2.lower_correct (descriptor network publicCount)
    wires publicInputs).mp accepted
  exact ⟨descriptor_forces network publicCount wires original.1, by simpa [descriptor, emit] using original.2⟩

#assert_axioms ir2_forces

#assert_axioms descriptor_forces

#assert_axioms graph_unique

#assert_axioms bit_injective
#assert_axioms bit_boolean
#assert_axioms constraints_bits_iff

#assert_axioms opExpr_correct
#assert_axioms gateConstraint_correct
#assert_axioms gateConstraint_bits
#assert_axioms constraints_correct
end Minidregg.Compiler.BendTraceConstraints
