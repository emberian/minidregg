import Compiler.BendTraceIR2

/- Explicit public-column selection for the actual IR2 descriptor. The caller
must derive pins and expected public values from the admitted statement; this
module does not authorize revealing a private wire. -/
namespace Minidregg.Compiler.BendTracePublicPins
open BendTraceIR2
set_option autoImplicit false
variable {F : Type} [Field F]

def lower (descriptor : ConstraintDescriptor F) (pins : List Nat) : Plan F :=
  let base := BendTraceIR2.lower { descriptor with nPublic := 0 }
  { base with
    publicCount := pins.length
    constraints := base.constraints ++ pins.zipIdx.map (fun entry => .pi entry.1 entry.2) }

/-- Every arithmetic gate and zero root survives, and the exact selected
columns are bound to their independently expected public indices. -/
theorem lower_correct (descriptor : ConstraintDescriptor F) (pins : List Nat)
    (row publicInputs : Nat → F) :
    (lower descriptor pins).Holds row publicInputs ↔
      descriptorHolds descriptor row ∧
      (∀ entry ∈ pins.zipIdx, row entry.1 = publicInputs entry.2) := by
  have base := BendTraceIR2.lower_correct { descriptor with nPublic := 0 } row publicInputs
  simp only [lower, Plan.Holds, List.forall_mem_append, List.forall_mem_map]
  change (BendTraceIR2.lower { descriptor with nPublic := 0 }).Holds row publicInputs ∧ _ ↔ _
  rw [base]
  simp [descriptorHolds, RowConstraint.Holds]

#assert_axioms lower_correct
end Minidregg.Compiler.BendTracePublicPins
