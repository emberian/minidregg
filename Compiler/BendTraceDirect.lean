import Compiler.BendTraceConstraints

/- The existing AIR is already quadratic for Boolean networks. Serialize its
arithmetic fold directly to IR2 WindowExpr, avoiding unnecessary auxiliary
wires for subexpressions. This is a generic algebra interpretation, not a
second gate language or a hand-written native constraint implementation. -/
namespace Minidregg.Compiler.BendTraceDirect
open BendTraceIR2 BendTraceConstraints
set_option autoImplicit false
variable {F : Type} [Field F]

def rowAlg : Alg (AirSig F Nat) (RowExpr F) := fun operation =>
  match operation with
  | .const value => fun _ => .constant value
  | .var index => fun _ => .loc index
  | .add => fun children => .add (children false) (children true)
  | .mul => fun children => .mul (children false) (children true)

def expression : Term (AirSig F Nat) → RowExpr F := fold rowAlg

theorem expression_correct (assignment : Nat → F) (term : Term (AirSig F Nat)) :
    (expression term).eval assignment = eval assignment term := by
  have hom : IsFoldHom (evalAlg assignment)
      (fun term => (expression term).eval assignment) := by
    intro operation children
    cases operation <;> rfl
  exact congrFun (agree_by_initiality (evalAlg assignment)
    (fun term => (expression term).eval assignment) (eval assignment)
    hom (fold_isFoldHom (evalAlg assignment))) term

def lower (system : ConstraintSystem F Nat) (width : Nat) (pins : List Nat) : Plan F where
  width := width
  publicCount := pins.length
  constraints := system.map (fun term => .zero (expression term)) ++
    pins.zipIdx.map (fun entry => .pi entry.1 entry.2)

theorem lower_correct (system : ConstraintSystem F Nat) (width : Nat) (pins : List Nat)
    (row publicInputs : Nat → F) :
    (lower system width pins).Holds row publicInputs ↔
      systemAccepts row system ∧ (∀ entry ∈ pins.zipIdx, row entry.1 = publicInputs entry.2) := by
  simp only [lower, Plan.Holds, List.forall_mem_append, List.forall_mem_map,
    RowConstraint.Holds, expression_correct]
  rfl

/-- Arbitrary accepted direct rows retain the identical existing network AIR
relation plus every selected public binding. No honest-witness assumption. -/
theorem network_forces (network : ObliviousNetwork.Network) (pins : List Nat)
    (row publicInputs : Nat → F)
    (accepted : (lower (constraints network) (network.inputCount + network.gates.size) pins).Holds
      row publicInputs) :
    Holds network row ∧ (∀ entry ∈ pins.zipIdx, row entry.1 = publicInputs entry.2) := by
  obtain ⟨relation, pinned⟩ := (lower_correct _ _ _ row publicInputs).mp accepted
  exact ⟨(constraints_correct network row).mp relation, pinned⟩

#assert_axioms expression_correct
#assert_axioms lower_correct
#assert_axioms network_forces
end Minidregg.Compiler.BendTraceDirect
