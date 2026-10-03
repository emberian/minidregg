import Compiler.EmitSerialize
import Theory.AssertAxioms

/- Executable lowering from Mini's emitted arithmetic descriptor to the
existing Bread IR2 local-row subset. The native parser/PCS boundary remains
conformance and backend soundness, not a theorem about Rust execution. -/
namespace Minidregg.Compiler.BendTraceIR2
set_option autoImplicit false
universe u
variable {F : Type u} [Field F]

inductive RowExpr (F : Type u) where
  | constant (value : F)
  | loc (column : Nat)
  | add (left right : RowExpr F)
  | mul (left right : RowExpr F)

def RowExpr.eval (row : Nat → F) : RowExpr F → F
  | .constant value => value
  | .loc column => row column
  | .add left right => left.eval row + right.eval row
  | .mul left right => left.eval row * right.eval row

def wireExpr : DWire F → RowExpr F
  | .cnst value => .constant value
  | .wire column => .loc column

def gateExpr (gate : DGate F) : RowExpr F :=
  .add (match gate.op with
    | .add => .add (wireExpr gate.a) (wireExpr gate.b)
    | .mul => .mul (wireExpr gate.a) (wireExpr gate.b))
    (.mul (.constant (-1)) (.loc gate.out))

inductive RowConstraint (F : Type u) where
  | zero (expression : RowExpr F)
  | pi (column index : Nat)

def RowConstraint.Holds (row publicInputs : Nat → F) : RowConstraint F → Prop
  | .zero expression => expression.eval row = 0
  | .pi column index => row column = publicInputs index

structure Plan (F : Type u) where
  width : Nat
  publicCount : Nat
  constraints : List (RowConstraint F)

def lower (descriptor : ConstraintDescriptor F) : Plan F where
  width := descriptor.nWires
  publicCount := descriptor.nPublic
  constraints :=
    (List.range descriptor.nPublic).map (fun i => .pi i i) ++
    descriptor.gates.map (fun gate => .zero (gateExpr gate)) ++
    descriptor.zeros.map (fun wire => .zero (wireExpr wire))

def Plan.Holds (plan : Plan F) (row publicInputs : Nat → F) : Prop :=
  ∀ constraint ∈ plan.constraints, constraint.Holds row publicInputs

theorem wireExpr_correct (wire : DWire F) (row : Nat → F) :
    (wireExpr wire).eval row = wire.read row := by cases wire <;> rfl

theorem gateExpr_correct (gate : DGate F) (row : Nat → F) :
    (gateExpr gate).eval row = 0 ↔ gate.holds row := by
  cases gate with
  | mk op a b out =>
    cases op <;>
      simp [gateExpr, RowExpr.eval, wireExpr_correct, DGate.holds,
        GateOp.denote, ← sub_eq_add_neg, sub_eq_zero]

/-- Arbitrary-witness equivalence. Every original public input is pinned; every
emitted arithmetic gate and zero root is retained. This is not a proof-system
soundness assumption hidden as a Lean theorem. -/
theorem lower_correct (descriptor : ConstraintDescriptor F) (row publicInputs : Nat → F) :
    (lower descriptor).Holds row publicInputs ↔
      descriptorHolds descriptor row ∧
      (∀ i < descriptor.nPublic, row i = publicInputs i) := by
  simp only [Plan.Holds, lower, List.forall_mem_append, List.forall_mem_map]
  simp [RowConstraint.Holds, gateExpr_correct, wireExpr_correct,
    descriptorHolds, and_assoc, and_comm, and_left_comm]

open Lean (Json toJson)

def RowExpr.toJson {p : Nat} [NeZero p] : RowExpr (ZMod p) → Json
  | .constant value => Json.mkObj [("t", .str "const"), ("v", Lean.toJson value.val)]
  | .loc column => Json.mkObj [("t", .str "loc"), ("c", Lean.toJson column)]
  | .add left right => Json.mkObj [("t", .str "add"), ("l", left.toJson), ("r", right.toJson)]
  | .mul left right => Json.mkObj [("t", .str "mul"), ("l", left.toJson), ("r", right.toJson)]

def RowConstraint.toJson {p : Nat} [NeZero p] : RowConstraint (ZMod p) → Json
  | .zero expression => Json.mkObj [("t", .str "window_gate"),
      ("on_transition", .bool false), ("body", expression.toJson)]
  | .pi column index => Json.mkObj [("t", .str "pi_binding"),
      ("row", .str "first"), ("col", Lean.toJson column), ("pi_index", Lean.toJson index)]

/-- IR2 is BabyBear-specific; never serialize a different field under this ABI.
No witness, source count, private input, or secret trace state is included. -/
def Plan.toJson (plan : Plan BabyBear) : Json := Json.mkObj
  [("name", .str "mini-bend-bounded-trace-ir2-v1"), ("ir", Lean.toJson (2 : Nat)),
   ("trace_width", Lean.toJson plan.width), ("public_input_count", Lean.toJson plan.publicCount),
   ("challenges", Lean.toJson (0 : Nat)),
   ("tables", .arr #[Json.mkObj [("id", Lean.toJson (0 : Nat)), ("name", .str "main"),
     ("arity", Lean.toJson plan.width), ("sem", .str "main")]]),
   ("constraints", .arr (plan.constraints.map RowConstraint.toJson).toArray),
   ("hash_sites", .arr #[]), ("ranges", .arr #[])]

#assert_axioms wireExpr_correct
#assert_axioms gateExpr_correct
#assert_axioms lower_correct
end Minidregg.Compiler.BendTraceIR2
