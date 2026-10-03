/-
Fixed-data-case specialization through Mini's existing AIR/flatten/emit compiler.
This module is a backend block, not another Bend interpreter. The source adapter
in BendLogicSpecialization supplies the actual pinned BendTT Eval derivation.
Input and output are binary enum tags. Quantity and privacy are separate.
The public prefix is chosen by the receiving profile (0..2); the relation's
source/input/output commitments belong to the outer statement, not this header.
-/
import Compiler.Emit
import Theory.AssertAxioms

namespace Minidregg.Compiler.BendLogicCase

set_option autoImplicit false

structure Plan where
  onFalse : Bool
  onTrue : Bool
  deriving DecidableEq, Repr

def Plan.output (p : Plan) (input : Bool) : Bool :=
  if input then p.onTrue else p.onFalse

def bit {F : Type} [Field F] (b : Bool) : F := if b then 1 else 0

/-- Output occupies wire 0; nPublic=1 reveals only output while input wire 1
remains private. nPublic=0 hides both and nPublic=2 exposes both. -/
def assignment {F : Type} [Field F] (input output : Bool) : Fin 2 → F :=
  fun i => if i.val = 0 then bit output else bit input

/-- The Boolean truth table is interpolated on precisely the two encoded tags.
No finite-field aliasing of a Nat/Sigma representation is promised. -/
def outputExpr {F : Type} [Field F] (p : Plan) : Term (AirSig F (Fin 2)) :=
  add' (cst (bit p.onFalse))
    (mul' (vr 1) (cst (bit p.onTrue - bit p.onFalse)))

def constraints {F : Type} [Field F] (p : Plan) : ConstraintSystem F (Fin 2) :=
  [boolGadget 0, boolGadget 1,
    add' (vr 0) (mul' (cst (-1)) (outputExpr p))]

/-- All emitted auxiliary assignments are forced by Emit. Publicness is a
layout selection and does not alter the secret-input relation. -/
def descriptor {F : Type} [Field F] (nPublic : Nat) (p : Plan) : ConstraintDescriptor F :=
  emit Fin.val nPublic 2 (constraints p)

/-- The constructive reading computes the output; it does not need a supplied
output wire or solve a constraint system. This is what an encrypted evaluator
must consume, with the same plan as the relational proof artifact. -/
theorem outputExpr_correct {F : Type} [Field F] (p : Plan) (input output : Bool) :
    eval (assignment (F := F) input output) (outputExpr p) = bit (p.output input) := by
  rw [← eval_agrees_exec]
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> cases input <;>
    simp [evalExec, outputExpr, assignment, bit, Plan.output,
      cst, vr, add', mul', AirSig]

theorem constraints_correct {F : Type} [Field F] (p : Plan) (input output : Bool) :
    systemAccepts (assignment (F := F) input output) (constraints p) ↔
      output = p.output input := by
  simp only [systemAccepts, constraints, List.forall_mem_cons]
  simp only [List.not_mem_nil, false_implies, implies_true, and_true]
  simp only [boolGadget_correct]
  simp only [accepts_iff_semHolds, semHolds]
  change ((assignment (F := F) input output 0 = 0 ∨ assignment (F := F) input output 0 = 1) ∧
    (assignment (F := F) input output 1 = 0 ∨ assignment (F := F) input output 1 = 1) ∧
    (assignment (F := F) input output 0 + (-1) * evalExec (assignment (F := F) input output) (outputExpr p) = 0)) ↔ _
  rw [eval_agrees_exec, outputExpr_correct]
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> cases input <;> cases output <;>
    simp [assignment, bit, Plan.output]

/-- One validated source plan determines both the executable output expression
and the relational artifact. They are derived projections, not independently
supplied circuits that can disagree. Flattening is the existing Mini fold. -/
structure Block where
  plan : Plan
  nPublic : Nat
  publicFits : nPublic ≤ 2

def Block.expression {F : Type} [Field F] (b : Block) : Term (AirSig F (Fin 2)) :=
  outputExpr b.plan

def Block.flatOutput {F : Type} [Field F] (b : Block) : FlatOut F (Fin 2) :=
  flatten b.expression 0

def Block.relation {F : Type} [Field F] (b : Block) : ConstraintDescriptor F :=
  descriptor b.nPublic b.plan

/-- Arbitrary satisfying descriptor vectors, not only an emitter-produced
witness, imply the selected source result; false result claims have no witness. -/
theorem descriptor_correct {F : Type} [Field F] (nPublic : Nat) (p : Plan)
    (input output : Bool) :
    (∃ wv : Nat → F,
      (∀ i : Fin 2, wv i.val = assignment input output i) ∧
      descriptorHolds (descriptor nPublic p) wv) ↔ output = p.output input := by
  rw [descriptor, emit_accepts_iff_fin, constraints_correct]

theorem wrong_output_refused {F : Type} [Field F] (nPublic : Nat) (p : Plan)
    (input output : Bool) (wrong : output ≠ p.output input) :
    ¬ ∃ wv : Nat → F,
      (∀ i : Fin 2, wv i.val = assignment input output i) ∧
      descriptorHolds (descriptor nPublic p) wv := by
  rw [descriptor_correct]
  exact wrong

#assert_axioms outputExpr_correct
#assert_axioms constraints_correct
#assert_axioms descriptor_correct
#assert_axioms wrong_output_refused

end Minidregg.Compiler.BendLogicCase
