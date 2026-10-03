/- Exact signed origin and bounded intermediates for the admitted Boolean
compiler blocks. No global Rat→Fp homomorphism is asserted. These cast only
integer expressions; BFV noise, ciphertext membership and custody are separate. -/
import Compiler.BendLogicMux

namespace Minidregg.Compiler.BendLogicSignedSemantics

set_option autoImplicit false

def integerBit (b : Bool) : Int := if b then 1 else 0

theorem integerBit_cast {F : Type} [Field F] (b : Bool) :
    (integerBit b : F) = BendLogicCase.bit b := by
  cases b <;> simp [integerBit, BendLogicCase.bit]

def literalInteger (plan : BendLogicCase.Plan) (input : Bool) : Int :=
  integerBit plan.onFalse + integerBit input *
    (integerBit plan.onTrue - integerBit plan.onFalse)

theorem literalInteger_correct (plan : BendLogicCase.Plan) (input : Bool) :
    literalInteger plan input = integerBit (plan.output input) := by
  rcases plan with ⟨a,b⟩
  cases a <;> cases b <;> cases input <;>
    simp [literalInteger, integerBit, BendLogicCase.Plan.output]

theorem literal_signed_bounds (plan : BendLogicCase.Plan) (input : Bool) :
    -1 ≤ integerBit plan.onTrue - integerBit plan.onFalse ∧
    integerBit plan.onTrue - integerBit plan.onFalse ≤ 1 ∧
    -1 ≤ integerBit input * (integerBit plan.onTrue - integerBit plan.onFalse) ∧
    integerBit input * (integerBit plan.onTrue - integerBit plan.onFalse) ≤ 1 ∧
    0 ≤ literalInteger plan input ∧ literalInteger plan input ≤ 1 := by
  rcases plan with ⟨a,b⟩
  cases a <;> cases b <;> cases input <;> decide

theorem literal_integer_semantics {F : Type} [Field F]
    (plan : BendLogicCase.Plan) (input output : Bool) :
    eval (BendLogicCase.assignment (F := F) input output)
      (BendLogicCase.outputExpr plan) = (literalInteger plan input : F) := by
  rw [BendLogicCase.outputExpr_correct, literalInteger_correct, integerBit_cast]

def muxInteger (selector onTrue onFalse : Bool) : Int :=
  integerBit onFalse + integerBit selector *
    (integerBit onTrue - integerBit onFalse)

theorem muxInteger_correct (selector onTrue onFalse : Bool) :
    muxInteger selector onTrue onFalse =
      integerBit (BendLogicMux.result selector onTrue onFalse) := by
  cases selector <;> cases onTrue <;> cases onFalse <;>
    simp [muxInteger, integerBit, BendLogicMux.result]

theorem mux_signed_bounds (selector onTrue onFalse : Bool) :
    -1 ≤ -integerBit onFalse ∧ -integerBit onFalse ≤ 0 ∧
    -1 ≤ integerBit onTrue - integerBit onFalse ∧
    integerBit onTrue - integerBit onFalse ≤ 1 ∧
    -1 ≤ integerBit selector * (integerBit onTrue - integerBit onFalse) ∧
    integerBit selector * (integerBit onTrue - integerBit onFalse) ≤ 1 ∧
    0 ≤ muxInteger selector onTrue onFalse ∧ muxInteger selector onTrue onFalse ≤ 1 := by
  cases selector <;> cases onTrue <;> cases onFalse <;> decide

theorem mux_integer_semantics {F : Type} [Field F]
    (selector onTrue onFalse output : Bool) :
    eval (BendLogicMux.assignment (F := F) selector onTrue onFalse output)
      BendLogicMux.outputExpr = (muxInteger selector onTrue onFalse : F) := by
  rw [BendLogicMux.outputExpr_correct, muxInteger_correct, integerBit_cast]

/-- Every field uses the same ordered constructive graph. Constants retain
integer origin; changing field modulus changes only the literal cast. -/
theorem literal_flat_layout {F : Type} [Field F] (plan : BendLogicCase.Plan) :
    flatten (BendLogicCase.outputExpr (F := F) plan) 0 =
      (⟨.aux 1,
        [⟨.mul, .var 1, .cnst (BendLogicCase.bit plan.onTrue - BendLogicCase.bit plan.onFalse), 0⟩,
         ⟨.add, .cnst (BendLogicCase.bit plan.onFalse), .aux 0, 1⟩],
        2⟩ : FlatOut F (Fin 2)) := by rfl

theorem mux_flat_layout {F : Type} [Field F] :
    flatten (BendLogicMux.outputExpr (F := F)) 0 =
      (⟨.aux 3,
        [⟨.mul, .cnst (-1), .var 3, 0⟩,
         ⟨.add, .var 2, .aux 0, 1⟩,
         ⟨.mul, .var 1, .aux 1, 2⟩,
         ⟨.add, .var 3, .aux 2, 3⟩],
        4⟩ : FlatOut F (Fin 4)) := by rfl

#assert_axioms integerBit_cast
#assert_axioms literalInteger_correct
#assert_axioms literal_signed_bounds
#assert_axioms literal_integer_semantics
#assert_axioms muxInteger_correct
#assert_axioms mux_signed_bounds
#assert_axioms mux_integer_semantics
#assert_axioms literal_flat_layout
#assert_axioms mux_flat_layout

end Minidregg.Compiler.BendLogicSignedSemantics
