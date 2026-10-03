/- The actual first BFV consumer plaintext modulus. This is a source arithmetic
corollary, not a BFV noise/encryption/bit-validity or custody theorem. It applies
only after the plaintext input is admitted as the exact Boolean tag encoding. -/
import Compiler.BendLogicCase
import Mathlib.Tactic.NormNum.Prime

namespace Minidregg.Compiler.BendLogicBFVPlain

open BendLogicCase

set_option autoImplicit false

def modulus : Nat := 1032193

theorem modulus_prime : Nat.Prime modulus := by norm_num [modulus]

instance : Fact (Nat.Prime modulus) := ⟨modulus_prime⟩

abbrev Plain := ZMod modulus

/-- Instantiates the actual shared compiler expression in the plaintext field,
with no reinterpreted BabyBear residue. Input validity is an explicit premise
of using assignment, while the output's encrypted implementation is separate. -/
theorem plaintext_output_exact (plan : Plan) (input output : Bool) :
    eval (assignment (F := Plain) input output) (outputExpr plan) =
      bit (plan.output input) :=
  outputExpr_correct plan input output

theorem plaintext_descriptor_exact (nPublic : Nat) (plan : Plan)
    (input output : Bool) :
    (∃ wv : Nat → Plain,
      (∀ i : Fin 2, wv i.val = assignment input output i) ∧
      descriptorHolds (descriptor nPublic plan) wv) ↔ output = plan.output input :=
  descriptor_correct nPublic plan input output

#assert_axioms modulus_prime
#assert_axioms plaintext_output_exact
#assert_axioms plaintext_descriptor_exact

end Minidregg.Compiler.BendLogicBFVPlain
