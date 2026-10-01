/-
# The native policy field: `ZMod (2^127 - 1)`

Mini's admission has no proof system: a compiled law is checked by evaluating
its constraint system natively, so the field is not chosen by a prover. It must
only be a genuine prime field wide enough that the order gadget's
range decomposition never wraps for every difference friends can write
(`NativeHostProfile.orderWidth`). BabyBear (`2^31 - 2^27 + 1`) fitted a
29-bit difference and nothing more, which refused every law comparing the
wall clock with a small field.

Primality is the Lucas–Lehmer test, evaluated by the kernel
(`lucas_lehmer_sufficiency` with Mathlib's `norm_num` extension), not by
`native_decide`.
-/
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Algebra.Field.ZMod
import Theory.AssertAxioms

namespace Minidregg.Compiler

/-- The Mersenne prime `2^127 - 1`. -/
def mersenne127P : ℕ := 2 ^ 127 - 1

theorem mersenne127P_eq : mersenne127P = 170141183460469231731687303715884105727 := by
  decide

theorem mersenne127P_prime : Nat.Prime mersenne127P := by
  have h := lucas_lehmer_sufficiency 127 (by norm_num) (by norm_num)
  simpa [mersenne, mersenne127P] using h

instance : NeZero mersenne127P := ⟨mersenne127P_prime.ne_zero⟩

instance : Fact (Nat.Prime mersenne127P) := ⟨mersenne127P_prime⟩

abbrev Mersenne127 := ZMod mersenne127P

#assert_axioms mersenne127P_prime

end Minidregg.Compiler
