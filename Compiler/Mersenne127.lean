/-
# The native policy field: `ZMod (2^127 - 1)`

Mini's admission has no proof system: a compiled law is checked by evaluating
its constraint system natively, so the field is not chosen by a prover. It must
only be a genuine prime field wide enough that the order gadget's
range decomposition never wraps for every difference friends can write
(`NativeHostProfile.orderWidth`). BabyBear (`2^31 - 2^27 + 1`) fitted a
29-bit difference and nothing more, which refused every law comparing the
wall clock with a small field.

Primality is a Pratt certificate checked by the kernel (`lucas_primality`: 43 has
order exactly `p - 1`, against the complete factorization of `p - 1`; its one
large factor carries its own certificate), with the powers reduced by
`reduce_mod_char`, not by `native_decide`. Mathlib's Lucas–Lehmer module would also
do, but it imports about 2,600 Mathlib modules into every Host module; this
certificate's imports are about half of that.
-/
module

public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.List.Prime
public import Mathlib.Algebra.Field.ZMod
public import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Compiler

/-- The Mersenne prime `2^127 - 1`. -/
def mersenne127P : ℕ := 2 ^ 127 - 1

theorem mersenne127P_eq : mersenne127P = 170141183460469231731687303715884105727 := by
  decide

/-- A Pratt certificate: `a` has order exactly `p - 1` in `ZMod p`, checked against a
complete factorization `l` of `p - 1` into primes. -/
theorem prime_of_pratt (p : ℕ) (a : ZMod p) (l : List ℕ) (primes : ∀ r ∈ l, r.Prime)
    (prod : l.prod = p - 1) (full : a ^ (p - 1) = 1) (proper : ∀ q ∈ l, a ^ ((p - 1) / q) ≠ 1) :
    p.Prime :=
  lucas_primality p a full fun q prime dvd => by
    rw [← prod] at dvd
    obtain ⟨r, mem, divides⟩ := (Prime.dvd_prod_iff prime.prime).mp dvd
    rw [(Nat.prime_dvd_prime_iff_eq prime (primes r mem)).mp divides]
    exact proper r mem

/-- The largest prime factor of `2^127 - 2`, by its own certificate (`norm_num`'s trial
division at this size overflows the kernel's recursion). -/
theorem prime_77158673929 : Nat.Prime 77158673929 :=
  prime_of_pratt _ 11 [2, 2, 2, 3, 3, 3, 7, 73, 699053]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> norm_num)
    (by norm_num) (by reduce_mod_char)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> (reduce_mod_char; decide))

theorem mersenne127P_prime : Nat.Prime mersenne127P := by
  rw [mersenne127P_eq]
  exact prime_of_pratt _ 43 [2, 3, 3, 3, 7, 7, 19, 43, 73, 127, 337, 5419, 92737, 649657, 77158673929]
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
      all_goals first | exact prime_77158673929 | norm_num)
    (by norm_num) (by reduce_mod_char)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro q (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;>
        (reduce_mod_char; decide))

instance : NeZero mersenne127P := ⟨mersenne127P_prime.ne_zero⟩

instance : Fact (Nat.Prime mersenne127P) := ⟨mersenne127P_prime⟩

abbrev Mersenne127 := ZMod mersenne127P

#assert_axioms prime_of_pratt
#assert_axioms prime_77158673929
#assert_axioms mersenne127P_prime

end Minidregg.Compiler
