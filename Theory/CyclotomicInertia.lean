/-
# Theory.CyclotomicInertia — which cyclotomic rings are FIELDS over our candidate primes

**The question this file settles.** A module-SIS / lattice commitment lives over a ring
`R_q = F_q[X]/(Φ_η)`.  Extraction arguments in that family need *small-norm ring elements to be
invertible*, and how many of them are invertible is governed entirely by how `Φ_η` factors over
`F_q` — i.e. by the **inertia degree** `ord_η(q)`.  Maximal inertia (`ord_η(q) = φ(η)`, so `Φ_η`
is irreducible and `R_q` is a *field*) is the best possible case: every nonzero element is a unit.
Minimal inertia (`ord_η(q) = 1`, so `Φ_η` splits into `φ(η)` linear factors) is the worst: the
ring is a product of copies of `F_q` and zero divisors are everywhere.

**The result.** At the deployed-candidate prime **KoalaBear** `= 2³¹ − 2²⁴ + 1`:

* `orderOf_koalaBear_three_pow` — for **every** `k`, `ord_{3^(k+1)}(KB) = 2·3^k = φ(3^(k+1))`.
  This is fully general, not a per-`k` computation: it comes from a lifting-the-exponent step
  (`ZMod.orderOf_one_add_mul_prime`, Mathlib) on the witness `KB² = 1 + 3·a` with `3 ∤ a`.
* `irreducible_cyclotomic_three_pow` — hence `Φ_{3^(k+1)}` is **irreducible** over `F_KB` for
  every `k`, and in particular `irreducible_cyclotomic_81` at the headline conductor `η = 81`.
* `KBCyc81_isField` / `KBCyc81_finrank` — therefore `R_q := F_KB[X]/(Φ₈₁)` **is a field**, of
  degree `54 = φ(81)` over `F_KB`.  Maximal inertia at conductor 81.

**The teeth — both halves, because a hypothesis never shown to be a constraint is not a
hypothesis.**

* *The field is a constraint.* `not_irreducible_cyclotomic_81_babyBear` and
  `not_irreducible_cyclotomic_81_mersenne31`: at the **same** conductor 81, BabyBear
  (`ord = 27`, 2 factors of degree 27) and Mersenne-31 (`ord = 9`, 6 factors of degree 9) make
  `Φ₈₁` **reducible**.  BabyBear is the incumbent field; it does not have this property.
* *The conductor is a constraint.* `natDegree_factor_negacyclic` / `card_factors_negacyclic` /
  `splits_negacyclic` / `not_irreducible_negacyclic`: over the **same** field `F_KB`, the
  negacyclic conductor `η = 2^(k+1)` gives `X^(2^k) + 1 = Φ_{2^(k+1)}`, `ord = 1`, and exactly
  `2^k` distinct irreducible factors **each of degree 1** — total splitting, the worst case, for
  every `k + 1 ≤ 24`, i.e. every power-of-two degree `d = 2^k ≤ 2²³`, which covers every `d ≤ 1024`
  the negacyclic family actually uses (they are all powers of two).  This is why
  the entire power-of-two negacyclic lattice-PCS family (Greyhound / LaBRADOR / Hachi …) is
  arithmetically incompatible with KoalaBear: `KB − 1 = 2²⁴ · 127`, so KoalaBear is *too*
  two-adic, which is exactly what makes it FRI-friendly.

**SCOPE — what this is and is not.**  This is an **arithmetic possibility result**.  It says a
lattice commitment over unmodified KoalaBear is *not ruled out by ring splitting*, and that among
our candidates KoalaBear is the one with the best splitting behaviour at a power-of-three
conductor.  It says **nothing** about whether such a commitment should be built:

* the security bill is **unpriced** — non-power-of-two cyclotomics give module-BKZ a
  subexponential speedup (Ducas–Engelberts–de Perthuis) that is unquantified at these parameters;
* the KoalaBear-compatible ring family contains **no PCS** at all today (Neo/SuperNeo are folding
  schemes; every lattice PCS on the shelf is negacyclic);
* non-full-splitting costs the NTT;
* nothing here is a norm bound, an invertibility-of-challenge-differences bound, or a hardness
  assumption.  "The ring is a field" makes every nonzero element a unit; it prices nothing.

**Reused from Mathlib** (this file hand-rolls none of it):
`Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible`,
`ZMod.irreducible_of_dvd_cyclotomic_of_natDegree`,
`Polynomial.normalizedFactors_cyclotomic_card`,
`Polynomial.cyclotomic_prime_pow_eq_geom_sum`, `ZMod.orderOf_one_add_mul_prime`,
`orderOf_eq_of_pow_and_pow_div_prime`, `AdjoinRoot.powerBasis`.
-/
import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.RingTheory.AdjoinRoot

namespace Minidregg.Theory.CyclotomicInertia

open Polynomial
open scoped Nat

set_option autoImplicit false

/-! ## 0. The candidate primes -/

/-- **KoalaBear**, `2³¹ − 2²⁴ + 1 = 2130706433`. -/
def koalaBear : ℕ := 2 ^ 31 - 2 ^ 24 + 1

/-- **BabyBear**, `2³¹ − 2²⁷ + 1 = 2013265921` — the incumbent field, present here as a
refutation and nothing else. -/
def babyBear : ℕ := 2 ^ 31 - 2 ^ 27 + 1

/-- **Mersenne-31**, `2³¹ − 1 = 2147483647` — a second refutation. -/
def mersenne31 : ℕ := 2 ^ 31 - 1

theorem koalaBear_eq : koalaBear = 2130706433 := by norm_num [koalaBear]

theorem babyBear_eq : babyBear = 2013265921 := by norm_num [babyBear]

theorem mersenne31_eq : mersenne31 = 2147483647 := by norm_num [mersenne31]

theorem koalaBear_prime : Nat.Prime koalaBear := by rw [koalaBear_eq]; norm_num

theorem babyBear_prime : Nat.Prime babyBear := by rw [babyBear_eq]; norm_num

theorem mersenne31_prime : Nat.Prime mersenne31 := by rw [mersenne31_eq]; norm_num

instance : Fact (Nat.Prime koalaBear) := ⟨koalaBear_prime⟩
instance : Fact (Nat.Prime babyBear) := ⟨babyBear_prime⟩
instance : Fact (Nat.Prime mersenne31) := ⟨mersenne31_prime⟩

/-- `KB − 1 = 2²⁴ · 127`: KoalaBear's two-adicity is 24.  This is simultaneously why it is
FRI-friendly and why every power-of-two negacyclic ring over it collapses (§4). -/
theorem koalaBear_sub_one : koalaBear - 1 = 2 ^ 24 * 127 := by rw [koalaBear_eq]; norm_num

/-! ## 1. The bridge — `ord_η(p)` decides the factorization of `Φ_η` over `F_p`

Everything downstream is an instance of these four.  They are stated in terms of
`orderOf ((p : ZMod η))` (the multiplicative order of the field characteristic modulo the
conductor) rather than Mathlib's `orderOf (ZMod.unitOfCoprime …)`, so that the arithmetic
side never has to carry a coprimality proof term around. -/

section Bridge

variable {p η : ℕ} [hp : Fact p.Prime]

/-- Every irreducible factor of `Φ_η` over `F_p` has degree exactly `ord_η(p)`. -/
theorem natDegree_eq_orderOf_of_irreducible {P : (ZMod p)[X]} (hpη : ¬p ∣ η)
    (hP : P ∣ cyclotomic η (ZMod p)) (hPirr : Irreducible P) :
    P.natDegree = orderOf ((p : ZMod η)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hK : Fintype.card (ZMod p) = p ^ 1 := by simp [ZMod.card]
  have h := Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible (K := ZMod p) (p := p) (f := 1)
    hK ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpη) hP hPirr
  rw [h, ← orderOf_units, ZMod.coe_unitOfCoprime, pow_one]

/-- **Maximal inertia ⇒ irreducible.**  If `p` generates the whole unit group `(ℤ/η)ˣ` then
`Φ_η` is irreducible over `F_p`, so `F_p[X]/(Φ_η)` is a field of degree `φ η`. -/
theorem irreducible_cyclotomic_of_orderOf_eq_totient (hpη : ¬p ∣ η)
    (h : orderOf ((p : ZMod η)) = φ η) : Irreducible (cyclotomic η (ZMod p)) := by
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree hpη dvd_rfl ?_
  rw [natDegree_cyclotomic, ← orderOf_units, ZMod.coe_unitOfCoprime, h]

/-- **The refutation direction.**  If `p` does *not* generate `(ℤ/η)ˣ` then `Φ_η` is
REDUCIBLE over `F_p`.  This is what makes the hypothesis of the previous theorem a real
constraint rather than decoration. -/
theorem not_irreducible_cyclotomic_of_orderOf_ne_totient (hpη : ¬p ∣ η)
    (h : orderOf ((p : ZMod η)) ≠ φ η) : ¬Irreducible (cyclotomic η (ZMod p)) := fun hirr =>
  h (by rw [← natDegree_eq_orderOf_of_irreducible hpη dvd_rfl hirr, natDegree_cyclotomic])

open UniqueFactorizationMonoid in
/-- Every monic irreducible factor of `Φ_η` over `F_p` has degree `ord_η(p)`. -/
theorem natDegree_of_mem_normalizedFactors (hpη : ¬p ∣ η) {P : (ZMod p)[X]}
    (hP : P ∈ normalizedFactors (cyclotomic η (ZMod p))) :
    P.natDegree = orderOf ((p : ZMod η)) :=
  natDegree_eq_orderOf_of_irreducible hpη (dvd_of_mem_normalizedFactors hP)
    (irreducible_of_normalized_factor P hP)

open UniqueFactorizationMonoid in
/-- `Φ_η` has exactly `φ η / ord_η(p)` distinct monic irreducible factors over `F_p`. -/
theorem card_normalizedFactors (hpη : ¬p ∣ η) :
    (normalizedFactors (cyclotomic η (ZMod p))).toFinset.card = φ η / orderOf ((p : ZMod η)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hK : Fintype.card (ZMod p) = p ^ 1 := by simp [ZMod.card]
  have h := Polynomial.normalizedFactors_cyclotomic_card (K := ZMod p) (p := p) (f := 1) (n := η)
    hK ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpη)
  rw [h, ← orderOf_units, ZMod.coe_unitOfCoprime, pow_one]

end Bridge

/-! ## 2. Arithmetic helpers -/

private theorem prime_dvd_three_pow {q e : ℕ} (hq : q.Prime) (h : q ∣ 3 ^ e) : q = 3 :=
  (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h)

private theorem prime_dvd_54 {q : ℕ} (hq : q.Prime) (h : q ∣ 54) : q = 2 ∨ q = 3 := by
  rw [show (54 : ℕ) = 2 * 3 ^ 3 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h')
  · exact Or.inr (prime_dvd_three_pow hq h')

/-- `φ 81 = 54`. -/
theorem totient_81 : φ 81 = 54 := by
  rw [show (81 : ℕ) = 3 ^ (3 + 1) by norm_num, Nat.totient_prime_pow_succ Nat.prime_three]
  norm_num

/-! ## 3. KoalaBear at conductor `3^k` — maximal inertia, at every `k`

`orderOf_koalaBear_mod81` is the headline instance done by direct computation;
`orderOf_koalaBear_three_pow` is the general theorem, proved by lifting the exponent.  They are
*independent* derivations of the same `k = 3` fact, which is exactly the cross-check the
numerical evidence was asking for. -/

/-- **Fact 1, by computation.** `ord₈₁(KB) = 54 = φ(81)`: `KB ≡ 56 (mod 81)` generates the whole
unit group `(ℤ/81)ˣ`.  Proved by exhibiting `56⁵⁴ = 1` together with `56²⁷ ≠ 1` and `56¹⁸ ≠ 1`
(the two maximal proper divisors of 54 = 2·3³). -/
theorem orderOf_koalaBear_mod81 : orderOf ((koalaBear : ZMod 81)) = 54 := by
  have hc : ((koalaBear : ℕ) : ZMod 81) = 56 := by rw [koalaBear_eq]; decide
  rw [hc]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) ?_
  intro q hq hqd
  rcases prime_dvd_54 hq hqd with rfl | rfl
  · decide
  · decide

/-- The lifting witness: `KB² − 1 = 3·a` with `3 ∤ a`, i.e. `v₃(KB² − 1) = 1` exactly.  That
`v₃` is *exactly* 1 is what makes the order full at every `3^k` rather than stalling. -/
private def liftWitness : ℤ := 1513303301209194496

private theorem koalaBear_sq : ((koalaBear : ℕ) : ℤ) ^ 2 = 1 + 3 * liftWitness := by
  rw [koalaBear_eq]; norm_num [liftWitness]

private theorem three_not_dvd_liftWitness : ¬(3 : ℤ) ∣ liftWitness := by
  rintro ⟨c, hc⟩
  rw [liftWitness] at hc
  omega

/-- **Fact 4, general.** For every `k`, `ord_{3^(k+1)}(KB) = 2·3^k`.  Proof: `KB²` has order
exactly `3^k` mod `3^(k+1)` by lifting the exponent from `v₃(KB² − 1) = 1`
(`ZMod.orderOf_one_add_mul_prime`), while `KB ≡ −1 (mod 3)` forces the order to be even; the two
are coprime, so their product divides, and `KB^(2·3^k) = 1` bounds it above. -/
theorem orderOf_koalaBear_three_pow (k : ℕ) :
    orderOf ((koalaBear : ZMod (3 ^ (k + 1)))) = 2 * 3 ^ k := by
  set x : ZMod (3 ^ (k + 1)) := ((koalaBear : ℕ) : ZMod (3 ^ (k + 1))) with hxdef
  -- (a) `x²` has order `3^k`, by lifting the exponent.
  have hord2 : orderOf (x ^ 2) = 3 ^ k := by
    have h := ZMod.orderOf_one_add_mul_prime (p := 3) Nat.prime_three (by norm_num) liftWitness
      three_not_dvd_liftWitness k
    rw [← h]
    congr 1
    have hcast := congrArg (fun z : ℤ => (z : ZMod (3 ^ (k + 1)))) koalaBear_sq
    push_cast at hcast ⊢
    rw [hxdef]
    exact hcast
  -- (b) the order is even, because `KB ≡ −1 (mod 3)`.
  have hdvd : (3 : ℕ) ∣ 3 ^ (k + 1) := dvd_pow_self 3 (Nat.succ_ne_zero k)
  have hcast3 : (ZMod.castHom hdvd (ZMod 3)) x = (2 : ZMod 3) := by
    rw [hxdef, map_natCast, koalaBear_eq]; decide
  have h2ord : orderOf ((2 : ZMod 3)) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)
  have hmap : orderOf ((ZMod.castHom hdvd (ZMod 3)) x) ∣ orderOf x :=
    orderOf_map_dvd (ZMod.castHom hdvd (ZMod 3)).toMonoidHom x
  have h2 : 2 ∣ orderOf x := by rwa [hcast3, h2ord] at hmap
  -- (c) `3^k ∣ orderOf x` and `orderOf x ∣ 2·3^k`.
  have h3k : 3 ^ k ∣ orderOf x := hord2 ▸ orderOf_pow_dvd (x := x) 2
  have hupper : orderOf x ∣ 2 * 3 ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_mul, ← hord2, pow_orderOf_eq_one]
  have hco : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact Nat.dvd_antisymm hupper (Nat.Coprime.mul_dvd_of_dvd_of_dvd hco h2 h3k)

/-- The same, in `φ` form: KoalaBear is a primitive root modulo every power of three. -/
theorem orderOf_koalaBear_three_pow_eq_totient (k : ℕ) :
    orderOf ((koalaBear : ZMod (3 ^ (k + 1)))) = φ (3 ^ (k + 1)) := by
  rw [orderOf_koalaBear_three_pow, Nat.totient_prime_pow_succ Nat.prime_three]
  ring

/-- **The cross-check, as a term.** `ord₈₁(KB) = 54` again — this time as a corollary of the
general lifted theorem rather than by `decide`.  Two independent derivations of one statement:
the computation checks the lifting argument, and the lifting argument checks that the
computation was not an accident of `k = 3`. -/
theorem orderOf_koalaBear_mod81_of_lifting : orderOf ((koalaBear : ZMod 81)) = 54 := by
  have h := orderOf_koalaBear_three_pow 3
  norm_num at h
  exact h

private theorem koalaBear_not_dvd_prime_pow {r e : ℕ} (hr : r.Prime) (hlt : r < koalaBear)
    (h : koalaBear ∣ r ^ e) : False := by
  have h1 : koalaBear ∣ r := koalaBear_prime.dvd_of_dvd_pow h
  exact absurd (Nat.le_of_dvd hr.pos h1) (by omega)

theorem koalaBear_not_dvd_three_pow (k : ℕ) : ¬koalaBear ∣ 3 ^ k := fun h =>
  koalaBear_not_dvd_prime_pow Nat.prime_three (by rw [koalaBear_eq]; norm_num) h

theorem koalaBear_not_dvd_two_pow (k : ℕ) : ¬koalaBear ∣ 2 ^ k := fun h =>
  koalaBear_not_dvd_prime_pow Nat.prime_two (by rw [koalaBear_eq]; norm_num) h

/-- **Fact 2, general.** `Φ_{3^(k+1)}` is IRREDUCIBLE over `F_KB`, at every `k`. -/
theorem irreducible_cyclotomic_three_pow (k : ℕ) :
    Irreducible (cyclotomic (3 ^ (k + 1)) (ZMod koalaBear)) :=
  irreducible_cyclotomic_of_orderOf_eq_totient (koalaBear_not_dvd_three_pow (k + 1))
    (orderOf_koalaBear_three_pow_eq_totient k)

/-- **Fact 2, the headline instance.** `Φ₈₁` is irreducible over `F_KB`. -/
theorem irreducible_cyclotomic_81 : Irreducible (cyclotomic 81 (ZMod koalaBear)) := by
  have h := irreducible_cyclotomic_three_pow 3
  norm_num at h
  exact h

instance : Fact (Irreducible (cyclotomic 81 (ZMod koalaBear))) := ⟨irreducible_cyclotomic_81⟩

/-- `R_q := F_KB[X]/(Φ₈₁)` — the candidate lattice-commitment ring at conductor 81. -/
abbrev KBCyc81 : Type := AdjoinRoot (cyclotomic 81 (ZMod koalaBear))

/-- **The point.** `R_q = F_KB[X]/(Φ₈₁)` is a FIELD: every nonzero element is invertible, which
is the strongest possible answer to the invertibility question an extraction argument asks. -/
theorem KBCyc81_isField : IsField KBCyc81 := Field.toIsField _

/-- `R_q` has degree `54 = φ(81)` over `F_KB` — maximal inertia, one factor. -/
theorem KBCyc81_finrank : Module.finrank (ZMod koalaBear) KBCyc81 = 54 := by
  have hne : (cyclotomic 81 (ZMod koalaBear)) ≠ 0 := cyclotomic_ne_zero 81 _
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim hne,
    natDegree_cyclotomic, totient_81]

/-! ## 4. TOOTH A — the conductor is a constraint: KoalaBear kills every negacyclic ring

`X^(2^k) + 1 = Φ_{2^(k+1)}`, and `KB ≡ 1 (mod 2^(k+1))` for every `k + 1 ≤ 24` because
`KB − 1 = 2²⁴ · 127`.  So `ord = 1`: the ring `F_KB[X]/(X^(2^k)+1)` is a product of `2^k`
copies of `F_KB`.  Minimal inertia — the exact opposite of §3, over the SAME field. -/

/-- `Φ_{2^(k+1)} = X^(2^k) + 1`: the negacyclic ring *is* the `2^(k+1)`-st cyclotomic ring. -/
theorem cyclotomic_two_pow_succ (R : Type*) [CommRing R] (k : ℕ) :
    cyclotomic (2 ^ (k + 1)) R = X ^ 2 ^ k + 1 := by
  rw [cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  simp [Finset.sum_range_succ, add_comm]

/-- `KB ≡ 1 (mod 2^k)` for every `k ≤ 24`. -/
theorem koalaBear_cast_two_pow {k : ℕ} (hk : k ≤ 24) : ((koalaBear : ℕ) : ZMod (2 ^ k)) = 1 := by
  haveI : NeZero ((2 : ℕ) ^ k) := ⟨by positivity⟩
  have hdvd : (2 : ℕ) ^ k ∣ koalaBear - 1 :=
    dvd_trans (pow_dvd_pow 2 hk) ⟨127, koalaBear_sub_one⟩
  have hz : ((koalaBear - 1 : ℕ) : ZMod (2 ^ k)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  have hsucc : koalaBear - 1 + 1 = koalaBear := by rw [koalaBear_eq]
  calc ((koalaBear : ℕ) : ZMod (2 ^ k))
      = ((koalaBear - 1 + 1 : ℕ) : ZMod (2 ^ k)) := by rw [hsucc]
    _ = 0 + 1 := by rw [Nat.cast_add, hz, Nat.cast_one]
    _ = 1 := zero_add 1

/-- **Fact 3, the order.** `ord_{2^k}(KB) = 1` for every `k ≤ 24`. -/
theorem orderOf_koalaBear_two_pow {k : ℕ} (hk : k ≤ 24) :
    orderOf ((koalaBear : ZMod (2 ^ k))) = 1 := by
  rw [koalaBear_cast_two_pow hk]; exact orderOf_one

open UniqueFactorizationMonoid in
/-- **Fact 3a.** Every irreducible factor of `X^(2^k) + 1` over `F_KB` is LINEAR. -/
theorem natDegree_factor_negacyclic {k : ℕ} (hk : k + 1 ≤ 24) {P : (ZMod koalaBear)[X]}
    (hP : P ∈ normalizedFactors (X ^ 2 ^ k + 1 : (ZMod koalaBear)[X])) : P.natDegree = 1 := by
  rw [← cyclotomic_two_pow_succ] at hP
  rw [natDegree_of_mem_normalizedFactors (koalaBear_not_dvd_two_pow (k + 1)) hP,
    orderOf_koalaBear_two_pow hk]

open UniqueFactorizationMonoid in
/-- **Fact 3b.** `X^(2^k) + 1` has exactly `2^k` distinct monic irreducible factors over `F_KB`
— and since its degree is `2^k` and each factor is linear (3a), it splits completely into
distinct linear factors. -/
theorem card_factors_negacyclic {k : ℕ} (hk : k + 1 ≤ 24) :
    (normalizedFactors (X ^ 2 ^ k + 1 : (ZMod koalaBear)[X])).toFinset.card = 2 ^ k := by
  rw [← cyclotomic_two_pow_succ, card_normalizedFactors (koalaBear_not_dvd_two_pow (k + 1)),
    orderOf_koalaBear_two_pow hk, Nat.totient_prime_pow_succ Nat.prime_two]
  norm_num

/-- **Fact 3c, the tooth stated as a refusal.** For `k ≥ 1`, `X^(2^k) + 1` is NOT irreducible
over `F_KB`.  Contrast `irreducible_cyclotomic_three_pow`: same field, different conductor,
opposite verdict. -/
theorem not_irreducible_negacyclic {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ 24) :
    ¬Irreducible (X ^ 2 ^ k + 1 : (ZMod koalaBear)[X]) := by
  rw [← cyclotomic_two_pow_succ]
  refine not_irreducible_cyclotomic_of_orderOf_ne_totient (koalaBear_not_dvd_two_pow (k + 1)) ?_
  rw [orderOf_koalaBear_two_pow hk, Nat.totient_prime_pow_succ Nat.prime_two]
  have : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  omega

open UniqueFactorizationMonoid in
/-- A nonzero polynomial over a field whose every monic irreducible factor is linear SPLITS.
(Stated and proved here rather than routed through `X^q − X`: the divisibility chain
`Φ ∣ X^n − 1 ∣ X^(q−1) − 1 ∣ X^q − X` forces the kernel to stare at a degree-2130706433
polynomial, which it will not do.) -/
private theorem splits_of_normalizedFactors_linear {K : Type*} [Field K] [DecidableEq K]
    {f : K[X]} (hf : f ≠ 0) (h : ∀ P ∈ normalizedFactors f, P.natDegree ≤ 1) : Splits f := by
  obtain ⟨u, hu⟩ := prod_normalizedFactors hf
  rw [← hu]
  refine Splits.mul (Splits.multisetProd fun P hP => ?_) (IsUnit.splits u.isUnit)
  refine splits_of_natDegree_le_one_of_monic (h P hP) ?_
  have hP0 : P ≠ 0 := fun h0 => zero_notMem_normalizedFactors f (h0 ▸ hP)
  rw [← normalize_normalized_factor P hP]
  exact monic_normalize hP0

/-- **Fact 3d, `Splits` in Mathlib's own vocabulary.** `X^(2^k) + 1` splits completely over
`F_KB` for every `k + 1 ≤ 24` — a product of linear factors, no residue field bigger than
`F_KB` anywhere in the ring. -/
theorem splits_negacyclic {k : ℕ} (hk : k + 1 ≤ 24) :
    Splits (X ^ 2 ^ k + 1 : (ZMod koalaBear)[X]) := by
  refine splits_of_normalizedFactors_linear ?_ fun P hP =>
    (natDegree_factor_negacyclic hk hP).le
  rw [← cyclotomic_two_pow_succ]
  exact cyclotomic_ne_zero _ _

/-! ## 5. TOOTH B — the field is a constraint: at the SAME conductor 81, our other candidates fail

BabyBear (`ord₈₁ = 27`, two factors of degree 27) and Mersenne-31 (`ord₈₁ = 9`, six factors of
degree 9) both make `Φ₈₁` reducible.  Irreducibility at conductor 81 is a property of KoalaBear
specifically, not of "a 31-bit prime". -/

private theorem babyBear_not_dvd_81 : ¬babyBear ∣ 81 := by
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  rw [babyBear_eq] at this; omega

private theorem mersenne31_not_dvd_81 : ¬mersenne31 ∣ 81 := by
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  rw [mersenne31_eq] at this; omega

/-- `ord₈₁(BabyBear) = 27` — a proper divisor of `φ(81) = 54`. -/
theorem orderOf_babyBear_mod81 : orderOf ((babyBear : ZMod 81)) = 27 := by
  have hc : ((babyBear : ℕ) : ZMod 81) = 67 := by rw [babyBear_eq]; decide
  rw [hc]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) ?_
  intro q hq hqd
  rw [prime_dvd_three_pow (e := 3) hq (by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact hqd)]
  decide

/-- `ord₈₁(M31) = 9`. -/
theorem orderOf_mersenne31_mod81 : orderOf ((mersenne31 : ZMod 81)) = 9 := by
  have hc : ((mersenne31 : ℕ) : ZMod 81) = 64 := by rw [mersenne31_eq]; decide
  rw [hc]
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) ?_
  intro q hq hqd
  rw [prime_dvd_three_pow (e := 2) hq (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hqd)]
  decide

/-- **Tooth B₁.** `Φ₈₁` is NOT irreducible over BabyBear. -/
theorem not_irreducible_cyclotomic_81_babyBear :
    ¬Irreducible (cyclotomic 81 (ZMod babyBear)) := by
  refine not_irreducible_cyclotomic_of_orderOf_ne_totient babyBear_not_dvd_81 ?_
  rw [orderOf_babyBear_mod81, totient_81]
  norm_num

/-- **Tooth B₂.** `Φ₈₁` is NOT irreducible over Mersenne-31. -/
theorem not_irreducible_cyclotomic_81_mersenne31 :
    ¬Irreducible (cyclotomic 81 (ZMod mersenne31)) := by
  refine not_irreducible_cyclotomic_of_orderOf_ne_totient mersenne31_not_dvd_81 ?_
  rw [orderOf_mersenne31_mod81, totient_81]
  norm_num

open UniqueFactorizationMonoid in
/-- BabyBear: `Φ₈₁` splits into exactly **2** irreducible factors over `F_BabyBear`. -/
theorem card_factors_81_babyBear :
    (normalizedFactors (cyclotomic 81 (ZMod babyBear))).toFinset.card = 2 := by
  rw [card_normalizedFactors babyBear_not_dvd_81, orderOf_babyBear_mod81, totient_81]

open UniqueFactorizationMonoid in
/-- Mersenne-31: `Φ₈₁` splits into exactly **6** irreducible factors over `F_M31`. -/
theorem card_factors_81_mersenne31 :
    (normalizedFactors (cyclotomic 81 (ZMod mersenne31))).toFinset.card = 6 := by
  rw [card_normalizedFactors mersenne31_not_dvd_81, orderOf_mersenne31_mod81, totient_81]

open UniqueFactorizationMonoid in
/-- KoalaBear at conductor 81: exactly **1** factor.  The three counts `1 / 2 / 6` at one
conductor are the whole comparison in one line. -/
theorem card_factors_81_koalaBear :
    (normalizedFactors (cyclotomic 81 (ZMod koalaBear))).toFinset.card = 1 := by
  rw [card_normalizedFactors (by simpa using koalaBear_not_dvd_three_pow 4 : ¬koalaBear ∣ 81),
    orderOf_koalaBear_mod81, totient_81]

/-! ## 6. Axiom pins -/

/-- info: 'Minidregg.Theory.CyclotomicInertia.koalaBear_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms koalaBear_prime
/-- info: 'Minidregg.Theory.CyclotomicInertia.orderOf_koalaBear_mod81' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderOf_koalaBear_mod81
/-- info: 'Minidregg.Theory.CyclotomicInertia.orderOf_koalaBear_three_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderOf_koalaBear_three_pow
/-- info: 'Minidregg.Theory.CyclotomicInertia.orderOf_koalaBear_mod81_of_lifting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderOf_koalaBear_mod81_of_lifting
/-- info: 'Minidregg.Theory.CyclotomicInertia.irreducible_cyclotomic_three_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms irreducible_cyclotomic_three_pow
/-- info: 'Minidregg.Theory.CyclotomicInertia.irreducible_cyclotomic_81' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms irreducible_cyclotomic_81
/-- info: 'Minidregg.Theory.CyclotomicInertia.KBCyc81_isField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KBCyc81_isField
/-- info: 'Minidregg.Theory.CyclotomicInertia.KBCyc81_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms KBCyc81_finrank
/-- info: 'Minidregg.Theory.CyclotomicInertia.natDegree_factor_negacyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natDegree_factor_negacyclic
/-- info: 'Minidregg.Theory.CyclotomicInertia.card_factors_negacyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_factors_negacyclic
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_irreducible_negacyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_irreducible_negacyclic
/-- info: 'Minidregg.Theory.CyclotomicInertia.splits_negacyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms splits_negacyclic
/-- info: 'Minidregg.Theory.CyclotomicInertia.orderOf_babyBear_mod81' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderOf_babyBear_mod81
/-- info: 'Minidregg.Theory.CyclotomicInertia.orderOf_mersenne31_mod81' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderOf_mersenne31_mod81
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_irreducible_cyclotomic_81_babyBear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_irreducible_cyclotomic_81_babyBear
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_irreducible_cyclotomic_81_mersenne31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_irreducible_cyclotomic_81_mersenne31
/-- info: 'Minidregg.Theory.CyclotomicInertia.card_factors_81_koalaBear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_factors_81_koalaBear
/-- info: 'Minidregg.Theory.CyclotomicInertia.card_factors_81_babyBear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_factors_81_babyBear
/-- info: 'Minidregg.Theory.CyclotomicInertia.card_factors_81_mersenne31' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_factors_81_mersenne31

end Minidregg.Theory.CyclotomicInertia
