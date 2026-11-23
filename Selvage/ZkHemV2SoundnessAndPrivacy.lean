/-
# Selvage.ZkHemV2SoundnessAndPrivacy — `dregg-sig` zk-Hem v2: quintic Goldilocks, Frobenius-orbit
# blinder rank, mask-line HVZK and the integer millibit ledger

Statement-first companion to `dregg-sig/crates/agg/SECURITY.md` §V2 (read-only source, working
tree of 2026-11-22). Every theorem below is checked by the Lean kernel; nothing here is a claim
about the Rust implementation beyond the integer arithmetic it models (§6), which the
standalone differential crate `zkml-research/research/wave11_frontier_upgrades_2026_11_22/
zkhem_v2_closure/` checks bit-for-bit against a port of `zk_hem::v2::bounds`.

The field and orbit results support Lemma V2.2. The scalar line is Lemma V2.4.
The conditional ledger covers the canonical no-lookup sizes. The Rust calculator selects
the agreements and the weakest round. Lean recomputes the Stage-0 query, mask and work bounds.
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum.Prime

namespace Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy

open Polynomial Module
open scoped IntermediateField

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1. Goldilocks and `QuinticGoldilocks = F_p[X]/(X^5 - 3)` -/

/-- `p_GL = 2^64 - 2^32 + 1`. -/
def pGL : ℕ := 18446744069414584321

theorem pGL_eq : pGL = 2 ^ 64 - 2 ^ 32 + 1 := by norm_num [pGL]

abbrev FpGL := ZMod pGL

/-- Binary square-and-multiply in `FpGL` (`64` kernel steps under `decide`). -/
def powFuel : ℕ → FpGL → ℕ → FpGL
  | 0, _, _ => 1
  | fuel + 1, a, e =>
    if e = 0 then 1
    else
      let half := powFuel fuel (a * a) (e / 2)
      if e % 2 = 1 then a * half else half

theorem powFuel_eq_pow (fuel : ℕ) :
    ∀ (a : FpGL) (e : ℕ), e < 2 ^ fuel → powFuel fuel a e = a ^ e := by
  induction fuel with
  | zero =>
    intro a e he; have he0 : e = 0 := by omega
    subst he0; simp [powFuel]
  | succ fuel ih =>
    intro a e he; rw [pow_succ] at he
    by_cases he0 : e = 0
    · subst he0; simp [powFuel]
    · have hrec := ih (a * a) (e / 2) (by omega)
      have hsq : (a * a) ^ (e / 2) = a ^ (2 * (e / 2)) := by rw [← sq, ← pow_mul]
      by_cases hodd : e % 2 = 1
      · simp only [powFuel, he0, ↓reduceIte, hodd, hrec, hsq, ← pow_succ']; congr 1; omega
      · simp only [powFuel, he0, ↓reduceIte, hodd, hrec, hsq]; congr 1; omega

private theorem prime_dvd_pGL_pred {q : ℕ} (hq : q.Prime) (hdvd : q ∣ pGL - 1) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
  have hfac : pGL - 1 = 2 ^ 32 * (3 * (5 * (17 * (257 * 65537)))) := by norm_num [pGL]
  rw [hfac] at hdvd
  have e : ∀ r : ℕ, r.Prime → q ∣ r → q = r := fun r hr h => (Nat.prime_dvd_prime_iff_eq hq hr).mp h
  rcases hq.dvd_mul.mp hdvd with h | h
  · exact Or.inl (e 2 Nat.prime_two (hq.dvd_of_dvd_pow h))
  rcases hq.dvd_mul.mp h with h | h
  · exact Or.inr <| Or.inl (e 3 (by norm_num) h)
  rcases hq.dvd_mul.mp h with h | h
  · exact Or.inr <| Or.inr <| Or.inl (e 5 (by norm_num) h)
  rcases hq.dvd_mul.mp h with h | h
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (e 17 (by norm_num) h)
  rcases hq.dvd_mul.mp h with h | h
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (e 257 (by norm_num) h)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (e 65537 (by norm_num) h)

private theorem seven_lucas_checks :
    powFuel 64 7 (pGL - 1) = 1 ∧ powFuel 64 7 ((pGL - 1) / 2) ≠ 1 ∧
    powFuel 64 7 ((pGL - 1) / 3) ≠ 1 ∧ powFuel 64 7 ((pGL - 1) / 5) ≠ 1 ∧
    powFuel 64 7 ((pGL - 1) / 17) ≠ 1 ∧ powFuel 64 7 ((pGL - 1) / 257) ≠ 1 ∧
    powFuel 64 7 ((pGL - 1) / 65537) ≠ 1 := by decide

/-- `p_GL` is prime (Lucas certificate at the primitive root `7`). -/
theorem pGL_prime : Nat.Prime pGL := by
  have hc := seven_lucas_checks
  apply lucas_primality pGL (7 : FpGL)
  · rw [← powFuel_eq_pow 64 7 (pGL - 1) (by norm_num [pGL])]; exact hc.1
  · intro q hq hdvd
    rcases prime_dvd_pGL_pred hq hdvd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [← powFuel_eq_pow 64 7 _ (by norm_num [pGL])]
    exacts [hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2]

instance pGL_fact : Fact (Nat.Prime pGL) := ⟨pGL_prime⟩

/-- `5 ∣ p_GL - 1`, so `F_p` holds the fifth roots of unity and Kummer theory applies. -/
theorem five_dvd_pGL_pred : 5 ∣ pGL - 1 := by decide

/-- The Frobenius constant of `field5.rs:30-32`: `3^((p-1)/5) = 1_041_288_259_238_279_555 ≠ 1`. -/
theorem three_pow_quintic_eq_zeta :
    (3 : FpGL) ^ ((pGL - 1) / 5) = 1041288259238279555 := by
  rw [← powFuel_eq_pow 64 3 _ (by norm_num [pGL])]; decide

theorem three_pow_quintic_ne_one : (3 : FpGL) ^ ((pGL - 1) / 5) ≠ 1 := by
  rw [three_pow_quintic_eq_zeta]; decide

/-- `3` is not a fifth power in `F_p` (Euler criterion for degree `5`). -/
theorem three_not_fifth_power (b : FpGL) : b ^ 5 ≠ 3 := by
  intro h
  have hb : b ≠ 0 := by
    rintro rfl; exact absurd h (by decide)
  apply three_pow_quintic_ne_one
  rw [← h, ← pow_mul, show 5 * ((pGL - 1) / 5) = pGL - 1 by norm_num [pGL]]
  exact ZMod.pow_card_sub_one_eq_one hb

noncomputable section Quintic

/-- The defining binomial of `v2/field5.rs` (`FP5_W = 3`). -/
def quinticPoly : FpGL[X] := X ^ 5 - C 3

/-- **`X^5 - 3` is irreducible over `F_p`** (Kummer, prime degree `5`). -/
theorem quinticGoldilocks_irreducible : Irreducible quinticPoly :=
  X_pow_sub_C_irreducible_of_prime (by norm_num) three_not_fifth_power

instance quinticPoly_fact : Fact (Irreducible quinticPoly) := ⟨quinticGoldilocks_irreducible⟩

abbrev QuinticGoldilocks := AdjoinRoot quinticPoly

theorem quintic_finrank : finrank FpGL QuinticGoldilocks = 5 := by
  change finrank FpGL (FpGL[X] ⧸ Ideal.span {quinticPoly}) = 5
  rw [finrank_quotient_span_eq_natDegree]; simp [quinticPoly]

instance : Module.Finite FpGL QuinticGoldilocks :=
  Module.finite_of_finrank_pos (by rw [quintic_finrank]; norm_num)

instance : Finite QuinticGoldilocks := Module.finite_of_finite FpGL

theorem quintic_natCard : Nat.card QuinticGoldilocks = pGL ^ 5 := by
  rw [Module.natCard_eq_pow_finrank (K := FpGL), quintic_finrank, Nat.card_zmod]

set_option exponentiation.threshold 512 in
/-- `|E| = p^5 > 2^319` (the `FIELD_MILLIBITS = 319_998` budget of `v2/bounds.rs`). -/
theorem quintic_card_gt_two_pow_319 : 2 ^ 319 < Nat.card QuinticGoldilocks := by
  rw [quintic_natCard]; decide

end Quintic

/-- In an extension of prime degree every intermediate field is `⊥` or `⊤`. -/
theorem intermediateField_eq_bot_or_top {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] (hp : (finrank K E).Prime) (M : IntermediateField K E) :
    M = ⊥ ∨ M = ⊤ := by
  have htow := Module.finrank_mul_finrank K M E
  rcases (Nat.dvd_prime hp).mp (Dvd.intro _ htow) with h1 | h5
  · exact Or.inl (IntermediateField.finrank_eq_one_iff.mp h1)
  · exact Or.inr (IntermediateField.eq_of_le_of_finrank_eq le_top
      (by rw [h5, IntermediateField.finrank_top']))

/-- **`QuinticGoldilocks` has no proper intermediate field** (`[E : F_p] = 5` is prime). -/
theorem quintic_no_proper_intermediate_field (M : IntermediateField FpGL QuinticGoldilocks) :
    M = ⊥ ∨ M = ⊤ :=
  intermediateField_eq_bot_or_top (by rw [quintic_finrank]; norm_num) M

/-- A point outside the base field of a prime-degree extension has minimal polynomial of
full degree `[E : K]`. -/
theorem minpoly_natDegree_of_not_base {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] (hp : (finrank K E).Prime) {z : E}
    (hz : z ∉ Set.range (algebraMap K E)) : (minpoly K z).natDegree = finrank K E := by
  have hint : IsIntegral K z := .of_finite K z
  rw [← IntermediateField.adjoin.finrank hint]
  rcases intermediateField_eq_bot_or_top hp K⟮z⟯ with h | h
  · exact absurd (IntermediateField.mem_bot.mp (h ▸ IntermediateField.mem_adjoin_simple_self K z)) hz
  · rw [h, IntermediateField.finrank_top']

/-! ## §2. Odd norm index: base-coset disjointness of `2^s`-powers -/

theorem pow_five_sub_one_factor {p : ℕ} (hp : 1 ≤ p) :
    p ^ 5 - 1 = (p - 1) * (p ^ 4 + p ^ 3 + p ^ 2 + p + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Nat.sub_eq_of_eq_add
  ring

/-- **The norm index `(p^5 - 1)/(p - 1) = p^4 + p^3 + p^2 + p + 1` is odd** for odd `p`. -/
theorem norm_index_odd {p : ℕ} (hp : Odd p) : ¬ 2 ∣ p ^ 4 + p ^ 3 + p ^ 2 + p + 1 := by
  have h1 : p % 2 = 1 := Nat.odd_iff.mp hp
  rw [Nat.dvd_iff_mod_eq_zero]
  simp [Nat.add_mod, Nat.pow_mod, h1]

theorem gcd_two_pow_mul_pred {p : ℕ} (hp : Odd p) (s : ℕ) :
    Nat.gcd (2 ^ s * (p - 1)) (p ^ 5 - 1) = p - 1 := by
  rw [pow_five_sub_one_factor hp.pos, mul_comm (2 ^ s), Nat.gcd_mul_left]
  have hcop : Nat.Coprime (2 ^ s) (p ^ 4 + p ^ 3 + p ^ 2 + p + 1) :=
    Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (norm_index_odd hp))
  rw [Nat.Coprime.gcd_eq_one hcop, mul_one]

/-- **Base-coset disjointness, abstract form.** In a field of `p^5` elements with `p` odd, if
`z^(2^s)` is fixed by `x ↦ x^p` then so is `z`. -/
theorem frobFixed_of_two_pow_frobFixed {p : ℕ} {E : Type*} [Field E] [Fintype E]
    (hcard : Fintype.card E = p ^ 5) (hp : Odd p) (s : ℕ) (z : E)
    (h : (z ^ 2 ^ s) ^ p = z ^ 2 ^ s) : z ^ p = z := by
  have hp0 : p ≠ 0 := by rintro rfl; exact absurd hp (by decide)
  by_cases hz : z = 0
  · subst hz; exact zero_pow hp0
  have hy : z ^ 2 ^ s ≠ 0 := pow_ne_zero _ hz
  have hy1 : (z ^ 2 ^ s) ^ (p - 1) = 1 := by
    have : (z ^ 2 ^ s) ^ (p - 1) * z ^ 2 ^ s = 1 * z ^ 2 ^ s := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, h]
    exact mul_right_cancel₀ hy this
  have hA : z ^ (2 ^ s * (p - 1)) = 1 := by rw [pow_mul]; exact hy1
  have hB : z ^ (p ^ 5 - 1) = 1 := by rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one z hz
  have hC : z ^ (p - 1) = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hA, hB⟩
    rwa [gcd_two_pow_mul_pred hp s] at this
  calc z ^ p = z ^ (p - 1) * z := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    _ = z := by rw [hC, one_mul]

section FrobIter

variable {M : Type*} [Monoid M] {p : ℕ}

/-- Frobenius iterates: if `z^(p^a) = z` then `z^(p^(a+b)) = z^(p^b)`. -/
theorem frob_add_of_fixed {z : M} {a : ℕ} (ha : z ^ p ^ a = z) (b : ℕ) :
    z ^ p ^ (a + b) = z ^ p ^ b := by
  rw [pow_add, pow_mul, ha]

theorem frob_mul_of_fixed {z : M} {c : ℕ} (hc : z ^ p ^ c = z) (n : ℕ) :
    z ^ p ^ (c * n) = z := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, add_comm, frob_add_of_fixed hc, ih]

/-- With `z^(p^5) = z`, any nontrivial period `0 < c < 5` collapses to `z^p = z`. -/
theorem frob_period_collapse {z : M} (h5 : z ^ p ^ 5 = z) {c : ℕ} (hc0 : 0 < c) (hc5 : c < 5)
    (hc : z ^ p ^ c = z) : z ^ p = z := by
  have key : ∀ n q : ℕ, c * n = 5 * q + 1 → z ^ p = z := fun n q hnq => by
    have h1 := frob_add_of_fixed (frob_mul_of_fixed h5 q) 1
    rw [← hnq, frob_mul_of_fixed hc n, pow_one] at h1
    exact h1.symm
  interval_cases c
  · simpa using hc
  · exact key 3 1 rfl
  · exact key 2 1 rfl
  · exact key 4 3 rfl

theorem frob_mod_five {z : M} (h5 : z ^ p ^ 5 = z) (n : ℕ) : z ^ p ^ n = z ^ p ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5]
  exact frob_add_of_fixed (frob_mul_of_fixed h5 _) _

end FrobIter

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] {E : Type*} [Field E] [Algebra (ZMod p) E]

/-- The base field is exactly the Frobenius-fixed set (`field5.rs::is_base` docstring). -/
theorem mem_range_of_pow_char_eq {z : E} (h : z ^ p = z) :
    z ∈ Set.range (algebraMap (ZMod p) E) := by
  classical
  by_contra hz
  have hp1 : 1 < p := hp.out.one_lt
  set f : E[X] := X ^ p - X with hf
  have hdeg : f.natDegree = p := by
    rw [hf, natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hp1]
  have hf0 : f ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hdeg; omega
  have hroot : ∀ x : E, x ^ p = x → x ∈ f.roots := fun x hx => by
    rw [mem_roots hf0]; simp [hf, hx]
  let S : Finset E := insert z (Finset.univ.image (algebraMap (ZMod p) E))
  have hsub : S.val ⊆ f.roots := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hroot _ h
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  have hnot : z ∉ Finset.univ.image (algebraMap (ZMod p) E) := by
    intro hmem; obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hmem; exact hz ⟨a, rfl⟩
  have hcardS : S.card = p + 1 := by
    rw [Finset.card_insert_of_notMem hnot,
      Finset.card_image_of_injective _ (algebraMap (ZMod p) E).injective, Finset.card_univ,
      ZMod.card]
  have := card_le_degree_of_subset_roots hsub
  omega

theorem pow_char_eq_of_mem_range {z : E} (h : z ∈ Set.range (algebraMap (ZMod p) E)) :
    z ^ p = z := by
  obtain ⟨a, rfl⟩ := h; rw [← map_pow, ZMod.pow_card]

theorem charP_of_zmod_algebra : CharP E p :=
  charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p

/-- Frobenius commutes with evaluation of base-field polynomials: `B(z^p) = B(z)^p`. -/
theorem aeval_pow_char (f : (ZMod p)[X]) (z : E) : aeval (z ^ p) f = aeval z f ^ p := by
  have := charP_of_zmod_algebra (p := p) (E := E)
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_pow_char]
  | monomial n a =>
    rw [aeval_monomial, aeval_monomial, mul_pow, ← map_pow (algebraMap (ZMod p) E) a p,
      ZMod.pow_card, ← pow_mul, ← pow_mul, mul_comm p n]

theorem aeval_pow_char_pow (f : (ZMod p)[X]) (z : E) (k : ℕ) :
    aeval (z ^ p ^ k) f = aeval z f ^ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, aeval_pow_char, ih, ← pow_mul]

end Frobenius

/-- **`quintic_nonbase_pow_two_not_in_base`.** For every `z ∈ F_{p^5} \ F_p` and every `s`,
`z^(2^s) ∉ F_p`: the first clause of (G2) in `SECURITY.md` V2.1 is equivalent to
`omega_j ∉ F_p`, and `{x : x^(2^s) ∈ F_p}` is exactly `F_p` (`p` points, not
`2^s (p - 1) + 1`). -/
theorem quintic_nonbase_pow_two_not_in_base (s : ℕ) (z : QuinticGoldilocks)
    (hz : z ∉ Set.range (algebraMap FpGL QuinticGoldilocks)) :
    z ^ 2 ^ s ∉ Set.range (algebraMap FpGL QuinticGoldilocks) := by
  rintro ⟨a, ha⟩
  apply hz
  apply mem_range_of_pow_char_eq
  have := Fintype.ofFinite QuinticGoldilocks
  refine frobFixed_of_two_pow_frobFixed (p := pGL) ?_ ⟨pGL / 2, by norm_num [pGL]⟩ s z ?_
  · rw [Fintype.card_eq_nat_card, quintic_natCard]
  · rw [← ha, ← map_pow, ZMod.pow_card]

/-- Every `2^s`-th root of unity of `QuinticGoldilocks` lies in `F_p` (`v_2(p^5 - 1) = 32`):
hence `x^(2^s) = σ^i(y^(2^s))` has at most `2^s` solutions `x`, as `SECURITY.md` V2.1 counts. -/
theorem quintic_two_pow_roots_of_unity_in_base (s : ℕ) (ζ : QuinticGoldilocks)
    (h : ζ ^ 2 ^ s = 1) : ζ ∈ Set.range (algebraMap FpGL QuinticGoldilocks) := by
  apply mem_range_of_pow_char_eq
  have := Fintype.ofFinite QuinticGoldilocks
  exact frobFixed_of_two_pow_frobFixed (p := pGL) (by rw [Fintype.card_eq_nat_card, quintic_natCard])
    ⟨pGL / 2, by norm_num [pGL]⟩ s ζ (by rw [h, one_pow])

/-! ## §3. Lemma V2.2: Frobenius-orbit blinder rank and its teeth -/

section BlinderRank

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

/-- The `K`-linear evaluation of a blinder `B ∈ K[X]_{<n}` at `m` points of `E`. -/
noncomputable def oodEval (n : ℕ) {m : ℕ} (z : Fin m → E) : degreeLT K n →ₗ[K] (Fin m → E) where
  toFun B i := aeval (z i) (B : K[X])
  map_add' B C := by ext i; simp
  map_smul' c B := by ext i; simp

theorem oodEval_apply (n : ℕ) {m : ℕ} (z : Fin m → E) (B : degreeLT K n) (i : Fin m) :
    oodEval n z B i = aeval (z i) (B : K[X]) := rfl

theorem finrank_degreeLT (n : ℕ) : finrank K (degreeLT K n) = n :=
  (degreeLTEquiv K n).finrank_eq.trans (Module.finrank_fin_fun K)

/-- Vanishing on `n` distinct points of `E` kills every `B ∈ K[X]` of degree `< n`. -/
theorem eq_zero_of_vanish_distinct {n : ℕ} (B : K[X]) (hB : B.degree < n) {ι : Type*}
    [Fintype ι] (hcard : Fintype.card ι = n) (w : ι → E) (hw : Function.Injective w)
    (hv : ∀ i, aeval (w i) B = 0) : B = 0 := by
  classical
  by_contra hne
  have hmap : B.map (algebraMap K E) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K E).injective).mpr hne
  have hsub : (Finset.univ.image w).val ⊆ (B.map (algebraMap K E)).roots := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    rw [mem_roots hmap, IsRoot, eval_map, ← aeval_def, hv]
  have h1 := card_le_degree_of_subset_roots hsub
  rw [Finset.card_image_of_injective _ hw, Finset.card_univ, hcard, natDegree_map] at h1
  have h2 : B.natDegree < n := (natDegree_lt_iff_degree_lt hne).mpr hB
  omega

/-- **SmallWood+ (`2026/2880`) Lemma 1, linear-algebra form (`insufficient_base_blinders_leak`).**
Fewer than `[E : K]` base-field blinders can never make an `E`-valued view uniform: no `K`-linear
map from `K^k`, `k < [E : K]`, onto `E` exists. -/
theorem insufficient_base_blinders_leak [FiniteDimensional K E] {k : ℕ} (hk : k < finrank K E)
    (f : (Fin k → K) →ₗ[K] E) : ¬ Function.Surjective f := by
  intro hs
  have h1 := LinearMap.finrank_range_le f
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_fin_fun] at h1
  omega

end BlinderRank

theorem quintic_insufficient_blinders {k : ℕ} (hk : k < 5)
    (f : (Fin k → FpGL) →ₗ[FpGL] QuinticGoldilocks) : ¬ Function.Surjective f :=
  insufficient_base_blinders_leak (by rw [quintic_finrank]; exact hk) f

section OrbitRank

variable {p : ℕ} [hp : Fact p.Prime] {E : Type*} [Field E] [Fintype E] [Algebra (ZMod p) E]

/-- Under distinct Frobenius orbits the `5m` conjugates `z_i^(p^k)` are pairwise distinct. -/
theorem orbit_points_injective (hcard : Fintype.card E = p ^ 5) {m : ℕ} (z : Fin m → E)
    (hbase : ∀ i, z i ∉ Set.range (algebraMap (ZMod p) E))
    (horb : ∀ i j, i ≠ j → ∀ k < 5, z j ≠ z i ^ p ^ k) :
    Function.Injective (fun x : Fin m × Fin 5 => z x.1 ^ p ^ (x.2 : ℕ)) := by
  have h5 : ∀ w : E, w ^ p ^ 5 = w := fun w => by rw [← hcard]; exact FiniteField.pow_card w
  rintro ⟨i, a⟩ ⟨j, b⟩ hab
  simp only at hab
  have hb5 : (b : ℕ) ≤ 5 := by omega
  have e1 : (z i ^ p ^ (a : ℕ)) ^ p ^ (5 - (b : ℕ)) = z i ^ p ^ ((a : ℕ) + (5 - b)) := by
    rw [← pow_mul, ← pow_add]
  have e2 : (z j ^ p ^ (b : ℕ)) ^ p ^ (5 - (b : ℕ)) = z j := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hb5, h5]
  have e3 : z i ^ p ^ ((a : ℕ) + (5 - b)) = z j := by rw [← e1, hab, e2]
  have key : z j = z i ^ p ^ (((a : ℕ) + (5 - b)) % 5) := by
    rw [← e3]; exact frob_mod_five (h5 _) _
  by_cases hij : i = j
  · subst hij
    by_cases hr : ((a : ℕ) + (5 - b)) % 5 = 0
    · have hab' : (a : ℕ) = b := by omega
      exact Prod.ext rfl (Fin.ext hab')
    · exact absurd (mem_range_of_pow_char_eq (frob_period_collapse (h5 _) (Nat.pos_of_ne_zero hr)
        (Nat.mod_lt _ (by norm_num)) key.symm)) (hbase i)
  · exact absurd key (horb i j hij _ (Nat.mod_lt _ (by norm_num)))

/-- **Lemma V2.2, interpolation form (`distinct_frobenius_orbits_full_rank_5m`).** Let
`[E : F_p] = 5` and `z_0..z_{m-1} ∈ E \ F_p` with pairwise distinct Frobenius orbits (the check
`z_i^(p^k) ≠ z_j`, `k = 0..4`, of `v2/pcs.rs::mask_points_good`). Evaluation of base-field
blinders of degree `< 5m` at the `z_i` is an `F_p`-linear **bijection** onto `E^m`: uniform
blinders give a uniform view (rank `5m`). -/
theorem distinct_frobenius_orbits_full_rank_5m (hfr : finrank (ZMod p) E = 5) {m : ℕ}
    (z : Fin m → E) (hbase : ∀ i, z i ∉ Set.range (algebraMap (ZMod p) E))
    (horb : ∀ i j, i ≠ j → ∀ k < 5, z j ≠ z i ^ p ^ k) :
    Function.Bijective (oodEval (K := ZMod p) (5 * m) z) := by
  have hcard : Fintype.card E = p ^ 5 := by
    rw [Module.card_eq_pow_finrank (K := ZMod p) (V := E), ZMod.card, hfr]
  have hinj : Function.Injective (oodEval (K := ZMod p) (5 * m) z) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro B hB
    apply Subtype.ext
    refine eq_zero_of_vanish_distinct (K := ZMod p) B.1 (mem_degreeLT.mp B.2)
      (ι := Fin m × Fin 5) (by simp [mul_comm]) _ (orbit_points_injective hcard z hbase horb) ?_
    rintro ⟨i, k⟩
    have hi : aeval (z i) (B : (ZMod p)[X]) = 0 := by
      simpa [oodEval_apply] using congrFun hB i
    simp only
    rw [aeval_pow_char_pow, hi, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  refine ⟨hinj, ?_⟩
  have : FiniteDimensional (ZMod p) (degreeLT (ZMod p) (5 * m)) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv _ _).symm
  rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  rw [finrank_degreeLT, Module.finrank_pi_fintype]
  simp [hfr, mul_comm]

omit [Fintype E] in
/-- **Tooth (`frobenius_conjugate_ood_rank_collapse`).** If two OOD points are Frobenius
conjugate, `z_j = z_i^(p^k)`, the view obeys `B(z_j) = B(z_i)^(p^k)` for *every* base-field
blinder `B`, so no number `n` of blinders makes it surjective (in degree five the rank is `≤ 5(m-1)`; the differential
crate measures `25 → 20` at `m = 5`). -/
theorem frobenius_conjugate_ood_rank_collapse (n : ℕ) {m : ℕ} (z : Fin m → E) {i j : Fin m}
    (hij : i ≠ j) {k : ℕ} (hconj : z j = z i ^ p ^ k) :
    ¬ Function.Surjective (oodEval (K := ZMod p) n z) := by
  classical
  intro hs
  obtain ⟨B, hB⟩ := hs (Pi.single j 1)
  have hBj : aeval (z j) (B : (ZMod p)[X]) = 1 := by
    simpa [oodEval_apply] using congrFun hB j
  have hBi : aeval (z i) (B : (ZMod p)[X]) = 0 := by
    simpa [oodEval_apply, Pi.single_apply, hij] using congrFun hB i
  rw [hconj, aeval_pow_char_pow, hBi, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at hBj
  exact zero_ne_one hBj

omit [Fintype E] in
/-- A base-field OOD point is a tooth too: its value is fixed by Frobenius, so the view
`(B(z))` misses every non-base target. -/
theorem base_ood_point_not_surjective (n : ℕ) {m : ℕ} (z : Fin m → E) (i : Fin m)
    (hb : z i ∈ Set.range (algebraMap (ZMod p) E)) (t : E)
    (ht : t ∉ Set.range (algebraMap (ZMod p) E)) :
    ∀ B : degreeLT (ZMod p) n, oodEval n z B i ≠ t := by
  intro B hB
  apply ht
  apply mem_range_of_pow_char_eq
  rw [← hB, oodEval_apply, ← aeval_pow_char, pow_char_eq_of_mem_range hb]

/-- **Fiber bridge (the obligation `SECURITY.md` V2.6 leaves open).** For `s` folds the
Stage-0 residues are read through the `2^s` roots `w_(j,l)` of `x^(2^s) = z_j`. If the `z_j`
are non-base and pairwise non-conjugate and the roots over each `z_j` are distinct, the
`t * 2^s` roots satisfy the hypotheses of `distinct_frobenius_orbits_full_rank_5m`. -/
theorem fiber_roots_distinct_orbits (hcard : Fintype.card E = p ^ 5) (s : ℕ) {t : ℕ}
    (zs : Fin t → E) (hbase : ∀ j, zs j ∉ Set.range (algebraMap (ZMod p) E))
    (horb : ∀ i j, i ≠ j → ∀ k < 5, zs j ≠ zs i ^ p ^ k)
    (w : Fin t × Fin (2 ^ s) → E) (hw : ∀ x, w x ^ 2 ^ s = zs x.1)
    (hdist : ∀ j (l l' : Fin (2 ^ s)), l ≠ l' → w (j, l) ≠ w (j, l')) :
    (∀ x, w x ∉ Set.range (algebraMap (ZMod p) E)) ∧
      (∀ x y, x ≠ y → ∀ k < 5, w y ≠ w x ^ p ^ k) := by
  have h5 : ∀ v : E, v ^ p ^ 5 = v := fun v => by rw [← hcard]; exact FiniteField.pow_card v
  refine ⟨fun x hx => hbase x.1 ?_, fun x y hxy k hk hyx => ?_⟩
  · obtain ⟨a, ha⟩ := hx
    exact ⟨a ^ 2 ^ s, by rw [map_pow, ha, hw]⟩
  · have hz : zs y.1 = zs x.1 ^ p ^ k := by
      rw [← hw y, hyx, ← hw x, ← pow_mul, ← pow_mul, mul_comm]
    by_cases hj : x.1 = y.1
    · rw [← hj] at hz
      by_cases hk0 : k = 0
      · subst hk0
        obtain ⟨j, l⟩ := x; obtain ⟨j', l'⟩ := y
        simp only at hj; subst hj
        have hl : l ≠ l' := fun h => hxy (by rw [h])
        exact hdist j l l' hl (by simpa using hyx.symm)
      · exact hbase x.1 (mem_range_of_pow_char_eq
          (frob_period_collapse (h5 _) (Nat.pos_of_ne_zero hk0) hk hz.symm))
    · exact horb x.1 y.1 hj k hk hz

end OrbitRank

/-- **Lemma V2.2 at the v2 field (`m = 5` OOD points, `25` blinders per fiber point).** For
`QuinticGoldilocks`, five non-base OOD points that pass `mask_points_good` give a full-rank
`25 × 25` base-field evaluation map. -/
theorem quintic_full_rank_5m {m : ℕ} (z : Fin m → QuinticGoldilocks)
    (hbase : ∀ i, z i ∉ Set.range (algebraMap FpGL QuinticGoldilocks))
    (horb : ∀ i j, i ≠ j → ∀ k < 5, z j ≠ z i ^ pGL ^ k) :
    Function.Bijective (oodEval (K := FpGL) (5 * m) z) := by
  have := Fintype.ofFinite QuinticGoldilocks
  exact distinct_frobenius_orbits_full_rank_5m (p := pGL) quintic_finrank z hbase horb

/-- The orbit predicates of `mask_points_good` from `v2/pcs.rs:731-738` (on `z_j = ω_j^(2^s)`). -/
def maskPointsGood {m : ℕ} (z : Fin m → QuinticGoldilocks) : Prop :=
  (∀ i, z i ∉ Set.range (algebraMap FpGL QuinticGoldilocks)) ∧
    ∀ i j : Fin m, j < i → ∀ k < 5, z i ^ pGL ^ k ≠ z j

/-- `mask_points_good` (which tests only `j < i`) implies the symmetric orbit hypothesis: the
dregg-sig guard already enforces the Frobenius-conjugacy condition of Lemma V2.2. -/
theorem maskPointsGood_full_rank {m : ℕ} (z : Fin m → QuinticGoldilocks) (h : maskPointsGood z) :
    Function.Bijective (oodEval (K := FpGL) (5 * m) z) := by
  refine quintic_full_rank_5m z h.1 fun i j hij k hk hzj => ?_
  have := Fintype.ofFinite QuinticGoldilocks
  have hcard : Fintype.card QuinticGoldilocks = pGL ^ 5 := by
    rw [Fintype.card_eq_nat_card, quintic_natCard]
  have h5 : ∀ w : QuinticGoldilocks, w ^ pGL ^ 5 = w := fun w => by
    rw [← hcard]; exact FiniteField.pow_card w
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · -- `i < j`: the guard checks `z j ^ p^k ≠ z i`; `z j = z i ^ p^k` gives `z j ^ p^(5-k) = z i`.
    by_cases hk0 : k = 0
    · subst hk0; exact h.2 j i hlt 0 (by norm_num) (by simpa using hzj)
    · refine h.2 j i hlt (5 - k) (by omega) ?_
      rw [hzj, ← pow_mul, ← pow_add, Nat.add_sub_cancel' (by omega), h5]
  · exact h.2 i j hgt k hk hzj.symm |>.elim

/-- Residue coordinates of the Rust matrix: write B(X) = ∑ᵣ Xʳ Bᵣ(Xᵈ), d = 2^s.
Modulo Xᵈ − zⱼ the coefficient of Xʳ is Bᵣ(zⱼ). This proves bijectivity of
that coordinate map for every s, without assuming the fiber polynomials split. -/
theorem maskPointsGood_residue_coordinates {m : ℕ} (s : ℕ) (z : Fin m → QuinticGoldilocks)
    (h : maskPointsGood z) :
    Function.Bijective (fun (B : Fin (2 ^ s) → degreeLT FpGL (5 * m)) r =>
      oodEval (K := FpGL) (5 * m) z (B r)) := by
  let e := LinearEquiv.ofBijective _ (maskPointsGood_full_rank z h)
  exact (Equiv.piCongrRight (fun _ : Fin (2 ^ s) => e.toEquiv)).bijective

/-! ## §4. Lemma V2.4 mask line = VEIL (`2026/683`) linear zk-PG; V2.0 and V2.8 teeth -/

section MaskLine

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- VEIL Definition 2.20 / Lemma 3.4: a zk proximity generator `(ρ₁, ρ₂) ∈ F × F^×` combines the
witness word and a uniform mask as `x' = ρ₁ w' + ρ₂ r'`. -/
def zkPGLine (ρ₁ ρ₂ : F) (w r : V) : V := ρ₁ • w + ρ₂ • r

theorem zkPGLine_bijective (ρ₁ : F) {ρ₂ : F} (hρ₂ : ρ₂ ≠ 0) (w : V) :
    Function.Bijective (zkPGLine ρ₁ ρ₂ w) := by
  refine ⟨fun r r' h => ?_, fun g => ⟨ρ₂⁻¹ • (g - ρ₁ • w), ?_⟩⟩
  · simp only [zkPGLine, add_right_inj] at h
    exact smul_right_injective V hρ₂ h
  · simp [zkPGLine, smul_smul, mul_inv_cancel₀ hρ₂]

/-- **Lemma V2.4 (mask line).** `R ↦ P + β_R R` is the VEIL zk-PG line at `ρ₁ = 1`. -/
theorem maskLine_bijective (P : V) {β : F} (hβ : β ≠ 0) :
    Function.Bijective (fun R : V => P + β • R) := by
  convert zkPGLine_bijective (1 : F) hβ P using 1
  funext R; simp [zkPGLine]

/-- Exactly one mask `R` yields each Stage-1 word `g`, whatever the witness `P`. -/
theorem maskLine_fiber_card_one [Fintype V] [DecidableEq V] (P g : V) {β : F} (hβ : β ≠ 0) :
    (Finset.univ.filter (fun R : V => P + β • R = g)).card = 1 := by
  rw [Finset.card_eq_one]
  obtain ⟨R, hR⟩ := (maskLine_bijective P hβ).2 g
  refine ⟨R, ?_⟩
  ext R'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => (maskLine_bijective P hβ).1 (h.trans hR.symm), fun h => h ▸ hR⟩

/-- **V2.4 HVZK of the scalar line.** Under a uniform mask the law of `g` is the same for
every witness word `P`. -/
theorem maskLine_hvzk [Fintype V] [DecidableEq V] (P P' g : V) {β : F} (hβ : β ≠ 0) :
    (Finset.univ.filter (fun R : V => P + β • R = g)).card =
      (Finset.univ.filter (fun R : V => P' + β • R = g)).card := by
  rw [maskLine_fiber_card_one P g hβ, maskLine_fiber_card_one P' g hβ]

/-- Inverse and public linear-claim identity of Lemma V2.4: `R = (g - P)/β_R` and `μ = (⟨g, v⟩ - σ)/β_R`. -/
theorem maskLine_view_determined (φ : V →ₗ[F] F) {P R g : V} {β : F} (hβ : β ≠ 0)
    (h : P + β • R = g) : R = β⁻¹ • (g - P) ∧ φ R = β⁻¹ * (φ g - φ P) := by
  have hR : R = β⁻¹ • (g - P) := by
    rw [← h, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hβ, one_smul]
  exact ⟨hR, by rw [hR, map_smul, map_sub, smul_eq_mul]⟩

/-- Joint view of the masked word and any family of opened linear claims, for a fresh
uniform mask. Each output has one preimage iff its claims agree with the public values. -/
theorem maskLine_joint_fiber_card {W : Type*} [AddCommGroup W] [Module F W] [DecidableEq W]
    [Fintype V] [DecidableEq V] (φ : V →ₗ[F] W) (P g : V) (μ : W) {β : F} (hβ : β ≠ 0) :
    (Finset.univ.filter (fun R : V => P + β • R = g ∧ φ R = μ)).card =
      if φ g = φ P + β • μ then 1 else 0 := by
  have hclaim (R : V) (h : P + β • R = g) : (φ R = μ) ↔ φ g = φ P + β • μ := by
    rw [← h, map_add, map_smul, add_right_inj]
    exact (smul_right_injective W hβ).eq_iff.symm
  have e (R : V) := and_congr_right (hclaim R)
  simp only [e]
  split_ifs with h <;> simp [h, maskLine_fiber_card_one P g hβ]

/-- **Tooth:** `β_R = 0` publishes the witness word; two witnesses give disjoint views. -/
theorem maskLine_zero_challenge_leaks [Fintype V] [DecidableEq V] {P P' : V} (hP : P ≠ P') :
    (Finset.univ.filter (fun R : V => P + (0 : F) • R = P)).card = Fintype.card V ∧
      (Finset.univ.filter (fun R : V => P' + (0 : F) • R = P)).card = 0 := by
  constructor
  · simp
  · simp [Ne.symm hP]

end MaskLine

/-- **Tooth for V2.0 departure 1.** The affine combiner `g = P + (a + bY) R` reveals `P(-a/b)`
whatever the mask `R`. -/
theorem affine_combiner_reveals_root_eval {F : Type*} [Field F] (P R : F[X]) (a : F) {b : F}
    (hb : b ≠ 0) : (P + (C a + C b * X) * R).eval (-a / b) = P.eval (-a / b) := by
  have h0 : a + b * (-a / b) = 0 := by field_simp; ring
  simp [h0]

/-- **Tooth for V2.8.** A two-mask cascade `P + L₁R₁ + L₂R₂` whose linear factors share a root
`r` reveals `P(r)`: distinct roots are a necessary part of its unproved rank condition. -/
theorem cascade_common_root_reveals {F : Type*} [Field F] (P R₁ R₂ L₁ L₂ : F[X]) (r : F)
    (h₁ : L₁.eval r = 0) (h₂ : L₂.eval r = 0) :
    (P + L₁ * R₁ + L₂ * R₂).eval r = P.eval r := by
  simp [h₁, h₂]

/-! ## §5. Fiat–Shamir grinding ledger (`2026/2326`) -/

/-- A verifier round: proven error exponent and grinding credit, in millibits. -/
structure GrindRound where
  bits : ℤ
  grind : ℤ

/-- Level of a schedule: the minimum of `bits + grind` over its rounds with initial cap `acc`. -/
def ledgerLevel (rs : List GrindRound) (acc : ℤ) : ℤ :=
  rs.foldl (fun a r => min a (r.bits + r.grind)) acc

/-- The level with all grinding credit removed. -/
def algebraicLevel (rs : List GrindRound) (acc : ℤ) : ℤ :=
  rs.foldl (fun a r => min a r.bits) acc

theorem ledgerLevel_eq_algebraic_of_zero_grind (rs : List GrindRound) (acc : ℤ)
    (h : ∀ r ∈ rs, r.grind = 0) : ledgerLevel rs acc = algebraicLevel rs acc := by
  induction rs generalizing acc with
  | nil => rfl
  | cons r rs ih =>
    simp only [ledgerLevel, algebraicLevel, List.foldl_cons] at ih ⊢
    rw [h r (by simp), add_zero]
    exact ih _ (fun r' hr' => h r' (by simp [hr']))

theorem foldl_min_mono {α : Type*} (f : α → ℤ) (l : List α) {a b : ℤ} (hab : a ≤ b) :
    l.foldl (fun x r => min x (f r)) a ≤ l.foldl (fun x r => min x (f r)) b := by
  induction l generalizing a b with
  | nil => exact hab
  | cons r l ih => exact ih (min_le_min_right _ hab)

/-- Grinding credit can only raise the level. -/
theorem algebraicLevel_le_ledgerLevel (rs : List GrindRound) (acc : ℤ)
    (h : ∀ r ∈ rs, 0 ≤ r.grind) : algebraicLevel rs acc ≤ ledgerLevel rs acc := by
  induction rs generalizing acc with
  | nil => exact le_rfl
  | cons r rs ih =>
    have h0 := h r (by simp)
    calc algebraicLevel (r :: rs) acc = algebraicLevel rs (min acc r.bits) := rfl
      _ ≤ algebraicLevel rs (min acc (r.bits + r.grind)) := by
          unfold algebraicLevel
          exact foldl_min_mono (fun r : GrindRound => r.bits) rs (min_le_min_left _ (by linarith))
      _ ≤ ledgerLevel rs (min acc (r.bits + r.grind)) :=
          ih _ (fun r' hr' => h r' (by simp [hr']))
      _ = ledgerLevel (r :: rs) acc := rfl

/-- **A level above the algebraic one relies on a PoW.** Some round then carries nonzero
grinding, whose credit needs a non-amortizing PoW; `2026/2326` Theorem 1 (informal; Theorem 6.1
formal) bounds the conjunction of strength and non-amortization under its verifier-efficiency
hypotheses. Construction 7.1 composes two PoWs. The statement below is ledger arithmetic. -/
theorem level_relies_on_grinding (rs : List GrindRound) (acc T : ℤ)
    (hlo : algebraicLevel rs acc < T) (hhi : T ≤ ledgerLevel rs acc) :
    ∃ r ∈ rs, r.grind ≠ 0 := by
  by_contra hno
  have hz : ∀ r ∈ rs, r.grind = 0 := fun r hr => by_contra fun h => hno ⟨r, hr, h⟩
  rw [ledgerLevel_eq_algebraic_of_zero_grind rs acc hz] at hhi
  exact absurd (lt_of_lt_of_le hlo hhi) (lt_irrefl _)

/-! ## §6. Integer replica of the `zk_hem::bounds` / `zk_hem::v2::bounds` millibit ledger

Definitions mirror `crates/agg/src/zk_hem/bounds.rs` (`log2_lo`, `log2_hi`, `log2_one_plus`,
`sum_bits`) and `crates/agg/src/zk_hem/v2/bounds.rs` (`mask_line_bad_challenges`, `mask_line`,
`Report::{qrom,classical}_{sum,work}_bits`); the work search scans down from the single-term ceiling, and the kernel evaluates
them under `decide`. The differential crate pins the same values from a Rust port. -/

/-- `floor(log2 x)` for `0 < x < 2^fuel`. -/
def natLog2 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, x => if x < 2 then 0 else natLog2 fuel (x / 2) + 1

/-- The 24 squarings of `log2_lo`: `y ← y²/2^63`, emit a bit when `y ≥ 2^64`. -/
def log2Loop : ℕ → ℕ → ℕ → ℕ
  | 0, _, frac => frac
  | n + 1, y, frac =>
    if 2 ^ 64 ≤ y * y / 2 ^ 63 then log2Loop n (y * y / 2 ^ 63 / 2) (frac + 2 ^ n)
    else log2Loop n (y * y / 2 ^ 63) frac

/-- `(x << leading_zeros) >> 64` for a `u128` `x`: the top 64 bits, normalised to `[2^63, 2^64)`. -/
def normTop (x : ℕ) : ℕ :=
  if 63 ≤ natLog2 130 x then x / 2 ^ (natLog2 130 x - 63) else x * 2 ^ (63 - natLog2 130 x)

/-- `bounds.rs::log2_lo`: a lower bound on `1000 log2 x` for positive u128 input. -/
def log2Lo (x : ℕ) : ℤ :=
  (natLog2 130 x : ℤ) * 1000 + ((log2Loop 24 (normTop x) 0 * 1000 / 2 ^ 24 : ℕ) : ℤ)

/-- `bounds.rs::log2_hi`: an upper bound on `1000 log2 x` for positive u128 input. -/
def log2Hi (x : ℕ) : ℤ := if 2 ^ natLog2 130 x = x then log2Lo x else log2Lo x + 2

def eighths : ℕ → ℕ
  | 0 => 1000 | 1 => 918 | 2 => 841 | 3 => 772 | 4 => 708 | 5 => 649 | 6 => 595 | _ => 546

/-- `bounds.rs::log2_one_plus`: an upper bound on `1000 log2(1 + 2^(-d/1000))`. -/
def log2OnePlus (d : ℕ) : ℤ :=
  if 40 ≤ d / 125 / 8 then 1
  else ((min ((1443 * eighths (d / 125 % 8) + 999) / 1000 / 2 ^ (d / 125 / 8)) 999 : ℕ) : ℤ) + 1

/-- `bounds.rs::sum_bits`: a lower bound on `-1000 log2(2^(-a/1000) + 2^(-b/1000))` (millibits). -/
def sumBits (a b : ℤ) : ℤ := min a b - log2OnePlus (a - b).natAbs

/-- `FIELD_MILLIBITS` and the two QROM constants of `v2/bounds.rs`. -/
def fieldMillibits : ℤ := 319998
def qromRbrConst : ℤ := 8322
def qromMerkleConst : ℤ := 12640
def qromSlack : ℤ := 23
/-- `8000 * DIGEST_BYTES` with `DIGEST_BYTES = 50`. -/
def digestMillibits : ℤ := 400000

def qromSumBits (rbr logT : ℤ) : ℤ :=
  sumBits (rbr - qromRbrConst - qromSlack - 2 * logT)
    (digestMillibits - qromMerkleConst - qromSlack - 3 * logT)

def classicalSumBits (rbr logT : ℤ) : ℤ := sumBits (rbr - logT) (digestMillibits - 2000 - 2 * logT)

/-- Inspect candidates from the single-term upper bound down. Eighth-bit buckets can
make the rounded sum pass again after a failure. The lower endpoint is checked by the caller. -/
def scanWork (f : ℤ → ℤ) : ℕ → ℤ → ℤ
  | 0, w => w
  | n + 1, w => if 0 ≤ f w then w else scanWork f n (w - 1)

def qromWorkTerms (rbr : ℤ) : ℤ × ℤ :=
  ((rbr - qromRbrConst - qromSlack).tdiv 2, (digestMillibits - qromMerkleConst - qromSlack) / 3)

def qromWorkBits (rbr : ℤ) (rounds : ℕ) : Option ℤ :=
  let hi := min (qromWorkTerms rbr).1 (qromWorkTerms rbr).2
  if rounds < 512 ∧ 24000 ≤ hi ∧ 0 ≤ qromSumBits rbr 24000 then
    some (scanWork (qromSumBits rbr) (hi - 24000).toNat hi) else none

def classicalWorkBits (rbr : ℤ) : Option ℤ :=
  let hi := min rbr ((digestMillibits - 2000) / 2)
  if 0 ≤ classicalSumBits rbr 0 then some (scanWork (classicalSumBits rbr) hi.toNat hi) else none

/-- Re-entry of both rounded predicates on synthetic reports. -/
theorem rounded_work_reentry :
    qromSumBits 267508 128798 < 0 ∧ qromWorkBits 267508 100 = some 128799 ∧
    classicalSumBits 200094 198530 < 0 ∧ classicalWorkBits 200094 = some 198531 := by decide

/-- `mask_line_bad_challenges`: `ceil((2m+1)^3 n^2 / (3D))`, `n = blowup 2^rem`, `D = 2^rem + 1`. -/
def maskLineBadChallenges (blowup rem m : ℕ) : ℕ :=
  ((2 * m + 1) ^ 3 * (blowup * 2 ^ rem) ^ 2 + 3 * (2 ^ rem + 1) - 1) / (3 * (2 ^ rem + 1))

/-- `mask_line`: `FIELD_MILLIBITS - log2_hi(b_cf)`. -/
def maskLineBits (blowup rem m : ℕ) : ℤ := fieldMillibits - log2Hi (max (maskLineBadChallenges blowup rem m) 1)

/-- The `[DKT26]`/Johnson cover predicate of `mask_line_bad_challenges`. -/
def lineCovers (blowup rem m a : ℕ) : Bool :=
  (2 * m + 1) ^ 2 * (blowup * 2 ^ rem) * (2 ^ rem + 2) ≤ (2 * m * a) ^ 2

set_option exponentiation.threshold 400000 in
/-- `FIELD_MILLIBITS = floor(1000 log2(p^5 - 1)) - 1 = 319_998`:
`2^319999 ≤ (p^5 - 1)^1000 < 2^320000`. -/
theorem fieldMillibits_certified :
    2 ^ 319999 ≤ (pGL ^ 5 - 1) ^ 1000 ∧ (pGL ^ 5 - 1) ^ 1000 < 2 ^ 320000 := by
  constructor <;> decide

/-- The digest term of the QROM level: `(400000 - 12640 - 23) / 3 = 129_112`
(`every_accepted_size_reaches_128_bits_classical_and_qrom`). -/
theorem qrom_digest_term : (qromWorkTerms 0).2 = 129112 := by decide

/-- `[DKT26]` Theorem 5.12 line at `2^21` cells (`rem = 15`, `m = 256`): `b_cf` and `275.573`
bits, inside the pinned window `275_550..=275_580`; threshold `a` is the least cover. -/
theorem mask_line_2pow21 :
    maskLineBadChallenges 4 15 256 = 23593235614501 ∧ maskLineBits 4 15 256 = 275573 ∧
      lineCovers 4 15 256 65667 = true ∧ lineCovers 4 15 256 65666 = false := by decide

/-- `2^28` cells (`rem = 22`, `m = 128`): `271.565` bits, inside `271_540..=271_570`. -/
theorem mask_line_2pow28 : maskLineBits 4 22 128 = 271565 := by decide

/-- Calculator rows of the working-tree `v2/bounds.rs` at `size(L, 2^(L-1))`, `schedule(L)`:
`(log_cells, rbr_bits, qrom_work_bits, qrom_error_bits(64), mask_m, mask_bits, rounds, agreement)`, from the
differential crate (`zkhem_v2_conformance.json`). Every `rbr_round` there is `Query(0)`. -/
def v2LedgerRows : List (ℕ × ℤ × ℤ × ℤ × ℕ × ℤ × ℕ × ℕ) :=
  [(16, 265230, 128276, 128884, 54, 285277, 64, 8271),
    (17, 265183, 128253, 128837, 54, 285277, 70, 8271),
    (18, 264811, 128121, 128465, 75, 282866, 72, 16496),
    (19, 264853, 128136, 128507, 105, 280418, 74, 32927),
    (20, 265014, 128195, 128668, 145, 278027, 76, 65765),
    (21, 265009, 128192, 128663, 145, 278027, 80, 65765),
    (22, 265204, 128263, 128858, 200, 275639, 84, 131403),
    (23, 265374, 128317, 129028, 271, 273327, 92, 262630),
    (24, 264514, 128001, 128168, 364, 271052, 94, 525011),
    (25, 264620, 128047, 128274, 480, 268856, 98, 1049672),
    (26, 264634, 128048, 128288, 511, 267586, 102, 2099207),
    (27, 264629, 128051, 128283, 512, 266577, 106, 4198403),
    (28, 264627, 128050, 128281, 512, 265577, 110, 8396803)]

/-- Directed hypergeometric product for a nonzero-probability query on the pinned rows.
Round the mantissa up, then shift it exactly as in zk_hem/bounds.rs::query_bits. -/
def queryBits (n a q : ℕ) : ℤ :=
  let (mant, exp) := (List.range q).foldl (fun (st : ℕ × ℕ) i =>
    let m := (st.1 * (a - i) + (n - i - 1)) / (n - i)
    let shift := 63 - m.log2
    (m * 2 ^ shift, st.2 + shift)) (2 ^ 64, 0)
  (exp : ℤ) * 1000 + 64000 - log2Hi mant

/-- Recompute the selected mask (including Johnson pairs), query and compiled work levels.
The calculator supplies the agreement and m from its search across stages. -/
def rowCertified (r : ℕ × ℤ × ℤ × ℤ × ℕ × ℤ × ℕ × ℕ) : Bool :=
  let (l, rbr, q, t64, m, mask, rounds, a) := r
  let s := if l = 16 then 4 else if l ≤ 20 then 5 else 6
  let n := 4 * 2 ^ (l - s)
  let d := 2 ^ (l - s) + 1
  let pairs := n * (a - d) / (a * a - n * d)
  lineCovers 4 (l - s) m a && decide (3 ≤ m ∧ m ≤ 512 ∧ n * d < a * a ∧ a + s ≤ n ∧ 267 ≤ a) &&
    decide (mask = fieldMillibits - log2Hi (maskLineBadChallenges 4 (l - s) m + pairs)) &&
    decide (rbr = queryBits n (a + s) (if l < 24 then 267 else 266) - 1000) &&
  qromWorkBits rbr rounds = some q && decide (0 ≤ qromSumBits rbr q) && decide (qromSumBits rbr (q + 1) < 0) &&
    qromSumBits rbr 64000 = t64 && classicalWorkBits rbr = some 198999 && decide (128000 ≤ q) &&
    decide (rbr < mask)

/-- **The `128_000`-millibit ledger, `2^16..=2^28` cells (`v2_ledger_rows_certified`).** -/
theorem v2_ledger_rows_certified : v2LedgerRows.all rowCertified = true := by decide

/-- The tightest QROM margin is at `2^24` cells: `128.001` bits, one millibit over target. -/
theorem v2_tightest_margin_2pow24 : (v2LedgerRows.map Prod.fst) = List.range' 16 13 ∧
    (v2LedgerRows.filter (fun (_, _, q, _, _, _, _, _) => q ≤ 128001)).map Prod.fst = [24] ∧
    (v2LedgerRows.map (fun (_, _, q, _, _, _, _, _) => q)).min? = some 128001 := by decide

/-- The `SECURITY.md` V2.7 table (pre-V2.12 `[BCGM25]` schedule) is internally consistent:
its `rbr` column maps to its QROM column. It no longer describes the calculator (see the rows
above: Stage-0 queries `267`/`266`, `rbr_round = Query(0)` at every size). -/
theorem security_md_v27_table_consistent :
    [(264827, 128123), (264838, 128129), (264667, 128062), (265042, 128209), (264918, 128158)].all
      (fun r : ℤ × ℤ => qromWorkBits r.1 0 = some r.2 && classicalWorkBits r.1 = some 198999) = true := by
  decide

/-! ## Axiom footprint (pinned) -/

/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.maskPointsGood_residue_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskPointsGood_residue_coordinates
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.maskLine_joint_fiber_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskLine_joint_fiber_card
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.rounded_work_reentry' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms rounded_work_reentry
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.pGL_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pGL_prime
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.three_pow_quintic_eq_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms three_pow_quintic_eq_zeta
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.quinticGoldilocks_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quinticGoldilocks_irreducible
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.quintic_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quintic_finrank
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.quintic_card_gt_two_pow_319' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quintic_card_gt_two_pow_319
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.quintic_no_proper_intermediate_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quintic_no_proper_intermediate_field
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.norm_index_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms norm_index_odd
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.frobFixed_of_two_pow_frobFixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frobFixed_of_two_pow_frobFixed
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.mem_range_of_pow_char_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_range_of_pow_char_eq
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.aeval_pow_char_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms aeval_pow_char_pow
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.quintic_nonbase_pow_two_not_in_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quintic_nonbase_pow_two_not_in_base
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.quintic_two_pow_roots_of_unity_in_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quintic_two_pow_roots_of_unity_in_base
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.insufficient_base_blinders_leak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms insufficient_base_blinders_leak
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.quintic_insufficient_blinders' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quintic_insufficient_blinders
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.orbit_points_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orbit_points_injective
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.distinct_frobenius_orbits_full_rank_5m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms distinct_frobenius_orbits_full_rank_5m
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.frobenius_conjugate_ood_rank_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frobenius_conjugate_ood_rank_collapse
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.base_ood_point_not_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms base_ood_point_not_surjective
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.fiber_roots_distinct_orbits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fiber_roots_distinct_orbits
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.quintic_full_rank_5m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms quintic_full_rank_5m
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.maskPointsGood_full_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskPointsGood_full_rank
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.zkPGLine_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zkPGLine_bijective
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.maskLine_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskLine_bijective
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.maskLine_hvzk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskLine_hvzk
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.maskLine_view_determined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskLine_view_determined
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.maskLine_zero_challenge_leaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskLine_zero_challenge_leaks
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.affine_combiner_reveals_root_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms affine_combiner_reveals_root_eval
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.cascade_common_root_reveals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cascade_common_root_reveals
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.ledgerLevel_eq_algebraic_of_zero_grind' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms ledgerLevel_eq_algebraic_of_zero_grind
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.algebraicLevel_le_ledgerLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms algebraicLevel_le_ledgerLevel
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.level_relies_on_grinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms level_relies_on_grinding
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.fieldMillibits_certified' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms fieldMillibits_certified
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.qrom_digest_term' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms qrom_digest_term
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.mask_line_2pow21' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms mask_line_2pow21
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.mask_line_2pow28' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms mask_line_2pow28
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.v2_ledger_rows_certified' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms v2_ledger_rows_certified
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.v2_tightest_margin_2pow24' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms v2_tightest_margin_2pow24
/-- info: 'Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy.security_md_v27_table_consistent' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms security_md_v27_table_consistent

end Minidregg.Selvage.ZkHemV2SoundnessAndPrivacy
