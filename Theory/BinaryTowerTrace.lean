/-
# Theory.BinaryTowerTrace — [BTOWER-fanpaar-basis] CLOSED: Wiedemann's trace
induction discharges the Fan–Paar tower basis, and with it the ENTIRE
Fan–Paar recursion [BTOWER-fanpaar].

Builds on `Theory.BinaryTowerFanPaar` (`fpGen`, the recursion relations, and
the reductions of [BTOWER-fanpaar-gen] / [BTOWER-mult-full] to the basis
residual).

## The argument (Wiedemann 1988)

The absolute trace Tr : T_m → GF(2), `bTrace m u = Σ_{i < 2^m} u^(2^i)` (the
sum over the Frobenius orbit — the Galois group of T_m over GF(2)), separates
the embedded subfield from the Fan–Paar generator:

* every element of range(embed m) has trace 0 in T_{m+1}: its Frobenius orbit
  has period 2^m, so the 2^(m+1)-term sum counts each conjugate twice and
  char 2 kills it (`bTrace_embed_eq_zero`);
* `Tr(fpGen k) = 1` at EVERY level (`bTrace_fpGen`), by induction:
  - base: Tr(x₀) = x₀ + x₀² = 1 from x₀² + x₀ + 1 = 0;
  - step: a root z of X² + fpGen k·X + 1 down in T_{k+1} would force
    Tr((fpGen k)⁻¹) = Tr(w² + w) = 0 (w = z/fpGen k) while
    (fpGen k)⁻¹ = fpGen k + embed(coeff) makes that trace equal Tr(fpGen k) =
    1 — contradiction. So fpGen (k+1) avoids the embedded T_{k+1}, hence its
    Frobenius conjugate fpGen (k+1)^|T_{k+1}| is the OTHER root of the
    quadratic (`binaryTower_mem_range_of_pow_card` is the fixed-field
    characterization), the relative trace y + y^q IS embed(fpGen k), and the
    2^(k+2)-term sum folds to embed(Tr(fpGen k)) = embed 1 = 1.

Hence fpGen k ∉ range(embed k) for ALL k (`fpGen_not_mem_range_all`) — the ONE
∀ that was [BTOWER-fanpaar-basis] — and by the reductions already landed in
`Theory.BinaryTowerFanPaar`:

* `fanPaarTowerBasis_holds` — [BTOWER-fanpaar-basis] CLOSED;
* `fanPaarGeneration_holds` — [BTOWER-fanpaar-gen] CLOSED;
* `towerMulFull_holds` — [BTOWER-mult-full] CLOSED: the Fan–Paar packing is a
  bijection at every level, the recursive fast multiply is total;
* `fanPaarRecursion_holds` — [BTOWER-fanpaar] `FanPaarRecursion` CLOSED.

## Design note: why the concrete Frobenius-orbit sum, not `Algebra.trace`

The tower levels are tied by `Classical.choice`-chosen AlgHoms, not by
`IntermediateField`s; routing mathlib's `Algebra.trace` through them would
need per-level `Algebra`/`IsScalarTower` scaffolding plus trace transitivity
along non-canonical embeddings. The concrete `bTrace` IS Tr_{T_m/GF(2)} (the
Galois group is the Frobenius orbit), and the four properties the proof needs
— additivity, Frobenius-invariance, GF(2)-valuedness, vanishing on the
embedded subfield — are proved directly from char 2 and u^|T_m| = u.

Keystones: `bTrace_fpGen_zero` / `bTrace_fpGen_one` (Tr = 1 at GF(4)/GF(16),
via the base computation and the induction); TEETH `bTrace_embed_gf2_eq_zero`
/ `bTrace_embed_gf4_eq_zero` (the embedded subfield has trace 0 — the trace
genuinely separates) and `bTrace_eq_zero_or_one` (genuinely GF(2)-valued).

Candidate-independent FIELD MATH — imports Mathlib + Theory only (boundary
enforced by `scripts/check-import-boundary.sh`).
-/
import Theory.BinaryTowerFanPaar

namespace Minidregg.Theory

open Polynomial

/-! ### Frobenius facts at each level -/

/-- Every element of T_m is fixed by the full Frobenius power u ↦ u^|T_m|. -/
theorem binaryTower_pow_card (m : ℕ) (u : binaryTower m) : u ^ 2 ^ 2 ^ m = u := by
  letI : Fintype (binaryTower m) := Fintype.ofFinite _
  have hcard : Fintype.card (binaryTower m) = 2 ^ 2 ^ m := by
    rw [← Nat.card_eq_fintype_card]; exact binaryTower_card m
  rw [← hcard]
  exact FiniteField.pow_card u

/-! ### The absolute trace, concretely -/

/-- **The absolute trace** Tr_{T_m/GF(2)} : T_m → T_m (GF(2)-valued, see
`bTrace_eq_zero_or_one`): the sum of `u` over its Frobenius orbit,
Σ_{i < 2^m} u^(2^i) — the Galois group of T_m over GF(2) is exactly the
2^m Frobenius powers. -/
noncomputable def bTrace (m : ℕ) (u : binaryTower m) : binaryTower m :=
  ∑ i ∈ Finset.range (2 ^ m), u ^ 2 ^ i

/-- The trace is additive (Frobenius is, in char 2). -/
theorem bTrace_add (m : ℕ) (u v : binaryTower m) :
    bTrace m (u + v) = bTrace m u + bTrace m v := by
  simp only [bTrace, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => add_pow_char_pow u v 2 i

/-- The trace is Frobenius-invariant: Tr(u²) = Tr(u) — squaring cyclically
shifts the orbit sum (the wrap-around is `binaryTower_pow_card`). -/
theorem bTrace_sq (m : ℕ) (u : binaryTower m) : bTrace m (u ^ 2) = bTrace m u := by
  have hkey : ∀ i : ℕ, (u ^ 2) ^ 2 ^ i = u ^ 2 ^ (i + 1) := fun i => by
    rw [← pow_mul, ← pow_succ']
  have h1 := Finset.sum_range_succ' (fun i => u ^ 2 ^ i) (2 ^ m)
  have h2 := Finset.sum_range_succ (fun i => u ^ 2 ^ i) (2 ^ m)
  simp only [pow_zero, pow_one] at h1
  simp only [binaryTower_pow_card m u] at h2
  simp only [bTrace, hkey]
  exact add_right_cancel (h1.symm.trans h2)

/-- The trace value is its own square … -/
theorem bTrace_pow_two (m : ℕ) (u : binaryTower m) : bTrace m u ^ 2 = bTrace m u := by
  have h : bTrace m u ^ 2 = bTrace m (u ^ 2) := by
    simp only [bTrace]
    rw [sum_pow_char]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h, bTrace_sq]

/-- … so the trace is genuinely GF(2)-VALUED: Tr(u) ∈ {0, 1}. -/
theorem bTrace_eq_zero_or_one (m : ℕ) (u : binaryTower m) :
    bTrace m u = 0 ∨ bTrace m u = 1 := by
  have h2 : (2 : binaryTower m) = 0 := binaryTower_two_eq_zero m
  have hsq := bTrace_pow_two m u
  have key : bTrace m u * (bTrace m u + 1) = 0 := by
    linear_combination hsq + bTrace m u * h2
  rcases mul_eq_zero.mp key with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h - h2)

/-- **Trace transitivity, one level, concretely**: the T_{m+1}-trace of y is
the 2^m-term orbit sum of the RELATIVE trace y + y^(2^(2^m)) — split the
2^(m+1)-term sum into two half-orbits. -/
theorem bTrace_succ_eq (m : ℕ) (y : binaryTower (m + 1)) :
    bTrace (m + 1) y =
      ∑ i ∈ Finset.range (2 ^ m), (y + y ^ 2 ^ 2 ^ m) ^ 2 ^ i := by
  have hterm : ∀ i : ℕ, (y + y ^ 2 ^ 2 ^ m) ^ 2 ^ i =
      y ^ 2 ^ i + y ^ 2 ^ (2 ^ m + i) := by
    intro i
    rw [add_pow_char_pow]
    congr 1
    rw [← pow_mul, ← pow_add]
  have hrange : Finset.range (2 ^ (m + 1)) = Finset.range (2 ^ m + 2 ^ m) := by
    rw [pow_succ, mul_two]
  calc bTrace (m + 1) y
      = ∑ i ∈ Finset.range (2 ^ m + 2 ^ m), y ^ 2 ^ i := by
        simp only [bTrace]; rw [hrange]
    _ = (∑ i ∈ Finset.range (2 ^ m), y ^ 2 ^ i) +
        ∑ i ∈ Finset.range (2 ^ m), y ^ 2 ^ (2 ^ m + i) :=
        Finset.sum_range_add _ _ _
    _ = ∑ i ∈ Finset.range (2 ^ m), (y + y ^ 2 ^ 2 ^ m) ^ 2 ^ i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => (hterm i).symm

/-- **TOOTH: the embedded subfield has trace 0.** The Frobenius orbit of an
embedded element has period 2^m, so the T_{m+1}-trace counts each conjugate
twice — char 2 kills the sum. (Equivalently: the relative trace of a subfield
element is 2·a = 0.) This is the separating half of the Wiedemann argument. -/
theorem bTrace_embed_eq_zero (m : ℕ) (a : binaryTower m) :
    bTrace (m + 1) (binaryTowerEmbed m a) = 0 := by
  rw [bTrace_succ_eq]
  have hfix : binaryTowerEmbed m a ^ 2 ^ 2 ^ m = binaryTowerEmbed m a := by
    rw [← map_pow, binaryTower_pow_card]
  rw [hfix, CharTwo.add_self_eq_zero]
  exact Finset.sum_eq_zero fun i _ => zero_pow (Nat.two_pow_pos i).ne'

/-! ### The fixed-field characterization of the embedded subfield -/

/-- **Fixed by Frobenius^(2^m) ⟹ in the embedded subfield**: range(embed m)
has 2^(2^m) elements, ALL roots of X^(2^(2^m)) + X; a fixed point outside the
range would be a (2^(2^m)+1)-th root of a degree-2^(2^m) polynomial. -/
theorem binaryTower_mem_range_of_pow_card {m : ℕ} {y : binaryTower (m + 1)}
    (hy : y ^ 2 ^ 2 ^ m = y) : y ∈ (binaryTowerEmbed m).range := by
  classical
  by_contra hnot
  have h2 : (2 : binaryTower (m + 1)) = 0 := binaryTower_two_eq_zero (m + 1)
  have hq1 : 1 < 2 ^ 2 ^ m := Nat.one_lt_two_pow (pow_ne_zero m two_ne_zero)
  set p : (binaryTower (m + 1))[X] := X ^ 2 ^ 2 ^ m + X with hp
  have hcoeff : p.coeff (2 ^ 2 ^ m) = 1 := by
    rw [hp, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_pos rfl,
      Polynomial.coeff_X, if_neg hq1.ne, add_zero]
  have hpne : p ≠ 0 := fun h0 => one_ne_zero
    (by rw [h0, Polynomial.coeff_zero] at hcoeff; exact hcoeff.symm)
  have hpdeg : p.natDegree ≤ 2 ^ 2 ^ m := by
    rw [hp]
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
    exact max_le le_rfl hq1.le
  have hroot : ∀ x : binaryTower (m + 1), x ^ 2 ^ 2 ^ m = x → p.IsRoot x := by
    intro x hx
    show Polynomial.eval x p = 0
    rw [hp, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, hx]
    linear_combination x * h2
  have hsub : insert y ((binaryTowerEmbed m).range : Set (binaryTower (m + 1))) ⊆
      ↑p.roots.toFinset := by
    intro x hx
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hpne]
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hroot x hy
    · rw [SetLike.mem_coe, AlgHom.mem_range] at hx
      obtain ⟨a, rfl⟩ := hx
      exact hroot _ (by rw [← map_pow, binaryTower_pow_card])
  have hrange_card :
      ((binaryTowerEmbed m).range : Set (binaryTower (m + 1))).ncard = 2 ^ 2 ^ m := by
    rw [AlgHom.coe_range, ← Nat.card_coe_set_eq,
      Nat.card_range_of_injective (binaryTowerEmbed_injective m), binaryTower_card]
  have hins : (insert y ((binaryTowerEmbed m).range :
      Set (binaryTower (m + 1)))).ncard = 2 ^ 2 ^ m + 1 := by
    rw [Set.ncard_insert_of_notMem hnot, hrange_card]
  have hle : 2 ^ 2 ^ m + 1 ≤ p.roots.toFinset.card := by
    rw [← hins, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hcontra : p.roots.toFinset.card ≤ 2 ^ 2 ^ m :=
    le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' p) hpdeg)
  exact Nat.not_succ_le_self _ (le_trans hle hcontra)

/-! ### The Wiedemann trace invariant: Tr(fpGen k) = 1 at every level -/

/-- **The trace invariant (Wiedemann 1988), for ALL k**: Tr_{T_{k+1}/GF(2)}
(fpGen k) = 1. Base: x₀ + x₀² = 1 from the base relation. Step: (1) if the
level-(k+1) quadratic had a root z DOWN in T_{k+1}, then w = z/fpGen k gives
Tr((fpGen k)⁻¹) = Tr(w² + w) = 0, but (fpGen k)⁻¹ = fpGen k + embed(coeff)
forces that trace to equal Tr(fpGen k) = 1 — contradiction; so (2) fpGen (k+1)
avoids the embedded subfield, its Frobenius conjugate is the OTHER root of
X² + embed(fpGen k)·X + 1, the relative trace y + y^q equals embed(fpGen k),
and the orbit sum folds to embed(Tr(fpGen k)) = 1. -/
theorem bTrace_fpGen : ∀ k, bTrace (k + 1) (fpGen k) = 1
  | 0 => by
    have h2 : (2 : binaryTower 1) = 0 := binaryTower_two_eq_zero 1
    have hx := fpGen_base
    have hrange : Finset.range (2 ^ 1) = Finset.range (1 + 1) := by norm_num
    show ∑ i ∈ Finset.range (2 ^ 1), fpGen 0 ^ 2 ^ i = 1
    rw [hrange, Finset.sum_range_succ, Finset.sum_range_one]
    linear_combination hx - h2
  | k + 1 => by
    have ih := bTrace_fpGen k
    have h2K : (2 : binaryTower (k + 1)) = 0 := binaryTower_two_eq_zero (k + 1)
    have h2L : (2 : binaryTower (k + 2)) = 0 := binaryTower_two_eq_zero (k + 2)
    -- (1) fpGen (k+1) avoids the embedded T_{k+1}: a root z of
    --     X² + fpGen k·X + 1 down in T_{k+1} would force Tr(fpGen k) = 0.
    have hnm : fpGen (k + 1) ∉ (binaryTowerEmbed (k + 1)).range := by
      rw [AlgHom.mem_range]
      rintro ⟨z, hz⟩
      have hstepz := fpGen_step k
      rw [← hz] at hstepz
      have hzK : z ^ 2 + fpGen k * z + 1 = 0 := by
        apply binaryTowerEmbed_injective (k + 1)
        rw [map_add, map_add, map_mul, map_pow, map_one, map_zero]
        exact hstepz
      have hb0 : fpGen k ≠ 0 := fpGen_ne_zero k
      have hbb : fpGen k * (fpGen k)⁻¹ = 1 := mul_inv_cancel₀ hb0
      have hbinv : (fpGen k)⁻¹ = fpGen k + binaryTowerEmbed k (towerMulCoeff k) := by
        have hrel := fpGen_quadratic k
        exact inv_eq_of_mul_eq_one_right (by linear_combination hrel - h2K)
      have hw : (z * (fpGen k)⁻¹) ^ 2 + z * (fpGen k)⁻¹ = (fpGen k)⁻¹ ^ 2 := by
        linear_combination (fpGen k)⁻¹ ^ 2 * hzK - z * (fpGen k)⁻¹ * hbb -
          (fpGen k)⁻¹ ^ 2 * h2K
      have htr0 : bTrace (k + 1) ((fpGen k)⁻¹ ^ 2) = 0 := by
        rw [← hw, bTrace_add, bTrace_sq, CharTwo.add_self_eq_zero]
      have htr1 : bTrace (k + 1) ((fpGen k)⁻¹ ^ 2) = 1 := by
        rw [bTrace_sq, hbinv, bTrace_add, ih, bTrace_embed_eq_zero, add_zero]
      exact zero_ne_one (htr0.symm.trans htr1)
    -- (2) the Frobenius conjugate of fpGen (k+1) is the OTHER root of
    --     X² + embed(fpGen k)·X + 1: y^q = embed(fpGen k) + y.
    have hstep := fpGen_step k
    have hcq : binaryTowerEmbed (k + 1) (fpGen k) ^ 2 ^ 2 ^ (k + 1) =
        binaryTowerEmbed (k + 1) (fpGen k) := by
      rw [← map_pow, binaryTower_pow_card]
    have hpowq : (fpGen (k + 1) ^ 2 +
        binaryTowerEmbed (k + 1) (fpGen k) * fpGen (k + 1) + 1) ^ 2 ^ 2 ^ (k + 1) =
        0 := by
      rw [hstep, zero_pow (Nat.two_pow_pos _).ne']
    have hrootq : (fpGen (k + 1) ^ 2 ^ 2 ^ (k + 1)) ^ 2 +
        binaryTowerEmbed (k + 1) (fpGen k) * fpGen (k + 1) ^ 2 ^ 2 ^ (k + 1) + 1 =
        0 := by
      rw [add_pow_char_pow, add_pow_char_pow, mul_pow, hcq, one_pow] at hpowq
      have hyy : (fpGen (k + 1) ^ 2) ^ 2 ^ 2 ^ (k + 1) =
          (fpGen (k + 1) ^ 2 ^ 2 ^ (k + 1)) ^ 2 := by
        rw [← pow_mul, ← pow_mul, mul_comm]
      rw [hyy] at hpowq
      exact hpowq
    have hfactor : (fpGen (k + 1) ^ 2 ^ 2 ^ (k + 1) + fpGen (k + 1)) *
        (fpGen (k + 1) ^ 2 ^ 2 ^ (k + 1) +
          (binaryTowerEmbed (k + 1) (fpGen k) + fpGen (k + 1))) = 0 := by
      linear_combination hrootq + hstep +
        (fpGen (k + 1) * fpGen (k + 1) ^ 2 ^ 2 ^ (k + 1) - 1) * h2L
    have hyq : fpGen (k + 1) ^ 2 ^ 2 ^ (k + 1) =
        binaryTowerEmbed (k + 1) (fpGen k) + fpGen (k + 1) := by
      rcases mul_eq_zero.mp hfactor with hcase | hcase
      · exact absurd
          (binaryTower_mem_range_of_pow_card
            (by linear_combination hcase - fpGen (k + 1) * h2L))
          hnm
      · linear_combination hcase -
          (binaryTowerEmbed (k + 1) (fpGen k) + fpGen (k + 1)) * h2L
    -- (3) fold the orbit sum through the relative trace = embed (fpGen k).
    rw [bTrace_succ_eq, hyq]
    have hcollapse : fpGen (k + 1) +
        (binaryTowerEmbed (k + 1) (fpGen k) + fpGen (k + 1)) =
        binaryTowerEmbed (k + 1) (fpGen k) := by
      linear_combination fpGen (k + 1) * h2L
    rw [hcollapse]
    simp only [← map_pow]
    rw [← map_sum]
    rw [show (∑ i ∈ Finset.range (2 ^ (k + 1)), fpGen k ^ 2 ^ i) =
      bTrace (k + 1) (fpGen k) from rfl, ih, map_one]

/-! ### [BTOWER-fanpaar-basis] and everything downstream of it, CLOSED -/

/-- **The Fan–Paar tower basis, for ALL k** — the ONE ∀ that was
[BTOWER-fanpaar-basis]: fpGen k has trace 1, the embedded T_k has trace 0. -/
theorem fpGen_not_mem_range_all (k : ℕ) : fpGen k ∉ (binaryTowerEmbed k).range := by
  rw [AlgHom.mem_range]
  rintro ⟨a, ha⟩
  have h := bTrace_fpGen k
  rw [← ha, bTrace_embed_eq_zero] at h
  exact zero_ne_one h

/-- **[BTOWER-fanpaar-basis] CLOSED**: X² + gₖ·X + 1 is irreducible over
T_{k+1} at every level — the tower basis {1, fpGen k} is real all the way
up. -/
theorem fanPaarTowerBasis_holds : FanPaarTowerBasis := fpGen_not_mem_range_all

/-- **[BTOWER-fanpaar-gen] CLOSED**: every Fan–Paar generator generates its
level over GF(2). -/
theorem fanPaarGeneration_holds : FanPaarGeneration :=
  fanPaarGeneration_of_towerBasis fanPaarTowerBasis_holds

/-- **[BTOWER-mult-full] CLOSED**: the Fan–Paar packing T_k × T_k ≃ T_{k+1}
is a bijection at EVERY level — the recursive fast tower multiply
(`towerMul`, 3 sub-multiplies per level) is total all the way down. -/
theorem towerMulFull_holds : TowerMulFull :=
  towerMulFull_of_towerBasis fanPaarTowerBasis_holds

/-- **[BTOWER-fanpaar] CLOSED: `FanPaarRecursion` HOLDS** — the generator
sequence with the base and step relations, each generator generating its
level. The binary tower carries the fast Fan–Paar/Wiedemann arithmetic,
unconditionally. -/
theorem fanPaarRecursion_holds : FanPaarRecursion :=
  fanPaarRecursion_of_towerBasis fanPaarTowerBasis_holds

/-! ### Keystones at the concrete bottom -/

/-- KEYSTONE (GF(4)): Tr(x₀) = x₀ + x₀² = 1, computed from the base
relation. -/
theorem bTrace_fpGen_zero : bTrace 1 (fpGen 0) = 1 := bTrace_fpGen 0

/-- KEYSTONE (GF(16)): Tr(x₁) = 1 — the induction instantiated once. -/
theorem bTrace_fpGen_one : bTrace 2 (fpGen 1) = 1 := bTrace_fpGen 1

/-- TOOTH (the trace separates, at GF(4)): every embedded GF(2) element has
trace 0 — while `bTrace_fpGen_zero` gives fpGen 0 trace 1. -/
theorem bTrace_embed_gf2_eq_zero (a : binaryTower 0) :
    bTrace 1 (binaryTowerEmbed 0 a) = 0 := bTrace_embed_eq_zero 0 a

/-- TOOTH (the trace separates, at GF(16)): every embedded GF(4) element has
trace 0 — while `bTrace_fpGen_one` gives fpGen 1 trace 1. -/
theorem bTrace_embed_gf4_eq_zero (a : binaryTower 1) :
    bTrace 2 (binaryTowerEmbed 1 a) = 0 := bTrace_embed_eq_zero 1 a

end Minidregg.Theory
