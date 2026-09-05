/-
# Theory.CyclotomicExceptionalSet — fixed-weight exceptional sets in a Galois ring `ℤ_{p^e}[X]/(f)`

**The question this file settles.**  `Theory.ExceptionalSetLocalRing` says: in a local ring an
exceptional set (pairwise-unit differences) is a set on which the residue map is injective, so it is
no larger than the residue field.  This file exhibits the *rings* and the *sets*:

* the ring is `AdjoinRoot f = (ZMod n)[X]/(f)` for `n` a power of a prime `p` and `f` monic with
  `f mod p` **irreducible** over `F_p` — a Galois ring `GR(p^e, deg f)`, residue field
  `F_p[X]/(f mod p) = F_{p^{deg f}}`;
* the sets are the **fixed-weight sets** `weightSet f h = { X^{i₁} + ⋯ + X^{i_h} : i₁ < ⋯ < i_h < deg f }`
  (`indicatorPoly S` reduced mod `f`, `S` ranging over the `h`-subsets of `{0, …, deg f − 1}`).

**Statements (statement-first; hypotheses are constraints — see the falsifier).**

* `isLocalRing_adjoinRoot` — `(ZMod n)[X]/(f)` is a **local ring** whenever `p ∣ n ∣ p^e` and
  `f mod p` is irreducible.  Route: the coefficient-reduction hom `toResidue f : (ZMod n)[X]/(f) →+*
  F_p[X]/(f mod p)` is surjective with **nil kernel** (`pow_eq_zero_of_toResidue_eq_zero`: every
  kernel element `x` has `x^e = 0`, because `ker (ZMod n → ZMod p) = (p)` and `p^e = 0`), hence a
  **local homomorphism** (`isLocalHom_toResidue`), hence the domain is local
  (`RingHom.domain_isLocalRing`).
* `isExceptional_weightSet` — **the fixed-weight sets are exceptional**: any two distinct
  `h`-subset sums of distinct powers of `X` differ by a unit.  The mechanism is exactly the general
  lemma: `toResidue` is injective on the set, because in `F_p[X]/(f mod p)` two 0/1-polynomials of
  degree `< deg f` reduce to the same class only if they are equal (`mk_indicatorPoly_injOn`, a
  `modByMonic` degree argument — no field structure needed for *this* step), and equal
  0/1-polynomials have equal supports (`indicatorPoly_injective`, coefficient comparison).
* `card_weightSet` — **the count**, `|weightSet f h| = Nat.choose (deg f) h`, for ANY monic `f`
  over ANY nontrivial commutative ring: counting needs neither `p` nor irreducibility, only that
  `X^0, …, X^{d−1}` are independent mod a monic `f` of degree `d`.  This is the general theorem the
  brief asked for; it is not instance-only.

**The instance at conductor 9 over `ZMod 4`** (`GR4Cyc9 = (ZMod 4)[X]/(Φ₉)`, `Φ₉ = X⁶ + X³ + 1`,
`ord₉(2) = 6 = φ(9)` so `Φ₉` is irreducible mod 2 and the residue field is `F₆₄`):
`irreducible_cyclotomic_9_zmod2`, `GR4Cyc9_isLocalRing`, `isExceptional_weightSet_GR4Cyc9`
(weights 1 and 2 as named corollaries `isExceptional_weight_one_GR4Cyc9`,
`isExceptional_weight_two_GR4Cyc9`), `card_weightSet_GR4Cyc9 : |A_h| = C(6, h)` with the
concrete values `6` and `15`, and a concrete witness `isUnit_witness_GR4Cyc9 :
IsUnit ((1 + X) − (1 + X²))`.

**Which route and why.**  The Mathlib quotient (`AdjoinRoot`), NOT an explicit finite model:
Mathlib's `Polynomial` is noncomputable so `decide` cannot run inside the quotient, but the
statements needed are all *uniform* degree/coefficient arguments, and doing them once over
`AdjoinRoot` yields the general theorems above (any `p`, any `e`, any monic `f`, any weight `h`)
where a finite model would have yielded one 4096-element table.  `decide` is used exactly where
it is the right tool: `ord₉(2) = 6`, `φ(9) = 6`, the divisibilities `2 ∣ 4 ∣ 2²`, and subset
membership for the concrete witness.

**Falsifier — the irreducible-mod-`p` hypothesis is load-bearing.**  Over the negacyclic
`(ZMod 4)[X]/(X² + 1)` (`X² + 1 ≡ (X + 1)² mod 2`: reducible, residue field `F_2`), the weight-1
set `{1, X}` is NOT exceptional: `not_isUnit_root_sub_one : ¬ IsUnit (X − 1)`.  Proof: its image in
`F_2[X]/((X+1)²)` is `X + 1`, nonzero and square-zero, hence not a unit; units map to units.

**The deployment conductor `6561`** (§4b): `orderOf_two_mod6561 : ord₆₅₆₁(2) = 4374 = φ(6561)`,
kernel-checked through the sibling file's binary modular exponentiation `powMod` (`decide`, no
`native_decide`), so `Φ₆₅₆₁` is irreducible mod 2 (`irreducible_cyclotomic_6561_zmod2`),
`GR4Cyc6561 = (ZMod 4)[X]/(Φ₆₅₆₁) = GR(4, 4374)` is local (`GR4Cyc6561_isLocalRing`), and the
weight-16 set is exceptional (`isExceptional_weight_sixteen_GR4Cyc6561`) with exactly
`Nat.choose 4374 16 ≈ 2^149` elements (`card_weightSet_GR4Cyc6561`).  The residue field is
`F_{2^4374}`; the ceiling `2^4374` is nowhere near binding.

**The coefficient operator norm** (§5, over `ℤ`, a different carrier): `phi3Shift r m v` is the
harness's `phi3_shift` — multiply the coefficient vector `v : Fin (2r) → ℤ` by `X^m` in
`ℤ[X]/(X^{2r} + X^r + 1)` via `X^{3r} = 1` and the fold `X^{2r+j} = −X^{r+j} − X^j`.
`abs_phi3Shift_le : |(phi3Shift r m v) i| ≤ 2 · ‖v‖_∞` for every `r`, `m`, `v`, `i`: each output
coordinate is a difference of at most two input coordinates.  What is NOT proved: that
`phi3Shift` agrees with multiplication in `AdjoinRoot (X^{2r} + X^r + 1)` — that is the named
obligation `phi3Shift_spec` (§5 docstring).

**Reused from Mathlib** (this file hand-rolls none of it): `AdjoinRoot.lift/mk/mk_eq_mk/mk_eq_zero/
mk_self/mk_surjective/aeval_eq/instField`, `Polynomial.ker_mapRingHom`, `Polynomial.map_cyclotomic`,
`Polynomial.Monic.not_dvd_of_natDegree_lt`, `ZMod.castHom(_surjective)`, `ZMod.cast_eq_val`,
`ZMod.natCast_eq_zero_iff`, `Ideal.map_span`, `IsNilpotent.isUnit_one_add`,
`RingHom.domain_isLocalRing`, `Finset.card_powersetCard`, `orderOf_eq_iff`.  From this repo:
`Theory.CyclotomicInertia.irreducible_cyclotomic_of_orderOf_eq_totient` (the inertia bridge) and
`Theory.ExceptionalSetLocalRing.isExceptional_of_injOn` (the general lemma).
-/
import Mathlib.Tactic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Theory.ExceptionalSetLocalRing
import Theory.CyclotomicInertia

namespace Minidregg.Theory.CyclotomicExceptionalSet

open Polynomial IsLocalRing
open Minidregg.Theory.ExceptionalSetLocalRing (IsExceptional isExceptional_of_injOn
  card_le_card_residueField_of_isExceptional)
open Minidregg.Theory.CyclotomicInertia (powMod natCast_pow_eq_one_iff_powMod
  irreducible_cyclotomic_of_orderOf_eq_totient)

set_option autoImplicit false

/-! ## 1. Fixed-weight sets, their injectivity and their count — any monic `f`, any ring -/

section Weight

variable {R : Type*} [CommRing R]

/-- The 0/1-polynomial supported on `S`: `∑_{i ∈ S} X^i`. -/
noncomputable def indicatorPoly (S : Finset ℕ) : R[X] := ∑ i ∈ S, X ^ i

theorem coeff_indicatorPoly (S : Finset ℕ) (n : ℕ) :
    (indicatorPoly (R := R) S).coeff n = if n ∈ S then 1 else 0 := by
  simp [indicatorPoly, coeff_X_pow, Finset.sum_ite_eq]

/-- Coefficient reduction fixes 0/1-polynomials. -/
theorem map_indicatorPoly {S' : Type*} [CommRing S'] (g : R →+* S') (S : Finset ℕ) :
    (indicatorPoly (R := R) S).map g = indicatorPoly S := by
  simp [indicatorPoly, Polynomial.map_sum]

/-- The support determines the 0/1-polynomial (over a nontrivial ring, `1 ≠ 0`). -/
theorem indicatorPoly_injective [Nontrivial R] :
    Function.Injective (indicatorPoly (R := R)) := by
  intro S T h
  ext n
  have hc := congrArg (fun p : R[X] => p.coeff n) h
  simp only [coeff_indicatorPoly] at hc
  by_cases hS : n ∈ S <;> by_cases hT : n ∈ T <;> simp_all

theorem natDegree_indicatorPoly_lt {d : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range d)
    (hd : 0 < d) : (indicatorPoly (R := R) S).natDegree < d := by
  have : (indicatorPoly (R := R) S).natDegree ≤ d - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro i hi
    have := Finset.mem_range.mp (hS hi)
    exact (natDegree_X_pow_le i).trans (by omega)
  omega

/-- Reduction mod a monic `f` is injective on polynomials of degree `< natDegree f`
(`modByMonic` degree argument; no domain hypothesis). -/
theorem mk_eq_mk_of_natDegree_lt [Nontrivial R] {f : R[X]} (hf : f.Monic) {p q : R[X]}
    (hp : p.natDegree < f.natDegree) (hq : q.natDegree < f.natDegree)
    (h : AdjoinRoot.mk f p = AdjoinRoot.mk f q) : p = q := by
  rw [AdjoinRoot.mk_eq_mk] at h
  by_contra hne
  have hne' : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hlt : (p - q).natDegree < f.natDegree :=
    lt_of_le_of_lt (natDegree_sub_le p q) (max_lt hp hq)
  exact hf.not_dvd_of_natDegree_lt hne' hlt h

/-- `S ↦ (∑_{i∈S} X^i mod f)` is injective on the `h`-subsets of `{0, …, natDegree f − 1}`. -/
theorem mk_indicatorPoly_injOn [Nontrivial R] {f : R[X]} (hf : f.Monic) (h : ℕ) :
    Set.InjOn (fun S : Finset ℕ => AdjoinRoot.mk f (indicatorPoly S))
      (Finset.powersetCard h (Finset.range f.natDegree) : Set (Finset ℕ)) := by
  intro S hS T hT hST
  rw [Finset.mem_coe, Finset.mem_powersetCard] at hS hT
  by_cases hd : f.natDegree = 0
  · rw [hd, Finset.range_zero, Finset.subset_empty] at hS hT
    rw [hS.1, hT.1]
  · exact indicatorPoly_injective (mk_eq_mk_of_natDegree_lt hf
      (natDegree_indicatorPoly_lt hS.1 (Nat.pos_of_ne_zero hd))
      (natDegree_indicatorPoly_lt hT.1 (Nat.pos_of_ne_zero hd)) hST)

open scoped Classical in
/-- **The weight-`h` set** in `R[X]/(f)`: all sums of `h` distinct powers `X^i`, `i < natDegree f`. -/
noncomputable def weightSet (f : R[X]) (h : ℕ) : Finset (AdjoinRoot f) :=
  (Finset.powersetCard h (Finset.range f.natDegree)).image
    (fun S => AdjoinRoot.mk f (indicatorPoly S))

/-- **The count.**  `|weightSet f h| = C(natDegree f, h)` for any monic `f` over any nontrivial
commutative ring. -/
theorem card_weightSet [Nontrivial R] {f : R[X]} (hf : f.Monic) (h : ℕ) :
    (weightSet f h).card = Nat.choose f.natDegree h := by
  classical
  unfold weightSet
  rw [Finset.card_image_of_injOn (mk_indicatorPoly_injOn hf h), Finset.card_powersetCard,
    Finset.card_range]

theorem mem_weightSet {f : R[X]} {h : ℕ} {x : AdjoinRoot f} :
    x ∈ weightSet f h ↔ ∃ S ∈ Finset.powersetCard h (Finset.range f.natDegree),
      AdjoinRoot.mk f (indicatorPoly S) = x := by
  classical
  simp [weightSet]

end Weight

/-! ## 2. The tower `(ZMod n)[X]/(f) → F_p[X]/(f mod p)` for `p ∣ n ∣ p^e`

The residue-field map of a Galois ring, built by hand as `toResidue f` (coefficient reduction),
shown surjective with nil kernel, hence a local homomorphism. -/

section Tower

variable {p n e : ℕ} [hp : Fact p.Prime]

/-- Coefficient reduction `ZMod n → ZMod p` for `p ∣ n`. -/
abbrev red (hpn : p ∣ n) : ZMod n →+* ZMod p := ZMod.castHom hpn (ZMod p)

theorem red_surjective (hpn : p ∣ n) : Function.Surjective (red hpn) :=
  ZMod.castHom_surjective hpn

/-- The kernel of coefficient reduction is `(p)`. -/
theorem eq_mul_of_red_eq_zero (hpn : p ∣ n) (hnp : n ∣ p ^ e) {c : ZMod n}
    (hc : red hpn c = 0) : ∃ m : ZMod n, c = p * m := by
  haveI : NeZero n := ⟨ne_zero_of_dvd_ne_zero (pow_ne_zero e hp.out.ne_zero) hnp⟩
  rw [red, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hc
  obtain ⟨m, hm⟩ := hc
  refine ⟨m, ?_⟩
  rw [← ZMod.natCast_zmod_val c, hm]
  push_cast
  rfl

omit hp in
/-- `p^e = 0` in `ZMod n` when `n ∣ p^e`. -/
theorem natCast_prime_pow_eq_zero (hnp : n ∣ p ^ e) : ((p : ZMod n)) ^ e = 0 := by
  rw [← Nat.cast_pow]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hnp

variable (hpn : p ∣ n) (f : (ZMod n)[X])

/-- **The residue map of the Galois ring**: reduce coefficients mod `p`, then reduce mod `f mod p`. -/
noncomputable def toResidue : AdjoinRoot f →+* AdjoinRoot (f.map (red hpn)) :=
  AdjoinRoot.lift ((algebraMap (ZMod p) (AdjoinRoot (f.map (red hpn)))).comp (red hpn))
    (AdjoinRoot.root _) (by
      rw [← Polynomial.eval₂_map, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])

theorem toResidue_mk (q : (ZMod n)[X]) :
    toResidue hpn f (AdjoinRoot.mk f q) = AdjoinRoot.mk _ (q.map (red hpn)) := by
  rw [toResidue, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← Polynomial.aeval_def,
    AdjoinRoot.aeval_eq]

theorem toResidue_surjective : Function.Surjective (toResidue hpn f) := by
  intro y
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨q', rfl⟩ := Polynomial.map_surjective (red hpn) (red_surjective hpn) q
  exact ⟨AdjoinRoot.mk f q', toResidue_mk hpn f q'⟩

/-- **Nil kernel.**  Everything `toResidue` kills is `p · (something)`, and `p^e = 0`. -/
theorem pow_eq_zero_of_toResidue_eq_zero (hnp : n ∣ p ^ e) {x : AdjoinRoot f}
    (hx : toResidue hpn f x = 0) : x ^ e = 0 := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [toResidue_mk, AdjoinRoot.mk_eq_zero] at hx
  obtain ⟨r, hr⟩ := hx
  obtain ⟨r', rfl⟩ := Polynomial.map_surjective (red hpn) (red_surjective hpn) r
  have hker : q - f * r' ∈ RingHom.ker (Polynomial.mapRingHom (red hpn)) := by
    rw [RingHom.mem_ker, Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, hr,
      sub_self]
  rw [Polynomial.ker_mapRingHom] at hker
  have hle : RingHom.ker (red hpn) ≤ Ideal.span {(p : ZMod n)} := by
    intro c hc
    rw [RingHom.mem_ker] at hc
    obtain ⟨m, hm⟩ := eq_mul_of_red_eq_zero hpn hnp hc
    exact Ideal.mem_span_singleton.mpr ⟨m, hm⟩
  have hker' := Ideal.map_mono (f := (C : ZMod n →+* (ZMod n)[X])) hle hker
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hker'
  obtain ⟨s, hs⟩ := hker'
  have hq : AdjoinRoot.mk f q = (p : AdjoinRoot f) * AdjoinRoot.mk f s := by
    have hq' : q = C (p : ZMod n) * s + f * r' := by rw [← hs]; ring
    rw [hq', map_add, map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero,
      show C (p : ZMod n) = (p : (ZMod n)[X]) from map_natCast C p, map_natCast (AdjoinRoot.mk f)]
  have hp0 : (p : AdjoinRoot f) ^ e = 0 := by
    rw [← map_natCast (algebraMap (ZMod n) (AdjoinRoot f)), ← map_pow,
      natCast_prime_pow_eq_zero hnp, map_zero]
  rw [hq, mul_pow, hp0, zero_mul]

/-- **`toResidue` is a local homomorphism**: a unit downstairs lifts, because the kernel is nil. -/
theorem isLocalHom_toResidue (hnp : n ∣ p ^ e) : IsLocalHom (toResidue hpn f) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  obtain ⟨y', rfl⟩ := toResidue_surjective hpn f y
  rw [← map_mul, ← sub_eq_zero, ← map_one (toResidue hpn f), ← map_sub] at hy
  have hnil : IsNilpotent (x * y' - 1) := ⟨e, pow_eq_zero_of_toResidue_eq_zero hpn f hnp hy⟩
  have hu : IsUnit (x * y') := by
    have h1 : x * y' = 1 + (x * y' - 1) := by ring
    rw [h1]
    exact hnil.isUnit_one_add
  exact isUnit_of_mul_isUnit_left hu

/-- **The Galois ring is local** once `f mod p` is irreducible (so the target is a field). -/
theorem isLocalRing_adjoinRoot (hnp : n ∣ p ^ e) [Fact (Irreducible (f.map (red hpn)))] :
    IsLocalRing (AdjoinRoot f) :=
  haveI := isLocalHom_toResidue hpn f hnp
  RingHom.domain_isLocalRing (toResidue hpn f)

/-- **The fixed-weight sets are exceptional.**  Any two distinct sums of `h` distinct powers of
`X` (exponents `< natDegree f`) differ by a UNIT of `(ZMod n)[X]/(f)`, when `f` is monic and
`f mod p` is irreducible. -/
theorem isExceptional_weightSet (hnp : n ∣ p ^ e) [Fact (Irreducible (f.map (red hpn)))]
    (hf : f.Monic) (h : ℕ) : IsExceptional (weightSet f h : Set (AdjoinRoot f)) := by
  haveI := isLocalHom_toResidue hpn f hnp
  apply isExceptional_of_injOn (toResidue hpn f)
  intro x hx y hy hxy
  rw [Finset.mem_coe, mem_weightSet] at hx hy
  obtain ⟨S, hS, rfl⟩ := hx
  obtain ⟨T, hT, rfl⟩ := hy
  rw [toResidue_mk, toResidue_mk, map_indicatorPoly, map_indicatorPoly] at hxy
  have hmonic : (f.map (red hpn)).Monic := hf.map (red hpn)
  have hdeg : (f.map (red hpn)).natDegree = f.natDegree := hf.natDegree_map (red hpn)
  rw [← hdeg] at hS hT
  rw [mk_indicatorPoly_injOn hmonic h hS hT hxy]

/-- The ceiling of `Theory.ExceptionalSetLocalRing`, specialised: the fixed-weight set is no
larger than the residue field.  (With `card_weightSet`: `C(deg f, h) ≤ |k|`.) -/
theorem card_weightSet_le_card_residueField (hnp : n ∣ p ^ e)
    [Fact (Irreducible (f.map (red hpn)))] (hf : f.Monic) (h : ℕ)
    [IsLocalRing (AdjoinRoot f)] [Fintype (ResidueField (AdjoinRoot f))] :
    (weightSet f h).card ≤ Fintype.card (ResidueField (AdjoinRoot f)) :=
  card_le_card_residueField_of_isExceptional (isExceptional_weightSet hpn f hnp hf h)

end Tower

/-! ## 3. The instance: conductor 9 over `ZMod 4` — the Galois ring `GR(4, 6)` -/

section Conductor9

instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem two_dvd_four : (2 : ℕ) ∣ 4 := by norm_num

theorem four_dvd_two_pow_two : (4 : ℕ) ∣ 2 ^ 2 := by norm_num

/-- `ord₉(2) = 6`: `2` is a primitive root mod `9`. -/
theorem orderOf_two_mod9 : orderOf (((2 : ℕ) : ZMod 9)) = 6 :=
  (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩

theorem totient_9 : Nat.totient 9 = 6 := by decide

/-- `Φ₉` is irreducible over `F₂` — maximal inertia at `p = 2`, conductor `9`. -/
theorem irreducible_cyclotomic_9_zmod2 : Irreducible (cyclotomic 9 (ZMod 2)) :=
  irreducible_cyclotomic_of_orderOf_eq_totient (by norm_num) (by rw [orderOf_two_mod9, totient_9])

/-- `Φ₉` over `ZMod 4` reduces to `Φ₉` over `ZMod 2`. -/
theorem map_cyclotomic_9_red :
    (cyclotomic 9 (ZMod 4)).map (red two_dvd_four) = cyclotomic 9 (ZMod 2) :=
  Polynomial.map_cyclotomic 9 _

instance : Fact (Irreducible ((cyclotomic 9 (ZMod 4)).map (red two_dvd_four))) :=
  ⟨map_cyclotomic_9_red ▸ irreducible_cyclotomic_9_zmod2⟩

/-- `GR(4, 6) = (ZMod 4)[X]/(Φ₉)`. -/
abbrev GR4Cyc9 : Type := AdjoinRoot (cyclotomic 9 (ZMod 4))

/-- **`GR(4, 6)` is a local ring.** -/
theorem GR4Cyc9_isLocalRing : IsLocalRing GR4Cyc9 :=
  isLocalRing_adjoinRoot two_dvd_four _ four_dvd_two_pow_two

/-- `natDegree Φ₉ = 6`. -/
theorem natDegree_cyclotomic_9_zmod4 : (cyclotomic 9 (ZMod 4)).natDegree = 6 := by
  rw [natDegree_cyclotomic, totient_9]

/-- **Every fixed-weight set of `GR(4, 6)` is exceptional.** -/
theorem isExceptional_weightSet_GR4Cyc9 (h : ℕ) :
    IsExceptional (weightSet (cyclotomic 9 (ZMod 4)) h : Set GR4Cyc9) :=
  isExceptional_weightSet two_dvd_four _ four_dvd_two_pow_two (cyclotomic.monic 9 _) h

/-- Weight 1: `{X^j : j < 6}` has pairwise-unit differences. -/
theorem isExceptional_weight_one_GR4Cyc9 :
    IsExceptional (weightSet (cyclotomic 9 (ZMod 4)) 1 : Set GR4Cyc9) :=
  isExceptional_weightSet_GR4Cyc9 1

/-- Weight 2: `{X^i + X^j : i < j < 6}` has pairwise-unit differences. -/
theorem isExceptional_weight_two_GR4Cyc9 :
    IsExceptional (weightSet (cyclotomic 9 (ZMod 4)) 2 : Set GR4Cyc9) :=
  isExceptional_weightSet_GR4Cyc9 2

/-- **The count at conductor 9**: `|A_h| = C(6, h)`. -/
theorem card_weightSet_GR4Cyc9 (h : ℕ) :
    (weightSet (cyclotomic 9 (ZMod 4)) h).card = Nat.choose 6 h := by
  rw [card_weightSet (cyclotomic.monic 9 _), natDegree_cyclotomic_9_zmod4]

theorem card_weightSet_GR4Cyc9_one : (weightSet (cyclotomic 9 (ZMod 4)) 1).card = 6 := by
  rw [card_weightSet_GR4Cyc9]; rfl

theorem card_weightSet_GR4Cyc9_two : (weightSet (cyclotomic 9 (ZMod 4)) 2).card = 15 := by
  rw [card_weightSet_GR4Cyc9]; rfl

theorem indicatorPoly_zero_one : indicatorPoly (R := ZMod 4) {0, 1} = 1 + X := by
  simp [indicatorPoly]

theorem indicatorPoly_zero_two : indicatorPoly (R := ZMod 4) {0, 2} = 1 + X ^ 2 := by
  simp [indicatorPoly]

/-- **A concrete witness**: `(1 + X) − (1 + X²)` is a unit of `GR(4, 6)`. -/
theorem isUnit_witness_GR4Cyc9 :
    IsUnit (AdjoinRoot.mk (cyclotomic 9 (ZMod 4)) (1 + X) -
      AdjoinRoot.mk (cyclotomic 9 (ZMod 4)) (1 + X ^ 2)) := by
  have h01 : AdjoinRoot.mk (cyclotomic 9 (ZMod 4)) (1 + X) ∈ weightSet (cyclotomic 9 (ZMod 4)) 2 :=
    mem_weightSet.mpr ⟨{0, 1}, by rw [natDegree_cyclotomic_9_zmod4]; decide,
      by rw [indicatorPoly_zero_one]⟩
  have h02 : AdjoinRoot.mk (cyclotomic 9 (ZMod 4)) (1 + X ^ 2) ∈
      weightSet (cyclotomic 9 (ZMod 4)) 2 :=
    mem_weightSet.mpr ⟨{0, 2}, by rw [natDegree_cyclotomic_9_zmod4]; decide,
      by rw [indicatorPoly_zero_two]⟩
  refine isExceptional_weight_two_GR4Cyc9 _ (Finset.mem_coe.mpr h01) _ (Finset.mem_coe.mpr h02) ?_
  intro heq
  have := mk_eq_mk_of_natDegree_lt (cyclotomic.monic 9 (ZMod 4))
    (by rw [natDegree_cyclotomic_9_zmod4, ← indicatorPoly_zero_one]
        exact natDegree_indicatorPoly_lt (by decide) (by norm_num))
    (by rw [natDegree_cyclotomic_9_zmod4, ← indicatorPoly_zero_two]
        exact natDegree_indicatorPoly_lt (by decide) (by norm_num)) heq
  rw [← indicatorPoly_zero_one, ← indicatorPoly_zero_two] at this
  have := indicatorPoly_injective this
  exact absurd this (by decide)

end Conductor9

/-! ## 4. The falsifier: the negacyclic `(ZMod 4)[X]/(X² + 1)` — `X − 1` is NOT a unit

`X² + 1 ≡ (X + 1)² (mod 2)` is reducible, the residue field is `F₂`, and the weight-1 set
`{1, X}` fails.  The irreducible-mod-`p` hypothesis of `isExceptional_weightSet` is a constraint. -/

section Negacyclic

/-- `X − 1 = X + 1` in `F₂[X]`, and it squares to `X² + 1`. -/
theorem X_sub_one_sq_zmod2 : ((X : (ZMod 2)[X]) - 1) ^ 2 = X ^ 2 + 1 := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    have := CharP.cast_eq_zero (ZMod 2)[X] 2
    simpa using this
  linear_combination (-X) * h2

theorem monic_X_sq_add_one_zmod2 : (X ^ 2 + 1 : (ZMod 2)[X]).Monic := by
  simpa using monic_X_pow_add_C (1 : ZMod 2) (by norm_num : (2 : ℕ) ≠ 0)

/-- In `F₂[X]/(X² + 1)`, the class of `X − 1` is nonzero … -/
theorem mk_X_sub_one_ne_zero :
    AdjoinRoot.mk (X ^ 2 + 1 : (ZMod 2)[X]) (X - 1) ≠ 0 := by
  have hX : (X - 1 : (ZMod 2)[X]) = X - C 1 := by simp
  refine AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_X_sq_add_one_zmod2 ?_ ?_
  · rw [hX]; exact X_sub_C_ne_zero 1
  · rw [hX, natDegree_X_sub_C]
    have : (X ^ 2 + 1 : (ZMod 2)[X]).natDegree = 2 := by
      simpa using natDegree_X_pow_add_C (R := ZMod 2) (n := 2) (r := 1)
    omega

/-- … and squares to zero, so it is not a unit. -/
theorem not_isUnit_mk_X_sub_one_zmod2 :
    ¬IsUnit (AdjoinRoot.mk (X ^ 2 + 1 : (ZMod 2)[X]) (X - 1)) := by
  intro hu
  have hsq : (AdjoinRoot.mk (X ^ 2 + 1 : (ZMod 2)[X]) (X - 1)) ^ 2 = 0 := by
    rw [← map_pow, X_sub_one_sq_zmod2, AdjoinRoot.mk_self]
  have h0 : IsUnit ((0 : AdjoinRoot (X ^ 2 + 1 : (ZMod 2)[X]))) := hsq ▸ hu.pow 2
  haveI : Nontrivial (AdjoinRoot (X ^ 2 + 1 : (ZMod 2)[X])) := nontrivial_of_ne _ 0 mk_X_sub_one_ne_zero
  exact not_isUnit_zero h0

/-- `X² + 1` over `ZMod 4` reduces to `X² + 1` over `ZMod 2`. -/
theorem map_X_sq_add_one_red :
    (X ^ 2 + 1 : (ZMod 4)[X]).map (red two_dvd_four) = X ^ 2 + 1 := by
  simp

/-- **The falsifier.**  In `(ZMod 4)[X]/(X² + 1)` the weight-1 elements `1` and `X` do NOT differ
by a unit. -/
theorem not_isUnit_root_sub_one :
    ¬IsUnit (AdjoinRoot.root (X ^ 2 + 1 : (ZMod 4)[X]) - 1) := by
  intro hu
  have h := hu.map (toResidue two_dvd_four (X ^ 2 + 1 : (ZMod 4)[X]))
  rw [← AdjoinRoot.mk_X, ← map_one (AdjoinRoot.mk _), ← map_sub, toResidue_mk,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one] at h
  rw [map_X_sq_add_one_red] at h
  exact not_isUnit_mk_X_sub_one_zmod2 h

end Negacyclic

/-! ## 4b. The deployment conductor `6561` — `GR(4, 4374)` and the weight-16 set

`ord₆₅₆₁(2) = 4374` is beyond `decide` on `ZMod 6561` (the elaborator refuses `2^4374`), so the
three modular powers go through the sibling file's `powMod`, evaluated in the kernel by binary
exponentiation over GMP-accelerated `Nat` arithmetic. -/

section Conductor6561

theorem totient_6561 : Nat.totient 6561 = 4374 := by
  rw [show (6561 : ℕ) = 3 ^ (7 + 1) by norm_num, Nat.totient_prime_pow_succ Nat.prime_three]
  norm_num

private theorem prime_dvd_4374 {q : ℕ} (hq : q.Prime) (h : q ∣ 4374) : q = 2 ∨ q = 3 := by
  rw [show (4374 : ℕ) = 2 * 3 ^ 7 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h' | h'
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h')
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h'))

/-- `ord₆₅₆₁(2) = 4374 = φ(6561)`: `2` is a primitive root mod `3⁸`.  Kernel-checked:
`2^4374 ≡ 1`, `2^2187 ≢ 1`, `2^1458 ≢ 1 (mod 6561)` through `powMod`. -/
theorem orderOf_two_mod6561 : orderOf (((2 : ℕ) : ZMod 6561)) = 4374 := by
  have hplt : 1 < 6561 := by norm_num
  refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) ?_ ?_
  · exact (natCast_pow_eq_one_iff_powMod 13 hplt (by norm_num)).mpr (by decide)
  · intro q hq hqd
    rcases prime_dvd_4374 hq hqd with rfl | rfl
    · exact fun hcon => (by decide : powMod 6561 13 2 (4374 / 2) ≠ 1)
        ((natCast_pow_eq_one_iff_powMod 13 hplt (by norm_num)).mp hcon)
    · exact fun hcon => (by decide : powMod 6561 13 2 (4374 / 3) ≠ 1)
        ((natCast_pow_eq_one_iff_powMod 13 hplt (by norm_num)).mp hcon)

/-- `Φ₆₅₆₁` is irreducible over `F₂` — maximal inertia at the deployment conductor. -/
theorem irreducible_cyclotomic_6561_zmod2 : Irreducible (cyclotomic 6561 (ZMod 2)) :=
  irreducible_cyclotomic_of_orderOf_eq_totient (by norm_num)
    (by rw [orderOf_two_mod6561, totient_6561])

theorem map_cyclotomic_6561_red :
    (cyclotomic 6561 (ZMod 4)).map (red two_dvd_four) = cyclotomic 6561 (ZMod 2) :=
  Polynomial.map_cyclotomic 6561 _

instance : Fact (Irreducible ((cyclotomic 6561 (ZMod 4)).map (red two_dvd_four))) :=
  ⟨map_cyclotomic_6561_red ▸ irreducible_cyclotomic_6561_zmod2⟩

/-- `GR(4, 4374) = (ZMod 4)[X]/(Φ₆₅₆₁)`. -/
abbrev GR4Cyc6561 : Type := AdjoinRoot (cyclotomic 6561 (ZMod 4))

/-- **`GR(4, 4374)` is a local ring.** -/
theorem GR4Cyc6561_isLocalRing : IsLocalRing GR4Cyc6561 :=
  isLocalRing_adjoinRoot two_dvd_four _ four_dvd_two_pow_two

/-- **Every fixed-weight set of `GR(4, 4374)` is exceptional.** -/
theorem isExceptional_weightSet_GR4Cyc6561 (h : ℕ) :
    IsExceptional (weightSet (cyclotomic 6561 (ZMod 4)) h : Set GR4Cyc6561) :=
  isExceptional_weightSet two_dvd_four _ four_dvd_two_pow_two (cyclotomic.monic 6561 _) h

/-- **The deployment challenge set**: weight 16 at conductor 6561 has pairwise-unit differences. -/
theorem isExceptional_weight_sixteen_GR4Cyc6561 :
    IsExceptional (weightSet (cyclotomic 6561 (ZMod 4)) 16 : Set GR4Cyc6561) :=
  isExceptional_weightSet_GR4Cyc6561 16

/-- …and has exactly `C(4374, 16)` (`≈ 2^149`) elements. -/
theorem card_weightSet_GR4Cyc6561 :
    (weightSet (cyclotomic 6561 (ZMod 4)) 16).card = Nat.choose 4374 16 := by
  rw [card_weightSet (cyclotomic.monic 6561 _), natDegree_cyclotomic, totient_6561]

end Conductor6561

/-! ## 5. The coefficient operator norm over `ℤ` (a different carrier)

`phi3Shift r m v` is the harness's `phi3_shift`: multiply `v ∈ ℤ^{2r}` by `X^m` in
`ℤ[X]/(X^{2r} + X^r + 1)`.  Lift to the cyclic ring `ℤ[X]/(X^{3r} − 1)` (rotate by `m`), then fold
with `X^{2r+j} = −X^{r+j} − X^j`.  Every output coordinate is `c_t − c_{t'}` for two rotated
coordinates, so `|out| ≤ 2 ‖v‖_∞`.

**Named obligation `phi3Shift_spec`** (not proved here): for `r ≥ 1`,
`AdjoinRoot.mk (X^(2r) + X^r + 1) (X^m * ∑ v_j X^j) = AdjoinRoot.mk _ (∑ (phi3Shift r m v)_i X^i)`. -/

section OperatorNorm

/-- The rotated coefficient: the unique `j < 2r` with `(j + m) % 3r = t`, if any. -/
def rotCoeff (r m : ℕ) (v : Fin (2 * r) → ℤ) (t : ℕ) : ℤ :=
  if h : (t + 3 * r - m % (3 * r)) % (3 * r) < 2 * r then v ⟨_, h⟩ else 0

/-- Multiplication by `X^m` in `ℤ[X]/(X^{2r} + X^r + 1)` on coefficient vectors. -/
def phi3Shift (r m : ℕ) (v : Fin (2 * r) → ℤ) : Fin (2 * r) → ℤ := fun i =>
  if (i : ℕ) < r then rotCoeff r m v i - rotCoeff r m v (2 * r + i)
  else rotCoeff r m v i - rotCoeff r m v (r + i)

theorem abs_rotCoeff_le (r m : ℕ) (v : Fin (2 * r) → ℤ) {B : ℤ} (hB : 0 ≤ B)
    (hv : ∀ j, |v j| ≤ B) (t : ℕ) : |rotCoeff r m v t| ≤ B := by
  unfold rotCoeff
  split_ifs with h
  · exact hv _
  · simpa using hB

/-- **The coefficient operator-norm bound**: if `‖v‖_∞ ≤ B` then `‖X^m · v‖_∞ ≤ 2B`, for every
`r`, `m`, `v` — each output coordinate is a difference of two rotated coordinates. -/
theorem abs_phi3Shift_le (r m : ℕ) (v : Fin (2 * r) → ℤ) {B : ℤ} (hv : ∀ j, |v j| ≤ B)
    (i : Fin (2 * r)) : |phi3Shift r m v i| ≤ 2 * B := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hv i)
  unfold phi3Shift
  split_ifs
  · calc |rotCoeff r m v i - rotCoeff r m v (2 * r + i)|
        ≤ |rotCoeff r m v i| + |rotCoeff r m v (2 * r + i)| := abs_sub _ _
      _ ≤ B + B := add_le_add (abs_rotCoeff_le r m v hB hv _) (abs_rotCoeff_le r m v hB hv _)
      _ = 2 * B := by ring
  · calc |rotCoeff r m v i - rotCoeff r m v (r + i)|
        ≤ |rotCoeff r m v i| + |rotCoeff r m v (r + i)| := abs_sub _ _
      _ ≤ B + B := add_le_add (abs_rotCoeff_le r m v hB hv _) (abs_rotCoeff_le r m v hB hv _)
      _ = 2 * B := by ring

/-- The bound at conductor 9 (`r = 3`, `d = 6`), the harness's fully-enumerated case. -/
theorem abs_phi3Shift_le_conductor9 (m : ℕ) (v : Fin 6 → ℤ) {B : ℤ} (hv : ∀ j, |v j| ≤ B)
    (i : Fin 6) : |phi3Shift 3 m v i| ≤ 2 * B :=
  abs_phi3Shift_le 3 m v hv i

end OperatorNorm

/-! ## 6. Axiom pins -/

/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.indicatorPoly_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms indicatorPoly_injective
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.mk_eq_mk_of_natDegree_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mk_eq_mk_of_natDegree_lt
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.mk_indicatorPoly_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mk_indicatorPoly_injOn
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.card_weightSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_weightSet
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.pow_eq_zero_of_toResidue_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pow_eq_zero_of_toResidue_eq_zero
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.isLocalHom_toResidue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isLocalHom_toResidue
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.isLocalRing_adjoinRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isLocalRing_adjoinRoot
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.isExceptional_weightSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isExceptional_weightSet
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.card_weightSet_le_card_residueField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_weightSet_le_card_residueField
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.orderOf_two_mod9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderOf_two_mod9
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.irreducible_cyclotomic_9_zmod2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms irreducible_cyclotomic_9_zmod2
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.GR4Cyc9_isLocalRing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GR4Cyc9_isLocalRing
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.isExceptional_weightSet_GR4Cyc9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isExceptional_weightSet_GR4Cyc9
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.isExceptional_weight_one_GR4Cyc9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isExceptional_weight_one_GR4Cyc9
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.isExceptional_weight_two_GR4Cyc9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isExceptional_weight_two_GR4Cyc9
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.card_weightSet_GR4Cyc9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_weightSet_GR4Cyc9
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.card_weightSet_GR4Cyc9_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_weightSet_GR4Cyc9_one
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.card_weightSet_GR4Cyc9_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_weightSet_GR4Cyc9_two
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.isUnit_witness_GR4Cyc9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isUnit_witness_GR4Cyc9
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.not_isUnit_mk_X_sub_one_zmod2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_isUnit_mk_X_sub_one_zmod2
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.not_isUnit_root_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_isUnit_root_sub_one
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.orderOf_two_mod6561' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderOf_two_mod6561
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.irreducible_cyclotomic_6561_zmod2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms irreducible_cyclotomic_6561_zmod2
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.GR4Cyc6561_isLocalRing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GR4Cyc6561_isLocalRing
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.isExceptional_weight_sixteen_GR4Cyc6561' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms isExceptional_weight_sixteen_GR4Cyc6561
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.card_weightSet_GR4Cyc6561' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_weightSet_GR4Cyc6561
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.abs_phi3Shift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms abs_phi3Shift_le
/-- info: 'Minidregg.Theory.CyclotomicExceptionalSet.abs_phi3Shift_le_conductor9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms abs_phi3Shift_le_conductor9

end Minidregg.Theory.CyclotomicExceptionalSet
