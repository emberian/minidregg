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

**Extended 2026-08-13 — the family law, the sibling prime, and domain availability.**

* `familyP_maximalInertia_iff` — **THE FAMILY LAW.**  For a *prime* `p = 127·2ⁿ + 1`, maximal
  3-adic inertia (`ord_{3^(k+1)}(p) = 2·3^k` at every `k`, equivalently by
  `maximalThreeAdicInertia_iff_irreducible`: `Φ_{3^(k+1)}` irreducible over `F_p` at every `k`)
  holds **iff `n ≡ 0 or 2 (mod 6)`**.  Mechanism: `127 ≡ 1 (mod 9)` and `2ⁿ mod 9` cycles with
  period 6 through `(1,2,4,8,7,5)`, so `p ≡ 2ⁿ + 1 (mod 9)` hits a primitive root of `(ℤ/9)ˣ`
  exactly at those residues; `p mod 9 ∈ {2,5}` yields the lifting witness `v₃(p²−1) = 1`
  *symbolically* and §3's lifting-the-exponent route generalizes verbatim
  (`orderOf_three_pow_of_mod_nine`).  KoalaBear (`n = 24`) is re-derived as an instance
  (`orderOf_koalaBear_three_pow_of_family` — the same statement as
  `orderOf_koalaBear_three_pow`, from an independent proof).
* `p61_prime` / `maximalInertia_p61` — the sibling **p61** `= 2⁶¹ − 2⁵⁴ + 1 = 127·2⁵⁴ + 1`
  (KoalaBear one machine word up: same Solinas shape, same cofactor).  Primality is a Lucas
  certificate checked *in the kernel* by binary modular exponentiation (`powMod`, `decide` —
  no `native_decide`, no compiler in the trust base); two-adicity is exactly 54; maximal
  inertia is the family law at `54 ≡ 0 (mod 6)`, with the conductor-81 field
  `P61Cyc81_isField` / `P61Cyc81_finrank` mirroring KoalaBear's.
* **TOOTH C** — the family law's failing side is *inhabited*: `n ≡ 1,3,5 (mod 6)` contain no
  primes at all (`not_prime_familyP_of_mod_six`), `n = 4` gives `2033 = 19·107`, and the
  smallest prime member in the bad class `n ≡ 4 (mod 6)` is `n = 214` (`familyP_214_prime`,
  Lucas again).  There inertia FAILS: `ord₉ = 2` and `Φ₉` splits into exactly **3** quadratic
  factors (`card_factors_9_familyP_214`) — the refutation witness.
* **Domain availability** (`exists_unitsZMod_orderOf_eq` / `not_exists_subgroup_card_eq`) —
  in `F_pˣ` a (cyclic) subgroup of order `d` exists iff `d ∣ p − 1`; instantiated at the
  two-adic domains: **Goldilocks** (`2⁶⁴ − 2³² + 1`, proved prime here, two-adicity exactly
  32) has a domain of order `2^(ν+1)` for every `ν + 1 ≤ 32` and **none** of order `2³³` —
  `goldilocks_no_domain_two_pow_33` is the deployed `Domain::new(2^32)` panic stated as
  mathematics — and **p61** has domains to `2⁵⁴` and none of order `2⁵⁵`.

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
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

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

/-! ## 6. The family law — `p = 127·2ⁿ + 1` has maximal 3-adic inertia iff `n ≡ 0, 2 (mod 6)`

§3 proved the `n = 24` member (KoalaBear) from a numerically exhibited lifting witness.  This
section proves the law for the whole Solinas family at once.  `127 ≡ 1 (mod 9)` and `2ⁿ mod 9`
cycles with period 6 through `(1, 2, 4, 8, 7, 5)`, so `p = 127·2ⁿ + 1 ≡ 2ⁿ + 1 (mod 9)` runs
through `(2, 3, 5, 0, 8, 6)` as `n mod 6` runs through `(0, …, 5)`.  The unit group `(ℤ/9)ˣ`
is cyclic of order 6 with primitive roots exactly `{2, 5}` — hit at `n ≡ 0, 2 (mod 6)` — and
`p mod 9 ∈ {2, 5}` already hands over the lifting witness `v₃(p² − 1) = 1` *symbolically*, so
the lifting-the-exponent step of §3 carries every member.  The other residues: `n ≡ 1, 3, 5`
force `3 ∣ p` (those classes contain no primes at all), and `n ≡ 4` forces `p ≡ 8 ≡ −1
(mod 9)`, order 2, so inertia collapses at conductor 9 already (§9 exhibits the smallest
prime member, `n = 214`).  Arithmetic facts about integers throughout; no security claim. -/

/-- The Solinas family `127·2ⁿ + 1`.  KoalaBear is `familyP 24` (§3); p61 is `familyP 54`
(§8); the bad-class witness is `familyP 214` (§9). -/
def familyP (n : ℕ) : ℕ := 127 * 2 ^ n + 1

/-- **Maximal 3-adic inertia**: `p` is a primitive root modulo `3^(k+1)` for EVERY `k` —
equivalently (`maximalThreeAdicInertia_iff_irreducible`) `Φ_{3^(k+1)}` is irreducible over
`F_p` at every `k`, so every power-of-three cyclotomic ring over `F_p` is a field. -/
def MaximalThreeAdicInertia (p : ℕ) : Prop :=
  ∀ k : ℕ, orderOf ((p : ZMod (3 ^ (k + 1)))) = 2 * 3 ^ k

/-- `φ(3^(k+1)) = 2·3^k`. -/
theorem totient_three_pow_succ (k : ℕ) : φ (3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_prime_pow_succ Nat.prime_three]
  omega

theorem one_lt_familyP (n : ℕ) : 1 < familyP n := by
  have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  simp only [familyP]
  omega

theorem familyP_sub_one (n : ℕ) : familyP n - 1 = 127 * 2 ^ n := by simp [familyP]

/-- `x ≡ 2` or `5 (mod 9)` hands over the lifting witness *symbolically*: `x² = 1 + 3a` with
`3 ∤ a`, i.e. `v₃(x² − 1) = 1` exactly.  §3 exhibited this witness for KoalaBear as a
19-digit literal; here it is a polynomial in `x / 9`. -/
private theorem exists_liftWitness_of_mod_nine {x : ℕ} (hx : x % 9 = 2 ∨ x % 9 = 5) :
    ∃ a : ℤ, ((x : ℕ) : ℤ) ^ 2 = 1 + 3 * a ∧ ¬(3 : ℤ) ∣ a := by
  obtain ⟨m, hm⟩ : ∃ m, x = 9 * m + x % 9 := ⟨x / 9, by omega⟩
  rcases hx with h | h
  · refine ⟨27 * (m : ℤ) ^ 2 + 12 * (m : ℤ) + 1, by rw [hm, h]; push_cast; ring, ?_⟩
    rintro ⟨c, hc⟩
    obtain ⟨M, hM⟩ : ∃ M : ℤ, (m : ℤ) ^ 2 = M := ⟨_, rfl⟩
    rw [hM] at hc
    omega
  · refine ⟨27 * (m : ℤ) ^ 2 + 30 * (m : ℤ) + 8, by rw [hm, h]; push_cast; ring, ?_⟩
    rintro ⟨c, hc⟩
    obtain ⟨M, hM⟩ : ∃ M : ℤ, (m : ℤ) ^ 2 = M := ⟨_, rfl⟩
    rw [hM] at hc
    omega

/-- **The general lifted-order theorem.**  Any `x ≡ 2` or `5 (mod 9)` — the two primitive
roots of `(ℤ/9)ˣ` — has order exactly `2·3^k` modulo `3^(k+1)`, for every `k`.  This is §3's
KoalaBear proof with the numerical witness replaced by the symbolic one; note that primality
of `x` is used nowhere. -/
theorem orderOf_three_pow_of_mod_nine {x : ℕ} (hx : x % 9 = 2 ∨ x % 9 = 5) (k : ℕ) :
    orderOf ((x : ZMod (3 ^ (k + 1)))) = 2 * 3 ^ k := by
  obtain ⟨a, ha, ha3⟩ := exists_liftWitness_of_mod_nine hx
  have hx3 : x % 3 = 2 := by omega
  set y : ZMod (3 ^ (k + 1)) := ((x : ℕ) : ZMod (3 ^ (k + 1))) with hydef
  -- (a) `y²` has order `3^k`, by lifting the exponent from the symbolic witness.
  have hord2 : orderOf (y ^ 2) = 3 ^ k := by
    have h := ZMod.orderOf_one_add_mul_prime (p := 3) Nat.prime_three (by norm_num) a ha3 k
    rw [← h]
    congr 1
    have hcast := congrArg (fun z : ℤ => (z : ZMod (3 ^ (k + 1)))) ha
    push_cast at hcast ⊢
    rw [hydef]
    exact hcast
  -- (b) the order is even, because `x ≡ 2 (mod 3)`.
  have hdvd : (3 : ℕ) ∣ 3 ^ (k + 1) := dvd_pow_self 3 (Nat.succ_ne_zero k)
  have hcast3 : (ZMod.castHom hdvd (ZMod 3)) y = (2 : ZMod 3) := by
    rw [hydef, map_natCast, ← ZMod.natCast_mod, hx3]
    norm_num
  have h2ord : orderOf ((2 : ZMod 3)) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by decide) (by decide)
  have hmap : orderOf ((ZMod.castHom hdvd (ZMod 3)) y) ∣ orderOf y :=
    orderOf_map_dvd (ZMod.castHom hdvd (ZMod 3)).toMonoidHom y
  have h2 : 2 ∣ orderOf y := by rwa [hcast3, h2ord] at hmap
  -- (c) `3^k ∣ orderOf y` and `orderOf y ∣ 2·3^k`.
  have h3k : 3 ^ k ∣ orderOf y := hord2 ▸ orderOf_pow_dvd (x := y) 2
  have hupper : orderOf y ∣ 2 * 3 ^ k := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [pow_mul, ← hord2, pow_orderOf_eq_one]
  have hco : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact Nat.dvd_antisymm hupper (Nat.Coprime.mul_dvd_of_dvd_of_dvd hco h2 h3k)

/-- `2ⁿ mod 9` has period 6 (`2⁶ = 64 ≡ 1`), so `familyP n mod 9` is decided by `n mod 6`:
the cycle is `(2, 3, 5, 0, 8, 6)` at `n ≡ (0, 1, 2, 3, 4, 5) (mod 6)`. -/
theorem familyP_mod_nine (n : ℕ) : familyP n % 9 = (2 ^ (n % 6) + 1) % 9 := by
  have h : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
    conv_lhs => rw [← Nat.div_add_mod n 6]
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    have h64 : (2 : ℕ) ^ 6 % 9 = 1 := by norm_num
    rw [h64, one_pow]
    omega
  simp only [familyP]
  omega

/-- The residues `n ≡ 1, 3, 5 (mod 6)` contain NO primes: there `3 ∣ familyP n`.  So the
family's populated residues mod 6 are exactly `{0, 2, 4}`, and the failing side of the law
lives entirely at `n ≡ 4` (§9). -/
theorem not_prime_familyP_of_mod_six {n : ℕ} (h : n % 6 = 1 ∨ n % 6 = 3 ∨ n % 6 = 5) :
    ¬(familyP n).Prime := by
  intro hp
  have hmod := familyP_mod_nine n
  have hlarge : 127 ≤ familyP n := by
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    simp only [familyP]
    omega
  have h3 : familyP n % 3 = 0 := by
    rcases h with h | h | h <;> rw [h] at hmod <;> norm_num at hmod <;> omega
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h3)
  omega

/-- **THE FAMILY LAW.**  For a PRIME `p = 127·2ⁿ + 1`: maximal 3-adic inertia holds iff
`n ≡ 0` or `2 (mod 6)`.  Forward direction: `n ≡ 1, 3, 5` contradict primality
(`not_prime_familyP_of_mod_six`) and `n ≡ 4` puts `p ≡ −1 (mod 9)`, order 2 at conductor 9,
refuting the `k = 1` instance.  Backward: those residues put `p mod 9` on a primitive root
of `(ℤ/9)ˣ` and `orderOf_three_pow_of_mod_nine` lifts it to every `k`. -/
theorem familyP_maximalInertia_iff {n : ℕ} (hp : (familyP n).Prime) :
    MaximalThreeAdicInertia (familyP n) ↔ n % 6 = 0 ∨ n % 6 = 2 := by
  constructor
  · intro hmax
    by_contra hcon
    have h6 : n % 6 = 4 ∨ (n % 6 = 1 ∨ n % 6 = 3 ∨ n % 6 = 5) := by omega
    rcases h6 with h | h
    · -- `p ≡ 8 ≡ −1 (mod 9)`: order 2 at conductor 9, but `hmax 1` demands 6.
      have hmod := familyP_mod_nine n
      rw [h] at hmod
      norm_num at hmod
      have h1 := hmax 1
      norm_num at h1
      rw [show ((familyP n : ZMod 9)) = ((8 : ℕ) : ZMod 9) by
        rw [← ZMod.natCast_mod, hmod]] at h1
      have h8 : orderOf (((8 : ℕ) : ZMod 9)) = 2 := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (by decide) (by decide)
      omega
    · exact absurd hp (not_prime_familyP_of_mod_six h)
  · intro hn k
    refine orderOf_three_pow_of_mod_nine ?_ k
    have hmod := familyP_mod_nine n
    rcases hn with h | h
    · rw [h] at hmod
      norm_num at hmod
      exact Or.inl hmod
    · rw [h] at hmod
      norm_num at hmod
      exact Or.inr hmod

/-- The promised equivalence: maximal 3-adic inertia ⟺ `Φ_{3^(k+1)}` irreducible over `F_p`
at every `k`.  Both directions are §1's bridge; the totient bookkeeping is
`totient_three_pow_succ`. -/
theorem maximalThreeAdicInertia_iff_irreducible {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    MaximalThreeAdicInertia p ↔ ∀ k : ℕ, Irreducible (cyclotomic (3 ^ (k + 1)) (ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnd : ∀ e : ℕ, ¬p ∣ 3 ^ e := fun e h => hp3 (prime_dvd_three_pow hp h)
  constructor
  · intro h k
    exact irreducible_cyclotomic_of_orderOf_eq_totient (hnd _)
      ((h k).trans (totient_three_pow_succ k).symm)
  · intro h k
    have horder : orderOf ((p : ZMod (3 ^ (k + 1)))) = φ (3 ^ (k + 1)) := by
      by_contra hne
      exact not_irreducible_cyclotomic_of_orderOf_ne_totient (hnd _) hne (h k)
    rw [horder, totient_three_pow_succ]

theorem koalaBear_eq_familyP : koalaBear = familyP 24 := by norm_num [koalaBear, familyP]

/-- KoalaBear's maximal inertia as an INSTANCE of the family law: `24 ≡ 0 (mod 6)`. -/
theorem maximalInertia_koalaBear : MaximalThreeAdicInertia koalaBear := by
  rw [koalaBear_eq_familyP]
  exact (familyP_maximalInertia_iff (koalaBear_eq_familyP ▸ koalaBear_prime)).mpr
    (Or.inl (by norm_num))

/-- **The cross-check, family edition.**  The SAME statement as
`orderOf_koalaBear_three_pow` (§3), re-derived from the family law rather than from the
numerical lifting witness — a third independent derivation of the `k = 3` headline, and a
second of the all-`k` theorem.  §3's theorem is kept; this one certifies that the family
law specializes to it. -/
theorem orderOf_koalaBear_three_pow_of_family (k : ℕ) :
    orderOf ((koalaBear : ZMod (3 ^ (k + 1)))) = 2 * 3 ^ k :=
  maximalInertia_koalaBear k

/-! ## 7. Kernel-checked modular exponentiation, and Lucas primality for the family

`Nat.Prime` by `norm_num` is trial division — hopeless at 2⁶¹.  But `familyP n − 1 = 127·2ⁿ`
factors by construction, so Lucas's theorem (`Mathlib.NumberTheory.LucasPrimality`) needs
exactly three modular powers of a witness.  `powMod` is binary exponentiation, structurally
recursive in an explicit fuel so that the KERNEL evaluates it through GMP-accelerated `Nat`
arithmetic: every certificate below is `decide`, never `native_decide` — no compiler in the
trust base, and the axiom pins (§11) stay `[propext, Classical.choice, Quot.sound]`. -/

/-- Binary modular exponentiation with structural fuel: `powMod p fuel a e = a ^ e % p`
whenever `e < 2 ^ fuel` (`powMod_eq`).  Kernel-evaluable by `decide`. -/
def powMod (p : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % p
  | fuel + 1, a, e =>
    if e = 0 then 1 % p
    else if e % 2 = 1 then powMod p fuel (a * a % p) (e / 2) * (a % p) % p
    else powMod p fuel (a * a % p) (e / 2)

theorem powMod_eq (p : ℕ) : ∀ fuel a e, e < 2 ^ fuel → powMod p fuel a e = a ^ e % p := by
  intro fuel
  induction fuel with
  | zero =>
    intro a e he
    have he0 : e = 0 := Nat.lt_one_iff.mp (by simpa using he)
    subst he0
    simp [powMod]
  | succ fuel ih =>
    intro a e he
    by_cases h0 : e = 0
    · subst h0
      simp [powMod]
    · have hlt : e / 2 < 2 ^ fuel := by
        have h2 : (2 : ℕ) ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      have key : powMod p fuel (a * a % p) (e / 2) = a ^ (2 * (e / 2)) % p := by
        rw [ih (a * a % p) (e / 2) hlt, ← Nat.pow_mod, ← pow_two, ← pow_mul]
      simp only [powMod]
      rw [if_neg h0]
      by_cases hpar : e % 2 = 1
      · rw [if_pos hpar, key, ← Nat.mul_mod, ← pow_succ]
        have he2 : 2 * (e / 2) + 1 = e := by omega
        rw [he2]
      · rw [if_neg hpar, key]
        have he2 : 2 * (e / 2) = e := by omega
        rw [he2]

/-- The bridge from a kernel-computed `powMod` value to a `ZMod` power equation. -/
theorem natCast_pow_eq_one_iff_powMod {p a e : ℕ} (fuel : ℕ) (hp : 1 < p)
    (he : e < 2 ^ fuel) : ((a : ZMod p)) ^ e = 1 ↔ powMod p fuel a e = 1 := by
  rw [powMod_eq p fuel a e he, ← Nat.cast_pow,
    show (1 : ZMod p) = ((1 : ℕ) : ZMod p) by norm_cast,
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hp]

/-- **Lucas primality for the family**, from three kernel-checked powers of a witness `a`:
`a^(127·2^(m+1)) = 1`, `a^(127·2^m) ≠ 1`, `a^(2^(m+1)) ≠ 1` modulo `familyP (m+1)`.  The
two proper-divisor exponents cover both prime divisors `{2, 127}` of `p − 1`, which is the
whole point of the Solinas shape: the Lucas certificate is three lines. -/
theorem familyP_prime_of_powMod {m a fuel : ℕ} (hfuel : 127 * 2 ^ (m + 1) < 2 ^ fuel)
    (h1 : powMod (familyP (m + 1)) fuel a (127 * 2 ^ (m + 1)) = 1)
    (h2 : powMod (familyP (m + 1)) fuel a (127 * 2 ^ m) ≠ 1)
    (h3 : powMod (familyP (m + 1)) fuel a (2 ^ (m + 1)) ≠ 1) :
    (familyP (m + 1)).Prime := by
  have hplt : 1 < familyP (m + 1) := one_lt_familyP _
  have hsub : familyP (m + 1) - 1 = 127 * 2 ^ (m + 1) := familyP_sub_one _
  have hb2 : 127 * 2 ^ m < 2 ^ fuel := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (Nat.le_succ m)
    omega
  have hb3 : 2 ^ (m + 1) < 2 ^ fuel := by omega
  refine lucas_primality _ ((a : ℕ) : ZMod (familyP (m + 1))) ?_ ?_
  · rw [hsub]
    exact (natCast_pow_eq_one_iff_powMod fuel hplt hfuel).mpr h1
  · intro q hq hqd
    rw [hsub] at hqd
    rw [hsub]
    rcases (Nat.Prime.dvd_mul hq).mp hqd with hd | hd
    · obtain rfl : q = 127 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp hd
      rw [Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 127)]
      exact fun hcon => h3 ((natCast_pow_eq_one_iff_powMod fuel hplt hb3).mp hcon)
    · obtain rfl : q = 2 :=
        (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hd)
      have hdiv : 127 * 2 ^ (m + 1) / 2 = 127 * 2 ^ m := by
        rw [pow_succ, ← mul_assoc]
        exact Nat.mul_div_cancel _ (by norm_num)
      rw [hdiv]
      exact fun hcon => h2 ((natCast_pow_eq_one_iff_powMod fuel hplt hb2).mp hcon)

/-! ## 8. The sibling instance — p61 `= 2⁶¹ − 2⁵⁴ + 1 = 127·2⁵⁴ + 1`

KoalaBear one machine word up: same Solinas shape, same cofactor 127, two-adicity 54 in
place of 24.  `54 ≡ 0 (mod 6)`, so the family law gives it maximal 3-adic inertia — the
property Goldilocks and BabyBear both lack — while `p61 − 1 = 2⁵⁴·127` gives it FRI/NTT
domains to `2⁵⁴` (§10).  Everything below mirrors §3's KoalaBear section. -/

/-- **p61**, `2⁶¹ − 2⁵⁴ + 1 = 2287828610704211969`. -/
def p61 : ℕ := 2 ^ 61 - 2 ^ 54 + 1

theorem p61_eq : p61 = 2287828610704211969 := by norm_num [p61]

/-- The Solinas/family identity: `p61 = 127·2⁵⁴ + 1`. -/
theorem p61_eq_familyP : p61 = familyP 54 := by norm_num [p61, familyP]

/-- `p61 − 1 = 2⁵⁴·127`: two-adicity at least 54 (exactly 54 by
`not_two_pow_55_dvd_p61_sub_one`). -/
theorem p61_sub_one : p61 - 1 = 2 ^ 54 * 127 := by rw [p61_eq]; norm_num

/-- …and exactly 54: `2⁵⁵ ∤ p61 − 1`, since the cofactor 127 is odd. -/
theorem not_two_pow_55_dvd_p61_sub_one : ¬2 ^ 55 ∣ p61 - 1 := by
  rw [p61_sub_one]
  norm_num

/-- `p61 ≡ 1 (mod 2¹³)`: the whole `N = 8192` negacyclic/NTT ladder of root-of-unity
orders divides `p61 − 1` with 41 powers of two to spare. -/
theorem p61_mod_8192 : p61 % 8192 = 1 := by rw [p61_eq]

set_option maxRecDepth 40000 in
/-- **p61 is prime** — Lucas certificate with witness 3, checked by the kernel
(`decide` through `powMod`; no `native_decide`). -/
theorem p61_prime : Nat.Prime p61 := by
  rw [p61_eq_familyP]
  exact familyP_prime_of_powMod (m := 53) (a := 3) (fuel := 64)
    (by norm_num) (by decide) (by decide) (by decide)

instance : Fact (Nat.Prime p61) := ⟨p61_prime⟩

/-- p61 has maximal 3-adic inertia: the family law at `54 ≡ 0 (mod 6)`. -/
theorem maximalInertia_p61 : MaximalThreeAdicInertia p61 := by
  rw [p61_eq_familyP]
  exact (familyP_maximalInertia_iff (p61_eq_familyP ▸ p61_prime)).mpr (Or.inl (by norm_num))

/-- `ord_{3^(k+1)}(p61) = 2·3^k` at every `k` — the mirror of
`orderOf_koalaBear_three_pow`. -/
theorem orderOf_p61_three_pow (k : ℕ) :
    orderOf ((p61 : ZMod (3 ^ (k + 1)))) = 2 * 3 ^ k :=
  maximalInertia_p61 k

theorem p61_not_dvd_three_pow (k : ℕ) : ¬p61 ∣ 3 ^ k := fun h => by
  have h3 := prime_dvd_three_pow p61_prime h
  rw [p61_eq] at h3
  norm_num at h3

/-- `Φ_{3^(k+1)}` is IRREDUCIBLE over `F_p61`, at every `k`. -/
theorem irreducible_cyclotomic_three_pow_p61 (k : ℕ) :
    Irreducible (cyclotomic (3 ^ (k + 1)) (ZMod p61)) :=
  irreducible_cyclotomic_of_orderOf_eq_totient (p61_not_dvd_three_pow (k + 1))
    ((orderOf_p61_three_pow k).trans (totient_three_pow_succ k).symm)

/-- The headline conductor: `Φ₈₁` is irreducible over `F_p61`. -/
theorem irreducible_cyclotomic_81_p61 : Irreducible (cyclotomic 81 (ZMod p61)) := by
  have h := irreducible_cyclotomic_three_pow_p61 3
  norm_num at h
  exact h

instance : Fact (Irreducible (cyclotomic 81 (ZMod p61))) := ⟨irreducible_cyclotomic_81_p61⟩

/-- `R_q := F_p61[X]/(Φ₈₁)` — the p61 lattice-commitment ring at conductor 81. -/
abbrev P61Cyc81 : Type := AdjoinRoot (cyclotomic 81 (ZMod p61))

/-- `F_p61[X]/(Φ₈₁)` is a FIELD — the p61 mirror of `KBCyc81_isField`. -/
theorem P61Cyc81_isField : IsField P61Cyc81 := Field.toIsField _

/-- …of degree `54 = φ(81)` over `F_p61`.  Maximal inertia, one factor. -/
theorem P61Cyc81_finrank : Module.finrank (ZMod p61) P61Cyc81 = 54 := by
  have hne : (cyclotomic 81 (ZMod p61)) ≠ 0 := cyclotomic_ne_zero 81 _
  rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim hne,
    natDegree_cyclotomic, totient_81]

/-! ## 9. TOOTH C — the family law's failing side is inhabited

A hypothesis never shown to be a constraint is not a hypothesis (§4–5 said this for the
conductor and the field; here it is said for the RESIDUE).  The bad classes are thin:
`n ≡ 1, 3, 5 (mod 6)` contain no primes at all (`not_prime_familyP_of_mod_six`), and in
`n ≡ 4 (mod 6)` the candidates `n = 4 (2033 = 19·107), 10, 16, …, 208` are ALL composite —
the smallest prime member of the bad class is **`n = 214`**, a 67-digit prime (Lucas again;
its `p − 1 = 127·2²¹⁴` factors by construction).  There the law's failing side bites:
`p ≡ 8 ≡ −1 (mod 9)`, order 2, and `Φ₉` splits into exactly **3** quadratic factors —
the refutation witness. -/

theorem familyP_four_eq : familyP 4 = 2033 := by norm_num [familyP]

/-- The first bad-class candidate is COMPOSITE: `2033 = 19·107`.  (So the tooth needs
`n = 214`; every bad-class `n < 214` fails primality.) -/
theorem not_prime_familyP_four : ¬(familyP 4).Prime := by
  rw [familyP_four_eq]
  norm_num

/-- `214 ≡ 4 (mod 6)` — the populated bad class. -/
theorem two_hundred_fourteen_mod_six : 214 % 6 = 4 := by norm_num

set_option maxRecDepth 150000 in
/-- **The bad-class prime**: `familyP 214 = 127·2²¹⁴ + 1` is prime (Lucas, witness 3,
kernel-checked). -/
theorem familyP_214_prime : (familyP 214).Prime :=
  familyP_prime_of_powMod (m := 213) (a := 3) (fuel := 224)
    (by norm_num) (by decide) (by decide) (by decide)

instance : Fact (Nat.Prime (familyP 214)) := ⟨familyP_214_prime⟩

/-- **The tooth at the law level**: the bad-class prime does NOT have maximal inertia. -/
theorem not_maximalInertia_familyP_214 : ¬MaximalThreeAdicInertia (familyP 214) := fun h => by
  rcases (familyP_maximalInertia_iff familyP_214_prime).mp h with hc | hc <;> norm_num at hc

/-- Where it fails: `familyP 214 ≡ 8 ≡ −1 (mod 9)`, so its order at conductor 9 is 2,
against `φ(9) = 6`. -/
theorem orderOf_familyP_214_mod_nine : orderOf ((familyP 214 : ZMod 9)) = 2 := by
  have hmod := familyP_mod_nine 214
  norm_num at hmod
  rw [show ((familyP 214 : ZMod 9)) = ((8 : ℕ) : ZMod 9) by rw [← ZMod.natCast_mod, hmod]]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by decide) (by decide)

theorem totient_nine : φ 9 = 6 := by
  rw [show (9 : ℕ) = 3 ^ (1 + 1) by norm_num, totient_three_pow_succ]
  norm_num

private theorem familyP_not_dvd_nine (n : ℕ) : ¬familyP n ∣ 9 := by
  intro h
  have hle := Nat.le_of_dvd (by norm_num) h
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  simp only [familyP] at hle
  omega

/-- `Φ₉` is REDUCIBLE over the bad-class prime — inertia fails at the first conductor. -/
theorem not_irreducible_cyclotomic_9_familyP_214 :
    ¬Irreducible (cyclotomic 9 (ZMod (familyP 214))) := by
  refine not_irreducible_cyclotomic_of_orderOf_ne_totient (familyP_not_dvd_nine 214) ?_
  rw [orderOf_familyP_214_mod_nine, totient_nine]
  norm_num

open UniqueFactorizationMonoid in
/-- **The factor count as the refutation witness**: `Φ₉` splits into exactly **3** distinct
monic irreducible factors over `F_(familyP 214)` — against 1 factor (irreducibility) at every
good-class prime.  With `natDegree_factor_9_familyP_214`, each factor is quadratic. -/
theorem card_factors_9_familyP_214 :
    (normalizedFactors (cyclotomic 9 (ZMod (familyP 214)))).toFinset.card = 3 := by
  rw [card_normalizedFactors (familyP_not_dvd_nine 214), orderOf_familyP_214_mod_nine,
    totient_nine]

open UniqueFactorizationMonoid in
/-- …and each of the 3 factors has degree exactly 2 (= the collapsed order). -/
theorem natDegree_factor_9_familyP_214 {P : (ZMod (familyP 214))[X]}
    (hP : P ∈ normalizedFactors (cyclotomic 9 (ZMod (familyP 214)))) : P.natDegree = 2 := by
  rw [natDegree_of_mem_normalizedFactors (familyP_not_dvd_nine 214) hP,
    orderOf_familyP_214_mod_nine]

/-! ## 10. Domain availability — an FFT/FRI domain of size `2^(ν+1)` is a subgroup of `F_pˣ`,
and Lagrange decides whether it EXISTS

`F_pˣ` is cyclic of order `p − 1`, so a (cyclic) subgroup of order `d` exists iff `d ∣ p − 1`
— and for `d = 2^(ν+1)` that is exactly `ν + 1 ≤ v₂(p − 1)`.  The negative direction is
Lagrange: no subgroup order can fail to divide `p − 1`.  Instantiated at **Goldilocks**
(`v₂ = 32`: domains to `2³²`, none at `2³³` — the deployed panic) and **p61** (`v₂ = 54`:
domains to `2⁵⁴`, none at `2⁵⁵`).  Arithmetic existence statements about subgroups; they
price nothing about FRI soundness. -/

section DomainAvailability

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Positive, element form.**  For every `d ∣ p − 1` there is an `x ∈ F_pˣ` of order
exactly `d` — the generator of the size-`d` domain (a primitive `d`-th root of unity). -/
theorem exists_unitsZMod_orderOf_eq {d : ℕ} (hd : d ∣ p - 1) :
    ∃ x : (ZMod p)ˣ, orderOf x = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hordg : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨c, hc⟩ := hd
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · have := hp.out.two_le
      omega
    · exact h
  refine ⟨g ^ c, Nat.dvd_antisymm ?_ ?_⟩
  · refine orderOf_dvd_of_pow_eq_one ?_
    rw [← pow_mul, mul_comm c d, ← hc, ← hordg, pow_orderOf_eq_one]
  · have h1 : g ^ (c * orderOf (g ^ c)) = 1 := by
      rw [pow_mul]
      exact pow_orderOf_eq_one _
    have h2 : p - 1 ∣ c * orderOf (g ^ c) := by
      rw [← hordg]
      exact orderOf_dvd_of_pow_eq_one h1
    rw [hc, mul_comm d c] at h2
    exact (Nat.mul_dvd_mul_iff_left hc0).mp h2

/-- **Positive, subgroup form**: a CYCLIC subgroup of `F_pˣ` of order `d`, for every
`d ∣ p − 1`. -/
theorem exists_subgroup_card_eq {d : ℕ} (hd : d ∣ p - 1) :
    ∃ H : Subgroup (ZMod p)ˣ, IsCyclic H ∧ Nat.card H = d := by
  obtain ⟨x, hx⟩ := exists_unitsZMod_orderOf_eq hd
  exact ⟨Subgroup.zpowers x, inferInstance, by rw [Nat.card_zpowers, hx]⟩

/-- **Negative, element form** (Lagrange): if `d ∤ p − 1` then NO element of `F_pˣ` has
order `d`. -/
theorem not_exists_unitsZMod_orderOf_eq {d : ℕ} (hd : ¬d ∣ p - 1) :
    ¬∃ x : (ZMod p)ˣ, orderOf x = d := by
  rintro ⟨x, rfl⟩
  exact hd (ZMod.card_units p ▸ orderOf_dvd_card)

/-- **Negative, subgroup form** (Lagrange): if `d ∤ p − 1` then `F_pˣ` has NO subgroup of
order `d` — cyclic or otherwise. -/
theorem not_exists_subgroup_card_eq {d : ℕ} (hd : ¬d ∣ p - 1) :
    ¬∃ H : Subgroup (ZMod p)ˣ, Nat.card H = d := by
  rintro ⟨H, rfl⟩
  refine hd ?_
  have h := Subgroup.card_subgroup_dvd_card H
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  rwa [hcard] at h

end DomainAvailability

/-- **Goldilocks**, `2⁶⁴ − 2³² + 1 = 18446744069414584321` — the deployed 64-bit FFT prime,
here as the domain-availability refutation. -/
def goldilocks : ℕ := 2 ^ 64 - 2 ^ 32 + 1

theorem goldilocks_eq : goldilocks = 18446744069414584321 := by norm_num [goldilocks]

/-- `Goldilocks − 1 = 2³²·(2³² − 1)`: two-adicity at least 32 (exactly 32 by
`not_two_pow_33_dvd_goldilocks_sub_one`). -/
theorem goldilocks_sub_one : goldilocks - 1 = 2 ^ 32 * 4294967295 := by
  norm_num [goldilocks]

private theorem prime_dvd_goldilocks_sub_one {q : ℕ} (hq : q.Prime)
    (h : q ∣ goldilocks - 1) : q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
  rw [show goldilocks - 1 = 2 ^ 32 * (3 * (5 * (17 * (257 * 65537)))) by
    norm_num [goldilocks]] at h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact Or.inr <| Or.inl <| (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact Or.inr <| Or.inr <| Or.inl <| (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  rcases (Nat.Prime.dvd_mul hq).mp h with h | h
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <|
      (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h

set_option maxRecDepth 40000 in
/-- **Goldilocks is prime** — Lucas certificate with witness 7 over the fully factored
`p − 1 = 2³²·3·5·17·257·65537`, kernel-checked (`decide` through `powMod`). -/
theorem goldilocks_prime : Nat.Prime goldilocks := by
  have hplt : (1 : ℕ) < goldilocks := by norm_num [goldilocks]
  refine lucas_primality _ ((7 : ℕ) : ZMod goldilocks) ?_ ?_
  · rw [show goldilocks - 1 = 18446744069414584320 by norm_num [goldilocks]]
    exact (natCast_pow_eq_one_iff_powMod 64 hplt (by norm_num)).mpr (by decide)
  · intro q hq hqd
    rcases prime_dvd_goldilocks_sub_one hq hqd with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show (goldilocks - 1) / 2 = 9223372034707292160 by norm_num [goldilocks]]
      exact fun hcon => (by decide : powMod goldilocks 64 7 9223372034707292160 ≠ 1)
        ((natCast_pow_eq_one_iff_powMod 64 hplt (by norm_num)).mp hcon)
    · rw [show (goldilocks - 1) / 3 = 6148914689804861440 by norm_num [goldilocks]]
      exact fun hcon => (by decide : powMod goldilocks 64 7 6148914689804861440 ≠ 1)
        ((natCast_pow_eq_one_iff_powMod 64 hplt (by norm_num)).mp hcon)
    · rw [show (goldilocks - 1) / 5 = 3689348813882916864 by norm_num [goldilocks]]
      exact fun hcon => (by decide : powMod goldilocks 64 7 3689348813882916864 ≠ 1)
        ((natCast_pow_eq_one_iff_powMod 64 hplt (by norm_num)).mp hcon)
    · rw [show (goldilocks - 1) / 17 = 1085102592318504960 by norm_num [goldilocks]]
      exact fun hcon => (by decide : powMod goldilocks 64 7 1085102592318504960 ≠ 1)
        ((natCast_pow_eq_one_iff_powMod 64 hplt (by norm_num)).mp hcon)
    · rw [show (goldilocks - 1) / 257 = 71777214277877760 by norm_num [goldilocks]]
      exact fun hcon => (by decide : powMod goldilocks 64 7 71777214277877760 ≠ 1)
        ((natCast_pow_eq_one_iff_powMod 64 hplt (by norm_num)).mp hcon)
    · rw [show (goldilocks - 1) / 65537 = 281470681743360 by norm_num [goldilocks]]
      exact fun hcon => (by decide : powMod goldilocks 64 7 281470681743360 ≠ 1)
        ((natCast_pow_eq_one_iff_powMod 64 hplt (by norm_num)).mp hcon)

instance : Fact (Nat.Prime goldilocks) := ⟨goldilocks_prime⟩

theorem two_pow_dvd_goldilocks_sub_one {ν : ℕ} (h : ν + 1 ≤ 32) :
    2 ^ (ν + 1) ∣ goldilocks - 1 :=
  dvd_trans (pow_dvd_pow 2 h) ⟨4294967295, goldilocks_sub_one⟩

/-- …and exactly 32: `2³³ ∤ Goldilocks − 1`, since `2³² − 1` is odd. -/
theorem not_two_pow_33_dvd_goldilocks_sub_one : ¬2 ^ 33 ∣ goldilocks - 1 := by
  rw [goldilocks_sub_one]
  norm_num

/-- Goldilocks HAS every two-adic domain up to `2³²`: for `ν + 1 ≤ 32`, a cyclic subgroup
of `F_pˣ` of order `2^(ν+1)` exists. -/
theorem goldilocks_domain_exists {ν : ℕ} (h : ν + 1 ≤ 32) :
    ∃ H : Subgroup (ZMod goldilocks)ˣ, IsCyclic H ∧ Nat.card H = 2 ^ (ν + 1) :=
  exists_subgroup_card_eq (two_pow_dvd_goldilocks_sub_one h)

/-- **The deployed panic, stated as mathematics.**  `F_goldilocksˣ` has NO subgroup of
order `2³³` — by Lagrange, since `v₂(p − 1) = 32` exactly.  A domain constructor asked for
a coset-LDE domain at `ν = 32` needs an order-`2³³` subgroup to exist; this theorem is why
`Domain::new(2^32)` panics in the deployed Goldilocks matvecmul stack (measured 2026-08:
the `D·t·n ≤ 2³¹` hard stop), and no code change can lift it — only a modulus change
(§8: p61 moves the wall to `2⁵⁴`). -/
theorem goldilocks_no_domain_two_pow_33 :
    ¬∃ H : Subgroup (ZMod goldilocks)ˣ, Nat.card H = 2 ^ 33 :=
  not_exists_subgroup_card_eq not_two_pow_33_dvd_goldilocks_sub_one

theorem two_pow_dvd_p61_sub_one {ν : ℕ} (h : ν + 1 ≤ 54) : 2 ^ (ν + 1) ∣ p61 - 1 :=
  dvd_trans (pow_dvd_pow 2 h) ⟨127, p61_sub_one⟩

/-- p61 HAS every two-adic domain up to `2⁵⁴` — `2²²` times Goldilocks' ceiling. -/
theorem p61_domain_exists {ν : ℕ} (h : ν + 1 ≤ 54) :
    ∃ H : Subgroup (ZMod p61)ˣ, IsCyclic H ∧ Nat.card H = 2 ^ (ν + 1) :=
  exists_subgroup_card_eq (two_pow_dvd_p61_sub_one h)

/-- …and its own wall, in the same voice: no subgroup of order `2⁵⁵`. -/
theorem p61_no_domain_two_pow_55 :
    ¬∃ H : Subgroup (ZMod p61)ˣ, Nat.card H = 2 ^ 55 :=
  not_exists_subgroup_card_eq not_two_pow_55_dvd_p61_sub_one

/-! ## 11. Axiom pins -/

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
/-- info: 'Minidregg.Theory.CyclotomicInertia.orderOf_three_pow_of_mod_nine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderOf_three_pow_of_mod_nine
/-- info: 'Minidregg.Theory.CyclotomicInertia.familyP_mod_nine' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms familyP_mod_nine
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_prime_familyP_of_mod_six' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_prime_familyP_of_mod_six
/-- info: 'Minidregg.Theory.CyclotomicInertia.familyP_maximalInertia_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms familyP_maximalInertia_iff
/-- info: 'Minidregg.Theory.CyclotomicInertia.maximalThreeAdicInertia_iff_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maximalThreeAdicInertia_iff_irreducible
/-- info: 'Minidregg.Theory.CyclotomicInertia.maximalInertia_koalaBear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maximalInertia_koalaBear
/-- info: 'Minidregg.Theory.CyclotomicInertia.orderOf_koalaBear_three_pow_of_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderOf_koalaBear_three_pow_of_family
/-- info: 'Minidregg.Theory.CyclotomicInertia.powMod_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms powMod_eq
/-- info: 'Minidregg.Theory.CyclotomicInertia.familyP_prime_of_powMod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms familyP_prime_of_powMod
/-- info: 'Minidregg.Theory.CyclotomicInertia.p61_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms p61_prime
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_two_pow_55_dvd_p61_sub_one' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms not_two_pow_55_dvd_p61_sub_one
/-- info: 'Minidregg.Theory.CyclotomicInertia.p61_mod_8192' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms p61_mod_8192
/-- info: 'Minidregg.Theory.CyclotomicInertia.maximalInertia_p61' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maximalInertia_p61
/-- info: 'Minidregg.Theory.CyclotomicInertia.irreducible_cyclotomic_three_pow_p61' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms irreducible_cyclotomic_three_pow_p61
/-- info: 'Minidregg.Theory.CyclotomicInertia.irreducible_cyclotomic_81_p61' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms irreducible_cyclotomic_81_p61
/-- info: 'Minidregg.Theory.CyclotomicInertia.P61Cyc81_isField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms P61Cyc81_isField
/-- info: 'Minidregg.Theory.CyclotomicInertia.P61Cyc81_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms P61Cyc81_finrank
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_prime_familyP_four' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms not_prime_familyP_four
/-- info: 'Minidregg.Theory.CyclotomicInertia.familyP_214_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms familyP_214_prime
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_maximalInertia_familyP_214' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_maximalInertia_familyP_214
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_irreducible_cyclotomic_9_familyP_214' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_irreducible_cyclotomic_9_familyP_214
/-- info: 'Minidregg.Theory.CyclotomicInertia.card_factors_9_familyP_214' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_factors_9_familyP_214
/-- info: 'Minidregg.Theory.CyclotomicInertia.natDegree_factor_9_familyP_214' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natDegree_factor_9_familyP_214
/-- info: 'Minidregg.Theory.CyclotomicInertia.exists_unitsZMod_orderOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_unitsZMod_orderOf_eq
/-- info: 'Minidregg.Theory.CyclotomicInertia.exists_subgroup_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exists_subgroup_card_eq
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_exists_unitsZMod_orderOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_exists_unitsZMod_orderOf_eq
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_exists_subgroup_card_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_exists_subgroup_card_eq
/-- info: 'Minidregg.Theory.CyclotomicInertia.goldilocks_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goldilocks_prime
/-- info: 'Minidregg.Theory.CyclotomicInertia.not_two_pow_33_dvd_goldilocks_sub_one' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms not_two_pow_33_dvd_goldilocks_sub_one
/-- info: 'Minidregg.Theory.CyclotomicInertia.goldilocks_domain_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goldilocks_domain_exists
/-- info: 'Minidregg.Theory.CyclotomicInertia.goldilocks_no_domain_two_pow_33' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goldilocks_no_domain_two_pow_33
/-- info: 'Minidregg.Theory.CyclotomicInertia.p61_domain_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms p61_domain_exists
/-- info: 'Minidregg.Theory.CyclotomicInertia.p61_no_domain_two_pow_55' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms p61_no_domain_two_pow_55

end Minidregg.Theory.CyclotomicInertia
