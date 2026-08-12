/-
# `Theory.IntegerFingerprint` — `a·b = c + u·m` over ℤ, fingerprinted at a random prime

Statement-first scaffold for the integer-relation obligation at the heart of the
Zaratan/Limber recipe: Chen, Xia, Nguyen and Bünz, *Limber: Low Overhead SNARKs for
Integers from Any PCS*, eprint 2026/1635 (7 Aug 2026); the fingerprinting recipe is
Zaratan's [CHA24].  A moduli-R1CS row (Limber Definition 6.1, `Az ∘ Bz = Cz + mods ∘
quos`, read one row at a time) is the integer equation `a * b = c + u * m`.  The prover
commits the quotient `u`; the verifier then samples a λ-bit prime `p` and checks the
same equation in `Zp` (Definition 6.2, Protocol 6.1).  The whole security of the recipe
rests on that ordering and on the counting fact below.

Everything here is authored in Lean.  No constraint, gadget or acceptance predicate for
this relation exists anywhere else in the tree, and none should be written in Rust.

## What this module establishes

* `Row.HoldsInt` / `Row.HoldsMod` — the two relations, with `Row.residual` as the single
  integer whose vanishing decides both (`holdsInt_iff_residual_eq_zero`,
  `holdsMod_iff_dvd_residual`).
* `fingerprint_complete` — a true integer relation survives **every** fingerprint.  This
  is the easy direction and it is proved outright.
* `pow_card_undetected_le` — the load-bearing counting fact, and the honest core of
  Limber's Lemma 4.29.  If the integer relation FAILS and every prime in the verifier's
  sampling space is at least `B`, then `B ^ (#primes that fail to detect it) ≤ |residual|`,
  because those primes are distinct primes dividing a nonzero integer, so their product
  divides it.
* `card_undetected_le_log` — the same bound in the paper's shape, `#bad ≤ log_B |z|`.
  This is exactly the numerator of Lemma 4.29.
* `fingerprint_error_le` — the soundness error, cross-multiplied over ℕ, plus
  `fingerprint_error_ratio_le`, the same fact written as the ratio `#bad / #space` over ℚ.

## What this module does NOT establish

* **The prime-counting denominator is a hypothesis, not a theorem.**  Lemma 4.29's
  headline `log Tz / 2^(λ-2)` needs Rosser–Schoenfeld bounds on `π(x)` (the paper's
  Theorem 4.28 [RS62], used via its Corollary A.1) to lower-bound
  `|Primes(2^(λ-1), 2^λ)|`.  That analytic input is **not** formalized here.  It enters
  `fingerprint_error_le` as an explicit `spaceFloor ≤ space.card` hypothesis that the
  caller must discharge.  There is no axiom and no `sorry` in this file: the unmet
  obligation is a named hypothesis, and nothing downstream can consume it by accident.
* **Nothing about polynomial commitments.**  Limber's actual contribution is the integer
  mod-PCS of its §5 (limb-splitting, `IntEval`, partial evaluation with modulo
  decomposition, CRT over small random primes).  None of that is modelled here.  This
  module is only the *relation* a mod-PCS is used to check; it makes no commitment,
  extraction or knowledge-soundness claim whatsoever.
* **Nothing about probability spaces.**  "Probability over a uniform draw from `space`"
  is modelled as a cardinality ratio.  That is precisely what the paper's own proof
  computes, but it is a modelling decision stated here, not a measure-theoretic theorem.
* **Nothing about a deployed prover.**  No witness generator, no field embedding, no
  emitted descriptor.  A row here is a mathematical object, not a trace.

## Why the sampling order is load-bearing (the teeth)

`adaptive_quotient_defeats_fingerprint` shows that if the quotient `u` may be chosen
*after* `p` is known, the mod-`p` relation is satisfiable for **every** `a, b, c` with `m`
invertible — this is the paper's own reason (§3.1) that moduli-R1CS cannot be stated over
a field at all.  `forgedRow_repaired_by_other_quotient` is its concrete companion: the
same public `(a, b, c, m)` is satisfiable over ℤ with a *different* quotient, so the
residual is a fact about the committed `u`, never about the row's public part.

`undetected_nonempty` pins the counting bound as non-vacuous from the other side: there
is a concrete row that fails over ℤ and is nevertheless accepted at a concrete prime.

## The accumulator question, answered as arithmetic

`babybear_excluded_from_six_variables` and `goldilocks_clears_limber_min` compute Limber's
own minimum PCS field characteristic (Remark 5.9: with `k = 1` and Soundness Bound 1's
`P > 32λm`, the Partial Evaluation Norm Bound forces `q ≥ 4P²`).  At λ = 128 the floor
already exceeds BabyBear's characteristic once the committed polynomial has six variables,
i.e. 64 hypercube entries.  Goldilocks clears the same floor with enormous room.  This is
the arithmetic behind the report's verdict that Limber's "small fields" means 64-bit, not
31-bit, and it is stated here so it can go red if anyone re-derives the parameters.
-/
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace Minidregg.Theory.IntegerFingerprint

set_option autoImplicit false

/-! ## The relation -/

/-- One row of the integer moduli-R1CS relation `Az ∘ Bz = Cz + mods ∘ quos`
(Limber Definition 6.1).  `u` is the committed quotient (`quos`) and `m` the modulus
(`mods`); `a`, `b`, `c` are the three matrix-vector products at that row. -/
structure Row where
  /-- the `Az` entry -/
  a : ℤ
  /-- the `Bz` entry -/
  b : ℤ
  /-- the `Cz` entry -/
  c : ℤ
  /-- the committed quotient (`quos`) -/
  u : ℤ
  /-- the modulus (`mods`) -/
  m : ℤ
deriving DecidableEq, Repr

namespace Row

/-- The single integer whose vanishing decides the row, over ℤ and modulo every prime. -/
def residual (r : Row) : ℤ := r.a * r.b - (r.c + r.u * r.m)

/-- The integer relation `a · b = c + u · m`.  This is the obligation; the mod-`p` image
below is only evidence for it. -/
def HoldsInt (r : Row) : Prop := r.a * r.b = r.c + r.u * r.m

instance (r : Row) : Decidable r.HoldsInt :=
  inferInstanceAs (Decidable (r.a * r.b = r.c + r.u * r.m))

/-- The fingerprinted image of the row at a prime `p` (Limber Definition 6.2). -/
def HoldsMod (p : ℕ) (r : Row) : Prop :=
  r.a * r.b ≡ r.c + r.u * r.m [ZMOD (p : ℤ)]

instance (p : ℕ) (r : Row) : Decidable (r.HoldsMod p) :=
  inferInstanceAs (Decidable (r.a * r.b % (p : ℤ) = (r.c + r.u * r.m) % (p : ℤ)))

theorem holdsInt_iff_residual_eq_zero (r : Row) : r.HoldsInt ↔ r.residual = 0 := by
  unfold HoldsInt residual
  omega

theorem holdsMod_iff_dvd_residual (p : ℕ) (r : Row) :
    r.HoldsMod p ↔ (p : ℤ) ∣ r.residual := by
  have h : r.c + r.u * r.m - r.a * r.b = -r.residual := by
    unfold residual; ring
  unfold HoldsMod
  rw [Int.modEq_iff_dvd, h, dvd_neg]

/-- **Completeness of fingerprinting.**  A true integer relation survives every prime —
unconditionally, with no bound and no sampling assumption (Limber §3.2, Lemma 6.3's
completeness leg). -/
theorem fingerprint_complete {r : Row} (h : r.HoldsInt) (p : ℕ) : r.HoldsMod p :=
  (holdsMod_iff_dvd_residual p r).mpr <| by
    rw [(holdsInt_iff_residual_eq_zero r).mp h]
    exact dvd_zero _

end Row

/-! ## Soundness of fingerprinting: the counting core -/

/-- The primes in the verifier's sampling space at which the fingerprint fails to detect a
false row.  This is exactly the paper's set `S` of large prime divisors of the residual
(proof of Lemma 4.29). -/
def undetected (space : Finset ℕ) (r : Row) : Finset ℕ :=
  space.filter (fun p => r.HoldsMod p)

theorem mem_undetected {space : Finset ℕ} {r : Row} {p : ℕ} :
    p ∈ undetected space r ↔ p ∈ space ∧ (p : ℤ) ∣ r.residual := by
  simp [undetected, Row.holdsMod_iff_dvd_residual]

/-- **The load-bearing counting fact.**  If the integer relation fails, the primes that
fail to detect it are distinct primes dividing a nonzero integer, so their product divides
that integer.  Bounding each of them below by `B` gives `B ^ #bad ≤ |residual|`.

This is the honest core of Limber's Lemma 4.29: everything else in that lemma is the
analytic estimate of the *denominator*, which this module does not prove. -/
theorem pow_card_undetected_le {space : Finset ℕ} {r : Row} {B : ℕ}
    (hfail : ¬ r.HoldsInt)
    (hprime : ∀ p ∈ space, Nat.Prime p)
    (hfloor : ∀ p ∈ space, B ≤ p) :
    B ^ (undetected space r).card ≤ r.residual.natAbs := by
  have hz : r.residual ≠ 0 := fun h => hfail ((Row.holdsInt_iff_residual_eq_zero r).mpr h)
  have hnat : r.residual.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hdvd : ∀ p ∈ undetected space r, p ∣ r.residual.natAbs := by
    intro p hp
    have hp' : ((p : ℤ)).natAbs ∣ r.residual.natAbs :=
      Int.natAbs_dvd_natAbs.mpr (mem_undetected.mp hp).2
    simpa using hp'
  have hprime' : ∀ p ∈ undetected space r, Prime p := fun p hp =>
    Nat.prime_iff.mp (hprime p (mem_undetected.mp hp).1)
  have hprod : (∏ p ∈ undetected space r, p) ∣ r.residual.natAbs :=
    Finset.prod_primes_dvd _ hprime' hdvd
  have hlow : B ^ (undetected space r).card ≤ ∏ p ∈ undetected space r, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => hfloor p (mem_undetected.mp hp).1
  exact hlow.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hnat) hprod)

/-- The counting fact in the paper's shape: at most `log_B |residual|` primes of the
sampling space are bad. -/
theorem card_undetected_le_log {space : Finset ℕ} {r : Row} {B : ℕ}
    (hB : 1 < B) (hfail : ¬ r.HoldsInt)
    (hprime : ∀ p ∈ space, Nat.Prime p)
    (hfloor : ∀ p ∈ space, B ≤ p) :
    (undetected space r).card ≤ Nat.log B r.residual.natAbs :=
  Nat.le_log_of_pow_le hB (pow_card_undetected_le hfail hprime hfloor)

/-- **Fingerprint soundness error, in the verifier's shape.**

`spaceFloor` is a lower bound on the size of the sampling space and `bound` an upper bound
on the residual (the paper's `Tz`).  Under a uniform draw from `space`, the chance that a
false row goes undetected is `#bad / #space`, and this bounds it by `log_B bound /
spaceFloor`.

⚠ `spaceFloor` is supplied by the caller.  Limber discharges it with Rosser–Schoenfeld
(`|Primes(P/2, P)| > P / (4 log P)`, its Corollary A.1), which is **not** proved in this
file.  Nothing here asserts that the paper's `log Tz / 2^(λ-2)` is a theorem of Lean; only
that it follows from this statement once the prime count is supplied. -/
theorem fingerprint_error_le {space : Finset ℕ} {r : Row} {B spaceFloor bound : ℕ}
    (hB : 1 < B) (hfail : ¬ r.HoldsInt)
    (hprime : ∀ p ∈ space, Nat.Prime p)
    (hfloor : ∀ p ∈ space, B ≤ p)
    (hbound : r.residual.natAbs ≤ bound)
    (hspace : spaceFloor ≤ space.card) :
    (undetected space r).card * spaceFloor ≤ Nat.log B bound * space.card :=
  Nat.mul_le_mul
    ((card_undetected_le_log hB hfail hprime hfloor).trans (Nat.log_mono_right hbound))
    hspace

/-- The same bound read as a fraction, which is the form the paper quotes.  Division is
only notation over the cross-multiplied fact above; the content is `fingerprint_error_le`. -/
theorem fingerprint_error_ratio_le {space : Finset ℕ} {r : Row} {B spaceFloor bound : ℕ}
    (hB : 1 < B) (hfail : ¬ r.HoldsInt)
    (hprime : ∀ p ∈ space, Nat.Prime p)
    (hfloor : ∀ p ∈ space, B ≤ p)
    (hbound : r.residual.natAbs ≤ bound)
    (hfloorPos : 0 < spaceFloor) (hspace : spaceFloor ≤ space.card) :
    ((undetected space r).card : ℚ) / (space.card : ℚ)
      ≤ (Nat.log B bound : ℚ) / (spaceFloor : ℚ) := by
  have hnum : ((undetected space r).card : ℚ) ≤ (Nat.log B bound : ℚ) := by
    exact_mod_cast (card_undetected_le_log hB hfail hprime hfloor).trans
      (Nat.log_mono_right hbound)
  have hden : (spaceFloor : ℚ) ≤ (space.card : ℚ) := by exact_mod_cast hspace
  have hpos : (0 : ℚ) < (spaceFloor : ℚ) := by exact_mod_cast hfloorPos
  have hcard : (0 : ℚ) < (space.card : ℚ) := lt_of_lt_of_le hpos hden
  gcongr

/-! ## Satisfiability -/

/-- Euclidean division always produces a satisfying row: this is exactly how an honest
prover builds its quotient witness for an accumulator reduced against a modulus. -/
def ofEuclid (a b m : ℤ) : Row :=
  { a := a, b := b, c := (a * b) % m, u := (a * b) / m, m := m }

/-- **Satisfiability, general.**  Every `(a, b, m)` admits a witness. -/
theorem ofEuclid_holdsInt (a b m : ℤ) : (ofEuclid a b m).HoldsInt := by
  have h := Int.emod_add_mul_ediv (a * b) m
  show a * b = (a * b) % m + ((a * b) / m) * m
  linear_combination -h

/-- BabyBear's characteristic, `2^31 - 2^27 + 1 = 2013265921`. -/
def babybear : ℤ := 2 ^ 31 - 2 ^ 27 + 1

/-- **Satisfiability, concrete.**  A 35-bit accumulator — the width a 12-bit quantized dot
product reaches, which is the measured motivation for this whole reading — reduced against
BabyBear.  `2^18 · 2^17 = 2^35` overflows the field by a factor of 17. -/
def accumulatorRow : Row := ofEuclid (2 ^ 18) (2 ^ 17) babybear

theorem accumulatorRow_holdsInt : accumulatorRow.HoldsInt := ofEuclid_holdsInt _ _ _

/-- The concrete witness is not degenerate: the quotient is 17, so the product really does
leave the field, and the remainder is the surviving 27-bit value. -/
theorem accumulatorRow_values :
    accumulatorRow.u = 17 ∧ accumulatorRow.c = 134217711 := by decide

/-! ## Teeth -/

/-- **Tooth 0 — why an integer relation is needed at all.**  A 35-bit accumulator and the
same value minus BabyBear's characteristic are *distinct integers* with the *same* BabyBear
image.  A field-native accumulation cannot tell them apart, so the accumulation obligation
has to be stated over ℤ, which is the premise of the entire Limber/Zaratan line. -/
theorem babybear_accumulator_aliases :
    (2 ^ 35 : ℤ) ≠ 2 ^ 35 - babybear ∧
      (2 ^ 35 : ℤ) ≡ 2 ^ 35 - babybear [ZMOD babybear] := by
  refine ⟨by decide, ?_⟩
  exact Int.modEq_iff_dvd.mpr (by unfold babybear; decide)

/-- A row whose integer relation is FALSE: `202 · 1 ≠ 0 + 1 · 101`.  Its residual is
exactly `101`. -/
def forgedRow : Row := { a := 202, b := 1, c := 0, u := 1, m := 101 }

/-- **Tooth 1 — the statement refutes a false row.** -/
theorem forgedRow_not_holdsInt : ¬ forgedRow.HoldsInt := by decide

theorem forgedRow_residual : forgedRow.residual = 101 := by decide

/-- **Tooth 2 — the mod-`p` check alone is unsound.**  The same false row is *accepted* at
`p = 101`.  So `HoldsMod` is strictly weaker than `HoldsInt`, and the gap is not
hypothetical: it is inhabited by a five-integer counterexample. -/
theorem forgedRow_holdsMod_101 : forgedRow.HoldsMod 101 := by decide

/-- **Tooth 3 — the residual is a fact about the committed quotient, not about the row's
public part.**  The same `(a, b, c, m)` is satisfiable over ℤ with `u = 2`.  A prover that
gets to pick `u` after seeing the challenge therefore faces no obligation at all. -/
theorem forgedRow_repaired_by_other_quotient :
    ({ forgedRow with u := 2 } : Row).HoldsInt := by decide

/-- **Tooth 4 — why `p` must be sampled after the witness is committed.**  Over a prime
field with `m` invertible, the mod-`p` relation is satisfiable for *every* `a, b, c` by
solving for the quotient.  This is Limber §3.1's own argument that moduli-R1CS cannot be
stated over a field: `quos_i = (A_i z · B_i z − C_i z) · mods_i⁻¹`.  Fingerprinting is
sound only because the prover moves first. -/
theorem adaptive_quotient_defeats_fingerprint {F : Type*} [Field F]
    (a b c m : F) (hm : m ≠ 0) : ∃ u : F, a * b = c + u * m :=
  ⟨(a * b - c) / m, by field_simp; ring⟩

/-- The same collapse at the deployed shape: a prime field `ZMod p`, which is what the
verifier's fingerprint actually lands in. -/
theorem adaptive_quotient_defeats_fingerprint_zmod (p : ℕ) [Fact (Nat.Prime p)]
    (a b c m : ZMod p) (hm : m ≠ 0) : ∃ u : ZMod p, a * b = c + u * m :=
  adaptive_quotient_defeats_fingerprint a b c m hm

/-! ### Premise inhabitation for the counting bound -/

/-- A concrete sampling space: three primes, all at least `101`. -/
def exampleSpace : Finset ℕ := {101, 103, 107}

theorem exampleSpace_prime : ∀ p ∈ exampleSpace, Nat.Prime p := by
  intro p hp
  fin_cases hp <;> norm_num

theorem exampleSpace_floor : ∀ p ∈ exampleSpace, 101 ≤ p := by decide

/-- The undetected set is INHABITED, so `pow_card_undetected_le` is not a statement about
an empty family. -/
theorem undetected_nonempty : (undetected exampleSpace forgedRow).Nonempty :=
  ⟨101, by decide⟩

theorem undetected_card_eq_one : (undetected exampleSpace forgedRow).card = 1 := by decide

/-- The counting bound, instantiated at that inhabited witness: `101 ^ 1 ≤ 101`.  Tight,
and therefore not slack-hiding. -/
theorem forgedRow_counting_bound :
    101 ^ (undetected exampleSpace forgedRow).card ≤ forgedRow.residual.natAbs :=
  pow_card_undetected_le forgedRow_not_holdsInt exampleSpace_prime exampleSpace_floor

/-! ## Limber's own field floor, at our parameters

Remark 5.9: with `k = 1` and Soundness Bound 1's requirement `P > 32 λ m`, the Partial
Evaluation Norm Bound `2^k · P^k · max(T, P) ≤ (q − P)/2` forces `q ≥ 2^(k+1) P^(k+1) = 4P²`.
`m` is the number of variables of the *limb-split* polynomial, so `2^m` is its hypercube
length. -/

/-- Limber's minimum PCS field characteristic at `k = 1`, as a function of the small-prime
ceiling `P` (Remark 5.9). -/
def limberMinCharacteristic (P : ℕ) : ℕ := 4 * P ^ 2

/-- **BabyBear is below Limber's own floor once the committed polynomial has six
variables** — that is, once it has 64 hypercube entries.  At λ = 128, Soundness Bound 1
forces `P > 32 · 128 · 6 = 24576`, hence `q ≥ 4 · 24577² = 2416115716 > 2013265921`.

This is the precise sense in which Limber does not run over BabyBear: not "asymptotically
awkward", but excluded by its own parameter inequalities at any useful polynomial size. -/
theorem babybear_excluded_from_six_variables (m P : ℕ) (hm : 6 ≤ m)
    (hP : 32 * 128 * m < P) :
    (2 ^ 31 - 2 ^ 27 + 1 : ℕ) < limberMinCharacteristic P := by
  have h24576 : 24576 < P := lt_of_le_of_lt (by omega) hP
  have hsq : 24577 ^ 2 ≤ P ^ 2 := Nat.pow_le_pow_left h24576 2
  calc (2 ^ 31 - 2 ^ 27 + 1 : ℕ) = 2013265921 := by norm_num
    _ < 4 * 24577 ^ 2 := by norm_num
    _ ≤ 4 * P ^ 2 := Nat.mul_le_mul_left 4 hsq

/-- Goldilocks clears the same floor with room to spare, at the paper's own suggested
`P = 64 λ m` with λ = 128 and m = 25 (Table 3's running shape). -/
theorem goldilocks_clears_limber_min :
    limberMinCharacteristic (64 * 128 * 25) < (2 ^ 64 - 2 ^ 32 + 1 : ℕ) := by
  norm_num [limberMinCharacteristic]

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.IntegerFingerprint.Row.holdsInt_iff_residual_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Row.holdsInt_iff_residual_eq_zero
/-- info: 'Minidregg.Theory.IntegerFingerprint.Row.holdsMod_iff_dvd_residual' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Row.holdsMod_iff_dvd_residual
/-- info: 'Minidregg.Theory.IntegerFingerprint.Row.fingerprint_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Row.fingerprint_complete
/-- info: 'Minidregg.Theory.IntegerFingerprint.mem_undetected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_undetected
/-- info: 'Minidregg.Theory.IntegerFingerprint.pow_card_undetected_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pow_card_undetected_le
/-- info: 'Minidregg.Theory.IntegerFingerprint.card_undetected_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_undetected_le_log
/-- info: 'Minidregg.Theory.IntegerFingerprint.fingerprint_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fingerprint_error_le
/-- info: 'Minidregg.Theory.IntegerFingerprint.fingerprint_error_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fingerprint_error_ratio_le
/-- info: 'Minidregg.Theory.IntegerFingerprint.ofEuclid_holdsInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofEuclid_holdsInt
/-- info: 'Minidregg.Theory.IntegerFingerprint.accumulatorRow_holdsInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accumulatorRow_holdsInt
/-- info: 'Minidregg.Theory.IntegerFingerprint.accumulatorRow_values' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms accumulatorRow_values
/-- info: 'Minidregg.Theory.IntegerFingerprint.babybear_accumulator_aliases' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms babybear_accumulator_aliases
/-- info: 'Minidregg.Theory.IntegerFingerprint.forgedRow_not_holdsInt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms forgedRow_not_holdsInt
/-- info: 'Minidregg.Theory.IntegerFingerprint.forgedRow_residual' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms forgedRow_residual
/-- info: 'Minidregg.Theory.IntegerFingerprint.forgedRow_holdsMod_101' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms forgedRow_holdsMod_101
/-- info: 'Minidregg.Theory.IntegerFingerprint.forgedRow_repaired_by_other_quotient' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms forgedRow_repaired_by_other_quotient
/-- info: 'Minidregg.Theory.IntegerFingerprint.adaptive_quotient_defeats_fingerprint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms adaptive_quotient_defeats_fingerprint
/-- info: 'Minidregg.Theory.IntegerFingerprint.adaptive_quotient_defeats_fingerprint_zmod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms adaptive_quotient_defeats_fingerprint_zmod
/-- info: 'Minidregg.Theory.IntegerFingerprint.exampleSpace_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exampleSpace_prime
/-- info: 'Minidregg.Theory.IntegerFingerprint.exampleSpace_floor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exampleSpace_floor
/-- info: 'Minidregg.Theory.IntegerFingerprint.undetected_nonempty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms undetected_nonempty
/-- info: 'Minidregg.Theory.IntegerFingerprint.undetected_card_eq_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms undetected_card_eq_one
/-- info: 'Minidregg.Theory.IntegerFingerprint.forgedRow_counting_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forgedRow_counting_bound
/-- info: 'Minidregg.Theory.IntegerFingerprint.babybear_excluded_from_six_variables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms babybear_excluded_from_six_variables
/-- info: 'Minidregg.Theory.IntegerFingerprint.goldilocks_clears_limber_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goldilocks_clears_limber_min

end Minidregg.Theory.IntegerFingerprint
