/-
# Compiler.Tower256AlgebraicCert -- Zero-Byte-Leakage Algebraic `Tower256` Zerocheck + `LogUp256` Certificates

Closes the `[OPEN]` boundary of `zkml-research/docs/LEAF-PROVER-DECISION.md` §6.2 (`L273-276`)
and `zkml-research/notes/tower256-private-content-certificates.md` §3:

In `Compiler.Tower256PrivateContentCert`, DFA transitions and endpoints were checked by opening
`2 + stepQueries` positions (`0`, `recordLength - 1`, and Fiat–Shamir sampled indices), yielding
`((L - 1) / L) ^ stepQueries` soundness and disclosing individual bytes at those positions.

This module replaces all sampled position openings with an **algebraic `Tower256` multilinear
zerocheck + characteristic-2-safe `LogUp256` lookup argument + coset Additive-FRI**, achieving
`< 2^{-230}` algebraic soundness + Selvage `IdealAccept` (`UD-100` FRI) with **literally zero
single-byte or trace-row position disclosures**:

1. **Order-`(2^32 - 1)` Multiplicative Counter Subgroup (`GF(2^32)^× ⊂ Tower256^×`):**
   Embeds `Coordinate 5` (`GF(2^32)`) into `C8` (`Coordinate 8` / `Tower256`) via the ring
   homomorphism `embed5To8`, proves `zetaC = leafOfNat 65541` (`0x10005`) has exact multiplicative
   order `2^32 - 1` (`orderOf_zetaF`, `zetaF_pow_injOn`), and encodes exact non-wrapping integer
   accept-visit counts (`cumCount_i ↦ ζ^{cumCount_i}`) across `.accept b`, `.count n`, and
   zero-count-disclosure `(d + 1)`-bit `.bound lo hi` claims without characteristic-2 `1 + 1 = 0`
   cancellation.

2. **Zero-Position-Disclosure Half-Cube Masking & Disjoint Coset Commitment:**
   Blinds every witness table `w : (Fin d → Bool) → Tower256` on `{0, 1}^{d+1}` via
   `halfCubeExtend w u` (`x_d = 0` witness, `x_d = 1` uniform random mask `u`) and commits its
   Boolean-Möbius additive-novel-basis polynomial on the disjoint coset `cosetOffset ell + V_ell`
   (`cosetOffset ell = 2^ell`).
   - `zero_position_disclosure_hiding` & `zero_position_disclosure_uniform_prob`: for every
     `r_d ∉ {0, 1}` (`r_d ≠ 0`), `mle (halfCubeExtend w u) (Fin.snoc r r_d)` has **exact uniform
     probability `1 / 2^256`** over `u` for **every** target `y : Tower256` and **any** two private
     records `w₀, w₁`.
   - `coset_theta_last_not_boolean`: at **every** point of `cosetOffset ell + V_ell`, the masking
     coordinate `θ_d(z)` satisfies `θ_d(z) ≠ 0 ∧ θ_d(z) ≠ 1`.
   - `maskedContentRoot_eq_or_collision`: equal `maskedContentCommit` roots imply equal records
     and masks, or expose an explicit `FramedXofCollision`.

3. **Exact Algebraic DFA + `LogUp256` Lookup Equivalence & Falsifier Teeth:**
   - `algebraicRowValid_iff_dfaRun` & `algebraicStepCheck_iff_dfaRun`: exact algebraic transition,
     multiplicative counter, terminal `ClaimData`, and `θ_row`-weighted `LogUp256` satisfaction iff
     `Dfaops.satisfiesClaim t claim w = true` away from explicit low-degree root escape sets.
   - `gamma_pole_guard`, `forged_transition_nonzero_polynomial`, and
     `char_two_unweighted_parity_trap_tooth` (proving why unweighted `1 + 1 = 0` LogUp fails in
     characteristic 2 while `θ_row`-weighted `LogUp256` succeeds).

4. **Executable Verifier (`checkAlgebraic`) & Soundness (`checkAlgebraic_sound_or_collision`):**
   `checkAlgebraic` runs in polylogarithmic + table-linear field operations (`0` inversions),
   welds into `Tower256SuccinctCheck.check` (`IdealAccept`), and proves every accepted receipt
   either satisfies `AlgebraicPrivateHolds` + `IdealAccept`, hits an explicit challenge-pinned
   polynomial/fold escape event (`< 2^{-230}` algebraic bound), or exposes an input-pinned
   `cSHAKE256` `FramedXofCollision` (`checkAlgebraic_premises_inhabited` proves joint non-vacuity).
-/

import Compiler.Tower256PrivateContentCert
import Compiler.Logup256ReceiptClause
import Mathlib.GroupTheory.OrderOfElement

namespace Minidregg.Compiler.Tower256AlgebraicCert

open Polynomial
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate coordinateFinEquiv capacity
  coordinateFieldEquiv coordinateFieldEquiv_add coordinateFieldEquiv_mul
  coordinateFieldEquiv_zero coordinateFieldEquiv_one)
open Minidregg.Theory.BinaryCubeAddress (binaryAddressBits binaryCubeIndexEquiv)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256CshakeMerkleBinding
open Minidregg.Compiler.Tower256CoordinateMerkle
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8 toField evalCoeffs polyOf)
open Minidregg.Compiler.Tower256ContentCert
open Minidregg.Compiler.Tower256AdditiveFriController (TranscriptPins Tower256)
open Minidregg.Compiler.Tower256AdditiveFriRawController
  (RawTranscript IdealAccept ReceiptCollision)
open Minidregg.Compiler.Tower256AdditiveFriSuccinctController
  (Consistent toRawStatement FinalCollision succinct_accepts_ideal_or_collision)
open Minidregg.Compiler.Tower256AdditiveFriRawDeployment (rawPcs bootstrapPins)
open Minidregg.Compiler.Tower256SuccinctCheck
open Minidregg.Compiler.Tower256SuccinctProver (unitBasis unitBasis_independent)
open Minidregg.Compiler.Tower256PrivateContentCert
open Minidregg.Selvage

set_option autoImplicit false

/-! ## §1. `GF(2^32)^× ⊂ Tower256^×` Multiplicative Counter Subgroup (`zetaC = 0x10005`) -/

/-- Embed `Coordinate k` into the low half of `Coordinate (k + 1)` (`high = 0`). -/
def embedToSucc {k : Nat} (c : Coordinate k) : Coordinate (k + 1) :=
  .pair c (Coordinate.zero k)

theorem Coordinate.mul_zero_right : ∀ (k : Nat) (a : Coordinate k),
    Coordinate.mul k a (Coordinate.zero k) = Coordinate.zero k
  | 0, .bit x => by simp [Coordinate.mul, Coordinate.zero, Coordinate.bitOf]
  | k + 1, .pair al ah => by
      apply (coordinateFieldEquiv (k + 1)).injective
      rw [coordinateFieldEquiv_mul, coordinateFieldEquiv_zero, mul_zero]

theorem Coordinate.mul_zero_left (k : Nat) (a : Coordinate k) :
    Coordinate.mul k (Coordinate.zero k) a = Coordinate.zero k := by
  apply (coordinateFieldEquiv k).injective
  rw [coordinateFieldEquiv_mul, coordinateFieldEquiv_zero, zero_mul]

theorem Coordinate.add_zero_right (k : Nat) (a : Coordinate k) :
    Coordinate.add k a (Coordinate.zero k) = a := by
  apply (coordinateFieldEquiv k).injective
  rw [coordinateFieldEquiv_add, coordinateFieldEquiv_zero, add_zero]

theorem Coordinate.add_self_zero (k : Nat) (a : Coordinate k) :
    Coordinate.add k a a = Coordinate.zero k := by
  apply (coordinateFieldEquiv k).injective
  rw [coordinateFieldEquiv_add, coordinateFieldEquiv_zero, CharTwo.add_self_eq_zero]

@[simp] theorem embedToSucc_zero (k : Nat) :
    embedToSucc (Coordinate.zero k) = Coordinate.zero (k + 1) := rfl

@[simp] theorem embedToSucc_one (k : Nat) :
    embedToSucc (Coordinate.one k) = Coordinate.one (k + 1) := rfl

theorem embedToSucc_add {k : Nat} (a b : Coordinate k) :
    Coordinate.add (k + 1) (embedToSucc a) (embedToSucc b) =
      embedToSucc (Coordinate.add k a b) := by
  simp [embedToSucc, Coordinate.add, Coordinate.add_self_zero]

theorem embedToSucc_mul {k : Nat} (a b : Coordinate k) :
    Coordinate.mul (k + 1) (embedToSucc a) (embedToSucc b) =
      embedToSucc (Coordinate.mul k a b) := by
  simp only [embedToSucc, Coordinate.mul, Coordinate.low_pair, Coordinate.high_pair,
    Coordinate.mul_zero_right, Coordinate.mul_zero_left, Coordinate.add_zero_right,
    Coordinate.add_self_zero]

theorem embedToSucc_injective {k : Nat} : Function.Injective (embedToSucc (k := k)) := by
  intro a b h
  cases h
  rfl

/-- Canonical subfield embedding `GF(2^32) = Coordinate 5 ↪ Coordinate 8 = C8`. -/
def embed5To8 (c : Coordinate 5) : C8 :=
  embedToSucc (embedToSucc (embedToSucc c))

theorem embed5To8_injective : Function.Injective embed5To8 :=
  embedToSucc_injective.comp (embedToSucc_injective.comp embedToSucc_injective)

@[simp] theorem embed5To8_zero : embed5To8 (Coordinate.zero 5) = Coordinate.zero 8 := rfl
@[simp] theorem embed5To8_one : embed5To8 (Coordinate.one 5) = Coordinate.one 8 := rfl

theorem embed5To8_add (a b : Coordinate 5) :
    addC (embed5To8 a) (embed5To8 b) = embed5To8 (Coordinate.add 5 a b) := by
  unfold addC embed5To8
  rw [embedToSucc_add, embedToSucc_add, embedToSucc_add]

theorem embed5To8_mul (a b : Coordinate 5) :
    mulC (embed5To8 a) (embed5To8 b) = embed5To8 (Coordinate.mul 5 a b) := by
  unfold mulC embed5To8
  rw [embedToSucc_mul, embedToSucc_mul, embedToSucc_mul]

/-- Fuel-bounded binary exponentiation on `Coordinate k` (`O(fuel)` multiplications; kernel-reducible for `decide`). -/
def powCoordAux (k : Nat) (base : Coordinate k) : Nat → Nat → Coordinate k
  | 0, _ => Coordinate.one k
  | _ + 1, 0 => Coordinate.one k
  | fuel + 1, e + 1 =>
      let half := powCoordAux k base fuel ((e + 1) / 2)
      let sq := Coordinate.mul k half half
      if (e + 1) % 2 = 1 then Coordinate.mul k sq base else sq

def powCoord (k : Nat) (base : Coordinate k) (e : Nat) : Coordinate k :=
  powCoordAux k base 64 e

theorem toField_powCoordAux (k : Nat) (base : Coordinate k) :
    ∀ (fuel e : Nat), e < 2 ^ fuel →
      coordinateFieldEquiv k (powCoordAux k base fuel e) = (coordinateFieldEquiv k base) ^ e
  | 0, e, he => by
      have he0 : e = 0 := by omega
      subst he0
      simp [powCoordAux]
  | fuel + 1, 0, _ => by
      simp [powCoordAux]
  | fuel + 1, e + 1, he => by
      have hhalf : (e + 1) / 2 < 2 ^ fuel := by
        have h2 : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
        omega
      have ih := toField_powCoordAux k base fuel ((e + 1) / 2) hhalf
      simp only [powCoordAux]
      split
      · rename_i hodd
        rw [coordinateFieldEquiv_mul, coordinateFieldEquiv_mul, ih, ← pow_add, ← two_mul, ← pow_succ]
        congr 1
        omega
      · rename_i heven
        rw [coordinateFieldEquiv_mul, ih, ← pow_add, ← two_mul]
        congr 1
        omega

theorem toField_powCoord (k : Nat) (base : Coordinate k) (e : Nat) (he : e < 2 ^ 64) :
    coordinateFieldEquiv k (powCoord k base e) = (coordinateFieldEquiv k base) ^ e :=
  toField_powCoordAux k base 64 e he

abbrev powC8 (base : C8) (e : Nat) : C8 := powCoord 8 base e

theorem toField_powC8 (base : C8) (e : Nat) (he : e < 2 ^ 64) :
    toField (powC8 base e) = (toField base) ^ e :=
  toField_powCoord 8 base e he

theorem embed5To8_powCoordAux (base : Coordinate 5) :
    ∀ (fuel e : Nat), powCoordAux 8 (embed5To8 base) fuel e = embed5To8 (powCoordAux 5 base fuel e)
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | fuel + 1, e + 1 => by
      simp only [powCoordAux]
      have ih := embed5To8_powCoordAux base fuel ((e + 1) / 2)
      change (if (e + 1) % 2 = 1 then
        mulC (mulC (powCoordAux 8 (embed5To8 base) fuel ((e + 1) / 2))
                   (powCoordAux 8 (embed5To8 base) fuel ((e + 1) / 2)))
          (embed5To8 base)
       else
        mulC (powCoordAux 8 (embed5To8 base) fuel ((e + 1) / 2))
             (powCoordAux 8 (embed5To8 base) fuel ((e + 1) / 2))) = _
      rw [ih]
      split
      · rw [embed5To8_mul, embed5To8_mul]
      · rw [embed5To8_mul]

theorem embed5To8_powCoord (base : Coordinate 5) (e : Nat) :
    powC8 (embed5To8 base) e = embed5To8 (powCoord 5 base e) :=
  embed5To8_powCoordAux base 64 e

/-- Primitive generator `0x10005 = 65541` of `GF(2^32)^×` in Fan–Paar `Coordinate 5`. -/
def zeta5 : Coordinate 5 := Coord.ofNat 5 65541

/-- Embedded generator `zetaC = leafOfNat 65541` of multiplicative order `2^32 - 1` in `C8`. -/
def zetaC : C8 := embed5To8 zeta5

/-- Multiplicative inverse `ζ^(2^32 - 2)` of `zetaC`. -/
def zetaInv5 : Coordinate 5 := powCoord 5 zeta5 (2 ^ 32 - 2)
def zetaInvC : C8 := embed5To8 zetaInv5

noncomputable abbrev zetaF : Tower256 := toField zetaC

/-- Kernel-verified order-`(2^32 - 1)` check and Fermat-prime cofactor disequalities in `Coordinate 5`. -/
theorem zeta5_order_checks :
    powCoord 5 zeta5 (2 ^ 32 - 1) = Coordinate.one 5 ∧
    powCoord 5 zeta5 ((2 ^ 32 - 1) / 3) ≠ Coordinate.one 5 ∧
    powCoord 5 zeta5 ((2 ^ 32 - 1) / 5) ≠ Coordinate.one 5 ∧
    powCoord 5 zeta5 ((2 ^ 32 - 1) / 17) ≠ Coordinate.one 5 ∧
    powCoord 5 zeta5 ((2 ^ 32 - 1) / 257) ≠ Coordinate.one 5 ∧
    powCoord 5 zeta5 ((2 ^ 32 - 1) / 65537) ≠ Coordinate.one 5 ∧
    Coordinate.mul 5 zeta5 zetaInv5 = Coordinate.one 5 := by
  decide

theorem zetaC_eq_leafOfNat : zetaC = leafOfNat 65541 := by
  decide

theorem zetaC_mul_zetaInvC : mulC zetaC zetaInvC = Coordinate.one 8 := by
  rw [zetaC, zetaInvC, embed5To8_mul, zeta5_order_checks.2.2.2.2.2.2, embed5To8_one]

theorem zetaF_mul_zetaInvF : zetaF * toField zetaInvC = 1 := by
  rw [zetaF, ← toField_mulC, zetaC_mul_zetaInvC, coordinateFieldEquiv_one]

private theorem prime_dvd_fermat_prod {p : Nat} (hp : p.Prime)
    (hdvd : p ∣ 2 ^ 32 - 1) :
    p = 3 ∨ p = 5 ∨ p = 17 ∨ p = 257 ∨ p = 65537 := by
  have hfac : (2 ^ 32 - 1 : Nat) = 3 * (5 * (17 * (257 * 65537))) := by norm_num
  rw [hfac] at hdvd
  rcases hp.dvd_mul.mp hdvd with h3 | hdvd
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3)
  · rcases hp.dvd_mul.mp hdvd with h5 | hdvd
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5))
    · rcases hp.dvd_mul.mp hdvd with h17 | hdvd
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h17)))
      · rcases hp.dvd_mul.mp hdvd with h257 | h65537
        · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h257))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h65537))))

/-- **`orderOf zetaF = 2^32 - 1`**: `zetaC` generates an exact cyclic subgroup of size `4,294,967,295`
inside `Tower256^×`, giving wraparound-free integer counting up to `4.29B` in characteristic 2. -/
theorem orderOf_zetaF : orderOf zetaF = 2 ^ 32 - 1 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · rw [zetaF, ← toField_powC8 _ _ (by norm_num), zetaC, embed5To8_powCoord, zeta5_order_checks.1,
      embed5To8_one, coordinateFieldEquiv_one]
  · intro p hp hdvd heq
    have hlt : (2 ^ 32 - 1) / p < 2 ^ 64 :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num)
    have hpow : powCoord 5 zeta5 ((2 ^ 32 - 1) / p) = Coordinate.one 5 := by
      apply embed5To8_injective
      apply toField.injective
      rw [← embed5To8_powCoord, ← zetaC, toField_powC8 _ _ hlt, embed5To8_one, coordinateFieldEquiv_one]
      exact heq
    rcases prime_dvd_fermat_prod hp hdvd with rfl | rfl | rfl | rfl | rfl
    · exact zeta5_order_checks.2.1 hpow
    · exact zeta5_order_checks.2.2.1 hpow
    · exact zeta5_order_checks.2.2.2.1 hpow
    · exact zeta5_order_checks.2.2.2.2.1 hpow
    · exact zeta5_order_checks.2.2.2.2.2.1 hpow

/-- **Injectivity of `k ↦ zetaF ^ k` on `[0, 2^32 - 1)`**: distinct integer counts below `2^32 - 1`
map to distinct elements of `Tower256`. -/
theorem zetaF_pow_injOn {a b : Nat} (ha : a < 2 ^ 32 - 1) (hb : b < 2 ^ 32 - 1) :
    zetaF ^ a = zetaF ^ b ↔ a = b := by
  constructor
  · intro h
    exact pow_injOn_Iio_orderOf (x := zetaF)
      (by rw [Set.mem_Iio, orderOf_zetaF]; exact ha)
      (by rw [Set.mem_Iio, orderOf_zetaF]; exact hb) h
  · rintro rfl; rfl

/-! ## §2. Zero-Position-Disclosure Half-Cube Masking & Coset Novel-Basis Commitment -/

/-- Extend a witness table `w` (`x_d = false`) with a random blinding table `u` (`x_d = true`)
onto the `(d + 1)`-dimensional Boolean hypercube `{0, 1}^{d+1}`. -/
def halfCubeExtend {F : Type*} {d : Nat} (w u : (Fin d → Bool) → F) :
    (Fin (d + 1) → Bool) → F :=
  fun b => if b (Fin.last d) then u (Fin.init b) else w (Fin.init b)

theorem chiEval_snoc {F : Type*} [CommRing F] {d : Nat}
    (b : Fin d → Bool) (bd : Bool) (r : Fin d → F) (rd : F) :
    chiEval (Fin.snoc b bd) (Fin.snoc r rd) =
      chiEval b r * (if bd then rd else 1 - rd) := by
  unfold chiEval
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- **Half-Cube Multilinear Decomposition**: evaluating `mle (halfCubeExtend w u)` at `(r, r_d)`
equals `(1 - r_d) * mle w r + r_d * mle u r`. -/
theorem mle_halfCubeExtend {F : Type*} [CommRing F] {d : Nat}
    (w u : (Fin d → Bool) → F) (r : Fin d → F) (rd : F) :
    mle (halfCubeExtend w u) (Fin.snoc r rd) =
      (1 - rd) * mle w r + rd * mle u r := by
  let snocEquiv : (Fin d → Bool) × Bool ≃ (Fin (d + 1) → Bool) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun b => (Fin.init b, b (Fin.last d))
      left_inv := fun p => by simp
      right_inv := fun b => Fin.snoc_init_self b }
  unfold mle
  rw [← Equiv.sum_comp snocEquiv]
  rw [Fintype.sum_prod_type]
  simp only [snocEquiv, Equiv.coe_fn_mk, Fintype.sum_bool, halfCubeExtend,
    Fin.snoc_last, Fin.init_snoc, chiEval_snoc, Bool.false_eq_true, ↓reduceIte]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_; ring
  · refine Finset.sum_congr rfl fun b _ => ?_; ring

/-- Partition of unity for the Lagrange `chiEval` basis: `∑_b χ_b(r) = 1` at every `r ∈ F^d`. -/
theorem sum_chiEval_eq_one {F : Type*} [Field F] {d : Nat} (r : Fin d → F) :
    (∑ b : Fin d → Bool, chiEval b r) = 1 := by
  have h1 : (∑ b : Fin d → Bool, chiEval b r) = mle (fun _ : Fin d → Bool => (1 : F)) r := by
    simp [mle]
  rw [h1]
  have heq : mle (fun _ : Fin d → Bool => (1 : F)) = fun _ : Fin d → F => (1 : F) := by
    apply multiAffine_ext (mle_multilinear _)
    · intro i x t; ring
    · intro b; rw [mle_agrees]
  exact congrFun heq r

/-- At every point `r : Fin d → F`, at least one hypercube corner `b*` has `chiEval b* r ≠ 0`. -/
theorem exists_chiEval_ne_zero {F : Type*} [Field F] {d : Nat} (r : Fin d → F) :
    ∃ b : Fin d → Bool, chiEval b r ≠ 0 := by
  by_contra h
  push Not at h
  have hsum : (∑ b : Fin d → Bool, chiEval b r) = 0 :=
    Finset.sum_eq_zero fun b _ => h b
  rw [sum_chiEval_eq_one] at hsum
  exact one_ne_zero hsum

theorem mle_update_corner {F : Type*} [CommRing F] {d : Nat}
    (u : (Fin d → Bool) → F) (bStar : Fin d → Bool) (v : F) (r : Fin d → F) :
    mle (Function.update u bStar (u bStar + v)) r = mle u r + v * chiEval bStar r := by
  classical
  unfold mle
  have hsplit : ∀ b : Fin d → Bool,
      Function.update u bStar (u bStar + v) b * chiEval b r =
        u b * chiEval b r + (if b = bStar then v * chiEval bStar r else 0) := by
    intro b
    by_cases hb : b = bStar
    · subst hb; simp [add_mul]
    · simp [hb]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp

noncomputable instance : Fintype Tower256 :=
  Fintype.ofEquiv C8 toField

theorem card_tower256 : Fintype.card Tower256 = 2 ^ 256 := by
  rw [Fintype.card_congr toField.symm, Fintype.card_congr (coordinateFinEquiv 8),
    Fintype.card_fin, capacity_eight]

theorem card_tower256_real : (Fintype.card Tower256 : ℝ) = (2 : ℝ) ^ 256 := by
  rw [card_tower256]
  norm_num

/-- Explicit involutive mask-shift bijection absorbing the difference between **any** two private
witness tables `w₀, w₁` at any off-witness evaluation point `(r, r_d)` (`r_d ≠ 0`). -/
noncomputable def halfCubeMaskShiftEquiv {d : Nat}
    (w₀ w₁ : (Fin d → Bool) → Tower256) (r : Fin d → Tower256) (rd : Tower256)
    (_hrd : rd ≠ 0) :
    ((Fin d → Bool) → Tower256) ≃ ((Fin d → Bool) → Tower256) := by
  classical
  let bStar : Fin d → Bool := Classical.choose (exists_chiEval_ne_zero r)
  let delta : Tower256 := ((1 - rd) * (mle w₀ r - mle w₁ r)) / (rd * chiEval bStar r)
  refine
    { toFun := fun u => Function.update u bStar (u bStar + delta)
      invFun := fun u => Function.update u bStar (u bStar + delta)
      left_inv := fun u => ?_
      right_inv := fun u => ?_ }
  · funext b
    by_cases hb : b = bStar
    · subst hb
      simp [add_assoc, CharTwo.add_self_eq_zero]
    · simp [hb]
  · funext b
    by_cases hb : b = bStar
    · subst hb
      simp [add_assoc, CharTwo.add_self_eq_zero]
    · simp [hb]

theorem mle_halfCubeMaskShiftEquiv {d : Nat}
    (w₀ w₁ : (Fin d → Bool) → Tower256) (r : Fin d → Tower256) (rd : Tower256)
    (hrd : rd ≠ 0) (u : (Fin d → Bool) → Tower256) :
    mle (halfCubeExtend w₁ (halfCubeMaskShiftEquiv w₀ w₁ r rd hrd u)) (Fin.snoc r rd) =
      mle (halfCubeExtend w₀ u) (Fin.snoc r rd) := by
  classical
  let bStar : Fin d → Bool := Classical.choose (exists_chiEval_ne_zero r)
  have hchi : chiEval bStar r ≠ 0 := Classical.choose_spec (exists_chiEval_ne_zero r)
  have hden : rd * chiEval bStar r ≠ 0 := mul_ne_zero hrd hchi
  let delta : Tower256 := ((1 - rd) * (mle w₀ r - mle w₁ r)) / (rd * chiEval bStar r)
  have hshift : halfCubeMaskShiftEquiv w₀ w₁ r rd hrd u =
      Function.update u bStar (u bStar + delta) := rfl
  rw [hshift, mle_halfCubeExtend, mle_halfCubeExtend, mle_update_corner]
  have hmul : rd * (delta * chiEval bStar r) = (1 - rd) * (mle w₀ r - mle w₁ r) := by
    calc
      rd * (delta * chiEval bStar r) = delta * (rd * chiEval bStar r) := by ring
      _ = (1 - rd) * (mle w₀ r - mle w₁ r) := div_mul_cancel₀ _ hden
  linear_combination hmul

/-- **`zero_position_disclosure_hiding` (Witness Indistinguishability)**:
for any `r_d ∉ {0, 1}` (indeed any `r_d ≠ 0`), the half-cube masked evaluation
`mle (halfCubeExtend w u) (Fin.snoc r r_d)` has **identical distribution** over uniform random
mask `u : (Fin d → Bool) → Tower256` for **every** pair of private records `w₀, w₁` and target `y`. -/
theorem zero_position_disclosure_hiding {d : Nat}
    (w₀ w₁ : (Fin d → Bool) → Tower256)
    (r : Fin d → Tower256) (rd : Tower256) (hrd : rd ≠ 0 ∧ rd ≠ 1)
    (y : Tower256) :
    BindingGame.prob (fun u : (Fin d → Bool) → Tower256 =>
      mle (halfCubeExtend w₀ u) (Fin.snoc r rd) = y) =
    BindingGame.prob (fun u : (Fin d → Bool) → Tower256 =>
      mle (halfCubeExtend w₁ u) (Fin.snoc r rd) = y) := by
  refine prob_eq_of_equiv (halfCubeMaskShiftEquiv w₀ w₁ r rd hrd.1) _ _ fun u => ?_
  rw [mle_halfCubeMaskShiftEquiv]

/-- **`zero_position_disclosure_uniform_prob` (Exact Uniformity over `Tower256`)**:
for any witness `w`, any `(r, r_d)` with `r_d ≠ 0`, and **every** target `y : Tower256`,
`BindingGame.prob (fun u => mle (halfCubeExtend w u) (Fin.snoc r r_d) = y) = 1 / 2^256`. -/
theorem zero_position_disclosure_uniform_prob {d : Nat}
    (w : (Fin d → Bool) → Tower256)
    (r : Fin d → Tower256) (rd : Tower256) (hrd : rd ≠ 0)
    (y : Tower256) :
    BindingGame.prob (fun u : (Fin d → Bool) → Tower256 =>
      mle (halfCubeExtend w u) (Fin.snoc r rd) = y) = 1 / (2 ^ 256 : ℝ) := by
  classical
  -- First show probability is independent of `y` via target shift on `bStar`.
  have hconst : ∀ y₁ y₂ : Tower256,
      BindingGame.prob (fun u : (Fin d → Bool) → Tower256 =>
        mle (halfCubeExtend w u) (Fin.snoc r rd) = y₁) =
      BindingGame.prob (fun u : (Fin d → Bool) → Tower256 =>
        mle (halfCubeExtend w u) (Fin.snoc r rd) = y₂) := by
    intro y₁ y₂
    let bStar : Fin d → Bool := Classical.choose (exists_chiEval_ne_zero r)
    have hchi : chiEval bStar r ≠ 0 := Classical.choose_spec (exists_chiEval_ne_zero r)
    have hden : rd * chiEval bStar r ≠ 0 := mul_ne_zero hrd hchi
    let dy : Tower256 := (y₂ - y₁) / (rd * chiEval bStar r)
    let eY : ((Fin d → Bool) → Tower256) ≃ ((Fin d → Bool) → Tower256) :=
      { toFun := fun u => Function.update u bStar (u bStar + dy)
        invFun := fun u => Function.update u bStar (u bStar + dy)
        left_inv := fun u => by
          funext b
          by_cases hb : b = bStar
          · subst hb; simp [add_assoc, CharTwo.add_self_eq_zero]
          · simp [Function.update_of_ne hb]
        right_inv := fun u => by
          funext b
          by_cases hb : b = bStar
          · subst hb; simp [add_assoc, CharTwo.add_self_eq_zero]
          · simp [Function.update_of_ne hb] }
    refine prob_eq_of_equiv eY _ _ fun u => ?_
    show mle (halfCubeExtend w u) (Fin.snoc r rd) = y₁ ↔
      mle (halfCubeExtend w (Function.update u bStar (u bStar + dy))) (Fin.snoc r rd) = y₂
    rw [mle_halfCubeExtend, mle_halfCubeExtend, mle_update_corner]
    have hmul : rd * (dy * chiEval bStar r) = y₂ - y₁ := by
      calc
        rd * (dy * chiEval bStar r) = dy * (rd * chiEval bStar r) := by ring
        _ = y₂ - y₁ := div_mul_cancel₀ _ hden
    constructor
    · intro heq; linear_combination heq + hmul
    · intro heq; linear_combination heq - hmul
  -- Sum over all `y : Tower256` equals `1`, and there are `2^256` equal terms.
  have hsum_one :
      (∑ z : Tower256,
        BindingGame.prob (fun u : (Fin d → Bool) → Tower256 =>
          mle (halfCubeExtend w u) (Fin.snoc r rd) = z)) = 1 := by
    simp_rw [BindingGame.prob_eq_mean]
    unfold BindingGame.mean
    rw [← Finset.sum_div, Finset.sum_comm]
    have hinner : ∀ u : (Fin d → Bool) → Tower256,
        (∑ z : Tower256, if mle (halfCubeExtend w u) (Fin.snoc r rd) = z then (1 : ℝ) else 0) = 1 :=
      fun u => by simp
    simp_rw [hinner]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, div_self]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hall_eq :
      (∑ z : Tower256,
        BindingGame.prob (fun u : (Fin d → Bool) → Tower256 =>
          mle (halfCubeExtend w u) (Fin.snoc r rd) = z)) =
      (2 ^ 256 : ℝ) *
        BindingGame.prob (fun u : (Fin d → Bool) → Tower256 =>
          mle (halfCubeExtend w u) (Fin.snoc r rd) = y) := by
    have hcongr :
        (∑ z : Tower256,
          BindingGame.prob (fun u : (Fin d → Bool) → Tower256 =>
            mle (halfCubeExtend w u) (Fin.snoc r rd) = z)) =
        ∑ _z : Tower256,
          BindingGame.prob (fun u : (Fin d → Bool) → Tower256 =>
            mle (halfCubeExtend w u) (Fin.snoc r rd) = y) :=
      Finset.sum_congr rfl fun z _ => hconst z y
    rw [hcongr, Finset.sum_const, Finset.card_univ, card_tower256, nsmul_eq_mul]
    norm_num
  linarith

/-! ### Disjoint Coset Offset & Non-Boolean Masking Coordinate Theorem -/

/-- Canonical disjoint coset offset `2^ell` (`unitBasis (ell + 1)` at `ell`). -/
def cosetOffset (ell : Nat) : C8 :=
  Coord.ofNat 8 (2 ^ ell)

/-- **Every point on `cosetOffset ell + V_ell` has non-Boolean masking coordinate `θ_r ≠ 0 ∧ θ_r ≠ 1`:**
for any round `r < ell` with `ell < 256`, the `r`-folded domain value `domC (unitBasis ell) (cosetOffset ell) r c`
never equals `0` and never equals `pivotC (unitBasis ell) r`, so `θ_r = dom / pivot_r ∉ {0, 1}`
across the **entire** coset `Ω_0`! -/
theorem coset_theta_last_not_boolean {ell : Nat} (hell : ell + 1 ≤ 256)
    (r : Nat) (hr : r < ell) (c : AdditiveFriLevels ell r) :
    toField (pivotC (unitBasis ell) r) ≠ 0 ∧
    toField (domC (unitBasis ell) (cosetOffset ell) r c) ≠ 0 ∧
    toField (domC (unitBasis ell) (cosetOffset ell) r c) ≠ toField (pivotC (unitBasis ell) r) := by
  let extBeta := unitBasis (ell + 1)
  have hextInd : LinearIndependent (ZMod 2) (fun j : Fin (ell + 1) => betaF extBeta j) :=
    unitBasis_independent (ell + 1) hell
  have hsubInd : LinearIndependent (ZMod 2) (fun j : Fin ell => betaF (unitBasis ell) j) :=
    unitBasis_independent ell (by omega)
  have hpivNe : toField (pivotC (unitBasis ell) r) ≠ 0 := by
    rw [toField_pivotC]
    exact additiveTowerPivot_ne_zero ell (betaF (unitBasis ell)) (toField (cosetOffset ell))
      hsubInd r (ell - r - 1) (by omega)
  -- Shared `(ell + 1)`-basis `B' = cons (cosetOffset ell) (unitBasis ell)`
  let B' : Fin (ell + 1) → Tower256 :=
    Fin.cons (toField (cosetOffset ell)) (fun j : Fin ell => toField (unitBasis ell j))
  let perm : Fin (ell + 1) ≃ Fin (ell + 1) :=
    { toFun := Fin.cases ⟨ell, Nat.lt_succ_self ell⟩ (fun i : Fin ell => ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      invFun := fun k => if hk : k.val < ell then (⟨k.val, hk⟩ : Fin ell).succ else 0
      left_inv := fun j => by
        cases j using Fin.cases with
        | zero => simp
        | succ i => simp [i.isLt]
      right_inv := fun k => by
        by_cases hk : k.val < ell
        · simp [hk]
        · have hkv : k.val = ell := by have := k.isLt; omega
          have hkeq : k = ⟨ell, Nat.lt_succ_self ell⟩ := Fin.ext hkv
          rw [hkeq]
          simp }
  have hB'eq : B' = (fun j : Fin (ell + 1) => betaF extBeta (perm j).val) := by
    funext j
    cases j using Fin.cases with
    | zero =>
        have hlt : ell < ell + 1 := Nat.lt_succ_self ell
        simp only [B', Fin.cons_zero, perm, Equiv.coe_fn_mk, Fin.cases_zero,
          betaF, hlt, ↓reduceDIte, extBeta, unitBasis, cosetOffset]
    | succ i =>
        have hlt : i.val < ell + 1 := Nat.lt_succ_of_lt i.isLt
        simp only [B', Fin.cons_succ, perm, Equiv.coe_fn_mk, Fin.cases_succ,
          betaF, hlt, ↓reduceDIte, extBeta, unitBasis]
  have hB'ind : LinearIndependent (ZMod 2) B' := by
    rw [hB'eq]
    exact hextInd.comp perm perm.injective
  let B'pad : Nat → Tower256 := fun n => if hn : n < ell + 1 then B' ⟨n, hn⟩ else 0
  have hB'padInd : LinearIndependent (ZMod 2) (fun j : Fin (ell + 1) => B'pad j.val) := by
    have hfun : (fun j : Fin (ell + 1) => B'pad j.val) = B' := by
      funext j; simp [B'pad, j.isLt]
    rw [hfun]
    exact hB'ind
  have hB'rev : ∀ t < ell, additiveReverseBasis (ell + 1) B'pad t =
      additiveReverseBasis ell (betaF (unitBasis ell)) t := by
    intro t ht
    unfold additiveReverseBasis
    have h1 : ell + 1 - 1 - t < ell + 1 := by omega
    have h0 : ell - 1 - t < ell := by omega
    have h2 : ell + 1 - 1 - t = (ell - 1 - t) + 1 := by omega
    simp only [B'pad, h1, ↓reduceDIte]
    have hfin : (⟨ell + 1 - 1 - t, h1⟩ : Fin (ell + 1)) = (⟨ell - 1 - t, h0⟩ : Fin ell).succ :=
      Fin.ext h2
    rw [hfin]
    simp only [B', Fin.cons_succ, betaF, h0, ↓reduceDIte]
  have hMapEq : ∀ (t : Nat), t ≤ ell → ∀ x : Tower256,
      additiveTowerMap (ell + 1) B'pad t x =
        additiveTowerMap ell (betaF (unitBasis ell)) t x := by
    intro t ht
    induction t with
    | zero => intro x; rfl
    | succ s ih =>
        intro x
        rw [additiveTowerMap_succ, additiveTowerMap_succ]
        unfold additiveTowerPivot
        rw [ih (by omega), ih (by omega), hB'rev s (by omega)]
  have hMapZero : ∀ (t : Nat), additiveTowerMap (ell + 1) B'pad t 0 = 0 := by
    intro t
    induction t with
    | zero => simp [additiveTowerMap]
    | succ s ih =>
        rw [additiveTowerMap_succ, ih]
        simp [foldMap]
  let c' : AdditiveFriLevels (ell + 1) r := fun idx =>
    if idx.val = 0 then 1
    else c ⟨idx.val - 1, by have := idx.isLt; omega⟩
  have hRawEq : additiveTowerRawPoint B'pad 0 (ell + 1 - r) c' =
      additiveTowerRawPoint (betaF (unitBasis ell)) (toField (cosetOffset ell)) (ell - r) c := by
    have hlen : ell + 1 - r = (ell - r) + 1 := by omega
    unfold additiveTowerRawPoint domainPoint
    let eCast : Fin ((ell - r) + 1) ≃ Fin (ell + 1 - r) := finCongr hlen.symm
    rw [← Equiv.sum_comp eCast, Fin.sum_univ_succ, zero_add]
    have hhead : (c' (eCast 0)) • B'pad (eCast 0).val = toField (cosetOffset ell) := by
      have hv0 : (eCast 0).val = 0 := rfl
      have h0lt : 0 < ell + 1 := Nat.zero_lt_succ ell
      simp only [c', hv0, ↓reduceIte, one_smul, B'pad, h0lt, ↓reduceDIte]
      rfl
    rw [hhead]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hvi : (eCast i.succ).val = i.val + 1 := rfl
    have hlt1 : i.val + 1 < ell + 1 := by have := i.isLt; omega
    have hlt0 : i.val < ell := by have := i.isLt; omega
    have hc' : c' (eCast i.succ) = c i := by simp [c', hvi]
    rw [hc']
    simp only [B'pad, hvi, hlt1, ↓reduceDIte]
    have hBsucc : B' ⟨i.val + 1, hlt1⟩ = betaF (unitBasis ell) i.val := by
      rw [show (⟨i.val + 1, hlt1⟩ : Fin (ell + 1)) = (⟨i.val, hlt0⟩ : Fin ell).succ from rfl]
      simp only [B', Fin.cons_succ, betaF, hlt0, ↓reduceDIte]
    rw [hBsucc]
  have hdomEq : toField (domC (unitBasis ell) (cosetOffset ell) r c) =
      additiveTowerMap ell (betaF (unitBasis ell)) r
        (additiveTowerRawPoint (betaF (unitBasis ell)) (toField (cosetOffset ell)) (ell - r) c) := by
    unfold domC
    rw [toField_applyPivots, toField_rawC]
  refine ⟨hpivNe, ?_, ?_⟩
  · intro hdom0
    have hPt0 : additiveTowerPoint (ell + 1) B'pad 0 r (ell + 1 - r) c' = 0 := by
      unfold additiveTowerPoint
      rw [hRawEq, hMapEq r (by omega), ← hdomEq]
      exact hdom0
    let cZero : AdditiveFriLevels (ell + 1) r := fun _ => 0
    have hPtZero : additiveTowerPoint (ell + 1) B'pad 0 r (ell + 1 - r) cZero = 0 := by
      unfold additiveTowerPoint additiveTowerRawPoint domainPoint
      simp only [cZero, zero_smul, Finset.sum_const_zero, add_zero]
      exact hMapZero r
    have hinj := additiveTowerPoint_injective (ell + 1) B'pad 0 hB'padInd r (by omega)
      (show r + (ell + 1 - r) = ell + 1 by omega) (hPt0.trans hPtZero.symm)
    have hbit0 := congrFun hinj ⟨0, by omega⟩
    simp [c', cZero] at hbit0
  · intro hdomPiv
    let cPiv : AdditiveFriLevels (ell + 1) r := fun idx =>
      if idx.val = ell - r then 1 else 0
    have hRawPiv : additiveTowerRawPoint B'pad 0 (ell + 1 - r) cPiv =
        additiveReverseBasis ell (betaF (unitBasis ell)) r := by
      unfold additiveTowerRawPoint domainPoint additiveReverseBasis
      rw [zero_add]
      let idxP : Fin (ell + 1 - r) := ⟨ell - r, by omega⟩
      rw [Fintype.sum_eq_single idxP]
      · have hlt1 : ell - r < ell + 1 := by omega
        have hlt0 : ell - 1 - r < ell := by omega
        simp only [cPiv, idxP, ↓reduceIte, one_smul, B'pad, hlt1, ↓reduceDIte, hlt0]
        have hfin : (⟨ell - r, hlt1⟩ : Fin (ell + 1)) = (⟨ell - 1 - r, hlt0⟩ : Fin ell).succ :=
          Fin.ext (by omega)
        rw [hfin]
        simp only [B', Fin.cons_succ, betaF, hlt0, ↓reduceDIte]
      · intro j hj
        have hjv : j.val ≠ ell - r := fun e => hj (Fin.ext e)
        simp [cPiv, hjv]
    have hEqPts :
        additiveTowerPoint (ell + 1) B'pad 0 r (ell + 1 - r) c' =
        additiveTowerPoint (ell + 1) B'pad 0 r (ell + 1 - r) cPiv := by
      unfold additiveTowerPoint
      rw [hRawEq, hRawPiv, hMapEq r (by omega), hMapEq r (by omega), ← hdomEq]
      have h2 : toField (pivotC (unitBasis ell) r) =
          additiveTowerMap ell (betaF (unitBasis ell)) r
            (additiveReverseBasis ell (betaF (unitBasis ell)) r) := by
        rw [toField_pivotC]
        rfl
      rw [← h2]
      exact hdomPiv
    have hinj := additiveTowerPoint_injective (ell + 1) B'pad 0 hB'padInd r (by omega)
      (show r + (ell + 1 - r) = ell + 1 by omega) hEqPts
    have hbit0 := congrFun hinj ⟨0, by omega⟩
    have hne0 : (0 : Nat) ≠ ell - r := by omega
    simp [c', cPiv, hne0] at hbit0

/-! ### Reversible Additive Coset Expansion & Masked Content Commitment Binding -/

/-- One reversible coset-expansion step from `(ell - s - 1)`-subspace pairs to `(ell - s)`-subspace word:
`lo = ev + θ * od`, `hi = lo + od`, where `θ * pivot_s = dom_s`. -/
def expandStepC (ell s : Nat) (pivInv : C8) (ev od : AdditiveFriLevels ell (s + 1) → C8) :
    AdditiveFriLevels ell s → C8 :=
  fun coord =>
    let tail : AdditiveFriLevels ell (s + 1) := fun i => coord ⟨i.val, by have := i.isLt; omega⟩
    let loDom := domC (unitBasis ell) (cosetOffset ell) s
      (fun i => if h : i.val < ell - (s + 1) then tail ⟨i.val, h⟩ else 0)
    let theta := mulC loDom pivInv
    let loVal := addC (ev tail) (mulC theta (od tail))
    if h : s < ell then
      if coord ⟨ell - (s + 1), by omega⟩ = 0 then loVal else addC loVal (od tail)
    else loVal

/-- Exact one-step fold inverse over coordinates (`r_s = 0` recovers `ev`, `r_s = 1` recovers `ev + od`!). -/
def foldAtBitC (ell s : Nat) (_hs : s < ell) (bit : Bool) (w : AdditiveFriLevels ell s → C8) :
    AdditiveFriLevels ell (s + 1) → C8 :=
  fun k =>
    let lo : AdditiveFriLevels ell s := fun i =>
      if h : i.val < ell - (s + 1) then k ⟨i.val, h⟩ else 0
    let hi : AdditiveFriLevels ell s := fun i =>
      if h : i.val < ell - (s + 1) then k ⟨i.val, h⟩ else 1
    let piv := pivotC (unitBasis ell) s
    let pivInv := Minidregg.Compiler.Tower256SuccinctHonestRun.invC piv
    let dLo := domC (unitBasis ell) (cosetOffset ell) s lo
    let alpha := if bit then piv else Coordinate.zero 8
    addC (w lo) (mulC (mulC (addC dLo alpha) (addC (w lo) (w hi))) pivInv)

/-- Recursive coset novel-basis encoding of a `v`-variable Boolean-Möbius table on `Ω_0` (`v ≤ ell`). -/
def cosetEncodeTableC (ell : Nat) :
    (v : Nat) → (s : Nat) → ((Fin v → Bool) → C8) → AdditiveFriLevels ell s → C8
  | 0, _, f => fun _ => f (fun i => i.elim0)
  | v + 1, s, f =>
      let f0 : (Fin v → Bool) → C8 := fun b => f (Fin.cons false b)
      let f1 : (Fin v → Bool) → C8 := fun b => addC (f (Fin.cons false b)) (f (Fin.cons true b))
      let ev := cosetEncodeTableC ell v (s + 1) f0
      let od := cosetEncodeTableC ell v (s + 1) f1
      let pivInv := Minidregg.Compiler.Tower256SuccinctHonestRun.invC (pivotC (unitBasis ell) s)
      expandStepC ell s pivInv ev od

/-- Recursive `v`-round coset evaluation-fold decoder at any Boolean corner `b : Fin v → Bool`. -/
def cosetDecodeCornerC (ell : Nat) :
    (v : Nat) → (s : Nat) → (hs : s + v ≤ ell) →
    (AdditiveFriLevels ell s → C8) → (Fin v → Bool) → C8
  | 0, _, _, w, _ => w (fun _ => 0)
  | v + 1, s, hs, w, b =>
      let wNext := foldAtBitC ell s (by omega) (b 0) w
      cosetDecodeCornerC ell v (s + 1) (by omega) wNext (Fin.tail b)

/-- `invC` inverts every non-zero coordinate `p : C8` (`toField p ≠ 0`). -/
theorem toField_invC (p : C8) (hp : toField p ≠ 0) :
    toField (Minidregg.Compiler.Tower256SuccinctHonestRun.invC p) = (toField p)⁻¹ := by
  -- `invC p` computes `p ^ (2^256 - 2)` via `foldl` over `List.range 255`:
  -- step `k` maps `(p^(2^k), p^(2^1 + ... + 2^k))` to `(p^(2^(k+1)), p^(2^1 + ... + 2^(k+1)))`.
  unfold Minidregg.Compiler.Tower256SuccinctHonestRun.invC
  have hloop : ∀ (n : Nat) (x acc : C8),
      let res := ((List.range n).foldl (fun (st : C8 × C8) _ =>
        let sq := mulC st.1 st.1
        (sq, mulC st.2 sq)) (x, acc))
      toField res.1 = (toField x) ^ (2 ^ n) ∧
      toField res.2 = toField acc * (toField x) ^ (2 ^ (n + 1) - 2) := by
    intro n
    induction n with
    | zero =>
        intro x acc
        simp
    | succ k ih =>
        intro x acc
        simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        obtain ⟨h1, h2⟩ := ih x acc
        dsimp only at h1 h2 ⊢
        refine ⟨?_, ?_⟩
        · rw [toField_mulC, h1, ← pow_add, show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by ring]
        · rw [toField_mulC, h2, toField_mulC, h1, mul_assoc, ← pow_add, ← pow_add]
          congr 2
          have hge : 2 ≤ 2 ^ (k + 1) := by
            calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
  obtain ⟨_, h2⟩ := hloop 255 p (Coordinate.one 8)
  dsimp only at h2
  rw [h2, coordinateFieldEquiv_one, one_mul]
  -- By Lagrange's theorem on `Tower256ˣ` (`card Tower256ˣ = 2^256 - 1`), `(toField p)^(2^256 - 1) = 1`.
  let u : Tower256ˣ := Units.mk0 (toField p) hp
  have hcardU : Fintype.card Tower256ˣ = 2 ^ 256 - 1 := by
    rw [Fintype.card_units, card_tower256]
  have huPow : u ^ (2 ^ 256 - 1) = 1 := by
    rw [← hcardU]
    exact pow_card_eq_one
  have hpPow : (toField p) ^ (2 ^ 256 - 1) = 1 := by
    simpa [u] using congrArg Units.val huPow
  apply mul_left_cancel₀ hp
  rw [mul_inv_cancel₀ hp, ← pow_succ', show (2 ^ (255 + 1) - 2) + 1 = 2 ^ 256 - 1 by norm_num]
  exact hpPow

theorem foldAtBitC_expandStepC (ell s : Nat) (hell : ell ≤ 256) (hs : s < ell)
    (ev od : AdditiveFriLevels ell (s + 1) → C8) (bit : Bool) :
    foldAtBitC ell s hs bit
        (expandStepC ell s (Minidregg.Compiler.Tower256SuccinctHonestRun.invC (pivotC (unitBasis ell) s)) ev od) =
      fun k => if bit then addC (ev k) (od k) else ev k := by
  have hpivNe : toField (pivotC (unitBasis ell) s) ≠ 0 := by
    rw [toField_pivotC]
    exact additiveTowerPivot_ne_zero ell (betaF (unitBasis ell)) (toField (cosetOffset ell))
      (unitBasis_independent ell hell) s (ell - s - 1) (by omega)
  funext k
  apply toField.injective
  unfold foldAtBitC expandStepC
  let lo : AdditiveFriLevels ell s := fun i =>
    if h : i.val < ell - (s + 1) then k ⟨i.val, h⟩ else 0
  let hi : AdditiveFriLevels ell s := fun i =>
    if h : i.val < ell - (s + 1) then k ⟨i.val, h⟩ else 1
  have htailLo : (fun i : Fin (ell - (s + 1)) => lo ⟨i.val, by have := i.isLt; omega⟩) = k := by
    funext i; simp [lo, i.isLt]
  have htailHi : (fun i : Fin (ell - (s + 1)) => hi ⟨i.val, by have := i.isLt; omega⟩) = k := by
    funext i; simp [hi, i.isLt]
  have hloBit : lo ⟨ell - (s + 1), by omega⟩ = 0 := by simp [lo]
  have hhiBit : hi ⟨ell - (s + 1), by omega⟩ = 1 := by simp [hi]
  have hhiNe0 : hi ⟨ell - (s + 1), by omega⟩ ≠ 0 := by rw [hhiBit]; decide
  have hdLoEq : (fun i : Fin (ell - s) =>
      if h : i.val < ell - (s + 1) then k ⟨i.val, h⟩ else 0) = lo := rfl
  set piv := pivotC (unitBasis ell) s
  set pivInv := Minidregg.Compiler.Tower256SuccinctHonestRun.invC piv
  set dLo := domC (unitBasis ell) (cosetOffset ell) s lo
  have hpivMul : toField piv * toField pivInv = 1 := by
    rw [toField_invC piv hpivNe, mul_inv_cancel₀ hpivNe]
  have hExpLo : expandStepC ell s pivInv ev od lo =
      addC (ev k) (mulC (mulC dLo pivInv) (od k)) := by
    unfold expandStepC
    dsimp only
    simp only [hs, ↓reduceDIte, htailLo, hdLoEq, hloBit, ↓reduceIte]
  have hExpHi : expandStepC ell s pivInv ev od hi =
      addC (addC (ev k) (mulC (mulC dLo pivInv) (od k))) (od k) := by
    unfold expandStepC
    dsimp only
    simp only [hs, ↓reduceDIte, htailHi, hdLoEq, hhiNe0, ↓reduceIte]
  change toField (addC (expandStepC ell s pivInv ev od lo)
    (mulC (mulC (addC dLo (if bit then piv else Coordinate.zero 8))
      (addC (expandStepC ell s pivInv ev od lo) (expandStepC ell s pivInv ev od hi))) pivInv)) =
    toField (if bit then addC (ev k) (od k) else ev k)
  rw [hExpLo, hExpHi]
  cases bit
  · simp only [Bool.false_eq_true, ↓reduceIte, toField_addC, toField_mulC, toField_zeroC, add_zero]
    have hdiff : (toField (ev k) + toField dLo * toField pivInv * toField (od k)) +
        (toField (ev k) + toField dLo * toField pivInv * toField (od k) + toField (od k)) =
        toField (od k) := by
      have hchar : ∀ a b : Tower256, a + (a + b) = (a + a) + b := fun _ _ => by ring
      rw [hchar, CharTwo.add_self_eq_zero, zero_add]
    rw [hdiff]
    have h1 : toField dLo * toField (od k) * toField pivInv =
        toField dLo * toField pivInv * toField (od k) := by ring
    rw [h1]
    have hchar2 : ∀ a b : Tower256, (a + b) + b = a + (b + b) := fun _ _ => by ring
    rw [hchar2, CharTwo.add_self_eq_zero, add_zero]
  · simp only [↓reduceIte, toField_addC, toField_mulC]
    have hdiff : (toField (ev k) + toField dLo * toField pivInv * toField (od k)) +
        (toField (ev k) + toField dLo * toField pivInv * toField (od k) + toField (od k)) =
        toField (od k) := by
      have hchar : ∀ a b : Tower256, a + (a + b) = (a + a) + b := fun _ _ => by ring
      rw [hchar, CharTwo.add_self_eq_zero, zero_add]
    rw [hdiff]
    calc
      toField (ev k) + toField dLo * toField pivInv * toField (od k) +
          (toField dLo + toField piv) * toField (od k) * toField pivInv
        = toField (ev k) +
            (toField dLo * toField pivInv * toField (od k) +
             toField dLo * toField pivInv * toField (od k)) +
            (toField piv * toField pivInv) * toField (od k) := by ring
      _ = toField (ev k) + toField (od k) := by
          rw [CharTwo.add_self_eq_zero, add_zero, hpivMul, one_mul]

/-- **Exact Left-Inverse Theorem (`cosetDecodeCornerC_cosetEncodeTableC`)**:
folding `cosetEncodeTableC ell v s f` across `v` rounds at any Boolean corner `b` recovers `f b`! -/
theorem cosetDecodeCornerC_cosetEncodeTableC (ell : Nat) (hell : ell ≤ 256) :
    ∀ (v s : Nat) (hs : s + v ≤ ell) (f : (Fin v → Bool) → C8) (b : Fin v → Bool),
      cosetDecodeCornerC ell v s hs (cosetEncodeTableC ell v s f) b = f b
  | 0, s, _, f, b => by
      simp only [cosetDecodeCornerC, cosetEncodeTableC]
      congr 1
      funext i
      exact i.elim0
  | v + 1, s, hs, f, b => by
      simp only [cosetDecodeCornerC, cosetEncodeTableC]
      rw [foldAtBitC_expandStepC ell s hell (by omega)]
      cases hb0 : b 0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [cosetDecodeCornerC_cosetEncodeTableC ell hell v (s + 1) (by omega)]
        have hcons : Fin.cons false (Fin.tail b) = b := by
          rw [← hb0]; exact Fin.cons_self_tail b
        rw [hcons]
      · simp only [↓reduceIte]
        have hrec : (fun k => addC
            (cosetEncodeTableC ell v (s + 1) (fun t => f (Fin.cons false t)) k)
            (cosetEncodeTableC ell v (s + 1)
              (fun t => addC (f (Fin.cons false t)) (f (Fin.cons true t))) k)) =
            cosetEncodeTableC ell v (s + 1) (fun t => f (Fin.cons true t)) := by
          -- Linearity of `cosetEncodeTableC` + `a + (a + c) = c` in char 2!
          have hlin : ∀ (v' s' : Nat) (g₁ g₂ : (Fin v' → Bool) → C8),
              (fun k => addC (cosetEncodeTableC ell v' s' g₁ k) (cosetEncodeTableC ell v' s' g₂ k)) =
                cosetEncodeTableC ell v' s' (fun t => addC (g₁ t) (g₂ t)) := by
            intro v'
            induction v' with
            | zero => intro s' g₁ g₂; rfl
            | succ u ih =>
                intro s' g₁ g₂
                funext coord
                simp only [cosetEncodeTableC]
                have ih0 := ih (s' + 1) (fun t => g₁ (Fin.cons false t))
                  (fun t => g₂ (Fin.cons false t))
                have ih1 := ih (s' + 1)
                  (fun t => addC (g₁ (Fin.cons false t)) (g₁ (Fin.cons true t)))
                  (fun t => addC (g₂ (Fin.cons false t)) (g₂ (Fin.cons true t)))
                have hmid : (fun t => addC (addC (g₁ (Fin.cons false t)) (g₁ (Fin.cons true t)))
                    (addC (g₂ (Fin.cons false t)) (g₂ (Fin.cons true t)))) =
                    (fun t => addC (addC (g₁ (Fin.cons false t)) (g₂ (Fin.cons false t)))
                      (addC (g₁ (Fin.cons true t)) (g₂ (Fin.cons true t)))) := by
                  funext t; apply toField.injective; simp; ring
                rw [← hmid, ← ih0, ← ih1]
                apply toField.injective
                unfold expandStepC
                dsimp only
                split
                · split
                  · simp only [toField_addC, toField_mulC]; ring
                  · simp only [toField_addC, toField_mulC]; ring
                · simp only [toField_addC, toField_mulC]; ring
          rw [hlin]
          congr 1
          funext t
          apply toField.injective
          simp only [toField_addC]
          have hc : ∀ x y : Tower256, x + (x + y) = (x + x) + y := fun _ _ => by ring
          rw [hc, CharTwo.add_self_eq_zero, zero_add]
        rw [hrec, cosetDecodeCornerC_cosetEncodeTableC ell hell v (s + 1) (by omega)]
        have hcons : Fin.cons true (Fin.tail b) = b := by
          rw [← hb0]; exact Fin.cons_self_tail b
        rw [hcons]

/-- Half-cube byte table on `{0, 1}^{d+1}`: `leafOfNat w[i]` on `x_d = false`, `mask[i]` on `x_d = true`. -/
def halfCubeByteTable (d : Nat) (w : List UInt8) (mask : List C8) : (Fin (d + 1) → Bool) → C8 :=
  halfCubeExtend
    (fun b =>
      let idx := (binaryCubeIndexEquiv d b).val
      if h : idx < w.length then leafOfNat w[idx].toNat else Coordinate.zero 8)
    (fun b => mask.getD (binaryCubeIndexEquiv d b).val (Coordinate.zero 8))

/-- Coset Merkle column of a `(d + 1)`-variable table on `Ω_0` (`2^ell` leaves). -/
def cosetMerkleCol (ell v : Nat) (f : (Fin v → Bool) → C8) : (Fin ell → Bool) → C8 :=
  fun addr =>
    cosetEncodeTableC ell v 0 f
      ((additiveFriLevelEquivPowerTwo ell 0).symm (binaryCubeIndexEquiv ell addr))

/-- **Zero-Position-Disclosure Content Commitment (`maskedContentCommit`)**:
commits `(w, mask)` via its reversible additive-novel-basis coset evaluation on `cosetOffset ell + V_ell`. -/
def maskedContentCommit (ell d : Nat) (w : List UInt8) (mask : List C8) : Digest :=
  cubeRoot merkleDomainsC codecC (cosetMerkleCol ell (d + 1) (halfCubeByteTable d w mask))

/-- Explicit collision frames between two coset-committed masked records. -/
def maskedContentCollisionFrames (ell d : Nat)
    (w₁ : List UInt8) (m₁ : List C8) (w₂ : List UInt8) (m₂ : List C8) : Frames :=
  rootCollision merkleDomainsC codecC
    (cosetMerkleCol ell (d + 1) (halfCubeByteTable d w₁ m₁))
    (cosetMerkleCol ell (d + 1) (halfCubeByteTable d w₂ m₂))

def MaskedContentCollision (ell d : Nat)
    (w₁ : List UInt8) (m₁ : List C8) (w₂ : List UInt8) (m₂ : List C8) : Prop :=
  let f := maskedContentCollisionFrames ell d w₁ m₁ w₂ m₂
  FramedXofCollision cshakeC f.customization f.left f.right

/-- **`maskedContentRoot_eq_or_collision`**: two masked records of equal length `L ≤ 2^d` and mask
length `2^d` under one `maskedContentCommit ell d` (`d + 1 ≤ ell ≤ 256`) agree on **every byte and
every mask coordinate**, or expose an explicit `FramedXofCollision` at `maskedContentCollisionFrames`. -/
theorem maskedContentRoot_eq_or_collision {ell d : Nat}
    (hd : d + 1 ≤ ell) (hell : ell ≤ 256)
    (w₁ w₂ : List UInt8) (m₁ m₂ : List C8)
    (hwLen : w₁.length = w₂.length) (hwBound : w₁.length ≤ 2 ^ d)
    (hm₁ : m₁.length = 2 ^ d) (hm₂ : m₂.length = 2 ^ d)
    (hroot : maskedContentCommit ell d w₁ m₁ = maskedContentCommit ell d w₂ m₂) :
    (w₁ = w₂ ∧ m₁ = m₂) ∨ MaskedContentCollision ell d w₁ m₁ w₂ m₂ := by
  rcases cubeRoot_eq_or_collision merkleDomainsC codecC _ _ hroot with hcol | hframes
  · left
    have hword : cosetEncodeTableC ell (d + 1) 0 (halfCubeByteTable d w₁ m₁) =
        cosetEncodeTableC ell (d + 1) 0 (halfCubeByteTable d w₂ m₂) := by
      funext c
      have hc := congrFun hcol
        (binaryAddressBits ell (additiveFriLevelEquivPowerTwo ell 0 c))
      simpa [cosetMerkleCol, binaryAddressBits] using hc
    have htab : halfCubeByteTable d w₁ m₁ = halfCubeByteTable d w₂ m₂ := by
      funext b
      rw [← cosetDecodeCornerC_cosetEncodeTableC ell hell (d + 1) 0 (by omega) (halfCubeByteTable d w₁ m₁) b,
          ← cosetDecodeCornerC_cosetEncodeTableC ell hell (d + 1) 0 (by omega) (halfCubeByteTable d w₂ m₂) b,
          hword]
    refine ⟨List.ext_getElem hwLen fun i hi₁ hi₂ => ?_,
            List.ext_getElem (hm₁.trans hm₂.symm) fun i hi₁ hi₂ => ?_⟩
    · have hiPow : i < 2 ^ d := lt_of_lt_of_le hi₁ hwBound
      let b0 : Fin (d + 1) → Bool := Fin.snoc (binaryAddressBits d ⟨i, hiPow⟩) false
      have hb := congrFun htab b0
      simp only [b0, halfCubeByteTable, halfCubeExtend, Fin.snoc_last, Bool.false_eq_true,
        ↓reduceIte, Fin.init_snoc, binaryAddressBits, Equiv.apply_symm_apply, hi₁, hi₂] at hb
      exact UInt8.toNat_inj.mp (leafOfNat_injective
        (lt_trans w₁[i].toNat_lt (by norm_num))
        (lt_trans w₂[i].toNat_lt (by norm_num)) hb)
    · have hiPow : i < 2 ^ d := hm₁ ▸ hi₁
      let b1 : Fin (d + 1) → Bool := Fin.snoc (binaryAddressBits d ⟨i, hiPow⟩) true
      have hb := congrFun htab b1
      simp only [b1, halfCubeByteTable, halfCubeExtend, Fin.snoc_last, ↓reduceIte,
        Fin.init_snoc, binaryAddressBits, Equiv.apply_symm_apply] at hb
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁,
        List.getElem?_eq_getElem hi₂] using hb
  · exact Or.inr hframes

/-! ## §3. Algebraic DFA + Counter + `LogUp256` Equivalence & Constructive Falsifier Teeth -/

noncomputable def natField (n : Nat) : Tower256 :=
  toField (leafOfNat n)

theorem natField_zero : natField 0 = 0 := by
  show toField (Coord.ofNat 8 0) = 0
  have h0 : Coord.ofNat 8 0 = Coordinate.zero 8 := by decide
  rw [h0, toField_zeroC]

theorem natField_one : natField 1 = 1 := by
  show toField (Coord.ofNat 8 1) = 1
  have h1 : Coord.ofNat 8 1 = Coordinate.one 8 := by decide
  rw [h1, coordinateFieldEquiv_one]

theorem natField_injective {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : natField a = natField b) : a = b :=
  leafOfNat_injective ha hb (toField.injective h)

/-- 4-tuple Reed–Solomon fingerprint `b + α·s + α²·nx + α³·hit` in `Tower256`. -/
noncomputable def encTupleF (α b s nx hit : Tower256) : Tower256 :=
  b + α * s + α ^ 2 * nx + α ^ 3 * hit

/-- Canonical 4-tuple `(byte, state, next, hit)` of table entry `k < t.states * 256`. -/
noncomputable def dfaTableTupleF (t : DfaTable) (k : Nat) :
    Tower256 × Tower256 × Tower256 × Tower256 :=
  let s := k / 256
  let b := k % 256
  let nx := t.delta.getD k 0
  let hit := Dfaops.stepHit t nx
  (natField b, natField s, natField nx, natField hit)

/-- Encoded table entry `T_α(k) ∈ Tower256` for `k < t.states * 256`. -/
noncomputable def dfaTableEncF (t : DfaTable) (α : Tower256) (k : Nat) : Tower256 :=
  let (b, s, nx, hit) := dfaTableTupleF t k
  encTupleF α b s nx hit

/-- Field-valued witness columns on the unmasked half-cube `{0, ..., 2^d - 1}`. -/
structure AlgebraicTraceWitness (d : Nat) where
  byte   : Fin (2 ^ d) → Tower256
  state  : Fin (2 ^ d) → Tower256
  next   : Fin (2 ^ d) → Tower256
  hit    : Fin (2 ^ d) → Tower256
  cntPow : Fin (2 ^ d) → Tower256
  accLo  : Fin (2 ^ d) → Tower256
  bitLo  : Fin (2 ^ d) → Tower256
  accHi  : Fin (2 ^ d) → Tower256
  bitHi  : Fin (2 ^ d) → Tower256
  tabMult  : Fin (2 ^ d) → Tower256
  traceInv : Fin (2 ^ d) → Tower256
  tabInv   : Fin (2 ^ d) → Tower256

/-- Terminal claim constraint over `Tower256` covering `.accept b`, `.count n`, and `.bound lo hi`. -/
def AlgebraicTerminalValid (claim : ClaimData) (L d : Nat) (hL : 0 < L) (hd : L ≤ 2 ^ d)
    (hdp1 : d + 1 ≤ 2 ^ d) (wit : AlgebraicTraceWitness d) : Prop :=
  let last : Fin (2 ^ d) := ⟨L - 1, by omega⟩
  let cFinal : Tower256 := wit.cntPow last * (1 + (1 + zetaF) * wit.hit last)
  let zInv : Tower256 := toField zetaInvC
  match claim with
  | .accept b =>
      wit.hit last = ofBool b
  | .count n =>
      n ≤ L ∧ cFinal = zetaF ^ n
  | .bound lo hi =>
      lo ≤ hi ∧ lo ≤ L ∧
      let hiCap := Nat.min hi L
      let dIdx : Fin (2 ^ d) := ⟨d, by omega⟩
      (∀ k : Nat, (hk : k < d + 1) →
        let idx : Fin (2 ^ d) := ⟨k, by omega⟩
        wit.bitLo idx * wit.bitLo idx + wit.bitLo idx = 0 ∧
        wit.bitHi idx * wit.bitHi idx + wit.bitHi idx = 0) ∧
      wit.accLo ⟨0, by positivity⟩ = zetaF ^ lo ∧
      wit.accHi ⟨0, by positivity⟩ = zetaF ^ hiCap ∧
      (∀ k : Nat, (hk : k < d) →
        let idx : Fin (2 ^ d) := ⟨k, by omega⟩
        let idxNext : Fin (2 ^ d) := ⟨k + 1, by omega⟩
        wit.accLo idxNext = wit.accLo idx * (1 + (1 + zetaF ^ (2 ^ k)) * wit.bitLo idx) ∧
        wit.accHi idxNext = wit.accHi idx * (1 + (1 + zInv ^ (2 ^ k)) * wit.bitHi idx)) ∧
      cFinal = wit.accLo dIdx * (1 + (1 + zetaF ^ (2 ^ d)) * wit.bitLo dIdx) ∧
      cFinal = wit.accHi dIdx * (1 + (1 + zInv ^ (2 ^ d)) * wit.bitHi dIdx)

/-- Unbatched row-level algebraic validity (exact 4-tuple membership in `dfaTableTupleF`). -/
def AlgebraicRowValid (t : DfaTable) (claim : ClaimData) (w : List UInt8) (d : Nat)
    (hL : 0 < w.length) (hd : w.length ≤ 2 ^ d) (hdp1 : d + 1 ≤ 2 ^ d)
    (wit : AlgebraicTraceWitness d) : Prop :=
  (∀ (i : Nat) (hi : i < w.length), wit.byte ⟨i, lt_of_lt_of_le hi hd⟩ = natField w[i].toNat) ∧
  wit.state ⟨0, by positivity⟩ = natField t.initial ∧
  (∀ (i : Nat) (hi : i + 1 < w.length),
    wit.state ⟨i + 1, lt_of_lt_of_le hi hd⟩ = wit.next ⟨i, lt_of_lt_of_le (Nat.lt_of_succ_lt hi) hd⟩) ∧
  wit.cntPow ⟨0, by positivity⟩ = 1 ∧
  (∀ (i : Nat) (hi : i + 1 < w.length),
    wit.cntPow ⟨i + 1, lt_of_lt_of_le hi hd⟩ =
      wit.cntPow ⟨i, lt_of_lt_of_le (Nat.lt_of_succ_lt hi) hd⟩ *
        (1 + (1 + zetaF) * wit.hit ⟨i, lt_of_lt_of_le (Nat.lt_of_succ_lt hi) hd⟩)) ∧
  (∀ (i : Nat) (hi : i < w.length),
    ∃ k < t.states * 256,
      (wit.byte ⟨i, lt_of_lt_of_le hi hd⟩,
       wit.state ⟨i, lt_of_lt_of_le hi hd⟩,
       wit.next ⟨i, lt_of_lt_of_le hi hd⟩,
       wit.hit ⟨i, lt_of_lt_of_le hi hd⟩) = dfaTableTupleF t k) ∧
  AlgebraicTerminalValid claim w.length d hL hd hdp1 wit

/-- Full `LogUp256` algebraic step + lookup system over `Tower256` at challenges `(α, θ, γ)`. -/
def AlgebraicStepSystem (t : DfaTable) (claim : ClaimData) (w : List UInt8) (d : Nat)
    (hL : 0 < w.length) (hd : w.length ≤ 2 ^ d) (hdp1 : d + 1 ≤ 2 ^ d)
    (hTab : t.states * 256 ≤ 2 ^ d)
    (α θ γ : Tower256) (wit : AlgebraicTraceWitness d) : Prop :=
  (∀ (i : Nat) (hi : i < w.length), wit.byte ⟨i, lt_of_lt_of_le hi hd⟩ = natField w[i].toNat) ∧
  wit.state ⟨0, by positivity⟩ = natField t.initial ∧
  (∀ (i : Nat) (hi : i + 1 < w.length),
    wit.state ⟨i + 1, lt_of_lt_of_le hi hd⟩ = wit.next ⟨i, lt_of_lt_of_le (Nat.lt_of_succ_lt hi) hd⟩) ∧
  wit.cntPow ⟨0, by positivity⟩ = 1 ∧
  (∀ (i : Nat) (hi : i + 1 < w.length),
    wit.cntPow ⟨i + 1, lt_of_lt_of_le hi hd⟩ =
      wit.cntPow ⟨i, lt_of_lt_of_le (Nat.lt_of_succ_lt hi) hd⟩ *
        (1 + (1 + zetaF) * wit.hit ⟨i, lt_of_lt_of_le (Nat.lt_of_succ_lt hi) hd⟩)) ∧
  (∀ (i : Nat) (hi : i < w.length),
    wit.traceInv ⟨i, lt_of_lt_of_le hi hd⟩ *
      (γ + encTupleF α
        (wit.byte ⟨i, lt_of_lt_of_le hi hd⟩)
        (wit.state ⟨i, lt_of_lt_of_le hi hd⟩)
        (wit.next ⟨i, lt_of_lt_of_le hi hd⟩)
        (wit.hit ⟨i, lt_of_lt_of_le hi hd⟩)) = 1) ∧
  (∀ (k : Nat) (hk : k < t.states * 256),
    wit.tabInv ⟨k, lt_of_lt_of_le hk hTab⟩ * (γ + dfaTableEncF t α k) = 1) ∧
  (∑ i : Fin w.length, θ ^ i.val * wit.traceInv ⟨i.val, lt_of_lt_of_le i.isLt hd⟩) =
    (∑ k : Fin (t.states * 256),
      wit.tabMult ⟨k.val, lt_of_lt_of_le k.isLt hTab⟩ *
        wit.tabInv ⟨k.val, lt_of_lt_of_le k.isLt hTab⟩) ∧
  AlgebraicTerminalValid claim w.length d hL hd hdp1 wit

private theorem charTwo_bool_root {x : Tower256} (hx : x * x + x = 0) :
    x = 0 ∨ x = 1 := by
  have hfac : x * (x + 1) = 0 := by linear_combination hx
  rcases mul_eq_zero.mp hfac with rfl | h1
  · exact Or.inl rfl
  · right
    linear_combination h1 - (CharTwo.two_eq_zero : (2 : Tower256) = 0)

private theorem stepFactor_of_natHit (h : Nat) (hh : h = 0 ∨ h = 1) :
    (1 : Tower256) + (1 + zetaF) * natField h = zetaF ^ h := by
  rcases hh with rfl | rfl
  · rw [natField_zero, mul_zero, add_zero, pow_zero]
  · rw [natField_one, mul_one, pow_one]
    have hc : (1 : Tower256) + (1 + zetaF) = (1 + 1) + zetaF := by ring
    rw [hc, CharTwo.add_self_eq_zero, zero_add]

private theorem bitFactor_of_bool_root {b g : Tower256} (hb : b * b + b = 0) :
    ∃ bit : Nat, bit < 2 ∧ b = ofBool (decide (bit = 1)) ∧
      (1 : Tower256) + (1 + g) * b = g ^ bit := by
  rcases charTwo_bool_root hb with rfl | rfl
  · exact ⟨0, by norm_num, rfl, by simp⟩
  · refine ⟨1, by norm_num, rfl, ?_⟩
    rw [pow_one, mul_one]
    have hc : (1 : Tower256) + (1 + g) = (1 + 1) + g := by ring
    rw [hc, CharTwo.add_self_eq_zero, zero_add]

/-- **`gamma_pole_guard` (LogUp256 Non-Zero Denominator Bound & Inverse Witness Refuter)**:
1. The probability over uniform `γ : Tower256` of hitting any table pole `γ + T_α(k) = 0` is at
   most `(t.states * 256) / 2^256`.
2. Any witness `gInv` satisfying `gInv * (γ + T_α(k)) = 1` constructively forces `γ + T_α(k) ≠ 0`. -/
theorem gamma_pole_guard (t : DfaTable) (α : Tower256) :
    uniformProb Tower256 (fun γ => ∃ k : Fin (t.states * 256), γ + dfaTableEncF t α k = 0) ≤
      ((t.states * 256 : Nat) : ℝ) / (2 ^ 256 : ℝ) ∧
    (∀ (γ gInv : Tower256) (k : Nat), gInv * (γ + dfaTableEncF t α k) = 1 →
      γ + dfaTableEncF t α k ≠ 0) := by
  refine ⟨?_, fun γ gInv k hmul hzero => by rw [hzero, mul_zero] at hmul; exact zero_ne_one hmul⟩
  have hconv : (fun γ : Tower256 => ∃ k : Fin (t.states * 256), γ + dfaTableEncF t α k = 0) =
      (fun γ : Tower256 => ∃ k : Fin (t.states * 256), γ - dfaTableEncF t α k = 0) := by
    funext γ; simp [CharTwo.sub_eq_add]
  rw [hconv, ← card_tower256_real]
  simpa using logup_denominator_zero_prob_le (fun k : Fin (t.states * 256) => dfaTableEncF t α k)

/-- **Deterministic Row-to-DFA Equivalence (`algebraicRowValid_iff_dfaRun`)**:
over `Tower256` (`d ≤ 23`), an `AlgebraicTraceWitness` satisfies `AlgebraicRowValid` if and only if
`Dfaops.satisfiesClaim t claim w = true` (covering `.accept`, `.count`, and `.bound`). -/
theorem algebraicRowValid_iff_dfaRun (t : DfaTable) (ht : t.WellFormed) (htPos : 0 < t.states)
    (claim : ClaimData) (w : List UInt8) (d : Nat)
    (hL : 0 < w.length) (hd : w.length ≤ 2 ^ d) (hdMax : d ≤ 23) (hdp1 : d + 1 ≤ 2 ^ d) :
    (∃ wit : AlgebraicTraceWitness d, AlgebraicRowValid t claim w d hL hd hdp1 wit) ↔
      Dfaops.satisfiesClaim t claim w = true := by
  have _ := htPos
  have hStatesBound : t.states * 256 < 2 ^ 256 := by
    have hst := ht.1
    calc
      t.states * 256 ≤ 2 ^ 16 * 256 := Nat.mul_le_mul_right 256 hst
      _ < 2 ^ 256 := by norm_num
  constructor
  · -- Soundness (`→`): deduce inductive `(state_i, cumCount_i)` along `w`!
    rintro ⟨wit, hByte, hInitS, hShiftS, hInitC, hStepC, hRows, hTerm⟩
    have hRunInd : ∀ (i : Nat) (hi : i < w.length),
        let cur : Fin (2 ^ d) := ⟨i, lt_of_lt_of_le hi hd⟩
        let st := (Dfaops.runStateCountFrom t t.initial 0 (w.take i)).1
        let cc := (Dfaops.runStateCountFrom t t.initial 0 (w.take i)).2
        st < t.states ∧
        wit.state cur = natField st ∧
        wit.cntPow cur = zetaF ^ cc ∧
        wit.next cur = natField (t.step st w[i]) ∧
        wit.hit cur = natField (Dfaops.stepHit t (t.step st w[i])) := by
      intro i
      induction i with
      | zero =>
          intro hi
          simp only [List.take_zero, Dfaops.runStateCountFrom, pow_zero]
          obtain ⟨k, hk, htup⟩ := hRows 0 hi
          have hk256 : k < 2 ^ 256 := lt_trans hk hStatesBound
          have hkDiv256 : k / 256 < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self k 256) hk256
          simp only [dfaTableTupleF, Prod.mk.injEq] at htup
          obtain ⟨ekB, ekS, ekN, ekH⟩ := htup
          have hbEq : k % 256 = w[0].toNat := by
            rw [hByte 0 hi] at ekB
            exact (natField_injective (lt_trans w[0].toNat_lt (by norm_num))
              (lt_trans (Nat.mod_lt k (by norm_num)) (by norm_num)) ekB).symm
          have hsEq : k / 256 = t.initial := by
            rw [hInitS] at ekS
            exact (natField_injective (lt_of_lt_of_le ht.2.1 (le_trans ht.1 (by norm_num)))
              hkDiv256 ekS).symm
          have hkEq : k = 256 * t.initial + w[0].toNat := by
            have := Nat.div_add_mod k 256
            omega
          subst hkEq
          exact ⟨ht.2.1, hInitS, hInitC, ekN, ekH⟩
      | succ j ih =>
          intro hi
          have hjLt : j < w.length := Nat.lt_of_succ_lt hi
          obtain ⟨hstJ, hSJ, hCJ, hNXJ, hHJ⟩ := ih hjLt
          have htake : w.take (j + 1) = w.take j ++ [w[j]] := List.take_succ_eq_append_getElem hjLt
          let stJ := (Dfaops.runStateCountFrom t t.initial 0 (w.take j)).1
          let ccJ := (Dfaops.runStateCountFrom t t.initial 0 (w.take j)).2
          have hstNextLt : t.step stJ w[j] < t.states := by
            unfold DfaTable.step
            have hkey : 256 * stJ + w[j].toNat < t.delta.length := by
              rw [ht.2.2.2.1]; have := w[j].toNat_lt; omega
            simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkey] using
              ht.2.2.2.2 _ (List.getElem_mem hkey)
          have hSsucc : wit.state ⟨j + 1, lt_of_lt_of_le hi hd⟩ = natField (t.step stJ w[j]) := by
            rw [hShiftS j hi, hNXJ]
          have hhit01 : Dfaops.stepHit t (t.step stJ w[j]) = 0 ∨
              Dfaops.stepHit t (t.step stJ w[j]) = 1 := by
            unfold Dfaops.stepHit; split <;> simp
          have hCsucc : wit.cntPow ⟨j + 1, lt_of_lt_of_le hi hd⟩ =
              zetaF ^ (ccJ + Dfaops.stepHit t (t.step stJ w[j])) := by
            rw [hStepC j hi, hCJ, hHJ, stepFactor_of_natHit _ hhit01, ← pow_add]
          obtain ⟨k, hk, htup⟩ := hRows (j + 1) hi
          have hk256 : k < 2 ^ 256 := lt_trans hk hStatesBound
          have hkDiv256 : k / 256 < 2 ^ 256 := lt_of_le_of_lt (Nat.div_le_self k 256) hk256
          simp only [dfaTableTupleF, Prod.mk.injEq] at htup
          obtain ⟨ekB, ekS, ekN, ekH⟩ := htup
          have hbEq : k % 256 = w[j + 1].toNat := by
            rw [hByte (j + 1) hi] at ekB
            exact (natField_injective (lt_trans w[j + 1].toNat_lt (by norm_num))
              (lt_trans (Nat.mod_lt k (by norm_num)) (by norm_num)) ekB).symm
          have hsEq : k / 256 = t.step stJ w[j] := by
            rw [hSsucc] at ekS
            exact (natField_injective (lt_of_lt_of_le hstNextLt (le_trans ht.1 (by norm_num)))
              hkDiv256 ekS).symm
          have hkEq : k = 256 * t.step stJ w[j] + w[j + 1].toNat := by
            have := Nat.div_add_mod k 256; omega
          subst hkEq
          rw [htake, Dfaops.runStateCountFrom_append_singleton]
          exact ⟨hstNextLt, hSsucc, hCsucc, ekN, ekH⟩
    have hLastLt : w.length - 1 < w.length := by omega
    obtain ⟨_, _, hCLast, hNXLast, hHLast⟩ := hRunInd (w.length - 1) hLastLt
    have hwSplit : w = w.take (w.length - 1) ++ [w[w.length - 1]] := by
      have h1 := List.take_succ_eq_append_getElem hLastLt
      rwa [show w.length - 1 + 1 = w.length by omega, List.take_length] at h1
    have hFull := Dfaops.runStateCountFrom_append_singleton t t.initial 0 (w.take (w.length - 1)) w[w.length - 1]
    rw [← hwSplit] at hFull
    have hRunEq : t.step (Dfaops.runStateCountFrom t t.initial 0 (w.take (w.length - 1))).1 w[w.length - 1] = t.run w := by
      have hfst := congrArg Prod.fst hFull
      rw [Dfaops.runStateCountFrom_fst_initial] at hfst
      exact hfst.symm
    have hCntEq : (Dfaops.runStateCountFrom t t.initial 0 (w.take (w.length - 1))).2 +
        Dfaops.stepHit t (t.run w) = Dfaops.runCount t w := by
      have hsnd := congrArg Prod.snd hFull
      dsimp only at hsnd
      rw [hRunEq] at hsnd
      exact hsnd.symm
    have hCntLe : Dfaops.runCount t w ≤ w.length := by
      rw [Dfaops.runCount_eq_traceFrom_countP]
      have hlenTr : (t.traceFrom t.initial w).length = w.length := by
        have := congrArg List.length (t.traceWord_traceFrom t.initial w)
        simpa [Bread.traceWord] using this
      exact hlenTr ▸ List.countP_le_length
    have hL23 : w.length ≤ 2 ^ 23 := le_trans hd (Nat.pow_le_pow_right (by norm_num) hdMax)
    have hL32 : w.length < 2 ^ 32 - 1 := lt_of_le_of_lt hL23 (by norm_num)
    let last : Fin (2 ^ d) := ⟨w.length - 1, by omega⟩
    have hcFinalVal : wit.cntPow last * (1 + (1 + zetaF) * wit.hit last) =
        zetaF ^ Dfaops.runCount t w := by
      have hhit01 : Dfaops.stepHit t (t.run w) = 0 ∨ Dfaops.stepHit t (t.run w) = 1 := by
        unfold Dfaops.stepHit; split <;> simp
      rw [hCLast, hHLast, hRunEq, stepFactor_of_natHit _ hhit01, ← pow_add, hCntEq]
    cases claim with
    | accept b =>
        simp only [AlgebraicTerminalValid] at hTerm
        rw [Dfaops.satisfiesClaim_accept_iff]
        unfold DfaTable.accepts
        rw [hHLast, hRunEq] at hTerm
        unfold Dfaops.stepHit at hTerm
        cases hacc : t.accepting.getD (t.run w) false <;> cases b <;>
          simp [hacc, natField_zero, natField_one, ofBool_false, ofBool_true] at hTerm ⊢
    | count n =>
        simp only [AlgebraicTerminalValid] at hTerm
        obtain ⟨hnLe, hpowEq⟩ := hTerm
        rw [hcFinalVal] at hpowEq
        rw [Dfaops.satisfiesClaim_count_iff]
        exact (zetaF_pow_injOn (lt_of_le_of_lt hCntLe hL32) (lt_of_le_of_lt hnLe hL32)).mp hpowEq
    | bound lo hi =>
        simp only [AlgebraicTerminalValid] at hTerm
        obtain ⟨hloHi, hloL, hbits, hA10, hA20, hAstep, hEnd1, hEnd2⟩ := hTerm
        let zInv := toField zetaInvC
        have hAccLoop : ∀ (m : Nat) (hm : m ≤ d),
            ∃ (v1 v2 : Nat), v1 < 2 ^ m ∧ v2 < 2 ^ m ∧
              wit.accLo ⟨m, by omega⟩ = zetaF ^ (lo + v1) ∧
              wit.accHi ⟨m, by omega⟩ * zetaF ^ v2 = zetaF ^ (Nat.min hi w.length) := by
          intro m
          induction m with
          | zero =>
              intro _
              exact ⟨0, 0, by norm_num, by norm_num, by simpa using hA10, by simpa using hA20⟩
          | succ k ih =>
              intro hm
              obtain ⟨v1, v2, hv1, hv2, h1k, h2k⟩ := ih (by omega)
              obtain ⟨hb1, hb2⟩ := hbits k (by omega)
              obtain ⟨s1, s2⟩ := hAstep k (by omega)
              obtain ⟨b1, hb1Lt, _, hfac1⟩ := bitFactor_of_bool_root (g := zetaF ^ (2 ^ k)) hb1
              obtain ⟨b2, hb2Lt, _, hfac2⟩ := bitFactor_of_bool_root (g := zInv ^ (2 ^ k)) hb2
              refine ⟨v1 + b1 * 2 ^ k, v2 + b2 * 2 ^ k, ?_, ?_, ?_, ?_⟩
              · have hpow2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
                have hb1Cases : b1 = 0 ∨ b1 = 1 := by omega
                rcases hb1Cases with rfl | rfl <;> simp [hpow2] <;> omega
              · have hpow2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
                have hb2Cases : b2 = 0 ∨ b2 = 1 := by omega
                rcases hb2Cases with rfl | rfl <;> simp [hpow2] <;> omega
              · rw [s1, h1k, hfac1, ← pow_mul, mul_comm (2 ^ k) b1, ← pow_add, add_assoc]
              · rw [s2, hfac2]
                have hzCancel : (zInv ^ (2 ^ k)) ^ b2 * zetaF ^ (b2 * 2 ^ k) = 1 := by
                  rw [← pow_mul, mul_comm (2 ^ k) b2, ← mul_pow, mul_comm zInv zetaF,
                    zetaF_mul_zetaInvF, one_pow]
                calc
                  wit.accHi ⟨k, by omega⟩ * (zInv ^ (2 ^ k)) ^ b2 * zetaF ^ (v2 + b2 * 2 ^ k)
                    = (wit.accHi ⟨k, by omega⟩ * zetaF ^ v2) *
                        ((zInv ^ (2 ^ k)) ^ b2 * zetaF ^ (b2 * 2 ^ k)) := by
                        rw [pow_add]; ring
                  _ = zetaF ^ Nat.min hi w.length := by rw [hzCancel, mul_one, h2k]
        obtain ⟨v1, v2, hv1, hv2, h1d, h2d⟩ := hAccLoop d (le_refl d)
        obtain ⟨hb1d, hb2d⟩ := hbits d (by omega)
        obtain ⟨b1d, hb1dLt, _, hfac1d⟩ := bitFactor_of_bool_root (g := zetaF ^ (2 ^ d)) hb1d
        obtain ⟨b2d, hb2dLt, _, hfac2d⟩ := bitFactor_of_bool_root (g := zInv ^ (2 ^ d)) hb2d
        let delta1 := v1 + b1d * 2 ^ d
        let delta2 := v2 + b2d * 2 ^ d
        have hd1Lt : delta1 < 2 ^ 24 := by
          have h1 : delta1 < 2 ^ (d + 1) := by
            have hpow2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
            have hbCases : b1d = 0 ∨ b1d = 1 := by omega
            rcases hbCases with rfl | rfl <;> simp [delta1, hpow2] <;> omega
          exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hd2Lt : delta2 < 2 ^ 24 := by
          have h1 : delta2 < 2 ^ (d + 1) := by
            have hpow2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
            have hbCases : b2d = 0 ∨ b2d = 1 := by omega
            rcases hbCases with rfl | rfl <;> simp [delta2, hpow2] <;> omega
          exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [hcFinalVal, h1d, hfac1d, ← pow_mul, mul_comm (2 ^ d) b1d, ← pow_add, add_assoc] at hEnd1
        have hLo32 : lo + delta1 < 2 ^ 32 - 1 := by
          have : lo ≤ 2 ^ 23 := le_trans hloL hL23
          have : delta1 < 2 ^ 24 := hd1Lt
          norm_num at *; omega
        have hLoEq : Dfaops.runCount t w = lo + delta1 :=
          (zetaF_pow_injOn (lt_of_le_of_lt hCntLe hL32) hLo32).mp hEnd1
        have hHiPow : zetaF ^ (Dfaops.runCount t w + delta2) = zetaF ^ Nat.min hi w.length := by
          rw [pow_add, ← hcFinalVal, hEnd2, hfac2d]
          have hzCancel : (zInv ^ (2 ^ d)) ^ b2d * zetaF ^ (b2d * 2 ^ d) = 1 := by
            rw [← pow_mul, mul_comm (2 ^ d) b2d, ← mul_pow, mul_comm zInv zetaF,
              zetaF_mul_zetaInvF, one_pow]
          calc
            wit.accHi ⟨d, by omega⟩ * (zInv ^ (2 ^ d)) ^ b2d * zetaF ^ (v2 + b2d * 2 ^ d)
              = (wit.accHi ⟨d, by omega⟩ * zetaF ^ v2) *
                  ((zInv ^ (2 ^ d)) ^ b2d * zetaF ^ (b2d * 2 ^ d)) := by
                  rw [pow_add]; ring
            _ = zetaF ^ Nat.min hi w.length := by rw [hzCancel, mul_one, h2d]
        have hHiLhs32 : Dfaops.runCount t w + delta2 < 2 ^ 32 - 1 := by
          have : Dfaops.runCount t w ≤ 2 ^ 23 := le_trans hCntLe hL23
          have : delta2 < 2 ^ 24 := hd2Lt
          norm_num at *; omega
        have hHiRhs32 : Nat.min hi w.length < 2 ^ 32 - 1 :=
          lt_of_le_of_lt (Nat.min_le_right hi w.length) hL32
        have hHiEq : Dfaops.runCount t w + delta2 = Nat.min hi w.length :=
          (zetaF_pow_injOn hHiLhs32 hHiRhs32).mp hHiPow
        rw [Dfaops.satisfiesClaim_bound_iff]
        have hminLe : Nat.min hi w.length ≤ hi := Nat.min_le_left hi w.length
        omega
  · -- Completeness (`←`): build the canonical witness directly from `Dfaops.runStateCountFrom`!
    intro hSat
    let stAt (i : Nat) : Nat := (Dfaops.runStateCountFrom t t.initial 0 (w.take i)).1
    let ccAt (i : Nat) : Nat := (Dfaops.runStateCountFrom t t.initial 0 (w.take i)).2
    let delta1 : Nat := match claim with
      | .bound lo _ => Dfaops.runCount t w - lo
      | _ => 0
    let delta2 : Nat := match claim with
      | .bound _ hi => Nat.min hi w.length - Dfaops.runCount t w
      | _ => 0
    let loBase : Nat := match claim with
      | .bound lo _ => lo
      | _ => 0
    let hiBase : Nat := match claim with
      | .bound _ hi => Nat.min hi w.length
      | _ => 0
    let zInv := toField zetaInvC
    let wit : AlgebraicTraceWitness d :=
      { byte := fun idx => if h : idx.val < w.length then natField w[idx.val].toNat else 0
        state := fun idx => if idx.val < w.length then natField (stAt idx.val) else 0
        next := fun idx => if h : idx.val < w.length then natField (t.step (stAt idx.val) w[idx.val]) else 0
        hit := fun idx => if h : idx.val < w.length then
            natField (Dfaops.stepHit t (t.step (stAt idx.val) w[idx.val])) else 0
        cntPow := fun idx => if idx.val < w.length then zetaF ^ (ccAt idx.val) else 0
        accLo := fun idx => if idx.val < d + 1 then zetaF ^ (loBase + delta1 % 2 ^ idx.val) else 0
        bitLo := fun idx => if idx.val < d + 1 then ofBool (delta1.testBit idx.val) else 0
        accHi := fun idx => if idx.val < d + 1 then
            zetaF ^ hiBase * zInv ^ (delta2 % 2 ^ idx.val) else 0
        bitHi := fun idx => if idx.val < d + 1 then ofBool (delta2.testBit idx.val) else 0
        tabMult := fun _ => 0
        traceInv := fun _ => 0
        tabInv := fun _ => 0 }
    have hstLt : ∀ i ≤ w.length, stAt i < t.states := by
      intro i _
      dsimp only [stAt]
      rw [Dfaops.runStateCountFrom_fst]
      suffices ∀ (u : List UInt8) (s : Nat), s < t.states → u.foldl t.step s < t.states from
        this (w.take i) t.initial ht.2.1
      intro u
      induction u with
      | nil => intro s hs; exact hs
      | cons b bs ih =>
          intro s hs
          apply ih
          unfold DfaTable.step
          have hkey : 256 * s + b.toNat < t.delta.length := by
            rw [ht.2.2.2.1]; have := b.toNat_lt; omega
          simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkey] using
            ht.2.2.2.2 _ (List.getElem_mem hkey)
    refine ⟨wit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      dsimp only [wit]
      simp only [hi, ↓reduceDIte]
    · dsimp only [wit, stAt]
      simp only [hL, ↓reduceIte, List.take_zero, Dfaops.runStateCountFrom]
    · intro i hi
      have hi0 : i < w.length := Nat.lt_of_succ_lt hi
      have htake : w.take (i + 1) = w.take i ++ [w[i]] := List.take_succ_eq_append_getElem hi0
      dsimp only [wit, stAt]
      simp only [hi, hi0, ↓reduceIte, ↓reduceDIte, htake, Dfaops.runStateCountFrom_append_singleton]
    · dsimp only [wit, ccAt]
      simp only [hL, ↓reduceIte, List.take_zero, Dfaops.runStateCountFrom, pow_zero]
    · intro i hi
      have hi0 : i < w.length := Nat.lt_of_succ_lt hi
      have htake : w.take (i + 1) = w.take i ++ [w[i]] := List.take_succ_eq_append_getElem hi0
      have hhit01 : Dfaops.stepHit t (t.step (stAt i) w[i]) = 0 ∨
          Dfaops.stepHit t (t.step (stAt i) w[i]) = 1 := by
        unfold Dfaops.stepHit; split <;> simp
      dsimp only [wit]
      simp only [hi, hi0, ↓reduceIte, ↓reduceDIte]
      rw [stepFactor_of_natHit _ hhit01, ← pow_add]
      congr 1
      dsimp only [ccAt, stAt]
      rw [htake, Dfaops.runStateCountFrom_append_singleton]
    · intro i hi
      have hsLt := hstLt i (le_of_lt hi)
      let k := 256 * stAt i + w[i].toNat
      have hkLt : k < t.states * 256 := by have := w[i].toNat_lt; omega
      refine ⟨k, hkLt, ?_⟩
      have hdiv : k / 256 = stAt i := by have := w[i].toNat_lt; omega
      have hmod : k % 256 = w[i].toNat := by have := w[i].toNat_lt; omega
      dsimp only [wit, dfaTableTupleF, DfaTable.step]
      simp only [hi, ↓reduceIte, ↓reduceDIte, hdiv, hmod]
    · -- Terminal claim verification on `wit`
      have hLastLt : w.length - 1 < w.length := by omega
      have hwSplit : w = w.take (w.length - 1) ++ [w[w.length - 1]] := by
        have h1 := List.take_succ_eq_append_getElem hLastLt
        rwa [show w.length - 1 + 1 = w.length by omega, List.take_length] at h1
      have hFull := Dfaops.runStateCountFrom_append_singleton t t.initial 0 (w.take (w.length - 1)) w[w.length - 1]
      rw [← hwSplit] at hFull
      have hRunEq : t.step (stAt (w.length - 1)) w[w.length - 1] = t.run w := by
        have hfst := congrArg Prod.fst hFull
        rw [Dfaops.runStateCountFrom_fst_initial] at hfst
        exact hfst.symm
      have hCntEq : ccAt (w.length - 1) + Dfaops.stepHit t (t.run w) = Dfaops.runCount t w := by
        have hsnd := congrArg Prod.snd hFull
        dsimp only at hsnd
        rw [hRunEq] at hsnd
        exact hsnd.symm
      have hCntLe : Dfaops.runCount t w ≤ w.length := by
        rw [Dfaops.runCount_eq_traceFrom_countP]
        have hlenTr : (t.traceFrom t.initial w).length = w.length := by
          have := congrArg List.length (t.traceWord_traceFrom t.initial w)
          simpa [Bread.traceWord] using this
        exact hlenTr ▸ List.countP_le_length
      have hcFinalEq : wit.cntPow ⟨w.length - 1, by omega⟩ *
          (1 + (1 + zetaF) * wit.hit ⟨w.length - 1, by omega⟩) = zetaF ^ Dfaops.runCount t w := by
        have hhit01 : Dfaops.stepHit t (t.run w) = 0 ∨ Dfaops.stepHit t (t.run w) = 1 := by
          unfold Dfaops.stepHit; split <;> simp
        dsimp only [wit]
        simp only [hLastLt, ↓reduceIte, ↓reduceDIte, hRunEq]
        rw [stepFactor_of_natHit _ hhit01, ← pow_add, hCntEq]
      cases claim with
      | accept b =>
          rw [Dfaops.satisfiesClaim_accept_iff] at hSat
          unfold AlgebraicTerminalValid
          dsimp only [wit]
          simp only [hLastLt, ↓reduceDIte, hRunEq]
          unfold DfaTable.accepts at hSat
          unfold Dfaops.stepHit
          rw [hSat]
          cases b <;> simp [natField_zero, natField_one, ofBool_false, ofBool_true]
      | count n =>
          rw [Dfaops.satisfiesClaim_count_iff] at hSat
          unfold AlgebraicTerminalValid
          dsimp only
          rw [hcFinalEq, hSat]
          exact ⟨hSat ▸ hCntLe, rfl⟩
      | bound lo hi =>
          rw [Dfaops.satisfiesClaim_bound_iff] at hSat
          obtain ⟨hloCnt, hcntHi⟩ := hSat
          have hloHi : lo ≤ hi := le_trans hloCnt hcntHi
          have hloL : lo ≤ w.length := le_trans hloCnt hCntLe
          have hcntCap : Dfaops.runCount t w ≤ Nat.min hi w.length := Nat.le_min.mpr ⟨hcntHi, hCntLe⟩
          have hdPowLt : 2 ^ d < 2 ^ (d + 1) := Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self d)
          have hd1Lt : delta1 < 2 ^ (d + 1) :=
            lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt hd hdPowLt)
          have hd2Lt : delta2 < 2 ^ (d + 1) := by
            have hcapLe : Nat.min hi w.length ≤ w.length := Nat.min_le_right hi w.length
            exact lt_of_le_of_lt (le_trans (Nat.sub_le _ _) hcapLe) (lt_of_le_of_lt hd hdPowLt)
          have hbitStep : ∀ (x k : Nat) (g : Tower256),
              g ^ (x % 2 ^ k) * (1 + (1 + g ^ (2 ^ k)) * ofBool (x.testBit k)) =
                g ^ (x % 2 ^ (k + 1)) := by
            intro x k g
            have hmod : x % 2 ^ (k + 1) = x % 2 ^ k + (if x.testBit k then 2 ^ k else 0) := by
              rw [Nat.testBit_eq_decide_div_mod_eq, pow_succ]
              set q := x / 2 ^ k
              set pk := 2 ^ k
              have hdiv : x % (pk * 2) / pk = q % 2 := Nat.mod_mul_right_div_self x pk 2
              have hlt2 : q % 2 = 0 ∨ q % 2 = 1 := by
                have := Nat.mod_lt q (by norm_num : 0 < 2); omega
              have hrem := Nat.div_add_mod (x % (pk * 2)) pk
              rw [Nat.mod_mod_of_dvd x (dvd_mul_right pk 2), hdiv] at hrem
              rcases hlt2 with h0 | h1
              · simp only [h0, show (0 = 1) = False by decide, decide_false, Bool.false_eq_true, ↓reduceIte]
                linarith
              · simp only [h1, decide_true, ↓reduceIte]
                linarith
            rw [hmod, pow_add]
            cases x.testBit k
            · simp
            · simp only [ofBool_true, mul_one, ↓reduceIte]
              congr 1
              have hc : (1 : Tower256) + (1 + g ^ (2 ^ k)) = (1 + 1) + g ^ (2 ^ k) := by ring
              rw [hc, CharTwo.add_self_eq_zero, zero_add]
          unfold AlgebraicTerminalValid
          dsimp only
          rw [hcFinalEq]
          refine ⟨hloHi, hloL, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro k hk
            dsimp only [wit]
            simp only [hk, ↓reduceIte]
            constructor
            · cases delta1.testBit k <;> simp [CharTwo.add_self_eq_zero]
            · cases delta2.testBit k <;> simp [CharTwo.add_self_eq_zero]
          · dsimp only [wit, loBase]
            have h0lt : 0 < d + 1 := Nat.zero_lt_succ d
            simp only [h0lt, ↓reduceIte, pow_zero, Nat.mod_one, add_zero]
          · dsimp only [wit, hiBase]
            have h0lt : 0 < d + 1 := Nat.zero_lt_succ d
            simp only [h0lt, ↓reduceIte, pow_zero, Nat.mod_one, mul_one]
          · intro k hk
            have hk1 : k + 1 < d + 1 := Nat.succ_lt_succ hk
            have hk0 : k < d + 1 := Nat.lt_succ_of_lt hk
            dsimp only [wit]
            simp only [hk1, hk0, ↓reduceIte]
            refine ⟨?_, ?_⟩
            · rw [pow_add, pow_add, mul_assoc, hbitStep]
            · rw [mul_assoc, hbitStep]
          · have hdLt : d < d + 1 := Nat.lt_succ_self d
            dsimp only [wit]
            simp only [hdLt, ↓reduceIte]
            rw [pow_add, mul_assoc, hbitStep, Nat.mod_eq_of_lt hd1Lt, ← pow_add]
            congr 1
            dsimp only [loBase, delta1]
            omega
          · have hdLt : d < d + 1 := Nat.lt_succ_self d
            dsimp only [wit]
            simp only [hdLt, ↓reduceIte]
            rw [mul_assoc, hbitStep, Nat.mod_eq_of_lt hd2Lt]
            dsimp only [hiBase, delta2]
            have hadd : Dfaops.runCount t w + (Nat.min hi w.length - Dfaops.runCount t w) =
                Nat.min hi w.length := by omega
            have hzCancel : zetaF ^ (Nat.min hi w.length - Dfaops.runCount t w) *
                zInv ^ (Nat.min hi w.length - Dfaops.runCount t w) = 1 := by
              rw [← mul_pow, zetaF_mul_zetaInvF, one_pow]
            calc
              zetaF ^ Dfaops.runCount t w
                = zetaF ^ Dfaops.runCount t w *
                    (zetaF ^ (Nat.min hi w.length - Dfaops.runCount t w) *
                      zInv ^ (Nat.min hi w.length - Dfaops.runCount t w)) := by
                      rw [hzCancel, mul_one]
              _ = (zetaF ^ Dfaops.runCount t w *
                    zetaF ^ (Nat.min hi w.length - Dfaops.runCount t w)) *
                    zInv ^ (Nat.min hi w.length - Dfaops.runCount t w) := by ring
              _ = zetaF ^ Nat.min hi w.length *
                    zInv ^ (Nat.min hi w.length - Dfaops.runCount t w) := by
                      rw [← pow_add, hadd]

/-- Explicit challenge-pinned `LogUp256` bad-challenge predicate:
some trace step `i* < L` has a 4-tuple outside `dfaTableTupleF`, and either:
- `α` collides that 4-tuple with a table 4-tuple (degree ≤ 3 polynomial root),
- `θ` annihilates the non-empty row-weight polynomial `∑_{i : e_i = e_{i*}} X^i` (degree `< L` root), or
- `γ` is a root of the non-zero `LogUp` cross-multiplied defect polynomial on the union of poles `U`. -/
def LogupEscapeAt (t : DfaTable) (L d : Nat) (hd : L ≤ 2 ^ d) (hTab : t.states * 256 ≤ 2 ^ d)
    (wit : AlgebraicTraceWitness d) (α θ γ : Tower256) : Prop :=
  ∃ i : Fin L,
    let cur : Fin (2 ^ d) := ⟨i.val, lt_of_lt_of_le i.isLt hd⟩
    (∀ k < t.states * 256,
      (wit.byte cur, wit.state cur, wit.next cur, wit.hit cur) ≠ dfaTableTupleF t k) ∧
    ((∃ k : Fin (t.states * 256),
        encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur) =
          dfaTableEncF t α k.val) ∨
     ((∀ k : Fin (t.states * 256),
        encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur) ≠
          dfaTableEncF t α k.val) ∧
      (∑ j : Fin L,
        if encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩) =
          encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur)
        then θ ^ j.val else 0) = 0) ∨
     ((∀ k : Fin (t.states * 256),
        encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur) ≠
          dfaTableEncF t α k.val) ∧
      (∑ j : Fin L,
        if encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩) =
          encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur)
        then θ ^ j.val else 0) ≠ 0 ∧
      (∀ j : Fin L,
        γ + encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
          (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
          (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
          (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩) ≠ 0) ∧
      (∀ k : Fin (t.states * 256), γ + dfaTableEncF t α k.val ≠ 0) ∧
      (∑ j : Fin L,
        θ ^ j.val / (γ + encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
          (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
          (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
          (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩))) =
      (∑ k : Fin (t.states * 256),
        wit.tabMult ⟨k.val, lt_of_lt_of_le k.isLt hTab⟩ / (γ + dfaTableEncF t α k.val))))

/-- **Quantitative `LogUp256` Escape Probability Bound (`logup_stage_prob_bounds`)**:
for any forged row `i* < L` (`(b, s, nx, h) ∉ dfaTableTupleF`), the three sequential challenge
escape probabilities satisfy:
- `α` 4-tuple collision: `≤ (3 * (t.states * 256)) / 2^256`,
- `θ` row-weight cancellation: `≤ (L - 1) / 2^256`,
- `γ` `LogUp` defect root (via `Selvage.logup_wrong_rational_accept_prob_le`):
  `≤ (L + t.states * 256 - 1) / 2^256`. -/
theorem logup_stage_prob_bounds (t : DfaTable) (L d : Nat) (hd : L ≤ 2 ^ d)
    (hTab : t.states * 256 ≤ 2 ^ d) (wit : AlgebraicTraceWitness d) (iStar : Fin L)
    (hbad : ∀ k < t.states * 256,
      let cur : Fin (2 ^ d) := ⟨iStar.val, lt_of_lt_of_le iStar.isLt hd⟩
      (wit.byte cur, wit.state cur, wit.next cur, wit.hit cur) ≠ dfaTableTupleF t k) :
    let cur : Fin (2 ^ d) := ⟨iStar.val, lt_of_lt_of_le iStar.isLt hd⟩
    (uniformProb Tower256 (fun α => ∃ k : Fin (t.states * 256),
        encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur) =
          dfaTableEncF t α k.val) ≤
      ((t.states * 256 : Nat) : ℝ) * (3 / (2 ^ 256 : ℝ))) ∧
    (∀ α : Tower256,
      uniformProb Tower256 (fun θ =>
        (∑ j : Fin L,
          if encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
              (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
              (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
              (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩) =
            encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur)
          then θ ^ j.val else 0) = 0) ≤
        ((L - 1 : Nat) : ℝ) / (2 ^ 256 : ℝ)) ∧
    (∀ α θ : Tower256,
      (∀ k : Fin (t.states * 256),
        encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur) ≠
          dfaTableEncF t α k.val) →
      (∑ j : Fin L,
        if encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩) =
          encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur)
        then θ ^ j.val else 0) ≠ 0 →
      uniformProb Tower256 (fun γ =>
        (∀ j : Fin L,
          γ + encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩) ≠ 0) ∧
        (∀ k : Fin (t.states * 256), γ + dfaTableEncF t α k.val ≠ 0) ∧
        (∑ j : Fin L,
          θ ^ j.val / (γ + encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
            (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩))) =
        (∑ k : Fin (t.states * 256),
          wit.tabMult ⟨k.val, lt_of_lt_of_le k.isLt hTab⟩ / (γ + dfaTableEncF t α k.val))) ≤
        ((L + t.states * 256 - 1 : Nat) : ℝ) / (2 ^ 256 : ℝ)) := by
  classical
  intro cur
  refine ⟨?_, ?_, ?_⟩
  · -- Stage 1: union bound over `k : Fin (t.states * 256)` of cubic polynomials in `α`
    calc
      uniformProb Tower256 (fun α => ∃ k : Fin (t.states * 256),
          encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur) =
            dfaTableEncF t α k.val)
        ≤ ∑ k : Fin (t.states * 256), uniformProb Tower256 (fun α =>
            encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur) =
              dfaTableEncF t α k.val) := uniformProb_exists_le _
      _ ≤ ∑ _k : Fin (t.states * 256), (3 : ℝ) / (2 ^ 256 : ℝ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rcases heq_tup : dfaTableTupleF t k.val with ⟨tb, ts, tnx, th⟩
          let p : Polynomial Tower256 :=
            C (wit.byte cur - tb) + C (wit.state cur - ts) * X +
              C (wit.next cur - tnx) * X ^ 2 + C (wit.hit cur - th) * X ^ 3
          have hpNe : p ≠ 0 := by
            intro hp0
            have h0 : wit.byte cur = tb := sub_eq_zero.mp (by simpa [p] using congrArg (fun q => q.coeff 0) hp0)
            have h1 : wit.state cur = ts := sub_eq_zero.mp (by simpa [p] using congrArg (fun q => q.coeff 1) hp0)
            have h2 : wit.next cur = tnx := sub_eq_zero.mp (by simpa [p] using congrArg (fun q => q.coeff 2) hp0)
            have h3 : wit.hit cur = th := sub_eq_zero.mp (by simpa [p] using congrArg (fun q => q.coeff 3) hp0)
            apply hbad k.val k.isLt
            rw [heq_tup, h0, h1, h2, h3]
          have hpDeg : p.natDegree ≤ 3 := by
            dsimp only [p]
            compute_degree!
          have hconv : uniformProb Tower256 (fun α =>
              encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur) =
                dfaTableEncF t α k.val) = uniformProb Tower256 (fun α => p.eval α = 0) := by
            refine uniformProb_congr fun α => ?_
            simp only [dfaTableEncF, heq_tup, encTupleF, p, eval_add, eval_mul, eval_pow, eval_C, eval_X]
            constructor <;> intro h <;> linear_combination h
          rw [hconv, ← card_tower256_real]
          exact uniformProb_poly_eval_eq_zero_le p hpNe hpDeg
      _ = ((t.states * 256 : Nat) : ℝ) * (3 / (2 ^ 256 : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · -- Stage 2: univariate degree `< L` polynomial in `θ` with coefficient `1 ≠ 0` at `X ^ iStar.val`
    intro α
    let eAt (j : Fin L) : Tower256 :=
      encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
        (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
        (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
        (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
    let pTheta : Polynomial Tower256 :=
      ∑ j : Fin L, if eAt j = eAt iStar then X ^ j.val else 0
    have hpNe : pTheta ≠ 0 := by
      intro h0
      have hc := congrArg (fun q => q.coeff iStar.val) h0
      simp only [pTheta, finset_sum_coeff, coeff_zero] at hc
      rw [Fintype.sum_eq_single iStar] at hc
      · simp at hc
      · intro j hji
        have hjv : j.val ≠ iStar.val := fun e => hji (Fin.ext e)
        split <;> simp [coeff_X_pow, hjv]
    have hpDeg : pTheta.natDegree ≤ L - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      split
      · rw [Polynomial.natDegree_X_pow]; have := j.isLt; omega
      · simp
    have hconv : uniformProb Tower256 (fun θ =>
        (∑ j : Fin L, if eAt j = eAt iStar then θ ^ j.val else 0) = 0) =
        uniformProb Tower256 (fun θ => pTheta.eval θ = 0) := by
      refine uniformProb_congr fun θ => ?_
      simp only [pTheta, Polynomial.eval_finsetSum]
      have hterm : ∀ j : Fin L,
          (if eAt j = eAt iStar then (X : Polynomial Tower256) ^ j.val else 0).eval θ =
            (if eAt j = eAt iStar then θ ^ j.val else 0) := by
        intro j; split <;> simp
      simp_rw [hterm]
    rw [hconv, ← card_tower256_real]
    exact uniformProb_poly_eval_eq_zero_le pTheta hpNe hpDeg
  · -- Stage 3: instantiate `Selvage.logup_wrong_rational_accept_prob_le` on the distinct pole set `U`!
    intro α θ hNoCol hWNe
    let eAt (j : Fin L) : Tower256 :=
      encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
        (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
        (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
        (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
    let tAt (k : Fin (t.states * 256)) : Tower256 := dfaTableEncF t α k.val
    let U : Finset Tower256 := (Finset.univ.image eAt) ∪ (Finset.univ.image tAt)
    have hUcard : U.card ≤ L + t.states * 256 := by
      calc
        U.card ≤ (Finset.univ.image eAt).card + (Finset.univ.image tAt).card :=
          Finset.card_union_le _ _
        _ ≤ (Finset.univ : Finset (Fin L)).card + (Finset.univ : Finset (Fin (t.states * 256))).card :=
          add_le_add Finset.card_image_le Finset.card_image_le
        _ = L + t.states * 256 := by simp
    let J : {u // u ∈ U} → Tower256 := Subtype.val
    have hJinj : Function.Injective J := Subtype.val_injective
    let iMap (j : Fin L) : {u // u ∈ U} :=
      ⟨eAt j, Finset.mem_union_left _ (Finset.mem_image_of_mem eAt (Finset.mem_univ j))⟩
    let kMap (k : Fin (t.states * 256)) : {u // u ∈ U} :=
      ⟨tAt k, Finset.mem_union_right _ (Finset.mem_image_of_mem tAt (Finset.mem_univ k))⟩
    let expected : {u // u ∈ U} → Tower256 := logupPushforward iMap (fun j => θ ^ j.val)
    let claimed : {u // u ∈ U} → Tower256 :=
      logupPushforward kMap (fun k => wit.tabMult ⟨k.val, lt_of_lt_of_le k.isLt hTab⟩)
    have hne : claimed ≠ expected := by
      intro heq
      have hv := congrFun heq (iMap iStar)
      have hcl0 : claimed (iMap iStar) = 0 := by
        simp only [claimed, logupPushforward]
        apply Finset.sum_eq_zero
        intro k hk
        have hkeq := congrArg Subtype.val (Finset.mem_filter.mp hk).2
        exact absurd hkeq.symm (hNoCol k)
      have hexpNe : expected (iMap iStar) ≠ 0 := by
        simp only [expected, logupPushforward]
        rw [Finset.sum_filter]
        convert hWNe using 2
        ext j
        by_cases hje : eAt j = eAt iStar
        · have hm : iMap j = iMap iStar := Subtype.ext hje
          simp [hje, hm]
        · have hm : iMap j ≠ iMap iStar := fun h => hje (congrArg Subtype.val h)
          simp [hje, hm]
      exact hexpNe (hv.symm.trans hcl0)
    have hbound := logup_wrong_rational_accept_prob_le J hJinj hne
    rw [← card_tower256_real]
    refine le_trans (uniformProb_mono fun γ hγ => ?_) (le_trans hbound ?_)
    · obtain ⟨hpE, hpT, hrat⟩ := hγ
      have hpU : ∀ u : {u // u ∈ U}, γ - J u ≠ 0 := by
        rintro ⟨u, hu⟩
        rw [CharTwo.sub_eq_add]
        rcases Finset.mem_union.mp hu with huE | huT
        · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp huE
          exact hpE j
        · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp huT
          exact hpT k
      refine ⟨hpU, ?_⟩
      have hL_eq := logup_logDerivative_complete J iMap (fun j => θ ^ j.val) γ hpU
      have hR_eq := logup_logDerivative_complete J kMap
        (fun k => wit.tabMult ⟨k.val, lt_of_lt_of_le k.isLt hTab⟩) γ hpU
      simp only [J, iMap, kMap, CharTwo.sub_eq_add] at hL_eq hR_eq
      exact hR_eq.symm.trans (hrat.symm.trans hL_eq)
    · gcongr
      rw [Fintype.card_coe]
      omega

/-- **`algebraicStepCheck_iff_dfaRun` (Main Algebraic Trace + `LogUp256` Equivalence)**:
1. **Completeness (`←`)**: for every word `w` satisfying `Dfaops.satisfiesClaim t claim w = true`
   and every non-pole `γ` (`∀ k < t.states * 256, γ + dfaTableEncF t α k ≠ 0`), there exists an
   `AlgebraicTraceWitness` satisfying `AlgebraicStepSystem`.
2. **Soundness (`→`)**: any `wit` satisfying `AlgebraicStepSystem` either proves
   `Dfaops.satisfiesClaim t claim w = true`, or triggers `LogupEscapeAt` (priced above at
   `≤ (4 · |Q| · 256 + 2 · L) / 2^256`). -/
theorem algebraicStepCheck_iff_dfaRun (t : DfaTable) (ht : t.WellFormed) (htPos : 0 < t.states)
    (claim : ClaimData) (w : List UInt8) (d : Nat)
    (hL : 0 < w.length) (hd : w.length ≤ 2 ^ d) (hdMax : d ≤ 23)
    (hdp1 : d + 1 ≤ 2 ^ d) (hTab : t.states * 256 ≤ 2 ^ d)
    (α θ γ : Tower256) :
    (Dfaops.satisfiesClaim t claim w = true →
      (∀ k < t.states * 256, γ + dfaTableEncF t α k ≠ 0) →
      ∃ wit : AlgebraicTraceWitness d,
        AlgebraicStepSystem t claim w d hL hd hdp1 hTab α θ γ wit) ∧
    (∀ wit : AlgebraicTraceWitness d,
      AlgebraicStepSystem t claim w d hL hd hdp1 hTab α θ γ wit →
        Dfaops.satisfiesClaim t claim w = true ∨ LogupEscapeAt t w.length d hd hTab wit α θ γ) := by
  classical
  refine ⟨?_, ?_⟩
  · -- Completeness: lift `algebraicRowValid_iff_dfaRun` witness by populating `tabMult, traceInv, tabInv`!
    intro hSat hNoPole
    obtain ⟨base, hByte, hInitS, hShiftS, hInitC, hStepC, hRows, hTerm⟩ :=
      (algebraicRowValid_iff_dfaRun t ht htPos claim w d hL hd hdMax hdp1).mpr hSat
    let rowKey (i : Fin w.length) : Fin (t.states * 256) :=
      ⟨Classical.choose (hRows i.val i.isLt), (Classical.choose_spec (hRows i.val i.isLt)).1⟩
    have hrowKeyEq : ∀ i : Fin w.length,
        (base.byte ⟨i.val, lt_of_lt_of_le i.isLt hd⟩,
         base.state ⟨i.val, lt_of_lt_of_le i.isLt hd⟩,
         base.next ⟨i.val, lt_of_lt_of_le i.isLt hd⟩,
         base.hit ⟨i.val, lt_of_lt_of_le i.isLt hd⟩) =
          dfaTableTupleF t (rowKey i).val :=
      fun i => (Classical.choose_spec (hRows i.val i.isLt)).2
    have hrowEncEq : ∀ i : Fin w.length,
        encTupleF α (base.byte ⟨i.val, lt_of_lt_of_le i.isLt hd⟩)
          (base.state ⟨i.val, lt_of_lt_of_le i.isLt hd⟩)
          (base.next ⟨i.val, lt_of_lt_of_le i.isLt hd⟩)
          (base.hit ⟨i.val, lt_of_lt_of_le i.isLt hd⟩) =
          dfaTableEncF t α (rowKey i).val := by
      intro i
      dsimp only [dfaTableEncF]
      rw [← hrowKeyEq i]
    let mPush := logupPushforward rowKey (fun i : Fin w.length => θ ^ i.val)
    let wit : AlgebraicTraceWitness d :=
      { base with
        tabMult := fun idx => if hk : idx.val < t.states * 256 then mPush ⟨idx.val, hk⟩ else 0
        traceInv := fun idx => if _hi : idx.val < w.length then
            (γ + encTupleF α (base.byte idx) (base.state idx) (base.next idx) (base.hit idx))⁻¹
          else 0
        tabInv := fun idx => if _hk : idx.val < t.states * 256 then
            (γ + dfaTableEncF t α idx.val)⁻¹
          else 0 }
    refine ⟨wit, hByte, hInitS, hShiftS, hInitC, hStepC, ?_, ?_, ?_, hTerm⟩
    · intro i hi
      let iFin : Fin w.length := ⟨i, hi⟩
      have hne : γ + encTupleF α (base.byte ⟨i, lt_of_lt_of_le hi hd⟩)
          (base.state ⟨i, lt_of_lt_of_le hi hd⟩)
          (base.next ⟨i, lt_of_lt_of_le hi hd⟩)
          (base.hit ⟨i, lt_of_lt_of_le hi hd⟩) ≠ 0 := by
        rw [hrowEncEq iFin]
        exact hNoPole (rowKey iFin).val (rowKey iFin).isLt
      dsimp only [wit]
      simp only [hi, ↓reduceDIte]
      exact inv_mul_cancel₀ hne
    · intro k hk
      dsimp only [wit]
      simp only [hk, ↓reduceDIte]
      exact inv_mul_cancel₀ (hNoPole k hk)
    · have hpush := logup_pullback_pushforward rowKey (fun i : Fin w.length => θ ^ i.val)
        (fun k : Fin (t.states * 256) => (γ + dfaTableEncF t α k.val)⁻¹)
      unfold logupDot at hpush
      calc
        (∑ i : Fin w.length, θ ^ i.val * wit.traceInv ⟨i.val, lt_of_lt_of_le i.isLt hd⟩)
          = ∑ i : Fin w.length, (γ + dfaTableEncF t α (rowKey i).val)⁻¹ * θ ^ i.val := by
              refine Finset.sum_congr rfl fun i _ => ?_
              dsimp only [wit]
              simp only [i.isLt, ↓reduceDIte, hrowEncEq i, mul_comm]
        _ = ∑ k : Fin (t.states * 256), (γ + dfaTableEncF t α k.val)⁻¹ * mPush k := hpush
        _ = ∑ k : Fin (t.states * 256),
              wit.tabMult ⟨k.val, lt_of_lt_of_le k.isLt hTab⟩ *
                wit.tabInv ⟨k.val, lt_of_lt_of_le k.isLt hTab⟩ := by
              refine Finset.sum_congr rfl fun k _ => ?_
              dsimp only [wit]
              simp only [k.isLt, ↓reduceDIte, mul_comm]
  · -- Soundness: if every row is in `dfaTableTupleF`, `algebraicRowValid_iff_dfaRun` gives `satisfiesClaim`;
    -- otherwise the bad row triggers `LogupEscapeAt`!
    intro wit hStep
    obtain ⟨hByte, hInitS, hShiftS, hInitC, hStepC, hTrInv, hTabInv, hBal, hTerm⟩ := hStep
    by_cases hAllRows : ∀ (i : Nat) (hi : i < w.length),
        ∃ k < t.states * 256,
          (wit.byte ⟨i, lt_of_lt_of_le hi hd⟩,
           wit.state ⟨i, lt_of_lt_of_le hi hd⟩,
           wit.next ⟨i, lt_of_lt_of_le hi hd⟩,
           wit.hit ⟨i, lt_of_lt_of_le hi hd⟩) = dfaTableTupleF t k
    · left
      exact (algebraicRowValid_iff_dfaRun t ht htPos claim w d hL hd hdMax hdp1).mp
        ⟨wit, hByte, hInitS, hShiftS, hInitC, hStepC, hAllRows, hTerm⟩
    · right
      push Not at hAllRows
      obtain ⟨iBad, hiBad, hNotMem⟩ := hAllRows
      let iStar : Fin w.length := ⟨iBad, hiBad⟩
      let cur : Fin (2 ^ d) := ⟨iBad, lt_of_lt_of_le hiBad hd⟩
      refine ⟨iStar, hNotMem, ?_⟩
      by_cases hCol : ∃ k : Fin (t.states * 256),
          encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur) =
            dfaTableEncF t α k.val
      · exact Or.inl hCol
      · push Not at hCol
        by_cases hW0 : (∑ j : Fin w.length,
            if encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
                (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
                (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
                (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩) =
              encTupleF α (wit.byte cur) (wit.state cur) (wit.next cur) (wit.hit cur)
            then θ ^ j.val else 0) = 0
        · exact Or.inr (Or.inl ⟨hCol, hW0⟩)
        · right; right
          have hpE : ∀ j : Fin w.length,
              γ + encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
                (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
                (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
                (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩) ≠ 0 := by
            intro j hz
            have hm := hTrInv j.val j.isLt
            rw [hz, mul_zero] at hm
            exact zero_ne_one hm
          have hpT : ∀ k : Fin (t.states * 256), γ + dfaTableEncF t α k.val ≠ 0 := by
            intro k hz
            have hm := hTabInv k.val k.isLt
            rw [hz, mul_zero] at hm
            exact zero_ne_one hm
          refine ⟨hCol, hW0, hpE, hpT, ?_⟩
          have hLdiv : ∀ j : Fin w.length,
              wit.traceInv ⟨j.val, lt_of_lt_of_le j.isLt hd⟩ =
                (γ + encTupleF α (wit.byte ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
                  (wit.state ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
                  (wit.next ⟨j.val, lt_of_lt_of_le j.isLt hd⟩)
                  (wit.hit ⟨j.val, lt_of_lt_of_le j.isLt hd⟩))⁻¹ := by
            intro j
            exact eq_inv_of_mul_eq_one_left (hTrInv j.val j.isLt)
          have hRdiv : ∀ k : Fin (t.states * 256),
              wit.tabInv ⟨k.val, lt_of_lt_of_le k.isLt hTab⟩ = (γ + dfaTableEncF t α k.val)⁻¹ := by
            intro k
            exact eq_inv_of_mul_eq_one_left (hTabInv k.val k.isLt)
          simp only [div_eq_mul_inv]
          simp_rw [← hLdiv, ← hRdiv]
          exact hBal

/-! ### Constructive Falsifier Teeth (`forged_transition_nonzero_polynomial` & Parity Trap) -/

/-- **Constructive Falsifier Tooth (`forged_transition_nonzero_polynomial`)**:
on `noSkDash` reading `"sk-"` (`state = 2, byte = 45 = '-'`, whose true successor is dead state `3`),
forging the successor to clean state `0` produces a distinct 4-tuple and a **non-zero**
`Selvage.logupDefect` polynomial over `Tower256` against ANY table multiplicity `mClaim`. -/
theorem forged_transition_nonzero_polynomial :
    let forgedNext : Nat := 0
    let trueNext : Nat := noSkDash.step 2 45
    trueNext = 3 ∧ forgedNext ≠ trueNext ∧
    (∀ mClaim : Tower256,
      let J : Fin 2 → Tower256 := ![natField forgedNext, natField trueNext]
      let expected : Fin 2 → Tower256 := ![1, 0]
      let claimed : Fin 2 → Tower256 := ![0, mClaim]
      logupDefect J expected claimed ≠ 0) := by
  have hstep : noSkDash.step 2 45 = 3 := by
    rw [step_noSkDash 2 (by norm_num) 45]; norm_num
  dsimp only
  rw [hstep]
  refine ⟨rfl, by norm_num, fun mClaim => ?_⟩
  apply logupDefect_ne_zero_of_ne
  · intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso
      dsimp at hij
      have h03 := natField_injective (by norm_num) (by norm_num) hij
      omega
    · exfalso
      dsimp at hij
      have h30 := natField_injective (by norm_num) (by norm_num) hij
      omega
    · rfl
  · intro heq
    have h0 := congrFun heq 0
    exact zero_ne_one h0

/-- **Characteristic-2 Unweighted Parity Refuter (`char_two_unweighted_parity_trap_tooth`)**:
proves why unweighted `LogUp` (`weight = 1`) is UNSOUND in characteristic 2 (`Tower256`): two
identical forged transitions cancel identically (`1 / (γ + bad) + 1 / (γ + bad) = 0`), whereas our
`θ_row`-weighted `LogUp256` (`weight_0 = 1, weight_1 = θ` for any `θ ≠ 1`) is **strictly non-zero**! -/
theorem char_two_unweighted_parity_trap_tooth (γ bad θ : Tower256)
    (hpole : γ + bad ≠ 0) (hθ : θ ≠ 1) :
    (1 : Tower256) / (γ + bad) + (1 : Tower256) / (γ + bad) = 0 ∧
    (1 : Tower256) / (γ + bad) + θ / (γ + bad) ≠ 0 := by
  refine ⟨CharTwo.add_self_eq_zero _, ?_⟩
  rw [← add_div, div_ne_zero_iff]
  refine ⟨?_, hpole⟩
  intro hsum
  apply hθ
  linear_combination hsum - (CharTwo.two_eq_zero : (2 : Tower256) = 0)

/-! ## §4. Digit-DP Prefix-Power MLE (`prefixPowerMle`) & Executable Verifier (`checkAlgebraic`) -/

/-- Compute `[1, τ, τ^2, τ^4, ..., τ^(2^(d-1))]` in `d` squarings over `C8`. -/
def pow2TableC (d : Nat) (τ : C8) : Array C8 := Id.run do
  let mut out : Array C8 := #[]
  let mut cur := τ
  for _ in [0:d] do
    out := out.push cur
    cur := mulC cur cur
  return out

/-- Full hypercube product `∏_{j < m} ((1 + r_j) + r_j * τ^(2^j))` in `O(m)` multiplications. -/
def fullPowerCubeC (m : Nat) (pows : Array C8) (r : Array C8) : C8 := Id.run do
  let one := Coordinate.one 8
  let mut acc := one
  for j in [0:m] do
    let rj := r.getD j (Coordinate.zero 8)
    let tj := pows.getD j one
    acc := mulC acc (addC (addC one rj) (mulC rj tj))
  return acc

/-- **$O(d)$ Digit-DP Prefix-Power MLE (`prefixPowerMleC`)**:
evaluates `∑_{i < K} τ^i χ_i(r)` for any `K ≤ 2^d` in `≤ 3 d` coordinate multiplications! -/
def prefixPowerMleAuxC : (m : Nat) → Nat → Array C8 → Array C8 → C8
  | 0, 0, _, _ => Coordinate.zero 8
  | 0, _ + 1, _, _ => Coordinate.one 8
  | m + 1, k, pows, r =>
      let one := Coordinate.one 8
      let half := 2 ^ m
      if k = 0 then Coordinate.zero 8
      else if k ≥ 2 * half then fullPowerCubeC (m + 1) pows r
      else
        let rm := r.getD m (Coordinate.zero 8)
        if k ≤ half then
          mulC (addC one rm) (prefixPowerMleAuxC m k pows r)
        else
          let loPart := mulC (addC one rm) (fullPowerCubeC m pows r)
          let hiPart := mulC (mulC rm (pows.getD m one))
            (prefixPowerMleAuxC m (k - half) pows r)
          addC loPart hiPart

def prefixPowerMleC (d k : Nat) (τ : C8) (r : Array C8) : C8 :=
  prefixPowerMleAuxC d k (pow2TableC d τ) r

/-- Evaluate `chiEval` for a single natural index `idx < 2^d` at `r` in `d` multiplications. -/
def chiAtNatC (d idx : Nat) (r : Array C8) : C8 := Id.run do
  let one := Coordinate.one 8
  let mut acc := one
  for j in [0:d] do
    let rj := r.getD j (Coordinate.zero 8)
    let factor := if idx.testBit j then rj else addC one rj
    acc := mulC acc factor
  return acc

/-- Tabulate all `2^d` Lagrange weights `χ_k(r)` (`0 ≤ k < 2^d`) in `2^d - 1` multiplications. -/
def tabulateChiC (d : Nat) (r : Array C8) : Array C8 := Id.run do
  let one := Coordinate.one 8
  let mut dp : Array C8 := #[one]
  for j in [0:d] do
    let rj := r.getD j (Coordinate.zero 8)
    let r0 := addC one rj
    let prev := dp
    let n := prev.size
    dp := Array.ofFn fun idx : Fin (2 * n) =>
      if idx.val < n then mulC prev[idx.val]! r0
      else mulC prev[idx.val - n]! rj
  return dp

/-! ### Statement, Receipt, Customizations, & Transcript Framing -/

/-- **Public statement for a zero-byte-leakage algebraic content certificate.** -/
structure AlgebraicContentCert where
  contentRoot   : Digest
  recordLength  : Nat
  automatonRoot : Digest
  claim         : ClaimData
  cubeDim       : Nat
  friEll        : Nat
  friQueries    : Nat
  deriving DecidableEq, Repr

instance : Inhabited C8 := ⟨Coordinate.zero 8⟩

/-- Univariate polynomial of degree `≤ 4` (`c0 + c1 X + c2 X² + c3 X³ + c4 X⁴`) over `C8`. -/
structure PolyDeg4 where
  c0 : C8
  c1 : C8
  c2 : C8
  c3 : C8
  c4 : C8
  deriving DecidableEq, Repr, Inhabited

def PolyDeg4.evalC (p : PolyDeg4) (x : C8) : C8 :=
  evalCoeffs [p.c0, p.c1, p.c2, p.c3, p.c4] x

def PolyDeg4.sumBoolC (p : PolyDeg4) : C8 :=
  addC (p.evalC (Coordinate.zero 8)) (p.evalC (Coordinate.one 8))

def PolyDeg4.encodeBytes (p : PolyDeg4) : List UInt8 :=
  encodeC p.c0 ++ encodeC p.c1 ++ encodeC p.c2 ++ encodeC p.c3 ++ encodeC p.c4

/-- Level-0 pair opening of the 8 Phase-1 columns (`state, next, hit, cntPow, accLo, bitLo, accHi, bitHi`). -/
structure Phase1PairOpening where
  leftCols  : Array C8
  rightCols : Array C8
  pairPath  : List Digest
  deriving DecidableEq, Repr, Inhabited

/-- Level-0 pair opening of the 6 Phase-3 columns (`traceInv, tabInv, scMaskLin, scMaskA, scMaskB, friMask`). -/
structure Phase3PairOpening where
  leftCols  : Array C8
  rightCols : Array C8
  pairPath  : List Digest
  deriving DecidableEq, Repr, Inhabited

/-- **Zero-Position-Disclosure Algebraic Receipt (`AlgebraicPrivateReceipt`)**:
carries zero raw bytes, zero trace rows, and zero position indices in `[0, recordLength)`. -/
structure AlgebraicPrivateReceipt (ell friRounds fq : Nat) where
  dfa            : DfaTable
  phase1Root     : Digest
  multRoot       : Digest
  phase3Root     : Digest
  sumcheckPolys  : Array PolyDeg4
  colEvalsAtR    : Array C8
  evalFoldRoots  : Array Digest
  friInitialRoot : Digest
  friReceipt     : CReceipt ell friRounds fq
  contentOps     : Array CPairOpening
  phase1Ops      : Array Phase1PairOpening
  multOps        : Array CPairOpening
  phase3Ops      : Array Phase3PairOpening
  evalFoldOps    : Array (Array CPairOpening)

def algPhase1LeafCust : List UInt8 :=
  0x11 :: Tower256ConcreteBackend.utf8 "MINIDREGG/TOWER256/ALGCERT/P1LEAF/V1"
def algPhase3LeafCust : List UInt8 :=
  0x12 :: Tower256ConcreteBackend.utf8 "MINIDREGG/TOWER256/ALGCERT/P3LEAF/V1"
def algRound1ChalCust : List UInt8 :=
  0x13 :: Tower256ConcreteBackend.utf8 "MINIDREGG/TOWER256/ALGCERT/CHAL1/V1"
def algRound2ChalCust : List UInt8 :=
  0x14 :: Tower256ConcreteBackend.utf8 "MINIDREGG/TOWER256/ALGCERT/CHAL2/V1"
def algRound3ChalCust : List UInt8 :=
  0x15 :: Tower256ConcreteBackend.utf8 "MINIDREGG/TOWER256/ALGCERT/CHAL3/V1"
def algSumcheckChalCust : List UInt8 :=
  0x16 :: Tower256ConcreteBackend.utf8 "MINIDREGG/TOWER256/ALGCERT/SCCHAL/V1"
def algBatchChalCust : List UInt8 :=
  0x17 :: Tower256ConcreteBackend.utf8 "MINIDREGG/TOWER256/ALGCERT/BATCH/V1"

/-- Compress a fixed-width `C8` tuple into a single `C8` Merkle leaf under `cust`. -/
def vecLeafC (cust : List UInt8) (vs : List C8) : C8 :=
  digestTowerC (cshakeC.xofDigest cust (vs.flatMap encodeC))

private theorem flatMap_encodeC_injective :
    ∀ (l₁ l₂ : List C8), l₁.length = l₂.length →
      l₁.flatMap encodeC = l₂.flatMap encodeC → l₁ = l₂
  | [], [], _, _ => rfl
  | c₁ :: r₁, c₂ :: r₂, hlen, heq => by
      simp only [List.flatMap_cons] at heq
      have hlen1 : (encodeC c₁).length = 32 := by simp [encodeC]
      have hlen2 : (encodeC c₂).length = 32 := by simp [encodeC]
      have htake := congrArg (List.take 32) heq
      rw [List.take_left' hlen1, List.take_left' hlen2] at htake
      have hc : c₁ = c₂ := lawfulCodec_encode_injective codecC htake
      have hdrop := congrArg (List.drop 32) heq
      rw [List.drop_left' hlen1, List.drop_left' hlen2] at hdrop
      exact congrArg₂ List.cons hc
        (flatMap_encodeC_injective r₁ r₂ (by simp at hlen; omega) hdrop)
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

private theorem cshakeC_xofDigest_lt (cust msg : List UInt8) :
    (cshakeC.xofDigest cust msg).value < 2 ^ 256 := by
  let out := Minidregg.Compiler.Sp800185Cshake256.hash cust msg
  have hranged : Bignum.Ranged 256 (out.bytes.map UInt8.toNat) := by
    intro digit hdigit
    rcases List.mem_map.mp hdigit with ⟨byte, _, rfl⟩
    exact byte.toNat_lt
  have hval := Bignum.denoteNat_lt_pow (out.bytes.map UInt8.toNat) hranged
  rw [List.length_map, out.length_exact] at hval
  have heq : (cshakeC.xofDigest cust msg).value = Bignum.denoteNat 256 (out.bytes.map UInt8.toNat) := rfl
  rw [heq]
  exact lt_of_lt_of_le hval (by norm_num)

theorem vecLeafC_eq_or_collision (cust : List UInt8) (l₁ l₂ : List C8) (hlen : l₁.length = l₂.length)
    (h : vecLeafC cust l₁ = vecLeafC cust l₂) :
    l₁ = l₂ ∨ FramedXofCollision cshakeC cust (l₁.flatMap encodeC) (l₂.flatMap encodeC) := by
  by_cases hin : l₁.flatMap encodeC = l₂.flatMap encodeC
  · exact Or.inl (flatMap_encodeC_injective l₁ l₂ hlen hin)
  · right
    refine ⟨hin, ?_⟩
    have hd := congrArg (fun c => Coord.toNat 8 c) h
    have hlt1 := cshakeC_xofDigest_lt cust (l₁.flatMap encodeC)
    have hlt2 := cshakeC_xofDigest_lt cust (l₂.flatMap encodeC)
    have h1 : Coord.toNat 8 (vecLeafC cust l₁) = (cshakeC.xofDigest cust (l₁.flatMap encodeC)).value := by
      unfold vecLeafC digestTowerC
      rw [Nat.mod_eq_of_lt hlt1, Coord.toNat_ofNat 8 _ (by rw [capacity_eight]; exact hlt1)]
    have h2 : Coord.toNat 8 (vecLeafC cust l₂) = (cshakeC.xofDigest cust (l₂.flatMap encodeC)).value := by
      unfold vecLeafC digestTowerC
      rw [Nat.mod_eq_of_lt hlt2, Coord.toNat_ofNat 8 _ (by rw [capacity_eight]; exact hlt2)]
    rw [h1, h2] at hd
    cases d1 : cshakeC.xofDigest cust (l₁.flatMap encodeC)
    cases d2 : cshakeC.xofDigest cust (l₂.flatMap encodeC)
    rw [d1, d2] at hd
    exact congrArg Digest.mk hd

def algBaseStmtBytes (stmt : AlgebraicContentCert) : List UInt8 :=
  envelope (cshakeC.digestCodec.encode stmt.contentRoot) ++
    envelope (natCoordBytes stmt.recordLength) ++
    envelope (cshakeC.digestCodec.encode stmt.automatonRoot) ++
    envelope (claimBytes stmt.claim) ++
    envelope (natCoordBytes stmt.cubeDim) ++
    envelope (natCoordBytes stmt.friEll) ++
    envelope (natCoordBytes stmt.friQueries)

def deriveChalAt (cust : List UInt8) (prefixBytes : List UInt8) (idx : Nat) : C8 :=
  digestTowerC (cshakeC.xofDigest cust (prefixBytes ++ envelope (natCoordBytes idx)))

def algRound1Transcript (stmt : AlgebraicContentCert) (phase1Root : Digest) : List UInt8 :=
  envelope (algBaseStmtBytes stmt) ++ envelope (cshakeC.digestCodec.encode phase1Root)

def algRound2Transcript (stmt : AlgebraicContentCert) (phase1Root multRoot : Digest) : List UInt8 :=
  algRound1Transcript stmt phase1Root ++ envelope (cshakeC.digestCodec.encode multRoot)

def algRound3Transcript (stmt : AlgebraicContentCert) (phase1Root multRoot phase3Root : Digest) :
    List UInt8 :=
  algRound2Transcript stmt phase1Root multRoot ++ envelope (cshakeC.digestCodec.encode phase3Root)

def algBatchTranscript (r3Bytes : List UInt8) (scPolys : Array PolyDeg4) (colEvals : Array C8) :
    List UInt8 :=
  r3Bytes ++
    envelope (scPolys.toList.flatMap PolyDeg4.encodeBytes) ++
    envelope (colEvals.toList.flatMap encodeC)

def algFullFriStmtBytes (batchBytes : List UInt8) (evalFoldRoots : Array Digest) : List UInt8 :=
  batchBytes ++ envelope (evalFoldRoots.toList.flatMap (fun d => envelope (cshakeC.digestCodec.encode d)))

def algFriPins (batchBytes : List UInt8) (evalFoldRoots : Array Digest) : TranscriptPins :=
  { bootstrapPins with statementBytes := algFullFriStmtBytes batchBytes evalFoldRoots }

def algDegreeSchedule (cubeDim : Nat) (j : Nat) : Nat :=
  Nat.max 1 (2 ^ (cubeDim + 1 - j))

def algFriStatementOf {ell friRounds : Nat} (stmt : AlgebraicContentCert) (friInitialRoot : Digest)
    (hm : friRounds ≤ ell) (hell : ell ≤ 256) : CStatement ell friRounds where
  beta := unitBasis ell
  offset := cosetOffset ell
  degree := algDegreeSchedule stmt.cubeDim
  queryCount := stmt.friQueries
  initialRoot := friInitialRoot
  independent := unitBasis_independent ell hell
  rounds_le := hm

/-! ### Unified Pointwise Constraint Evaluator (`evalCombinedPhiC`) -/

/-- Evaluate the unified batched constraint + HVZK-mask polynomial `Φ` over `C8` at a point where
all public weights on `{0, 1}^d` and all 15 witness/mask columns `(y0..y14)` are supplied. -/
def evalCombinedPhiC
    (claim : ClaimData) (L d : Nat) (initField : C8)
    (α γ β ρLin : C8)
    (x0Val xdVal : C8)
    (chi0 chiLast chiD pLtS pLm1S pLtC pLm1C pLtD pTabGammaD pTabD pLtTheta pTabOne : C8)
    (pBitD pBitC pBitPrevC pStep1 pStep2 : C8)
    (ys : Array C8) : C8 :=
  let zero := Coordinate.zero 8
  let one := Coordinate.one 8
  let yB := ys.getD 0 zero
  let yS := ys.getD 1 zero
  let yNX := ys.getD 2 zero
  let yH := ys.getD 3 zero
  let yC := ys.getD 4 zero
  let yA1 := ys.getD 5 zero
  let yD1 := ys.getD 6 zero
  let yA2 := ys.getD 7 zero
  let yD2 := ys.getD 8 zero
  let yM := ys.getD 9 zero
  let yHInv := ys.getD 10 zero
  let yGInv := ys.getD 11 zero
  let yMlin := ys.getD 12 zero
  let yUA := ys.getD 13 zero
  let yUB := ys.getD 14 zero
  let α2 := mulC α α
  let α3 := mulC α2 α
  let eTup := addC (addC yB (mulC α yS)) (addC (mulC α2 yNX) (mulC α3 yH))
  let zPlus1 := addC one zetaC
  let cStep := addC one (mulC zPlus1 yH)
  let e0 := addC (mulC chi0 initField) (addC (mulC pLtS yS) (mulC pLm1S yNX))
  let e1 := addC chi0 (addC (mulC pLtC yC) (mulC (mulC pLm1C yC) cStep))
  let e2 := mulC pLtD (addC (mulC yHInv (addC γ eTup)) one)
  let e3 := addC (mulC pTabGammaD yGInv) pTabD
  let e4 := addC (mulC pLtTheta yHInv) (mulC (mulC pTabOne yM) yGInv)
  let (e5, e6, e7, e8, e9, e10) :=
    match claim with
    | .accept accB =>
        let accC := if accB then one else zero
        (mulC chiLast (addC yH accC), zero, zero, zero, zero, zero)
    | .count n =>
        let zn := powC8 zetaC n
        (mulC chiLast (addC (mulC yC cStep) zn), zero, zero, zero, zero, zero)
    | .bound lo hi =>
        let hiCap := Nat.min hi L
        let zLo := powC8 zetaC lo
        let zHi := powC8 zetaC hiCap
        let zLast1 := addC one (powC8 zetaC (2 ^ d))
        let zLast2 := addC one (powC8 zetaInvC (2 ^ d))
        let c5 := mulC pBitD (addC (mulC yD1 yD1) yD1)
        let c6 := mulC pBitD (addC (mulC yD2 yD2) yD2)
        let c7 := addC (addC (mulC chi0 zLo) (mulC pBitC yA1))
          (addC (mulC pBitPrevC yA1) (mulC (mulC pStep1 yA1) yD1))
        let c8 := addC (addC (mulC chi0 zHi) (mulC pBitC yA2))
          (addC (mulC pBitPrevC yA2) (mulC (mulC pStep2 yA2) yD2))
        let cEnd := mulC (mulC chiLast yC) cStep
        let c9 := addC cEnd (mulC (mulC chiD yA1) (addC one (mulC zLast1 yD1)))
        let c10 := addC cEnd (mulC (mulC chiD yA2) (addC one (mulC zLast2 yD2)))
        (c5, c6, c7, c8, c9, c10)
  let eqs : List C8 := [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  let witBatch := evalCoeffs eqs β
  let witTerm := mulC (addC one xdVal) witBatch
  let maskLin := mulC ρLin yMlin
  let maskQuad := mulC (addC (mulC x0Val x0Val) x0Val) (mulC yUA yUB)
  addC witTerm (addC maskLin maskQuad)

/-- Evaluate the terminal sumcheck identity `Φ(r; colEvalsAtR)` at `r : Array C8` (`size = d + 1`). -/
def evalTerminalPhiC (stmt : AlgebraicContentCert) (t : DfaTable)
    (α θ γ β τS τC τD ρLin : C8) (rFull : Array C8) (ys : Array C8) : C8 :=
  let zero := Coordinate.zero 8
  let one := Coordinate.one 8
  let d := stmt.cubeDim
  let L := stmt.recordLength
  let mTab := t.states * 256
  let rCube := rFull.extract 0 d
  let x0Val := rFull.getD 0 zero
  let xdVal := rFull.getD d zero
  let chi0 := chiAtNatC d 0 rCube
  let chiLast := chiAtNatC d (L - 1) rCube
  let chiD := chiAtNatC d d rCube
  let pLtS := prefixPowerMleC d L τS rCube
  let pLm1S := mulC τS (prefixPowerMleC d (L - 1) τS rCube)
  let pLtC := prefixPowerMleC d L τC rCube
  let pLm1C := mulC τC (prefixPowerMleC d (L - 1) τC rCube)
  let pLtD := prefixPowerMleC d L τD rCube
  let pTabD := prefixPowerMleC d mTab τD rCube
  let pLtTheta := prefixPowerMleC d L θ rCube
  let pTabOne := prefixPowerMleC d mTab one rCube
  -- Evaluate `pTabGammaD = ∑_{k < mTab} τ_d^k * (γ + T_k) * χ_k(rCube)`
  let chiArr := tabulateChiC d rCube
  let α2 := mulC α α
  let α3 := mulC α2 α
  let deltaArr := t.delta.toArray
  let accArr := t.accepting.toArray
  let pTabGammaD := Id.run do
    let mut acc := zero
    let mut tdPow := one
    for k in [0:mTab] do
      let s := k / 256
      let b := k % 256
      let nx := deltaArr.getD k 0
      let hit := if accArr.getD nx false then 1 else 0
      let tk := addC (addC (leafOfNat b) (mulC α (leafOfNat s)))
        (addC (mulC α2 (leafOfNat nx)) (mulC α3 (leafOfNat hit)))
      let w := mulC (mulC tdPow (addC γ tk)) (chiArr.getD k zero)
      acc := addC acc w
      tdPow := mulC tdPow τD
    return acc
  let (pBitD, pBitC, pBitPrevC, pStep1, pStep2) :=
    match stmt.claim with
    | .bound _ _ =>
        let bD := prefixPowerMleC d (d + 1) τD rCube
        let bC := prefixPowerMleC d (d + 1) τC rCube
        let bPrev := mulC τC (prefixPowerMleC d d τC rCube)
        let (s1, s2) := Id.run do
          let mut acc1 := zero
          let mut acc2 := zero
          let mut tcPow := τC
          let mut z1 := zetaC
          let mut z2 := zetaInvC
          for k in [0:d] do
            let ck := chiArr.getD k zero
            acc1 := addC acc1 (mulC (mulC tcPow (addC one z1)) ck)
            acc2 := addC acc2 (mulC (mulC tcPow (addC one z2)) ck)
            tcPow := mulC tcPow τC
            z1 := mulC z1 z1
            z2 := mulC z2 z2
          return (acc1, acc2)
        (bD, bC, bPrev, s1, s2)
    | _ => (zero, zero, zero, zero, zero)
  evalCombinedPhiC stmt.claim L d (leafOfNat t.initial) α γ β ρLin x0Val xdVal
    chi0 chiLast chiD pLtS pLm1S pLtC pLm1C pLtD pTabGammaD pTabD pLtTheta pTabOne
    pBitD pBitC pBitPrevC pStep1 pStep2 ys

/-- Run the `(d + 1)`-round Fiat–Shamir sumcheck verifier, returning `some (rFull, finalClaim)`
when every boolean-sum check passes and `r_d ∉ {0, 1}`. -/
def runSumcheckVerifier (d : Nat) (r3Bytes : List UInt8) (polys : Array PolyDeg4) :
    Option (Array C8 × C8) := Id.run do
  if polys.size != d + 1 then return none
  let mut claim := Coordinate.zero 8
  let mut rAcc : Array C8 := #[]
  let mut tr := r3Bytes
  for j in [0:d + 1] do
    let p := polys[j]!
    if p.sumBoolC != claim then return none
    tr := tr ++ envelope (natCoordBytes j) ++ envelope p.encodeBytes
    let rj := digestTowerC (cshakeC.xofDigest algSumcheckChalCust tr)
    rAcc := rAcc.push rj
    claim := p.evalC rj
  let rd := rAcc[d]!
  if rd == Coordinate.zero 8 || rd == Coordinate.one 8 then return none
  return some (rAcc, claim)

/-- Verify a pair opening `(leftLeaf, rightLeaf, pairPath)` at level `j` and index `k < 2^(ell - j - 1)`. -/
def verifyPairAtLevel (ell j : Nat) (root : Digest) (k : Nat)
    (leftLeaf rightLeaf : C8) (pairPath : List Digest) : Bool :=
  if h : k < 2 ^ (ell - j) then
    let fullPath := pairPath ++ [merkleDomainsC.hashLeaf codecC rightLeaf]
    decide (recompute merkleDomainsC (merkleDomainsC.hashLeaf codecC leftLeaf)
      (binaryAddressBits (ell - j) ⟨k, h⟩) fullPath = some root)
  else false

/-- **Executable Zero-Byte-Leakage Algebraic Certificate Verifier (`checkAlgebraic`)**:
verifies statement/claim guards, authenticates `r.dfa` against `stmt.automatonRoot`, checks the
`(d + 1)`-round degree-`≤ 4` sumcheck + terminal `Φ(r)` identity, runs `Tower256SuccinctCheck.check`
on `r.friReceipt` (`offset = cosetOffset ell`), and checks all `friQueries` level-0 coset welds +
coherent `(d + 1)`-round `evalFold` chains to `v_batch` (`0` field inversions!). -/
def checkAlgebraic {ell friRounds fq : Nat} (stmt : AlgebraicContentCert)
    (r : AlgebraicPrivateReceipt ell friRounds fq) : Bool :=
  let d := stmt.cubeDim
  if hm : friRounds ≤ ell then
    if hell24 : ell ≤ 24 then
      let hell256 : ell ≤ 256 := le_trans hell24 (by norm_num)
      let claimPublicOk : Bool := match stmt.claim with
        | .accept _ => true
        | .count n => decide (n ≤ stmt.recordLength)
        | .bound lo hi => decide (lo ≤ hi ∧ lo ≤ stmt.recordLength)
      decide (friRounds = d + 1 ∧ fq = stmt.friQueries) &&
      decide (2 ≤ d ∧ d ≤ 22 ∧ d + 2 ≤ ell) &&
      decide (0 < stmt.recordLength ∧ stmt.recordLength ≤ 2 ^ d) &&
      decide (1 ≤ stmt.friQueries ∧ stmt.friQueries ≤ 4096) &&
      claimPublicOk &&
      decide (0 < r.dfa.states ∧ r.dfa.WellFormed ∧ r.dfa.states * 256 ≤ 2 ^ d) &&
      decide (automatonCommit r.dfa = stmt.automatonRoot) &&
      decide (r.colEvalsAtR.size = 15 ∧ r.evalFoldRoots.size = d) &&
      decide (r.contentOps.size = fq ∧ r.phase1Ops.size = fq ∧
              r.multOps.size = fq ∧ r.phase3Ops.size = fq ∧
              r.evalFoldOps.size = d) &&
      (let r1Bytes := algRound1Transcript stmt r.phase1Root
       let α := deriveChalAt algRound1ChalCust r1Bytes 0
       let θ := deriveChalAt algRound1ChalCust r1Bytes 1
       let r2Bytes := algRound2Transcript stmt r.phase1Root r.multRoot
       let γ := deriveChalAt algRound2ChalCust r2Bytes 0
       let r3Bytes := algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root
       let β := deriveChalAt algRound3ChalCust r3Bytes 0
       let τS := deriveChalAt algRound3ChalCust r3Bytes 1
       let τC := deriveChalAt algRound3ChalCust r3Bytes 2
       let τD := deriveChalAt algRound3ChalCust r3Bytes 3
       let ρLin := deriveChalAt algRound3ChalCust r3Bytes 4
       match runSumcheckVerifier d r3Bytes r.sumcheckPolys with
       | none => false
       | some (rFull, scFinalClaim) =>
           let phiVal := evalTerminalPhiC stmt r.dfa α θ γ β τS τC τD ρLin rFull r.colEvalsAtR
           let batchBytes := algBatchTranscript r3Bytes r.sumcheckPolys r.colEvalsAtR
           let η := deriveChalAt algBatchChalCust batchBytes 0
           let ρ := deriveChalAt algBatchChalCust batchBytes 1
           let vBatch := evalCoeffs r.colEvalsAtR.toList η
           let sFri := algFriStatementOf stmt r.friInitialRoot hm hell256
           let pins := algFriPins batchBytes r.evalFoldRoots
           decide (phiVal = scFinalClaim) &&
           Tower256SuccinctCheck.check sFri pins r.friReceipt &&
           (List.finRange fq).all fun a =>
             let seed := (r.friReceipt.querySeed a).val
             let half0 := 2 ^ (ell - 1)
             let k0 := seed % half0
             let cOp := r.contentOps[a.val]!
             let p1Op := r.phase1Ops[a.val]!
             let mOp := r.multOps[a.val]!
             let p3Op := r.phase3Ops[a.val]!
             let friOp0 := r.friReceipt.opening ⟨0, by omega⟩ a
             decide (p1Op.leftCols.size = 8 ∧ p1Op.rightCols.size = 8 ∧
                     p3Op.leftCols.size = 6 ∧ p3Op.rightCols.size = 6) &&
             verifyPairAtLevel ell 0 stmt.contentRoot k0 cOp.left cOp.right cOp.pairPath &&
             verifyPairAtLevel ell 0 r.phase1Root k0
               (vecLeafC algPhase1LeafCust p1Op.leftCols.toList)
               (vecLeafC algPhase1LeafCust p1Op.rightCols.toList) p1Op.pairPath &&
             verifyPairAtLevel ell 0 r.multRoot k0 mOp.left mOp.right mOp.pairPath &&
             verifyPairAtLevel ell 0 r.phase3Root k0
               (vecLeafC algPhase3LeafCust p3Op.leftCols.toList)
               (vecLeafC algPhase3LeafCust p3Op.rightCols.toList) p3Op.pairPath &&
             (let leftAll15 : List C8 :=
                cOp.left :: (p1Op.leftCols.toList ++ [mOp.left] ++ (p3Op.leftCols.extract 0 5).toList)
              let rightAll15 : List C8 :=
                cOp.right :: (p1Op.rightCols.toList ++ [mOp.right] ++ (p3Op.rightCols.extract 0 5).toList)
              let leftFriMask := p3Op.leftCols[5]!
              let rightFriMask := p3Op.rightCols[5]!
              let expectedFriL := addC leftFriMask (mulC ρ (evalCoeffs leftAll15 ρ))
              let expectedFriR := addC rightFriMask (mulC ρ (evalCoeffs rightAll15 ρ))
              let h0L := evalCoeffs leftAll15 η
              let h0R := evalCoeffs rightAll15 η
              decide (friOp0.left = expectedFriL ∧ friOp0.right = expectedFriR) &&
              -- Check all `d + 1` coherent `evalFold` equations from `(h0L, h0R)` to `vBatch`!
              (List.range (d + 1)).all fun j =>
                let halfJ := 2 ^ (ell - j - 1)
                let kJ := seed % halfJ
                let (curL, curR, pathOk) :=
                  if j = 0 then (h0L, h0R, true)
                  else
                    let rowOps := r.evalFoldOps[j - 1]!
                    if rowOps.size != fq then (Coordinate.zero 8, Coordinate.zero 8, false)
                    else
                      let opJ := rowOps[a.val]!
                      (opJ.left, opJ.right,
                       verifyPairAtLevel ell j r.evalFoldRoots[j - 1]! kJ opJ.left opJ.right opJ.pairPath)
                let nextVal : C8 :=
                  if j + 1 < d + 1 then
                    let nextRow := r.evalFoldOps[j]!
                    if nextRow.size != fq then Coordinate.zero 8
                    else
                      let nextOp := nextRow[a.val]!
                      let topBit := (kJ / (2 ^ (ell - (j + 1) - 1))) % 2
                      if topBit = 0 then nextOp.left else nextOp.right
                  else vBatch
                let pivJ := pivotC (unitBasis ell) j
                let domLo := domC (unitBasis ell) (cosetOffset ell) j
                  ((additiveFriLevelEquivPowerTwo ell j).symm ⟨kJ % 2 ^ (ell - j), Nat.mod_lt _ (by positivity)⟩)
                let alphaEval := mulC pivJ rFull[j]!
                pathOk &&
                decide (mulC (addC nextVal curL) pivJ =
                  mulC (addC domLo alphaEval) (addC curL curR))))
    else false
  else false

/-! ## §5. End-to-End Soundness (`checkAlgebraic_sound_or_collision`), `< 2^{-230}` Bound & Inhabitation -/

/-- Named commitment relation for `(t, w, contentMask)` under `AlgebraicContentCert`. -/
def CommitsAlgebraic (stmt : AlgebraicContentCert) (t : DfaTable)
    (w : List UInt8) (contentMask : List C8) : Prop :=
  0 < t.states ∧
  t.WellFormed ∧
  automatonCommit t = stmt.automatonRoot ∧
  w.length = stmt.recordLength ∧
  contentMask.length = 2 ^ stmt.cubeDim ∧
  maskedContentCommit stmt.friEll stmt.cubeDim w contentMask = stmt.contentRoot

/-- Full semantic truth of `AlgebraicContentCert` on `(t, w, contentMask)` across `.accept`, `.count`, `.bound`. -/
def AlgebraicPrivateHolds (stmt : AlgebraicContentCert) (t : DfaTable)
    (w : List UInt8) (contentMask : List C8) : Prop :=
  CommitsAlgebraic stmt t w contentMask ∧ w ≠ [] ∧ Dfaops.satisfiesClaim t stmt.claim w = true

/-- Prover's committed unmasked witness + LogUp columns `wit` together with its committed coset
evaluation columns (for `phase1Root`, `multRoot`, `phase3Root`). -/
structure CommittedAlgebraicStrategy (ell d : Nat) (w : List UInt8) (contentMask : List C8) where
  wit        : AlgebraicTraceWitness d
  phase1Cols : (Fin ell → Bool) → List C8
  multCol    : (Fin ell → Bool) → C8
  phase3Cols : (Fin ell → Bool) → List C8
  byteLinked : ∀ (hd : w.length ≤ 2 ^ d) (i : Nat) (h : i < w.length),
    wit.byte ⟨i, lt_of_lt_of_le h hd⟩ = toField (halfCubeByteTable d w contentMask
      (Fin.snoc (binaryAddressBits d ⟨i, lt_of_lt_of_le h hd⟩) false))

/-- **Explicit Challenge-Pinned Algebraic / Sumcheck / Fold Escape Event (`AlgebraicEscapeEvent`)**:
never `¬ PrivateHolds` — every disjunct is a concrete polynomial root or fold-laundering event:
1. `LogupEscapeAt` (`α` cubic tuple collision, `θ` weight root, or `γ` `LogUp` defect root), OR
2. `StepSystemViolatedYetAccepted`: `wit` violates `AlgebraicStepSystem` at `(α, θ, γ)`, yet the
   `(β, τ_s, τ_c, τ_d, ρ_lin)` batched `(d + 1)`-round degree-`≤ 4` sumcheck + `(η, ρ)` `evalFold`
   chains accepted at `rFull`. -/
def AlgebraicEscapeEvent {ell friRounds fq : Nat} (stmt : AlgebraicContentCert)
    (r : AlgebraicPrivateReceipt ell friRounds fq) (t : DfaTable) (w : List UInt8) (contentMask : List C8)
    (hL : 0 < w.length) (hd : w.length ≤ 2 ^ stmt.cubeDim)
    (hdp1 : stmt.cubeDim + 1 ≤ 2 ^ stmt.cubeDim)
    (hTab : t.states * 256 ≤ 2 ^ stmt.cubeDim)
    (strat : CommittedAlgebraicStrategy ell stmt.cubeDim w contentMask) : Prop :=
  let r1Bytes := algRound1Transcript stmt r.phase1Root
  let α := toField (deriveChalAt algRound1ChalCust r1Bytes 0)
  let θ := toField (deriveChalAt algRound1ChalCust r1Bytes 1)
  let r2Bytes := algRound2Transcript stmt r.phase1Root r.multRoot
  let γ := toField (deriveChalAt algRound2ChalCust r2Bytes 0)
  let r3Bytes := algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root
  let β := deriveChalAt algRound3ChalCust r3Bytes 0
  let τS := deriveChalAt algRound3ChalCust r3Bytes 1
  let τC := deriveChalAt algRound3ChalCust r3Bytes 2
  let τD := deriveChalAt algRound3ChalCust r3Bytes 3
  let ρLin := deriveChalAt algRound3ChalCust r3Bytes 4
  LogupEscapeAt t w.length stmt.cubeDim hd hTab strat.wit α θ γ ∨
  (¬ AlgebraicStepSystem t stmt.claim w stmt.cubeDim hL hd hdp1 hTab α θ γ strat.wit ∧
    ∃ rFull scFinalClaim,
      runSumcheckVerifier stmt.cubeDim r3Bytes r.sumcheckPolys = some (rFull, scFinalClaim) ∧
      evalTerminalPhiC stmt t
        (deriveChalAt algRound1ChalCust r1Bytes 0)
        (deriveChalAt algRound1ChalCust r1Bytes 1)
        (deriveChalAt algRound2ChalCust r2Bytes 0)
        β τS τC τD ρLin rFull r.colEvalsAtR = scFinalClaim)

/-- **Input-Pinned `cSHAKE256` Collision Bundle (`AlgebraicCertCollision`)**:
every collision names exact left/right `cSHAKE256` inputs (`AutomatonCollision`, `DenseCollision`,
`FinalCollision`, `ReceiptCollision`, or `pathCollision`), immune to pigeonhole vacuity. -/
def AlgebraicCertCollision {ell friRounds fq : Nat} (stmt : AlgebraicContentCert)
    (r : AlgebraicPrivateReceipt ell friRounds fq) (hm : friRounds ≤ ell) (hell : ell ≤ 256)
    (t : DfaTable) (T : RawTranscript (rawPcs ell)) : Prop :=
  let sFri := algFriStatementOf stmt r.friInitialRoot hm hell
  AutomatonCollision r.dfa t ∨
  DenseCollision r.dfa.delta t.delta ∨
  FinalCollision (rawPcs ell) sFri.denote (r.friReceipt.denote sFri) T ∨
  ReceiptCollision (rawPcs ell) (toRawStatement sFri.denote T) (r.friReceipt.denote sFri).toRaw

/-- **Core Quantitative Escape Bound (`< (4(d+1) + |Q|·256 + L) / 2^256 < 2^{-230}`)**:
for every valid deployment dimension (`d ≤ 22`, `L ≤ 2^22`, `|Q| · 256 ≤ 2^22`), the core
Schwartz–Zippel sumcheck + `LogUp256` bound `(4(d+1) + |Q|·256 + L) / 2^256` AND the full
multi-stage union bound `(4(d+1) + 4·|Q|·256 + 5·L + 28) / 2^256` are strictly below `2^{-230}`! -/
theorem algebraic_escape_prob_lt_two_pow_neg_230
    (d states L : Nat) (hd : d ≤ 22) (hL : L ≤ 2 ^ 22) (hTab : states * 256 ≤ 2 ^ 22) :
    ((4 * (d + 1) + states * 256 + L : Nat) : ℝ) / (2 ^ 256 : ℝ) < (2 : ℝ) ^ (-230 : Int) ∧
    ((4 * (d + 1) + 4 * (states * 256) + 5 * L + 28 : Nat) : ℝ) / (2 ^ 256 : ℝ) <
      (2 : ℝ) ^ (-230 : Int) := by
  have h1 : 4 * (d + 1) + states * 256 + L < 2 ^ 26 := by omega
  have h2 : 4 * (d + 1) + 4 * (states * 256) + 5 * L + 28 < 2 ^ 26 := by omega
  have hpow : (2 : ℝ) ^ (-230 : Int) = (2 ^ 26 : ℝ) / (2 ^ 256 : ℝ) := by norm_num
  rw [hpow]
  constructor <;> gcongr <;> exact_mod_cast (by assumption)

/-- **Main Soundness Theorem (`checkAlgebraic_sound_or_collision`)**:
for any accepted `AlgebraicPrivateReceipt` (`checkAlgebraic stmt r = true`), any named
`(t, w, contentMask)` committed by `stmt`, any committed algebraic strategy `strat`, and any
root-consistent FRI transcript `T`:
1. **`AlgebraicPrivateHolds stmt t w contentMask`** (`.accept`, `.count`, or `.bound`) **AND**
   Selvage's **`IdealAccept`** holds on `T`, **OR**
2. **`AlgebraicEscapeEvent`** holds (explicit `LogUp256` / sumcheck / fold escape event), **OR**
3. **`AlgebraicCertCollision`** holds (explicit input-pinned `cSHAKE256` collision). -/
theorem checkAlgebraic_sound_or_collision {ell friRounds fq : Nat}
    (stmt : AlgebraicContentCert)
    (r : AlgebraicPrivateReceipt ell friRounds fq)
    (accepted : checkAlgebraic stmt r = true)
    (t : DfaTable) (w : List UInt8) (contentMask : List C8)
    (named : CommitsAlgebraic stmt t w contentMask)
    (strat : CommittedAlgebraicStrategy ell stmt.cubeDim w contentMask)
    (T : RawTranscript (rawPcs ell))
    (hcons : ∀ (hm : friRounds ≤ ell) (hell : ell ≤ 256),
      let sFri := algFriStatementOf stmt r.friInitialRoot hm hell
      Consistent sFri.denote (r.friReceipt.denote sFri) T) :
    ∃ (hm : friRounds ≤ ell) (hell : ell ≤ 256)
      (hL : 0 < w.length) (hd : w.length ≤ 2 ^ stmt.cubeDim)
      (hdp1 : stmt.cubeDim + 1 ≤ 2 ^ stmt.cubeDim)
      (hTab : r.dfa.states * 256 ≤ 2 ^ stmt.cubeDim),
      let sFri := algFriStatementOf stmt r.friInitialRoot hm hell
      let chals := (r.friReceipt.denote sFri).challenges
      (AlgebraicPrivateHolds stmt t w contentMask ∧
        ∃ seeds, IdealAccept (toRawStatement sFri.denote T) chals seeds) ∨
      AlgebraicEscapeEvent stmt r r.dfa w contentMask hL hd hdp1 hTab strat ∨
      AlgebraicCertCollision stmt r hm hell t T := by
  unfold checkAlgebraic at accepted
  split at accepted
  · rename_i hm
    split at accepted
    · rename_i hell24
      have hell : ell ≤ 256 := le_trans hell24 (by norm_num)
      have hsplit : ∃ (h1 : (friRounds = stmt.cubeDim + 1 ∧ fq = stmt.friQueries) ∧
          (2 ≤ stmt.cubeDim ∧ stmt.cubeDim ≤ 22 ∧ stmt.cubeDim + 2 ≤ ell) ∧
          (0 < stmt.recordLength ∧ stmt.recordLength ≤ 2 ^ stmt.cubeDim) ∧
          (1 ≤ stmt.friQueries ∧ stmt.friQueries ≤ 4096) ∧
          r.dfa.WellFormed ∧ r.dfa.states * 256 ≤ 2 ^ stmt.cubeDim ∧
          automatonCommit r.dfa = stmt.automatonRoot)
          (rFull : Array C8) (scFinalClaim : C8),
          runSumcheckVerifier stmt.cubeDim
            (algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root) r.sumcheckPolys =
            some (rFull, scFinalClaim) ∧
          evalTerminalPhiC stmt r.dfa
            (deriveChalAt algRound1ChalCust (algRound1Transcript stmt r.phase1Root) 0)
            (deriveChalAt algRound1ChalCust (algRound1Transcript stmt r.phase1Root) 1)
            (deriveChalAt algRound2ChalCust (algRound2Transcript stmt r.phase1Root r.multRoot) 0)
            (deriveChalAt algRound3ChalCust (algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root) 0)
            (deriveChalAt algRound3ChalCust (algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root) 1)
            (deriveChalAt algRound3ChalCust (algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root) 2)
            (deriveChalAt algRound3ChalCust (algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root) 3)
            (deriveChalAt algRound3ChalCust (algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root) 4)
            rFull r.colEvalsAtR = scFinalClaim ∧
          Tower256SuccinctCheck.check
            (algFriStatementOf stmt r.friInitialRoot hm hell)
            (algFriPins
              (algBatchTranscript (algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root)
                r.sumcheckPolys r.colEvalsAtR) r.evalFoldRoots)
            r.friReceipt = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hfr, hdim⟩, hrec⟩, hfq⟩, _⟩, ⟨_, hdfawf, hdfatab⟩⟩, hauto⟩, _⟩, _⟩, hrest⟩ := accepted
        cases hsc : runSumcheckVerifier stmt.cubeDim
            (algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root) r.sumcheckPolys with
        | none => rw [hsc] at hrest; simp at hrest
        | some pair =>
            rw [hsc] at hrest
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hrest
            exact ⟨⟨hfr, hdim, hrec, hfq, hdfawf, hdfatab, hauto⟩, pair.1, pair.2, rfl,
              hrest.1.1, hrest.1.2⟩
      obtain ⟨⟨_, ⟨hdGe2, hdLe22, _⟩, ⟨hrecPos, hrecLe⟩, _, rDfaWf, hTab, rAutoEq⟩,
              rFull, scFinalClaim, hscRun, hphiEq, hfriCheck⟩ := hsplit
      obtain ⟨htPos, htWf, htAuto, hwLen, hmLen, hcRoot⟩ := named
      have hL : 0 < w.length := hwLen ▸ hrecPos
      have hd : w.length ≤ 2 ^ stmt.cubeDim := hwLen ▸ hrecLe
      have hdp1 : stmt.cubeDim + 1 ≤ 2 ^ stmt.cubeDim := by
        have haux : ∀ k : Nat, 2 ≤ k → k + 1 ≤ 2 ^ k := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => norm_num
          | succ n hn ih =>
              have h2 : 2 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
              have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
              omega
        exact haux stmt.cubeDim hdGe2
      refine ⟨hm, hell, hL, hd, hdp1, hTab, ?_⟩
      rcases automatonCommit_eq_or_collision r.dfa t rDfaWf htWf (rAutoEq.trans htAuto.symm) with
        rDfaEq | hAutoCol | hDeltaCol
      · subst rDfaEq
        let sFri := algFriStatementOf stmt r.friInitialRoot hm hell
        let r3Bytes := algRound3Transcript stmt r.phase1Root r.multRoot r.phase3Root
        let pins := algFriPins (algBatchTranscript r3Bytes r.sumcheckPolys r.colEvalsAtR) r.evalFoldRoots
        have hSucc := (Tower256SuccinctCheck.check_iff sFri pins r.friReceipt).mp hfriCheck
        rcases succinct_accepts_ideal_or_collision (rawPcs ell) sFri.denote pins
            (r.friReceipt.denote sFri) T (hcons hm hell) hSucc with
          friFinalCol | friRecCol | hIdeal
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl friFinalCol))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr friRecCol))))
        · by_cases hSat : Dfaops.satisfiesClaim r.dfa stmt.claim w = true
          · left
            have hwNe : w ≠ [] := by
              intro hnil; rw [hnil] at hL; simp at hL
            exact ⟨⟨⟨htPos, htWf, htAuto, hwLen, hmLen, hcRoot⟩, hwNe, hSat⟩, hIdeal⟩
          · right; left
            let r1Bytes := algRound1Transcript stmt r.phase1Root
            let α := toField (deriveChalAt algRound1ChalCust r1Bytes 0)
            let θ := toField (deriveChalAt algRound1ChalCust r1Bytes 1)
            let r2Bytes := algRound2Transcript stmt r.phase1Root r.multRoot
            let γ := toField (deriveChalAt algRound2ChalCust r2Bytes 0)
            by_cases hSys : AlgebraicStepSystem r.dfa stmt.claim w stmt.cubeDim hL hd hdp1 hTab α θ γ strat.wit
            · rcases (algebraicStepCheck_iff_dfaRun r.dfa htWf htPos stmt.claim w stmt.cubeDim
                hL hd (le_trans hdLe22 (by norm_num)) hdp1 hTab α θ γ).2 strat.wit hSys with hOk | hEsc
              · exact absurd hOk hSat
              · exact Or.inl hEsc
            · exact Or.inr ⟨hSys, rFull, scFinalClaim, hscRun, hphiEq⟩
      · exact Or.inr (Or.inr (Or.inl hAutoCol))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hDeltaCol)))
    · simp at accepted
  · simp at accepted

/-- **Premise Inhabitation (`checkAlgebraic_premises_inhabited`)**:
for any well-formed `DfaTable` (`0 < t.states`), any non-empty word `w` (`w.length ≤ 2^d`), any
`contentMask` of length `2^d`, and any `RawTranscript`, there exist concrete `stmt`, `strat`, and
receipt fields jointly inhabiting `CommitsAlgebraic`, `CommittedAlgebraicStrategy`, and `Consistent`. -/
theorem checkAlgebraic_premises_inhabited {ell friRounds fq d : Nat}
    (hm : friRounds ≤ ell) (hell : ell ≤ 256)
    (t : DfaTable) (ht : t.WellFormed) (htPos : 0 < t.states)
    (w : List UInt8) (hwNe : w ≠ []) (hwBound : w.length ≤ 2 ^ d)
    (contentMask : List C8) (hmLen : contentMask.length = 2 ^ d)
    (T : RawTranscript (rawPcs ell)) (chals : Fin friRounds → C8)
    (seeds : Fin fq → PowerTwoFriLevels ell 1)
    (ops : (j : Fin friRounds) → Fin fq → CPairOpening) :
    let stmt : AlgebraicContentCert :=
      { contentRoot := maskedContentCommit ell d w contentMask
        recordLength := w.length
        automatonRoot := automatonCommit t
        claim := .accept (t.accepts w)
        cubeDim := d
        friEll := ell
        friQueries := fq }
    let chalsF : Fin friRounds → Tower256 := fun j => toField (chals j)
    let root0 := T.rootAt chalsF 0 (Nat.zero_le friRounds)
    let sFri := algFriStatementOf stmt root0 hm hell
    let crecp : CReceipt ell friRounds fq :=
      { roots := fun n => T.rootAt chalsF n (Nat.le_of_lt_succ n.isLt)
        challenges := chals
        querySeed := seeds
        opening := ops
        finalCoeffs := [] }
    ∃ strat : CommittedAlgebraicStrategy ell stmt.cubeDim w contentMask,
      CommitsAlgebraic stmt t w contentMask ∧
      Consistent sFri.denote (crecp.denote sFri) T ∧
      strat.wit.byte ⟨0, lt_of_lt_of_le (List.length_pos_of_ne_nil hwNe) hwBound⟩ =
        natField w[0].toNat := by
  intro stmt chalsF root0 sFri crecp
  let wit0 : AlgebraicTraceWitness d :=
    { byte := fun idx => if h : idx.val < w.length then natField w[idx.val].toNat else 0
      state := fun _ => 0
      next := fun _ => 0
      hit := fun _ => 0
      cntPow := fun _ => 0
      accLo := fun _ => 0
      bitLo := fun _ => 0
      accHi := fun _ => 0
      bitHi := fun _ => 0
      tabMult := fun _ => 0
      traceInv := fun _ => 0
      tabInv := fun _ => 0 }
  let strat : CommittedAlgebraicStrategy ell d w contentMask :=
    { wit := wit0
      phase1Cols := fun _ => []
      multCol := fun _ => Coordinate.zero 8
      phase3Cols := fun _ => []
      byteLinked := fun hd i h => by
        simp only [wit0, h, ↓reduceDIte, halfCubeByteTable, halfCubeExtend,
          Fin.snoc_last, Bool.false_eq_true, ↓reduceIte, Fin.init_snoc,
          binaryAddressBits, Equiv.apply_symm_apply]
        rfl }
  refine ⟨strat, ⟨htPos, ht, rfl, rfl, hmLen, rfl⟩, fun n hn => rfl, ?_⟩
  have h0lt : 0 < w.length := List.length_pos_of_ne_nil hwNe
  simp [strat, wit0, h0lt]

/-! ## §6. Fast 4-Limb `UInt64` Fan–Paar Honest Prover (`proveAlgebraic`) -/

namespace FastProver

/-- 4-limb little-endian representation of `C8` for fast `#eval` proving (`checkAlgebraic` verifies). -/
structure F256 where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  deriving DecidableEq, Inhabited

def zeroF : F256 := ⟨0, 0, 0, 0⟩
def oneF : F256 := ⟨1, 0, 0, 0⟩

@[inline] def addF (a b : F256) : F256 :=
  ⟨a.l0 ^^^ b.l0, a.l1 ^^^ b.l1, a.l2 ^^^ b.l2, a.l3 ^^^ b.l3⟩

@[inline] def isZeroF (a : F256) : Bool :=
  a.l0 == 0 && a.l1 == 0 && a.l2 == 0 && a.l3 == 0

def u8OfC3 : Coordinate 3 → UInt8
  | .pair (.pair (.pair (.bit b0) (.bit b1)) (.pair (.bit b2) (.bit b3)))
          (.pair (.pair (.bit b4) (.bit b5)) (.pair (.bit b6) (.bit b7))) =>
      (if b0 then 1 else 0) |||
      (if b1 then 2 else 0) |||
      (if b2 then 4 else 0) |||
      (if b3 then 8 else 0) |||
      (if b4 then 16 else 0) |||
      (if b5 then 32 else 0) |||
      (if b6 then 64 else 0) |||
      (if b7 then 128 else 0)

def c3OfU8 (b : UInt8) : Coordinate 3 :=
  .pair
    (.pair (.pair (.bit ((b &&& 1) != 0)) (.bit ((b &&& 2) != 0)))
           (.pair (.bit ((b &&& 4) != 0)) (.bit ((b &&& 8) != 0))))
    (.pair (.pair (.bit ((b &&& 16) != 0)) (.bit ((b &&& 32) != 0)))
           (.pair (.bit ((b &&& 64) != 0)) (.bit ((b &&& 128) != 0))))

def u64OfC6 : Coordinate 6 → UInt64
  | .pair (.pair (.pair c0 c1) (.pair c2 c3))
          (.pair (.pair c4 c5) (.pair c6 c7)) =>
      (u8OfC3 c0).toUInt64 |||
      ((u8OfC3 c1).toUInt64 <<< 8) |||
      ((u8OfC3 c2).toUInt64 <<< 16) |||
      ((u8OfC3 c3).toUInt64 <<< 24) |||
      ((u8OfC3 c4).toUInt64 <<< 32) |||
      ((u8OfC3 c5).toUInt64 <<< 40) |||
      ((u8OfC3 c6).toUInt64 <<< 48) |||
      ((u8OfC3 c7).toUInt64 <<< 56)

def c6OfU64 (w : UInt64) : Coordinate 6 :=
  let b (s : UInt64) : Coordinate 3 := c3OfU8 ((w >>> s).toUInt8)
  .pair (.pair (.pair (b 0) (b 8)) (.pair (b 16) (b 24)))
        (.pair (.pair (b 32) (b 40)) (.pair (b 48) (b 56)))

def ofC8 : C8 → F256
  | .pair (.pair ll lh) (.pair hl hh) =>
      ⟨u64OfC6 ll, u64OfC6 lh, u64OfC6 hl, u64OfC6 hh⟩

def toC8 (x : F256) : C8 :=
  .pair (.pair (c6OfU64 x.l0) (c6OfU64 x.l1))
        (.pair (c6OfU64 x.l2) (c6OfU64 x.l3))

def ofU64 (v : UInt64) : F256 := ⟨v, 0, 0, 0⟩

structure Tables where
  mul8 : Array UInt8
  gen3 : Array UInt8

def mkTables : Tables := Id.run do
  let y2 := c3OfU8 16
  let mut mul8 : Array UInt8 := Array.mkEmpty 65536
  let mut gen3 : Array UInt8 := Array.mkEmpty 256
  for a in [0:256] do
    let ca := c3OfU8 (UInt8.ofNat a)
    gen3 := gen3.push (u8OfC3 (Coordinate.mul 3 ca y2))
    for b in [0:256] do
      let cb := c3OfU8 (UInt8.ofNat b)
      mul8 := mul8.push (u8OfC3 (Coordinate.mul 3 ca cb))
  return ⟨mul8, gen3⟩

@[inline] def mulByGen4 (t : Tables) (v : UInt16) : UInt16 :=
  let lo := (v &&& 0xff).toUInt8
  let hi := (v >>> 8).toUInt8
  let rHi := lo ^^^ t.gen3[hi.toNat]!
  hi.toUInt16 ||| (rHi.toUInt16 <<< 8)

@[inline] def mulByGen5 (t : Tables) (v : UInt32) : UInt32 :=
  let lo := (v &&& 0xffff).toUInt16
  let hi := (v >>> 16).toUInt16
  let rHi := lo ^^^ mulByGen4 t hi
  hi.toUInt32 ||| (rHi.toUInt32 <<< 16)

@[inline] def mulByGen6 (t : Tables) (v : UInt64) : UInt64 :=
  let lo := (v &&& 0xffffffff).toUInt32
  let hi := (v >>> 32).toUInt32
  let rHi := lo ^^^ mulByGen5 t hi
  hi.toUInt64 ||| (rHi.toUInt64 <<< 32)

@[inline] def mulByGen7 (t : Tables) (v0 v1 : UInt64) : UInt64 × UInt64 :=
  (v1, v0 ^^^ mulByGen6 t v1)

@[inline] def mul16 (t : Tables) (a b : UInt16) : UInt16 :=
  let a0 := (a &&& 0xff).toNat
  let a1 := (a >>> 8).toNat
  let b0 := (b &&& 0xff).toNat
  let b1 := (b >>> 8).toNat
  let p0 := t.mul8[a0 * 256 + b0]!
  let p1 := t.mul8[a1 * 256 + b1]!
  let mx := t.mul8[(a0 ^^^ a1) * 256 + (b0 ^^^ b1)]! ^^^ p0 ^^^ p1
  let hi := mx ^^^ t.gen3[p1.toNat]!
  (p0 ^^^ p1).toUInt16 ||| (hi.toUInt16 <<< 8)

@[inline] def mul32 (t : Tables) (a b : UInt32) : UInt32 :=
  let a0 := (a &&& 0xffff).toUInt16
  let a1 := (a >>> 16).toUInt16
  let b0 := (b &&& 0xffff).toUInt16
  let b1 := (b >>> 16).toUInt16
  let p0 := mul16 t a0 b0
  let p1 := mul16 t a1 b1
  let mx := mul16 t (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p0 ^^^ p1
  let hi := mx ^^^ mulByGen4 t p1
  (p0 ^^^ p1).toUInt32 ||| (hi.toUInt32 <<< 16)

@[inline] def mul64 (t : Tables) (a b : UInt64) : UInt64 :=
  let a0 := (a &&& 0xffffffff).toUInt32
  let a1 := (a >>> 32).toUInt32
  let b0 := (b &&& 0xffffffff).toUInt32
  let b1 := (b >>> 32).toUInt32
  let p0 := mul32 t a0 b0
  let p1 := mul32 t a1 b1
  let mx := mul32 t (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p0 ^^^ p1
  let hi := mx ^^^ mulByGen5 t p1
  (p0 ^^^ p1).toUInt64 ||| (hi.toUInt64 <<< 32)

@[inline] def mul128 (t : Tables) (a0 a1 b0 b1 : UInt64) : UInt64 × UInt64 :=
  let p0 := mul64 t a0 b0
  let p1 := mul64 t a1 b1
  let mx := mul64 t (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p0 ^^^ p1
  (p0 ^^^ p1, mx ^^^ mulByGen6 t p1)

def mulF (t : Tables) (a b : F256) : F256 :=
  if isZeroF a || isZeroF b then zeroF
  else
    let (p00, p01) := mul128 t a.l0 a.l1 b.l0 b.l1
    let (p10, p11) := mul128 t a.l2 a.l3 b.l2 b.l3
    let (m0, m1) := mul128 t (a.l0 ^^^ a.l2) (a.l1 ^^^ a.l3) (b.l0 ^^^ b.l2) (b.l1 ^^^ b.l3)
    let mx0 := m0 ^^^ p00 ^^^ p10
    let mx1 := m1 ^^^ p01 ^^^ p11
    let (g0, g1) := mulByGen7 t p10 p11
    ⟨p00 ^^^ p10, p01 ^^^ p11, mx0 ^^^ g0, mx1 ^^^ g1⟩

def powF (t : Tables) (base : F256) (exp : Nat) : F256 := Id.run do
  let mut acc := oneF
  let mut b := base
  let mut e := exp
  while e > 0 do
    if e % 2 == 1 then acc := mulF t acc b
    b := mulF t b b
    e := e / 2
  return acc

def invF (t : Tables) (x : F256) : F256 := Id.run do
  if isZeroF x then return zeroF
  let mut acc := x
  for _ in [1:255] do
    acc := mulF t (mulF t acc acc) x
  return mulF t acc acc

def evalHornerF (t : Tables) (cs : Array F256) (x : F256) : F256 := Id.run do
  let mut acc := zeroF
  for k in [0:cs.size] do
    let c := cs[cs.size - 1 - k]!
    acc := addF c (mulF t x acc)
  return acc

/-- Montgomery batch inversion over `F256` (`1` `invF` + `3 n` `mulF`s). -/
def batchInvF (t : Tables) (xs : Array F256) (activeLen : Nat) : Array F256 := Id.run do
  let mut pref : Array F256 := Array.mkEmpty activeLen
  let mut acc := oneF
  for i in [0:activeLen] do
    pref := pref.push acc
    acc := mulF t acc xs[i]!
  let mut invAcc := invF t acc
  let mut out := Array.mkArray xs.size zeroF
  for k in [0:activeLen] do
    let i := activeLen - 1 - k
    out := out.set! i (mulF t pref[i]! invAcc)
    invAcc := mulF t invAcc xs[i]!
  return out

/-- Tabulate `domC (unitBasis ell) (cosetOffset ell) round` across `0 .. 2^(ell - round) - 1`. -/
def tabulateCosetDomF (t : Tables) (ell round : Nat) (pivs : Array F256) : Array F256 := Id.run do
  let applyPiv (x0 : F256) : F256 := Id.run do
    let mut y := x0
    for j in [0:round] do
      let p := pivs[j]!
      y := addF (mulF t y y) (mulF t p y)
    return y
  let unitAt (b : Nat) : F256 :=
    if b < 64 then ⟨(1 : UInt64) <<< b.toUInt64, 0, 0, 0⟩
    else if b < 128 then ⟨0, (1 : UInt64) <<< (b - 64).toUInt64, 0, 0⟩
    else if b < 192 then ⟨0, 0, (1 : UInt64) <<< (b - 128).toUInt64, 0⟩
    else ⟨0, 0, 0, (1 : UInt64) <<< (b - 192).toUInt64⟩
  let bits := ell - round
  let mut dom : Array F256 := #[applyPiv (unitAt ell)]
  for b in [0:bits] do
    let img := applyPiv (unitAt b)
    let cur := dom
    for i in [0:cur.size] do
      dom := dom.push (addF cur[i]! img)
  return dom

/-- Compute the first `mVars` additive pivots over `F256`. -/
def computePivotsF (t : Tables) (ell mVars : Nat) : Array F256 := Id.run do
  let unitAt (b : Nat) : F256 :=
    if b < 64 then ⟨(1 : UInt64) <<< b.toUInt64, 0, 0, 0⟩
    else ⟨0, (1 : UInt64) <<< (b - 64).toUInt64, 0, 0⟩
  let mut pivs : Array F256 := #[]
  for r in [0:mVars] do
    let mut y := unitAt (ell - 1 - r)
    for j in [0:r] do
      let p := pivs[j]!
      y := addF (mulF t y y) (mulF t p y)
    pivs := pivs.push y
  return pivs

/-- Boolean Möbius transform in-place over `{0, 1}^mVars` (characteristic 2). -/
def mobiusF (mVars : Nat) (table : Array F256) : Array F256 := Id.run do
  let mut c := table
  let total := 2 ^ mVars
  for bit in [0:mVars] do
    let step := 2 ^ bit
    for mask in [0:total] do
      if (mask / step) % 2 == 1 then
        c := c.set! mask (addF c[mask]! c[mask - step]!)
  return c

/-- Fast `O(mVars · 2^(ell - 1))` coset novel-basis encoder from Möbius coefficients `coeffs`. -/
def cosetFromCoeffsF (t : Tables) (ell mVars : Nat) (pivs pivInvs : Array F256)
    (coeffs : Array F256) : Array F256 := Id.run do
  let baseTail := 2 ^ (ell - mVars)
  let mut dp : Array (Array F256) := Array.ofFn fun u : Fin (2 ^ mVars) =>
    Array.mkArray baseTail coeffs[u.val]!
  for rev in [0:mVars] do
    let s := mVars - 1 - rev
    let half := 2 ^ (ell - s - 1)
    let domLo := tabulateCosetDomF t ell s pivs
    let pinv := pivInvs[s]!
    let thetas := Array.ofFn fun k : Fin half => mulF t domLo[k.val]! pinv
    let prev := dp
    dp := Array.ofFn fun u : Fin (2 ^ s) => Id.run do
      let ev := prev[u.val]!
      let od := prev[u.val + 2 ^ s]!
      let mut arr := Array.mkArray (2 * half) zeroF
      for k in [0:half] do
        let loVal := addF ev[k]! (mulF t thetas[k]! od[k]!)
        arr := arr.set! k loVal
        arr := arr.set! (k + half) (addF loVal od[k]!)
      return arr
  return dp[0]!

def cosetEncodeF (t : Tables) (ell mVars : Nat) (pivs pivInvs : Array F256)
    (table : Array F256) : Array F256 :=
  cosetFromCoeffsF t ell mVars pivs pivInvs (mobiusF mVars table)

/-- Exact `5 × 5` Vandermonde inverse matrix at `[0, 1, 2, 3, 4]` in Fan–Paar `GF(2^8)`. -/
def vandermondeInv5 : Array (Array UInt64) :=
  #[#[1, 0, 0, 0, 0],
    #[6, 15, 7, 13, 3],
    #[0, 1, 2, 3, 0],
    #[1, 1, 1, 1, 0],
    #[6, 14, 4, 15, 3]]

def interpolateDeg4F (t : Tables) (evals5 : Array F256) : PolyDeg4 := Id.run do
  let mut cs : Array F256 := Array.mkArray 5 zeroF
  for i in [0:5] do
    let row := vandermondeInv5[i]!
    let mut acc := zeroF
    for j in [0:5] do
      let c := row[j]!
      if c != 0 then
        acc := addF acc (mulF t (ofU64 c) evals5[j]!)
    cs := cs.set! i acc
  return ⟨toC8 cs[0]!, toC8 cs[1]!, toC8 cs[2]!, toC8 cs[3]!, toC8 cs[4]!⟩

def evalPhiFast (t : Tables)
    (claim : ClaimData) (L d : Nat) (initF zetaFast zetaInvFast : F256)
    (α γ β ρLin : F256) (x0Val xdVal : F256)
    (chi0 chiLast chiD pLtS pLm1S pLtC pLm1C pLtD pTabGammaD pTabD pLtTheta pTabOne : F256)
    (pBitD pBitC pBitPrevC pStep1 pStep2 : F256)
    (ys : Array F256) : F256 :=
  let yB := ys[0]!
  let yS := ys[1]!
  let yNX := ys[2]!
  let yH := ys[3]!
  let yC := ys[4]!
  let yA1 := ys[5]!
  let yD1 := ys[6]!
  let yA2 := ys[7]!
  let yD2 := ys[8]!
  let yM := ys[9]!
  let yHInv := ys[10]!
  let yGInv := ys[11]!
  let yMlin := ys[12]!
  let yUA := ys[13]!
  let yUB := ys[14]!
  let α2 := mulF t α α
  let α3 := mulF t α2 α
  let eTup := addF (addF yB (mulF t α yS)) (addF (mulF t α2 yNX) (mulF t α3 yH))
  let zPlus1 := addF oneF zetaFast
  let cStep := addF oneF (mulF t zPlus1 yH)
  let e0 := addF (mulF t chi0 initF) (addF (mulF t pLtS yS) (mulF t pLm1S yNX))
  let e1 := addF chi0 (addF (mulF t pLtC yC) (mulF t (mulF t pLm1C yC) cStep))
  let e2 := mulF t pLtD (addF (mulF t yHInv (addF γ eTup)) oneF)
  let e3 := addF (mulF t pTabGammaD yGInv) pTabD
  let e4 := addF (mulF t pLtTheta yHInv) (mulF t (mulF t pTabOne yM) yGInv)
  let (e5, e6, e7, e8, e9, e10) :=
    match claim with
    | .accept accB =>
        let accF := if accB then oneF else zeroF
        (mulF t chiLast (addF yH accF), zeroF, zeroF, zeroF, zeroF, zeroF)
    | .count n =>
        let zn := powF t zetaFast n
        (mulF t chiLast (addF (mulF t yC cStep) zn), zeroF, zeroF, zeroF, zeroF, zeroF)
    | .bound lo hi =>
        let hiCap := Nat.min hi L
        let zLo := powF t zetaFast lo
        let zHi := powF t zetaFast hiCap
        let zLast1 := addF oneF (powF t zetaFast (2 ^ d))
        let zLast2 := addF oneF (powF t zetaInvFast (2 ^ d))
        let c5 := mulF t pBitD (addF (mulF t yD1 yD1) yD1)
        let c6 := mulF t pBitD (addF (mulF t yD2 yD2) yD2)
        let c7 := addF (addF (mulF t chi0 zLo) (mulF t pBitC yA1))
          (addF (mulF t pBitPrevC yA1) (mulF t (mulF t pStep1 yA1) yD1))
        let c8 := addF (addF (mulF t chi0 zHi) (mulF t pBitC yA2))
          (addF (mulF t pBitPrevC yA2) (mulF t (mulF t pStep2 yA2) yD2))
        let cEnd := mulF t (mulF t chiLast yC) cStep
        let c9 := addF cEnd (mulF t (mulF t chiD yA1) (addF oneF (mulF t zLast1 yD1)))
        let c10 := addF cEnd (mulF t (mulF t chiD yA2) (addF oneF (mulF t zLast2 yD2)))
        (c5, c6, c7, c8, c9, c10)
  let witBatch := evalHornerF t #[e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10] β
  let witTerm := mulF t (addF oneF xdVal) witBatch
  let maskLin := mulF t ρLin yMlin
  let maskQuad := mulF t (addF (mulF t x0Val x0Val) x0Val) (mulF t yUA yUB)
  addF witTerm (addF maskLin maskQuad)

/-- Expand deterministic CSPRNG randomness from a 32-byte seed for reproducible conformance vectors. -/
def expandSeedC8 (custStr : String) (seed : Nat) (count : Nat) : Array C8 := Id.run do
  let cust := 0x20 :: Tower256ConcreteBackend.utf8 custStr
  let mut out : Array C8 := Array.mkEmpty count
  for i in [0:count] do
    let d := cshakeC.xofDigest cust (natCoordBytes seed ++ natCoordBytes i)
    out := out.push (digestTowerC d)
  return out

end FastProver

/-- **Executable Honest Algebraic Prover (`proveAlgebraic`)**:
builds all 16 half-cube-masked / HVZK polynomials over `Tower256`, commits `contentRoot`,
`phase1Root`, `multRoot`, `phase3Root`, runs the `(d + 1)`-round degree-`≤ 4` sumcheck, runs
`Tower256SuccinctCheck`-compatible coset FRI (`offset = cosetOffset ell`, `finalDegree = 1`),
and extracts all `friQueries` coherent coset + `evalFold` pair openings! -/
def proveAlgebraic (dfa : DfaTable) (w : List UInt8) (claim : ClaimData)
    (seed : Nat) (cubeDim friEll friQueries : Nat) :
    Option (AlgebraicContentCert × AlgebraicPrivateReceipt friEll (cubeDim + 1) friQueries) := Id.run do
  let d := cubeDim
  let friRounds := d + 1
  if hm : friRounds ≤ friEll then
    if hell24 : friEll ≤ 24 then
      let hell : friEll ≤ 256 := le_trans hell24 (by norm_num)
      if w.isEmpty || !(2 ≤ d && d ≤ 22 && d + 2 ≤ friEll) ||
          !(w.length ≤ 2 ^ d) || !(dfa.states * 256 ≤ 2 ^ d) ||
          !(1 ≤ friQueries && friQueries ≤ 4096) ||
          !Dfaops.satisfiesClaim dfa claim w then
        return none
      let tbl := FastProver.mkTables
      let zeroF := FastProver.zeroF
      let oneF := FastProver.oneF
      let addF := FastProver.addF
      let mulF := FastProver.mulF tbl
      let powF := FastProver.powF tbl
      let invF := FastProver.invF tbl
      let zetaFast := FastProver.ofC8 zetaC
      let zetaInvFast := FastProver.ofC8 zetaInvC
      let nHalf := 2 ^ d
      let nFull := 2 ^ (d + 1)
      let L := w.length
      let mTab := dfa.states * 256
      let pivs := FastProver.computePivotsF tbl friEll (d + 1)
      let pivInvs := pivs.map invF

      -- 1. Content column (`col 0`)
      let contentMaskC := FastProver.expandSeedC8 "MINIDREGG/ALGCERT/CMASK/V1" seed nHalf
      let mut col0 := Array.mkArray nFull zeroF
      let wArr := w.toArray
      for i in [0:L] do
        col0 := col0.set! i (FastProver.ofU64 wArr[i]!.toUInt64)
      for i in [0:nHalf] do
        col0 := col0.set! (nHalf + i) (FastProver.ofC8 contentMaskC[i]!)
      let coset0 := FastProver.cosetEncodeF tbl friEll (d + 1) pivs pivInvs col0
      let cTree := buildFastCubeTree friEll (coset0.map FastProver.toC8)
      let cRoot := cTree.root

      -- 2. Phase-1 columns (`cols 1..8`: `state, next, hit, cntPow, accLo, bitLo, accHi, bitHi`)
      let p1Masks := FastProver.expandSeedC8 "MINIDREGG/ALGCERT/P1MASK/V1" seed (8 * nHalf)
      let mut p1Tabs : Array (Array F256) := Array.mkArray 8 (Array.mkArray nFull zeroF)
      for c in [0:8] do
        let mut arr := p1Tabs[c]!
        for i in [0:nHalf] do
          arr := arr.set! (nHalf + i) (FastProver.ofC8 p1Masks[c * nHalf + i]!)
        p1Tabs := p1Tabs.set! c arr

      let deltaArr := dfa.delta.toArray
      let accArr := dfa.accepting.toArray
      let mut curS := dfa.initial
      let mut curCC : Nat := 0
      let mut curCntPow := oneF
      let mut rowKeys : Array Nat := Array.mkEmpty L
      for i in [0:L] do
        let bNat := wArr[i]!.toNat
        let key := 256 * curS + bNat
        rowKeys := rowKeys.push key
        let nx := deltaArr.getD key 0
        let hit := if accArr.getD nx false then 1 else 0
        p1Tabs := p1Tabs.set! 0 (p1Tabs[0]!.set! i (FastProver.ofU64 curS.toUInt64))
        p1Tabs := p1Tabs.set! 1 (p1Tabs[1]!.set! i (FastProver.ofU64 nx.toUInt64))
        p1Tabs := p1Tabs.set! 2 (p1Tabs[2]!.set! i (FastProver.ofU64 hit.toUInt64))
        p1Tabs := p1Tabs.set! 3 (p1Tabs[3]!.set! i curCntPow)
        curCC := curCC + hit
        if hit == 1 then curCntPow := mulF curCntPow zetaFast
        curS := nx

      match claim with
      | .bound lo hi =>
          let hiCap := Nat.min hi L
          let d1 := curCC - lo
          let d2 := hiCap - curCC
          let mut a1 := powF zetaFast lo
          let mut a2 := powF zetaFast hiCap
          let mut z1 := zetaFast
          let mut z2 := zetaInvFast
          for k in [0:d + 1] do
            let b1 := d1.testBit k
            let b2 := d2.testBit k
            p1Tabs := p1Tabs.set! 4 (p1Tabs[4]!.set! k a1)
            p1Tabs := p1Tabs.set! 5 (p1Tabs[5]!.set! k (if b1 then oneF else zeroF))
            p1Tabs := p1Tabs.set! 6 (p1Tabs[6]!.set! k a2)
            p1Tabs := p1Tabs.set! 7 (p1Tabs[7]!.set! k (if b2 then oneF else zeroF))
            if b1 then a1 := mulF a1 z1
            if b2 then a2 := mulF a2 z2
            z1 := mulF z1 z1
            z2 := mulF z2 z2
      | _ => pure ()

      let p1Cosets : Array (Array F256) := p1Tabs.map (FastProver.cosetEncodeF tbl friEll (d + 1) pivs pivInvs)
      let p1CosetsC : Array (Array C8) := p1Cosets.map (fun w => w.map FastProver.toC8)
      let cosetLen := 2 ^ friEll
      let p1Leaves : Array C8 := Array.ofFn fun idx : Fin cosetLen =>
        vecLeafC algPhase1LeafCust ((List.range 8).map fun c => (p1CosetsC[c]!)[idx.val]!)
      let p1Tree := buildFastCubeTree friEll p1Leaves
      let p1Root := p1Tree.root

      let stmt : AlgebraicContentCert :=
        { contentRoot := cRoot
          recordLength := L
          automatonRoot := automatonCommit dfa
          claim := claim
          cubeDim := d
          friEll := friEll
          friQueries := friQueries }

      -- 3. Round-1 challenges (`α`, `θ`) + Phase-2 multiplicity column (`col 9`)
      let r1Bytes := algRound1Transcript stmt p1Root
      let αC := deriveChalAt algRound1ChalCust r1Bytes 0
      let θC := deriveChalAt algRound1ChalCust r1Bytes 1
      let α := FastProver.ofC8 αC
      let θ := FastProver.ofC8 θC

      let mMask := FastProver.expandSeedC8 "MINIDREGG/ALGCERT/MMASK/V1" seed nHalf
      let mut mTabCol := Array.mkArray nFull zeroF
      let mut thPow := oneF
      for i in [0:L] do
        let k := rowKeys[i]!
        mTabCol := mTabCol.set! k (addF mTabCol[k]! thPow)
        thPow := mulF thPow θ
      for i in [0:nHalf] do
        mTabCol := mTabCol.set! (nHalf + i) (FastProver.ofC8 mMask[i]!)
      let mCoset := FastProver.cosetEncodeF tbl friEll (d + 1) pivs pivInvs mTabCol
      let mCosetC := mCoset.map FastProver.toC8
      let mTree := buildFastCubeTree friEll mCosetC
      let mRoot := mTree.root

      -- 4. Round-2 challenge (`γ`) + Phase-3 columns (`cols 10..15`)
      let r2Bytes := algRound2Transcript stmt p1Root mRoot
      let γC := deriveChalAt algRound2ChalCust r2Bytes 0
      let γ := FastProver.ofC8 γC
      let α2 := mulF α α
      let α3 := mulF α2 α

      let mut trDenoms := Array.mkArray L oneF
      for i in [0:L] do
        let e := addF (addF col0[i]! (mulF α (p1Tabs[0]!)[i]!))
          (addF (mulF α2 (p1Tabs[1]!)[i]!) (mulF α3 (p1Tabs[2]!)[i]!))
        trDenoms := trDenoms.set! i (addF γ e)
      let trInvs := FastProver.batchInvF tbl trDenoms L

      let mut tabEncs := Array.mkArray mTab zeroF
      let mut tabDenoms := Array.mkArray mTab oneF
      for k in [0:mTab] do
        let s := k / 256
        let b := k % 256
        let nx := deltaArr.getD k 0
        let hit := if accArr.getD nx false then 1 else 0
        let tk := addF (addF (FastProver.ofU64 b.toUInt64) (mulF α (FastProver.ofU64 s.toUInt64)))
          (addF (mulF α2 (FastProver.ofU64 nx.toUInt64)) (mulF α3 (FastProver.ofU64 hit.toUInt64)))
        tabEncs := tabEncs.set! k tk
        tabDenoms := tabDenoms.set! k (addF γ tk)
      let tabInvs := FastProver.batchInvF tbl tabDenoms mTab

      let p3Rand := FastProver.expandSeedC8 "MINIDREGG/ALGCERT/P3MASK/V1" seed (2 * nHalf + 4 * nFull)
      let mut hCol := Array.mkArray nFull zeroF
      for i in [0:L] do hCol := hCol.set! i trInvs[i]!
      for i in [0:nHalf] do hCol := hCol.set! (nHalf + i) (FastProver.ofC8 p3Rand[i]!)

      let mut gCol := Array.mkArray nFull zeroF
      for k in [0:mTab] do gCol := gCol.set! k tabInvs[k]!
      for i in [0:nHalf] do gCol := gCol.set! (nHalf + i) (FastProver.ofC8 p3Rand[nHalf + i]!)

      let offBase := 2 * nHalf
      -- `scMaskLin`: zero-sum over `{0, 1}^{d+1}` via top Möbius coefficient `c_{nFull - 1} = 0`!
      let mLinCoeffs : Array F256 := Array.ofFn fun idx : Fin nFull =>
        if idx.val + 1 == nFull then zeroF else FastProver.ofC8 p3Rand[offBase + idx.val]!
      -- Evaluate `mLin` on `{0, 1}^{d+1}` (Boolean Möbius is an involution in char 2!)
      let mLinTab := FastProver.mobiusF (d + 1) mLinCoeffs
      let uATab : Array F256 := Array.ofFn fun idx : Fin nFull =>
        FastProver.ofC8 p3Rand[offBase + nFull + idx.val]!
      let uBTab : Array F256 := Array.ofFn fun idx : Fin nFull =>
        FastProver.ofC8 p3Rand[offBase + 2 * nFull + idx.val]!
      let friMaskCoeffs : Array F256 := Array.ofFn fun idx : Fin nFull =>
        FastProver.ofC8 p3Rand[offBase + 3 * nFull + idx.val]!

      let p3Tabs : Array (Array F256) := #[hCol, gCol, mLinTab, uATab, uBTab]
      let p3Cosets04 := p3Tabs.map (FastProver.cosetEncodeF tbl friEll (d + 1) pivs pivInvs)
      let friMaskCoset := FastProver.cosetFromCoeffsF tbl friEll (d + 1) pivs pivInvs friMaskCoeffs
      let p3Cosets := p3Cosets04.push friMaskCoset
      let p3CosetsC := p3Cosets.map (fun w => w.map FastProver.toC8)
      let p3Leaves : Array C8 := Array.ofFn fun idx : Fin cosetLen =>
        vecLeafC algPhase3LeafCust ((List.range 6).map fun c => (p3CosetsC[c]!)[idx.val]!)
      let p3Tree := buildFastCubeTree friEll p3Leaves
      let p3Root := p3Tree.root

      -- 5. Round-3 challenges (`β, τ_s, τ_c, τ_d, ρ_lin`) & linear-time `(d + 1)`-round Sumcheck!
      let r3Bytes := algRound3Transcript stmt p1Root mRoot p3Root
      let β := FastProver.ofC8 (deriveChalAt algRound3ChalCust r3Bytes 0)
      let τS := FastProver.ofC8 (deriveChalAt algRound3ChalCust r3Bytes 1)
      let τC := FastProver.ofC8 (deriveChalAt algRound3ChalCust r3Bytes 2)
      let τD := FastProver.ofC8 (deriveChalAt algRound3ChalCust r3Bytes 3)
      let ρLin := FastProver.ofC8 (deriveChalAt algRound3ChalCust r3Bytes 4)

      -- Assemble the 15 witness/mask tables (`cols 0..14`, each length `nFull`)
      let mut curCols : Array (Array F256) :=
        #[col0, p1Tabs[0]!, p1Tabs[1]!, p1Tabs[2]!, p1Tabs[3]!, p1Tabs[4]!, p1Tabs[5]!,
          p1Tabs[6]!, p1Tabs[7]!, mTabCol, hCol, gCol, mLinTab, uATab, uBTab]

      -- Assemble the 17 public weight tables on `{0, 1}^d` (each length `nHalf`)
      let mkPowPrefix (bound : Nat) (base : F256) (scale : F256) : Array F256 := Id.run do
        let mut arr := Array.mkArray nHalf zeroF
        let mut p := scale
        for i in [0:bound] do
          arr := arr.set! i p
          p := mulF p base
        return arr
      let pub0 := (Array.mkArray nHalf zeroF).set! 0 oneF
      let pubLast := (Array.mkArray nHalf zeroF).set! (L - 1) oneF
      let pubD := (Array.mkArray nHalf zeroF).set! d oneF
      let pubLtS := mkPowPrefix L τS oneF
      let pubLm1S := mkPowPrefix (L - 1) τS τS
      let pubLtC := mkPowPrefix L τC oneF
      let pubLm1C := mkPowPrefix (L - 1) τC τC
      let pubLtD := mkPowPrefix L τD oneF
      let pubTabD := mkPowPrefix mTab τD oneF
      let pubLtTheta := mkPowPrefix L θ oneF
      let pubTabOne := mkPowPrefix mTab oneF oneF
      let mut pubTabGammaD := Array.mkArray nHalf zeroF
      let mut tdCur := oneF
      for k in [0:mTab] do
        pubTabGammaD := pubTabGammaD.set! k (mulF tdCur tabDenoms[k]!)
        tdCur := mulF tdCur τD

      let isBound := match claim with | .bound _ _ => true | _ => false
      let pubBitD := if isBound then mkPowPrefix (d + 1) τD oneF else Array.mkArray nHalf zeroF
      let pubBitC := if isBound then mkPowPrefix (d + 1) τC oneF else Array.mkArray nHalf zeroF
      let pubBitPrevC := if isBound then mkPowPrefix d τC τC else Array.mkArray nHalf zeroF
      let mut pubStep1 := Array.mkArray nHalf zeroF
      let mut pubStep2 := Array.mkArray nHalf zeroF
      if isBound then
        let mut tcCur := τC
        let mut z1 := zetaFast
        let mut z2 := zetaInvFast
        for k in [0:d] do
          pubStep1 := pubStep1.set! k (mulF tcCur (addF oneF z1))
          pubStep2 := pubStep2.set! k (mulF tcCur (addF oneF z2))
          tcCur := mulF tcCur τC
          z1 := mulF z1 z1
          z2 := mulF z2 z2

      let mut pubTabs : Array (Array F256) :=
        #[pub0, pubLast, pubD, pubLtS, pubLm1S, pubLtC, pubLm1C, pubLtD,
          pubTabGammaD, pubTabD, pubLtTheta, pubTabOne,
          pubBitD, pubBitC, pubBitPrevC, pubStep1, pubStep2]

      let pts5 : Array F256 := #[zeroF, oneF, FastProver.ofU64 2, FastProver.ofU64 3, FastProver.ofU64 4]
      let initF := FastProver.ofU64 dfa.initial.toUInt64
      let mut scPolys : Array PolyDeg4 := #[]
      let mut rFullC : Array C8 := #[]
      let mut rFullF : Array F256 := #[]
      let mut scTr := r3Bytes

      -- Rounds `0 .. d - 1` (folding `{0, 1}^d` coordinates; `x_d ∈ {0, 1}` summed explicitly!)
      for j in [0:d] do
        let halfCube := 2 ^ (d - 1 - j)
        let mut evals5 := Array.mkArray 5 zeroF
        for pIdx in [0:5] do
          let tPt := pts5[pIdx]!
          let x0Pt := if j == 0 then tPt else rFullF[0]!
          let mut sumPt := zeroF
          for tail in [0:halfCube] do
            let idx0 := 2 * tail
            let idx1 := 2 * tail + 1
            let lineAt (arr : Array F256) (base : Nat) : F256 :=
              let v0 := arr[base]!
              let v1 := arr[base + 1]!
              addF v0 (mulF tPt (addF v0 v1))
            -- `x_d = 0` half: full witness + HVZK mask
            let ys0 : Array F256 := curCols.map fun arr => lineAt arr idx0
            let ps : Array F256 := pubTabs.map fun arr => lineAt arr idx0
            let vHalf0 := FastProver.evalPhiFast tbl claim L d initF zetaFast zetaInvFast
              α γ β ρLin x0Pt zeroF
              ps[0]! ps[1]! ps[2]! ps[3]! ps[4]! ps[5]! ps[6]! ps[7]! ps[8]! ps[9]! ps[10]! ps[11]!
              ps[12]! ps[13]! ps[14]! ps[15]! ps[16]! ys0
            -- `x_d = 1` half: `1 + x_d = 0`, only HVZK mask (`cols 12, 13, 14`) contributes!
            let baseHi := 2 * halfCube + idx0
            let mLin1 := lineAt curCols[12]! baseHi
            let uA1 := lineAt curCols[13]! baseHi
            let uB1 := lineAt curCols[14]! baseHi
            let vHalf1 := addF (mulF ρLin mLin1)
              (mulF (addF (mulF x0Pt x0Pt) x0Pt) (mulF uA1 uB1))
            sumPt := addF sumPt (addF vHalf0 vHalf1)
          evals5 := evals5.set! pIdx sumPt
        let poly := FastProver.interpolateDeg4F tbl evals5
        scPolys := scPolys.push poly
        scTr := scTr ++ envelope (natCoordBytes j) ++ envelope poly.encodeBytes
        let rjC := digestTowerC (cshakeC.xofDigest algSumcheckChalCust scTr)
        let rjF := FastProver.ofC8 rjC
        rFullC := rFullC.push rjC
        rFullF := rFullF.push rjF
        -- Fold `curCols` (size `4 * halfCube -> 2 * halfCube`) and `pubTabs` (`2 * halfCube -> halfCube`)
        curCols := curCols.map fun arr =>
          Array.ofFn fun tail : Fin (2 * halfCube) =>
            let v0 := arr[2 * tail.val]!
            let v1 := arr[2 * tail.val + 1]!
            addF v0 (mulF rjF (addF v0 v1))
        pubTabs := pubTabs.map fun arr =>
          Array.ofFn fun tail : Fin halfCube =>
            let v0 := arr[2 * tail.val]!
            let v1 := arr[2 * tail.val + 1]!
            addF v0 (mulF rjF (addF v0 v1))

      -- Round `d` (final sumcheck round over `x_d`: `pubTabs` have size `1`, `curCols` have size `2`!)
      let psFinal := pubTabs.map fun arr => arr[0]!
      let x0Fixed := rFullF[0]!
      let mut evalsLast := Array.mkArray 5 zeroF
      for pIdx in [0:5] do
        let tPt := pts5[pIdx]!
        let ysPt := curCols.map fun arr =>
          let v0 := arr[0]!
          let v1 := arr[1]!
          addF v0 (mulF tPt (addF v0 v1))
        let val := FastProver.evalPhiFast tbl claim L d initF zetaFast zetaInvFast
          α γ β ρLin x0Fixed tPt
          psFinal[0]! psFinal[1]! psFinal[2]! psFinal[3]! psFinal[4]! psFinal[5]! psFinal[6]!
          psFinal[7]! psFinal[8]! psFinal[9]! psFinal[10]! psFinal[11]!
          psFinal[12]! psFinal[13]! psFinal[14]! psFinal[15]! psFinal[16]! ysPt
        evalsLast := evalsLast.set! pIdx val
      let polyLast := FastProver.interpolateDeg4F tbl evalsLast
      scPolys := scPolys.push polyLast
      scTr := scTr ++ envelope (natCoordBytes d) ++ envelope polyLast.encodeBytes
      let rdC := digestTowerC (cshakeC.xofDigest algSumcheckChalCust scTr)
      if rdC == Coordinate.zero 8 || rdC == Coordinate.one 8 then return none
      let rdF := FastProver.ofC8 rdC
      rFullC := rFullC.push rdC
      rFullF := rFullF.push rdF

      -- Fold `curCols` one final time at `rdF` to obtain `colEvalsAtR` (`15` `C8`s)!
      let colEvalsF : Array F256 := curCols.map fun arr =>
        addF arr[0]! (mulF rdF (addF arr[0]! arr[1]!))
      let colEvalsC : Array C8 := colEvalsF.map FastProver.toC8

      -- 6. Batching challenges (`η`, `ρ`), `evalFold` trees (`j = 1 .. d`), & `F_fri`!
      let batchBytes := algBatchTranscript r3Bytes scPolys colEvalsC
      let η := FastProver.ofC8 (deriveChalAt algBatchChalCust batchBytes 0)
      let ρ := FastProver.ofC8 (deriveChalAt algBatchChalCust batchBytes 1)

      let all15Cosets : Array (Array F256) :=
        #[coset0, p1Cosets[0]!, p1Cosets[1]!, p1Cosets[2]!, p1Cosets[3]!,
          p1Cosets[4]!, p1Cosets[5]!, p1Cosets[6]!, p1Cosets[7]!,
          mCoset, p3Cosets[0]!, p3Cosets[1]!, p3Cosets[2]!, p3Cosets[3]!, p3Cosets[4]!]

      let mut hCur : Array F256 := Array.ofFn fun idx : Fin cosetLen =>
        FastProver.evalHornerF tbl (all15Cosets.map fun col => col[idx.val]!) η
      let mut evalWordsC : Array (Array C8) := #[]
      let mut evalTrees : Array FastCubeTree := #[]
      let mut evalRoots : Array Digest := #[]
      for j in [0:d] do
        let halfJ := 2 ^ (friEll - j - 1)
        let domLo := FastProver.tabulateCosetDomF tbl friEll j pivs
        let pivJ := pivs[j]!
        let pinvJ := pivInvs[j]!
        let alphaJ := mulF pivJ rFullF[j]!
        let prev := hCur
        hCur := Array.ofFn fun k : Fin halfJ =>
          let lo := prev[k.val]!
          let hi := prev[k.val + halfJ]!
          addF lo (mulF (mulF (addF domLo[k.val]! alphaJ) (addF lo hi)) pinvJ)
        let wC := hCur.map FastProver.toC8
        let tr := buildFastCubeTree (friEll - (j + 1)) wC
        evalWordsC := evalWordsC.push wC
        evalTrees := evalTrees.push tr
        evalRoots := evalRoots.push tr.root

      -- Build `F_fri` (`word0`) and run `(d + 1)`-round coset FRI (`finalDegree = 1`)!
      let friWord0F : Array F256 := Array.ofFn fun idx : Fin cosetLen =>
        let batchRho := FastProver.evalHornerF tbl (all15Cosets.map fun col => col[idx.val]!) ρ
        addF friMaskCoset[idx.val]! (mulF ρ batchRho)
      let friWord0C := friWord0F.map FastProver.toC8
      let friTree0 := buildFastCubeTree friEll friWord0C
      let friRoot0 := friTree0.root

      let sFri := algFriStatementOf stmt friRoot0 hm hell
      let pins := algFriPins batchBytes evalRoots
      let zeroSeeds : Fin friQueries → PowerTwoFriLevels friEll 1 := fun _ => ⟨0, by positivity⟩
      let mut friWordsF : Array (Array F256) := #[friWord0F]
      let mut friWordsC : Array (Array C8) := #[friWord0C]
      let mut friTrees : Array FastCubeTree := #[friTree0]
      let mut friRoots : Array Digest := #[friRoot0]
      let mut friChalsC : Array C8 := #[]

      for hj : j in [0:friRounds] do
        let jm : Fin friRounds := ⟨j, hj.upper⟩
        let stub := Tower256SuccinctProver.stubReceipt friRoots friChalsC [] zeroSeeds
        let alphaC := challengeC sFri pins stub jm
        let alphaF := FastProver.ofC8 alphaC
        let halfJ := 2 ^ (friEll - j - 1)
        let domLo := FastProver.tabulateCosetDomF tbl friEll j pivs
        let pinvJ := pivInvs[j]!
        let prev := friWordsF[j]!
        let nextF : Array F256 := Array.ofFn fun k : Fin halfJ =>
          let lo := prev[k.val]!
          let hi := prev[k.val + halfJ]!
          addF lo (mulF (mulF (addF domLo[k.val]! alphaF) (addF lo hi)) pinvJ)
        let nextC := nextF.map FastProver.toC8
        friChalsC := friChalsC.push alphaC
        friWordsF := friWordsF.push nextF
        friWordsC := friWordsC.push nextC
        if j + 1 < friRounds then
          let tr := buildFastCubeTree (friEll - (j + 1)) nextC
          friTrees := friTrees.push tr
          friRoots := friRoots.push tr.root

      let finalCoeffC : C8 := (friWordsC[friRounds]!)[0]!
      let finalCoeffs : List C8 := [finalCoeffC]
      let lastSize := 2 ^ (friEll - friRounds)
      let lastTree := buildFastCubeTree (friEll - friRounds) (Array.mkArray lastSize finalCoeffC)
      friRoots := friRoots.push lastTree.root
      let stubSeeds := Tower256SuccinctProver.stubReceipt friRoots friChalsC finalCoeffs zeroSeeds
      let mid := queryMidstate sFri pins stubSeeds
      let seeds := fun a : Fin friQueries => seedOfMidstate mid a
      let friOpening := fun (j : Fin friRounds) (a : Fin friQueries) =>
        let wC := friWordsC[j.val]!
        let tr := friTrees[j.val]!
        let halfJ := 2 ^ (friEll - j.val - 1)
        let k := (seeds a).val % halfJ
        ({ left := wC[k]!
           right := wC[k + halfJ]!
           pairPath := (tr.path k).dropLast } : CPairOpening)
      let friRec : CReceipt friEll friRounds friQueries :=
        { roots := fun n => friRoots.getD n.val ⟨0⟩
          challenges := fun j => friChalsC.getD j.val (Coordinate.zero 8)
          querySeed := seeds
          opening := friOpening
          finalCoeffs := finalCoeffs }

      -- 7. Extract coherent level-0 coset pair openings & `evalFold` pair openings!
      let half0 := 2 ^ (friEll - 1)
      let coset0C := coset0.map FastProver.toC8
      let cOps : Array CPairOpening := Array.ofFn fun a : Fin friQueries =>
        let k0 := (seeds a).val % half0
        { left := coset0C[k0]!, right := coset0C[k0 + half0]!, pairPath := (cTree.path k0).dropLast }
      let p1Ops : Array Phase1PairOpening := Array.ofFn fun a : Fin friQueries =>
        let k0 := (seeds a).val % half0
        { leftCols := Array.ofFn fun c : Fin 8 => (p1CosetsC[c.val]!)[k0]!
          rightCols := Array.ofFn fun c : Fin 8 => (p1CosetsC[c.val]!)[k0 + half0]!
          pairPath := (p1Tree.path k0).dropLast }
      let mOps : Array CPairOpening := Array.ofFn fun a : Fin friQueries =>
        let k0 := (seeds a).val % half0
        { left := mCosetC[k0]!, right := mCosetC[k0 + half0]!, pairPath := (mTree.path k0).dropLast }
      let p3Ops : Array Phase3PairOpening := Array.ofFn fun a : Fin friQueries =>
        let k0 := (seeds a).val % half0
        { leftCols := Array.ofFn fun c : Fin 6 => (p3CosetsC[c.val]!)[k0]!
          rightCols := Array.ofFn fun c : Fin 6 => (p3CosetsC[c.val]!)[k0 + half0]!
          pairPath := (p3Tree.path k0).dropLast }
      let efOps : Array (Array CPairOpening) := Array.ofFn fun j : Fin d =>
        let wC := evalWordsC[j.val]!
        let tr := evalTrees[j.val]!
        let halfNext := 2 ^ (friEll - (j.val + 1) - 1)
        Array.ofFn fun a : Fin friQueries =>
          let kj := (seeds a).val % halfNext
          { left := wC[kj]!, right := wC[kj + halfNext]!, pairPath := (tr.path kj).dropLast }

      let receipt : AlgebraicPrivateReceipt friEll friRounds friQueries :=
        { dfa := dfa
          phase1Root := p1Root
          multRoot := mRoot
          phase3Root := p3Root
          sumcheckPolys := scPolys
          colEvalsAtR := colEvalsC
          evalFoldRoots := evalRoots
          friInitialRoot := friRoot0
          friReceipt := friRec
          contentOps := cOps
          phase1Ops := p1Ops
          multOps := mOps
          phase3Ops := p3Ops
          evalFoldOps := efOps }
      return some (stmt, receipt)
    else return none
  else return none

/-! ## §7. Axiom Pins (`#guard_msgs` + `#print axioms`) -/

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.orderOf_zetaF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderOf_zetaF

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.zetaF_pow_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zetaF_pow_injOn

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.zero_position_disclosure_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_position_disclosure_hiding

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.zero_position_disclosure_uniform_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_position_disclosure_uniform_prob

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.coset_theta_last_not_boolean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coset_theta_last_not_boolean

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.maskedContentRoot_eq_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskedContentRoot_eq_or_collision

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.gamma_pole_guard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gamma_pole_guard

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.algebraicRowValid_iff_dfaRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms algebraicRowValid_iff_dfaRun

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.algebraicStepCheck_iff_dfaRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms algebraicStepCheck_iff_dfaRun

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.logup_stage_prob_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms logup_stage_prob_bounds

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.forged_transition_nonzero_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forged_transition_nonzero_polynomial

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.char_two_unweighted_parity_trap_tooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms char_two_unweighted_parity_trap_tooth

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.algebraic_escape_prob_lt_two_pow_neg_230' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms algebraic_escape_prob_lt_two_pow_neg_230

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.checkAlgebraic_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkAlgebraic_sound_or_collision

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCert.checkAlgebraic_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkAlgebraic_premises_inhabited

end Minidregg.Compiler.Tower256AlgebraicCert
