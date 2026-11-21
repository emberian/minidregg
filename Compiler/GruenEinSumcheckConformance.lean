/-
# `Compiler/GruenEinSumcheckConformance.lean` — Gruen `{0, ∞}` Mode-2 `EinSumcheck` & E2M1 0-Mul Horner Conformance Seam

**Substrate, said out loud: this is a verified-side reference computation and algebraic bridge for
the native Rust seam (`prover/src/gruen_einsum.rs`).**

1. **Multi-Round BabyBear `EinSumcheck` Mode-2 Vector (`μL = 1, μR = 1, μS = 3, κ = 2` -> `5` rounds):**
   Instantiates `Assurance/ZkmlEinSumcheck.lean` (`einsumTable`, `mle₃`, `einsumTrue`,
   `einsumLeftTable`, `einsumRightTable`) and `Assurance/ZkmlGruenSumcheck.lean` (`eqLinPoly`,
   `quadFromZeroOneInf`, `gruen_q1_unique_of_r_ne_zero`, `gruen_r_zero_q1_unconstrained`,
   `gruen_phase_splice_double_strip_tooth`) over `BabyBear` (`p = 2013265921`) WITH an interior
   `F_{≥2}` round where `z_1 = 0` (`ePrint 2024/108` fn. 23 deterministic `q(1)` fallback!)
   alongside normal `z_0 ≠ 0` and `z_2 ≠ 0` rounds and `2` `S`-phase rounds.
   - Proves `mle_foldLsb` (connecting `O(2^m)` table folding directly to `Selvage.mle`) and
     `roundQuotient_eq_quadFromZeroOneInf` (connecting `{q(0), q(1), q(∞)}` reconstruction to the
     quotient sum over any `CommRing`).
   - Kernel-decides (`by decide`) every round's `(q(0), q(1), q(∞), q(2))`, Mode-2 stripped claims
     `σ_{i+1} = q_i(c_i)`, the `F_{≥2} -> S` transition claim `σ_3` (with Jolt `#1474`
     no-double-strip tooth instantiated on the vector!), and the factored terminal openings.

2. **Type-Enforced Zero-Multiplication 7-Bucket E2M1 Horner (`e2m1Horner_eq_dot`):**
   Defines `e2m1Horner` over `[AddCommGroup R]` (no `Mul R` instance in scope — type-level proof of
   zero multiplications!) and proves over any `[CommRing R]` that the 7-bucket 4-bit-plane Horner
   addition chain equals `∑ i, e2m1Decode (q i) * v i`, kernel-deciding a 32-element BabyBear
   vector covering all 16 4-bit E2M1 nibbles.

Emits `prover/testdata/gruen_einsumcheck_conformance.json` via `#eval`; Lean is the sole author.
-/
import Assurance.ZkmlGruenSumcheck
import Compiler.SumcheckConformance

namespace Minidregg.Compiler

open Minidregg.Selvage Minidregg.Assurance Minidregg.Assurance.ZkmlGruenSumcheck Polynomial
open Lean (Json ToJson toJson)

/-! ## §1. Table-Folding Bridge (`foldLsb`) & Gruen `{0, ∞}` Quotient Parametrization -/

section FoldingBridge

/-- Bind the LSB coordinate of an `(m + 1)`-variable hypercube table at `r`. -/
def foldLsb {R : Type*} [CommRing R] {m : ℕ}
    (f : (Fin (m + 1) → Bool) → R) (r : R) : (Fin m → Bool) → R :=
  fun b => f (lsbCons false b) + r * (f (lsbCons true b) - f (lsbCons false b))

/-- **`O(2^m)` table folding agrees identically with `Selvage.mle` along `lsbCons`.** -/
theorem mle_foldLsb {F : Type} [Field F] {m : ℕ}
    (f : (Fin (m + 1) → Bool) → F) (r : F) (xs : Fin m → F) :
    mle (foldLsb f r) xs = mle f (lsbCons r xs) := by
  rw [mle_lsb_recurrence]
  simp only [foldLsb, mle, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, mul_assoc]

/-- Mode-2 degree-`≤ 2` round quotient `q(t)` from folded `(k + 1)`-variable operand tables `L, R`
weighted by suffix `eq` weights `sufW : (Fin k → Bool) → R`. -/
def roundQuotient {R : Type*} [CommRing R] {k : ℕ}
    (sufW : (Fin k → Bool) → R)
    (L R_tab : (Fin (k + 1) → Bool) → R) (t : R) : R :=
  ∑ b : Fin k → Bool, sufW b * (foldLsb L t b * foldLsb R_tab t b)

/-- Leading `X²` coefficient `q(∞)` of `roundQuotient` (`ΔL · ΔR` weighted by `sufW`). -/
def roundQuotientInf {R : Type*} [CommRing R] {k : ℕ}
    (sufW : (Fin k → Bool) → R)
    (L R_tab : (Fin (k + 1) → Bool) → R) : R :=
  ∑ b : Fin k → Bool,
    sufW b * ((L (lsbCons true b) - L (lsbCons false b))
                * (R_tab (lsbCons true b) - R_tab (lsbCons false b)))

/-- **Universal `{0, 1, ∞}` Reconstruction (`roundQuotient_eq_quadFromZeroOneInf`):**
Over ANY commutative ring `R`, `roundQuotient sufW L R_tab t` equals `quadFromZeroOneInf` evaluated
at `(q(0), q(1), q(∞))`. -/
theorem roundQuotient_eq_quadFromZeroOneInf {R : Type*} [CommRing R] {k : ℕ}
    (sufW : (Fin k → Bool) → R)
    (L R_tab : (Fin (k + 1) → Bool) → R) (t : R) :
    roundQuotient sufW L R_tab t =
      (quadFromZeroOneInf
        (roundQuotient sufW L R_tab 0)
        (roundQuotient sufW L R_tab 1)
        (roundQuotientInf sufW L R_tab)).eval t := by
  simp only [quadFromZeroOneInf, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    roundQuotient, roundQuotientInf, foldLsb]
  have h0 : ∀ b : Fin k → Bool,
      L (lsbCons false b) + 0 * (L (lsbCons true b) - L (lsbCons false b)) = L (lsbCons false b) :=
    fun _ => by ring
  simp only [ ← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **`eq`-Weighted Round-Sum Chain (`roundQuotient_gruen_sum`):**
Splitting the LSB coordinate of `eq` weight `(if b 0 then z else 1 - z) * sufW (tail b)` yields
`(eqLinPoly z).eval 0 * q(0) + (eqLinPoly z).eval 1 * q(1)`. -/
theorem roundQuotient_gruen_sum {R : Type*} [CommRing R] {k : ℕ}
    (z : R) (sufW : (Fin k → Bool) → R)
    (L R_tab : (Fin (k + 1) → Bool) → R) :
    (eqLinPoly z).eval 0 * roundQuotient sufW L R_tab 0 +
      (eqLinPoly z).eval 1 * roundQuotient sufW L R_tab 1 =
      ∑ b : Fin (k + 1) → Bool,
        ((if b 0 then z else 1 - z) * sufW (fun j => b j.succ)) * (L b * R_tab b) := by
  rw [← (lsbCubeEquiv k).symm.sum_comp
      (fun b : Fin (k + 1) → Bool =>
        ((if b 0 then z else 1 - z) * sufW (fun j => b j.succ)) * (L b * R_tab b)),
    Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, lsbCubeEquiv_symm_apply, lsbCons_zero, lsbCons_succ,
    eqLinPoly_eval_zero, eqLinPoly_eval_one, roundQuotient, foldLsb, ↓reduceIte,
    Bool.false_eq_true, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Evaluating `mle` on a 0-variable cube returns the unique corner `Fin.elim0`. -/
theorem mle_zero_vars {F : Type} [Field F] (f : (Fin 0 → Bool) → F) (x : Fin 0 → F) :
    mle f x = f Fin.elim0 := by
  rw [mle, Fintype.sum_eq_single Fin.elim0 fun b hb => absurd (Subsingleton.elim b Fin.elim0) hb]
  simp [chiEval]

/-- Five sequential `foldLsb` binds over any `[Field F]` evaluate `Selvage.mle` at `c : Fin 5 → F`. -/
theorem foldLsb5_eq_mle {F : Type} [Field F]
    (f : (Fin 5 → Bool) → F) (c : Fin 5 → F) :
    foldLsb (foldLsb (foldLsb (foldLsb (foldLsb f (c 0)) (c 1)) (c 2)) (c 3)) (c 4) Fin.elim0
      = mle f c := by
  let f5 := foldLsb (foldLsb (foldLsb (foldLsb (foldLsb f (c 0)) (c 1)) (c 2)) (c 3)) (c 4)
  change f5 Fin.elim0 = mle f c
  rw [← mle_zero_vars f5 Fin.elim0, mle_foldLsb, mle_foldLsb, mle_foldLsb, mle_foldLsb,
    mle_foldLsb]
  congr 1
  funext i; fin_cases i <;> rfl

end FoldingBridge

/-! ## §2. Type-Enforced Zero-Mul 7-Bucket E2M1 Horner Identity -/

section E2m1Horner

/-- Doubled OCP MXFP4 E2M1 magnitudes `{0, 1, 2, 3, 4, 6, 8, 12}` indexed by `0..7`. -/
def e2m1Mag : Fin 8 → ℤ := ![0, 1, 2, 3, 4, 6, 8, 12]

/-- Magnitude index `nib % 8` of a 4-bit E2M1 nibble `nib : Fin 16`. -/
def e2m1MagIdx (nib : Fin 16) : Fin 8 :=
  ⟨nib.val % 8, Nat.mod_lt _ (by decide)⟩

/-- Signed ring value of a 4-bit E2M1 nibble (`bit 3` = sign, `-0 = 0`). -/
def e2m1Decode {R : Type*} [Ring R] (nib : Fin 16) : R :=
  let m : R := (e2m1Mag (e2m1MagIdx nib) : R)
  if nib.val < 8 then m else -m

/-- Signed bucket sum for magnitude index `idx : Fin 8` using ONLY group `+` and `-`. -/
def e2m1Bucket {R : Type*} [AddCommGroup R] {n : ℕ}
    (q : Fin n → Fin 16) (v : Fin n → R) (idx : Fin 8) : R :=
  ∑ i : Fin n,
    if e2m1MagIdx (q i) = idx then
      (if (q i).val < 8 then v i else -v i)
    else 0

/-- Four bit-plane combinations `(C_8, C_4, C_2, C_1)` from the 7 nonzero magnitude buckets. -/
def e2m1Planes {R : Type*} [AddCommGroup R] {n : ℕ}
    (q : Fin n → Fin 16) (v : Fin n → R) : R × R × R × R :=
  let b1 := e2m1Bucket q v 1
  let b2 := e2m1Bucket q v 2
  let b3 := e2m1Bucket q v 3
  let b4 := e2m1Bucket q v 4
  let b6 := e2m1Bucket q v 5
  let b8 := e2m1Bucket q v 6
  let b12 := e2m1Bucket q v 7
  (b8 + b12, b4 + b6 + b12, b2 + b3 + b6, b1 + b3)

/-- **7-Bucket 0-Mul E2M1 Horner (`e2m1Horner`):**
Notice `[AddCommGroup R]` has NO multiplication instance — Lean's type system guarantees zero `*`! -/
def e2m1Horner {R : Type*} [AddCommGroup R] {n : ℕ}
    (q : Fin n → Fin 16) (v : Fin n → R) : R :=
  let (c8, c4, c2, c1) := e2m1Planes q v
  let d8 := c8 + c8 + c4
  let d4 := d8 + d8 + c2
  d4 + d4 + c1

/-- Single-element E2M1 bit-plane decomposition lemma across all 16 4-bit nibbles. -/
private theorem e2m1_single_horner_eq {R : Type*} [CommRing R] (nib : Fin 16) (x : R) :
    let bk := fun idx : Fin 8 =>
      if e2m1MagIdx nib = idx then (if nib.val < 8 then x else -x) else (0 : R)
    let c8 := bk 6 + bk 7
    let c4 := bk 4 + bk 5 + bk 7
    let c2 := bk 2 + bk 3 + bk 5
    let c1 := bk 1 + bk 3
    let d8 := c8 + c8 + c4
    let d4 := d8 + d8 + c2
    d4 + d4 + c1 = e2m1Decode nib * x := by
  fin_cases nib <;> simp [e2m1MagIdx, e2m1Decode, e2m1Mag] <;> ring

/-- **Zero-Mul E2M1 Horner Soundness (`e2m1Horner_eq_dot`):**
Over ANY commutative ring `R` and block length `n`, `e2m1Horner q v` equals the exact inner product
`∑ i, e2m1Decode (q i) * v i`. -/
theorem e2m1Horner_eq_dot {R : Type*} [CommRing R] {n : ℕ}
    (q : Fin n → Fin 16) (v : Fin n → R) :
    e2m1Horner q v = ∑ i : Fin n, e2m1Decode (q i) * v i := by
  simp only [e2m1Horner, e2m1Planes, e2m1Bucket, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact e2m1_single_horner_eq (q i) (v i)

end E2m1Horner

/-! ## §3. Fixed Multi-Round BabyBear `EinSumcheck` Instance (`z_1 = 0` Interior Fallback) -/

/-- Left operand `A` (`2 × 8 × 4` for `μL = 1, μS = 3, κ = 2`), asymmetric with `p - 1` edge entry. -/
def grTableA : List (List (List BabyBear)) :=
  [ [ [11, 23, 37, 41], [53, 67, 79, 83], [97, 101, 103, 107], [109, 113, 127, 131],
      [137, 139, 149, 151], [157, 163, 167, 173], [179, 181, 191, 193], [197, 199, 211, 2013265920] ],
    [ [223, 227, 229, 233], [239, 241, 251, 257], [263, 269, 271, 277], [281, 283, 293, 307],
      [311, 313, 317, 331], [337, 347, 349, 353], [359, 367, 373, 379], [383, 389, 397, 401] ] ]

/-- Right operand `B` (`2 × 8 × 4` for `μR = 1, μS = 3, κ = 2`), asymmetric with `p - 2` edge entry. -/
def grTableB : List (List (List BabyBear)) :=
  [ [ [17, 19, 29, 31], [43, 47, 59, 61], [71, 73, 89, 105], [115, 121, 133, 145],
      [155, 161, 175, 185], [195, 205, 215, 225], [235, 245, 255, 2013265919], [265, 275, 285, 295] ],
    [ [305, 315, 325, 335], [345, 355, 365, 375], [385, 395, 405, 415], [425, 435, 445, 455],
      [465, 475, 485, 495], [505, 515, 525, 535], [545, 555, 565, 575], [585, 595, 605, 615] ] ]

def grA : (Fin 1 → Bool) → (Fin 3 → Bool) → (Fin 2 → Bool) → BabyBear :=
  fun aL h q => ((grTableA.getD (bitsToIdx aL) []).getD (bitsToIdx h) []).getD (bitsToIdx q) 0

def grB : (Fin 1 → Bool) → (Fin 3 → Bool) → (Fin 2 → Bool) → BabyBear :=
  fun aR h q => ((grTableB.getD (bitsToIdx aR) []).getD (bitsToIdx h) []).getD (bitsToIdx q) 0

def grXL : Fin 1 → BabyBear := ![123456789]
def grXR : Fin 1 → BabyBear := ![987654321]

/-- Shared-free `F_{≥2}` outer challenges: note **interior coordinate `grZS 1 = 0`** (`2024/108` fn. 23)! -/
def grZS : Fin 3 → BabyBear := ![111111111, 0, 333333333]

/-- Five sumcheck round challenges (`3` `F_{≥2}` rounds followed by `2` `S` rounds). -/
def grChals : Fin 5 → BabyBear := ![222222222, 444444444, 555555555, 666666666, 777777777]

/-- Initial `(3 + 2)`-variable flattened operand tables from `Assurance/ZkmlEinSumcheck.lean`. -/
def grL0 : (Fin 5 → Bool) → BabyBear := einsumLeftTable grA grXL
def grR0 : (Fin 5 → Bool) → BabyBear := einsumRightTable grB grXR

/-- Folded operand states across rounds `0..5`. -/
def grL1 : (Fin 4 → Bool) → BabyBear := foldLsb grL0 (grChals 0)
def grR1 : (Fin 4 → Bool) → BabyBear := foldLsb grR0 (grChals 0)
def grL2 : (Fin 3 → Bool) → BabyBear := foldLsb grL1 (grChals 1)
def grR2 : (Fin 3 → Bool) → BabyBear := foldLsb grR1 (grChals 1)
def grL3 : (Fin 2 → Bool) → BabyBear := foldLsb grL2 (grChals 2)
def grR3 : (Fin 2 → Bool) → BabyBear := foldLsb grR2 (grChals 2)
def grL4 : (Fin 1 → Bool) → BabyBear := foldLsb grL3 (grChals 3)
def grR4 : (Fin 1 → Bool) → BabyBear := foldLsb grR3 (grChals 3)
def grL5 : (Fin 0 → Bool) → BabyBear := foldLsb grL4 (grChals 4)
def grR5 : (Fin 0 → Bool) → BabyBear := foldLsb grR4 (grChals 4)

/-- Suffix `eq` weight tables on remaining `F_{≥2}` coordinates (`1` on `S` coordinates). -/
def grSuf0 : (Fin 4 → Bool) → BabyBear :=
  fun b =>
    (if b 0 then grZS 1 else 1 - grZS 1) *
      (if b 1 then grZS 2 else 1 - grZS 2)

def grSuf1 : (Fin 3 → Bool) → BabyBear :=
  fun b => if b 0 then grZS 2 else 1 - grZS 2

def grSuf2 : (Fin 2 → Bool) → BabyBear := fun _ => 1
def grSuf3 : (Fin 1 → Bool) → BabyBear := fun _ => 1
def grSuf4 : (Fin 0 → Bool) → BabyBear := fun _ => 1

/-! ## §4. Instantiated Identities & Kernel-Decided (`by decide`) Reference Theorems -/

/-- The `EinSumcheck` hypercube claim equals `mle₃ (einsumTable grA grB)` (`einsum_claim_total`). -/
theorem grClaim_eq_mle3 :
    einsumTrue grA grB grXL grXR grZS = mle₃ (einsumTable grA grB) grXL grXR grZS :=
  einsum_claim_total grA grB grXL grXR grZS

/-- Interior `F_{≥2}` coordinate `z_1` is zero while `z_0, z_2` are nonzero. -/
theorem grZS_interior_zero :
    grZS 0 ≠ 0 ∧ grZS 1 = 0 ∧ grZS 2 ≠ 0 := by decide

/-- Claimed total `σ_0 = 1687038750`, kernel-decided. -/
theorem grClaim_value :
    mle₃ (einsumTable grA grB) grXL grXR grZS = 1687038750 := by decide

/-- Round 0 (`F_{≥2}`, `z_0 = 111111111 ≠ 0`): `(q₀(0), q₀(1), q₀(∞), q₀(2), σ₁)`. -/
theorem grRound0_values :
    (roundQuotient grSuf0 grL0 grR0 0,
     roundQuotient grSuf0 grL0 grR0 1,
     roundQuotientInf grSuf0 grL0 grR0,
     roundQuotient grSuf0 grL0 grR0 2,
     roundQuotient grSuf0 grL0 grR0 (grChals 0))
      = (1769740813, 976308615, 1000557340, 170725176, 6543634) := by decide

/-- Round 1 (`F_{≥2}` INTERIOR `z_1 = 0` fallback!): `q₁(0) = σ₁ = 6543634`, while `q₁(1) = 922178728`
must be sent explicitly because `ℓ_0(1) = 0`. -/
theorem grRound1_values :
    (roundQuotient grSuf1 grL1 grR1 0,
     roundQuotient grSuf1 grL1 grR1 1,
     roundQuotientInf grSuf1 grL1 grR1,
     roundQuotient grSuf1 grL1 grR1 2,
     roundQuotient grSuf1 grL1 grR1 (grChals 1))
      = (6543634, 922178728, 129022191, 82592283, 354127710) := by decide

/-- Round 2 (`F_{≥2} -> S` boundary, `z_2 = 333333333 ≠ 0`): `σ₃ = 1645677380` enters `S`-phase directly. -/
theorem grRound2_values :
    (roundQuotient grSuf2 grL2 grR2 0,
     roundQuotient grSuf2 grL2 grR2 1,
     roundQuotientInf grSuf2 grL2 grR2,
     roundQuotient grSuf2 grL2 grR2 2,
     roundQuotient grSuf2 grL2 grR2 (grChals 2))
      = (1012612582, 1626406527, 752297734, 1731530019, 1645677380) := by decide

/-- Round 3 (`S` phase round 0): `q₃(0) + q₃(1) = σ₃ = 1645677380` (no double-strip!). -/
theorem grRound3_values :
    (roundQuotient grSuf3 grL3 grR3 0,
     roundQuotient grSuf3 grL3 grR3 1,
     roundQuotientInf grSuf3 grL3 grR3,
     roundQuotient grSuf3 grL3 grR3 2,
     roundQuotient grSuf3 grL3 grR3 (grChals 3))
      = (1468320951, 177356429, 1804935298, 482996582, 758373012) := by decide

/-- Round 4 (`S` phase round 1 -> terminal): `σ₅ = 1935010981`. -/
theorem grRound4_values :
    (roundQuotient grSuf4 grL4 grR4 0,
     roundQuotient grSuf4 grL4 grR4 1,
     roundQuotientInf grSuf4 grL4 grR4,
     roundQuotient grSuf4 grL4 grR4 2,
     roundQuotient grSuf4 grL4 grR4 (grChals 4))
      = (1565640808, 1205998125, 169899280, 1186154002, 1935010981) := by decide

/-- Factored terminal openings `(Â(xL, c_S, c_κ), B̂(xR, c_S, c_κ))` and `eqMle z_S c_S`, decided. -/
theorem grTerminal_values :
    (grL5 Fin.elim0,
     grR5 Fin.elim0,
     grL5 Fin.elim0 * grR5 Fin.elim0,
     eqMle grZS (rowHalf 3 2 grChals))
      = (475473014, 1881988079, 1935010981, 108855645) := by decide

/-- Folded terminal values equal the full `Selvage.mle` evaluations (`mle grL0 grChals`, `mle grR0 grChals`). -/
theorem grTerminal_matches_mle :
    grL5 Fin.elim0 = mle grL0 grChals ∧ grR5 Fin.elim0 = mle grR0 grChals :=
  ⟨foldLsb5_eq_mle grL0 grChals, foldLsb5_eq_mle grR0 grChals⟩

/-- **Jolt PR `#1474` Double-Strip Tooth on the Conformance Vector:**
Instantiates `gruen_phase_splice_double_strip_tooth` at round 2 (`F_{≥2} -> S` transition):
dividing `σ₃ = 1645677380` by `ℓ_{z_2}(c_2)` a second time corrupts the Phase-2 entry claim. -/
theorem grPhaseSplice_no_double_strip :
    let q_val : BabyBear := roundQuotient grSuf2 grL2 grR2 (grChals 2)
    ((eqLinPoly (grZS 2)).eval (grChals 2))⁻¹ * q_val ≠ q_val :=
  (gruen_phase_splice_double_strip_tooth
    (r := grZS 2) (c := grChals 2)
    (q_val := roundQuotient grSuf2 grL2 grR2 (grChals 2))
    (by decide) (by rw [eqLinPoly_eval]; decide) (by rw [eqLinPoly_eval]; decide)).2

/-! ## §5. Concrete 32-Element E2M1 7-Bucket 0-Mul Horner Vector -/

def grHornerNibbles : Fin 32 → Fin 16 :=
  fun b => ⟨(b.val * 7 + 3) % 16, Nat.mod_lt _ (by decide)⟩

def grHornerVec : Fin 32 → BabyBear :=
  fun b => ((b.val + 1 : BabyBear) * 123456791 + 98765431 * (b.val : BabyBear) * (b.val : BabyBear))

/-- All 7 signed E2M1 buckets, 4 Horner bit-planes, and 0-mul dot product, kernel-decided. -/
theorem grE2m1Horner_values :
    ([e2m1Bucket grHornerNibbles grHornerVec 1,
      e2m1Bucket grHornerNibbles grHornerVec 2,
      e2m1Bucket grHornerNibbles grHornerVec 3,
      e2m1Bucket grHornerNibbles grHornerVec 4,
      e2m1Bucket grHornerNibbles grHornerVec 5,
      e2m1Bucket grHornerNibbles grHornerVec 6,
      e2m1Bucket grHornerNibbles grHornerVec 7],
     e2m1Planes grHornerNibbles grHornerVec,
     e2m1Horner grHornerNibbles grHornerVec)
      = ([82894439, 783143611, 364084260, 386552847, 479485203, 667742668, 198295382],
         (866038050, 1064333432, 1626713074, 446978699),
         793181528) := by decide

/-! ## §6. JSON Conformance Writer -/

private def mkRoundObj (phase : String) (zEq : BabyBear) (fallback : Bool)
    (q0 q1 qInf q2 nextSigma : BabyBear) : Json :=
  let wire := if fallback then [q0, qInf, q1] else [q0, qInf]
  Json.mkObj
    [ ("phase", Json.str phase),
      ("zEq", toJson zEq.val),
      ("zeroEqFallback", toJson fallback),
      ("q0", toJson q0.val),
      ("q1", toJson q1.val),
      ("qInf", toJson qInf.val),
      ("q2", toJson q2.val),
      ("wire", Json.arr (wire.map fun v => toJson v.val).toArray),
      ("nextSigma", toJson nextSigma.val) ]

private def idxToBits (m k : ℕ) : Fin m → Bool :=
  fun i => (k / 2 ^ (i : ℕ)) % 2 == 1

def gruenEinSumcheckConformanceJson : Json :=
  let zOutJson := Json.arr <|
    ((List.finRange 2).map fun al =>
      Json.arr <|
        ((List.finRange 2).map fun ar =>
          Json.arr <|
            ((List.finRange 8).map fun h =>
              toJson (einsumTable grA grB (idxToBits 1 al.val) (idxToBits 1 ar.val)
                (idxToBits 3 h.val)).val).toArray).toArray).toArray
  let roundsJson := Json.arr
    #[ mkRoundObj "f2" (grZS 0) false
         (roundQuotient grSuf0 grL0 grR0 0) (roundQuotient grSuf0 grL0 grR0 1)
         (roundQuotientInf grSuf0 grL0 grR0) (roundQuotient grSuf0 grL0 grR0 2)
         (roundQuotient grSuf0 grL0 grR0 (grChals 0)),
       mkRoundObj "f2" (grZS 1) true
         (roundQuotient grSuf1 grL1 grR1 0) (roundQuotient grSuf1 grL1 grR1 1)
         (roundQuotientInf grSuf1 grL1 grR1) (roundQuotient grSuf1 grL1 grR1 2)
         (roundQuotient grSuf1 grL1 grR1 (grChals 1)),
       mkRoundObj "f2" (grZS 2) false
         (roundQuotient grSuf2 grL2 grR2 0) (roundQuotient grSuf2 grL2 grR2 1)
         (roundQuotientInf grSuf2 grL2 grR2) (roundQuotient grSuf2 grL2 grR2 2)
         (roundQuotient grSuf2 grL2 grR2 (grChals 2)),
       mkRoundObj "s" 0 false
         (roundQuotient grSuf3 grL3 grR3 0) (roundQuotient grSuf3 grL3 grR3 1)
         (roundQuotientInf grSuf3 grL3 grR3) (roundQuotient grSuf3 grL3 grR3 2)
         (roundQuotient grSuf3 grL3 grR3 (grChals 3)),
       mkRoundObj "s" 0 false
         (roundQuotient grSuf4 grL4 grR4 0) (roundQuotient grSuf4 grL4 grR4 1)
         (roundQuotientInf grSuf4 grL4 grR4) (roundQuotient grSuf4 grL4 grR4 2)
         (roundQuotient grSuf4 grL4 grR4 (grChals 4)) ]
  let (c8, c4, c2, c1) := e2m1Planes grHornerNibbles grHornerVec
  let hornerJson := Json.mkObj
    [ ("nibbles", Json.arr ((List.finRange 32).map fun b => toJson (grHornerNibbles b).val).toArray),
      ("vec", finVecToJson grHornerVec),
      ("buckets", Json.arr
        (([1, 2, 3, 4, 5, 6, 7] : List (Fin 8)).map fun idx =>
          toJson (e2m1Bucket grHornerNibbles grHornerVec idx).val).toArray),
      ("planes", Json.arr #[toJson c8.val, toJson c4.val, toJson c2.val, toJson c1.val]),
      ("expectedDot", toJson (e2m1Horner grHornerNibbles grHornerVec).val) ]
  Json.mkObj
    [ ("p", toJson babyBearP),
      ("muL", toJson (1 : ℕ)),
      ("muR", toJson (1 : ℕ)),
      ("muS", toJson (3 : ℕ)),
      ("kappa", toJson (2 : ℕ)),
      ("tableA", Json.arr (grTableA.map fun m =>
        Json.arr (m.map fun r => Json.arr (r.map fun v => toJson v.val).toArray).toArray).toArray),
      ("tableB", Json.arr (grTableB.map fun m =>
        Json.arr (m.map fun r => Json.arr (r.map fun v => toJson v.val).toArray).toArray).toArray),
      ("xL", finVecToJson grXL),
      ("xR", finVecToJson grXR),
      ("zS", finVecToJson grZS),
      ("challenges", finVecToJson grChals),
      ("outputZ", zOutJson),
      ("claim", toJson (mle₃ (einsumTable grA grB) grXL grXR grZS).val),
      ("rounds", roundsJson),
      ("sPhaseEntryClaim", toJson (roundQuotient grSuf2 grL2 grR2 (grChals 2)).val),
      ("terminalOpenings", Json.arr #[toJson (grL5 Fin.elim0).val, toJson (grR5 Fin.elim0).val]),
      ("terminalProduct", toJson (grL5 Fin.elim0 * grR5 Fin.elim0).val),
      ("eqAtCS", toJson (eqMle grZS (rowHalf 3 2 grChals)).val),
      ("e2m1Horner", hornerJson) ]

def writeGruenEinSumcheckConformance (path : System.FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (gruenEinSumcheckConformanceJson.pretty ++ "\n")

#eval writeGruenEinSumcheckConformance "prover/testdata/gruen_einsumcheck_conformance.json"

/-! ## §7. Axiom Pins (`#guard_msgs`) -/

/-- info: 'Minidregg.Compiler.mle_foldLsb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mle_foldLsb
/-- info: 'Minidregg.Compiler.roundQuotient_eq_quadFromZeroOneInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundQuotient_eq_quadFromZeroOneInf
/-- info: 'Minidregg.Compiler.roundQuotient_gruen_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roundQuotient_gruen_sum
/-- info: 'Minidregg.Compiler.e2m1Horner_eq_dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms e2m1Horner_eq_dot
/-- info: 'Minidregg.Compiler.grClaim_eq_mle3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grClaim_eq_mle3
/-- info: 'Minidregg.Compiler.grZS_interior_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grZS_interior_zero
/-- info: 'Minidregg.Compiler.grClaim_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grClaim_value
/-- info: 'Minidregg.Compiler.grRound0_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grRound0_values
/-- info: 'Minidregg.Compiler.grRound1_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grRound1_values
/-- info: 'Minidregg.Compiler.grRound2_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grRound2_values
/-- info: 'Minidregg.Compiler.grRound3_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grRound3_values
/-- info: 'Minidregg.Compiler.grRound4_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grRound4_values
/-- info: 'Minidregg.Compiler.grTerminal_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grTerminal_values
/-- info: 'Minidregg.Compiler.grTerminal_matches_mle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grTerminal_matches_mle
/-- info: 'Minidregg.Compiler.grPhaseSplice_no_double_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grPhaseSplice_no_double_strip
/-- info: 'Minidregg.Compiler.grE2m1Horner_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grE2m1Horner_values

end Minidregg.Compiler
