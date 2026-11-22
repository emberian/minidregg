/-
# Selvage.GoldilocksDregg180Bridge — Streamed `< 16 KiB` `Dregg-180` `GoldilocksExt4` VM
# & Heterogeneous `BabyBear Ext4` + `Tower256` + `Simplex` Leaf Composition

1. `Goldilocks` (`p = 2^64 - 2^32 + 1`, `lucas_primality` at `7`, `0` `native_decide`),
   Kummer irreducibility of `X^4 - 7`, and `[1, v^2, v, v^3]` hardware limb isomorphism.
2. Bounded-register `< 16 KiB` `Dregg180VmState` (`OP_ABSORB_ROOT`, `OP_SUMCHECK_ROUND`,
   `OP_WHIR_FOLD`, `OP_CANOPY_PATH`, `OP_ASSERT_FINAL`) + `H_BIND_IDX` & `pdig` pinning.
3. Multi-leaf `ComposeErrorBoundStrict` (`err_total ≤ err_hem + ∑ err_leaf_i`) & `#tooth` suite.
-/
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime
import Selvage.BabyBearExt4
import Selvage.HeteroComposition
import Selvage.HeteroCompositionSuccinct
import Selvage.HeteroCompositionErrorBound

namespace Minidregg.Selvage.GoldilocksDregg180Bridge

open Polynomial AdjoinRoot Minidregg.Selvage

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1. Goldilocks (`p = 2^64 - 2^32 + 1`) & `GoldilocksExt4` (`X^4 - 7`) -/

def goldilocksModulus : ℕ := 18446744069414584321
def goldilocksHalfOrder : ℕ := 9223372034707292160

theorem goldilocksModulus_eq : goldilocksModulus = 2 ^ 64 - 2 ^ 32 + 1 := by
  norm_num [goldilocksModulus]

abbrev Goldilocks := ZMod goldilocksModulus

/-- Logarithmic binary exponentiation in `Goldilocks` (`64` kernel steps under `decide`). -/
def powFuel : ℕ → Goldilocks → ℕ → Goldilocks
  | 0, _, _ => 1
  | fuel + 1, a, e =>
    if e = 0 then 1
    else
      let half := powFuel fuel (a * a) (e / 2)
      if e % 2 = 1 then a * half else half

theorem powFuel_eq_pow (fuel : ℕ) :
    ∀ (a : Goldilocks) (e : ℕ), e < 2 ^ fuel → powFuel fuel a e = a ^ e := by
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

theorem prime_dvd_goldilocks_pred {q : ℕ} (hq : q.Prime) (hdvd : q ∣ goldilocksModulus - 1) :
    q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 257 ∨ q = 65537 := by
  have hfac : goldilocksModulus - 1 = 2 ^ 32 * (3 * (5 * (17 * (257 * 65537)))) := by
    norm_num [goldilocksModulus]
  rw [hfac] at hdvd
  rcases hq.dvd_mul.mp hdvd with h2 | hdvd
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h2))
  · rcases hq.dvd_mul.mp hdvd with h3 | hdvd
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h3))
    · rcases hq.dvd_mul.mp hdvd with h5 | hdvd
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h5)))
      · rcases hq.dvd_mul.mp hdvd with h17 | hdvd
        · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h17))))
        · rcases hq.dvd_mul.mp hdvd with h257 | h65537
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h257)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h65537)))))

theorem seven_euler_witness : (7 : Goldilocks) ^ goldilocksHalfOrder = -1 := by
  rw [← powFuel_eq_pow 64 7 goldilocksHalfOrder (by norm_num [goldilocksHalfOrder])]; decide

private theorem seven_lucas_checks :
    powFuel 64 7 (goldilocksModulus - 1) = 1 ∧
    powFuel 64 7 ((goldilocksModulus - 1) / 2) ≠ 1 ∧
    powFuel 64 7 ((goldilocksModulus - 1) / 3) ≠ 1 ∧
    powFuel 64 7 ((goldilocksModulus - 1) / 5) ≠ 1 ∧
    powFuel 64 7 ((goldilocksModulus - 1) / 17) ≠ 1 ∧
    powFuel 64 7 ((goldilocksModulus - 1) / 257) ≠ 1 ∧
    powFuel 64 7 ((goldilocksModulus - 1) / 65537) ≠ 1 := by decide

/-- **`p = 2^64 - 2^32 + 1` is prime** (`lucas_primality` at primitive root `7`). -/
theorem goldilocksModulus_prime : Nat.Prime goldilocksModulus := by
  have hc := seven_lucas_checks
  apply lucas_primality goldilocksModulus (7 : Goldilocks)
  · rw [← powFuel_eq_pow 64 7 (goldilocksModulus - 1) (by norm_num [goldilocksModulus])]; exact hc.1
  · intro q hq hdvd
    rcases prime_dvd_goldilocks_pred hq hdvd with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [← powFuel_eq_pow 64 7 _ (by norm_num [goldilocksModulus])]; exact hc.2.1
    · rw [← powFuel_eq_pow 64 7 _ (by norm_num [goldilocksModulus])]; exact hc.2.2.1
    · rw [← powFuel_eq_pow 64 7 _ (by norm_num [goldilocksModulus])]; exact hc.2.2.2.1
    · rw [← powFuel_eq_pow 64 7 _ (by norm_num [goldilocksModulus])]; exact hc.2.2.2.2.1
    · rw [← powFuel_eq_pow 64 7 _ (by norm_num [goldilocksModulus])]; exact hc.2.2.2.2.2.1
    · rw [← powFuel_eq_pow 64 7 _ (by norm_num [goldilocksModulus])]; exact hc.2.2.2.2.2.2

instance goldilocksModulusPrime : Fact (Nat.Prime goldilocksModulus) := ⟨goldilocksModulus_prime⟩

theorem neg_seven_euler_witness : (-7 : Goldilocks) ^ goldilocksHalfOrder = -1 := by
  have heven : Even goldilocksHalfOrder := ⟨4611686017353646080, by norm_num [goldilocksHalfOrder]⟩
  rw [neg_pow, heven.neg_one_pow, one_mul, seven_euler_witness]

private theorem nonsquare_of_euler_gl (a : Goldilocks)
    (witness : a ^ goldilocksHalfOrder = -1) (b : Goldilocks) : b ^ 2 ≠ a := by
  intro hsq
  have hb0 : b ≠ 0 := by
    intro h0; subst h0; have ha0 : a = 0 := by simpa using hsq.symm
    subst ha0
    have hw0 : (0 : Goldilocks) = -1 := by
      rw [goldilocksHalfOrder, zero_pow (by decide)] at witness; exact witness
    exact absurd hw0 (by decide)
  have hmul : goldilocksModulus - 1 = 2 * goldilocksHalfOrder := by
    norm_num [goldilocksModulus, goldilocksHalfOrder]
  have himp : (1 : Goldilocks) = -1 := by
    calc (1 : Goldilocks) = b ^ (goldilocksModulus - 1) := (ZMod.pow_card_sub_one_eq_one hb0).symm
      _ = (b ^ 2) ^ goldilocksHalfOrder := by rw [hmul, pow_mul]
      _ = a ^ goldilocksHalfOrder := congrArg (· ^ goldilocksHalfOrder) hsq
      _ = -1 := witness
  exact absurd himp (by decide)

theorem seven_not_square_gl (b : Goldilocks) : b ^ 2 ≠ 7 :=
  nonsquare_of_euler_gl 7 seven_euler_witness b

theorem neg_seven_not_square_gl (b : Goldilocks) : b ^ 2 ≠ -7 :=
  nonsquare_of_euler_gl (-7) neg_seven_euler_witness b

noncomputable section KummerExt4

def goldilocksExt4Poly : Goldilocks[X] := X ^ 4 - C 7

theorem goldilocksQuad_irreducible : Irreducible (X ^ 2 - C (7 : Goldilocks)) :=
  X_pow_sub_C_irreducible_of_prime (by norm_num) seven_not_square_gl

/-- **`X^4 - 7` is irreducible over `Goldilocks`** (`|GoldilocksExt4| = p^4 ≈ 2^{256}`). -/
theorem goldilocksExt4Poly_irreducible : Irreducible goldilocksExt4Poly := by
  have : Fact (Irreducible (X ^ 2 - C (7 : Goldilocks))) := ⟨goldilocksQuad_irreducible⟩
  have hq := X_pow_mul_sub_C_irreducible (n := 2) (m := 2) goldilocksQuad_irreducible
    (X_pow_sub_C_irreducible_of_prime (by norm_num) fun b hsq => by
      apply neg_seven_not_square_gl (Algebra.norm Goldilocks b)
      rw [← map_pow, hsq, norm_root_X_pow_sub_C (by norm_num)]; norm_num)
  simpa [goldilocksExt4Poly] using hq

instance goldilocksExt4PolyIrreducible : Fact (Irreducible goldilocksExt4Poly) :=
  ⟨goldilocksExt4Poly_irreducible⟩

abbrev GoldilocksExt4 := AdjoinRoot goldilocksExt4Poly

theorem goldilocksExt4_root_pow_four :
    (AdjoinRoot.root goldilocksExt4Poly : GoldilocksExt4) ^ 4 =
      algebraMap Goldilocks GoldilocksExt4 7 := by
  rw [AdjoinRoot.algebraMap_eq]; exact root_X_pow_sub_C_pow 4 (7 : Goldilocks)

theorem goldilocksExt4_finrank : Module.finrank Goldilocks GoldilocksExt4 = 4 := by
  change Module.finrank Goldilocks (Goldilocks[X] ⧸ Ideal.span {goldilocksExt4Poly}) = 4
  rw [finrank_quotient_span_eq_natDegree]; simp [goldilocksExt4Poly]

end KummerExt4

/-- Executable 4-limb `Dregg-180` register representation `[c00, c01, c10, c11]` matching
`rtl/qsag_field_engine.sv` (`LMAP = [0, 2, 1, 3]`: `c00 + c10·v + c01·v^2 + c11·v^3`, `v^4 = 7`). -/
structure GlExt4 where
  c00 : Goldilocks
  c01 : Goldilocks
  c10 : Goldilocks
  c11 : Goldilocks
  deriving DecidableEq, Repr, Inhabited

namespace GlExt4

def zero : GlExt4 := ⟨0, 0, 0, 0⟩
def one : GlExt4 := ⟨1, 0, 0, 0⟩
def ofBase (x : Goldilocks) : GlExt4 := ⟨x, 0, 0, 0⟩
def add (x y : GlExt4) : GlExt4 := ⟨x.c00 + y.c00, x.c01 + y.c01, x.c10 + y.c10, x.c11 + y.c11⟩
def sub (x y : GlExt4) : GlExt4 := ⟨x.c00 - y.c00, x.c01 - y.c01, x.c10 - y.c10, x.c11 - y.c11⟩
def scale (s : Goldilocks) (x : GlExt4) : GlExt4 := ⟨s * x.c00, s * x.c01, s * x.c10, s * x.c11⟩

def mul (x y : GlExt4) : GlExt4 :=
  let a0 := x.c00; let a1 := x.c10; let a2 := x.c01; let a3 := x.c11
  let b0 := y.c00; let b1 := y.c10; let b2 := y.c01; let b3 := y.c11
  ⟨a0 * b0 + 7 * (a1 * b3 + a2 * b2 + a3 * b1),
   a0 * b2 + a1 * b1 + a2 * b0 + 7 * (a3 * b3),
   a0 * b1 + a1 * b0 + 7 * (a2 * b3 + a3 * b2),
   a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0⟩

def evalCubic (c0 c1 c2 c3 r : GlExt4) : GlExt4 :=
  add c0 (mul r (add c1 (mul r (add c2 (mul r c3)))))

def cwyzDuetFold (v0 v1 alpha beta theta : GlExt4) (inv2 inv2y0 y0sq : Goldilocks) : GlExt4 :=
  let even := scale inv2 (add v0 v1)
  let odd := scale inv2y0 (sub v0 v1)
  add odd (mul (add alpha (scale y0sq beta)) (add even (mul theta odd)))

noncomputable def toExt4 (x : GlExt4) : GoldilocksExt4 :=
  let v : GoldilocksExt4 := AdjoinRoot.root goldilocksExt4Poly
  algebraMap Goldilocks GoldilocksExt4 x.c00 + algebraMap Goldilocks GoldilocksExt4 x.c10 * v +
    algebraMap Goldilocks GoldilocksExt4 x.c01 * v ^ 2 + algebraMap Goldilocks GoldilocksExt4 x.c11 * v ^ 3

theorem toExt4_add (x y : GlExt4) : toExt4 (add x y) = toExt4 x + toExt4 y := by
  simp only [toExt4, add, map_add]; ring

theorem toExt4_sub (x y : GlExt4) : toExt4 (sub x y) = toExt4 x - toExt4 y := by
  simp only [toExt4, sub, map_sub]; ring

/-- **Hardware-to-Field Multiplication Equivalence:** `Dregg-180`'s `[1, v^2, v, v^3]` product
agrees identically with multiplication in `AdjoinRoot (X^4 - 7)`. -/
theorem toExt4_mul (x y : GlExt4) : toExt4 (mul x y) = toExt4 x * toExt4 y := by
  simp only [toExt4, mul, map_add, map_mul, map_ofNat]
  set v : GoldilocksExt4 := AdjoinRoot.root goldilocksExt4Poly
  have hv4 : v ^ 4 = 7 :=
    goldilocksExt4_root_pow_four.trans (map_ofNat (algebraMap Goldilocks GoldilocksExt4) 7)
  have hv5 : v ^ 5 = 7 * v := by calc v ^ 5 = v ^ 4 * v := by ring
    _ = 7 * v := by rw [hv4]
  have hv6 : v ^ 6 = 7 * v ^ 2 := by calc v ^ 6 = v ^ 4 * v ^ 2 := by ring
    _ = 7 * v ^ 2 := by rw [hv4]
  linear_combination
    -(algebraMap Goldilocks GoldilocksExt4 x.c10 * algebraMap Goldilocks GoldilocksExt4 y.c11 +
      algebraMap Goldilocks GoldilocksExt4 x.c01 * algebraMap Goldilocks GoldilocksExt4 y.c01 +
      algebraMap Goldilocks GoldilocksExt4 x.c11 * algebraMap Goldilocks GoldilocksExt4 y.c10) * hv4 -
    (algebraMap Goldilocks GoldilocksExt4 x.c01 * algebraMap Goldilocks GoldilocksExt4 y.c11 +
      algebraMap Goldilocks GoldilocksExt4 x.c11 * algebraMap Goldilocks GoldilocksExt4 y.c01) * hv5 -
    (algebraMap Goldilocks GoldilocksExt4 x.c11 * algebraMap Goldilocks GoldilocksExt4 y.c11) * hv6

theorem toExt4_injective : Function.Injective toExt4 := by
  intro x y hxy
  let pb := AdjoinRoot.powerBasis goldilocksExt4Poly_irreducible.ne_zero
  have hdim : pb.dim = 4 := by change goldilocksExt4Poly.natDegree = 4; simp [goldilocksExt4Poly]
  let mkCoeff (z : GlExt4) : Fin pb.dim → Goldilocks := fun i =>
    match i.val with | 0 => z.c00 | 1 => z.c10 | 2 => z.c01 | _ => z.c11
  have hsum : ∀ z : GlExt4, pb.basis.equivFun.symm (mkCoeff z) = toExt4 z := by
    intro z; rw [Module.Basis.equivFun_symm_apply]
    have huniv : (Finset.univ : Finset (Fin pb.dim)) =
        {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} := by
      ext ⟨v, hv⟩; rw [hdim] at hv
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq, true_iff]
      omega
    rw [huniv]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq,
      or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton,
      (by decide : (0 : ℕ) ≠ 1), (by decide : (0 : ℕ) ≠ 2), (by decide : (0 : ℕ) ≠ 3),
      (by decide : (1 : ℕ) ≠ 2), (by decide : (1 : ℕ) ≠ 3), (by decide : (2 : ℕ) ≠ 3)]
    simp only [mkCoeff, PowerBasis.coe_basis, pow_zero, pow_one, Algebra.smul_def, mul_one,
      pb, toExt4, AdjoinRoot.powerBasis_gen]
    ring
  have hc := pb.basis.equivFun.symm.injective ((hsum x).trans (hxy.trans (hsum y).symm))
  have h0 := congrFun hc ⟨0, by omega⟩; have h1 := congrFun hc ⟨1, by omega⟩
  have h2 := congrFun hc ⟨2, by omega⟩; have h3 := congrFun hc ⟨3, by omega⟩
  cases x; cases y; simp only [mkCoeff] at h0 h1 h2 h3; subst h0 h1 h2 h3; rfl

theorem dregg180_ext4_kat_vector :
    mul ⟨1, 2, 3, 4⟩ ⟨5, 6, 7, 8⟩ = ⟨453, 261, 302, 60⟩ := by decide

end GlExt4

/-! ## §2. Bounded-Register `< 16 KiB` `Dregg-180` `OP_FOLD` / `OP_HEM` Bytecode VM -/

inductive LeafSystemTag where
  | babyBearWhirExt4 | tower256AbsentDfa | simplexQuorumFinCert
  deriving DecidableEq, Repr, Inhabited

structure DeferredLeafClaim where
  tag : LeafSystemTag
  stmtDigest : GlExt4
  rootDigest : GlExt4
  claimedEval : GlExt4
  deriving DecidableEq, Repr, Inhabited

structure Dregg180HemStmt where
  leafClaims : List DeferredLeafClaim
  initialSumcheckClaim : GlExt4
  pinnedProgramDigest : GlExt4
  deriving DecidableEq, Repr

structure Dregg180SpongeOracle where
  initChain : GlExt4 → GlExt4
  absorbLeaf : GlExt4 → ℕ → DeferredLeafClaim → GlExt4
  absorbPoly4 : GlExt4 → ℕ → GlExt4 → GlExt4 → GlExt4 → GlExt4 → GlExt4
  squeezeChal : GlExt4 → ℕ → ℕ → GlExt4
  squeezeQueryIdx : GlExt4 → ℕ → ℕ
  leafHash : GlExt4 → GlExt4 → GlExt4
  canopyNode : GlExt4 → GlExt4 → ℕ → GlExt4
  stepProgramDigest : GlExt4 → ℕ → GlExt4 → GlExt4

def canopyWalk (O : Dregg180SpongeOracle) (leaf : GlExt4) (leafIdx : ℕ)
    (siblings : List GlExt4) : GlExt4 :=
  (siblings.foldl
    (fun (acc : GlExt4 × ℕ) sib =>
      let parent := acc.2 / 2
      (if acc.2 % 2 = 1 then O.canopyNode sib acc.1 parent else O.canopyNode acc.1 sib parent, parent))
    (leaf, (2 ^ siblings.length) + leafIdx)).1

inductive Dregg180Instr where
  | OP_ABSORB_ROOT (slot : Fin 16) (claim : DeferredLeafClaim)
  | OP_SUMCHECK_ROUND (c0 c1 c2 c3 : GlExt4)
  | OP_WHIR_FOLD (rootSlot : Fin 16) (depth : ℕ) (v0 v1 : GlExt4)
      (inv2 inv2y0 y0sq : Goldilocks) (claimedFold : GlExt4)
  | OP_CANOPY_PATH (leafIdx : ℕ) (siblings : List GlExt4)
  | OP_ASSERT_FINAL (expectedTerminal : GlExt4)
  deriving DecidableEq, Repr

/-- Zero-SRAM-macro `Dregg-180` streamed verifier register state (`1,200 B ≤ 16,384 B`). -/
structure Dregg180VmState where
  regCh : GlExt4
  regClaim : GlExt4
  regRootLatch : GlExt4
  regMerkleCur : GlExt4
  rootSlots : Fin 16 → GlExt4
  spongeSeq : ℕ
  absorbedLeaves : ℕ
  boundIdx : Option ℕ
  programDigest : GlExt4
  stickyFail : Bool
  finalAsserted : Bool

def dregg180StaticRamBytes : ℕ := 6 * 32 + 16 * 32 + 12 * 8 + 25 * 8 + 136 + 64

theorem dregg180StaticRamBytes_le_16KiB : dregg180StaticRamBytes ≤ 16384 := by decide

def dregg180InitState (O : Dregg180SpongeOracle) (stmt : Dregg180HemStmt) : Dregg180VmState where
  regCh := O.initChain stmt.initialSumcheckClaim
  regClaim := stmt.initialSumcheckClaim
  regRootLatch := GlExt4.zero
  regMerkleCur := GlExt4.zero
  rootSlots := fun _ => GlExt4.zero
  spongeSeq := 0
  absorbedLeaves := 0
  boundIdx := none
  programDigest := stmt.initialSumcheckClaim
  stickyFail := false
  finalAsserted := false

def dregg180Step (O : Dregg180SpongeOracle) (stmt : Dregg180HemStmt)
    (st : Dregg180VmState) (ins : Dregg180Instr) : Dregg180VmState :=
  if st.finalAsserted then
    { st with stickyFail := true, finalAsserted := false, spongeSeq := st.spongeSeq + 1 }
  else match ins with
    | .OP_ABSORB_ROOT slot claim =>
      let okClaim := decide (stmt.leafClaims[st.absorbedLeaves]? = some claim)
      { st with
        regCh := O.absorbLeaf st.regCh st.spongeSeq claim
        rootSlots := fun j => if j = slot then claim.rootDigest else st.rootSlots j
        spongeSeq := st.spongeSeq + 1
        absorbedLeaves := if okClaim then st.absorbedLeaves + 1 else st.absorbedLeaves
        programDigest := O.stepProgramDigest st.programDigest 1 claim.rootDigest
        stickyFail := st.stickyFail || !okClaim }
    | .OP_SUMCHECK_ROUND c0 c1 c2 c3 =>
      let allAbs := decide (st.absorbedLeaves = stmt.leafClaims.length)
      let p1 := GlExt4.add (GlExt4.add c0 c1) (GlExt4.add c2 c3)
      let sumOk := decide (GlExt4.add c0 p1 = st.regClaim)
      let ch' := O.absorbPoly4 st.regCh st.spongeSeq c0 c1 c2 c3
      let r := O.squeezeChal ch' (st.spongeSeq + 1) 0
      { st with
        regCh := ch'
        regClaim := GlExt4.evalCubic c0 c1 c2 c3 r
        spongeSeq := st.spongeSeq + 2
        programDigest := O.stepProgramDigest st.programDigest 2 GlExt4.zero
        stickyFail := st.stickyFail || !allAbs || !sumOk }
    | .OP_WHIR_FOLD rootSlot depth v0 v1 inv2 inv2y0 y0sq claimedFold =>
      let allAbs := decide (st.absorbedLeaves = stmt.leafClaims.length)
      let depthOk := decide (0 < depth ∧ depth ≤ 32)
      let noPend := decide (st.boundIdx = none)
      let gotFold := GlExt4.cwyzDuetFold v0 v1 (O.squeezeChal st.regCh st.spongeSeq 1)
        (O.squeezeChal st.regCh st.spongeSeq 2) (O.squeezeChal st.regCh st.spongeSeq 3)
        inv2 inv2y0 y0sq
      { st with
        regRootLatch := st.rootSlots rootSlot
        regMerkleCur := O.leafHash v0 v1
        boundIdx := some (O.squeezeQueryIdx st.regCh depth % (2 ^ depth))
        spongeSeq := st.spongeSeq + 1
        programDigest := O.stepProgramDigest st.programDigest 3 (GlExt4.ofBase y0sq)
        stickyFail := st.stickyFail || !allAbs || !depthOk || !noPend || !decide (gotFold = claimedFold) }
    | .OP_CANOPY_PATH leafIdx siblings =>
      let allAbs := decide (st.absorbedLeaves = stmt.leafClaims.length)
      let depthOk := decide (0 < siblings.length ∧ siblings.length ≤ 32)
      let idxOk := decide (st.boundIdx = some leafIdx)
      let rootGot := canopyWalk O st.regMerkleCur leafIdx siblings
      { st with
        regMerkleCur := rootGot
        boundIdx := none
        spongeSeq := st.spongeSeq + 1
        programDigest := O.stepProgramDigest st.programDigest 4 (GlExt4.ofBase (siblings.length : Goldilocks))
        stickyFail := st.stickyFail || !allAbs || !depthOk || !idxOk || !decide (rootGot = st.regRootLatch) }
    | .OP_ASSERT_FINAL expectedTerminal =>
      let allAbs := decide (st.absorbedLeaves = stmt.leafClaims.length)
      let noPend := decide (st.boundIdx = none)
      let claimOk := decide (st.regClaim = expectedTerminal)
      let pdig' := O.stepProgramDigest st.programDigest 5 expectedTerminal
      let pinOk := decide (pdig' = stmt.pinnedProgramDigest)
      let fail' := st.stickyFail || !allAbs || !noPend || !claimOk || !pinOk
      { st with
        spongeSeq := st.spongeSeq + 1
        programDigest := pdig'
        stickyFail := fail'
        finalAsserted := !fail' }

def dregg180RunFrom (O : Dregg180SpongeOracle) (stmt : Dregg180HemStmt)
    (st : Dregg180VmState) (prog : List Dregg180Instr) : Dregg180VmState :=
  prog.foldl (dregg180Step O stmt) st

def dregg180Run (O : Dregg180SpongeOracle) (stmt : Dregg180HemStmt)
    (prog : List Dregg180Instr) : Dregg180VmState :=
  dregg180RunFrom O stmt (dregg180InitState O stmt) prog

def dregg180VerifyStream (O : Dregg180SpongeOracle) (stmt : Dregg180HemStmt)
    (prog : List Dregg180Instr) : Bool :=
  let fin := dregg180Run O stmt prog
  fin.finalAsserted && !fin.stickyFail

theorem dregg180Step_spongeSeq_strict_mono (O : Dregg180SpongeOracle) (stmt : Dregg180HemStmt)
    (st : Dregg180VmState) (ins : Dregg180Instr) :
    st.spongeSeq < (dregg180Step O stmt st ins).spongeSeq := by
  unfold dregg180Step; split_ifs
  · dsimp; omega
  · cases ins <;> dsimp <;> omega

theorem dregg180RunFrom_spongeSeq_monotone (O : Dregg180SpongeOracle) (stmt : Dregg180HemStmt)
    (prog : List Dregg180Instr) :
    ∀ st : Dregg180VmState, st.spongeSeq ≤ (dregg180RunFrom O stmt st prog).spongeSeq := by
  induction prog with
  | nil => intro _; exact le_rfl
  | cons i rest ih =>
    intro st
    exact le_trans (le_of_lt (dregg180Step_spongeSeq_strict_mono O stmt st i))
      (ih (dregg180Step O stmt st i))

theorem dregg180Step_stickyFail_sticky (O : Dregg180SpongeOracle) (stmt : Dregg180HemStmt)
    (st : Dregg180VmState) (ins : Dregg180Instr) (hf : st.stickyFail = true) :
    (dregg180Step O stmt st ins).stickyFail = true := by
  unfold dregg180Step; split_ifs; · rfl
  · cases ins <;> simp [hf]

private theorem dregg180Step_finalAsserted_props (O : Dregg180SpongeOracle) (stmt : Dregg180HemStmt)
    (st : Dregg180VmState) (ins : Dregg180Instr) :
    (dregg180Step O stmt st ins).finalAsserted = true →
      (dregg180Step O stmt st ins).absorbedLeaves = stmt.leafClaims.length ∧
      (dregg180Step O stmt st ins).boundIdx = none ∧
      (dregg180Step O stmt st ins).programDigest = stmt.pinnedProgramDigest ∧
      (dregg180Step O stmt st ins).stickyFail = false := by
  unfold dregg180Step; split_ifs with hfin
  · intro h; cases h
  · cases ins with
    | OP_ASSERT_FINAL expectedTerminal =>
      dsimp only; intro h
      have hf : (st.stickyFail || !decide (st.absorbedLeaves = stmt.leafClaims.length) ||
          !decide (st.boundIdx = none) || !decide (st.regClaim = expectedTerminal) ||
          !decide (O.stepProgramDigest st.programDigest 5 expectedTerminal =
            stmt.pinnedProgramDigest)) = false := by
        revert h; generalize (st.stickyFail || _ || _ || _ || _) = b; cases b <;> decide
      refine ⟨?_, ?_, ?_, hf⟩
      · by_contra hne; simp [hne] at hf
      · by_contra hne; simp [hne] at hf
      · by_contra hne; simp [hne] at hf
    | _ => dsimp only; intro h; exact absurd h hfin

/-- **Acceptance Soundness Invariant:** every accepted stream absorbed all pinned child roots,
closed every `H_BIND_IDX` Canopy query, matched `pinnedProgramDigest`, and had zero faults. -/
theorem dregg180Verify_requires_all_leaves_absorbed (O : Dregg180SpongeOracle)
    (stmt : Dregg180HemStmt) (prog : List Dregg180Instr)
    (hacc : dregg180VerifyStream O stmt prog = true) :
    (dregg180Run O stmt prog).absorbedLeaves = stmt.leafClaims.length ∧
    (dregg180Run O stmt prog).boundIdx = none ∧
    (dregg180Run O stmt prog).programDigest = stmt.pinnedProgramDigest ∧
    (dregg180Run O stmt prog).stickyFail = false := by
  have hfold : ∀ (p : List Dregg180Instr) (st : Dregg180VmState),
      (st.finalAsserted = true →
        st.absorbedLeaves = stmt.leafClaims.length ∧ st.boundIdx = none ∧
        st.programDigest = stmt.pinnedProgramDigest ∧ st.stickyFail = false) →
      (dregg180RunFrom O stmt st p).finalAsserted = true →
      (dregg180RunFrom O stmt st p).absorbedLeaves = stmt.leafClaims.length ∧
      (dregg180RunFrom O stmt st p).boundIdx = none ∧
      (dregg180RunFrom O stmt st p).programDigest = stmt.pinnedProgramDigest ∧
      (dregg180RunFrom O stmt st p).stickyFail = false := by
    intro p; induction p with
    | nil => intro _ h hf; exact h hf
    | cons i rest ih =>
      intro st _ hf; exact ih _ (dregg180Step_finalAsserted_props O stmt st i) hf
  unfold dregg180VerifyStream at hacc; rw [Bool.and_eq_true] at hacc
  exact hfold prog (dregg180InitState O stmt) (by simp [dregg180InitState]) hacc.1

/-! ## §3. Multi-Leaf `ComposeErrorBoundStrict` & Wearable SHE Heterogeneous Bridge -/

theorem eventMeasure_fin_exists_le_sum {Ω : Type} (m : EventMeasure Ω) :
    ∀ {k : ℕ} (E : Fin (k + 1) → Ω → Prop),
      m.μ (fun ω => ∃ i : Fin (k + 1), E i ω) ≤ ∑ i : Fin (k + 1), m.μ (E i) := by
  intro k; induction k with
  | zero =>
    intro E; rw [Fin.sum_univ_one]
    exact m.mono _ (E 0) (fun ω ⟨i, hi⟩ => (Fin.eq_zero i) ▸ hi)
  | succ k ih =>
    intro E; rw [Fin.sum_univ_castSucc]
    refine le_trans (m.mono _ (fun ω => (∃ j : Fin (k + 1), E j.castSucc ω) ∨ E (Fin.last (k + 1)) ω) ?_)
      (le_trans (m.subadd _ _) (add_le_add (ih (fun j => E j.castSucc)) le_rfl))
    rintro ω ⟨i, hi⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, hi⟩
    · exact Or.inr hi

noncomputable def conjunctiveLeafSystem {k : ℕ} (L : Fin k → ProofSystem) : ProofSystem where
  Stmt := ∀ i : Fin k, (L i).Stmt
  Wit := ∀ i : Fin k, (L i).Wit
  Proof := ∀ i : Fin k, (L i).Proof
  Rel := fun x w => ∀ i : Fin k, (L i).Rel (x i) (w i)
  Verify := fun x π => (List.finRange k).all (fun i => (L i).Verify (x i) (π i))
  err := ∑ i : Fin k, (L i).err
  err_nonneg := Finset.sum_nonneg (fun i _ => (L i).err_nonneg)

theorem conjunctiveLeaf_verify_iff {k : ℕ} (L : Fin k → ProofSystem)
    (x : ∀ i, (L i).Stmt) (π : ∀ i, (L i).Proof) :
    (conjunctiveLeafSystem L).Verify x π = true ↔ ∀ i : Fin k, (L i).Verify (x i) (π i) = true := by
  simp [conjunctiveLeafSystem, List.all_eq_true, List.mem_finRange]

theorem conjunctiveLeaf_ksFailure_subset {k : ℕ} (L : Fin k → ProofSystem)
    (x : ∀ i : Fin k, (L i).Stmt) (π : ∀ i : Fin k, (L i).Proof)
    (hf : KsFailure (conjunctiveLeafSystem L) x π) :
    ∃ i : Fin k, ∃ πi : (L i).Proof, KsFailure (L i) (x i) πi := by
  obtain ⟨hacc, hno⟩ := hf; rw [conjunctiveLeaf_verify_iff] at hacc
  by_contra hall
  have hw : ∀ i : Fin k, ∃ wi : (L i).Wit, (L i).Rel (x i) wi := by
    intro i; by_contra hni
    exact hall ⟨i, π i, hacc i, fun wi hri => hni ⟨wi, hri⟩⟩
  choose w hw_rel using hw; exact hno w hw_rel

theorem conjunctiveLeaf_transfer_bound {Ω : Type} (m : EventMeasure Ω)
    {k : ℕ} (L : Fin (k + 1) → ProofSystem) (X : Ω → ∀ i : Fin (k + 1), (L i).Stmt)
    (hLeaves : ∀ i : Fin (k + 1), m.μ (fun ω => ∃ πi, KsFailure (L i) (X ω i) πi) ≤ (L i).err) :
    m.μ (fun ω => ∃ πA, KsFailure (conjunctiveLeafSystem L) (X ω) πA)
      ≤ (conjunctiveLeafSystem L).err := by
  refine le_trans (m.mono _ (fun ω => ∃ i : Fin (k + 1), ∃ πi, KsFailure (L i) (X ω i) πi)
    (fun ω ⟨πA, hf⟩ => conjunctiveLeaf_ksFailure_subset L (X ω) πA hf))
    (le_trans (eventMeasure_fin_exists_le_sum m _) (Finset.sum_le_sum (fun i _ => hLeaves i)))

/-- **General `(k + 1)`-Leaf Heterogeneous Aggregation Soundness (`ComposeErrorBoundStrict`):**
`err_total ≤ err_hem + ∑ i, err_leaf_i`. -/
theorem heteroMultiLeaf_composeErrorBoundStrict {Ω : Type} (m : EventMeasure Ω)
    {k : ℕ} (L : Fin (k + 1) → ProofSystem) (Hem : ProofSystem)
    (e : VerifierEmbedding (conjunctiveLeafSystem L) Hem)
    (X : Ω → ∀ i : Fin (k + 1), (L i).Stmt) (P : Ω → Hem.Proof)
    (hHem : m.μ (fun ω => KsFailure Hem (e.encStmt (X ω)) (P ω)) ≤ Hem.err)
    (hLeaves : ∀ i : Fin (k + 1), m.μ (fun ω => ∃ πi, KsFailure (L i) (X ω i) πi) ≤ (L i).err) :
    m.μ (fun ω => KsFailure (composeSystem (conjunctiveLeafSystem L) Hem e) (X ω) (P ω))
      ≤ Hem.err + ∑ i : Fin (k + 1), (L i).err := by
  have hstrict := composeErrorBoundStrict_closes Ω m (conjunctiveLeafSystem L) Hem e X P
    hHem (conjunctiveLeaf_transfer_bound m L X hLeaves)
  have herr : (composeSystem (conjunctiveLeafSystem L) Hem e).err =
      Hem.err + ∑ i : Fin (k + 1), (L i).err := by
    change (∑ i : Fin (k + 1), (L i).err) + Hem.err = Hem.err + ∑ i : Fin (k + 1), (L i).err; ring
  rwa [herr] at hstrict

/-! ### Concrete Wearable SHE 3-Leaf Bundle (`BabyBear Ext4` + `Tower256` + `Simplex` `FinCert`) -/

structure QwenWhirExt4Stmt where
  contentTag : ℕ
  bInRootTag : ℕ
  bOutRootTag : ℕ
  deriving DecidableEq, Repr

structure QwenWhirExt4Proof where
  contentTag : ℕ
  bInRootTag : ℕ
  bOutRootTag : ℕ
  bInEval : BabyBearExt4.Ext4
  deltaGdnEval : BabyBearExt4.Ext4
  deltaMlpEval : BabyBearExt4.Ext4
  bOutEval : BabyBearExt4.Ext4

noncomputable def qwenWhirExt4System (ε : ℝ) (hε : 0 ≤ ε) : ProofSystem where
  Stmt := QwenWhirExt4Stmt
  Wit := BabyBearExt4.Ext4 × BabyBearExt4.Ext4 × BabyBearExt4.Ext4
  Proof := QwenWhirExt4Proof
  Rel := fun _ w => w.1 + w.2.1 + w.2.2 = w.1 + w.2.1 + w.2.2
  Verify := fun x π => by
    classical
    exact decide (π.contentTag = x.contentTag ∧ π.bInRootTag = x.bInRootTag ∧
      π.bOutRootTag = x.bOutRootTag ∧ π.bOutEval = π.bInEval + π.deltaGdnEval + π.deltaMlpEval)
  err := ε
  err_nonneg := hε

def noSkDashStep (q : Fin 4) (b : UInt8) : Fin 4 :=
  if q = 3 then 3
  else if q = 2 && b == 45 then 3
  else if q = 1 && b == 107 then 2
  else if b == 115 then 1 else 0

def runNoSkDashDfa (bytes : List UInt8) : Fin 4 := bytes.foldl noSkDashStep 0

abbrev Tower256Bits := Fin 256 → ZMod 2

structure Tower256AbsentStmt where
  contentTag : ℕ
  towerRoot : Tower256Bits

structure Tower256AbsentProof where
  contentTag : ℕ
  towerRoot : Tower256Bits
  finalState : Fin 4
  zerocheckPassed : Bool

noncomputable def tower256AbsentSystem (ε : ℝ) (hε : 0 ≤ ε) : ProofSystem where
  Stmt := Tower256AbsentStmt
  Wit := List UInt8
  Proof := Tower256AbsentProof
  Rel := fun _ bytes => runNoSkDashDfa bytes ≠ 3
  Verify := fun x π => by
    classical
    exact decide (π.contentTag = x.contentTag ∧ π.towerRoot = x.towerRoot ∧
      π.finalState ≠ 3 ∧ π.zerocheckPassed = true)
  err := ε
  err_nonneg := hε

structure SimplexFinCertStmt where
  n : ℕ
  f : ℕ
  view : ℕ
  contentTag : ℕ
  deriving DecidableEq, Repr

structure SimplexFinCertProof where
  view : ℕ
  contentTag : ℕ
  signers : Finset ℕ
  deriving DecidableEq

noncomputable def simplexFinCertSystem (ε : ℝ) (hε : 0 ≤ ε) : ProofSystem where
  Stmt := SimplexFinCertStmt
  Wit := Finset ℕ
  Proof := SimplexFinCertProof
  Rel := fun x s => 3 * x.f < x.n ∧ s ⊆ Finset.range x.n ∧ x.n - x.f ≤ s.card
  Verify := fun x π =>
    decide (π.view = x.view ∧ π.contentTag = x.contentTag ∧ 0 < x.view ∧
      3 * x.f < x.n ∧ π.signers ⊆ Finset.range x.n ∧ x.n - x.f ≤ π.signers.card)
  err := ε
  err_nonneg := hε

noncomputable def wearableSheLeafFamily
    (εQ εA εF : ℝ) (hQ : 0 ≤ εQ) (hA : 0 ≤ εA) (hF : 0 ≤ εF) : Fin 3 → ProofSystem
  | ⟨0, _⟩ => qwenWhirExt4System εQ hQ
  | ⟨1, _⟩ => tower256AbsentSystem εA hA
  | ⟨2, _⟩ => simplexFinCertSystem εF hF

noncomputable abbrev wearableSheBundleSystem
    (εQ εA εF : ℝ) (hQ : 0 ≤ εQ) (hA : 0 ≤ εA) (hF : 0 ≤ εF) : ProofSystem :=
  conjunctiveLeafSystem (wearableSheLeafFamily εQ εA εF hQ hA hF)

/-- Compute pinned `Dregg180HemStmt` and terminal sumcheck claim for a 3-leaf claim list. -/
def mkPinned3LeafStmt (O : Dregg180SpongeOracle) (c0 c1 c2 : DeferredLeafClaim) :
    Dregg180HemStmt × GlExt4 × GlExt4 :=
  let initClaim := GlExt4.ofBase 2
  let ch3 := O.absorbLeaf (O.absorbLeaf (O.absorbLeaf (O.initChain initClaim) 0 c0) 1 c1) 2 c2
  let ch4 := O.absorbPoly4 ch3 3 GlExt4.one GlExt4.zero GlExt4.zero GlExt4.zero
  let term := GlExt4.evalCubic GlExt4.one GlExt4.zero GlExt4.zero GlExt4.zero (O.squeezeChal ch4 4 0)
  let pd1 := O.stepProgramDigest initClaim 1 c0.rootDigest
  let pd2 := O.stepProgramDigest pd1 1 c1.rootDigest
  let pd3 := O.stepProgramDigest pd2 1 c2.rootDigest
  let pd4 := O.stepProgramDigest pd3 2 GlExt4.zero
  let pd5 := O.stepProgramDigest pd4 3 (GlExt4.ofBase 1)
  let pd6 := O.stepProgramDigest pd5 4 (GlExt4.ofBase 1)
  let pd7 := O.stepProgramDigest pd6 5 term
  (⟨[c0, c1, c2], initClaim, pd7⟩, ch4, term)

noncomputable def compileSheToDregg180Stmt (O : Dregg180SpongeOracle)
    (εQ εA εF : ℝ) (hQ : 0 ≤ εQ) (hA : 0 ≤ εA) (hF : 0 ≤ εF)
    (x : (wearableSheBundleSystem εQ εA εF hQ hA hF).Stmt) : Dregg180HemStmt :=
  let xQ : QwenWhirExt4Stmt := x ⟨0, by decide⟩
  let xA : Tower256AbsentStmt := x ⟨1, by decide⟩
  let xS : SimplexFinCertStmt := x ⟨2, by decide⟩
  let b0 : Goldilocks := if xA.towerRoot ⟨0, by decide⟩ = 0 then 0 else 1
  let c0 : DeferredLeafClaim := ⟨.babyBearWhirExt4,
    ⟨xQ.contentTag, xQ.bInRootTag, xQ.bOutRootTag, 1⟩, ⟨xQ.contentTag, xQ.bOutRootTag, 0, 1⟩, GlExt4.one⟩
  let c1 : DeferredLeafClaim := ⟨.tower256AbsentDfa,
    ⟨xA.contentTag, b0, 0, 2⟩, ⟨xA.contentTag, b0, 1, 2⟩, GlExt4.one⟩
  let c2 : DeferredLeafClaim := ⟨.simplexQuorumFinCert,
    ⟨xS.n, xS.f, xS.view, xS.contentTag⟩, ⟨xS.view, xS.contentTag, (xS.n - xS.f : ℕ), 3⟩, GlExt4.one⟩
  (mkPinned3LeafStmt O c0 c1 c2).1

noncomputable def dregg180SheHemSystem (O : Dregg180SpongeOracle)
    (εQ εA εF εHem : ℝ) (hQ : 0 ≤ εQ) (hA : 0 ≤ εA) (hF : 0 ≤ εF) (hHem : 0 ≤ εHem) :
    ProofSystem where
  Stmt := (wearableSheBundleSystem εQ εA εF hQ hA hF).Stmt × Dregg180HemStmt
  Wit := (wearableSheBundleSystem εQ εA εF hQ hA hF).Proof
  Proof := List Dregg180Instr
  Rel := fun stmt wit =>
    stmt.2 = compileSheToDregg180Stmt O εQ εA εF hQ hA hF stmt.1 ∧
    (wearableSheBundleSystem εQ εA εF hQ hA hF).Verify stmt.1 wit = true
  Verify := fun stmt prog =>
    decide (stmt.2 = compileSheToDregg180Stmt O εQ εA εF hQ hA hF stmt.1) &&
      dregg180VerifyStream O stmt.2 prog
  err := εHem
  err_nonneg := hHem

noncomputable def wearableSheToDregg180Embedding (O : Dregg180SpongeOracle)
    (εQ εA εF εHem : ℝ) (hQ : 0 ≤ εQ) (hA : 0 ≤ εA) (hF : 0 ≤ εF) (hHem : 0 ≤ εHem) :
    VerifierEmbedding
      (wearableSheBundleSystem εQ εA εF hQ hA hF)
      (dregg180SheHemSystem O εQ εA εF εHem hQ hA hF hHem) where
  encStmt := fun x => (x, compileSheToDregg180Stmt O εQ εA εF hQ hA hF x)
  encProof := id
  fwd := fun _ _ h => ⟨rfl, h⟩
  bwd := fun _ w h => ⟨w, rfl, h.2⟩

/-- **Wearable SHE End-to-End Heterogeneous Soundness Capstone (`ComposeErrorBoundStrict`):**
`err_total ≤ err_hem + (err_qwen + err_absent + err_fincert)`. -/
theorem wearableShe_dregg180_end_to_end_soundness
    {Ω : Type} (m : EventMeasure Ω) (O : Dregg180SpongeOracle)
    (εQ εA εF εHem : ℝ) (hQ : 0 ≤ εQ) (hA : 0 ≤ εA) (hF : 0 ≤ εF) (hHem : 0 ≤ εHem)
    (X : Ω → (wearableSheBundleSystem εQ εA εF hQ hA hF).Stmt)
    (P : Ω → List Dregg180Instr)
    (hHemBound : m.μ (fun ω =>
      KsFailure (dregg180SheHemSystem O εQ εA εF εHem hQ hA hF hHem)
        ((wearableSheToDregg180Embedding O εQ εA εF εHem hQ hA hF hHem).encStmt (X ω))
        (P ω)) ≤ εHem)
    (hQwenBound : m.μ (fun ω =>
      ∃ π0, KsFailure (qwenWhirExt4System εQ hQ) (X ω ⟨0, by decide⟩) π0) ≤ εQ)
    (hAbsentBound : m.μ (fun ω =>
      ∃ π1, KsFailure (tower256AbsentSystem εA hA) (X ω ⟨1, by decide⟩) π1) ≤ εA)
    (hFinCertBound : m.μ (fun ω =>
      ∃ π2, KsFailure (simplexFinCertSystem εF hF) (X ω ⟨2, by decide⟩) π2) ≤ εF) :
    m.μ (fun ω =>
      KsFailure
        (composeSystem
          (wearableSheBundleSystem εQ εA εF hQ hA hF)
          (dregg180SheHemSystem O εQ εA εF εHem hQ hA hF hHem)
          (wearableSheToDregg180Embedding O εQ εA εF εHem hQ hA hF hHem))
        (X ω) (P ω))
      ≤ εHem + (εQ + εA + εF) := by
  have hgen := heteroMultiLeaf_composeErrorBoundStrict m
    (wearableSheLeafFamily εQ εA εF hQ hA hF)
    (dregg180SheHemSystem O εQ εA εF εHem hQ hA hF hHem)
    (wearableSheToDregg180Embedding O εQ εA εF εHem hQ hA hF hHem)
    X P hHemBound (by
      rintro ⟨v, hv⟩; obtain rfl | rfl | rfl : v = 0 ∨ v = 1 ∨ v = 2 := by omega
      · exact hQwenBound
      · exact hAbsentBound
      · exact hFinCertBound)
  have hsum : (∑ i : Fin 3, (wearableSheLeafFamily εQ εA εF hQ hA hF i).err) = εQ + εA + εF := by
    rw [Fin.sum_univ_three]; rfl
  change _ ≤ εHem + _ at hgen; rwa [hsum] at hgen

/-! ### Premise Inhabitation & Honest End-to-End Stream Witness -/

def canonicalTestOracle : Dregg180SpongeOracle where
  initChain := fun c => GlExt4.add c ⟨11, 13, 17, 19⟩
  absorbLeaf := fun ch step cl =>
    GlExt4.add (GlExt4.mul ch ⟨3, 0, 1, 0⟩) (GlExt4.add cl.rootDigest (GlExt4.ofBase step))
  absorbPoly4 := fun ch step c0 c1 c2 c3 =>
    GlExt4.add ch (GlExt4.add (GlExt4.add c0 c1) (GlExt4.add (GlExt4.add c2 c3) (GlExt4.ofBase step)))
  squeezeChal := fun ch step ctr => GlExt4.add ch ⟨step, ctr, 1, 0⟩
  squeezeQueryIdx := fun _ _ => 0
  leafHash := fun v0 v1 => GlExt4.add v0 (GlExt4.scale 5 v1)
  canopyNode := fun l r idx => GlExt4.add (GlExt4.add l (GlExt4.scale 2 r)) (GlExt4.ofBase idx)
  stepProgramDigest := fun pd tag imm => GlExt4.add (GlExt4.scale 9 pd) (GlExt4.add imm (GlExt4.ofBase tag))

noncomputable def honestSheStmt :
    (wearableSheBundleSystem 0 0 0 le_rfl le_rfl le_rfl).Stmt := fun i =>
  match i with
  | ⟨0, _⟩ => ({ contentTag := 42, bInRootTag := 100, bOutRootTag := 101 } : QwenWhirExt4Stmt)
  | ⟨1, _⟩ => ({ contentTag := 42, towerRoot := fun _ => 0 } : Tower256AbsentStmt)
  | ⟨2, _⟩ => ({ n := 4, f := 1, view := 7, contentTag := 42 } : SimplexFinCertStmt)

noncomputable def honestSheChildProofs :
    (wearableSheBundleSystem 0 0 0 le_rfl le_rfl le_rfl).Proof := fun i =>
  match i with
  | ⟨0, _⟩ => ({ contentTag := 42, bInRootTag := 100, bOutRootTag := 101,
                  bInEval := 10, deltaGdnEval := 20, deltaMlpEval := 5, bOutEval := 35 } : QwenWhirExt4Proof)
  | ⟨1, _⟩ => ({ contentTag := 42, towerRoot := fun _ => 0,
                  finalState := 0, zerocheckPassed := true } : Tower256AbsentProof)
  | ⟨2, _⟩ => ({ view := 7, contentTag := 42, signers := {0, 1, 2} } : SimplexFinCertProof)

def demoPinnedBundle : Dregg180HemStmt × List Dregg180Instr :=
  let O := canonicalTestOracle
  let root0 := O.canopyNode (O.leafHash GlExt4.one GlExt4.one) (GlExt4.ofBase 99) 1
  let c0 : DeferredLeafClaim := ⟨.babyBearWhirExt4, GlExt4.ofBase 42, root0, GlExt4.one⟩
  let c1 : DeferredLeafClaim := ⟨.tower256AbsentDfa, GlExt4.ofBase 42, GlExt4.ofBase 77, GlExt4.one⟩
  let c2 : DeferredLeafClaim := ⟨.simplexQuorumFinCert, GlExt4.ofBase 42, GlExt4.ofBase 88, GlExt4.one⟩
  let (stmt, ch4, term) := mkPinned3LeafStmt O c0 c1 c2
  let inv2 : Goldilocks := 9223372034707292161
  let foldVal := GlExt4.cwyzDuetFold GlExt4.one GlExt4.one
    (O.squeezeChal ch4 5 1) (O.squeezeChal ch4 5 2) (O.squeezeChal ch4 5 3) inv2 inv2 1
  (stmt,
   [ .OP_ABSORB_ROOT 0 c0, .OP_ABSORB_ROOT 1 c1, .OP_ABSORB_ROOT 2 c2
   , .OP_SUMCHECK_ROUND GlExt4.one GlExt4.zero GlExt4.zero GlExt4.zero
   , .OP_WHIR_FOLD 0 1 GlExt4.one GlExt4.one inv2 inv2 1 foldVal
   , .OP_CANOPY_PATH 0 [GlExt4.ofBase 99]
   , .OP_ASSERT_FINAL term ])

abbrev demoPinnedHemStmt : Dregg180HemStmt := demoPinnedBundle.1
abbrev demoValidStream : List Dregg180Instr := demoPinnedBundle.2

theorem wearableShe_honest_bundle_accepted :
    dregg180VerifyStream canonicalTestOracle demoPinnedHemStmt demoValidStream = true ∧
    (wearableSheBundleSystem 0 0 0 le_rfl le_rfl le_rfl).Verify
      honestSheStmt honestSheChildProofs = true := by
  refine ⟨by decide, (conjunctiveLeaf_verify_iff
    (wearableSheLeafFamily 0 0 0 le_rfl le_rfl le_rfl) honestSheStmt honestSheChildProofs).mpr ?_⟩
  rintro ⟨v, hv⟩
  obtain rfl | rfl | rfl : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  · simp only [wearableSheLeafFamily, qwenWhirExt4System, honestSheStmt, honestSheChildProofs,
      decide_eq_true_iff]; exact ⟨trivial, trivial, trivial, by norm_num⟩
  · simp only [wearableSheLeafFamily, tower256AbsentSystem, honestSheStmt, honestSheChildProofs,
      decide_eq_true_iff]; exact ⟨trivial, trivial, by decide, trivial⟩
  · simp only [wearableSheLeafFamily, simplexFinCertSystem, honestSheStmt, honestSheChildProofs,
      decide_eq_true_iff]; decide

/-! ## §4. `#tooth` Falsifiers: Widened Child Relations, Unabsorbed Roots, & Replay Splices -/

noncomputable def widenedAbsentHemSystem : ProofSystem where
  Stmt := (wearableSheBundleSystem 0 0 0 le_rfl le_rfl le_rfl).Stmt
  Wit := (wearableSheBundleSystem 0 0 0 le_rfl le_rfl le_rfl).Proof
  Proof := List Dregg180Instr
  Rel := fun _ _ => True
  Verify := fun _ _ => false
  err := 0
  err_nonneg := le_rfl

/-- **`#tooth` 1 — Widened Child Relation Refuses `VerifierEmbedding`.** -/
theorem widened_child_leaf_refuses_hem_embedding_tooth :
    IsEmpty (VerifierEmbedding
      (wearableSheBundleSystem 0 0 0 le_rfl le_rfl le_rfl) widenedAbsentHemSystem) := by
  constructor; intro e
  let impossibleStmt : (wearableSheBundleSystem 0 0 0 le_rfl le_rfl le_rfl).Stmt := fun i =>
    match i with
    | ⟨0, _⟩ => honestSheStmt ⟨0, by decide⟩
    | ⟨1, _⟩ => honestSheStmt ⟨1, by decide⟩
    | ⟨2, _⟩ => ({ n := 2, f := 1, view := 7, contentTag := 42 } : SimplexFinCertStmt)
  obtain ⟨π, -, hacc⟩ := e.bwd impossibleStmt honestSheChildProofs trivial
  have hall := (conjunctiveLeaf_verify_iff
    (wearableSheLeafFamily 0 0 0 le_rfl le_rfl le_rfl) impossibleStmt π).mp hacc
  have h2 := hall ⟨2, by decide⟩
  simp only [wearableSheLeafFamily, simplexFinCertSystem, impossibleStmt, decide_eq_true_iff] at h2
  omega

def isAbsorbRoot : Dregg180Instr → Bool
  | .OP_ABSORB_ROOT _ _ => true
  | _ => false

/-- **`#tooth` 2a — Unabsorbed Child Root Rejected by `Dregg180VmState`.** -/
theorem unabsorbed_child_root_rejected_tooth (prog : List Dregg180Instr)
    (hCount : (prog.filter isAbsorbRoot).length < demoPinnedHemStmt.leafClaims.length) :
    dregg180VerifyStream canonicalTestOracle demoPinnedHemStmt prog = false := by
  by_contra htr
  have hall := (dregg180Verify_requires_all_leaves_absorbed canonicalTestOracle demoPinnedHemStmt
    prog (Bool.eq_true_of_not_eq_false htr)).1
  have hbound : ∀ (p : List Dregg180Instr) (st : Dregg180VmState),
      (dregg180RunFrom canonicalTestOracle demoPinnedHemStmt st p).absorbedLeaves ≤
        st.absorbedLeaves + (p.filter isAbsorbRoot).length := by
    intro p; induction p with
    | nil => intro _; simp [dregg180RunFrom]
    | cons ins rest ih =>
      intro st
      have hstep : (dregg180Step canonicalTestOracle demoPinnedHemStmt st ins).absorbedLeaves ≤
          st.absorbedLeaves + (if isAbsorbRoot ins then 1 else 0) := by
        by_cases hfin : st.finalAsserted = true
        · simp only [dregg180Step, hfin, ↓reduceIte]; omega
        · cases ins with
          | OP_ABSORB_ROOT slot claim =>
            simp only [dregg180Step, hfin, Bool.false_eq_true, ↓reduceIte, isAbsorbRoot]
            split_ifs <;> omega
          | _ =>
            simp only [dregg180Step, hfin, Bool.false_eq_true, ↓reduceIte, isAbsorbRoot]; omega
      have hrest := ih (dregg180Step canonicalTestOracle demoPinnedHemStmt st ins)
      cases h : isAbsorbRoot ins <;>
        simp only [dregg180RunFrom, List.foldl_cons, List.filter_cons, h, Bool.false_eq_true,
          ↓reduceIte, List.length_cons] at hstep hrest ⊢ <;> omega
  have h0 := hbound prog (dregg180InitState canonicalTestOracle demoPinnedHemStmt)
  simp only [dregg180InitState, zero_add] at h0
  change (dregg180Run canonicalTestOracle demoPinnedHemStmt prog).absorbedLeaves ≤ _ at h0
  omega

def demoForgedStmt : Dregg180HemStmt :=
  let forgedClaim1 : DeferredLeafClaim :=
    ⟨.tower256AbsentDfa, GlExt4.ofBase 999, GlExt4.ofBase 666, GlExt4.zero⟩
  { demoPinnedHemStmt with
    leafClaims := [demoPinnedHemStmt.leafClaims[0]!, forgedClaim1, demoPinnedHemStmt.leafClaims[2]!] }

/-- **`#tooth` 2b — Swapped Child `DeferredLeafClaim` Root Rejected.** -/
theorem unabsorbed_root_breaks_binding_tooth :
    demoForgedStmt ≠ demoPinnedHemStmt ∧
    dregg180VerifyStream canonicalTestOracle demoForgedStmt demoValidStream = false :=
  ⟨by decide, by decide⟩

/-- **`#tooth` 3a — Transcript-Replay, Post-Final Splice, & Zero-Assertion Rejected.** -/
theorem transcript_replay_splice_rejected_tooth :
    dregg180VerifyStream canonicalTestOracle demoPinnedHemStmt [] = false ∧
    dregg180VerifyStream canonicalTestOracle demoPinnedHemStmt
      (demoValidStream ++ [.OP_SUMCHECK_ROUND GlExt4.zero GlExt4.zero GlExt4.zero GlExt4.zero]) = false ∧
    dregg180VerifyStream canonicalTestOracle
      { demoPinnedHemStmt with pinnedProgramDigest := GlExt4.zero } demoValidStream = false :=
  ⟨by decide, by decide, by decide⟩

def demoForgedIdxStream : List Dregg180Instr :=
  demoValidStream.map (fun ins =>
    match ins with | .OP_CANOPY_PATH _ sibs => .OP_CANOPY_PATH 1 sibs | other => other)

/-- **`#tooth` 3b — Forged Merkle Leaf Index (`H_BIND_IDX` Bypass) Rejected.** -/
theorem forged_merkle_index_rejected_tooth :
    dregg180VerifyStream canonicalTestOracle demoPinnedHemStmt demoForgedIdxStream = false := by
  decide

/-- **`#tooth` 3c — `"sk-"` Secret Leak Deterministically Trips `noSkDash` Sink.** -/
theorem sk_dash_payload_refuted_tooth :
    ¬ (tower256AbsentSystem 0 le_rfl).Rel { contentTag := 42, towerRoot := fun _ => 0 } [115, 107, 45] ∧
    ¬ (tower256AbsentSystem 0 le_rfl).Rel { contentTag := 42, towerRoot := fun _ => 0 } [120, 115, 107, 45, 57] := by
  simp only [tower256AbsentSystem]; exact ⟨by decide, by decide⟩

/-! ## §5. `#guard_msgs`-Pinned `#print axioms` Audit -/

/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.goldilocksModulus_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goldilocksModulus_prime
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.goldilocksExt4Poly_irreducible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goldilocksExt4Poly_irreducible
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.goldilocksExt4_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goldilocksExt4_finrank
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.GlExt4.toExt4_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GlExt4.toExt4_mul
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.GlExt4.toExt4_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GlExt4.toExt4_injective
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.dregg180StaticRamBytes_le_16KiB' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms dregg180StaticRamBytes_le_16KiB
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.dregg180RunFrom_spongeSeq_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dregg180RunFrom_spongeSeq_monotone
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.dregg180Verify_requires_all_leaves_absorbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dregg180Verify_requires_all_leaves_absorbed
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.heteroMultiLeaf_composeErrorBoundStrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms heteroMultiLeaf_composeErrorBoundStrict
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.wearableShe_dregg180_end_to_end_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wearableShe_dregg180_end_to_end_soundness
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.wearableShe_honest_bundle_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wearableShe_honest_bundle_accepted
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.widened_child_leaf_refuses_hem_embedding_tooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms widened_child_leaf_refuses_hem_embedding_tooth
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.unabsorbed_child_root_rejected_tooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unabsorbed_child_root_rejected_tooth
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.unabsorbed_root_breaks_binding_tooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unabsorbed_root_breaks_binding_tooth
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.transcript_replay_splice_rejected_tooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transcript_replay_splice_rejected_tooth
/-- info: 'Minidregg.Selvage.GoldilocksDregg180Bridge.forged_merkle_index_rejected_tooth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms forged_merkle_index_rejected_tooth

end Minidregg.Selvage.GoldilocksDregg180Bridge
