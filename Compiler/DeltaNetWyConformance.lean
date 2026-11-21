/-
# `Compiler/DeltaNetWyConformance.lean` — Division-Free Chunkwise WY Gated DeltaNet Conformance Vector

**Substrate, said out loud: this file is a verified-side reference computation for the seam.**
The unverified Rust prover re-computes the division-free chunkwise WY representation of
`Theory/ZkmlDeltaNet.lean` over BabyBear (`p = 2013265921`) at a fixed `C = 4, d_k = 2, d_v = 2`
instance. Rust has no formal semantics, so the seam is a CONFORMANCE VECTOR: this file defines
the division-free WY chunkwise operators over any `[CommRing R]`, instantiates
`Theory.ZkmlDeltaNet.wyChunk_bilinear_iff_recurrence` and `strictLowerTri_pow_card_eq_zero`,
KERNEL-DECIDES (`by decide`) exact agreement with the 4-step sequential `gdnStep`/`gdnReadout`
recurrence and every serialized matrix value, and writes `prover/testdata/deltanet_wy_conformance.json`.

## The vector's teeth

* **Explicit zero-decay step (`wyAlpha 1 = 0`)**: proves division-free correctness where
  `γ_i / γ_j` formulations divide by zero, while `wyAlpha 0 = 3 ≠ 0` keeps `γ_0 ≠ 0` so `W` and
  the non-zero initial state `wySInit` are genuinely exercised at step 0 and cleared at step 1.
* **Tight non-trivial nilpotency (`wyL ^ 2 ≠ 0 ∧ wyL ^ 4 = 0`)**: `wyAlpha 2 = 5, wyAlpha 3 = 7`
  keep the lower-right `3 × 3` sub-block of `wyL` genuinely degree-2 coupled, so a broken 1-term
  approximation `I - L` fails immediately.
* **Near-modulus BabyBear inputs** (`2013265918 = -3`, `2013265910 = -11`, `2013265915 = -6`):
  exercise canonical modular wrap-around in both sequential and chunkwise paths.
* **Falsifier tooth (`wyNonStrictLower_babybear_falsifier`)**: perturbing ONLY `L_bad 0 0 = -1`
  (`2013265920`) destroys `IsStrictLowerTri` and yields distinct `U₁ ≠ U₂` with identical
  `(1 + L_bad) * U₁ = (1 + L_bad) * U₂`.

The Lean side is the only author of `prover/testdata/deltanet_wy_conformance.json`; Rust only reads.
-/
import Compiler.SumcheckConformance
import Theory.ZkmlDeltaNet

namespace Minidregg.Compiler

open Minidregg.Theory.ZkmlDeltaNet
open Matrix
open Lean (Json ToJson toJson)

/-! ## §1. Division-Free Chunkwise WY Definitions over `[CommRing R]` -/

section GenericWY

variable {R : Type*} [CommRing R] {C dk dv : ℕ}

/-- Cumulative decay product from chunk start through step `i`: `γ_i = ∏_{m ≤ i} α_m`. -/
def wyGamma (α : Fin C → R) (i : Fin C) : R :=
  ∏ m ∈ Finset.univ.filter (· ≤ i), α m

/-- Suffix decay product from after step `j` to chunk end: `γ̄_j = ∏_{m > j} α_m`. -/
def wyBarGamma (α : Fin C → R) (j : Fin C) : R :=
  ∏ m ∈ Finset.univ.filter (j < ·), α m

/-- Division-free pairwise decay matrix `Γ_{i,j} = ∏_{j < m ≤ i} α_m` for `j ≤ i`, else `0`.
Requires zero field inversions and remains well-defined even when some `α_m = 0`. -/
def wyCapGamma (α : Fin C → R) : Matrix (Fin C) (Fin C) R :=
  Matrix.of fun i j =>
    if j ≤ i then
      ∏ m ∈ Finset.univ.filter (fun m => j < m ∧ m ≤ i), α m
    else
      0

/-- Strictly lower-triangular chunk coupling matrix
`L_{i,j} = β_i · Γ_{i,j} · ⟨K_i, K_j⟩` for `j < i`, else `0`. -/
def wyCouplingL (α β : Fin C → R) (K : Fin C → Fin dk → R) : Matrix (Fin C) (Fin C) R :=
  Matrix.of fun i j =>
    if j < i then
      β i * wyCapGamma α i j * dotProduct (K i) (K j)
    else
      0

/-- **Structural soundness**: `wyCouplingL α β K` is always strictly lower triangular over any
`CommRing R`, discharging the `IsStrictLowerTri` hypothesis of `wyChunk_bilinear_iff_recurrence`. -/
theorem wyCouplingL_strictLower (α β : Fin C → R) (K : Fin C → Fin dk → R) :
    IsStrictLowerTri (wyCouplingL α β K) := by
  intro i j hij
  simp [wyCouplingL, not_lt.mpr hij]

/-- Write-gate-scaled value matrix `(V_β)_{i,c} = β_i · V_{i,c}`. -/
def wyVbetaMat (β : Fin C → R) (V : Fin C → Fin dv → R) : Matrix (Fin C) (Fin dv) R :=
  Matrix.of fun i c => β i * V i c

/-- Decay-and-write-scaled key matrix `(K_{γβ})_{i,r} = β_i · γ_i · K_{i,r}`. -/
def wyKgammaBetaMat (α β : Fin C → R) (K : Fin C → Fin dk → R) : Matrix (Fin C) (Fin dk) R :=
  Matrix.of fun i r => β i * wyGamma α i * K i r

/-- Horizontally stacked WY right-hand side `[V_β | K_{γβ}] ∈ R^{C × (d_v + d_k)}`.
Columns `0 .. dv-1` hold `V_β`; columns `dv .. dv+dk-1` hold `K_{γβ}`. -/
def wyRHSMat (α β : Fin C → R) (K : Fin C → Fin dk → R) (V : Fin C → Fin dv → R) :
    Matrix (Fin C) (Fin (dv + dk)) R :=
  Matrix.of fun i col =>
    if h : col.val < dv then
      wyVbetaMat β V i ⟨col.val, h⟩
    else
      wyKgammaBetaMat α β K i ⟨col.val - dv, by omega⟩

/-- Stacked WY factor `[U | W] := neumannInv L * [V_β | K_{γβ}]`. -/
def wyUWMat (α β : Fin C → R) (K : Fin C → Fin dk → R) (V : Fin C → Fin dv → R) :
    Matrix (Fin C) (Fin (dv + dk)) R :=
  neumannInv (wyCouplingL α β K) * wyRHSMat α β K V

/-- Value WY factor `U ∈ R^{C × d_v}` (left `d_v` columns of `wyUWMat`). -/
def wyUMat (α β : Fin C → R) (K : Fin C → Fin dk → R) (V : Fin C → Fin dv → R) :
    Matrix (Fin C) (Fin dv) R :=
  Matrix.of fun i c => wyUWMat α β K V i ⟨c.val, by omega⟩

/-- State-coupling WY factor `W ∈ R^{C × d_k}` (right `d_k` columns of `wyUWMat`). -/
def wyWMat (α β : Fin C → R) (K : Fin C → Fin dk → R) (V : Fin C → Fin dv → R) :
    Matrix (Fin C) (Fin dk) R :=
  Matrix.of fun i r => wyUWMat α β K V i ⟨dv + r.val, by omega⟩

/-- Effective write updates `U_eff = U - W * S_init ∈ R^{C × d_v}`. -/
def wyUEffMat (α β : Fin C → R) (K : Fin C → Fin dk → R) (V : Fin C → Fin dv → R)
    (SInit : Matrix (Fin dk) (Fin dv) R) : Matrix (Fin C) (Fin dv) R :=
  wyUMat α β K V - wyWMat α β K V * SInit

/-- Chunkwise WY readout outputs `Y_out ∈ R^{C × d_v}`:
`(Y_out)_{i,c} = γ_i · (Q_i · S_init[:,c]) + ∑_j Γ_{i,j} · ⟨Q_i, K_j⟩ · (U_eff)_{j,c}`. -/
def wyYOutMat (α β : Fin C → R) (Q K : Fin C → Fin dk → R) (V : Fin C → Fin dv → R)
    (SInit : Matrix (Fin dk) (Fin dv) R) : Matrix (Fin C) (Fin dv) R :=
  let Ueff := wyUEffMat α β K V SInit
  let capG := wyCapGamma α
  Matrix.of fun i c =>
    wyGamma α i * (∑ r : Fin dk, Q i r * SInit r c) +
      ∑ j : Fin C, capG i j * dotProduct (Q i) (K j) * Ueff j c

/-- Chunkwise WY final recurrent state `S_final ∈ R^{d_k × d_v}`:
`(S_final)_{r,c} = (∏_m α_m) · (S_init)_{r,c} + ∑_j γ̄_j · K_{j,r} · (U_eff)_{j,c}`. -/
def wySFinalMat (α β : Fin C → R) (K : Fin C → Fin dk → R) (V : Fin C → Fin dv → R)
    (SInit : Matrix (Fin dk) (Fin dv) R) : Matrix (Fin dk) (Fin dv) R :=
  let Ueff := wyUEffMat α β K V SInit
  let bg := wyBarGamma α
  let gAll : R := ∏ m : Fin C, α m
  Matrix.of fun r c =>
    gAll * SInit r c + ∑ j : Fin C, bg j * K j r * Ueff j c

/-- Sequential `GDN` state executor using `Theory.ZkmlDeltaNet.gdnStep`, structurally recursive
on the step index `t < C`. -/
def gdnSeqStateAt (α β : Fin C → R) (K : Fin C → Fin dk → R) (V : Fin C → Fin dv → R)
    (SInit : Matrix (Fin dk) (Fin dv) R) : (t : ℕ) → t < C → Matrix (Fin dk) (Fin dv) R
  | 0, h => gdnStep (α ⟨0, h⟩) (β ⟨0, h⟩) (K ⟨0, h⟩) (V ⟨0, h⟩) SInit
  | t + 1, h =>
      gdnStep (α ⟨t + 1, h⟩) (β ⟨t + 1, h⟩) (K ⟨t + 1, h⟩) (V ⟨t + 1, h⟩)
        (gdnSeqStateAt α β K V SInit t (by omega))

end GenericWY

/-! ## §2. Fixed BabyBear (`ZMod 2013265921`) Instance (`C = 4, dk = 2, dv = 2`) -/

/-- Decay gates with an explicit zero step at `t = 1` (`wyAlpha 1 = 0`), while `wyAlpha 0, 2, 3 ≠ 0`
keep both `γ_0 ≠ 0` (exercising `W` and `wySInit`) and `wyL ^ 2 ≠ 0` (tight non-trivial coupling). -/
def wyAlpha : Fin 4 → BabyBear := ![3, 0, 5, 7]

/-- Write gates `β`. -/
def wyBeta : Fin 4 → BabyBear := ![2, 11, 13, 17]

/-- Query vectors `Q ∈ BabyBear^{4 × 2}`. -/
def wyQ : Fin 4 → Fin 2 → BabyBear :=
  ![![19, 23], ![29, 31], ![37, 41], ![43, 47]]

/-- Key vectors `K ∈ BabyBear^{4 × 2}` (includes `2013265918 = -3`). -/
def wyK : Fin 4 → Fin 2 → BabyBear :=
  ![![5, 9], ![12, 8], ![2013265918, 6], ![4, 15]]

/-- Value vectors `V ∈ BabyBear^{4 × 2}` (includes `2013265910 = -11`). -/
def wyV : Fin 4 → Fin 2 → BabyBear :=
  ![![101, 202], ![303, 404], ![505, 2013265910], ![707, 808]]

/-- Non-zero initial state `S_init ∈ BabyBear^{2 × 2}` (includes `2013265915 = -6`). -/
def wySInit : Matrix (Fin 2) (Fin 2) BabyBear :=
  Matrix.of ![![1000, 2000], ![3000, 2013265915]]

/-- Concrete strictly lower-triangular coupling matrix `L`. -/
def wyL : Matrix (Fin 4) (Fin 4) BabyBear :=
  wyCouplingL wyAlpha wyBeta wyK

/-- Concrete `V_β ∈ BabyBear^{4 × 2}`. -/
def wyVbeta : Matrix (Fin 4) (Fin 2) BabyBear :=
  wyVbetaMat wyBeta wyV

/-- Concrete `K_{γβ} ∈ BabyBear^{4 × 2}`. -/
def wyKgammaBeta : Matrix (Fin 4) (Fin 2) BabyBear :=
  wyKgammaBetaMat wyAlpha wyBeta wyK

/-- Concrete stacked RHS `[V_β | K_{γβ}] ∈ BabyBear^{4 × 4}`. -/
def wyRHS : Matrix (Fin 4) (Fin 4) BabyBear :=
  wyRHSMat wyAlpha wyBeta wyK wyV

/-- Concrete stacked WY factor `[U | W] = neumannInv wyL * wyRHS ∈ BabyBear^{4 × 4}`. -/
def wyUW : Matrix (Fin 4) (Fin 4) BabyBear :=
  wyUWMat wyAlpha wyBeta wyK wyV

/-- Concrete `U ∈ BabyBear^{4 × 2}`. -/
def wyU : Matrix (Fin 4) (Fin 2) BabyBear :=
  wyUMat wyAlpha wyBeta wyK wyV

/-- Concrete `W ∈ BabyBear^{4 × 2}`. -/
def wyW : Matrix (Fin 4) (Fin 2) BabyBear :=
  wyWMat wyAlpha wyBeta wyK wyV

/-- Concrete effective writes `U_eff = U - W * S_init ∈ BabyBear^{4 × 2}`. -/
def wyUEff : Matrix (Fin 4) (Fin 2) BabyBear :=
  wyUEffMat wyAlpha wyBeta wyK wyV wySInit

/-- Concrete chunkwise WY readouts `Y_out ∈ BabyBear^{4 × 2}`. -/
def wyYOut : Matrix (Fin 4) (Fin 2) BabyBear :=
  wyYOutMat wyAlpha wyBeta wyQ wyK wyV wySInit

/-- Concrete chunkwise WY final state `S_final ∈ BabyBear^{2 × 2}`. -/
def wySFinal : Matrix (Fin 2) (Fin 2) BabyBear :=
  wySFinalMat wyAlpha wyBeta wyK wyV wySInit

/-- Concrete 4-step sequential `gdnStep` state trajectory starting from `wySInit`. -/
def wySeqState (t : Fin 4) : Matrix (Fin 2) (Fin 2) BabyBear :=
  gdnSeqStateAt wyAlpha wyBeta wyK wyV wySInit t.val t.isLt

/-- Concrete 4-step sequential `gdnReadout` outputs. -/
def wySeqReadout (t : Fin 4) : Fin 2 → BabyBear :=
  gdnReadout (wyQ t) (wySeqState t)

/-! ## §3. Kernel-Decided & Instantiated Theorems -/

/-- **Zero-decay tooth (`wyAlpha_has_zero_step`)**: step 1 has `α_1 = 0`, ruling out
division-based `γ_i / γ_j` implementations. -/
theorem wyAlpha_has_zero_step : wyAlpha 1 = 0 := by
  decide

/-- **Tight nilpotency (`wyL_nilpotency_tight`)**: `wyL ^ 2 ≠ 0` (the lower-right `3 × 3`
block has genuine second-order coupling) while `wyL ^ 4 = 0` via `strictLowerTri_pow_card_eq_zero`. -/
theorem wyL_nilpotency_tight : wyL ^ 2 ≠ 0 ∧ wyL ^ 4 = 0 :=
  ⟨by decide, strictLowerTri_pow_card_eq_zero (wyCouplingL_strictLower wyAlpha wyBeta wyK)⟩

/-- **WY Bilinear-to-Recurrence Equivalence (`wyU_bilinear_and_recurrence`)**:
instantiates `Theory.ZkmlDeltaNet.wyChunk_bilinear_iff_recurrence` at `wyL` together with
kernel-decided witnesses for both `wyU` and stacked `wyUW`, pinning the flat degree-2 bilinear
identities, closed-form Neumann inverses, and sequential causal forward-substitution recurrences. -/
theorem wyU_bilinear_and_recurrence :
    (1 + wyL) * wyU = wyVbeta ∧
    wyU = neumannInv wyL * wyVbeta ∧
    (∀ i : Fin 4, ∀ col : Fin 2,
      wyU i col = wyVbeta i col - ∑ j ∈ Finset.univ.filter (· < i), wyL i j * wyU j col) ∧
    (1 + wyL) * wyUW = wyRHS ∧
    wyUW = neumannInv wyL * wyRHS ∧
    (∀ i : Fin 4, ∀ col : Fin 4,
      wyUW i col = wyRHS i col - ∑ j ∈ Finset.univ.filter (· < i), wyL i j * wyUW j col) := by
  have hL : IsStrictLowerTri wyL := wyCouplingL_strictLower wyAlpha wyBeta wyK
  have hU_eq : wyU = neumannInv wyL * wyVbeta := by decide
  have hUW_eq : wyUW = neumannInv wyL * wyRHS := rfl
  obtain ⟨hU_bilin, hU_rec⟩ := wyChunk_bilinear_iff_recurrence hL wyU wyVbeta
  obtain ⟨hUW_bilin, hUW_rec⟩ := wyChunk_bilinear_iff_recurrence hL wyUW wyRHS
  exact ⟨hU_bilin.mpr hU_eq, hU_eq, hU_rec.mp hU_eq,
         hUW_bilin.mpr hUW_eq, hUW_eq, hUW_rec.mp hUW_eq⟩

/-- **Sequential-vs-Chunkwise Exact Agreement (`wySequential_agrees_with_chunkwise`)**:
the 4-step sequential `gdnStep` + `gdnReadout` recurrence starting from `wySInit` agrees on the
nose with `(wyYOut, wySFinal)` at every step `t ∈ Fin 4` and at the final state `S_3`. -/
theorem wySequential_agrees_with_chunkwise :
    (∀ t : Fin 4, ∀ c : Fin 2, wySeqReadout t c = wyYOut t c) ∧
    wySeqState ⟨3, by omega⟩ = wySFinal := by
  have hY : Matrix.of wySeqReadout = wyYOut := by decide
  have hS : wySeqState ⟨3, by omega⟩ = wySFinal := by decide
  exact ⟨fun t c => congrFun (congrFun hY t) c, hS⟩

/-! ### Exact Numeric Value Pins (Kernel-Decided) -/

/-- Exact BabyBear value of `wyL`, kernel-decided. -/
theorem wyL_value :
    wyL = Matrix.of ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 780, 0, 0], ![0, 99960, 9282, 0]] := by
  decide

/-- Exact BabyBear value of `neumannInv wyL`, kernel-decided. -/
theorem wyNeumannInvL_value :
    neumannInv wyL =
      Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0],
                  ![0, 2013265141, 1, 0], ![0, 7140000, 2013256639, 1]] := by
  decide

/-- Exact BabyBear value of stacked `wyUW = [U | W]`, kernel-decided. -/
theorem wyUW_value :
    wyUW =
      Matrix.of ![![202, 404, 30, 54],
                  ![3333, 4444, 0, 0],
                  ![2010672746, 2009799458, 0, 0],
                  ![1590770558, 1532512247, 0, 0]] := by
  decide

/-- Exact BabyBear value of chunkwise readout `wyYOut`, kernel-decided. -/
theorem wyYOut_value :
    wyYOut =
      Matrix.of ![![1955606925, 1995479363],
                  ![1986468, 2648624],
                  ![1676052676, 1562447256],
                  ![1265793790, 1617562961]] := by
  decide

/-- Exact BabyBear value of chunkwise final state `wySFinal`, kernel-decided. -/
theorem wySFinal_value :
    wySFinal =
      Matrix.of ![![379141004, 164913428],
                  ![1607653129, 697411448]] := by
  decide

/-! ### Falsifier Tooth over BabyBear -/

/-- **Falsifier Tooth (`wyNonStrictLower_babybear_falsifier`)**:
violating `IsStrictLowerTri` at ONLY the `(0, 0)` diagonal entry (`L_bad 0 0 = -1 = 2013265920`)
while keeping all strict-lower entries of `wyL` intact destroys uniqueness of the bilinear check:
two distinct matrices `U₁ ≠ U₂` satisfy `(1 + L_bad) * U₁ = (1 + L_bad) * U₂`. -/
theorem wyNonStrictLower_babybear_falsifier :
    let L_bad : Matrix (Fin 4) (Fin 4) BabyBear :=
      Matrix.of fun i j => if i = 0 ∧ j = 0 then (2013265920 : BabyBear) else wyL i j
    let U₁ : Matrix (Fin 4) (Fin 2) BabyBear := wyU
    let U₂ : Matrix (Fin 4) (Fin 2) BabyBear :=
      Matrix.of fun i c => if i = 0 then wyU i c + 1 else wyU i c
    ¬ IsStrictLowerTri L_bad ∧
    U₁ ≠ U₂ ∧
    (1 + L_bad) * U₁ = (1 + L_bad) * U₂ := by
  refine ⟨?_, by decide, by decide⟩
  intro hL
  have h00 :
      (Matrix.of fun i j : Fin 4 =>
        if i = 0 ∧ j = 0 then (2013265920 : BabyBear) else wyL i j) 0 0 = 0 :=
    hL 0 0 (le_refl 0)
  revert h00
  decide

/-! ## §4. JSON Writer (`prover/testdata/deltanet_wy_conformance.json`) -/

/-- Serialize a `Fin m × Fin n` BabyBear matrix in row-major order with canonical `ZMod.val`s. -/
def finMatToJson {m n : ℕ} (M : Matrix (Fin m) (Fin n) BabyBear) : Json :=
  Json.arr ((List.finRange m).map fun i => finVecToJson (M i)).toArray

/-- Serialize a `Fin m → Fin n → BabyBear` row table in row-major order. -/
def finRowsToJson {m n : ℕ} (T : Fin m → Fin n → BabyBear) : Json :=
  Json.arr ((List.finRange m).map fun i => finVecToJson (T i)).toArray

/-- The whole division-free chunkwise WY conformance vector. -/
def deltaNetWyConformanceJson : Json :=
  Json.mkObj
    [ ("p", toJson babyBearP),
      ("c", toJson (4 : ℕ)),
      ("dk", toJson (2 : ℕ)),
      ("dv", toJson (2 : ℕ)),
      ("alpha", finVecToJson wyAlpha),
      ("beta", finVecToJson wyBeta),
      ("q", finRowsToJson wyQ),
      ("k", finRowsToJson wyK),
      ("v", finRowsToJson wyV),
      ("sInit", finMatToJson wySInit),
      ("gamma", finVecToJson (wyGamma wyAlpha)),
      ("barGamma", finVecToJson (wyBarGamma wyAlpha)),
      ("capGamma", finMatToJson (wyCapGamma wyAlpha)),
      ("matrixL", finMatToJson wyL),
      ("neumannInvL", finMatToJson (neumannInv wyL)),
      ("rhs", finMatToJson wyRHS),
      ("uw", finMatToJson wyUW),
      ("yOut", finMatToJson wyYOut),
      ("sFinal", finMatToJson wySFinal) ]

/-- Write the conformance file (creating the parent directory; repo-root-relative). -/
def writeDeltaNetWyConformance (path : System.FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (deltaNetWyConformanceJson.pretty ++ "\n")

#eval writeDeltaNetWyConformance "prover/testdata/deltanet_wy_conformance.json"

/-! ## §5. Axiom Pins (`#guard_msgs`) -/

/-- info: 'Minidregg.Compiler.wyCouplingL_strictLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyCouplingL_strictLower
/-- info: 'Minidregg.Compiler.wyAlpha_has_zero_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyAlpha_has_zero_step
/-- info: 'Minidregg.Compiler.wyL_nilpotency_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyL_nilpotency_tight
/-- info: 'Minidregg.Compiler.wyU_bilinear_and_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyU_bilinear_and_recurrence
/-- info: 'Minidregg.Compiler.wySequential_agrees_with_chunkwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wySequential_agrees_with_chunkwise
/-- info: 'Minidregg.Compiler.wyL_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyL_value
/-- info: 'Minidregg.Compiler.wyNeumannInvL_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyNeumannInvL_value
/-- info: 'Minidregg.Compiler.wyUW_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyUW_value
/-- info: 'Minidregg.Compiler.wyYOut_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyYOut_value
/-- info: 'Minidregg.Compiler.wySFinal_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wySFinal_value
/-- info: 'Minidregg.Compiler.wyNonStrictLower_babybear_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wyNonStrictLower_babybear_falsifier

end Minidregg.Compiler
