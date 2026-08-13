/-
# `Compiler/SumcheckConformance.lean` — `[PROVER-sumcheck]`'s conformance vector

**Substrate, said out loud: this file is a verified-side reference computation for the
seam.** The UNVERIFIED Rust prover (`prover/src/sumcheck.rs`) re-computes
`Selvage/MultilinearExtension.lean`'s `mle` (WHIR Def 4.5's `f̂`) and `roundSum` (the round
polynomial `gᵢ`); Rust has no formal semantics, so the seam is a CONFORMANCE VECTOR:
this file instantiates the REAL `mle`/`roundSum` at a fixed `m = 3` table over BabyBear
(`[PROVER-field]`), KERNEL-DECIDES the reference values, and writes table + challenges +
values to `prover/testdata/sumcheck_conformance.json`; the Rust test reproduces them
with its own `mle_eval`/`round_sum`. Agreement on the vector is the whole claim — never
refinement. The soundness content stays entirely on the Lean side
(`mle_sumcheck_soundness`, `roundSum_zero`/`_succ`/`_last`, `roundSum_affine`).

## The vector's teeth

* **Index convention pinned**: the table is serialized LSB-first — `bitsToIdx b =
  Σᵢ (if bᵢ then 2^i else 0)`, index bit `i` = cube coordinate `i`, round `i` binds
  coordinate `i`. All 8 table values are distinct, so an MSB/LSB flip in the Rust
  reader permutes the table and fails the vector.
* **`m = 3` has an INTERIOR round**: round 1 carries a non-boolean challenge prefix
  AND a boolean suffix corner at once — the full `glue` wiring; `m = 2` never
  exercises both sides of a round simultaneously.
* **`t = 2` evals**: each round is serialized at `t ∈ {0, 1, 2}`; the off-boolean
  point checks the Rust round evaluation agrees with the Lean `roundSum` beyond the
  two points that define the affine message (`roundSum_affine` exercised cross-side).
* **The chain identities are THEOREMS here** (`scChain0`/`scChainSucc`/`scChainLast`
  below — `roundSum_zero`/`_succ`/`_last` instantiated at this table, not re-proved);
  the Rust side EXERCISES the same identities numerically on the vector.

The Lean side is the only author of `prover/testdata/sumcheck_conformance.json`;
Rust only reads. `Selvage/` cannot host this file — the import boundary
(`scripts/check-import-boundary.sh`) rightly keeps `Lean.Data.Json` out of the proof
layer — so it lives here beside `EmitSerialize`, the seam's serialization home.
-/
import Compiler.EmitSerialize
import Selvage.MultilinearExtension

namespace Minidregg.Compiler

open Minidregg.Selvage
open Lean (Json ToJson toJson)

/-! ## §1. The fixed instance: table, challenges, probe point -/

/-- LSB-first corner index: bit `i` of the index is cube coordinate `i` — the
serialization order of the table, and the convention the Rust reader mirrors. -/
def bitsToIdx {m : ℕ} (b : Fin m → Bool) : ℕ :=
  ∑ i : Fin m, if b i then 2 ^ (i : ℕ) else 0

/-- The conformance table: 8 distinct values over BabyBear, far from the field's
edges (one at `p − 1` to exercise the modulus), asymmetric under index
bit-reversal so the vector pins the index convention. -/
def scTable : List BabyBear :=
  [123456789, 987654321, 555555555, 2013265920, 42, 777000777, 31415926, 271828182]

/-- The table as a hypercube function `(Fin 3 → Bool) → BabyBear` via `bitsToIdx`. -/
def scF : (Fin 3 → Bool) → BabyBear := fun b => scTable.getD (bitsToIdx b) 0

/-- The fixed challenge vector (Fiat-Shamir drawing is `[PROVER-fs]`, not this
rung): three distinct non-boolean points. -/
def scR : Fin 3 → BabyBear := ![111111111, 222222222, 1999999999]

/-- An extra off-cube probe point, pinning `mle` alone (no round structure). -/
def scExtra : Fin 3 → BabyBear := ![12345, 67890, 424242]

/-! ## §2. The chain identities, instantiated (theorems, not new proofs) -/

/-- `roundSum_zero` at this instance: `g₀(0) + g₀(1)` = the claimed total
`Σ_b scF b` (via `mle_hypercube_sum`). The Rust test checks the same identity
numerically on the serialized values. -/
theorem scChain0 :
    roundSum (mle scF) scR ⟨0, by norm_num⟩ 0 + roundSum (mle scF) scR ⟨0, by norm_num⟩ 1
      = ∑ b, scF b :=
  (roundSum_zero (by norm_num) (mle scF) scR).trans (mle_hypercube_sum scF).symm

/-- `roundSum_succ` at this instance: `g₁(0) + g₁(1) = g₀(r₀)`. -/
theorem scChainSucc0 :
    roundSum (mle scF) scR ⟨1, by norm_num⟩ 0 + roundSum (mle scF) scR ⟨1, by norm_num⟩ 1
      = roundSum (mle scF) scR ⟨0, by norm_num⟩ (scR ⟨0, by norm_num⟩) :=
  roundSum_succ (by norm_num) (mle scF) scR

/-- `roundSum_succ` again: `g₂(0) + g₂(1) = g₁(r₁)`. -/
theorem scChainSucc1 :
    roundSum (mle scF) scR ⟨2, by norm_num⟩ 0 + roundSum (mle scF) scR ⟨2, by norm_num⟩ 1
      = roundSum (mle scF) scR ⟨1, by norm_num⟩ (scR ⟨1, by norm_num⟩) :=
  roundSum_succ (by norm_num) (mle scF) scR

/-- `roundSum_last` at this instance: the final fold `g₂(r₂)` IS the full MLE
evaluation `f̂(r)` — the terminal oracle check target. -/
theorem scChainLast :
    roundSum (mle scF) scR ⟨2, by norm_num⟩ (scR ⟨2, by norm_num⟩) = mle scF scR := by
  have h := roundSum_last (i := (⟨2, by norm_num⟩ : Fin 3)) rfl (mle scF) scR
    (scR ⟨2, by norm_num⟩)
  rwa [Function.update_eq_self] at h

/-! ## §3. The reference values, KERNEL-DECIDED

The numbers the JSON carries, pinned in the kernel (`by decide`) so the writer
cannot drift from what the type-checker computed. -/

/-- The claimed total `Σ_b scF b`, decided. -/
example : (∑ b, scF b) = 733645670 := by decide

/-- `f̂` at the challenge point — the final oracle value, decided. -/
example : mle scF scR = 22389050 := by decide

/-- `f̂` at the extra probe point, decided. -/
example : mle scF scExtra = 645622878 := by decide

/-- Round 0's message at `t ∈ {0,1,2}`, decided. -/
example :
    (roundSum (mle scF) scR ⟨0, by norm_num⟩ 0,
     roundSum (mle scF) scR ⟨0, by norm_num⟩ 1,
     roundSum (mle scF) scR ⟨0, by norm_num⟩ 2)
      = (710428312, 23217358, 1349272325) := by decide

/-- Round 1's message at `t ∈ {0,1,2}`, decided. -/
example :
    (roundSum (mle scF) scR ⟨1, by norm_num⟩ 0,
     roundSum (mle scF) scR ⟨1, by norm_num⟩ 1,
     roundSum (mle scF) scR ⟨1, by norm_num⟩ 2)
      = (1100467620, 1217552018, 1334636416) := by decide

/-- Round 2's message at `t ∈ {0,1,2}`, decided. -/
example :
    (roundSum (mle scF) scR ⟨2, by norm_num⟩ 0,
     roundSum (mle scF) scR ⟨2, by norm_num⟩ 1,
     roundSum (mle scF) scR ⟨2, by norm_num⟩ 2)
      = (1422434450, 576864271, 1744560013) := by decide

/-! ## §4. The writer — same discipline as the Poseidon vector -/

/-- Round `i`'s serialized message: `[gᵢ(0), gᵢ(1), gᵢ(2)]`. -/
def scRoundJson (i : Fin 3) : Json :=
  Json.arr <|
    (([0, 1, 2] : List BabyBear).map fun t => toJson (roundSum (mle scF) scR i t).val).toArray

/-- The whole conformance file: field, dimension, table (LSB-first), challenges,
claim, per-round messages, and the two MLE probe values — all computed from the
REAL Selvage `mle`/`roundSum` (the values the decided examples above pin). -/
def sumcheckConformanceJson : Json :=
  Json.mkObj
    [ ("p", toJson babyBearP),
      ("m", toJson (3 : ℕ)),
      ("table", Json.arr (scTable.map fun v => toJson v.val).toArray),
      ("challenges", finVecToJson scR),
      ("claim", toJson (∑ b, scF b).val),
      ("rounds", Json.arr ((List.finRange 3).map scRoundJson).toArray),
      ("mleAtChallenges", toJson (mle scF scR).val),
      ("extraPoint", finVecToJson scExtra),
      ("mleAtExtraPoint", toJson (mle scF scExtra).val) ]

/-- Write the conformance file (creating the parent directory; repo-root-relative). -/
def writeSumcheckConformance (path : System.FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (sumcheckConformanceJson.pretty ++ "\n")

#eval writeSumcheckConformance "prover/testdata/sumcheck_conformance.json"

end Minidregg.Compiler
