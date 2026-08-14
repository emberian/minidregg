/-
# `Assurance/ZkmlMatmulConformance.lean` — the matmul contraction's conformance vector

**Substrate, said out loud: this is a verified-side REFERENCE COMPUTATION for the seam.**
The unverified Rust prover (`prover/src/sumcheck.rs`, the `matmul_*` items) re-computes
`Assurance/ZkmlMatmulSumcheck.lean`'s `mle₂` / `rowPartial` / `colPartial` / `matmulTable`
and drives them through the landed cubic engine. Rust has no formal semantics, so the seam
is a CONFORMANCE VECTOR: this file instantiates the REAL definitions at a fixed
`2×4 · 4×2` BabyBear matmul, KERNEL-DECIDES the reference values, and writes them to
`prover/testdata/zkml_matmul_conformance.json`. Agreement on the vector is the whole claim
— never refinement, never translation validation.

It lives beside its sibling in `Assurance/` for the same reason
`AirSumcheckCubicConformance.lean` does: the objects it binds live here, and a
`Compiler/`-side writer could only re-spell them, which would be a second shape that agrees
today.

## The instance, and why these dimensions

`μ = 1, κ = 2, ν = 1` — a `2×4` times a `4×2`. Small enough to kernel-decide every value,
and it is the smallest instance where the contraction is not a product: the inner cube has
FOUR corners, so the sumcheck runs two rounds and round 0 has a real boolean suffix while
round 1 has a real challenge prefix.

## The vector's teeth

* **The claim is the contraction, not a re-spelling.** `matmulClaim_is_contraction` is
  `matmul_claim_total` instantiated: the total the prover sends IS `Ĉ(x,y)` of the true
  output table. A Rust reader that computed the Hadamard product would fail immediately.
* **⚑ The leading coefficient is ZERO in every round, and that is stated as a THEOREM**
  (`matmulRounds_are_not_cubic`). At the contraction instance the head is constant and the
  second pair is dead, so the round polynomial is genuinely quadratic riding a degree-3
  wire. Saying so in the vector is the honest form of "the rung is not tight here" — and
  the companion `matmulRounds_are_quadratic` pins the SECOND difference nonzero, so a
  reader that fitted an affine message still fails.
* **The four wire nodes are all serialized**, `h(1)` included. A verifier that derived
  `h(1) = claim − h(0)` would have made its round check a tautology.
* **The tables are asymmetric under index bit-reversal**, so the LSB-first convention is
  pinned rather than assumed.
-/
import Assurance.ZkmlMatmulSumcheck
import Compiler.SumcheckConformance

namespace Minidregg.Assurance

open Minidregg.Compiler Minidregg.Selvage
open Lean (Json ToJson toJson)

/-! ## §1. The fixed instance -/

/-- The left operand `A`, a `2×4` matrix: row `i` is `mmA.getD i`, and within a row the
inner index is LSB-first over `{0,1}²`. -/
def mmTableA : List (List BabyBear) :=
  [[11, 2222, 333333, 44444444], [1000000007, 8, 99999999, 1234567]]

/-- The right operand `B`, a `4×2` matrix: inner index outer, column index inner. -/
def mmTableB : List (List BabyBear) :=
  [[7654321, 13], [2013265919, 90210], [5555, 141421356], [17320508, 223606797]]

/-- `A` as a block table on `{0,1}¹ × {0,1}²`. -/
def mmA : (Fin 1 → Bool) → (Fin 2 → Bool) → BabyBear :=
  fun a p => (mmTableA.getD (bitsToIdx a) []).getD (bitsToIdx p) 0

/-- `B` as a block table on `{0,1}² × {0,1}¹`. -/
def mmB : (Fin 2 → Bool) → (Fin 1 → Bool) → BabyBear :=
  fun p b => (mmTableB.getD (bitsToIdx p) []).getD (bitsToIdx b) 0

/-- The outer challenge point for the row index. -/
def mmX : Fin 1 → BabyBear := ![111111111]

/-- The outer challenge point for the column index. -/
def mmY : Fin 1 → BabyBear := ![222222222]

/-- The sumcheck challenges, one per inner-cube variable. -/
def mmR : Fin 2 → BabyBear := ![1999999999, 424242424]

/-- The prover's two folded tables: `Â(x, ·)` and `B̂(·, y)` on the inner cube. -/
def mmG : (Fin 2 → Bool) → BabyBear := rowPartial mmA mmX
def mmH : (Fin 2 → Bool) → BabyBear := colPartial mmB mmY

/-- The head table of the `cubicForm` instance: CONSTANT `1`, no `eq` factor. -/
def mmE : (Fin 2 → Bool) → BabyBear := fun _ => 1
/-- The dead second pair. -/
def mmC : (Fin 2 → Bool) → BabyBear := fun _ => 0
def mmD : (Fin 2 → Bool) → BabyBear := fun _ => 1

/-- The summand: the REAL `cubicForm` at the contraction instance. -/
def mmForm : (Fin 2 → BabyBear) → BabyBear := cubicForm mmE mmG mmH mmC mmD

/-! ## §2. The identities, instantiated (theorems, not new proofs) -/

/-- **The claim IS the contraction.** `matmul_claim_total` at this instance: the total the
prover sends equals `Ĉ(x,y)` of the true output table `A·B`. -/
theorem matmulClaim_is_contraction :
    (∑ p, ((1 : BabyBear) * (mmG p * mmH p + 0 * 1))) = mle₂ (matmulTable mmA mmB) mmX mmY :=
  matmul_claim_total mmA mmB mmX mmY

/-- `roundSum_zero` + `cubicForm_cube_sum`: round 0's boolean check target IS the claim. -/
theorem mmChain0 :
    roundSum mmForm mmR ⟨0, by norm_num⟩ 0 + roundSum mmForm mmR ⟨0, by norm_num⟩ 1
      = ∑ b, (mmE b * (mmG b * mmH b + mmC b * mmD b)) :=
  (roundSum_zero (by norm_num) mmForm mmR).trans (cubicForm_cube_sum mmE mmG mmH mmC mmD)

/-- `roundSum_succ`: `h₁(0) + h₁(1) = h₀(r₀)`. -/
theorem mmChainSucc0 :
    roundSum mmForm mmR ⟨1, by norm_num⟩ 0 + roundSum mmForm mmR ⟨1, by norm_num⟩ 1
      = roundSum mmForm mmR ⟨0, by norm_num⟩ (mmR ⟨0, by norm_num⟩) :=
  roundSum_succ (by norm_num) mmForm mmR

/-- `roundSum_last`: the final fold IS the factored terminal value the verifier combines
from the five openings. -/
theorem mmChainLast :
    roundSum mmForm mmR ⟨1, by norm_num⟩ (mmR ⟨1, by norm_num⟩)
      = mle mmE mmR * (mle mmG mmR * mle mmH mmR + mle mmC mmR * mle mmD mmR) := by
  have h := roundSum_last (i := (⟨1, by norm_num⟩ : Fin 2)) rfl mmForm mmR
    (mmR ⟨1, by norm_num⟩)
  rw [Function.update_eq_self] at h
  exact h

/-! ## §3. The reference values, KERNEL-DECIDED and NAMED -/

/-- The true output table `A·B` on the cube, decided — four entries the Rust reproduces. -/
theorem mmOutput_value :
    (matmulTable mmA mmB (fun _ => false) (fun _ => false),
     matmulTable mmA mmB (fun _ => false) (fun _ => true),
     matmulTable mmA mmB (fun _ => true) (fun _ => false),
     matmulTable mmA mmB (fun _ => true) (fun _ => true))
      = (1873098210, 1225017427, 1060214993, 812018714) := by decide

/-- The two folded tables at the outer point, LSB-first, decided. -/
theorem mmG_value :
    (mmG ![false, false], mmG ![true, false], mmG ![false, true], mmG ![true, true])
      = (1207514882, 1631710751, 100970867, 257853348) := by decide

theorem mmH_value :
    (mmH ![false, false], mmH ![true, false], mmH ![false, true], mmH ![true, true])
      = (721026820, 1022315665, 1385492447, 910150438) := by decide

/-- The claimed total, decided. -/
theorem mmClaim_value :
    (∑ b, (mmE b * (mmG b * mmH b + mmC b * mmD b))) = 1401643469 := by decide

/-- The five FACTORED terminal values, decided. Three are verifier-known constants
`1, 0, 1`, so the sumcheck's terminal face needs TWO operand MLE proofs, not five.
The overall succinct contraction additionally needs the output proof `Ĉ(x,y)`; that is
the third root-bound claim in `Assurance.ZkmlMatmulCommitment`. -/
theorem mmOpenings_value :
    (mle mmE mmR, mle mmG mmR, mle mmH mmR, mle mmC mmR, mle mmD mmR)
      = (1, 2013175046, 1038698509, 0, 1) := by decide

/-- Round 0's message at the four wire nodes, decided. -/
theorem mmRound0_value :
    (roundSum mmForm mmR ⟨0, by norm_num⟩ 0, roundSum mmForm mmR ⟨0, by norm_num⟩ 1,
     roundSum mmForm mmR ⟨0, by norm_num⟩ 2, roundSum mmForm mmR ⟨0, by norm_num⟩ 3)
      = (1223933664, 177709805, 1681418813, 1708528846) := by decide

/-- Round 1's message at the four wire nodes, decided. -/
theorem mmRound1_value :
    (roundSum mmForm mmR ⟨1, by norm_num⟩ 0, roundSum mmForm mmR ⟨1, by norm_num⟩ 1,
     roundSum mmForm mmR ⟨1, by norm_num⟩ 2, roundSum mmForm mmR ⟨1, by norm_num⟩ 3)
      = (1792486389, 184168601, 1183923258, 765218518) := by decide

/-- **⚑ TEETH — the contraction face is NOT cubic.** The third finite difference is `6·k₃`
and it is ZERO in both rounds: the head is constant and the second pair is dead, so the
degree-3 wire is carrying a degree-2 message. This is the honest form of "the rung is not
tight here", stated as a fact about the emitted numbers rather than as prose. -/
theorem matmulRounds_are_not_cubic :
    (roundSum mmForm mmR ⟨0, by norm_num⟩ 3 - 3 * roundSum mmForm mmR ⟨0, by norm_num⟩ 2
       + 3 * roundSum mmForm mmR ⟨0, by norm_num⟩ 1 - roundSum mmForm mmR ⟨0, by norm_num⟩ 0
     = 0)
    ∧ (roundSum mmForm mmR ⟨1, by norm_num⟩ 3 - 3 * roundSum mmForm mmR ⟨1, by norm_num⟩ 2
       + 3 * roundSum mmForm mmR ⟨1, by norm_num⟩ 1 - roundSum mmForm mmR ⟨1, by norm_num⟩ 0
     = 0) := by decide

/-- **TEETH — but it IS quadratic.** The second finite difference is nonzero in both
rounds, so a reader that fitted an affine message (two nodes) fails the vector. Together
with the theorem above, the message's degree is pinned from both sides. -/
theorem matmulRounds_are_quadratic :
    (roundSum mmForm mmR ⟨0, by norm_num⟩ 2 - 2 * roundSum mmForm mmR ⟨0, by norm_num⟩ 1
       + roundSum mmForm mmR ⟨0, by norm_num⟩ 0 ≠ 0)
    ∧ (roundSum mmForm mmR ⟨1, by norm_num⟩ 2 - 2 * roundSum mmForm mmR ⟨1, by norm_num⟩ 1
       + roundSum mmForm mmR ⟨1, by norm_num⟩ 0 ≠ 0) := by decide

/-! ## §4. The writer -/

/-- Round `i`'s serialized message: `[hᵢ(0), hᵢ(1), hᵢ(2), hᵢ(3)]`. `h(1)` is on the wire. -/
def mmRoundJson (i : Fin 2) : Json :=
  Json.arr <| (([0, 1, 2, 3] : List BabyBear).map fun t => toJson (roundSum mmForm mmR i t).val).toArray

/-- A `(Fin n → Bool) → BabyBear` table serialized LSB-first. -/
def mmCubeJson {n : ℕ} (f : (Fin n → Bool) → BabyBear) : Json :=
  Json.arr <|
    ((List.finRange (2 ^ n)).map fun k =>
      toJson (f (fun i => (k.val / 2 ^ (i : ℕ)) % 2 == 1)).val).toArray

/-- The whole matmul conformance file. -/
def matmulConformanceJson : Json :=
  Json.mkObj
    [ ("p", toJson babyBearP),
      ("mu", toJson (1 : ℕ)),
      ("kappa", toJson (2 : ℕ)),
      ("nu", toJson (1 : ℕ)),
      ("degree", toJson (3 : ℕ)),
      ("tableA", Json.arr (mmTableA.map fun row =>
        Json.arr (row.map fun v => toJson v.val).toArray).toArray),
      ("tableB", Json.arr (mmTableB.map fun row =>
        Json.arr (row.map fun v => toJson v.val).toArray).toArray),
      ("x", finVecToJson mmX),
      ("y", finVecToJson mmY),
      ("challenges", finVecToJson mmR),
      ("output", Json.arr
        (([[matmulTable mmA mmB (fun _ => false) (fun _ => false),
            matmulTable mmA mmB (fun _ => false) (fun _ => true)],
           [matmulTable mmA mmB (fun _ => true) (fun _ => false),
            matmulTable mmA mmB (fun _ => true) (fun _ => true)]] : List (List BabyBear)).map
          fun row => Json.arr (row.map fun v => toJson v.val).toArray).toArray),
      ("rowPartial", mmCubeJson mmG),
      ("colPartial", mmCubeJson mmH),
      ("claim", toJson (∑ b, (mmE b * (mmG b * mmH b + mmC b * mmD b))).val),
      ("mle2Output", toJson (mle₂ (matmulTable mmA mmB) mmX mmY).val),
      ("rounds", Json.arr ((List.finRange 2).map mmRoundJson).toArray),
      ("openings", Json.arr
        (([mle mmE mmR, mle mmG mmR, mle mmH mmR, mle mmC mmR, mle mmD mmR] :
            List BabyBear).map fun v => toJson v.val).toArray) ]

/-- Write the conformance file (repo-root-relative). -/
def writeMatmulConformance (path : System.FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (matmulConformanceJson.pretty ++ "\n")

#eval writeMatmulConformance "prover/testdata/zkml_matmul_conformance.json"

/-! ## §5. Axiom pins (house law) -/

/-- info: 'Minidregg.Assurance.matmulClaim_is_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmulClaim_is_contraction
/-- info: 'Minidregg.Assurance.mmChain0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mmChain0
/-- info: 'Minidregg.Assurance.mmChainLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mmChainLast
/-- info: 'Minidregg.Assurance.mmOutput_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mmOutput_value
/-- info: 'Minidregg.Assurance.mmClaim_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mmClaim_value
/-- info: 'Minidregg.Assurance.mmOpenings_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mmOpenings_value
/-- info: 'Minidregg.Assurance.matmulRounds_are_not_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmulRounds_are_not_cubic
/-- info: 'Minidregg.Assurance.matmulRounds_are_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms matmulRounds_are_quadratic

end Minidregg.Assurance
