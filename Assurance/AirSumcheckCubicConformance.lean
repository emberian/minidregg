/-
# `Assurance/AirSumcheckCubicConformance.lean` — the degree-3 conformance vector

**Substrate, said out loud: this is a verified-side REFERENCE COMPUTATION for the seam.**
The unverified Rust prover (`prover/src/sumcheck.rs`, the `cubic_*` items) re-computes
`Assurance/AirSumcheckCubic.lean`'s `cubicForm`/`roundSum` at degree 3. Rust has no formal
semantics, so the seam is a CONFORMANCE VECTOR: this file instantiates the REAL `cubicForm`
at a fixed `m = 3` five-table instance over BabyBear, KERNEL-DECIDES the reference values,
and writes them to `prover/testdata/sumcheck_cubic_conformance.json`. Agreement on the
vector is the whole claim — never refinement.

**Why it lives in `Assurance/` and not beside its degree-1 sibling.**
`Compiler/SumcheckConformance.lean` is the seam's serialization home, but `cubicForm` lives
in `Assurance/` (which imports `Compiler/`), so a Compiler-side writer could only re-spell
the summand and would be a second shape that agrees today. This file imports BOTH and binds
the vector to the ACTUAL `cubicForm` the soundness theorems are about.

## The vector's teeth

* **Four nodes on the wire.** Each round is serialized at `t ∈ {0,1,2,3}` — the degree-3
  message in full. `h(1)` is a serialized value, never something the reader reconstructs;
  the Rust verifier's round check reads it. (A verifier that derives `h(1) = claim − h(0)`
  has made its round check a tautology — the p3-sumcheck seam this rung refuses.)
* **`t = 2, 3` are off the boolean pair**, so the vector pins the round polynomial's CUBIC
  shape, not just the two points a degree-1 reader would fit.
* **`m = 3` has an interior round** — round 1 carries a non-boolean challenge prefix AND a
  boolean suffix corner at once, the full `glue` wiring.
* **Five distinct tables, all 40 values distinct and asymmetric under index bit-reversal**,
  so an LSB/MSB flip or a table permutation in the Rust reader fails the vector.
* **The chain identities are THEOREMS here** (`cubicChain0`/`cubicChainSucc*`/
  `cubicChainLast` — `roundSum_zero`/`_succ`/`_last` and `scChain_cubicHonest_final`
  instantiated at this instance, not re-proved), and the Rust side exercises the same
  identities numerically on the serialized numbers.
* **The reference values are NAMED theorems**, not anonymous `example`s: a fact worth
  asserting is worth naming, and an unnamed check leaves no term the writer can be held to.
-/
import Assurance.AirSumcheckCubic
import Compiler.SumcheckConformance

namespace Minidregg.Assurance

open Minidregg.Compiler Minidregg.Selvage
open Lean (Json ToJson toJson)

/-! ## §1. The fixed instance -/

/-- The five tables, LSB-first (`bitsToIdx`: index bit `i` = cube coordinate `i`).
All forty values are distinct and the set is asymmetric under index bit-reversal, so the
vector pins both the index convention and the table ORDER. -/
def cubTableE : List BabyBear :=
  [123456789, 987654321, 555555555, 2013265920, 42, 777000777, 31415926, 271828182]
def cubTableA : List BabyBear :=
  [11, 2222, 333333, 44444444, 1000000007, 8, 99999999, 1234567]
def cubTableB : List BabyBear :=
  [7654321, 13, 2013265919, 90210, 5555, 141421356, 17320508, 223606797]
def cubTableC : List BabyBear :=
  [1, 100, 10000, 1000000, 100000000, 2013265900, 65537, 4294967]
def cubTableD : List BabyBear :=
  [2718281828 % 2013265921, 3141592, 271, 828182845 % 2013265921, 9, 1618033988 % 2013265921,
   6180339, 887498948 % 2013265921]

/-- A list read as a hypercube table via the LSB-first index. -/
def cubOf (l : List BabyBear) : (Fin 3 → Bool) → BabyBear := fun b => l.getD (bitsToIdx b) 0

def cubE : (Fin 3 → Bool) → BabyBear := cubOf cubTableE
def cubA : (Fin 3 → Bool) → BabyBear := cubOf cubTableA
def cubB : (Fin 3 → Bool) → BabyBear := cubOf cubTableB
def cubC : (Fin 3 → Bool) → BabyBear := cubOf cubTableC
def cubD : (Fin 3 → Bool) → BabyBear := cubOf cubTableD

/-- The fixed challenge vector (Fiat-Shamir drawing is `[PROVER-fs]`, not this rung). -/
def cubR : Fin 3 → BabyBear := ![111111111, 222222222, 1999999999]

/-- The summand: the REAL `cubicForm`, not a re-spelling. -/
def cubForm : (Fin 3 → BabyBear) → BabyBear := cubicForm cubE cubA cubB cubC cubD

/-! ## §2. The chain identities, instantiated (theorems, not new proofs) -/

/-- `roundSum_zero` + `cubicForm_cube_sum` at this instance: round 0's boolean check target
IS the claimed total. -/
theorem cubicChain0 :
    roundSum cubForm cubR ⟨0, by norm_num⟩ 0 + roundSum cubForm cubR ⟨0, by norm_num⟩ 1
      = ∑ b, (cubE b * (cubA b * cubB b + cubC b * cubD b)) :=
  (roundSum_zero (by norm_num) cubForm cubR).trans
    (cubicForm_cube_sum cubE cubA cubB cubC cubD)

/-- `roundSum_succ`: `h₁(0) + h₁(1) = h₀(r₀)`. -/
theorem cubicChainSucc0 :
    roundSum cubForm cubR ⟨1, by norm_num⟩ 0 + roundSum cubForm cubR ⟨1, by norm_num⟩ 1
      = roundSum cubForm cubR ⟨0, by norm_num⟩ (cubR ⟨0, by norm_num⟩) :=
  roundSum_succ (by norm_num) cubForm cubR

/-- `roundSum_succ` again: `h₂(0) + h₂(1) = h₁(r₁)`. -/
theorem cubicChainSucc1 :
    roundSum cubForm cubR ⟨2, by norm_num⟩ 0 + roundSum cubForm cubR ⟨2, by norm_num⟩ 1
      = roundSum cubForm cubR ⟨1, by norm_num⟩ (cubR ⟨1, by norm_num⟩) :=
  roundSum_succ (by norm_num) cubForm cubR

/-- `roundSum_last` at this instance: the final fold IS the FACTORED terminal value
`Ê(r)·(Â(r)·B̂(r) + Ĉ(r)·D̂(r))` — the five openings the Rust verifier combines itself. -/
theorem cubicChainLast :
    roundSum cubForm cubR ⟨2, by norm_num⟩ (cubR ⟨2, by norm_num⟩)
      = mle cubE cubR * (mle cubA cubR * mle cubB cubR + mle cubC cubR * mle cubD cubR) := by
  have h := roundSum_last (i := (⟨2, by norm_num⟩ : Fin 3)) rfl cubForm cubR
    (cubR ⟨2, by norm_num⟩)
  rw [Function.update_eq_self] at h
  exact h

/-! ## §3. The reference values, KERNEL-DECIDED and NAMED

The numbers the JSON carries, pinned in the kernel (`by decide`) so the writer cannot drift
from what the type-checker computed. NAMED theorems, not anonymous `example`s: an unnamed
check leaves no term the writer can be held to and is invisible to axiom accounting. -/

/-- The claimed total `Σ_b E(b)·(A(b)·B(b) + C(b)·D(b))`, decided. -/
theorem cubClaim_value :
    (∑ b, (cubE b * (cubA b * cubB b + cubC b * cubD b))) = 908613629 := by decide

/-- The five FACTORED terminal openings at the challenge point, decided — the values the
Rust verifier combines itself as `Ê·(Â·B̂ + Ĉ·D̂)`. -/
theorem cubOpenings_value :
    (mle cubE cubR, mle cubA cubR, mle cubB cubR, mle cubC cubR, mle cubD cubR)
      = (22389050, 975840412, 347111176, 1905187762, 1473416475) := by decide

/-- Round 0's message at the four wire nodes `t ∈ {0,1,2,3}`, decided. -/
theorem cubRound0_value :
    (roundSum cubForm cubR ⟨0, by norm_num⟩ 0, roundSum cubForm cubR ⟨0, by norm_num⟩ 1,
     roundSum cubForm cubR ⟨0, by norm_num⟩ 2, roundSum cubForm cubR ⟨0, by norm_num⟩ 3)
      = (373836789, 534776840, 798195441, 1809927178) := by decide

/-- Round 1's message at the four wire nodes — the INTERIOR round, decided. -/
theorem cubRound1_value :
    (roundSum cubForm cubR ⟨1, by norm_num⟩ 0, roundSum cubForm cubR ⟨1, by norm_num⟩ 1,
     roundSum cubForm cubR ⟨1, by norm_num⟩ 2, roundSum cubForm cubR ⟨1, by norm_num⟩ 3)
      = (44197611, 374231620, 1996722578, 509539619) := by decide

/-- Round 2's message at the four wire nodes, decided. -/
theorem cubRound2_value :
    (roundSum cubForm cubR ⟨2, by norm_num⟩ 0, roundSum cubForm cubR ⟨2, by norm_num⟩ 1,
     roundSum cubForm cubR ⟨2, by norm_num⟩ 2, roundSum cubForm cubR ⟨2, by norm_num⟩ 3)
      = (1744416197, 497217055, 1827514357, 1307544482) := by decide

/-- **TEETH — the round message is genuinely CUBIC.** The third finite difference
`h(3) − 3h(2) + 3h(1) − h(0)` is `6·(leading coefficient)`; it is NONZERO in every round, so
no degree-≤2 message could carry these values and a Rust reader that fitted a quadratic
would fail the vector. -/
theorem cubRounds_are_cubic :
    (roundSum cubForm cubR ⟨0, by norm_num⟩ 3 - 3 * roundSum cubForm cubR ⟨0, by norm_num⟩ 2
       + 3 * roundSum cubForm cubR ⟨0, by norm_num⟩ 1 - roundSum cubForm cubR ⟨0, by norm_num⟩ 0
     ≠ 0)
    ∧ (roundSum cubForm cubR ⟨1, by norm_num⟩ 3 - 3 * roundSum cubForm cubR ⟨1, by norm_num⟩ 2
       + 3 * roundSum cubForm cubR ⟨1, by norm_num⟩ 1 - roundSum cubForm cubR ⟨1, by norm_num⟩ 0
     ≠ 0)
    ∧ (roundSum cubForm cubR ⟨2, by norm_num⟩ 3 - 3 * roundSum cubForm cubR ⟨2, by norm_num⟩ 2
       + 3 * roundSum cubForm cubR ⟨2, by norm_num⟩ 1 - roundSum cubForm cubR ⟨2, by norm_num⟩ 0
     ≠ 0) := by decide

/-! ## §4. The writer -/

/-- Round `i`'s serialized message: `[hᵢ(0), hᵢ(1), hᵢ(2), hᵢ(3)]` — FOUR nodes.
`h(1)` is on the wire; the reader never reconstructs it. -/
def cubRoundJson (i : Fin 3) : Json :=
  Json.arr <|
    (([0, 1, 2, 3] : List BabyBear).map fun t => toJson (roundSum cubForm cubR i t).val).toArray

/-- The whole degree-3 conformance file. -/
def cubicConformanceJson : Json :=
  Json.mkObj
    [ ("p", toJson babyBearP),
      ("m", toJson (3 : ℕ)),
      ("degree", toJson (3 : ℕ)),
      ("tableE", Json.arr (cubTableE.map fun v => toJson v.val).toArray),
      ("tableA", Json.arr (cubTableA.map fun v => toJson v.val).toArray),
      ("tableB", Json.arr (cubTableB.map fun v => toJson v.val).toArray),
      ("tableC", Json.arr (cubTableC.map fun v => toJson v.val).toArray),
      ("tableD", Json.arr (cubTableD.map fun v => toJson v.val).toArray),
      ("challenges", finVecToJson cubR),
      ("claim", toJson (∑ b, (cubE b * (cubA b * cubB b + cubC b * cubD b))).val),
      ("rounds", Json.arr ((List.finRange 3).map cubRoundJson).toArray),
      ("openings", Json.arr
        (([mle cubE cubR, mle cubA cubR, mle cubB cubR,
           mle cubC cubR, mle cubD cubR] : List BabyBear).map fun v => toJson v.val).toArray) ]

/-- Write the conformance file (repo-root-relative). -/
def writeCubicConformance (path : System.FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (cubicConformanceJson.pretty ++ "\n")

#eval writeCubicConformance "prover/testdata/sumcheck_cubic_conformance.json"


/-! ## §5. Axiom pins (house law) -/

/-- info: 'Minidregg.Assurance.cubicChain0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicChain0
/-- info: 'Minidregg.Assurance.cubicChainSucc0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicChainSucc0
/-- info: 'Minidregg.Assurance.cubicChainLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubicChainLast
/-- info: 'Minidregg.Assurance.cubClaim_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubClaim_value
/-- info: 'Minidregg.Assurance.cubOpenings_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubOpenings_value
/-- info: 'Minidregg.Assurance.cubRound1_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubRound1_value
/-- info: 'Minidregg.Assurance.cubRounds_are_cubic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubRounds_are_cubic

end Minidregg.Assurance
