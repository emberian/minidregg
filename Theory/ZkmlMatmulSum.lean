/-
# `Theory/ZkmlMatmulSum.lean` — the ordered contraction as a `Finset.sum`, and padding

**Substrate, said out loud: this is Lean-authored denotational content.** No constraint,
no field, no descriptor appears here; the file stays inside the `Theory/` boundary
(`scripts/check-import-boundary.sh`: Mathlib and `Theory/` only).

## What this file is for

`Theory/ZkmlTensorOps.lean` denotes `matmul` as a **left fold** over `List.finRange k`,
because the accumulation order is part of the semantics (f32 addition is not associative,
so an unordered specification would be ill-posed). Every sumcheck and MLE statement in
`Selvage/` and `Assurance/` is written over `Finset.sum`. **Nothing in the matmul path can
be stated until those two meet**, and the meeting is not free: it is exactly where the
ordered semantics is discarded.

So the bridge is built in **two named steps**, and the file's whole point is that the
boundary between them is a line you can put your finger on:

| step | lemma | hypothesis | what it discards |
|---|---|---|---|
| 1 | `foldl_add_eq_listSum` | `AddMonoid` — **associativity** and a unit | the bracketing |
| 2 | `listSum_finRange_eq_sum` | `AddCommMonoid` — **commutativity** | the order of the index set |

⚑ **The load-bearing property is ASSOCIATIVITY, not commutativity** — worth saying because
the informal statement of this hazard usually names the wrong one. IEEE-754 addition *is*
commutative; it is *not* associative. Step 1 is therefore the step a float-shaped reading
breaks, and `SatExample` breaks it on a real trace: a saturating `add` (the shape of every
finite accumulator at its range limit) makes the denotation of a one-op matmul trace
**differ from its own `Finset.sum`**, kernel-decided. Commutativity is not optional either,
but it enters at step 2 for a duller reason: `Finset.sum` over `Fin k` cannot be *written*
without it, so step 2 has no counterexample — it has a missing typeclass.

## Padding — and the `Theory/` change matmul turned out NOT to need

The MLE face wants dyadic domains (`Â` over `{0,1}^{log m} × {0,1}^{log k}`), and MNIST's
shapes are `784`, `100`, `10`, `2`. The build log's §4.5 offered a fork: a `pad` **op** in
the vocabulary with its own denotation, or MLE machinery over non-dyadic domains.

**Neither is needed, and this is the finding.** Zero-padding a contraction is a fact about
*tables*, not about *programs*: `padded_contraction` says extending the inner axis with
zeros leaves the contraction pointwise unchanged, and `padded_matmul_table` says the padded
output table *is* the zero-padding of the true one. No constructor enters `TOp`, so
`TOp.outTy`, `TOp.denote`, `TOp.arithmetic`, `TOp.macs`, `denote_op_rel` and
`ringHom_denote_op` — every place the thirteen constructors are enumerated — are untouched,
and no theorem of `ZkmlTensorOps` changes shape. The pad is a **commitment-layer**
obligation (the committed tables must really be zero outside the true extent), not a
denotational one.

## Scope, stated

This file says what the contraction *is* in a commutative ring. It says nothing about
whether a field reading is numerically adequate for the f32 one — `ZkmlTensorOps`' §7.4 gap
(bf16 exactness, accumulator width) is untouched, and `SatExample` is a lower bound on how
badly it can fail rather than a model of any particular float format.
-/
import Theory.ZkmlTensorOps

namespace Minidregg.Theory.ZkmlTensorOps

/-! ## §1. The bridge, in two steps -/

section Bridge

variable {α γ : Type}

/-- **STEP 1 — associativity only.** A left fold of `+` over a list is the list's sum,
starting from any accumulator. No commutativity: the list order is preserved on both
sides, and `List.sum` is itself a fold. This is the step a non-associative (float-shaped)
addition refutes — see `SatExample.sat_bridge_fails`. -/
theorem foldl_add_eq_listSum [AddMonoid α] (f : γ → α) :
    ∀ (l : List γ) (z : α), l.foldl (fun acc c => acc + f c) z = z + (l.map f).sum := by
  intro l
  induction l with
  | nil => intro z; simp
  | cons c l ih =>
      intro z
      show l.foldl _ (z + f c) = _
      rw [ih (z + f c), List.map_cons, List.sum_cons, add_assoc]

/-- **STEP 2 — where the ORDER is discarded.** `Finset.sum` over `Fin k` is a sum over an
index *set*; its definition requires `AddCommMonoid`, so this step cannot even be stated
for a reading whose addition does not commute. That is why it carries no counterexample:
the refutation of step 2 is a type error, not a number. -/
theorem listSum_finRange_eq_sum [AddCommMonoid α] {k : ℕ} (f : Fin k → α) :
    ((List.finRange k).map f).sum = ∑ p : Fin k, f p :=
  (Fin.sum_univ_def f).symm

/-- **The bridge.** The ordered accumulation over `List.finRange k` from `0` is the
unordered `Finset.sum`. Both hypotheses are visible in the typeclass; neither is free. -/
theorem foldl_finRange_eq_sum [AddCommMonoid α] {k : ℕ} (f : Fin k → α) :
    (List.finRange k).foldl (fun acc p => acc + f p) 0 = ∑ p : Fin k, f p := by
  rw [foldl_add_eq_listSum f, zero_add, listSum_finRange_eq_sum]

end Bridge

/-! ## §2. The matmul denotation, as a contraction

`IsRingReading` (already in `ZkmlTensorOps`) is the hypothesis: the reading's `0`, `+` and
`*` are the carrier's. Under it — and *only* under it — the ordered fold in `TOp.denote` is
the mathematical contraction `Σ_p a[i,p]·b[p,j]`. -/

section Contraction

variable {α : Type} [Ring α] {S : ScalarOps α} {Γ : Ctx} {d : Dtype} {m k n : ℕ}

/-- **The op-level bridge.** The `matmul` constructor's denotation at output index `(i,j)`
is the `Finset.sum` contraction. -/
theorem denote_matmul_sum (hS : IsRingReading S)
    (a : Var Γ ⟨d, [m, k]⟩) (b : Var Γ ⟨d, [k, n]⟩) (ρ : Env α Γ)
    (i : Fin m) (j : Fin n) :
    (TOp.matmul d m k n a b).denote S ρ (i, j, PUnit.unit)
      = ∑ p : Fin k, ρ.get a (i, p, PUnit.unit) * ρ.get b (p, j, PUnit.unit) := by
  show (List.finRange k).foldl
      (fun acc p => S.bin .add acc
        (S.bin .mul (ρ.get a (i, p, PUnit.unit)) (ρ.get b (p, j, PUnit.unit)))) S.zero = _
  simp only [hS.add, hS.mul, hS.zero]
  exact foldl_finRange_eq_sum
    (fun p => ρ.get a (i, p, PUnit.unit) * ρ.get b (p, j, PUnit.unit))

/-- A one-op matmul trace: the object every matmul statement downstream is about. -/
def matmulTrace (d : Dtype) (m k n : ℕ) {Γ : Ctx}
    (a : Var Γ ⟨d, [m, k]⟩) (b : Var Γ ⟨d, [k, n]⟩) : Trace ⟨d, [m, n]⟩ Γ :=
  Trace.op (TOp.matmul d m k n a b) (Trace.ret Var.here)

/-- **The trace-level bridge — the statement the build log named as blocking.**
`run S (matmulTrace …) ρ (i,j,⋆) = Σ_p a[i,p]·b[p,j]` over a ring-shaped reading. Every
MLE and sumcheck statement about matmul starts here. -/
theorem run_matmul_sum (hS : IsRingReading S)
    (a : Var Γ ⟨d, [m, k]⟩) (b : Var Γ ⟨d, [k, n]⟩) (ρ : Env α Γ)
    (i : Fin m) (j : Fin n) :
    run S (matmulTrace d m k n a b) ρ (i, j, PUnit.unit)
      = ∑ p : Fin k, ρ.get a (i, p, PUnit.unit) * ρ.get b (p, j, PUnit.unit) :=
  denote_matmul_sum hS a b ρ i j

end Contraction

/-! ## §3. Zero-padding to a dyadic domain

The contraction is stated on curried matrices (`matOf` views a `TVal` as one), because
padding changes the *type* of the index and a `TVal` carries its shape. All four theorems
are about tables; none is about a program. -/

section Padding

variable {α : Type} [Semiring α] {m k n s t u : ℕ}

/-- View a rank-2 tensor value as a matrix. -/
def matOf {d : Dtype} (v : TVal α ⟨d, [m, k]⟩) : Fin m → Fin k → α :=
  fun i p => v (i, p, PUnit.unit)

/-- The mathematical contraction of two matrices — what `run_matmul_sum` says the
denotation is. -/
def contract (A : Fin m → Fin k → α) (B : Fin k → Fin n → α) : Fin m → Fin n → α :=
  fun i j => ∑ p : Fin k, A i p * B p j

/-- Zero-extend a matrix's **second** axis (the contraction axis of the left operand, or
the column axis of the output). -/
def padRight (A : Fin m → Fin k → α) : Fin m → Fin (k + t) → α :=
  fun i => Fin.addCases (fun p => A i p) (fun _ => 0)

/-- Zero-extend a matrix's **first** axis (the contraction axis of the right operand, or
the row axis of the output). -/
def padDown (B : Fin k → Fin n → α) : Fin (k + t) → Fin n → α :=
  Fin.addCases (fun p => B p) (fun _ => fun _ => 0)

@[simp] theorem padRight_left (A : Fin m → Fin k → α) (i : Fin m) (p : Fin k) :
    (padRight (t := t) A) i (Fin.castAdd t p) = A i p := by
  simp [padRight]

@[simp] theorem padRight_right (A : Fin m → Fin k → α) (i : Fin m) (p : Fin t) :
    (padRight (t := t) A) i (Fin.natAdd k p) = 0 := by
  simp [padRight]

@[simp] theorem padDown_left (B : Fin k → Fin n → α) (p : Fin k) (j : Fin n) :
    (padDown (t := t) B) (Fin.castAdd t p) j = B p j := by
  simp [padDown]

@[simp] theorem padDown_right (B : Fin k → Fin n → α) (p : Fin t) (j : Fin n) :
    (padDown (t := t) B) (Fin.natAdd k p) j = 0 := by
  simp [padDown]

/-- **Padding the contraction axis changes nothing.** Extending the inner dimension from
`k` to `k + t` with zeros on both operands leaves every output entry equal to the true
contraction — so a prover may commit to dyadic tables and still be proving the claim about
the real shapes. `Fin.sum_univ_add` splits the padded sum; the second half is a sum of
`0 * 0`. -/
theorem padded_contraction (A : Fin m → Fin k → α) (B : Fin k → Fin n → α)
    (i : Fin m) (j : Fin n) :
    contract (padRight (t := t) A) (padDown (t := t) B) i j = contract A B i j := by
  simp only [contract, Fin.sum_univ_add, padRight_left, padDown_left, padRight_right,
    padDown_right, zero_mul, Finset.sum_const_zero, add_zero]

/-- **Padding the outer axes commutes with the contraction.** Padding rows of the left
operand and columns of the right operand produces exactly the zero-padding of the true
output table: the extra rows and columns are zero, not garbage the verifier must
separately constrain. -/
theorem padded_matmul_table (A : Fin m → Fin k → α) (B : Fin k → Fin n → α) :
    contract (padDown (t := s) A) (padRight (t := u) B)
      = padRight (t := u) (padDown (t := s) (contract A B)) := by
  funext i j
  refine Fin.addCases (motive := fun i =>
    contract (padDown (t := s) A) (padRight (t := u) B) i j
      = padRight (t := u) (padDown (t := s) (contract A B)) i j) ?_ ?_ i
  · intro i'
    refine Fin.addCases (motive := fun j =>
      contract (padDown (t := s) A) (padRight (t := u) B) (Fin.castAdd s i') j
        = padRight (t := u) (padDown (t := s) (contract A B)) (Fin.castAdd s i') j) ?_ ?_ j
    · intro j'; simp [contract]
    · intro j'; simp [contract]
  · intro i'
    refine Fin.addCases (motive := fun j =>
      contract (padDown (t := s) A) (padRight (t := u) B) (Fin.natAdd m i') j
        = padRight (t := u) (padDown (t := s) (contract A B)) (Fin.natAdd m i') j) ?_ ?_ j
    · intro j'; simp [contract]
    · intro j'; simp [contract]

/-- The MNIST first layer's inner axis, padded to a power of two: `784 + 240 = 2^10`.
Recorded as arithmetic so the instantiation of `padded_contraction` is not a guess. -/
theorem mnist_inner_dyadic : 784 + 240 = 2 ^ 10 := by norm_num

/-- The MNIST first layer's output axis: `100 + 28 = 2^7`. -/
theorem mnist_cols_dyadic : 100 + 28 = 2 ^ 7 := by norm_num

/-- The second layer: `100 + 28 = 2^7` inner, `10 + 6 = 2^4` out. -/
theorem mnist_second_dyadic : 10 + 6 = 2 ^ 4 := by norm_num

end Padding

/-! ## §4. Teeth — the bridge's hypothesis is REFUTABLE, on the real denotation

A hypothesis that is never exercised is decoration. `satOps` is a scalar reading whose
addition **saturates** at `10` — the shape of every finite accumulator at its range limit,
and the smallest honest stand-in for the fact that f32 addition is not associative. Under
it the ordered fold and the `Finset.sum` of the *same* trace disagree, so
`foldl_finRange_eq_sum` is not a tautology and `run_matmul_sum` is not free. -/

namespace SatExample

/-- Saturating integer addition: clamps at `10`. -/
def satAdd (a b : ℤ) : ℤ := if a + b ≤ 10 then a + b else 10

/-- A scalar reading whose `add` saturates. Everything else is the ordinary integer
reading, so the *only* thing being tested is the accumulator. -/
def satOps : ScalarOps ℤ where
  zero := 0
  one := 1
  un := fun _ a => -a
  bin := fun k a b => match k with
    | .add => satAdd a b
    | .sub => a - b
    | .mul => a * b
    | .div => a / b
    | .pow => a ^ b.toNat
  cmpB := fun _ a b => decide (a = b)
  fn := fun _ a => a
  cvt := fun _ _ a => a
  toIdx := Int.toNat

/-- **Saturating addition is not associative** — the property step 1 needs. -/
theorem satAdd_not_assoc : satAdd (satAdd 9 5) (-5) ≠ satAdd 9 (satAdd 5 (-5)) := by decide

/-- **It IS commutative.** Stated because the informal version of this hazard names
commutativity, and commutativity is not the property that fails: a float-shaped accumulator
commutes and does not associate. -/
theorem satAdd_comm (a b : ℤ) : satAdd a b = satAdd b a := by
  unfold satAdd; rw [add_comm]

/-- So `satOps` is not a ring reading, and `run_matmul_sum` does not apply to it. -/
theorem satOps_not_ringReading : ¬ IsRingReading satOps := by
  intro h
  have h9 : satOps.bin .add 9 5 = (9 : ℤ) + 5 := h.add 9 5
  simp [satOps, satAdd] at h9

/-- `f32[1,3]`. -/ def tSatA : TyT := ⟨Dtype.f32, [1, 3]⟩
/-- `f32[3,1]`. -/ def tSatB : TyT := ⟨Dtype.f32, [3, 1]⟩
/-- `f32[1,1]`. -/ def tSatC : TyT := ⟨Dtype.f32, [1, 1]⟩

/-- The context holding both operands. -/
def satCtx : Ctx := [tSatA, tSatB]

/-- `A = [[9, 5, −5]]`. -/
def satA : TVal ℤ tSatA := fun i => (![![9, 5, -5]] : Fin 1 → Fin 3 → ℤ) i.1 i.2.1

/-- `B = [[1],[1],[1]]`, so the contraction is `9 + 5 + (−5)`. -/
def satB : TVal ℤ tSatB := fun i => (![![1], ![1], ![1]] : Fin 3 → Fin 1 → ℤ) i.1 i.2.1

/-- The environment. -/
def satEnv : Env ℤ satCtx := Env.cons satA (Env.cons satB Env.nil)

/-- The one-op matmul trace `[1,3]·[3,1]`. -/
def satTrace : Trace tSatC satCtx :=
  matmulTrace Dtype.f32 1 3 1 Var.here (Var.there Var.here)

/-- **The ordered denotation saturates to `5`**: `((0+9)+5)+(−5)` clamps at the second
step and never recovers. Kernel-decided on the real `run`. -/
theorem satTrace_computes : run satOps satTrace satEnv (0, 0, PUnit.unit) = 5 := by decide

/-- **THE TOOTH — the bridge's conclusion is FALSE for a non-associative reading.** The
`Finset.sum` of the same products is `9`; the trace's own denotation is `5`. So
`run_matmul_sum` is refutable, its `IsRingReading` hypothesis is load-bearing, and "the
contraction is a sum" is a claim about the *reading*, not about matmul. -/
theorem sat_bridge_fails :
    run satOps satTrace satEnv (0, 0, PUnit.unit)
      ≠ ∑ p : Fin 3, satEnv.get (Γ := satCtx) (t := tSatA) Var.here (0, p, PUnit.unit)
          * satEnv.get (Γ := satCtx) (t := tSatB) (Var.there Var.here) (p, 0, PUnit.unit) := by
  decide

/-- **THE OTHER TOOTH — the contraction ORDER is observable.** Folding the same three
products in the reverse order gives `9`, not `5`. `TOp.denote`'s choice of
`List.finRange k` is therefore a semantic commitment, and the padding theorems above (which
append at the END of the index) preserve it only because the appended terms are zeros. -/
theorem sat_order_matters :
    (List.finRange 3).foldl
        (fun acc p => satOps.bin .add acc
          (satOps.bin .mul (satA (0, p, PUnit.unit)) (satB (p, 0, PUnit.unit)))) satOps.zero
      ≠ (List.finRange 3).reverse.foldl
        (fun acc p => satOps.bin .add acc
          (satOps.bin .mul (satA (0, p, PUnit.unit)) (satB (p, 0, PUnit.unit)))) satOps.zero := by
  decide

end SatExample

/-! ## §5. The bridge FIRES on the landed example

`ZkmlTensorOps`' own 2×3·3×2 witness (`mmTrace`, `mmEnv`, the exact integer reading `zOps`)
is already a `matmulTrace`; the bridge turns its fold into a contraction with no new
computation, and the sum form reproduces `[[4,5],[10,11]]`. -/

namespace RingExample

/-- The landed example trace IS a `matmulTrace` — definitionally, not by a lemma. -/
theorem mmTrace_eq_matmulTrace :
    mmTrace = matmulTrace Dtype.f32 2 3 2 Var.here (Var.there Var.here) := rfl

/-- **The bridge, instantiated on the landed witness.** Every output entry of the example
trace is the `Finset.sum` contraction of its operands — by `run_matmul_sum`, at every
`(i,j)`, not by computing four cases. -/
theorem mmTrace_contracts (i : Fin 2) (j : Fin 2) :
    run zOps mmTrace mmEnv (i, j, PUnit.unit)
      = ∑ p : Fin 3, aVal (i, p, PUnit.unit) * bVal (p, j, PUnit.unit) :=
  run_matmul_sum (intOps_isRingReading _ _ _) Var.here (Var.there Var.here) mmEnv i j

/-- And the sum form computes the same matrix the fold form did (`mmTrace_computes`). -/
theorem mmTrace_sum_computes :
    (∑ p : Fin 3, aVal (0, p, PUnit.unit) * bVal (p, 0, PUnit.unit)) = 4 ∧
    (∑ p : Fin 3, aVal (0, p, PUnit.unit) * bVal (p, 1, PUnit.unit)) = 5 ∧
    (∑ p : Fin 3, aVal (1, p, PUnit.unit) * bVal (p, 0, PUnit.unit)) = 10 ∧
    (∑ p : Fin 3, aVal (1, p, PUnit.unit) * bVal (p, 1, PUnit.unit)) = 11 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end RingExample

/-! ## §6. Axiom pins (house law) -/

/-- info: 'Minidregg.Theory.ZkmlTensorOps.foldl_add_eq_listSum' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms foldl_add_eq_listSum
/-- info: 'Minidregg.Theory.ZkmlTensorOps.foldl_finRange_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldl_finRange_eq_sum
/-- info: 'Minidregg.Theory.ZkmlTensorOps.denote_matmul_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms denote_matmul_sum
/-- info: 'Minidregg.Theory.ZkmlTensorOps.run_matmul_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_matmul_sum
/-- info: 'Minidregg.Theory.ZkmlTensorOps.padded_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_contraction
/-- info: 'Minidregg.Theory.ZkmlTensorOps.padded_matmul_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms padded_matmul_table
/-- info: 'Minidregg.Theory.ZkmlTensorOps.SatExample.sat_bridge_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SatExample.sat_bridge_fails
/-- info: 'Minidregg.Theory.ZkmlTensorOps.SatExample.sat_order_matters' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms SatExample.sat_order_matters
/-- info: 'Minidregg.Theory.ZkmlTensorOps.RingExample.mmTrace_contracts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RingExample.mmTrace_contracts

end Minidregg.Theory.ZkmlTensorOps
