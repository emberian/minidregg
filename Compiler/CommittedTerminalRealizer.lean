/-
# Compiler.CommittedTerminalRealizer -- a computable full-word realizer of `CommittedTerminal`

`Compiler/GateMleExt6.lean:246` leaves one seam open in the joined gate
protocol: `CommittedTerminal d wv enc gamma r` is a record whose only content is
`value = mle (gammaResidualTable d wv enc gamma) r`, "constructed by the
forthcoming Mobius/FRI assembly".  Nothing in the tree constructs it, and the
controller that would consume an authenticated terminal is `noncomputable`
because `Ext6Q := AdjoinRoot ext6Polynomial` is.

This module lands the smallest honest realizer, statement-first:

* **A computable Ext6 carrier.**  `Ext6L`, six BabyBear lanes as a STRICT
  structure, with lane addition/subtraction/powers beside the tree's `ext6Mul`
  (materialized through `Ext6L.ofFn`); every lane operation is proved to
  commute with `readExt6 := toExt6 ∘ toFn` into the proved field
  (`ext6Mul_correct` is reused, not re-proved).  Nothing here is a second
  field: `Ext6L` carries no ring instance, only the transport lemmas the
  bridge needs.
* **The sparse terminal.**  `mle (gammaResidualTable d wv enc gamma) r` is,
  because `enc` is injective, the sum over the residual LIST
  `Σ_k gamma^k · res_k · chi_{enc k}(r)` (`mle_gammaResidualTable_sparse`) --
  linear in the descriptor, never a walk over `2^m` cube corners.
  `laneTerminal` computes exactly that with a running gamma power, and
  `read_laneTerminal` is the bridge.
* **The realizer.**  `realize` reads the STATEMENT's root, an `Opening` (the
  whole committed trace plus the claimed terminal value) and decides with named
  refusals: `rootMismatch` when the opened word does not recommit to the root,
  `valueMismatch` when the recomputed terminal differs from the claim.  It is a
  plain `def`; `#eval` runs it.
* **`CommittedTerminal` inhabited.**  `committedTerminal` turns any accepted
  run into the record at the opened trace; `committedTerminalOfBinding` turns it
  into the record at the COMMITTED trace, consuming `BindingCommitment.commit_injective`
  -- the PCS premise as a named instance of the tree's interface, never assumed.
  `honestRounds_closes_realized` then closes the clear sumcheck against it
  through the existing `honestRounds_closes_committed`.

**Resolution and regime, on the label.**  This is the FULL-WORD resolution
(the checker lane's `[MATMUL-pcs]` scope; `Selvage/BaseFoldIor.lean` header):
the verifier reads the whole trace.  It is chosen because the tree's only
extractor with a proof, `Selvage/BaseFoldRbrTable.lean:138 extractTable`,
needs `2^m ≤ t` opened columns -- every position -- so a sampled realizer with
`t < 2^m` would carry a soundness premise (`[ERASURE-list]`, `Selvage/Erasure.lean`)
the tree does not yet discharge.  At full word the terminal step draws no
challenge and has error ZERO given binding; the sumcheck leg keeps its landed
price `m · 2/|F|` (`Selvage/BaseFoldRbr.lean:82 basefoldSumcheckRbr`).  Sampled
queries, Merkle authentication paths and `[COMMIT-CR]` are the named residuals
listed at the end of this file.

**ATLAS fields (law 2), decided by the kernel over the emitted demo descriptor
(`Compiler/EmitSerialize.lean:177 demoDescriptor`, 18 gates + 5 roots = 23
residuals in the five-cube) at the ideal commitment:**

* satisfiable -- `realizer_complete`: the honest opening of the evaluator-filled
  satisfying trace is accepted, and `demo_honest_terminal_zero` computes its
  terminal to be exactly `0` (a satisfying trace has an all-zero residual table);
  `demo_tampered_terminal` computes the terminal of a tampered trace to a
  NONZERO literal, so the realizer's arithmetic is exercised, not short-circuited;
* teeth -- `realizer_refuses_forged_opening` (the claimed value is off by one:
  `valueMismatch`) and `realizer_refuses_forged_word` (one aux wire changed
  under the honest root: `rootMismatch`), both decided;
* premise inhabitation -- `idealCommitment BabyBear (Fin 23)` is a built
  `BindingCommitment` (`Selvage/Commitment.lean:209`); the generic Merkle
  instance is stated over any `BinaryMerkle.HashSuite` with its binding reduced
  to `¬ Collision` by the tree's `positionBinding_of_collisionFree`, and that
  premise is inhabited by `identitySuite` (the digest IS the tree; axiom-free),
  at which `realizerMerkle_complete` / `realizerMerkle_refuses_forged_word`
  are decided through `cubeRoot` on the 32-leaf cube.

The Stage-0 descriptor (`Compiler/EvmAddAir.evmAddDescriptor`, 3,298 gates +
850 roots = 4,148 residuals, `m = 13`) is beyond kernel `decide`; it is
exhibited by a compiled `#eval` with build-failing teeth, the Lane-A idiom.
-/

import Compiler.GateMleExt6
import Compiler.DescriptorEval
import Selvage.Commitment
import Selvage.BinaryMerkle

namespace Minidregg.Compiler.CommittedTerminalRealizer

open scoped BigOperators
open Minidregg.Assurance Minidregg.Selvage Minidregg.Compiler.GateMleExt6
open Minidregg.Compiler.DescriptorEval Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000

/-! ## §1. The computable Ext6 carrier: six BabyBear lanes, STRICT -/

/-- Six BabyBear lanes: the coefficients of `a₀ + a₁u + ⋯ + a₅u⁵` with `u⁶ = 31`.
A structure, not a function, so every lane product is materialized once:
`ext6Mul` (`Compiler/Ext6Conformance.lean:265`) returns a lazy `Fin 6 → BabyBear`
closure, and a `laneProd` nest of depth `m` would re-evaluate inner lanes
`6^m` times (measured: `m = 13` did not terminate).  `toFn`/`ofFn` are the
reused-arithmetic bridge; `readExt6` reads the lanes into the proved field. -/
structure Ext6L where
  c0 : BabyBear
  c1 : BabyBear
  c2 : BabyBear
  c3 : BabyBear
  c4 : BabyBear
  c5 : BabyBear
  deriving DecidableEq, Repr

def Ext6L.toFn (a : Ext6L) : Fin 6 → BabyBear
  | 0 => a.c0 | 1 => a.c1 | 2 => a.c2 | 3 => a.c3 | 4 => a.c4 | 5 => a.c5

/-- Materialize a lane function (the strictness point). -/
def Ext6L.ofFn (f : Fin 6 → BabyBear) : Ext6L := ⟨f 0, f 1, f 2, f 3, f 4, f 5⟩

theorem Ext6L.toFn_ofFn (f : Fin 6 → BabyBear) : (Ext6L.ofFn f).toFn = f := by
  funext i
  fin_cases i <;> rfl

/-- The lanes read into the proved field `Ext6Q` (`toExt6`, REUSED). -/
noncomputable def readExt6 (a : Ext6L) : Ext6Q := toExt6 a.toFn

def ext6Zero : Ext6L := ⟨0, 0, 0, 0, 0, 0⟩
def ext6One : Ext6L := ⟨1, 0, 0, 0, 0, 0⟩
def ext6OfBase (c : BabyBear) : Ext6L := ⟨c, 0, 0, 0, 0, 0⟩
def ext6Add (a b : Ext6L) : Ext6L :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4, a.c5 + b.c5⟩
def ext6Sub (a b : Ext6L) : Ext6L :=
  ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3, a.c4 - b.c4, a.c5 - b.c5⟩

/-- Strict lane multiplication: the tree's `ext6Mul`, materialized. -/
def ext6MulL (a b : Ext6L) : Ext6L := Ext6L.ofFn (ext6Mul a.toFn b.toFn)

/-- Lane powers by repeated multiplication (structural in the exponent, so the
kernel reduces it). -/
def ext6Pow (a : Ext6L) : Nat → Ext6L
  | 0 => ext6One
  | n + 1 => ext6MulL (ext6Pow a n) a

theorem read_zero : readExt6 ext6Zero = 0 := by
  simp [readExt6, ext6Zero, Ext6L.toFn, toExt6]

theorem read_one : readExt6 ext6One = 1 := by
  simp [readExt6, ext6One, Ext6L.toFn, toExt6]

theorem read_ofBase (c : BabyBear) :
    readExt6 (ext6OfBase c) = algebraMap BabyBear Ext6Q c := by
  simp [readExt6, ext6OfBase, Ext6L.toFn, toExt6, AdjoinRoot.algebraMap_eq]

theorem read_add (a b : Ext6L) : readExt6 (ext6Add a b) = readExt6 a + readExt6 b := by
  simp only [readExt6, ext6Add, Ext6L.toFn, toExt6, map_add]
  ring

theorem read_sub (a b : Ext6L) : readExt6 (ext6Sub a b) = readExt6 a - readExt6 b := by
  simp only [readExt6, ext6Sub, Ext6L.toFn, toExt6, map_sub]
  ring

/-- `ext6Mul_correct`, transported: the strict product reads to the field product. -/
theorem read_mul (a b : Ext6L) : readExt6 (ext6MulL a b) = readExt6 a * readExt6 b := by
  unfold readExt6 ext6MulL
  rw [Ext6L.toFn_ofFn, ext6Mul_correct]

theorem read_pow (a : Ext6L) (n : Nat) : readExt6 (ext6Pow a n) = readExt6 a ^ n := by
  induction n with
  | zero => simp [ext6Pow, read_one]
  | succ n ih => rw [ext6Pow, read_mul, ih, pow_succ]

/-! ## §2. Lane products, the chi basis, and the sparse terminal -/

/-- Fold a list of lane values by multiplication. -/
def laneProd (l : List Ext6L) : Ext6L := l.foldr ext6MulL ext6One

theorem read_laneProd (l : List Ext6L) : readExt6 (laneProd l) = (l.map readExt6).prod := by
  induction l with
  | nil => simp [laneProd, read_one]
  | cons a l ih =>
    show readExt6 (ext6MulL a (laneProd l)) = _
    rw [read_mul, ih, List.map_cons, List.prod_cons]

/-- The lane chi basis polynomial at corner `b`, evaluated at `x`:
`∏ᵢ (if bᵢ then xᵢ else 1 − xᵢ)`, the shape of `Selvage.chiEval`. -/
def laneChi {m : Nat} (b : Fin m → Bool) (x : Fin m → Ext6L) : Ext6L :=
  laneProd (List.ofFn fun i => if b i then x i else ext6Sub ext6One (x i))

theorem read_laneChi {m : Nat} (b : Fin m → Bool) (x : Fin m → Ext6L) :
    readExt6 (laneChi b x) = chiEval b (fun i => readExt6 (x i)) := by
  unfold laneChi chiEval
  rw [read_laneProd, List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hb : b i
  · simp [hb]
  · simp [hb, read_sub, read_one]

/-- The running-power fold behind `laneTerminal`: entries `res` from position
`k` on, current power `gpow = gamma^k`, accumulator `acc`. -/
def laneTerminalGo {m : Nat} (gamma : Ext6L) (r : Fin m → Ext6L)
    (encNat : Nat → (Fin m → Bool)) :
    List BabyBear → Nat → Ext6L → Ext6L → Ext6L
  | [], _, _, acc => acc
  | c :: rest, k, gpow, acc =>
      laneTerminalGo gamma r encNat rest (k + 1) (ext6MulL gpow gamma)
        (ext6Add acc (ext6MulL (ext6MulL gpow (ext6OfBase c)) (laneChi (encNat k) r)))

/-- **The sparse gamma-weighted MLE terminal**: `Σ_k gamma^k · res_k · chi_{enc k}(r)`
over the residual list, in list order.  Linear in the descriptor. -/
def laneTerminal {m : Nat} (gamma : Ext6L) (r : Fin m → Ext6L)
    (encNat : Nat → (Fin m → Bool)) (res : List BabyBear) : Ext6L :=
  laneTerminalGo gamma r encNat res 0 ext6One ext6Zero

theorem read_laneTerminalGo {m : Nat} (gamma : Ext6L) (r : Fin m → Ext6L)
    (encNat : Nat → (Fin m → Bool)) (res : List BabyBear) :
    ∀ (k : Nat) (gpow acc : Ext6L),
      readExt6 (laneTerminalGo gamma r encNat res k gpow acc) =
        readExt6 acc + ∑ j ∈ Finset.range res.length,
          readExt6 gpow * readExt6 gamma ^ j *
            algebraMap BabyBear Ext6Q (res.getD j 0) *
            chiEval (encNat (k + j)) (fun i => readExt6 (r i)) := by
  induction res with
  | nil =>
    intro k gpow acc
    simp [laneTerminalGo]
  | cons c rest ih =>
    intro k gpow acc
    rw [laneTerminalGo, ih, List.length_cons, Finset.sum_range_succ']
    simp only [read_add, read_mul, read_ofBase, read_laneChi, List.getD_cons_zero,
      List.getD_cons_succ, pow_zero, mul_one, Nat.add_zero]
    have hshift : ∀ j ∈ Finset.range rest.length,
        readExt6 gpow * readExt6 gamma * readExt6 gamma ^ j *
            algebraMap BabyBear Ext6Q (rest.getD j 0) *
            chiEval (encNat (k + 1 + j)) (fun i => readExt6 (r i)) =
          readExt6 gpow * readExt6 gamma ^ (j + 1) *
            algebraMap BabyBear Ext6Q (rest.getD j 0) *
            chiEval (encNat (k + (j + 1))) (fun i => readExt6 (r i)) := by
      intro j _
      rw [pow_succ, show k + 1 + j = k + (j + 1) by omega]
      ring
    rw [Finset.sum_congr rfl hshift]
    ring

/-! ## §3. The sparse identity for the tree's table -/

/-- `mle` of the gamma-weighted padded table is the sum over the residual
LIST: the padded cube contributes nothing, and injectivity of `enc` collapses
the mask/lift product to one term per residual. -/
theorem mle_gammaResidualTable_sparse {m : Nat}
    (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (gamma : Ext6Q) (r : Fin m → Ext6Q) :
    mle (gammaResidualTable d wv enc gamma) r =
      ∑ k : Fin (descriptorResiduals d wv).length,
        gamma ^ (k : Nat) * algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get k) *
          chiEval (enc k) r := by
  have key : ∀ b : Fin m → Bool, gammaResidualTable d wv enc gamma b =
      ∑ k : Fin (descriptorResiduals d wv).length,
        if enc k = b then
          gamma ^ (k : Nat) * algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get k)
        else 0 := by
    intro b
    by_cases hb : ∃ k, enc k = b
    · obtain ⟨k0, rfl⟩ := hb
      rw [gammaResidualTable_read, sum_ite_enc enc _ k0]
    · have hb' : ∀ k, enc k ≠ b := fun k hk => hb ⟨k, hk⟩
      have h1 : gammaResidualTable d wv enc gamma b = 0 := by
        simp [gammaResidualTable, gammaMask, hb']
      rw [h1]
      symm
      apply Finset.sum_eq_zero
      intro k _
      simp [hb' k]
  unfold mle
  simp_rw [key, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- **The bridge**: the lane terminal read into the proved field is exactly the
MLE the `CommittedTerminal` interface demands, for any embedding `enc` that
agrees with the computable corner function on the residual indices. -/
theorem read_laneTerminal {m : Nat}
    (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) :
    readExt6 (laneTerminal gamma r encNat (descriptorResiduals d wv)) =
      mle (gammaResidualTable d wv enc (readExt6 gamma)) (fun i => readExt6 (r i)) := by
  rw [mle_gammaResidualTable_sparse, laneTerminal, read_laneTerminalGo, read_zero,
    zero_add, read_one, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _
  rw [hEnc, one_mul, Nat.zero_add, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem k.isLt, Option.getD_some, List.get_eq_getElem]

/-! ## §4. The corner function and the statement-owned embedding -/

/-- Residual `k` sits at the LSB-first bit corner of `k`. -/
def bitCorner (m : Nat) (k : Nat) : Fin m → Bool := fun i => k.testBit i

theorem bitCorner_inj {m : Nat} {k₁ k₂ : Nat} (h₁ : k₁ < 2 ^ m) (h₂ : k₂ < 2 ^ m)
    (h : bitCorner m k₁ = bitCorner m k₂) : k₁ = k₂ := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · exact congrFun h ⟨i, hi⟩
  · have hm : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hi)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h₁ hm),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h₂ hm)]

/-- The bit-corner embedding of `N ≤ 2^m` indices into the `m`-cube. -/
def bitEmbedding (N m : Nat) (h : N ≤ 2 ^ m) : Fin N ↪ (Fin m → Bool) :=
  ⟨fun k => bitCorner m k, fun k₁ k₂ hk =>
    Fin.ext (bitCorner_inj (lt_of_lt_of_le k₁.isLt h) (lt_of_lt_of_le k₂.isLt h) hk)⟩

@[simp] theorem bitEmbedding_apply (N m : Nat) (h : N ≤ 2 ^ m) (k : Fin N) :
    bitEmbedding N m h k = bitCorner m k := rfl

/-- The residual count does not depend on the trace (`descriptorResiduals_length`),
so one embedding serves every candidate trace of a descriptor. -/
def residualEmbedding {m : Nat} (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (h : d.gates.length + d.zeros.length ≤ 2 ^ m) :
    Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool) :=
  bitEmbedding _ m (by rw [descriptorResiduals_length]; exact h)

@[simp] theorem residualEmbedding_apply {m : Nat} (d : ConstraintDescriptor BabyBear)
    (wv : Nat → BabyBear) (h : d.gates.length + d.zeros.length ≤ 2 ^ m)
    (k : Fin (descriptorResiduals d wv).length) :
    residualEmbedding d wv h k = bitCorner m k := rfl

/-! ## §5. The realizer -/

/-- A full-word opening: the whole committed trace and the claimed terminal. -/
structure Opening (n : Nat) where
  word : Fin n → BabyBear
  value : Ext6L

/-- Every route by which the realizer refuses. -/
inductive Failure
  /-- The opened word does not recommit to the statement's root. -/
  | rootMismatch
  /-- The recomputed terminal differs from the claimed value. -/
  | valueMismatch
  deriving DecidableEq, Repr

/-- Read a finite word as the total trace the descriptor vocabulary expects
(`ConstraintDescriptor` reads by `Nat` index; out-of-range reads are `0`). -/
def traceOf {n : Nat} (word : Fin n → BabyBear) : Nat → BabyBear :=
  fun i => if h : i < n then word ⟨i, h⟩ else 0

/-- **The realizer.**  Recommit the opened word against the statement's root,
recompute the sparse terminal from the opened trace, compare with the claim. -/
def realize {Root : Type} [DecidableEq Root] {n m : Nat}
    (commit : (Fin n → BabyBear) → Root) (d : ConstraintDescriptor BabyBear)
    (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L) (r : Fin m → Ext6L)
    (rt : Root) (op : Opening n) : Except Failure Ext6L :=
  if commit op.word ≠ rt then .error .rootMismatch
  else if laneTerminal gamma r encNat (descriptorResiduals d (traceOf op.word)) ≠ op.value then
    .error .valueMismatch
  else .ok op.value

section Realize

variable {Root : Type} [DecidableEq Root] {n m : Nat}
variable (commit : (Fin n → BabyBear) → Root) (d : ConstraintDescriptor BabyBear)
variable (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L) (r : Fin m → Ext6L)

/-- The realizer accepts exactly when the word recommits and the claim is the
recomputed terminal. -/
theorem realize_ok_iff (rt : Root) (op : Opening n) (v : Ext6L) :
    realize commit d encNat gamma r rt op = .ok v ↔
      commit op.word = rt ∧
        laneTerminal gamma r encNat (descriptorResiduals d (traceOf op.word)) = op.value ∧
        v = op.value := by
  unfold realize
  by_cases hrt : commit op.word = rt
  · by_cases hv : laneTerminal gamma r encNat (descriptorResiduals d (traceOf op.word)) = op.value
    · simp only [hrt, hv, ne_eq, not_true_eq_false, if_false, Except.ok.injEq, true_and]
      exact eq_comm
    · simp [hrt, hv]
  · simp [hrt]

/-- Completeness in general: the honest opening of any word is accepted. -/
theorem realize_complete (w : Fin n → BabyBear) :
    realize commit d encNat gamma r (commit w)
        ⟨w, laneTerminal gamma r encNat (descriptorResiduals d (traceOf w))⟩ =
      .ok (laneTerminal gamma r encNat (descriptorResiduals d (traceOf w))) := by
  rw [realize_ok_iff]
  exact ⟨rfl, rfl, rfl⟩

/-- Refusal: a wrong claimed value under the honest root. -/
theorem realize_wrong_value_refused (rt : Root) (op : Opening n)
    (hrt : commit op.word = rt)
    (hv : laneTerminal gamma r encNat (descriptorResiduals d (traceOf op.word)) ≠ op.value) :
    realize commit d encNat gamma r rt op = .error .valueMismatch := by
  unfold realize
  simp [hrt, hv]

/-- Refusal: a word that does not recommit. -/
theorem realize_wrong_root_refused (rt : Root) (op : Opening n)
    (hrt : commit op.word ≠ rt) :
    realize commit d encNat gamma r rt op = .error .rootMismatch := by
  unfold realize
  simp [hrt]

/-- An accepted value is the exact MLE at the OPENED trace. -/
theorem realize_value_eq (rt : Root) (op : Opening n) (v : Ext6L)
    (h : realize commit d encNat gamma r rt op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf op.word)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) :
    readExt6 v =
      mle (gammaResidualTable d (traceOf op.word) enc (readExt6 gamma))
        (fun i => readExt6 (r i)) := by
  obtain ⟨-, hv, rfl⟩ := (realize_ok_iff commit d encNat gamma r rt op v).mp h
  rw [← hv]
  exact read_laneTerminal d _ enc encNat hEnc gamma r

/-- **`CommittedTerminal` inhabited at the opened trace.**  The RECORD is
`noncomputable` because its `value` field lives in `Ext6Q`; the decision that
produces it (`realize`) is not. -/
noncomputable def committedTerminal (rt : Root) (op : Opening n) (v : Ext6L)
    (h : realize commit d encNat gamma r rt op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf op.word)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) :
    CommittedTerminal d (traceOf op.word) enc (readExt6 gamma) (fun i => readExt6 (r i)) :=
  ⟨readExt6 v, realize_value_eq commit d encNat gamma r rt op v h enc hEnc⟩

end Realize

/-! ## §6. Soundness under the named PCS premise -/

section Sound

variable {Root Op : Type} [DecidableEq Root] {n m : Nat}
variable (S : BindingCommitment Root BabyBear (Fin n) Op)
variable (d : ConstraintDescriptor BabyBear)
variable (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L) (r : Fin m → Ext6L)

/-- **Soundness.**  Against a root that commits `w` under a `BindingCommitment`
(the PCS premise, as the tree's interface; `commit_injective` is the only
property consumed), an accepted value is the MLE at the COMMITTED trace --
whatever word the prover opened.  No challenge is drawn at this step: the
error is zero, the price is the binding event `[COMMIT-CR]` carried by `S`. -/
theorem realize_sound (w : Fin n → BabyBear) (op : Opening n) (v : Ext6L)
    (h : realize S.commit d encNat gamma r (S.commit w) op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) :
    readExt6 v =
      mle (gammaResidualTable d (traceOf w) enc (readExt6 gamma)) (fun i => readExt6 (r i)) := by
  have hw : op.word = w :=
    S.commit_injective ((realize_ok_iff S.commit d encNat gamma r _ op v).mp h).1
  subst hw
  exact realize_value_eq S.commit d encNat gamma r _ op v h enc hEnc

/-- **`CommittedTerminal` at the committed trace**, from an accepted run and
the named binding premise. -/
noncomputable def committedTerminalOfBinding (w : Fin n → BabyBear) (op : Opening n) (v : Ext6L)
    (h : realize S.commit d encNat gamma r (S.commit w) op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) :
    CommittedTerminal d (traceOf w) enc (readExt6 gamma) (fun i => readExt6 (r i)) :=
  ⟨readExt6 v, realize_sound S d encNat gamma r w op v h enc hEnc⟩

/-- The clear sumcheck (`honestRounds`) closes against the realized terminal:
`honestRounds_closes_committed` at this realizer. -/
theorem honestRounds_closes_realized (w : Fin n → BabyBear) (op : Opening n) (v : Ext6L)
    (h : realize S.commit d encNat gamma r (S.commit w) op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k)
    (hd : descriptorHolds d (traceOf w)) :
    scChain 0 (honestRounds d (traceOf w) enc (readExt6 gamma) (chalOf fun i => readExt6 (r i)))
        (chalOf fun i => readExt6 (r i)) m = readExt6 v :=
  honestRounds_closes_committed d (traceOf w) enc (readExt6 gamma) hd _
    (committedTerminalOfBinding S d encNat gamma r w op v h enc hEnc)

/-- Refusal through binding: under a binding root for `w`, opening any OTHER
word is refused at the root, before any arithmetic. -/
theorem realize_other_word_refused (w : Fin n → BabyBear) (op : Opening n)
    (hne : op.word ≠ w) :
    realize S.commit d encNat gamma r (S.commit w) op = .error .rootMismatch :=
  realize_wrong_root_refused S.commit d encNat gamma r _ op
    (fun hc => hne (S.commit_injective hc))

end Sound

/-! ## §7. The generic Merkle instance: binding priced as `¬ Collision` -/

section Merkle

open BinaryMerkle

variable {Digest : Type} [DecidableEq Digest] {k m : Nat}
variable (H : HashSuite BabyBear Digest)
variable (d : ConstraintDescriptor BabyBear)
variable (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L) (r : Fin m → Ext6L)

/-- The realizer over the tree's perfect binary Merkle tree on `2^k` leaves
(`BinaryMerkle.openingScheme`): the root is `cubeRoot`, recomputed from the
opened word.  Computable whenever `H` is. -/
def realizeMerkle (rt : Digest) (op : Opening (2 ^ k)) : Except Failure Ext6L :=
  realize (openingScheme H k).commit d encNat gamma r rt op

/-- Under collision-freeness of the suite the Merkle scheme is position-binding
(`positionBinding_of_collisionFree`, REUSED), hence a `BindingCommitment`, and
`realize_sound` applies with `[COMMIT-CR]` as the exact price. -/
def merkleBinding (hfree : ¬ Collision H) :
    BindingCommitment Digest BabyBear (Fin (2 ^ k)) (List Digest) :=
  ⟨openingScheme H k, positionBinding_of_collisionFree H k hfree⟩

theorem realizeMerkle_sound (hfree : ¬ Collision H)
    (w : Fin (2 ^ k) → BabyBear) (op : Opening (2 ^ k)) (v : Ext6L)
    (h : realizeMerkle H d encNat gamma r ((openingScheme H k).commit w) op = .ok v)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ kk, enc kk = encNat kk) :
    readExt6 v =
      mle (gammaResidualTable d (traceOf w) enc (readExt6 gamma)) (fun i => readExt6 (r i)) :=
  realize_sound (merkleBinding H hfree) d encNat gamma r w op v h enc hEnc

/-- **The identity Merkle suite** -- the digest IS the tree.  Collision-free by
constructor injectivity and succinctness-free by construction: the Merkle
analogue of `idealCommitment`, the inhabitation witness of the `¬ Collision`
premise above, never its deployment (`[CT-merkle-profile]`). -/
inductive IdTree
  | leaf (v : BabyBear)
  | node (l r : IdTree)
  deriving DecidableEq, Repr

def identitySuite : HashSuite BabyBear IdTree := ⟨IdTree.leaf, IdTree.node⟩

theorem identitySuite_collisionFree : ¬ Collision identitySuite := by
  rintro (⟨l, r, hne, h⟩ | ⟨l₁, r₁, l₂, r₂, hne, h⟩)
  · exact hne (IdTree.leaf.inj h)
  · obtain ⟨h1, h2⟩ := IdTree.node.inj h
    exact hne (by rw [h1, h2])

end Merkle

/-! ## §8. ATLAS fields: the emitted demo descriptor, decided -/

namespace DemoInstance

/-- The demo variables: `x = 13`, bits `(1,0,1,1)` (`EmitSerialize.demoVals`). -/
def demoVars : Array BabyBear := #[13, 1, 0, 1, 1]

/-- The evaluator-filled 23-wire trace (`DescriptorEval.fillAux`, REUSED). -/
def demoWord : Fin 23 → BabyBear := fun i => (fillAux demoDescriptor demoVars).getD i 0

/-- Residual count fits the five-cube: `18 + 5 ≤ 32`. -/
theorem demo_residuals_fit : demoDescriptor.gates.length + demoDescriptor.zeros.length ≤ 2 ^ 5 := by
  decide +kernel

abbrev S : BindingCommitment (Fin 23 → BabyBear) BabyBear (Fin 23) Unit :=
  idealCommitment BabyBear (Fin 23)

def gamma : Ext6L := ⟨3, 1, 4, 1, 5, 9⟩
def r : Fin 5 → Ext6L := fun i => ⟨((i : Nat) : BabyBear) + 2, 7, 1, 8, 2, 8⟩

/-- The satisfying trace, decided from the evaluator's output. -/
theorem demoWord_holds : descriptorHolds demoDescriptor (traceOf demoWord) := by
  decide +kernel

/-- The honest terminal of a satisfying trace is `0`: every residual is zero.
Decided by running the full lane arithmetic in the kernel. -/
theorem demo_honest_terminal_zero :
    laneTerminal gamma r (bitCorner 5) (descriptorResiduals demoDescriptor (traceOf demoWord)) =
      ext6Zero := by
  decide +kernel

def honest : Opening 23 := ⟨demoWord, ext6Zero⟩

/-- **Satisfiable, decided.** -/
theorem realizer_complete :
    realize S.commit demoDescriptor (bitCorner 5) gamma r (S.commit demoWord) honest =
      .ok ext6Zero := by
  decide +kernel

/-- **Teeth, decided:** the claimed value off by one is refused. -/
theorem realizer_refuses_forged_opening :
    realize S.commit demoDescriptor (bitCorner 5) gamma r (S.commit demoWord)
        ⟨demoWord, ext6Add ext6Zero ext6One⟩ =
      .error .valueMismatch := by
  decide +kernel

/-- Aux wire 5 changed: a trace that does not satisfy the descriptor. -/
def tamperedWord : Fin 23 → BabyBear := fun i => if i = 5 then demoWord 5 + 1 else demoWord i

/-- **Teeth, decided:** under the honest root the tampered word is refused at
the root, before any terminal arithmetic. -/
theorem realizer_refuses_forged_word :
    realize S.commit demoDescriptor (bitCorner 5) gamma r (S.commit demoWord)
        ⟨tamperedWord, ext6Zero⟩ =
      .error .rootMismatch := by
  decide +kernel

/-- The tampered trace violates the descriptor. -/
theorem tamperedWord_fails : ¬ descriptorHolds demoDescriptor (traceOf tamperedWord) := by
  decide +kernel

/-- The realizer AUTHENTICATES, it does not judge: at the tampered word's own
root the tampered opening is accepted, and its terminal is a NONZERO literal
-- the kernel ran the lane arithmetic through 23 residuals and five chi
factors to produce it.  Judging the trace is `honestRounds`' business
(`honestRounds_terminal` needs `descriptorHolds`). -/
theorem demo_tampered_terminal :
    laneTerminal gamma r (bitCorner 5)
        (descriptorResiduals demoDescriptor (traceOf tamperedWord)) ≠ ext6Zero := by
  decide +kernel

/-! ### The same instance through the Merkle scheme at the identity suite -/

/-- The demo word on the 32-leaf cube (`traceOf` reads wires `≥ 23` as `0` either way). -/
def demoWord32 : Fin (2 ^ 5) → BabyBear :=
  fun i => if h : i.val < 23 then demoWord ⟨i, h⟩ else 0

def tamperedWord32 : Fin (2 ^ 5) → BabyBear :=
  fun i => if h : i.val < 23 then tamperedWord ⟨i, h⟩ else 0

/-- The honest Merkle root: `cubeRoot` recomputed by the kernel. -/
def demoRoot : IdTree := (BinaryMerkle.openingScheme identitySuite 5).commit demoWord32

/-- **Satisfiable through the Merkle scheme, decided.** -/
theorem realizerMerkle_complete :
    realizeMerkle (k := 5) identitySuite demoDescriptor (bitCorner 5) gamma r demoRoot
        ⟨demoWord32, ext6Zero⟩ = .ok ext6Zero := by
  decide +kernel

/-- **Teeth through the Merkle scheme, decided:** the tampered word's recomputed
root differs, so it is refused before any terminal arithmetic. -/
theorem realizerMerkle_refuses_forged_word :
    realizeMerkle (k := 5) identitySuite demoDescriptor (bitCorner 5) gamma r demoRoot
        ⟨tamperedWord32, ext6Zero⟩ = .error .rootMismatch := by
  decide +kernel

/-- The premise of `realizeMerkle_sound` is inhabited at this instance. -/
theorem merkle_premise_inhabited : ¬ BinaryMerkle.Collision identitySuite :=
  identitySuite_collisionFree

end DemoInstance

/-! ## §9. Stage 0: the 4,131-wire candidate through the realizer (compiled exhibit) -/

namespace Stage0Exhibit

open Minidregg.Compiler.EvmAddAir

/-- `3,298 + 850 ≤ 2^13`, through the already kernel-decided shape
(`EvmAddAir.evmAddDescriptor_shape`; evaluating the flattening at elaboration
is the timeout Lane B documented). -/
theorem stage0_residuals_fit :
    evmAddDescriptor.gates.length + evmAddDescriptor.zeros.length ≤ 2 ^ 13 := by
  rw [evmAddDescriptor_shape.1, evmAddDescriptor_shape.2.2]
  norm_num

abbrev S : BindingCommitment (Fin 4131 → BabyBear) BabyBear (Fin 4131) Unit :=
  idealCommitment BabyBear (Fin 4131)

def gamma : Ext6L := ⟨2, 7, 1, 8, 2, 8⟩
def r : Fin 13 → Ext6L := fun i => ⟨((i : Nat) : BabyBear) * 31 + 1, 41, 59, 26, 53, 58⟩

def wordOf (c : Array BabyBear) : Fin 4131 → BabyBear := fun i => c.getD i 0

/-- One compiled exhibit, two 4,131-wire fills (the honest `(1, 2)` candidate and
the forged claim `Z = 4` on the same operands).  The honest opening is accepted
with terminal `0`; the forged word is refused at the honest root and
authenticated at its own root with a NONZERO terminal -- the realizer
authenticates, the descriptor check judges. -/
def exhibit : IO Unit := do
  let honest := wordOf (evmAddCandidate 1 2)
  match realize S.commit evmAddDescriptor (bitCorner 13) gamma r (S.commit honest)
      ⟨honest, ext6Zero⟩ with
  | .ok v =>
      if v = ext6Zero then IO.println "stage0 realizer: honest (1, 2) accepted, terminal 0"
      else throw (IO.userError "stage0 realizer: honest terminal is not 0")
  | .error e => throw (IO.userError s!"stage0 realizer: honest refused: {repr e}")
  let forged := wordOf (evmAddClaimed 1 2 4)
  let v := laneTerminal gamma r (bitCorner 13)
    (descriptorResiduals evmAddDescriptor (traceOf forged))
  if v = ext6Zero then throw (IO.userError "stage0 realizer: forged terminal is 0")
  match realize S.commit evmAddDescriptor (bitCorner 13) gamma r (S.commit honest)
      ⟨forged, v⟩ with
  | .error .rootMismatch => IO.println "stage0 realizer: forged word refused at the honest root"
  | _ => throw (IO.userError "stage0 realizer: forged word not refused at root")
  match realize S.commit evmAddDescriptor (bitCorner 13) gamma r (S.commit forged)
      ⟨forged, v⟩ with
  | .ok _ => IO.println s!"stage0 realizer: forged word authenticated at its own root, terminal {repr v}"
  | .error e => throw (IO.userError s!"stage0 realizer: forged self-opening refused: {repr e}")

#eval exhibit

end Stage0Exhibit

/-! ## §10. Named residuals (each an obligation, none assumed)

* `[CT-sampled]` -- the `t < 2^m` sampled-query realizer: `basefoldTableVerify`
  (`Selvage/BaseFoldRbrTable.lean:206`) over `TableMsg` columns with Merkle
  `openAt`/`verifyOpen`; its extractor needs the list-decoding seam
  `[ERASURE-list]`/`[OOD-pin-proximity]` (`Selvage/Erasure.lean`).  Statement
  exists in the tree; the computable verifier over lanes is ~250 lines.
* `[CT-factored7]` -- the controller's SEVEN factored terminals
  (`Ext6GateProofController.Receipt.terminalValue`, `GateFactoredExt6.lean:545
  LinearFunctionalOpening`) are linear functionals of the trace; the same
  sparse-sum construction realizes each (~150 lines) and would replace the
  opaque `traceOpeningProof`/`operandOpeningProof` bytes.
* `[CT-controller-lanes]` -- `Ext6GateProofController.Accepts` and `Verifier.check`
  live in `noncomputable section` because `Receipt` carries `Ext6Q` and
  `Polynomial Ext6Q`; a lane-carried receipt with `check_iff` proved through
  `toExt6` injectivity is the representation swap the scout named (~400 lines).
* `[CT-merkle-profile]` -- a computable BabyBear-leaf `HashSuite` for the
  Merkle instance (`BaseFoldPoseidon2.hashNode` is computable; the leaf packing
  is a profile decision) and its `[COMMIT-CR]` price.
* `[CT-compose]` -- the gamma-batching price: for a failing trace the zero
  claim is false unless `gamma` is a root of `Σ_k gamma^k res_k`
  (`≤ (N-1)/|Ext6Q|`), composed with `adaptive_sumcheck_soundness` at `d = 1`
  for the clear rounds.
-/

#check @read_laneTerminal
#check @mle_gammaResidualTable_sparse
#check @realize_sound
#check @committedTerminalOfBinding
#check @honestRounds_closes_realized
#check @DemoInstance.realizer_complete
#check @DemoInstance.realizer_refuses_forged_opening
#check @DemoInstance.realizer_refuses_forged_word
#check @DemoInstance.realizerMerkle_complete
#check @identitySuite_collisionFree

/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.read_laneTerminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_laneTerminal
/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.realize_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realize_sound
/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.honestRounds_closes_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestRounds_closes_realized
/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.DemoInstance.realizer_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.realizer_complete
/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.DemoInstance.realizer_refuses_forged_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.realizer_refuses_forged_opening
/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.DemoInstance.realizer_refuses_forged_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.realizer_refuses_forged_word
/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.DemoInstance.demo_tampered_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.demo_tampered_terminal
/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.realizeMerkle_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms realizeMerkle_sound
/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.DemoInstance.realizerMerkle_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.realizerMerkle_complete
/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.DemoInstance.realizerMerkle_refuses_forged_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.realizerMerkle_refuses_forged_word
/-- info: 'Minidregg.Compiler.CommittedTerminalRealizer.identitySuite_collisionFree' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms identitySuite_collisionFree

end Minidregg.Compiler.CommittedTerminalRealizer
