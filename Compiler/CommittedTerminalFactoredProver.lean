/-
# Compiler.CommittedTerminalFactoredProver -- [CT-factored-prover]: the quadratic factored
# protocol's honest prover and controller, in lanes

`CommittedTerminalController` decides the clear degree-one MLE sumcheck.  The protocol
`Ext6GateProofController.Accepts` reflects is the OTHER one: degree-two messages of
`Â·B̂ − Ĉ` (`factoredRounds = quadHonest (mulAGamma) (mulB) (combinedC)`), closing at the
seven factored terminals `terminalExpression` (`CommittedTerminalFactored7` realized them).
This module builds that protocol's honest prover and its computable controller beside
the degree-one one:

* **§1 dense tables, bit-corner layout.**  Under `bitCorner`, residual `k` sits at corner
  `k`, so the `A`, `B`, `C` tables ARE the payload lists padded with zeros to `2^m`
  (`tableA`/`tableB`/`tableC`, payloads matching `mulAGamma`, `mulB`, `combinedC` gate by
  gate: mul `(γ^k a, b, γ^k out)`, add `(0, 0, γ^k (out − a − b))`, root pin
  `(0, 0, −γ^{|gates|+j} z)`).  Linear in the descriptor to build.
* **§2 the fold and the round message.**  Coordinate `i` is the current least
  significant bit: `fold r` pairs consecutive entries `(x₀, x₁) ↦ (1 − r) x₀ + r x₁`;
  round `i`'s message is ONE walk over the paired tables -- `g(0) = Σ (a₀b₀ − c₀)`,
  `g(1) = Σ (a₁b₁ − c₁)`, `cross = Σ (a₁ − a₀)(b₁ − b₀)` -- the three numbers
  `quadRoundPoly` is built from.  `O(2^m)` per round, `O(2^{m+1})` in all; at Stage 0
  `2^13 = 8,192 ≈ 2N`.  (The sparse pairwise alternative the compose note sized,
  `Σ_{k,k'}` over pairs agreeing on the suffix bits, is `O(N·2^{m−i})` at round `i`
  without a hash-map grouping; the fold is the dense fold every BaseFold verifier
  already trusts.)
* **§3 the controller** `check7`: `realize7` on the seven, every round's Boolean check
  `g(0) + g(1) = claim` on the zero-anchored lane chain (`laneEval2` evaluates the
  quadratic at the challenge), the chain must close at `laneTerminalExpression` of the
  realized seven.  A plain `def`; `#eval` runs it.
* **§4 reflection and the ledger.**  `readPoly2 (g0, g1, ct) = C ct·X² + C (g1 − g0 − ct)·X
  + C g0` (`quadRoundPoly`'s shape exactly); `check7_accepts`: an accepted run is
  `GateProof7Accepts` in the field (degree `< 3`, rounds, closes at `terminalExpression`
  of the realized seven); **`gateProof7_sound`**: accepted against a root committing `w`
  under the named `BindingCommitment` ⇒ the trace satisfies the descriptor, or the gamma
  event, or the quadratic sumcheck event (`AdaptiveAcceptsFalse` against `quadHonest`,
  the tree's own) -- `realize7_sound` + `factored7_closes` (REUSED).  Prices:
  `sumcheck7_prob_le` = `quad_sumcheck_soundness` (REUSED), `m·2/|F|`; the gamma event
  is the SAME event as the degree-one protocol's (`gammaBatched_eq_sum_table`:
  `Σ_b (A·B − C)(b) = Σ_b gammaResidualTable b`), priced `(N−1)/|F|` by
  `gammaZero_prob_le` (REUSED).
* **§5 what closes and what is named.**  `[CT-factored-prover-honest]` -- the dense-fold
  lane messages read to `factoredRounds` -- enters as a `Prop` (`FactoredProverHonest`)
  with its consumer proved: `factoredProver_complete_of_honest` (the identity ⇒ the honest
  receipt passes `check7`, via `quadHonest_boolean_sum` and `factored7_closes`, REUSED).
  The identity itself is the fold lemma "`fold` at `r_i` of the level-`i` table is the
  level-`(i+1)` table of the MLE" plus the corner reading of the padded payload lists; it
  is NOT proved here.  Its ATLAS fields: satisfiable -- its CONSEQUENCE is decided on the
  emitted demo descriptor (`check7_complete_demo`: the fold prover's five messages and
  the seven pass `check7`) and compiled at Stage 0 (`exhibit`); teeth -- a tampered
  message is refused (`check7_refuses_tampered_message_demo`), the forged word refused at
  the root; premise-inhabitation -- `hfit` at the demo and Stage 0.

Label: *the factored protocol's honest prover EXISTS and its receipts are accepted at
Stage 0 and on the demo; its general completeness is one named identity away.*
-/

import Compiler.CommittedTerminalController

namespace Minidregg.Compiler.CommittedTerminalFactoredProver

open scoped BigOperators
open Minidregg.Assurance Minidregg.Selvage Minidregg.Compiler.GateMleExt6
open Minidregg.Compiler.GateFactoredExt6 Minidregg.Compiler.CommittedTerminalRealizer
open Minidregg.Compiler.CommittedTerminalFactored7 Minidregg.Compiler.CommittedTerminalCompose
open Minidregg.Compiler.Ext6GateProofController (terminalExpression)
open Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000

variable {m : Nat}

/-! ## §1. Dense tables in the bit-corner layout -/

/-- `A`'s gate payload: `γ^k · a` at a mul gate, else `0` (`mulAGamma`). -/
def payloadA (wv : Nat → BabyBear) (g : DGate BabyBear) (gpow : Ext6L) : Ext6L :=
  if g.op = .mul then ext6MulL gpow (ext6OfBase (g.a.read wv)) else ext6Zero

/-- `B`'s gate payload: `b` at a mul gate, else `0` (`mulB`, unweighted). -/
def payloadB (wv : Nat → BabyBear) (g : DGate BabyBear) (_gpow : Ext6L) : Ext6L :=
  if g.op = .mul then ext6OfBase (g.b.read wv) else ext6Zero

/-- `C`'s gate payload: `γ^k · out` at a mul gate, `γ^k · (out − a − b)` at an add gate
(`combinedC = mulC − addA − addB + addC` on gates). -/
def payloadC (wv : Nat → BabyBear) (g : DGate BabyBear) (gpow : Ext6L) : Ext6L :=
  match g.op with
  | .mul => ext6MulL gpow (ext6OfBase (wv g.out))
  | .add => ext6MulL gpow (ext6OfBase (wv g.out - g.a.read wv - g.b.read wv))

/-- Walk the gate list with the running gamma power. -/
def gateTable (gamma : Ext6L) (payload : DGate BabyBear → Ext6L → Ext6L) :
    List (DGate BabyBear) → Ext6L → List Ext6L
  | [], _ => []
  | g :: rest, gpow => payload g gpow :: gateTable gamma payload rest (ext6MulL gpow gamma)

/-- The root pins' `C` payload: `−γ^{|gates|+j} · z_j` (`−zeroGamma`). -/
def zeroTable (wv : Nat → BabyBear) (gamma : Ext6L) : List (DWire BabyBear) → Ext6L → List Ext6L
  | [], _ => []
  | z :: rest, gpow =>
      ext6Sub ext6Zero (ext6MulL gpow (ext6OfBase (z.read wv))) :: zeroTable wv gamma rest (ext6MulL gpow gamma)

/-- Pad with zeros to the cube size. -/
def padTo (len : Nat) (l : List Ext6L) : List Ext6L := l ++ List.replicate (len - l.length) ext6Zero

/-- The three dense tables on the `m`-cube: residual `k` at corner `k` (`bitCorner`). -/
def tableA (m : Nat) (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L) :
    List Ext6L :=
  padTo (2 ^ m) (gateTable gamma (payloadA wv) d.gates ext6One)

def tableB (m : Nat) (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L) :
    List Ext6L :=
  padTo (2 ^ m) (gateTable gamma (payloadB wv) d.gates ext6One)

def tableC (m : Nat) (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L) :
    List Ext6L :=
  padTo (2 ^ m) (gateTable gamma (payloadC wv) d.gates ext6One ++
    zeroTable wv gamma d.zeros (ext6Pow gamma d.gates.length))

/-! ## §2. The fold and the round message -/

/-- Fold the current least significant coordinate at `r`: `(x₀, x₁) ↦ (1 − r) x₀ + r x₁`. -/
def fold (r : Ext6L) : List Ext6L → List Ext6L
  | x0 :: x1 :: rest => ext6Add (ext6MulL (ext6Sub ext6One r) x0) (ext6MulL r x1) :: fold r rest
  | _ => []

/-- A round message: `(g(0), g(1), cross)` -- the quadratic engine's three numbers. -/
abbrev RoundMsg2 := Ext6L × Ext6L × Ext6L

def zeroMsg2 : RoundMsg2 := (ext6Zero, ext6Zero, ext6Zero)

/-- One walk over the paired tables. -/
def roundWalk2 : List Ext6L → List Ext6L → List Ext6L → RoundMsg2 → RoundMsg2
  | a0 :: a1 :: ra, b0 :: b1 :: rb, c0 :: c1 :: rc, (v0, v1, ct) =>
      roundWalk2 ra rb rc
        (ext6Add v0 (ext6Sub (ext6MulL a0 b0) c0),
          ext6Add v1 (ext6Sub (ext6MulL a1 b1) c1),
          ext6Add ct (ext6MulL (ext6Sub a1 a0) (ext6Sub b1 b0)))
  | _, _, _, acc => acc

def roundMsg2 (A B C : List Ext6L) : RoundMsg2 := roundWalk2 A B C zeroMsg2

/-- The factored protocol's lane transcript: degree-two messages, lane challenges. -/
structure Transcript2 (m : Nat) where
  message : Fin m → RoundMsg2
  challenge : Fin m → Ext6L

instance : DecidableEq (Transcript2 m) := fun a b =>
  decidable_of_iff (a.message = b.message ∧ a.challenge = b.challenge)
    (by cases a; cases b; simp)

/-- Round `i` and onward: emit the message of the current tables, fold at `r_i`, continue. -/
def honestGo (r : Fin m → Ext6L) : Nat → Nat → List Ext6L × List Ext6L × List Ext6L → List RoundMsg2
  | 0, _, _ => []
  | fuel + 1, i, (A, B, C) =>
      let ri := if h : i < m then r ⟨i, h⟩ else ext6Zero
      roundMsg2 A B C :: honestGo r fuel (i + 1) (fold ri A, fold ri B, fold ri C)

/-- **The honest factored messages**: `m` folds of the three dense tables. -/
def honestMessages (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L)
    (r : Fin m → Ext6L) : List RoundMsg2 :=
  honestGo r m 0 (tableA m d wv gamma, tableB m d wv gamma, tableC m d wv gamma)

/-- **The honest factored transcript** at challenges `r`. -/
def honestTranscript2 (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L)
    (r : Fin m → Ext6L) : Transcript2 m :=
  let msgs := honestMessages d wv gamma r
  ⟨fun i => msgs.getD i zeroMsg2, r⟩

/-! ## §3. The controller -/

/-- What an accepted factored run hands back. -/
structure Receipt7 (Root : Type) (m : Nat) where
  root : Root
  gamma : Ext6L
  transcript : Transcript2 m
  terminals : Fin 7 → Ext6L

instance {Root : Type} [DecidableEq Root] : DecidableEq (Receipt7 Root m) := fun a b =>
  decidable_of_iff
    (a.root = b.root ∧ a.gamma = b.gamma ∧ a.transcript = b.transcript ∧ a.terminals = b.terminals)
    (by cases a; cases b; simp)

/-- `g(t) = g(0) + (g(1) − g(0) − cross)·t + cross·t²`. -/
def laneEval2 (p : RoundMsg2) (t : Ext6L) : Ext6L :=
  ext6Add (ext6Add p.1 (ext6MulL (ext6Sub (ext6Sub p.2.1 p.1) p.2.2) t))
    (ext6MulL p.2.2 (ext6MulL t t))

def messageAt2 (tr : Transcript2 m) (i : Nat) : RoundMsg2 :=
  if h : i < m then tr.message ⟨i, h⟩ else zeroMsg2

def challengeAt2 (tr : Transcript2 m) (i : Nat) : Ext6L :=
  if h : i < m then tr.challenge ⟨i, h⟩ else ext6Zero

/-- The zero-anchored claim chain. -/
def laneChain2 (tr : Transcript2 m) : Nat → Ext6L
  | 0 => ext6Zero
  | i + 1 => laneEval2 (messageAt2 tr i) (challengeAt2 tr i)

def roundsOk2 (tr : Transcript2 m) : Bool :=
  (List.finRange m).all fun i =>
    decide (ext6Add (tr.message i).1 (tr.message i).2.1 = laneChain2 tr i)

/-- **The computable factored controller**: the seven realized, every round's Boolean check,
the chain closing at `terminalExpression` of the seven. -/
def check7 {Root : Type} [DecidableEq Root] {n : Nat} (commit : (Fin n → BabyBear) → Root)
    (d : ConstraintDescriptor BabyBear) (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L)
    (rt : Root) (op : Opening7 n) (tr : Transcript2 m) :
    Except CommittedTerminalController.Failure (Receipt7 Root m) :=
  match realize7 commit d encNat gamma tr.challenge rt op with
  | .error e => .error (.terminal e)
  | .ok v =>
      if roundsOk2 tr then
        if laneChain2 tr m = laneTerminalExpression v then .ok ⟨rt, gamma, tr, v⟩
        else .error .terminalMismatch
      else .error .roundCheck

section Check

variable {Root : Type} [DecidableEq Root] {n : Nat}
variable (commit : (Fin n → BabyBear) → Root) (d : ConstraintDescriptor BabyBear)
variable (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L)

theorem check7_ok_spec (rt : Root) (op : Opening7 n) (tr : Transcript2 m) (rc : Receipt7 Root m)
    (h : check7 commit d encNat gamma rt op tr = .ok rc) :
    realize7 commit d encNat gamma tr.challenge rt op = .ok rc.terminals ∧
      roundsOk2 tr = true ∧ laneChain2 tr m = laneTerminalExpression rc.terminals ∧
      rc.root = rt ∧ rc.gamma = gamma ∧ rc.transcript = tr := by
  unfold check7 at h
  split at h
  · exact absurd h (by simp)
  · rename_i v hv
    split at h
    · split at h
      · rename_i hr hc
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨hv, hr, hc, rfl, rfl, rfl⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)

theorem check7_ok_of (rt : Root) (op : Opening7 n) (tr : Transcript2 m) (v : Fin 7 → Ext6L)
    (hv : realize7 commit d encNat gamma tr.challenge rt op = .ok v)
    (hr : roundsOk2 tr = true) (hc : laneChain2 tr m = laneTerminalExpression v) :
    check7 commit d encNat gamma rt op tr = .ok ⟨rt, gamma, tr, v⟩ := by
  unfold check7
  rw [hv]
  simp [hr, hc]

theorem check7_refuses_terminal (rt : Root) (op : Opening7 n) (tr : Transcript2 m)
    (e : CommittedTerminalRealizer.Failure)
    (he : realize7 commit d encNat gamma tr.challenge rt op = .error e) :
    check7 commit d encNat gamma rt op tr = .error (.terminal e) := by
  unfold check7
  rw [he]

theorem check7_refuses_round (rt : Root) (op : Opening7 n) (tr : Transcript2 m)
    (v : Fin 7 → Ext6L) (hv : realize7 commit d encNat gamma tr.challenge rt op = .ok v)
    (hr : roundsOk2 tr = false) :
    check7 commit d encNat gamma rt op tr = .error .roundCheck := by
  unfold check7
  rw [hv]
  simp [hr]

end Check

/-! ## §4. Reflection into the field, and the ledger -/

/-- A lane message as `C ct·X² + C (g₁ − g₀ − ct)·X + C g₀` -- `quadRoundPoly`'s shape. -/
noncomputable def readPoly2 (p : RoundMsg2) : Polynomial Ext6Q :=
  C (readExt6 p.2.2) * X ^ 2 + C (readExt6 p.2.1 - readExt6 p.1 - readExt6 p.2.2) * X +
    C (readExt6 p.1)

theorem readPoly2_eval (p : RoundMsg2) (t : Ext6L) :
    (readPoly2 p).eval (readExt6 t) = readExt6 (laneEval2 p t) := by
  simp only [readPoly2, laneEval2, eval_add, eval_mul, eval_pow, eval_C, eval_X, read_add,
    read_mul, read_sub]
  ring

theorem readPoly2_eval_zero (p : RoundMsg2) : (readPoly2 p).eval 0 = readExt6 p.1 := by
  simp [readPoly2]

theorem readPoly2_eval_one (p : RoundMsg2) : (readPoly2 p).eval 1 = readExt6 p.2.1 := by
  simp [readPoly2]

theorem readPoly2_degree (p : RoundMsg2) :
    (readPoly2 p).degree < ((2 + 1 : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt Polynomial.degree_quadratic_le (by decide)

noncomputable def fieldProver2 (tr : Transcript2 m) : ℕ → Polynomial Ext6Q :=
  fun i => readPoly2 (messageAt2 tr i)

noncomputable def fieldChal2 (tr : Transcript2 m) : ℕ → Ext6Q :=
  fun i => readExt6 (challengeAt2 tr i)

theorem fieldChal2_eq (tr : Transcript2 m) :
    fieldChal2 tr = chalOf fun i => readExt6 (tr.challenge i) := by
  funext i
  unfold fieldChal2 challengeAt2 chalOf
  split <;> simp [read_zero]

theorem messageAt2_of_lt (tr : Transcript2 m) {i : Nat} (hi : i < m) :
    messageAt2 tr i = tr.message ⟨i, hi⟩ :=
  dif_pos hi

theorem read_laneChain2 (tr : Transcript2 m) (i : Nat) :
    readExt6 (laneChain2 tr i) = scChain 0 (fieldProver2 tr) (fieldChal2 tr) i := by
  cases i with
  | zero => simp [laneChain2, scChain, read_zero]
  | succ i =>
    show readExt6 (laneEval2 (messageAt2 tr i) (challengeAt2 tr i)) =
      (readPoly2 (messageAt2 tr i)).eval (readExt6 (challengeAt2 tr i))
    rw [readPoly2_eval]

theorem roundsOk2_iff (tr : Transcript2 m) :
    roundsOk2 tr = true ↔
      ∀ i : Fin m, ext6Add (tr.message i).1 (tr.message i).2.1 = laneChain2 tr i := by
  simp [roundsOk2, List.all_eq_true, List.mem_finRange]

section Sound

variable {Root Op : Type} [DecidableEq Root] {n : Nat}
variable (S : BindingCommitment Root BabyBear (Fin n) Op)
variable (d : ConstraintDescriptor BabyBear) (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L)

/-- **What the factored verifier decides, read into the field**: the clauses of
`Ext6GateProofController.Accepts` that are the protocol's (degree, rounds, closing at
`terminalExpression`), with the seven realized rather than carried. -/
structure GateProof7Accepts (r : Fin m → Ext6L) (rt : Root) (op : Opening7 n) (v : Fin 7 → Ext6L)
    (prover : ℕ → Polynomial Ext6Q) : Prop where
  terminal : realize7 S.commit d encNat gamma r rt op = .ok v
  degree : ∀ i, i < m → (prover i).degree < ((2 + 1 : ℕ) : WithBot ℕ)
  rounds : ∀ i, i < m → (prover i).eval 0 + (prover i).eval 1 =
    scChain 0 prover (chalOf fun i => readExt6 (r i)) i
  closes : scChain 0 prover (chalOf fun i => readExt6 (r i)) m =
    terminalExpression (fun j => readExt6 (v j))

/-- **Reflection**: an accepted run is `GateProof7Accepts` with the transcript's messages as
the prover. -/
theorem check7_accepts (rt : Root) (op : Opening7 n) (tr : Transcript2 m) (rc : Receipt7 Root m)
    (h : check7 S.commit d encNat gamma rt op tr = .ok rc) :
    GateProof7Accepts S d encNat gamma tr.challenge rt op rc.terminals (fieldProver2 tr) := by
  obtain ⟨hv, hr, hc, -, -, -⟩ := check7_ok_spec S.commit d encNat gamma rt op tr rc h
  refine ⟨hv, fun i _ => readPoly2_degree _, ?_, ?_⟩
  · intro i hi
    have hlane := (roundsOk2_iff tr).mp hr ⟨i, hi⟩
    have hread := congrArg readExt6 hlane
    rw [read_add, read_laneChain2, fieldChal2_eq] at hread
    rw [show fieldProver2 tr i = readPoly2 (messageAt2 tr i) from rfl, readPoly2_eval_zero,
      readPoly2_eval_one, messageAt2_of_lt tr hi]
    exact hread
  · have hread := congrArg readExt6 hc
    rw [read_laneChain2, fieldChal2_eq, read_laneTerminalExpression] at hread
    exact hread

/-- **The factored zero claim is the degree-one zero claim**: `Σ_b (A·B − C)(b)` is the
gamma-batched residual (`quadraticTable_sum_eq_gammaBatchedDescriptorResidual`, REUSED), and
that is `Σ_b gammaResidualTable b` (`sum_gammaResidualTable`, REUSED) -- the residual list
reindexed over gates then root pins. -/
theorem gammaBatched_eq_sum_table (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool)) (g : Ext6Q) :
    gammaBatchedDescriptorResidual d wv g = ∑ b, gammaResidualTable d wv enc g b := by
  rw [sum_gammaResidualTable, gammaBatchedDescriptorResidual]
  have hres : ∀ k : Fin (descriptorResiduals d wv).length,
      g ^ (k : Nat) * algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get k) =
        g ^ (k : Nat) * algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).getD k 0) := by
    intro k
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem k.isLt, Option.getD_some,
      List.get_eq_getElem]
  have hgate : ∀ k : Fin d.gates.length,
      g ^ (k : Nat) * algebraMap BabyBear Ext6Q (gateResidual wv (d.gates.get k)) =
        g ^ (k : Nat) * algebraMap BabyBear Ext6Q (gateResidual wv (d.gates.getD k dummyGate)) := by
    intro k
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem k.isLt, Option.getD_some,
      List.get_eq_getElem]
  have hzero : ∀ j : Fin d.zeros.length,
      g ^ (d.gates.length + (j : Nat)) * algebraMap BabyBear Ext6Q ((d.zeros.get j).read wv) =
        g ^ (d.gates.length + (j : Nat)) *
          algebraMap BabyBear Ext6Q ((d.zeros.getD j (DWire.cnst 0)).read wv) := by
    intro j
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt, Option.getD_some,
      List.get_eq_getElem]
  rw [Finset.sum_congr rfl (fun k _ => hres k), Finset.sum_congr rfl (fun k _ => hgate k),
    Finset.sum_congr rfl (fun j _ => hzero j),
    Fin.sum_univ_eq_sum_range (fun k => g ^ k * algebraMap BabyBear Ext6Q
      ((descriptorResiduals d wv).getD k 0)),
    Fin.sum_univ_eq_sum_range (fun k => g ^ k * algebraMap BabyBear Ext6Q
      (gateResidual wv (d.gates.getD k dummyGate))),
    Fin.sum_univ_eq_sum_range (fun j => g ^ (d.gates.length + j) * algebraMap BabyBear Ext6Q
      ((d.zeros.getD j (DWire.cnst 0)).read wv)),
    descriptorResiduals_length, Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < d.gates.length := Finset.mem_range.mp hk
    congr 2
    unfold descriptorResiduals
    have hk1 : k < (d.gates.map (gateResidual wv)).length := by
      rw [List.length_map]; exact hk'
    rw [List.getD_append _ _ _ _ hk1, List.getD_eq_getElem _ _ hk1, List.getElem_map,
      List.getD_eq_getElem _ _ hk']
  · apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < d.zeros.length := Finset.mem_range.mp hj
    congr 2
    unfold descriptorResiduals
    have hj1 : (d.gates.map (gateResidual wv)).length ≤ d.gates.length + j := by
      rw [List.length_map]; omega
    have hj2 : j < (d.zeros.map fun z => z.read wv).length := by
      rw [List.length_map]; exact hj'
    rw [List.getD_append_right _ _ _ _ hj1, List.length_map, Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ hj2, List.getElem_map, List.getD_eq_getElem _ _ hj']

/-- **The ledger theorem for the factored protocol.**  Accepted against a root committing `w`
under the named `BindingCommitment` `S`, with messages from any strategy `P` at the actual
challenges: the trace satisfies the descriptor, or the gamma event (the SAME event as the
degree-one protocol's, `gammaBatched_eq_sum_table`), or the quadratic sumcheck event against
the tree's `quadHonest` at the factored tables.  The terminal contributes no event:
`realize7_sound` is exact under `S`; `factored7_closes` (REUSED) is the honest chain's
terminal. -/
theorem gateProof7_sound (r : Fin m → Ext6L) (w : Fin n → BabyBear) (op : Opening7 n)
    (v : Fin 7 → Ext6L)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k)
    (P : (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q)
    (hacc : GateProof7Accepts S d encNat gamma r (S.commit w) op v
      (P (chalOf fun i => readExt6 (r i)))) :
    descriptorHolds d (traceOf w) ∨
      (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b) = 0 ∨
      AdaptiveAcceptsFalse P
        (quadHonest (mulAGamma d (traceOf w) enc (readExt6 gamma)) (mulB d (traceOf w) enc)
          (combinedC d (traceOf w) enc (readExt6 gamma)))
        0 (∑ b, (mulAGamma d (traceOf w) enc (readExt6 gamma) b * mulB d (traceOf w) enc b -
          combinedC d (traceOf w) enc (readExt6 gamma) b))
        (fun i => readExt6 (r i)) := by
  by_cases hd : descriptorHolds d (traceOf w)
  · exact Or.inl hd
  by_cases hz : (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b) = 0
  · exact Or.inr (Or.inl hz)
  have hsum : (∑ b, (mulAGamma d (traceOf w) enc (readExt6 gamma) b * mulB d (traceOf w) enc b -
      combinedC d (traceOf w) enc (readExt6 gamma) b)) =
      ∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b := by
    rw [quadraticTable_sum_eq_gammaBatchedDescriptorResidual, gammaBatched_eq_sum_table]
  refine Or.inr (Or.inr ⟨hacc.rounds, ?_, fun h => hz (by rw [← hsum]; exact h.symm)⟩)
  rw [hacc.closes, realize7_sound S d encNat gamma r w op v hacc.terminal]
  have hclose := factored7_closes d (traceOf w) enc encNat hEnc gamma r
  rw [gammaBatched_eq_sum_table d (traceOf w) enc, ← hsum] at hclose
  exact hclose.symm

/-- **The quadratic sumcheck price**: `quad_sumcheck_soundness` (REUSED) at the factored
tables -- `m · 2/|F|` against any prefix-measurable degree-`< 3` strategy. -/
theorem sumcheck7_prob_le (A B C : (Fin m → Bool) → Ext6Q)
    (P : (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q) (hpm : PrefixMeasurable P)
    (hdeg : ∀ (χ : ℕ → Ext6Q) (i : ℕ), i < m →
      (P χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → Ext6Q)
      (AdaptiveAcceptsFalse P (quadHonest A B C) 0 (∑ b, (A b * B b - C b))) ≤
      (m : ℝ) * (2 / Fintype.card Ext6Q) :=
  quad_sumcheck_soundness hpm hdeg

/-- The transcript as a constant strategy discharges both hypotheses. -/
noncomputable def constantStrategy2 (tr : Transcript2 m) : (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q :=
  fun _ => fieldProver2 tr

theorem constantStrategy2_prefixMeasurable (tr : Transcript2 m) :
    PrefixMeasurable (constantStrategy2 tr) :=
  fun _ _ _ _ => rfl

theorem constantStrategy2_degree (tr : Transcript2 m) (χ : ℕ → Ext6Q) (i : ℕ) (_ : i < m) :
    (constantStrategy2 tr χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ) :=
  readPoly2_degree _

/-- Refusal through binding: any other word under the honest root is refused at the root. -/
theorem receipt7_refuses_tamper (w : Fin n → BabyBear) (op : Opening7 n) (tr : Transcript2 m)
    (hne : op.word ≠ w) :
    check7 S.commit d encNat gamma (S.commit w) op tr = .error (.terminal .rootMismatch) :=
  check7_refuses_terminal S.commit d encNat gamma (S.commit w) op tr .rootMismatch
    (realize7_other_word_refused S d encNat gamma tr.challenge w op hne)

end Sound

/-! ## §5. The honest prover's completeness: the named identity and its consumer -/

/-- **[CT-factored-prover-honest] (named, not closed here).**  The dense-fold lane message of
round `i` reads to the quadratic engine's honest round polynomial at the bit-corner
embedding: `readPoly2 (honest message i) = factoredRounds … i`.  Its proof is the fold
lemma (`fold` at `r_i` of the level-`i` tables is the level-`(i+1)` restriction of the MLEs,
`mle_multilinear` coordinate by coordinate) plus the corner reading of the padded payload
lists (`sparseTable_read` at `bitCorner`).  Its CONSEQUENCE is decided on the demo
(`check7_complete_demo`) and compiled at Stage 0. -/
def FactoredProverHonest : Prop :=
  ∀ (m : Nat) (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (hfit : d.gates.length + d.zeros.length ≤ 2 ^ m) (gamma : Ext6L) (r : Fin m → Ext6L)
    (i : Fin m),
    readPoly2 ((honestTranscript2 d wv gamma r).message i) =
      factoredRounds d wv (residualEmbedding d wv hfit) (readExt6 gamma)
        (chalOf fun q => readExt6 (r q)) i.val

section Complete

variable {Root : Type} [DecidableEq Root] {n : Nat}
variable (commit : (Fin n → BabyBear) → Root) (d : ConstraintDescriptor BabyBear)
variable (gamma : Ext6L) (r : Fin m → Ext6L)

/-- **Completeness, conditional on the named identity**: for a satisfying word, the honest
seven with the fold prover's messages pass `check7` -- `quadHonest_boolean_sum` at the zero
claim (`gammaBatchedDescriptorResidual_zero_of_holds`) and `factored7_closes`, REUSED, carried
to lanes by `readExt6_injective`. -/
theorem factoredProver_complete_of_honest (H : FactoredProverHonest) (w : Fin n → BabyBear)
    (hfit : d.gates.length + d.zeros.length ≤ 2 ^ m) (hd : descriptorHolds d (traceOf w)) :
    check7 commit d (bitCorner m) gamma (commit w)
        ⟨w, laneTerminal7 d (traceOf w) gamma r (bitCorner m)⟩
        (honestTranscript2 d (traceOf w) gamma r) =
      .ok ⟨commit w, gamma, honestTranscript2 d (traceOf w) gamma r,
        laneTerminal7 d (traceOf w) gamma r (bitCorner m)⟩ := by
  set enc := residualEmbedding d (traceOf w) hfit with henc
  have hEnc : ∀ k, enc k = bitCorner m k := fun _ => rfl
  have hprover : fieldProver2 (honestTranscript2 d (traceOf w) gamma r) =
      factoredRounds d (traceOf w) enc (readExt6 gamma) (chalOf fun q => readExt6 (r q)) := by
    funext i
    unfold fieldProver2 messageAt2
    by_cases hi : i < m
    · rw [dif_pos hi]
      exact H m d (traceOf w) hfit gamma r ⟨i, hi⟩
    · rw [dif_neg hi]
      show readPoly2 zeroMsg2 = quadHonest _ _ _ _ i
      rw [quadHonest, dif_neg hi]
      simp [readPoly2, zeroMsg2, read_zero]
  have hzero : gammaBatchedDescriptorResidual d (traceOf w) (readExt6 gamma) = 0 :=
    gammaBatchedDescriptorResidual_zero_of_holds d (traceOf w) (readExt6 gamma) hd
  have hchal : fieldChal2 (honestTranscript2 d (traceOf w) gamma r) =
      chalOf fun q => readExt6 (r q) := fieldChal2_eq _
  have hbool := factoredRounds_boolean_sum d (traceOf w) enc (readExt6 gamma)
    (fun q => readExt6 (r q))
  rw [hzero] at hbool
  have hrounds : roundsOk2 (honestTranscript2 d (traceOf w) gamma r) = true := by
    rw [roundsOk2_iff]
    intro i
    apply lane_eq_of_read
    rw [read_add, read_laneChain2, hprover, hchal, ← hbool i.val i.isLt, ← hprover]
    show readExt6 ((honestTranscript2 d (traceOf w) gamma r).message i).1 +
        readExt6 ((honestTranscript2 d (traceOf w) gamma r).message i).2.1 =
      (readPoly2 (messageAt2 (honestTranscript2 d (traceOf w) gamma r) i.val)).eval 0 +
        (readPoly2 (messageAt2 (honestTranscript2 d (traceOf w) gamma r) i.val)).eval 1
    rw [readPoly2_eval_zero, readPoly2_eval_one, messageAt2_of_lt _ i.isLt]
  have hclose : laneChain2 (honestTranscript2 d (traceOf w) gamma r) m =
      laneTerminalExpression (laneTerminal7 d (traceOf w) gamma r (bitCorner m)) := by
    apply lane_eq_of_read
    rw [read_laneChain2, hprover, hchal, read_laneTerminalExpression]
    have hfinal := factored7_closes d (traceOf w) enc (bitCorner m) hEnc gamma r
    rw [hzero] at hfinal
    exact hfinal
  exact check7_ok_of commit d (bitCorner m) gamma (commit w) _ _ _
    (realize7_complete commit d (bitCorner m) gamma r w) hrounds hclose

end Complete

/-! ## §6. ATLAS fields on the emitted demo descriptor, decided -/

namespace DemoInstance

open CommittedTerminalRealizer.DemoInstance CommittedTerminalFactored7.DemoInstance

/-- The fold prover's five messages on the demo trace (32-entry tables), computed by the
kernel. -/
def honestTr2 : Transcript2 5 := honestTranscript2 demoDescriptor (traceOf demoWord) gamma r

/-- **Satisfiable, decided (the consequence of the named identity at this instance)**: the
honest seven (`demoSeven`, pinned literals) with the fold prover's five degree-two messages
are accepted by `check7` -- the kernel built the three 32-entry tables, folded them five
times, walked the pairs, realized the seven, and decided every round and the closing
against `laneTerminalExpression demoSeven` (nonzero: `factored7_ne_single`). -/
theorem check7_complete_demo :
    check7 S.commit demoDescriptor (bitCorner 5) gamma (S.commit demoWord) ⟨demoWord, demoSeven⟩
        honestTr2 = .ok ⟨demoWord, gamma, honestTr2, demoSeven⟩ := by
  decide +kernel

/-- **Teeth, decided**: message `2`'s `g(0)` shifted by one is refused at its round check. -/
theorem check7_refuses_tampered_message_demo :
    check7 S.commit demoDescriptor (bitCorner 5) gamma (S.commit demoWord) ⟨demoWord, demoSeven⟩
        ⟨Function.update honestTr2.message 2
          (ext6Add (honestTr2.message 2).1 ext6One, (honestTr2.message 2).2), r⟩ =
      .error .roundCheck := by
  decide +kernel

/-- **Teeth, decided**: the tampered word under the honest root is refused at the root. -/
theorem check7_refuses_tamper_demo :
    check7 S.commit demoDescriptor (bitCorner 5) gamma (S.commit demoWord)
        ⟨tamperedWord, demoSeven⟩ honestTr2 = .error (.terminal .rootMismatch) := by
  decide +kernel

/-- **Teeth, decided**: the honest word's seven claimed with the ZERO transcript: every round
check passes on the zero chain, and the chain closes at `0 ≠ laneTerminalExpression demoSeven`
(`factored7_ne_single`). -/
theorem check7_refuses_zero_transcript_demo :
    check7 S.commit demoDescriptor (bitCorner 5) gamma (S.commit demoWord) ⟨demoWord, demoSeven⟩
        ⟨fun _ => zeroMsg2, r⟩ = .error .terminalMismatch := by
  decide +kernel

end DemoInstance

/-! ## §7. Stage 0: the factored proof of the 4,131-wire candidate (compiled exhibit) -/

namespace Stage0Exhibit

open CommittedTerminalRealizer.Stage0Exhibit
open Minidregg.Compiler.DescriptorEval Minidregg.Compiler.EvmAddAir

/-- The honest `(1, 2)` candidate: its seven realized, its thirteen degree-two messages by the
fold prover (three 8,192-entry tables folded thirteen times), accepted end to end by `check7`;
the forged `Z = 4` word refused at the honest root, and at its own root with its own seven and
its own honest prover refused at a round check (its factored zero claim is nonzero at this
`γ`).  Throws on any deviation. -/
def exhibit : IO Unit := do
  let honest := wordOf (evmAddCandidate 1 2)
  let seven := laneTerminal7 evmAddDescriptor (traceOf honest) gamma r (bitCorner 13)
  let tr := honestTranscript2 evmAddDescriptor (traceOf honest) gamma r
  match check7 S.commit evmAddDescriptor (bitCorner 13) gamma (S.commit honest) ⟨honest, seven⟩ tr with
  | .ok rc =>
      if rc.terminals = seven then
        IO.println "stage0 factored prover: honest (1, 2) factored proof accepted end to end: 13 degree-two rounds, closing at the seven realized terminals"
      else throw (IO.userError "stage0 factored prover: accepted receipt carries other terminals")
  | .error e => throw (IO.userError s!"stage0 factored prover: honest proof refused: {repr e}")
  IO.println s!"stage0 factored prover: message 0 = {repr (tr.message 0)}"
  let forged := wordOf (evmAddClaimed 1 2 4)
  match check7 S.commit evmAddDescriptor (bitCorner 13) gamma (S.commit honest) ⟨forged, seven⟩ tr with
  | .error (.terminal .rootMismatch) =>
      IO.println "stage0 factored prover: forged word refused at the honest root"
  | _ => throw (IO.userError "stage0 factored prover: forged word not refused at the root")
  let sevenF := laneTerminal7 evmAddDescriptor (traceOf forged) gamma r (bitCorner 13)
  let trF := honestTranscript2 evmAddDescriptor (traceOf forged) gamma r
  match check7 S.commit evmAddDescriptor (bitCorner 13) gamma (S.commit forged) ⟨forged, sevenF⟩ trF with
  | .error .roundCheck =>
      IO.println "stage0 factored prover: forged word at its own root, its own honest factored prover refused at a round check (zero claim false)"
  | _ => throw (IO.userError "stage0 factored prover: forged self-proof not refused at a round")

#eval exhibit

end Stage0Exhibit

#check @check7
#check @check7_accepts
#check @gateProof7_sound
#check @sumcheck7_prob_le
#check @gammaBatched_eq_sum_table
#check FactoredProverHonest
#check @factoredProver_complete_of_honest

/-- info: 'Minidregg.Compiler.CommittedTerminalFactoredProver.check7_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms check7_accepts
/-- info: 'Minidregg.Compiler.CommittedTerminalFactoredProver.gammaBatched_eq_sum_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gammaBatched_eq_sum_table
/-- info: 'Minidregg.Compiler.CommittedTerminalFactoredProver.gateProof7_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gateProof7_sound
/-- info: 'Minidregg.Compiler.CommittedTerminalFactoredProver.sumcheck7_prob_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sumcheck7_prob_le
/-- info: 'Minidregg.Compiler.CommittedTerminalFactoredProver.factoredProver_complete_of_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms factoredProver_complete_of_honest
/-- info: 'Minidregg.Compiler.CommittedTerminalFactoredProver.DemoInstance.check7_complete_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.check7_complete_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalFactoredProver.DemoInstance.check7_refuses_tampered_message_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.check7_refuses_tampered_message_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalFactoredProver.DemoInstance.check7_refuses_tamper_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.check7_refuses_tamper_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalFactoredProver.DemoInstance.check7_refuses_zero_transcript_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.check7_refuses_zero_transcript_demo

end Minidregg.Compiler.CommittedTerminalFactoredProver
