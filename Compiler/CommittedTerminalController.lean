/-
# Compiler.CommittedTerminalController -- the full-word gate proof, decided by a `def`

`Ext6GateProofController.Accepts` (`:323`) is a `Prop` in a `noncomputable
section`, and `Ext6GateProofDeployment.check` (`:230`) is `decide` under
`classical`: nothing in the tree RUNS a gate-proof verifier.  The obstruction,
exactly: `Receipt` (`:216`) carries `gamma`, `roundChallenge`, `terminalValue`,
`eta`, `aggregateValue` in `Ext6Q = AdjoinRoot ext6Polynomial` and
`roundMessage` in `Polynomial Ext6Q` -- every field's arithmetic is
`AdjoinRoot.instField`, which is `noncomputable`; `derivedGamma`/`derivedEta`
land in `Ext6Q` through `digestToExt6 := toExt6 ∘ …` (`:56`, `toExt6` is
`noncomputable`); `etaAggregateLeft` (`:299`) sums `Finsupp`-weighted
functionals.  No edit to that file makes it computable short of replacing its
carrier; this module builds the computable controller BESIDE it, on the lane
carrier `Ext6L`, for the protocol whose terminal the realizer authenticates.

**Which protocol.**  The clear degree-one MLE sumcheck of `GateMleExt6`
(`honestRounds = mleHonest (gammaResidualTable …)`), zero-anchored, closing at
the single realized terminal -- the one `honestRounds_closes_realized` closes
and `CommittedTerminalCompose.gateProof_sound` prices.  It is NOT the
quadratic factored protocol `Accepts` reflects (seven terminals, degree-two
messages); that protocol's seven terminals are realized in
`CommittedTerminalFactored7`, but its honest prover is a pairwise product
over the sparse tables and is not built here (`[CT-factored-prover]`, sized
below).

* **The lane transcript.**  `Transcript m`: round messages as the two Boolean
  evaluations `(g(0), g(1))` of a degree-`≤ 1` polynomial (the
  `ZkmlMatmulSuccinctChecker.RoundMessage` idiom), challenges as lanes.
  `Receipt`: root, gamma, transcript, realized terminal.
* **`check`** -- `realize` on the opening, then every round's Boolean check on
  the zero-anchored lane chain (`laneChain` mirrors `scChain 0`), then the
  chain must close at the realized terminal.  A plain `def`; `#eval` runs it.
* **The reflection.**  `readPoly1` reads a lane message into `Polynomial Ext6Q`
  (`C (g₁ − g₀) X + C g₀`, the shape of `roundPoly`); `check_accepts`: an
  accepted run is `GateProofAccepts` in the field.  Hence `gateProof_sound_lane`
  -- the ledger theorem, at the controller.
* **The honest lane prover.**  `laneRound` computes round `i`'s message by one
  walk over the residual list -- for residual `k` at corner `b`, the weight
  `γ^k · res_k · ∏_{j<i} χ_{b_j}(r_j)` goes to `g(0)` or `g(1)` by `b_i` --
  linear in the descriptor, never `2^m`.  `residualSum_sparse` is the identity
  that makes it honest: the level-`k` residual claim of a sparse MLE is the
  prefix-chi sum (downward induction on `k` through `residualSum_step`, REUSED);
  `readPoly1_laneRound`: the lane message IS `mleHonest` (`fieldProver_honest`,
  as functions).
* **`receipt_complete`** -- honest word, satisfying trace ⇒ `.ok`
  (`mleHonest_boolean_sum`, `scChain_mleHonest_final`, REUSED, carried to lanes
  by `readExt6_injective`).  **`receipt_refuses_tamper`** -- any other word
  under the honest root is refused at the root.  **`receipt_refuses_false_claim`**
  -- a failing trace whose batched residual is nonzero has its OWN honest
  prover refused at round `0` (the gamma leg, closed for the honest prover;
  the adversarial prover is the ledger's business).

**ATLAS fields (law 2), decided by the kernel on `demoDescriptor` (`m = 5`,
23 residuals) at `idealCommitment`:** `receipt_complete_demo` (the honest
5-round proof accepted; its messages are all `(0, 0)` because a satisfying
trace's table is zero, and the kernel computed them), teeth:
`receipt_refuses_tamper_demo` (root), `receipt_refuses_false_claim_demo` (the
tampered trace's honest prover, refused at a round check),
`receipt_refuses_forged_terminal_demo` (the tampered trace with the zero
transcript, refused at the terminal against its pinned nonzero terminal),
`receipt_refuses_tampered_message_demo` (one honest message replaced).
Stage 0 (`m = 13`, 4,148 residuals, 4,131 wires) is the compiled `#eval`:
the honest `(1, 2)` proof accepted end to end; the forged `Z = 4` word refused
at the root, at a round check with its own honest prover, and at the terminal
with the honest word's transcript.
-/

import Compiler.CommittedTerminalCompose

namespace Minidregg.Compiler.CommittedTerminalController

open scoped BigOperators
open Minidregg.Assurance Minidregg.Selvage Minidregg.Compiler.GateMleExt6
open Minidregg.Compiler.CommittedTerminalRealizer Minidregg.Compiler.CommittedTerminalFactored7
open Minidregg.Compiler.CommittedTerminalCompose
open Polynomial

set_option autoImplicit false
set_option maxRecDepth 10000

variable {m : Nat}

/-! ## §1. Lane transcript, receipt, and the controller -/

/-- A round message: the degree-`≤ 1` polynomial as `(g(0), g(1))`. -/
abbrev RoundMsg := Ext6L × Ext6L

/-- The sumcheck transcript in lanes. -/
structure Transcript (m : Nat) where
  message : Fin m → RoundMsg
  challenge : Fin m → Ext6L

/-- Decidable equality by fields through `decidable_of_iff`, NOT the derived
instance: the derived one casts along each field equality (`h ▸ …`), and the
kernel can reduce that cast only when both sides are the same term -- never
for two function fields that merely agree pointwise (`decide +kernel` on a
computed transcript against a literal one got stuck exactly there).  The pi
instance underneath iterates the concrete indices, as `ext6_known_product`
already relies on. -/
instance : DecidableEq (Transcript m) := fun a b =>
  decidable_of_iff (a.message = b.message ∧ a.challenge = b.challenge)
    (by cases a; cases b; simp)

/-- What an accepted run hands back. -/
structure Receipt (Root : Type) (m : Nat) where
  root : Root
  gamma : Ext6L
  transcript : Transcript m
  terminal : Ext6L

instance {Root : Type} [DecidableEq Root] : DecidableEq (Receipt Root m) := fun a b =>
  decidable_of_iff
    (a.root = b.root ∧ a.gamma = b.gamma ∧ a.transcript = b.transcript ∧ a.terminal = b.terminal)
    (by cases a; cases b; simp)

/-- Every route by which the controller refuses. -/
inductive Failure
  /-- The realizer refused (root or value). -/
  | terminal (e : CommittedTerminalRealizer.Failure)
  /-- Some round's Boolean check failed. -/
  | roundCheck
  /-- The chain does not close at the realized terminal. -/
  | terminalMismatch
  deriving DecidableEq, Repr

/-- `g(0) + (g(1) − g(0)) · t`. -/
def laneEval (p : RoundMsg) (t : Ext6L) : Ext6L :=
  ext6Add p.1 (ext6MulL (ext6Sub p.2 p.1) t)

/-- Totalized views (junk past `m`, never consulted), as the controller's
`roundMessages`/`roundChallenges`. -/
def messageAt (tr : Transcript m) (i : Nat) : RoundMsg :=
  if h : i < m then tr.message ⟨i, h⟩ else (ext6Zero, ext6Zero)

def challengeAt (tr : Transcript m) (i : Nat) : Ext6L :=
  if h : i < m then tr.challenge ⟨i, h⟩ else ext6Zero

/-- The zero-anchored claim chain in lanes: `scChain 0`, structurally. -/
def laneChain (tr : Transcript m) : Nat → Ext6L
  | 0 => ext6Zero
  | i + 1 => laneEval (messageAt tr i) (challengeAt tr i)

/-- Every round's Boolean check `g_i(0) + g_i(1) = claim_i`. -/
def roundsOk (tr : Transcript m) : Bool :=
  (List.finRange m).all fun i =>
    decide (ext6Add (tr.message i).1 (tr.message i).2 = laneChain tr i)

/-- **The computable controller.**  The statement's root, the opening (whole
word + claimed terminal), the transcript; `gamma` and the challenges are
transcript inputs (their Fiat-Shamir derivation is not this controller's). -/
def check {Root : Type} [DecidableEq Root] {n : Nat} (commit : (Fin n → BabyBear) → Root)
    (d : ConstraintDescriptor BabyBear) (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L)
    (rt : Root) (op : Opening n) (tr : Transcript m) : Except Failure (Receipt Root m) :=
  match realize commit d encNat gamma tr.challenge rt op with
  | .error e => .error (.terminal e)
  | .ok v =>
      if roundsOk tr then
        if laneChain tr m = v then .ok ⟨rt, gamma, tr, v⟩ else .error .terminalMismatch
      else .error .roundCheck

section Check

variable {Root : Type} [DecidableEq Root] {n : Nat}
variable (commit : (Fin n → BabyBear) → Root) (d : ConstraintDescriptor BabyBear)
variable (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L)

theorem check_ok_spec (rt : Root) (op : Opening n) (tr : Transcript m) (rc : Receipt Root m)
    (h : check commit d encNat gamma rt op tr = .ok rc) :
    realize commit d encNat gamma tr.challenge rt op = .ok rc.terminal ∧
      roundsOk tr = true ∧ laneChain tr m = rc.terminal ∧
      rc.root = rt ∧ rc.gamma = gamma ∧ rc.transcript = tr := by
  unfold check at h
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

theorem check_ok_of (rt : Root) (op : Opening n) (tr : Transcript m) (v : Ext6L)
    (hv : realize commit d encNat gamma tr.challenge rt op = .ok v)
    (hr : roundsOk tr = true) (hc : laneChain tr m = v) :
    check commit d encNat gamma rt op tr = .ok ⟨rt, gamma, tr, v⟩ := by
  unfold check
  rw [hv]
  simp [hr, hc]

theorem check_refuses_terminal (rt : Root) (op : Opening n) (tr : Transcript m)
    (e : CommittedTerminalRealizer.Failure)
    (he : realize commit d encNat gamma tr.challenge rt op = .error e) :
    check commit d encNat gamma rt op tr = .error (.terminal e) := by
  unfold check
  rw [he]

theorem check_refuses_round (rt : Root) (op : Opening n) (tr : Transcript m) (v : Ext6L)
    (hv : realize commit d encNat gamma tr.challenge rt op = .ok v)
    (hr : roundsOk tr = false) :
    check commit d encNat gamma rt op tr = .error .roundCheck := by
  unfold check
  rw [hv]
  simp [hr]

theorem check_refuses_close (rt : Root) (op : Opening n) (tr : Transcript m) (v : Ext6L)
    (hv : realize commit d encNat gamma tr.challenge rt op = .ok v)
    (hr : roundsOk tr = true) (hc : laneChain tr m ≠ v) :
    check commit d encNat gamma rt op tr = .error .terminalMismatch := by
  unfold check
  rw [hv]
  simp [hr, hc]

end Check

/-! ## §2. Reflection into the field -/

/-- A lane message as the polynomial `C (g₁ − g₀) · X + C g₀` -- `roundPoly`'s shape. -/
noncomputable def readPoly1 (p : RoundMsg) : Polynomial Ext6Q :=
  C (readExt6 p.2 - readExt6 p.1) * X + C (readExt6 p.1)

theorem readPoly1_eval (p : RoundMsg) (t : Ext6L) :
    (readPoly1 p).eval (readExt6 t) = readExt6 (laneEval p t) := by
  simp only [readPoly1, laneEval, eval_add, eval_mul, eval_C, eval_X, read_add, read_mul, read_sub]
  ring

theorem readPoly1_eval_zero (p : RoundMsg) : (readPoly1 p).eval 0 = readExt6 p.1 := by
  simp [readPoly1]

theorem readPoly1_eval_one (p : RoundMsg) : (readPoly1 p).eval 1 = readExt6 p.2 := by
  simp [readPoly1]

theorem readPoly1_degree (p : RoundMsg) :
    (readPoly1 p).degree < ((1 + 1 : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt Polynomial.degree_linear_le (by decide)

/-- The transcript's messages as the field prover, totalized. -/
noncomputable def fieldProver (tr : Transcript m) : ℕ → Polynomial Ext6Q :=
  fun i => readPoly1 (messageAt tr i)

noncomputable def fieldChal (tr : Transcript m) : ℕ → Ext6Q :=
  fun i => readExt6 (challengeAt tr i)

theorem fieldChal_eq (tr : Transcript m) :
    fieldChal tr = chalOf fun i => readExt6 (tr.challenge i) := by
  funext i
  unfold fieldChal challengeAt chalOf
  split <;> simp [read_zero]

theorem messageAt_of_lt (tr : Transcript m) {i : Nat} (hi : i < m) :
    messageAt tr i = tr.message ⟨i, hi⟩ :=
  dif_pos hi

/-- The lane chain reads to `scChain 0`. -/
theorem read_laneChain (tr : Transcript m) (i : Nat) :
    readExt6 (laneChain tr i) = scChain 0 (fieldProver tr) (fieldChal tr) i := by
  cases i with
  | zero => simp [laneChain, scChain, read_zero]
  | succ i =>
    show readExt6 (laneEval (messageAt tr i) (challengeAt tr i)) =
      (readPoly1 (messageAt tr i)).eval (readExt6 (challengeAt tr i))
    rw [readPoly1_eval]

theorem roundsOk_iff (tr : Transcript m) :
    roundsOk tr = true ↔
      ∀ i : Fin m, ext6Add (tr.message i).1 (tr.message i).2 = laneChain tr i := by
  simp [roundsOk, List.all_eq_true, List.mem_finRange]

theorem scChain_congr_lt {base : Ext6Q} {poly poly' : ℕ → Polynomial Ext6Q} {chal : ℕ → Ext6Q}
    (i : ℕ) (h : ∀ j, j < i → poly j = poly' j) :
    scChain base poly chal i = scChain base poly' chal i := by
  cases i with
  | zero => rfl
  | succ n =>
    show (poly n).eval (chal n) = (poly' n).eval (chal n)
    rw [h n (Nat.lt_succ_self n)]

section Sound

variable {Root Op : Type} [DecidableEq Root] {n : Nat}
variable (S : BindingCommitment Root BabyBear (Fin n) Op)
variable (d : ConstraintDescriptor BabyBear) (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L)

/-- **Reflection:** an accepted run is `GateProofAccepts` in the field, with
the transcript's messages as the prover. -/
theorem check_accepts (rt : Root) (op : Opening n) (tr : Transcript m) (rc : Receipt Root m)
    (h : check S.commit d encNat gamma rt op tr = .ok rc) :
    GateProofAccepts S d encNat gamma tr.challenge rt op rc.terminal (fieldProver tr) := by
  obtain ⟨hv, hr, hc, -, -, -⟩ := check_ok_spec S.commit d encNat gamma rt op tr rc h
  refine ⟨hv, ?_, ?_⟩
  · intro i hi
    have hlane := (roundsOk_iff tr).mp hr ⟨i, hi⟩
    have hread := congrArg readExt6 hlane
    rw [read_add, read_laneChain, fieldChal_eq] at hread
    rw [show fieldProver tr i = readPoly1 (messageAt tr i) from rfl, readPoly1_eval_zero,
      readPoly1_eval_one, messageAt_of_lt tr hi]
    exact hread
  · have hread := congrArg readExt6 hc
    rw [read_laneChain, fieldChal_eq] at hread
    exact hread

/-- **The ledger theorem at the controller.**  Accepted against a root
committing `w` ⇒ the trace satisfies the descriptor, or the gamma event, or the
sumcheck event -- for any strategy `P` whose messages at the actual challenges
are the transcript's.  Prices: `gammaZero_prob_le`, `sumcheck_prob_le`. -/
theorem gateProof_sound_lane (w : Fin n → BabyBear) (op : Opening n) (tr : Transcript m)
    (rc : Receipt Root m)
    (h : check S.commit d encNat gamma (S.commit w) op tr = .ok rc)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k)
    (P : (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q)
    (hP : ∀ i, i < m → P (chalOf fun q => readExt6 (tr.challenge q)) i = fieldProver tr i) :
    descriptorHolds d (traceOf w) ∨
      (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b) = 0 ∨
      AdaptiveAcceptsFalse P (mleHonest (gammaResidualTable d (traceOf w) enc (readExt6 gamma)))
        0 (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b)
        (fun q => readExt6 (tr.challenge q)) := by
  apply gateProof_sound S d encNat gamma tr.challenge w op rc.terminal enc hEnc P
  have hacc := check_accepts S d encNat gamma (S.commit w) op tr rc h
  refine ⟨hacc.terminal, ?_, ?_⟩
  · intro i hi
    rw [hP i hi, scChain_congr_lt i (fun j hj => hP j (lt_trans hj hi))]
    exact hacc.rounds i hi
  · rw [scChain_congr_lt m (fun j hj => hP j hj)]
    exact hacc.closes

/-- The transcript as a constant (challenge-oblivious) strategy: trivially
prefix-measurable, degree `≤ 1` by construction -- the hypotheses
`sumcheck_prob_le` consumes, discharged. -/
noncomputable def constantStrategy (tr : Transcript m) : (ℕ → Ext6Q) → ℕ → Polynomial Ext6Q :=
  fun _ => fieldProver tr

theorem constantStrategy_prefixMeasurable (tr : Transcript m) :
    PrefixMeasurable (constantStrategy tr) :=
  fun _ _ _ _ => rfl

theorem constantStrategy_degree (tr : Transcript m) (χ : ℕ → Ext6Q) (i : ℕ) (_ : i < m) :
    (constantStrategy tr χ i).degree < ((1 + 1 : ℕ) : WithBot ℕ) :=
  readPoly1_degree _

end Sound

/-! ## §3. The honest lane prover -/

/-- `∏_{j<k} χ_{b_j}(x_j)` in lanes (the `laneChi` shape, cut at `k`). -/
def lanePrefixChi (b : Fin m → Bool) (x : Fin m → Ext6L) (k : Nat) : Ext6L :=
  laneProd (List.ofFn fun j : Fin m =>
    if j.val < k then (if b j then x j else ext6Sub ext6One (x j)) else ext6One)

noncomputable def prefixChiEval (b : Fin m → Bool) (x : Fin m → Ext6Q) (k : Nat) : Ext6Q :=
  ∏ j : Fin m, if j.val < k then (if b j then x j else 1 - x j) else 1

theorem read_lanePrefixChi (b : Fin m → Bool) (x : Fin m → Ext6L) (k : Nat) :
    readExt6 (lanePrefixChi b x k) = prefixChiEval b (fun i => readExt6 (x i)) k := by
  unfold lanePrefixChi prefixChiEval
  rw [read_laneProd, List.map_ofFn, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j.val < k
  · by_cases hb : b j
    · simp [hj, hb]
    · simp [hj, hb, read_sub, read_one]
  · simp [hj, read_one]

theorem prefixChiEval_full (b : Fin m → Bool) (x : Fin m → Ext6Q) :
    prefixChiEval b x m = chiEval b x := by
  unfold prefixChiEval chiEval
  apply Finset.prod_congr rfl
  intro j _
  rw [if_pos j.isLt]

/-- Pinning coordinate `i` to `t` and extending the prefix by one factor. -/
theorem prefixChiEval_update_succ (b : Fin m → Bool) (x : Fin m → Ext6Q) (i : Fin m) (t : Ext6Q) :
    prefixChiEval b (Function.update x i t) (i.val + 1) =
      prefixChiEval b x i.val * (if b i then t else 1 - t) := by
  unfold prefixChiEval
  rw [← Finset.mul_prod_erase Finset.univ
      (fun j : Fin m => if j.val < i.val + 1 then
        (if b j then Function.update x i t j else 1 - Function.update x i t j) else 1)
      (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ
      (fun j : Fin m => if j.val < i.val then (if b j then x j else 1 - x j) else 1)
      (Finset.mem_univ i)]
  simp only [Function.update_self, Nat.lt_succ_self, if_true, lt_irrefl, if_false, one_mul]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hne : j ≠ i := Finset.ne_of_mem_erase hj
  have hval : j.val ≠ i.val := fun h => hne (Fin.ext h)
  rw [Function.update_of_ne hne]
  by_cases hjk : j.val < i.val
  · rw [if_pos (Nat.lt_succ_of_lt hjk), if_pos hjk]
  · rw [if_neg (by omega), if_neg hjk]

theorem roundSum_eq_residualSum_update (g : (Fin m → Ext6Q) → Ext6Q) (x : Fin m → Ext6Q)
    (i : Fin m) (t : Ext6Q) :
    roundSum g x i t = residualSum g (Function.update x i t) (i.val + 1) := by
  simp only [roundSum, residualSum]

/-- **The residual claim of a sparse MLE is the prefix-chi sum**, at every level:
`Σ_{b ∈ {0,1}^{m−k}} f̂(x_{<k}, b) = Σ_j c_j ∏_{i<k} χ_{e_j,i}(x_i)`.  Downward
induction on the level through `residualSum_eq_roundSum_bool` and
`residualSum_step` (REUSED): each descent pins one coordinate to `0` and `1`,
and the two chi factors sum to `1`. -/
theorem residualSum_sparse {N : Nat} (f : (Fin m → Bool) → Ext6Q) (c : Fin N → Ext6Q)
    (e : Fin N → (Fin m → Bool)) (hf : ∀ x, mle f x = ∑ k, c k * chiEval (e k) x) :
    ∀ (j : Nat), j ≤ m → ∀ x : Fin m → Ext6Q,
      residualSum (mle f) x (m - j) = ∑ k, c k * prefixChiEval (e k) x (m - j) := by
  intro j
  induction j with
  | zero =>
    intro _ x
    rw [Nat.sub_zero, residualSum_full, hf]
    apply Finset.sum_congr rfl
    intro k _
    rw [prefixChiEval_full]
  | succ j ih =>
    intro hj x
    have hk : m - (j + 1) < m := by omega
    have hkj : m - j = m - (j + 1) + 1 := by omega
    rw [residualSum_eq_roundSum_bool hk,
      roundSum_eq_residualSum_update (mle f) x ⟨m - (j + 1), hk⟩ 0,
      roundSum_eq_residualSum_update (mle f) x ⟨m - (j + 1), hk⟩ 1]
    rw [← hkj, ih (by omega), ih (by omega), hkj]
    simp only [prefixChiEval_update_succ _ _ (⟨m - (j + 1), hk⟩ : Fin m)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring

/-- Round `i`'s partial sum of a sparse MLE. -/
theorem roundSum_sparse {N : Nat} (f : (Fin m → Bool) → Ext6Q) (c : Fin N → Ext6Q)
    (e : Fin N → (Fin m → Bool)) (hf : ∀ x, mle f x = ∑ k, c k * chiEval (e k) x)
    (x : Fin m → Ext6Q) (i : Fin m) (t : Ext6Q) :
    roundSum (mle f) x i t =
      ∑ k, c k * (prefixChiEval (e k) x i.val * (if e k i then t else 1 - t)) := by
  rw [roundSum_eq_residualSum_update]
  have h := residualSum_sparse f c e hf (m - (i.val + 1)) (by omega) (Function.update x i t)
  rw [show m - (m - (i.val + 1)) = i.val + 1 by omega] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  rw [prefixChiEval_update_succ]

/-- **The honest round walker.**  For residual `k` at corner `b = encNat k`,
the weight `w = γ^k · res_k · ∏_{j<i} χ_{b_j}(r_j)` goes to `g(0)` when
`b_i = false` and to `g(1)` when `b_i = true`; the prefix chi is computed once
per residual. -/
def roundWalk (gamma : Ext6L) (r : Fin m → Ext6L) (encNat : Nat → (Fin m → Bool)) (i : Fin m) :
    List BabyBear → Nat → Ext6L → RoundMsg → RoundMsg
  | [], _, _, acc => acc
  | c :: rest, k, gpow, acc =>
      let w := ext6MulL (ext6MulL gpow (ext6OfBase c)) (lanePrefixChi (encNat k) r i.val)
      roundWalk gamma r encNat i rest (k + 1) (ext6MulL gpow gamma)
        (if encNat k i then (acc.1, ext6Add acc.2 w) else (ext6Add acc.1 w, acc.2))

/-- The field weight of residual `j` at round `i`, routed by the corner bit. -/
noncomputable def roundWeight (gamma : Ext6L) (r : Fin m → Ext6L) (encNat : Nat → (Fin m → Bool))
    (i : Fin m) (side : Bool) (gpow : Ext6L) (c : BabyBear) (k j : Nat) : Ext6Q :=
  readExt6 gpow * readExt6 gamma ^ j * algebraMap BabyBear Ext6Q c *
    (prefixChiEval (encNat (k + j)) (fun q => readExt6 (r q)) i.val *
      (if encNat (k + j) i = side then 1 else 0))

theorem roundWeight_zero (gamma : Ext6L) (r : Fin m → Ext6L) (encNat : Nat → (Fin m → Bool))
    (i : Fin m) (side : Bool) (gpow : Ext6L) (c : BabyBear) (k : Nat) :
    roundWeight gamma r encNat i side gpow c k 0 =
      readExt6 gpow * algebraMap BabyBear Ext6Q c *
        (prefixChiEval (encNat k) (fun q => readExt6 (r q)) i.val *
          (if encNat k i = side then 1 else 0)) := by
  simp [roundWeight]

theorem read_roundWalk (gamma : Ext6L) (r : Fin m → Ext6L) (encNat : Nat → (Fin m → Bool))
    (i : Fin m) (l : List BabyBear) :
    ∀ (k : Nat) (gpow : Ext6L) (acc : RoundMsg),
      readExt6 (roundWalk gamma r encNat i l k gpow acc).1 =
        readExt6 acc.1 + ∑ j ∈ Finset.range l.length,
          roundWeight gamma r encNat i false gpow (l.getD j 0) k j ∧
      readExt6 (roundWalk gamma r encNat i l k gpow acc).2 =
        readExt6 acc.2 + ∑ j ∈ Finset.range l.length,
          roundWeight gamma r encNat i true gpow (l.getD j 0) k j := by
  induction l with
  | nil =>
    intro k gpow acc
    simp [roundWalk]
  | cons c rest ih =>
    intro k gpow acc
    have hshift : ∀ (side : Bool), ∀ j ∈ Finset.range rest.length,
        roundWeight gamma r encNat i side (ext6MulL gpow gamma) (rest.getD j 0) (k + 1) j =
          roundWeight gamma r encNat i side gpow (rest.getD j 0) k (j + 1) := by
      intro side j _
      unfold roundWeight
      rw [read_mul, show k + 1 + j = k + (j + 1) by omega, pow_succ]
      ring
    have hw : readExt6 (ext6MulL (ext6MulL gpow (ext6OfBase c)) (lanePrefixChi (encNat k) r i.val)) =
        readExt6 gpow * algebraMap BabyBear Ext6Q c *
          prefixChiEval (encNat k) (fun q => readExt6 (r q)) i.val := by
      rw [read_mul, read_mul, read_ofBase, read_lanePrefixChi]
    simp only [roundWalk, List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ]
    by_cases hb : encNat k i = true
    · rw [if_pos hb]
      obtain ⟨ih1, ih2⟩ := ih (k + 1) (ext6MulL gpow gamma) (acc.1, ext6Add acc.2 _)
      refine ⟨?_, ?_⟩
      · rw [ih1, Finset.sum_congr rfl (hshift false), roundWeight_zero, hb]
        simp only [Bool.true_eq_false, if_false, mul_zero, add_zero]
      · rw [ih2, Finset.sum_congr rfl (hshift true), roundWeight_zero, hb, if_pos rfl]
        dsimp only
        rw [read_add, hw]
        ring
    · have hb' : encNat k i = false := Bool.eq_false_iff.mpr hb
      rw [if_neg hb]
      obtain ⟨ih1, ih2⟩ := ih (k + 1) (ext6MulL gpow gamma) (ext6Add acc.1 _, acc.2)
      refine ⟨?_, ?_⟩
      · rw [ih1, Finset.sum_congr rfl (hshift false), roundWeight_zero, hb', if_pos rfl]
        dsimp only
        rw [read_add, hw]
        ring
      · rw [ih2, Finset.sum_congr rfl (hshift true), roundWeight_zero, hb']
        simp only [Bool.false_eq_true, if_false, mul_zero, add_zero]

/-- **Round `i`'s honest lane message**: one walk over the residual list. -/
def laneRound (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L)
    (r : Fin m → Ext6L) (encNat : Nat → (Fin m → Bool)) (i : Fin m) : RoundMsg :=
  roundWalk gamma r encNat i (descriptorResiduals d wv) 0 ext6One (ext6Zero, ext6Zero)

/-- **The honest transcript** at challenges `r`. -/
def honestTranscript (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear) (gamma : Ext6L)
    (r : Fin m → Ext6L) (encNat : Nat → (Fin m → Bool)) : Transcript m :=
  ⟨fun i => laneRound d wv gamma r encNat i, r⟩

/-- The lane message reads to the MLE round partial sums at `0` and `1`. -/
theorem read_laneRound (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) (i : Fin m) :
    readExt6 (laneRound d wv gamma r encNat i).1 =
        roundSum (mle (gammaResidualTable d wv enc (readExt6 gamma)))
          (fun q => readExt6 (r q)) i 0 ∧
      readExt6 (laneRound d wv gamma r encNat i).2 =
        roundSum (mle (gammaResidualTable d wv enc (readExt6 gamma)))
          (fun q => readExt6 (r q)) i 1 := by
  obtain ⟨h0, h1⟩ := read_roundWalk gamma r encNat i (descriptorResiduals d wv) 0 ext6One
    (ext6Zero, ext6Zero)
  have hsparse := roundSum_sparse (gammaResidualTable d wv enc (readExt6 gamma))
    (fun k => readExt6 gamma ^ (k : Nat) *
      algebraMap BabyBear Ext6Q ((descriptorResiduals d wv).get k))
    (fun k => enc k) (mle_gammaResidualTable_sparse d wv enc (readExt6 gamma))
    (fun q => readExt6 (r q)) i
  constructor
  · rw [laneRound, h0, read_zero, zero_add, hsparse 0, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    unfold roundWeight
    rw [read_one, one_mul, Nat.zero_add, hEnc, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem k.isLt, Option.getD_some, List.get_eq_getElem]
    by_cases hb : encNat k i = true <;> simp [hb]
  · rw [laneRound, h1, read_zero, zero_add, hsparse 1, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    unfold roundWeight
    rw [read_one, one_mul, Nat.zero_add, hEnc, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem k.isLt, Option.getD_some, List.get_eq_getElem]
    by_cases hb : encNat k i = true <;> simp [hb]

/-- **The lane message IS `mleHonest`'s round polynomial.** -/
theorem readPoly1_laneRound (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) (i : Fin m) :
    readPoly1 (laneRound d wv gamma r encNat i) =
      mleHonest (gammaResidualTable d wv enc (readExt6 gamma))
        (chalOf fun q => readExt6 (r q)) i.val := by
  obtain ⟨h0, h1⟩ := read_laneRound d wv enc encNat hEnc gamma r i
  rw [mleHonest, dif_pos i.isLt, chalOf_restrict, roundPoly, readPoly1, h0, h1]

/-- The honest transcript's field prover is exactly `mleHonest`, as functions. -/
theorem fieldProver_honest (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (enc : Fin (descriptorResiduals d wv).length ↪ (Fin m → Bool))
    (encNat : Nat → (Fin m → Bool)) (hEnc : ∀ k, enc k = encNat k)
    (gamma : Ext6L) (r : Fin m → Ext6L) :
    fieldProver (honestTranscript d wv gamma r encNat) =
      mleHonest (gammaResidualTable d wv enc (readExt6 gamma)) (chalOf fun q => readExt6 (r q)) := by
  funext i
  unfold fieldProver messageAt
  by_cases hi : i < m
  · rw [dif_pos hi]
    exact readPoly1_laneRound d wv enc encNat hEnc gamma r ⟨i, hi⟩
  · rw [dif_neg hi, mleHonest, dif_neg hi]
    simp [readPoly1, read_zero]

/-! ## §4. Completeness and the general refusals -/

section Complete

variable {Root : Type} [DecidableEq Root] {n : Nat}
variable (commit : (Fin n → BabyBear) → Root) (d : ConstraintDescriptor BabyBear)
variable (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L) (r : Fin m → Ext6L)

/-- **Completeness.**  The honest opening of a SATISFYING word, with the honest
lane transcript at any challenges, is accepted -- `mleHonest_boolean_sum` and
`scChain_mleHonest_final` (REUSED) at the zero claim, carried to lanes by
`readExt6_injective`. -/
theorem receipt_complete (w : Fin n → BabyBear)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) (hd : descriptorHolds d (traceOf w)) :
    check commit d encNat gamma (commit w)
        ⟨w, laneTerminal gamma r encNat (descriptorResiduals d (traceOf w))⟩
        (honestTranscript d (traceOf w) gamma r encNat) =
      .ok ⟨commit w, gamma, honestTranscript d (traceOf w) gamma r encNat,
        laneTerminal gamma r encNat (descriptorResiduals d (traceOf w))⟩ := by
  have hzero : (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b) = 0 :=
    gammaResidual_zeroClaim d (traceOf w) enc (readExt6 gamma) hd
  have hprover := fieldProver_honest d (traceOf w) enc encNat hEnc gamma r
  have hchal : fieldChal (honestTranscript d (traceOf w) gamma r encNat) =
      chalOf fun q => readExt6 (r q) := fieldChal_eq _
  have hrounds : roundsOk (honestTranscript d (traceOf w) gamma r encNat) = true := by
    rw [roundsOk_iff]
    intro i
    apply lane_eq_of_read
    rw [read_add, read_laneChain, hprover, hchal]
    have hb := mleHonest_boolean_sum (gammaResidualTable d (traceOf w) enc (readExt6 gamma))
      (fun q => readExt6 (r q)) i.val i.isLt
    rw [hzero] at hb
    rw [← hb, ← readPoly1_laneRound d (traceOf w) enc encNat hEnc gamma r i,
      readPoly1_eval_zero, readPoly1_eval_one]
    rfl
  have hclose : laneChain (honestTranscript d (traceOf w) gamma r encNat) m =
      laneTerminal gamma r encNat (descriptorResiduals d (traceOf w)) := by
    apply lane_eq_of_read
    rw [read_laneChain, hprover, hchal, read_laneTerminal d (traceOf w) enc encNat hEnc gamma r]
    have hfinal := scChain_mleHonest_final (gammaResidualTable d (traceOf w) enc (readExt6 gamma))
      (fun q => readExt6 (r q))
    rw [hzero] at hfinal
    exact hfinal
  exact check_ok_of commit d encNat gamma (commit w) _ _ _
    (realize_complete commit d encNat gamma r w) hrounds hclose

/-- **The honest prover of a failing trace is refused at round `0`** whenever
its batched residual is nonzero (all but `≤ N−1` gammas, `card_gammaZero_le`):
the zero claim is false and the first Boolean check says so.  The gamma leg,
closed for the honest prover. -/
theorem receipt_refuses_false_claim (w : Fin n → BabyBear)
    (enc : Fin (descriptorResiduals d (traceOf w)).length ↪ (Fin m → Bool))
    (hEnc : ∀ k, enc k = encNat k) (hm : 0 < m)
    (hz : (∑ b, gammaResidualTable d (traceOf w) enc (readExt6 gamma) b) ≠ 0) :
    check commit d encNat gamma (commit w)
        ⟨w, laneTerminal gamma r encNat (descriptorResiduals d (traceOf w))⟩
        (honestTranscript d (traceOf w) gamma r encNat) = .error .roundCheck := by
  apply check_refuses_round commit d encNat gamma (commit w) _ _ _
    (realize_complete commit d encNat gamma r w)
  apply Bool.eq_false_iff.mpr
  intro hok
  have hlane := (roundsOk_iff _).mp hok ⟨0, hm⟩
  have hread := congrArg readExt6 hlane
  rw [read_add, read_laneChain, fieldProver_honest d (traceOf w) enc encNat hEnc gamma r,
    fieldChal_eq, ← readPoly1_eval_zero, ← readPoly1_eval_one,
    show (honestTranscript d (traceOf w) gamma r encNat).message ⟨0, hm⟩ =
      laneRound d (traceOf w) gamma r encNat ⟨0, hm⟩ from rfl,
    readPoly1_laneRound d (traceOf w) enc encNat hEnc gamma r ⟨0, hm⟩,
    mleHonest_boolean_sum (gammaResidualTable d (traceOf w) enc (readExt6 gamma))
      (fun q => readExt6 (r q)) 0 hm] at hread
  exact hz hread

end Complete

section Refuse

variable {Root Op : Type} [DecidableEq Root] {n : Nat}
variable (S : BindingCommitment Root BabyBear (Fin n) Op)
variable (d : ConstraintDescriptor BabyBear) (encNat : Nat → (Fin m → Bool)) (gamma : Ext6L)

/-- **Refusal through binding:** under a root committing `w`, any other word
is refused at the root before any round is read. -/
theorem receipt_refuses_tamper (w : Fin n → BabyBear) (op : Opening n) (tr : Transcript m)
    (hne : op.word ≠ w) :
    check S.commit d encNat gamma (S.commit w) op tr = .error (.terminal .rootMismatch) :=
  check_refuses_terminal S.commit d encNat gamma (S.commit w) op tr .rootMismatch
    (realize_other_word_refused S d encNat gamma tr.challenge w op hne)

end Refuse

/-! ## §5. ATLAS fields on the emitted demo descriptor, decided -/

namespace DemoInstance

open CommittedTerminalRealizer.DemoInstance

/-- The honest transcript of the demo trace: five rounds, computed by the kernel. -/
def honestTr : Transcript 5 := honestTranscript demoDescriptor (traceOf demoWord) gamma r (bitCorner 5)

/-- The all-zero transcript: a satisfying trace's honest messages are all
`(0, 0)` (its table is zero), so this is what `honestTr` computes to. -/
def zeroTr : Transcript 5 := ⟨fun _ => (ext6Zero, ext6Zero), r⟩

set_option maxHeartbeats 1000000 in
/-- **The honest messages, computed by the kernel:** all five are `(0, 0)` --
a satisfying trace's table is zero, so every round partial sum is zero. -/
theorem honestTr_eq_zeroTr : honestTr = zeroTr := by
  decide +kernel

/-- **Satisfiable, decided:** the honest five-round proof of the satisfying
trace is accepted. -/
theorem receipt_complete_demo :
    check S.commit demoDescriptor (bitCorner 5) gamma (S.commit demoWord) honest honestTr =
      .ok ⟨demoWord, gamma, zeroTr, ext6Zero⟩ := by
  rw [honestTr_eq_zeroTr]
  decide +kernel

/-- **Teeth, decided:** the tampered word under the honest root is refused at
the root. -/
theorem receipt_refuses_tamper_demo :
    check S.commit demoDescriptor (bitCorner 5) gamma (S.commit demoWord)
        ⟨tamperedWord, ext6Zero⟩ honestTr = .error (.terminal .rootMismatch) := by
  decide +kernel

/-- The tampered trace's terminal, pinned (`demo_tampered_terminal` says
nonzero; this is the value). -/
def tamperedTerminal : Ext6L :=
  ⟨1612364632, 676004279, 1984653847, 1968643124, 911508879, 94536224⟩

/-- **Teeth, decided (the gamma leg):** the tampered word at its OWN root with
its OWN honest prover is refused at a round check -- its zero claim is false
at this gamma (`laneZeroClaim_tampered_ne_zero`). -/
theorem receipt_refuses_false_claim_demo :
    check S.commit demoDescriptor (bitCorner 5) gamma (S.commit tamperedWord)
        ⟨tamperedWord, tamperedTerminal⟩
        (honestTranscript demoDescriptor (traceOf tamperedWord) gamma r (bitCorner 5)) =
      .error .roundCheck := by
  decide +kernel

/-- **Teeth, decided:** the tampered word at its own root, claiming its true
terminal, with the ZERO transcript: every round check passes on the zero
chain, and the chain closes at `0 ≠ tamperedTerminal`. -/
theorem receipt_refuses_forged_terminal_demo :
    check S.commit demoDescriptor (bitCorner 5) gamma (S.commit tamperedWord)
        ⟨tamperedWord, tamperedTerminal⟩ zeroTr = .error .terminalMismatch := by
  decide +kernel

/-- **Teeth, decided:** one honest message replaced by `(1, 0)` is refused at
its round check. -/
theorem receipt_refuses_tampered_message_demo :
    check S.commit demoDescriptor (bitCorner 5) gamma (S.commit demoWord) honest
        ⟨Function.update zeroTr.message 2 (ext6One, ext6Zero), r⟩ = .error .roundCheck := by
  decide +kernel

end DemoInstance

/-! ## §6. Stage 0: the 4,131-wire proof end to end (compiled exhibit) -/

namespace Stage0Exhibit

open CommittedTerminalRealizer.Stage0Exhibit
open Minidregg.Compiler.DescriptorEval Minidregg.Compiler.EvmAddAir

def exhibit : IO Unit := do
  let honest := wordOf (evmAddCandidate 1 2)
  let tr := honestTranscript evmAddDescriptor (traceOf honest) gamma r (bitCorner 13)
  match check S.commit evmAddDescriptor (bitCorner 13) gamma (S.commit honest)
      ⟨honest, ext6Zero⟩ tr with
  | .ok rc =>
      if rc.terminal = ext6Zero then
        IO.println "stage0 controller: honest (1, 2) proof accepted end to end: 13 rounds, terminal 0"
      else throw (IO.userError "stage0 controller: honest receipt has a nonzero terminal")
  | .error e => throw (IO.userError s!"stage0 controller: honest proof refused: {repr e}")
  let forged := wordOf (evmAddClaimed 1 2 4)
  match check S.commit evmAddDescriptor (bitCorner 13) gamma (S.commit honest)
      ⟨forged, ext6Zero⟩ tr with
  | .error (.terminal .rootMismatch) =>
      IO.println "stage0 controller: forged word refused at the honest root"
  | _ => throw (IO.userError "stage0 controller: forged word not refused at the root")
  let vF := laneTerminal gamma r (bitCorner 13) (descriptorResiduals evmAddDescriptor (traceOf forged))
  let trF := honestTranscript evmAddDescriptor (traceOf forged) gamma r (bitCorner 13)
  match check S.commit evmAddDescriptor (bitCorner 13) gamma (S.commit forged)
      ⟨forged, vF⟩ trF with
  | .error .roundCheck =>
      IO.println "stage0 controller: forged word at its own root, its own honest prover refused at a round check (zero claim false)"
  | _ => throw (IO.userError "stage0 controller: forged self-proof not refused at a round")
  match check S.commit evmAddDescriptor (bitCorner 13) gamma (S.commit forged)
      ⟨forged, vF⟩ tr with
  | .error .terminalMismatch =>
      IO.println "stage0 controller: forged word with the honest transcript refused at the terminal"
  | _ => throw (IO.userError "stage0 controller: forged word with honest transcript not refused at the terminal")

#eval exhibit

end Stage0Exhibit

#check @check
#check @check_accepts
#check @gateProof_sound_lane
#check @residualSum_sparse
#check @readPoly1_laneRound
#check @receipt_complete
#check @receipt_refuses_tamper
#check @receipt_refuses_false_claim

/-- info: 'Minidregg.Compiler.CommittedTerminalController.check_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms check_accepts
/-- info: 'Minidregg.Compiler.CommittedTerminalController.gateProof_sound_lane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gateProof_sound_lane
/-- info: 'Minidregg.Compiler.CommittedTerminalController.residualSum_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms residualSum_sparse
/-- info: 'Minidregg.Compiler.CommittedTerminalController.readPoly1_laneRound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readPoly1_laneRound
/-- info: 'Minidregg.Compiler.CommittedTerminalController.receipt_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms receipt_complete
/-- info: 'Minidregg.Compiler.CommittedTerminalController.receipt_refuses_tamper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms receipt_refuses_tamper
/-- info: 'Minidregg.Compiler.CommittedTerminalController.receipt_refuses_false_claim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms receipt_refuses_false_claim
/-- info: 'Minidregg.Compiler.CommittedTerminalController.DemoInstance.honestTr_eq_zeroTr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.honestTr_eq_zeroTr
/-- info: 'Minidregg.Compiler.CommittedTerminalController.DemoInstance.receipt_complete_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.receipt_complete_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalController.DemoInstance.receipt_refuses_tamper_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.receipt_refuses_tamper_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalController.DemoInstance.receipt_refuses_false_claim_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.receipt_refuses_false_claim_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalController.DemoInstance.receipt_refuses_forged_terminal_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.receipt_refuses_forged_terminal_demo
/-- info: 'Minidregg.Compiler.CommittedTerminalController.DemoInstance.receipt_refuses_tampered_message_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DemoInstance.receipt_refuses_tampered_message_demo

end Minidregg.Compiler.CommittedTerminalController
