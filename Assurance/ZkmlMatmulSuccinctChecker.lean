/-
# Assurance.ZkmlMatmulSuccinctChecker — one succinct, runnable contraction checker

`Assurance.ZkmlMatmulChecker` decides a 2×2 F7 contraction by recomputing it.
This file is the succinct successor at the contraction layer: the checker never
reads a table.  It reads

* an exact **statement** — the registered suite identity, the three committed
  roots `rootA`, `rootB`, `rootC`, the outer point `(x, y)` and the claimed
  product evaluation `Ĉ(x, y) = value`;
* a **transcript** — `κ` degree-≤3 round messages as coefficient quadruples,
  the `κ` sumcheck challenges `r`, and the three opening claims
  `(root, point, value)` of `Selvage.MultilinearCommitment.MleEvalClaim`;

and it decides, with every failure route named in `Failure`:

1. the suite is a member of `ZkmlMatmulSuiteRegistry.auditRegistry`;
2. the three claims sit at the statement roots, at the derived points
   `(x, y)`, `(x, r)`, `(r, y)`, and the output claim carries `value`;
3. the contraction sumcheck replays: every round's Boolean sum equals the
   running claim, and the terminal claim equals `Â(x, r) · B̂(r, y)` read off
   the two operand openings.

`Checked` is the proof-bearing acceptance record; `check` computes it or a
`Failure`; `accepts_sound` / `accepts_of_checked` show `check` decides
exactly `Checked`.

## What is bound, what is named

* **Bound, proved.** `checked_sumcheckAccepts` — an accepted transcript whose
  three claims are true (`OpeningsHold`) is an accepted run of the landed
  contraction protocol `SumcheckAccepts` against the built honest family
  `matmulHonest`, on the claimed `mle₂ C x y`.  `strategy_sound` prices a
  wrong output table at `(μ+ν)/|F| + κ·3/|F|` (`matmul_sumcheck_soundness`),
  with the PCS truth as a named premise.  `strategy_sound_budget` makes that
  premise a visible term instead: `Pr[accept] ≤ contraction bound +
  Pr[accept ∧ some opening claim is false]`.  `fullWord_sound` composes the
  tree's full-word BaseFold IOR verifier `BaseFoldIorAccepts` for each of the
  three openings and lands the **complete budget**
  `matmulSuccinctSoundnessBudget = (μ+ν)/|F| + κ·3/|F| +
  matmulBaseFoldIorAlgebraicBudget`, the existing opening ledger, unchanged.
* **Named, not discharged.**  `[MATMUL-pcs]`: `BaseFoldIorAccepts` is the
  full-word resolution — the verifier reads whole words; sampled Merkle
  queries, their BCS compilation and `[COMMIT-CR]` are the same obligations
  `Selvage.BaseFoldCommittedIor` / `BaseFoldRawCommittedIor` retain.
  `[MATMUL-fs]`: every challenge here is a uniform draw; Fiat–Shamir is open.
  No sparse-oracle obligation arises — that is Spartan's, not the
  contraction's.  Native output stays neutral: nothing outside Lean produces
  an acceptance bit, and this checker consumes no bytes yet; the byte binding
  is the next row.

## Instance actually decided

Over `ZMod 7` with `μ = κ = ν = 1` (`eA = [[1,2],[3,4]]`, `eB = [[5,6],[0,1]]`,
`x = 3`, `y = 5`, `r = 4`), against the identity commitment whose roots are
the literal BaseFold words: the honest transcript is accepted by `decide`, and
the literal statement/transcript are proved to BE the honest ones
(`instance_statement_honest`, `instance_transcript_honest`).  Eight refusal
teeth pin a distinct `Failure` each.  The toy field makes the complete budget
`23/7 > 1` (`budget_f7`) — this is the runnable shape, not a secure
parameterization.
-/
import Assurance.ZkmlMatmulBaseFold
import Assurance.ZkmlMatmulSuiteRegistry

namespace Minidregg.Assurance.ZkmlMatmulSuccinctChecker

open Minidregg.Selvage
open Minidregg.Assurance.ZkmlMatmulSuiteRegistry
open Polynomial

set_option autoImplicit false

/-! ## §1. Statement, round messages, transcript, failure routes -/

/-- The exact statement the checker decides.  The roots are opaque data with
decidable equality; the checker never opens them. -/
structure Statement (Root F : Type) (μ κ ν : ℕ) where
  suite : AuditIdentity
  rootA : Root
  rootB : Root
  rootC : Root
  x : Fin μ → F
  y : Fin ν → F
  value : F

/-- One round message: the four coefficients of a degree-≤3 polynomial.
Coefficient form, so the replay needs no division and no characteristic
hypothesis — the same choice `cubicRoundPoly` makes. -/
structure RoundMessage (F : Type) where
  c0 : F
  c1 : F
  c2 : F
  c3 : F
  deriving DecidableEq

/-- The transcript: round messages (total in the round index, junk past `κ`
exactly as `scChain`'s families are), the challenges, and the three opening
claims. -/
structure Transcript (Root F : Type) (μ κ ν : ℕ) where
  rounds : ℕ → RoundMessage F
  challenges : Fin κ → F
  claims : MatmulMleClaims Root Root Root F μ κ ν

/-- Every route by which the checker refuses. -/
inductive Failure where
  | unregisteredSuite
  | outputRootMismatch
  | leftRootMismatch
  | rightRootMismatch
  | outputPointMismatch
  | leftPointMismatch
  | rightPointMismatch
  | outputValueMismatch
  | roundSumMismatch (round : ℕ)
  | terminalMismatch
  deriving DecidableEq, Repr

/-! ## §2. The replay: messages, chains, and their polynomial meaning -/

section Replay

variable {F : Type} [Field F] [DecidableEq F]

/-- Horner evaluation of a message. -/
def RoundMessage.eval (g : RoundMessage F) (t : F) : F :=
  g.c0 + t * (g.c1 + t * (g.c2 + t * g.c3))

/-- The Boolean sum `g(0) + g(1)` the verifier compares with its running claim. -/
def RoundMessage.boolSum (g : RoundMessage F) : F :=
  g.eval 0 + g.eval 1

/-- Embed finitely many messages as a total family (zero message past `κ`). -/
def messagesOf {κ : ℕ} (rounds : Fin κ → RoundMessage F) (i : ℕ) : RoundMessage F :=
  if h : i < κ then rounds ⟨i, h⟩ else ⟨0, 0, 0, 0⟩

/-- The verifier's running claim: `scChain` with messages for polynomials. -/
def chain (H : F) (msgs : ℕ → RoundMessage F) (chal : ℕ → F) : ℕ → F
  | 0 => H
  | i + 1 => (msgs i).eval (chal i)

/-- The first round below `n` whose Boolean sum misses the running claim. -/
def firstBadRound (H : F) (msgs : ℕ → RoundMessage F) (chal : ℕ → F) : ℕ → Option ℕ
  | 0 => none
  | n + 1 =>
      match firstBadRound H msgs chal n with
      | some i => some i
      | none => if (msgs n).boolSum = chain H msgs chal n then none else some n

theorem firstBadRound_eq_none_iff (H : F) (msgs : ℕ → RoundMessage F) (chal : ℕ → F) :
    ∀ n, firstBadRound H msgs chal n = none ↔
      ∀ i, i < n → (msgs i).boolSum = chain H msgs chal i := by
  intro n
  induction n with
  | zero => simp [firstBadRound]
  | succ n ih =>
    constructor
    · intro h i hi
      simp only [firstBadRound] at h
      cases hprev : firstBadRound H msgs chal n with
      | some j =>
        rw [hprev] at h
        simp at h
      | none =>
        rw [hprev] at h
        by_cases hn : (msgs n).boolSum = chain H msgs chal n
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
          · exact (ih.mp hprev) i hlt
          · exact hn
        · simp [hn] at h
    · intro h
      have hprev : firstBadRound H msgs chal n = none :=
        ih.mpr fun i hi => h i (Nat.lt_succ_of_lt hi)
      simp only [firstBadRound, hprev]
      rw [if_pos (h n (Nat.lt_succ_self n))]

/-- The polynomial a message denotes. -/
noncomputable def RoundMessage.poly (g : RoundMessage F) : Polynomial F :=
  C g.c0 + C g.c1 * X + C g.c2 * X ^ 2 + C g.c3 * X ^ 3

omit [DecidableEq F] in
theorem RoundMessage.poly_eval (g : RoundMessage F) (t : F) :
    g.poly.eval t = g.eval t := by
  simp only [RoundMessage.poly, RoundMessage.eval, eval_add, eval_mul, eval_C, eval_X,
    eval_pow]
  ring

omit [DecidableEq F] in
theorem RoundMessage.poly_degree (g : RoundMessage F) :
    g.poly.degree < ((3 + 1 : ℕ) : WithBot ℕ) := by
  have h : g.poly = C g.c3 * X ^ 3 + C g.c2 * X ^ 2 + C g.c1 * X + C g.c0 := by
    simp only [RoundMessage.poly]
    ring
  rw [h]
  exact lt_of_le_of_lt Polynomial.degree_cubic_le (by decide)

/-- The message of a degree-≤3 polynomial: its first four coefficients. -/
noncomputable def messageOf (p : Polynomial F) : RoundMessage F :=
  ⟨p.coeff 0, p.coeff 1, p.coeff 2, p.coeff 3⟩

omit [DecidableEq F] in
theorem messageOf_eval {p : Polynomial F}
    (hp : p.degree < ((3 + 1 : ℕ) : WithBot ℕ)) (t : F) :
    (messageOf p).eval t = p.eval t := by
  have hnat : p.natDegree < 4 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by simpa using hp)
  rw [Polynomial.eval_eq_sum_range' hnat]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, messageOf, RoundMessage.eval]
  ring

omit [DecidableEq F] in
/-- The message chain IS `scChain` on the denoted polynomials. -/
theorem chain_eq_scChain (H : F) (msgs : ℕ → RoundMessage F) (chal : ℕ → F) (i : ℕ) :
    chain H msgs chal i = scChain H (fun j => (msgs j).poly) chal i := by
  cases i with
  | zero => rfl
  | succ i =>
    show (msgs i).eval (chal i) = ((msgs i).poly).eval (chal i)
    rw [RoundMessage.poly_eval]

omit [DecidableEq F] in
/-- Below the horizon, a message chain agrees with `scChain` on any polynomial
family the messages evaluate like. -/
theorem chain_congr_scChain (H : F) (msgs : ℕ → RoundMessage F) (P : ℕ → Polynomial F)
    (chal : ℕ → F) {n : ℕ}
    (h : ∀ j, j < n → ∀ t, (msgs j).eval t = (P j).eval t) :
    ∀ i, i ≤ n → chain H msgs chal i = scChain H P chal i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    show (msgs i).eval (chal i) = (P i).eval (chal i)
    exact h i hi (chal i)

end Replay

/-! ## §3. The checker -/

section Check

variable {Root F : Type} [Field F] [DecidableEq F] [DecidableEq Root] {μ κ ν : ℕ}

/-- The proof-bearing acceptance record: exactly the checks the verifier ran. -/
structure Checked (stmt : Statement Root F μ κ ν) (tr : Transcript Root F μ κ ν) : Prop where
  registered : stmt.suite ∈ auditRegistry
  outputRoot : tr.claims.output.rt = stmt.rootC
  leftRoot : tr.claims.left.rt = stmt.rootA
  rightRoot : tr.claims.right.rt = stmt.rootB
  outputPoint : tr.claims.output.pt = Fin.append stmt.x stmt.y
  leftPoint : tr.claims.left.pt = Fin.append stmt.x tr.challenges
  rightPoint : tr.claims.right.pt = Fin.append tr.challenges stmt.y
  outputValue : tr.claims.output.val = stmt.value
  rounds : ∀ i, i < κ →
    (tr.rounds i).boolSum = chain stmt.value tr.rounds (chalOf tr.challenges) i
  terminal : chain stmt.value tr.rounds (chalOf tr.challenges) κ =
    tr.claims.left.val * tr.claims.right.val

/-- Decide the statement against the transcript.  Every refusal is a named
`Failure`; only the positive branch constructs `Checked`. -/
def check (stmt : Statement Root F μ κ ν) (tr : Transcript Root F μ κ ν) :
    Except Failure (PLift (Checked stmt tr)) := by
  if hreg : stmt.suite ∈ auditRegistry then
    if hrC : tr.claims.output.rt = stmt.rootC then
      if hrA : tr.claims.left.rt = stmt.rootA then
        if hrB : tr.claims.right.rt = stmt.rootB then
          if hpC : tr.claims.output.pt = Fin.append stmt.x stmt.y then
            if hpA : tr.claims.left.pt = Fin.append stmt.x tr.challenges then
              if hpB : tr.claims.right.pt = Fin.append tr.challenges stmt.y then
                if hval : tr.claims.output.val = stmt.value then
                  if hbad : firstBadRound stmt.value tr.rounds (chalOf tr.challenges) κ
                      = none then
                    if hterm : chain stmt.value tr.rounds (chalOf tr.challenges) κ =
                        tr.claims.left.val * tr.claims.right.val then
                      exact .ok ⟨{ registered := hreg
                                   outputRoot := hrC
                                   leftRoot := hrA
                                   rightRoot := hrB
                                   outputPoint := hpC
                                   leftPoint := hpA
                                   rightPoint := hpB
                                   outputValue := hval
                                   rounds := (firstBadRound_eq_none_iff _ _ _ κ).mp hbad
                                   terminal := hterm }⟩
                    else exact .error .terminalMismatch
                  else exact .error (.roundSumMismatch
                    ((firstBadRound stmt.value tr.rounds (chalOf tr.challenges) κ).getD 0))
                else exact .error .outputValueMismatch
              else exact .error .rightPointMismatch
            else exact .error .leftPointMismatch
          else exact .error .outputPointMismatch
        else exact .error .rightRootMismatch
      else exact .error .leftRootMismatch
    else exact .error .outputRootMismatch
  else exact .error .unregisteredSuite

def accepts (stmt : Statement Root F μ κ ν) (tr : Transcript Root F μ κ ν) : Bool :=
  match check stmt tr with
  | .ok _ => true
  | .error _ => false

/-- The refusal route, if any. -/
def failure (stmt : Statement Root F μ κ ν) (tr : Transcript Root F μ κ ν) : Option Failure :=
  match check stmt tr with
  | .ok _ => none
  | .error e => some e

theorem accepts_sound {stmt : Statement Root F μ κ ν} {tr : Transcript Root F μ κ ν}
    (h : accepts stmt tr = true) : Checked stmt tr := by
  unfold accepts at h
  cases hcheck : check stmt tr with
  | error e => simp [hcheck] at h
  | ok checked => exact checked.down

theorem accepts_of_checked {stmt : Statement Root F μ κ ν} {tr : Transcript Root F μ κ ν}
    (h : Checked stmt tr) : accepts stmt tr = true := by
  unfold accepts check
  simp only [dif_pos h.registered, dif_pos h.outputRoot, dif_pos h.leftRoot,
    dif_pos h.rightRoot, dif_pos h.outputPoint, dif_pos h.leftPoint, dif_pos h.rightPoint,
    dif_pos h.outputValue, dif_pos ((firstBadRound_eq_none_iff _ _ _ κ).mpr h.rounds),
    dif_pos h.terminal]

theorem accepts_iff {stmt : Statement Root F μ κ ν} {tr : Transcript Root F μ κ ν} :
    accepts stmt tr = true ↔ Checked stmt tr :=
  ⟨accepts_sound, accepts_of_checked⟩

end Check

/-! ## §4. Binding: acceptance + true openings = the landed contraction protocol -/

section Bind

variable {F : Type} [Field F] [DecidableEq F] {Root : Type} [DecidableEq Root]
variable {ιA ιB ιC OpA OpB OpC : Type*}
variable {μ κ ν : ℕ}

/-- **The named PCS premise.**  All three opening claims are true at their
roots, in the tree's claim vocabulary. -/
def OpeningsHold (SA : BindingCommitment Root F ιA OpA) (SB : BindingCommitment Root F ιB OpB)
    (SC : BindingCommitment Root F ιC OpC) (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (claims : MatmulMleClaims Root Root Root F μ κ ν) : Prop :=
  claims.output.Holds SC domC ∧ claims.left.Holds SA domA ∧ claims.right.Holds SB domB

/-- The statement whose roots are the honest commitments of `A`, `B`, `C`. -/
noncomputable def honestStatement (SA : BindingCommitment Root F ιA OpA)
    (SB : BindingCommitment Root F ιB OpB) (SC : BindingCommitment Root F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F) (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (C : (Fin μ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) (value : F) :
    Statement Root F μ κ ν :=
  ⟨auditIdentity, SA.commit (basefoldWord domA (flatten₂ A)),
    SB.commit (basefoldWord domB (flatten₂ B)), SC.commit (basefoldWord domC (flatten₂ C)),
    x, y, value⟩

/-- The polynomial family a transcript's messages denote. -/
noncomputable def Transcript.prover (tr : Transcript Root F μ κ ν) : ℕ → Polynomial F :=
  fun i => (tr.rounds i).poly

omit [DecidableEq F] in
/-- The terminal of the honest contraction chain, factored into the two
operand openings — `scChain_cubicHonest_final` at the contraction instance. -/
theorem scChain_matmulHonest_final (A : (Fin μ → Bool) → (Fin κ → Bool) → F)
    (B : (Fin κ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F)
    (r : Fin κ → F) :
    scChain (matmulTrue A B x y) (matmulHonest A B x y (chalOf r)) (chalOf r) κ =
      mle (rowPartial A x) r * mle (colPartial B y) r := by
  unfold matmulTrue matmulHonest
  rw [scChain_cubicHonest_final, mle_const, mle_const]
  ring

variable [Fintype ιA] [Fintype ιB] [Fintype ιC]

omit [DecidableEq Root] in
/-- ⭐ **The bridge.**  A checked transcript at the honest statement whose three
claims are true is an accepted run of the landed contraction sumcheck against
the built honest family, on the claimed output value `mle₂ C x y`. -/
theorem checked_sumcheckAccepts
    (SA : BindingCommitment Root F ιA OpA) (SB : BindingCommitment Root F ιB OpB)
    (SC : BindingCommitment Root F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (hcardA : 2 ^ (μ + κ) ≤ Fintype.card ιA) (hcardB : 2 ^ (κ + ν) ≤ Fintype.card ιB)
    (hcardC : 2 ^ (μ + ν) ≤ Fintype.card ιC)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F) (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (C : (Fin μ → Bool) → (Fin ν → Bool) → F) (x : Fin μ → F) (y : Fin ν → F) (value : F)
    (tr : Transcript Root F μ κ ν)
    (hchecked : Checked (honestStatement SA SB SC domA domB domC A B C x y value) tr)
    (hopen : OpeningsHold SA SB SC domA domB domC tr.claims) :
    SumcheckAccepts (v := κ) tr.prover (matmulHonest A B x y (chalOf tr.challenges))
      (mle₂ C x y) (matmulTrue A B x y) tr.challenges := by
  obtain ⟨hvC, hvA, hvB⟩ := matmul_opening_values_bound SA SB SC domA domB domC
    hcardA hcardB hcardC A B C x y tr.challenges tr.claims
    hchecked.leftRoot hchecked.rightRoot hchecked.outputRoot
    hchecked.leftPoint hchecked.rightPoint hchecked.outputPoint
    hopen.2.1 hopen.2.2 hopen.1
  have hH : value = mle₂ C x y := hchecked.outputValue.symm.trans hvC
  refine ⟨?_, ?_⟩
  · intro i hi
    have h := hchecked.rounds i hi
    simp only [RoundMessage.boolSum] at h
    rw [chain_eq_scChain, ← RoundMessage.poly_eval, ← RoundMessage.poly_eval] at h
    simpa [Transcript.prover, hH] using h
  · have hterm : scChain value tr.prover (chalOf tr.challenges) κ =
        tr.claims.left.val * tr.claims.right.val := by
      show scChain value (fun j => (tr.rounds j).poly) (chalOf tr.challenges) κ = _
      rw [← chain_eq_scChain]
      exact hchecked.terminal
    rw [scChain_matmulHonest_final, ← hvA, ← hvB, ← hterm, hH]

end Bind

/-! ## §5. Completeness: the honest transcript is accepted at every challenge -/

section Complete

variable {F : Type} [Field F] [DecidableEq F] {Root : Type} [DecidableEq Root]
variable {ιA ιB ιC OpA OpB OpC : Type*}
variable {μ κ ν : ℕ}

/-- The honest transcript: `matmulHonest`'s round polynomials as messages, the
challenges, and the three honest claims of `ZkmlMatmulCommitment`. -/
noncomputable def honestTranscript (SA : BindingCommitment Root F ιA OpA)
    (SB : BindingCommitment Root F ιB OpB) (SC : BindingCommitment Root F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F) (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (x : Fin μ → F) (y : Fin ν → F) (r : Fin κ → F) : Transcript Root F μ κ ν where
  rounds := fun i => messageOf (matmulHonest A B x y (chalOf r) i)
  challenges := r
  claims := honestMatmulMleClaims SA SB SC domA domB domC A B (matmulTable A B) x y r

omit [DecidableEq F] [DecidableEq Root] in
/-- ⭐ **Completeness.**  For every table pair, outer point and challenge vector,
the honest transcript at the honest statement is `Checked`. -/
theorem checker_complete (SA : BindingCommitment Root F ιA OpA)
    (SB : BindingCommitment Root F ιB OpB) (SC : BindingCommitment Root F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F) (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (x : Fin μ → F) (y : Fin ν → F) (r : Fin κ → F) :
    Checked (honestStatement SA SB SC domA domB domC A B (matmulTable A B) x y
        (mle₂ (matmulTable A B) x y))
      (honestTranscript SA SB SC domA domB domC A B x y r) := by
  have hcomplete := matmulHonest_complete A B x y r
  have hmsg : ∀ j, j < κ → ∀ t,
      (messageOf (matmulHonest A B x y (chalOf r) j)).eval t =
        (matmulHonest A B x y (chalOf r) j).eval t := by
    intro j hj t
    exact messageOf_eval (cubicHonest_degree _ _ _ _ _ _ j hj) t
  have hchain := chain_congr_scChain (mle₂ (matmulTable A B) x y)
    (fun i => messageOf (matmulHonest A B x y (chalOf r) i))
    (matmulHonest A B x y (chalOf r)) (chalOf r) hmsg
  refine
    { registered := auditIdentity_registered
      outputRoot := rfl
      leftRoot := rfl
      rightRoot := rfl
      outputPoint := rfl
      leftPoint := rfl
      rightPoint := rfl
      outputValue := rfl
      rounds := ?_
      terminal := ?_ }
  · intro i hi
    show (messageOf (matmulHonest A B x y (chalOf r) i)).boolSum =
      chain (mle₂ (matmulTable A B) x y)
        (fun i => messageOf (matmulHonest A B x y (chalOf r) i)) (chalOf r) i
    rw [RoundMessage.boolSum, hmsg i hi, hmsg i hi, hchain i (Nat.le_of_lt hi)]
    exact hcomplete.1 i hi
  · show chain (mle₂ (matmulTable A B) x y)
        (fun i => messageOf (matmulHonest A B x y (chalOf r) i)) (chalOf r) κ =
      mle (rowPartial A x) r * mle (colPartial B y) r
    rw [hchain κ le_rfl, ← matmul_claim_total A B x y]
    exact scChain_matmulHonest_final A B x y r

theorem checker_complete_accepts (SA : BindingCommitment Root F ιA OpA)
    (SB : BindingCommitment Root F ιB OpB) (SC : BindingCommitment Root F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F) (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (x : Fin μ → F) (y : Fin ν → F) (r : Fin κ → F) :
    accepts (honestStatement SA SB SC domA domB domC A B (matmulTable A B) x y
        (mle₂ (matmulTable A B) x y))
      (honestTranscript SA SB SC domA domB domC A B x y r) = true :=
  accepts_of_checked (checker_complete SA SB SC domA domB domC A B x y r)

end Complete

/-! ## §6. Soundness: the strategy, the contraction bound, and the complete budget -/

section Sound

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {Root : Type} [DecidableEq Root]
variable {μ κ ν : ℕ}

/-- The whole-protocol draw: the outer point, then the `κ` sumcheck challenges. -/
abbrev Draw (F : Type) (μ κ ν : ℕ) : Type := ((Fin μ → F) × (Fin ν → F)) × (Fin κ → F)

/-- An adaptive prover: round messages measurable in the challenge prefix, and
the claimed value and three opening claims chosen after all challenges. -/
structure Strategy (Root F : Type) (μ κ ν : ℕ) where
  message : (ℕ → F) → ℕ → RoundMessage F
  prefixMeasurable : ∀ (χ χ' : ℕ → F) (i : ℕ), (∀ j, j < i → χ j = χ' j) →
    message χ i = message χ' i
  value : (Fin μ → F) × (Fin ν → F) → F
  claims : (Fin μ → F) × (Fin ν → F) → (Fin κ → F) → MatmulMleClaims Root Root Root F μ κ ν

def Strategy.transcript (P : Strategy Root F μ κ ν) (o : (Fin μ → F) × (Fin ν → F))
    (r : Fin κ → F) : Transcript Root F μ κ ν :=
  ⟨P.message (chalOf r), r, P.claims o r⟩

noncomputable def Strategy.prover (P : Strategy Root F μ κ ν) : (ℕ → F) → ℕ → Polynomial F :=
  fun χ i => (P.message χ i).poly

omit [Fintype F] [DecidableEq F] [DecidableEq Root] in
theorem Strategy.prover_prefixMeasurable (P : Strategy Root F μ κ ν) :
    PrefixMeasurable P.prover := by
  intro χ χ' i h
  simp only [Strategy.prover, P.prefixMeasurable χ χ' i h]

omit [Fintype F] [DecidableEq F] [DecidableEq Root] in
theorem Strategy.prover_degree (P : Strategy Root F μ κ ν) :
    ∀ (χ : ℕ → F) (i : ℕ), i < κ → (P.prover χ i).degree < ((3 + 1 : ℕ) : WithBot ℕ) :=
  fun χ i _ => RoundMessage.poly_degree (P.message χ i)

variable {ιA ιB ιC OpA OpB OpC : Type*} [Fintype ιA] [Fintype ιB] [Fintype ιC]

/-- The checker's acceptance event on one draw, at the honest statement. -/
def Strategy.Accepts (P : Strategy Root F μ κ ν)
    (SA : BindingCommitment Root F ιA OpA) (SB : BindingCommitment Root F ιB OpB)
    (SC : BindingCommitment Root F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F) (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (C : (Fin μ → Bool) → (Fin ν → Bool) → F) (w : Draw F μ κ ν) : Prop :=
  accepts (honestStatement SA SB SC domA domB domC A B C w.1.1 w.1.2 (P.value w.1))
    (P.transcript w.1 w.2) = true

/-- ⭐ **Contraction soundness, PCS truth as a named premise.**  If the claimed
output table `C` is wrong as a table, the checker accepts with true openings
with probability at most `(μ+ν)/|F| + κ·3/|F|`. -/
theorem strategy_sound
    (SA : BindingCommitment Root F ιA OpA) (SB : BindingCommitment Root F ιB OpB)
    (SC : BindingCommitment Root F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (hcardA : 2 ^ (μ + κ) ≤ Fintype.card ιA) (hcardB : 2 ^ (κ + ν) ≤ Fintype.card ιB)
    (hcardC : 2 ^ (μ + ν) ≤ Fintype.card ιC)
    {A : (Fin μ → Bool) → (Fin κ → Bool) → F} {B : (Fin κ → Bool) → (Fin ν → Bool) → F}
    {C : (Fin μ → Bool) → (Fin ν → Bool) → F} (hC : C ≠ matmulTable A B)
    (P : Strategy Root F μ κ ν) :
    uniformProb (Draw F μ κ ν) (fun w =>
        P.Accepts SA SB SC domA domB domC A B C w ∧
          OpeningsHold SA SB SC domA domB domC (P.claims w.1 w.2))
      ≤ ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F) := by
  refine le_trans (uniformProb_mono ?_)
    (matmul_sumcheck_soundness hC P.prover_prefixMeasurable P.prover_degree)
  rintro w ⟨hacc, hopen⟩
  exact checked_sumcheckAccepts SA SB SC domA domB domC hcardA hcardB hcardC A B C
    w.1.1 w.1.2 (P.value w.1) (P.transcript w.1 w.2) (accepts_sound hacc) hopen

/-- ⭐ **The budget with the PCS event visible.**  Without any premise on the
openings, acceptance of a wrong table is at most the contraction bound plus
the probability that the checker accepts while some opening claim is false. -/
theorem strategy_sound_budget
    (SA : BindingCommitment Root F ιA OpA) (SB : BindingCommitment Root F ιB OpB)
    (SC : BindingCommitment Root F ιC OpC)
    (domA : ιA ↪ F) (domB : ιB ↪ F) (domC : ιC ↪ F)
    (hcardA : 2 ^ (μ + κ) ≤ Fintype.card ιA) (hcardB : 2 ^ (κ + ν) ≤ Fintype.card ιB)
    (hcardC : 2 ^ (μ + ν) ≤ Fintype.card ιC)
    {A : (Fin μ → Bool) → (Fin κ → Bool) → F} {B : (Fin κ → Bool) → (Fin ν → Bool) → F}
    {C : (Fin μ → Bool) → (Fin ν → Bool) → F} (hC : C ≠ matmulTable A B)
    (P : Strategy Root F μ κ ν) :
    uniformProb (Draw F μ κ ν) (fun w => P.Accepts SA SB SC domA domB domC A B C w)
      ≤ ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F) +
        uniformProb (Draw F μ κ ν) (fun w =>
          P.Accepts SA SB SC domA domB domC A B C w ∧
            ¬ OpeningsHold SA SB SC domA domB domC (P.claims w.1 w.2)) := by
  classical
  have hsplit : ∀ w : Draw F μ κ ν, P.Accepts SA SB SC domA domB domC A B C w →
      (P.Accepts SA SB SC domA domB domC A B C w ∧
          OpeningsHold SA SB SC domA domB domC (P.claims w.1 w.2)) ∨
        (P.Accepts SA SB SC domA domB domC A B C w ∧
          ¬ OpeningsHold SA SB SC domA domB domC (P.claims w.1 w.2)) := by
    intro w h
    by_cases ho : OpeningsHold SA SB SC domA domB domC (P.claims w.1 w.2)
    · exact Or.inl ⟨h, ho⟩
    · exact Or.inr ⟨h, ho⟩
  refine le_trans (uniformProb_mono hsplit) ?_
  refine le_trans (uniformProb_or_le _ _) ?_
  exact add_le_add
    (strategy_sound SA SB SC domA domB domC hcardA hcardB hcardC hC P) le_rfl

/-- **The complete failure budget**: the contraction's two terms plus the
existing three-opening BaseFold ledger, unchanged. -/
noncomputable def matmulSuccinctSoundnessBudget (F : Type) [Fintype F] (μ κ ν : ℕ) : ℝ :=
  ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F) +
    matmulBaseFoldIorAlgebraicBudget F μ κ ν

omit [Field F] [DecidableEq F] in
theorem matmulSuccinctSoundnessBudget_eq :
    matmulSuccinctSoundnessBudget F μ κ ν =
      ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F) +
        ((μ + ν : ℕ) : ℝ) * (3 / Fintype.card F) +
        ((μ + κ : ℕ) : ℝ) * (3 / Fintype.card F) +
        ((κ + ν : ℕ) : ℝ) * (3 / Fintype.card F) := by
  simp only [matmulSuccinctSoundnessBudget, matmulBaseFoldIorAlgebraicBudget]
  ring

end Sound

/-! ## §7. The composed full-word verifier and its complete budget

Each opening claim is resolved by the tree's full-word BaseFold IOR verifier
`BaseFoldIorAccepts` on the word the statement root commits.  Composing the
three opening draws with the contraction draw gives the complete budget.  The
verifier reads whole words here; sampled queries, BCS and `[COMMIT-CR]` are
the retained obligations of `BaseFoldCommittedIor` / `BaseFoldRawCommittedIor`. -/

section FullWord

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {Root : Type} [DecidableEq Root]
variable {μ κ ν : ℕ}
variable {ιA ιB ιC : ℕ → Type*} {OpA OpB OpC : Type*}
variable [∀ n, Fintype (ιA n)] [∀ n, Fintype (ιB n)] [∀ n, Fintype (ιC n)]

/-- The three opening draws. -/
abbrev OpenDraw (F : Type) (μ κ ν : ℕ) : Type :=
  (Fin (μ + ν) → F) × (Fin (μ + κ) → F) × (Fin (κ + ν) → F)

/-- An adaptive prover for the composed protocol: the contraction strategy plus
one prefix-measurable degree-≤2 opening prover per claim, chosen after the
contraction draw. -/
structure FullStrategy (Root F : Type) [Field F] (μ κ ν : ℕ)
    extends Strategy Root F μ κ ν where
  openC : Draw F μ κ ν → (ℕ → F) → ℕ → Polynomial F
  openA : Draw F μ κ ν → (ℕ → F) → ℕ → Polynomial F
  openB : Draw F μ κ ν → (ℕ → F) → ℕ → Polynomial F
  openC_pm : ∀ w, PrefixMeasurable (openC w)
  openA_pm : ∀ w, PrefixMeasurable (openA w)
  openB_pm : ∀ w, PrefixMeasurable (openB w)
  openC_deg : ∀ w (χ : ℕ → F) (i : ℕ), i < μ + ν →
    (openC w χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)
  openA_deg : ∀ w (χ : ℕ → F) (i : ℕ), i < μ + κ →
    (openA w χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)
  openB_deg : ∀ w (χ : ℕ → F) (i : ℕ), i < κ + ν →
    (openB w χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)

/-- The composed verifier: the runnable checker accepts, and each of the three
opening claims passes the full-word BaseFold IOR on the committed word. -/
def FullStrategy.Accepts (P : FullStrategy Root F μ κ ν)
    (SA : BindingCommitment Root F (ιA 0) OpA) (SB : BindingCommitment Root F (ιB 0) OpB)
    (SC : BindingCommitment Root F (ιC 0) OpC)
    (TA : FoldingTower F ιA (μ + κ)) (TB : FoldingTower F ιB (κ + ν))
    (TC : FoldingTower F ιC (μ + ν))
    (A : (Fin μ → Bool) → (Fin κ → Bool) → F) (B : (Fin κ → Bool) → (Fin ν → Bool) → F)
    (C : (Fin μ → Bool) → (Fin ν → Bool) → F)
    (d : Draw F μ κ ν × OpenDraw F μ κ ν) : Prop :=
  P.toStrategy.Accepts SA SB SC (TA.dom 0) (TB.dom 0) (TC.dom 0) A B C d.1 ∧
  BaseFoldIorAccepts TC (P.claims d.1.1 d.1.2).output.pt (P.claims d.1.1 d.1.2).output.val
    (basefoldWord (TC.dom 0) (flatten₂ C)) (P.openC d.1) d.2.1 ∧
  BaseFoldIorAccepts TA (P.claims d.1.1 d.1.2).left.pt (P.claims d.1.1 d.1.2).left.val
    (basefoldWord (TA.dom 0) (flatten₂ A)) (P.openA d.1) d.2.2.1 ∧
  BaseFoldIorAccepts TB (P.claims d.1.1 d.1.2).right.pt (P.claims d.1.1 d.1.2).right.val
    (basefoldWord (TB.dom 0) (flatten₂ B)) (P.openB d.1) d.2.2.2

omit [Fintype F] [DecidableEq Root] in
/-- A false claim at an honest root is not a strict BaseFold claim on the
committed word: one word admits one value (`basefoldExactClaim_value_unique`). -/
theorem not_exactClaim_of_not_holds {ι : ℕ → Type*} {Op : Type*} [Fintype (ι 0)] {m : ℕ}
    (S : BindingCommitment Root F (ι 0) Op) (T : FoldingTower F ι m)
    (hcard : 2 ^ m ≤ Fintype.card (ι 0)) (table : (Fin m → Bool) → F)
    (c : MleEvalClaim Root F m) (hrt : c.rt = S.commit (basefoldWord (T.dom 0) table))
    (hnot : ¬ c.Holds S (T.dom 0)) :
    ¬ BaseFoldExactClaim T c.pt c.val (basefoldWord (T.dom 0) table) := by
  intro hex
  have honest : BaseFoldExactClaim T c.pt (mle table c.pt) (basefoldWord (T.dom 0) table) :=
    ⟨table, rfl, rfl⟩
  have hval := basefoldExactClaim_value_unique T hcard c.pt hex honest
  exact hnot ⟨table, hrt, hval.symm⟩

omit [DecidableEq Root] in
/-- One opening's failure term: acceptance with a false claim at that root is
priced by the full-word IOR at `m·3/|F|`, uniformly in everything drawn earlier. -/
theorem opening_term_le {ι : ℕ → Type*} {Op : Type*} [∀ n, Fintype (ι n)] {m : ℕ}
    (S : BindingCommitment Root F (ι 0) Op) (T : FoldingTower F ι m)
    (hne : ∀ n, n ≤ m → Nonempty (ι n)) (hcard : 2 ^ m ≤ Fintype.card (ι 0))
    (table : (Fin m → Bool) → F) (c : MleEvalClaim Root F m)
    (hrt : c.rt = S.commit (basefoldWord (T.dom 0) table))
    (prover : (ℕ → F) → ℕ → Polynomial F) (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → F) (fun r =>
      ¬ c.Holds S (T.dom 0) ∧
        BaseFoldIorAccepts T c.pt c.val (basefoldWord (T.dom 0) table) prover r)
      ≤ (m : ℝ) * (3 / Fintype.card F) := by
  by_cases hholds : c.Holds S (T.dom 0)
  · rw [uniformProb_false fun _ h => h.1 hholds]
    positivity
  · refine le_trans (uniformProb_mono fun _ h => h.2) ?_
    exact basefoldIor_exact_sound T c.pt c.val _ prover hne
      (not_exactClaim_of_not_holds S T hcard table c hrt hholds) hpm hdeg

/-- ⭐ **The complete budget, composed.**  Against any adaptive full strategy,
a wrong output table passes the composed full-word verifier with probability
at most `matmulSuccinctSoundnessBudget F μ κ ν`. -/
theorem fullWord_sound
    (SA : BindingCommitment Root F (ιA 0) OpA) (SB : BindingCommitment Root F (ιB 0) OpB)
    (SC : BindingCommitment Root F (ιC 0) OpC)
    (TA : FoldingTower F ιA (μ + κ)) (TB : FoldingTower F ιB (κ + ν))
    (TC : FoldingTower F ιC (μ + ν))
    (hneA : ∀ n, n ≤ μ + κ → Nonempty (ιA n)) (hneB : ∀ n, n ≤ κ + ν → Nonempty (ιB n))
    (hneC : ∀ n, n ≤ μ + ν → Nonempty (ιC n))
    (hcardA : 2 ^ (μ + κ) ≤ Fintype.card (ιA 0)) (hcardB : 2 ^ (κ + ν) ≤ Fintype.card (ιB 0))
    (hcardC : 2 ^ (μ + ν) ≤ Fintype.card (ιC 0))
    {A : (Fin μ → Bool) → (Fin κ → Bool) → F} {B : (Fin κ → Bool) → (Fin ν → Bool) → F}
    {C : (Fin μ → Bool) → (Fin ν → Bool) → F} (hC : C ≠ matmulTable A B)
    (P : FullStrategy Root F μ κ ν) :
    uniformProb (Draw F μ κ ν × OpenDraw F μ κ ν)
        (P.Accepts SA SB SC TA TB TC A B C)
      ≤ matmulSuccinctSoundnessBudget F μ κ ν := by
  classical
  -- Shorthands.
  set dA := TA.dom 0
  set dB := TB.dom 0
  set dC := TC.dom 0
  let Acc : Draw F μ κ ν → Prop := P.toStrategy.Accepts SA SB SC dA dB dC A B C
  let Hold : Draw F μ κ ν → Prop := fun w =>
    OpeningsHold SA SB SC dA dB dC (P.claims w.1 w.2)
  let IorC : Draw F μ κ ν → (Fin (μ + ν) → F) → Prop := fun w r =>
    BaseFoldIorAccepts TC (P.claims w.1 w.2).output.pt (P.claims w.1 w.2).output.val
      (basefoldWord dC (flatten₂ C)) (P.openC w) r
  let IorA : Draw F μ κ ν → (Fin (μ + κ) → F) → Prop := fun w r =>
    BaseFoldIorAccepts TA (P.claims w.1 w.2).left.pt (P.claims w.1 w.2).left.val
      (basefoldWord dA (flatten₂ A)) (P.openA w) r
  let IorB : Draw F μ κ ν → (Fin (κ + ν) → F) → Prop := fun w r =>
    BaseFoldIorAccepts TB (P.claims w.1 w.2).right.pt (P.claims w.1 w.2).right.val
      (basefoldWord dB (flatten₂ B)) (P.openB w) r
  -- The four-way split of the composed acceptance event.
  have hsplit : ∀ d : Draw F μ κ ν × OpenDraw F μ κ ν,
      P.Accepts SA SB SC TA TB TC A B C d →
        ((Acc d.1 ∧ Hold d.1) ∨
          (Acc d.1 ∧ ¬ (P.claims d.1.1 d.1.2).output.Holds SC dC ∧ IorC d.1 d.2.1)) ∨
        ((Acc d.1 ∧ ¬ (P.claims d.1.1 d.1.2).left.Holds SA dA ∧ IorA d.1 d.2.2.1) ∨
          (Acc d.1 ∧ ¬ (P.claims d.1.1 d.1.2).right.Holds SB dB ∧ IorB d.1 d.2.2.2)) := by
    rintro d ⟨hacc, hC', hA', hB'⟩
    by_cases hoC : (P.claims d.1.1 d.1.2).output.Holds SC dC
    · by_cases hoA : (P.claims d.1.1 d.1.2).left.Holds SA dA
      · by_cases hoB : (P.claims d.1.1 d.1.2).right.Holds SB dB
        · exact Or.inl (Or.inl ⟨hacc, hoC, hoA, hoB⟩)
        · exact Or.inr (Or.inr ⟨hacc, hoB, hB'⟩)
      · exact Or.inr (Or.inl ⟨hacc, hoA, hA'⟩)
    · exact Or.inl (Or.inr ⟨hacc, hoC, hC'⟩)
  refine le_trans (uniformProb_mono hsplit) ?_
  refine le_trans (uniformProb_or_le _ _) ?_
  refine le_trans (add_le_add (uniformProb_or_le _ _) (uniformProb_or_le _ _)) ?_
  have hF : (0 : ℝ) ≤ 3 / Fintype.card F := by positivity
  -- Term 1: the contraction bound, read off the first coordinate.
  have h1 : uniformProb (Draw F μ κ ν × OpenDraw F μ κ ν)
      (fun d => Acc d.1 ∧ Hold d.1)
      ≤ ((μ : ℝ) + ν) / Fintype.card F + (κ : ℝ) * (3 / Fintype.card F) := by
    refine uniformProb_fst_le _ (fun w => Acc w ∧ Hold w) (fun _ => Iff.rfl)
      (by positivity) ?_
    exact strategy_sound SA SB SC dA dB dC hcardA hcardB hcardC hC P.toStrategy
  -- Term 2: the output opening.
  have h2 : uniformProb (Draw F μ κ ν × OpenDraw F μ κ ν)
      (fun d => Acc d.1 ∧ ¬ (P.claims d.1.1 d.1.2).output.Holds SC dC ∧ IorC d.1 d.2.1)
      ≤ ((μ + ν : ℕ) : ℝ) * (3 / Fintype.card F) := by
    refine uniformProb_prod_le (by positivity) fun w => ?_
    by_cases hacc : Acc w
    · refine uniformProb_fst_le _
        (fun r => ¬ (P.claims w.1 w.2).output.Holds SC dC ∧ IorC w r)
        (fun _ => by simp [hacc]) (by positivity) ?_
      have hrt : (P.claims w.1 w.2).output.rt = SC.commit (basefoldWord dC (flatten₂ C)) :=
        (accepts_sound hacc).outputRoot
      exact opening_term_le SC TC hneC hcardC (flatten₂ C) _ hrt (P.openC w)
        (P.openC_pm w) (P.openC_deg w)
    · rw [uniformProb_false fun _ h => hacc h.1]
      positivity
  -- Term 3: the left opening (second opening coordinate).
  have h3 : uniformProb (Draw F μ κ ν × OpenDraw F μ κ ν)
      (fun d => Acc d.1 ∧ ¬ (P.claims d.1.1 d.1.2).left.Holds SA dA ∧ IorA d.1 d.2.2.1)
      ≤ ((μ + κ : ℕ) : ℝ) * (3 / Fintype.card F) := by
    refine uniformProb_prod_le (by positivity) fun w => ?_
    by_cases hacc : Acc w
    · refine uniformProb_prod_le (by positivity) fun _ => ?_
      refine uniformProb_fst_le _
        (fun r => ¬ (P.claims w.1 w.2).left.Holds SA dA ∧ IorA w r)
        (fun _ => by simp [hacc]) (by positivity) ?_
      have hrt : (P.claims w.1 w.2).left.rt = SA.commit (basefoldWord dA (flatten₂ A)) :=
        (accepts_sound hacc).leftRoot
      exact opening_term_le SA TA hneA hcardA (flatten₂ A) _ hrt (P.openA w)
        (P.openA_pm w) (P.openA_deg w)
    · rw [uniformProb_false fun _ h => hacc h.1]
      positivity
  -- Term 4: the right opening (third opening coordinate).
  have h4 : uniformProb (Draw F μ κ ν × OpenDraw F μ κ ν)
      (fun d => Acc d.1 ∧ ¬ (P.claims d.1.1 d.1.2).right.Holds SB dB ∧ IorB d.1 d.2.2.2)
      ≤ ((κ + ν : ℕ) : ℝ) * (3 / Fintype.card F) := by
    refine uniformProb_prod_le (by positivity) fun w => ?_
    by_cases hacc : Acc w
    · refine uniformProb_prod_le (by positivity) fun _ => ?_
      refine uniformProb_prod_le (by positivity) fun _ => ?_
      have hrt : (P.claims w.1 w.2).right.rt = SB.commit (basefoldWord dB (flatten₂ B)) :=
        (accepts_sound hacc).rightRoot
      refine le_trans (uniformProb_mono fun r h => h.2) ?_
      exact opening_term_le SB TB hneB hcardB (flatten₂ B) _ hrt (P.openB w)
        (P.openB_pm w) (P.openB_deg w)
    · rw [uniformProb_false fun _ h => hacc h.1]
      positivity
  rw [matmulSuccinctSoundnessBudget_eq]
  linarith [h1, h2, h3, h4]

end FullWord

/-! ## §8. The F7 instance: decided, and proved to be the honest one -/

/-- The two-variable Boolean Möbius packing, evaluated: the four table entries
with `b 0` the LSB.  Stated at `1 + 1` so it matches `flatten₂`'s cube. -/
theorem booleanMobiusPolynomial_two_eval {F : Type} [Field F]
    (f : (Fin (1 + 1) → Bool) → F) (x : F) :
    (booleanMobiusPolynomial (1 + 1) f).eval x =
      f ![false, false] + x * (f ![true, false] - f ![false, false])
        + x ^ 2 * ((f ![false, true] - f ![false, false])
          + x * ((f ![true, true] - f ![false, true])
            - (f ![true, false] - f ![false, false]))) := by
  have hcons : ∀ a b : Bool,
      lsbCons a (lsbCons b (fun i => Fin.elim0 i)) = ![a, b] := by
    intro a b
    funext i
    fin_cases i <;> rfl
  simp only [booleanMobiusPolynomial, parityInterleave, eval_add, eval_mul, eval_X,
    Polynomial.expand_eval, eval_sub, eval_C, tableLsb, hcons]
  ring

namespace SuccinctExample

open MatmulExample MatmulCommitmentExample

abbrev F7 := ZMod 7
abbrev Root7 := Fin 4 → F7
abbrev S7 := idealCommitment F7 (Fin 4)

/-- The literal BaseFold words of `eA`, `eB`, and `eA · eB` on the four-point
domain — the roots under the identity commitment. -/
def rootA : Root7 := ![1, 4, 2, 2]
def rootB : Root7 := ![5, 1, 6, 6]
def rootC : Root7 := ![5, 1, 6, 2]

/-- The round-0 message `3t + 2t²` of the contraction at `x = 3, y = 5`. -/
def message : RoundMessage F7 := ⟨0, 3, 2, 0⟩

def stmt : Statement Root7 F7 1 1 1 :=
  ⟨auditIdentity, rootA, rootB, rootC, ![3], ![5], 5⟩

def tr : Transcript Root7 F7 1 1 1 :=
  ⟨messagesOf ![message], ![4],
    ⟨⟨rootC, Fin.append ![3] ![5], 5⟩,
      ⟨rootA, Fin.append ![3] ![4], 4⟩,
      ⟨rootB, Fin.append ![4] ![5], 4⟩⟩⟩

/-- ⭐ The runnable checker accepts the instance, decided by the kernel. -/
theorem checker_complete_f7 : accepts stmt tr = true := by decide

/-! ### Refusal teeth — each a distinct route -/

theorem wrong_suite_refused :
    failure { stmt with suite := unregisteredIdentity } tr = some .unregisteredSuite := by
  decide

theorem forged_output_value_refused :
    failure { stmt with value := 6 }
      { tr with claims := { tr.claims with output := ⟨rootC, Fin.append ![3] ![5], 6⟩ } }
      = some (.roundSumMismatch 0) := by
  decide

theorem forged_left_opening_refused :
    failure stmt
      { tr with claims := { tr.claims with left := ⟨rootA, Fin.append ![3] ![4], 5⟩ } }
      = some .terminalMismatch := by
  decide

theorem forged_right_opening_refused :
    failure stmt
      { tr with claims := { tr.claims with right := ⟨rootB, Fin.append ![4] ![5], 5⟩ } }
      = some .terminalMismatch := by
  decide

theorem forged_root_refused :
    failure stmt
      { tr with claims :=
        { tr.claims with output := ⟨![5, 1, 6, 3], Fin.append ![3] ![5], 5⟩ } }
      = some .outputRootMismatch := by
  decide

theorem forged_point_refused :
    failure stmt
      { tr with claims := { tr.claims with left := ⟨rootA, Fin.append ![3] ![5], 4⟩ } }
      = some .leftPointMismatch := by
  decide

theorem forged_round_message_refused :
    failure stmt { tr with rounds := messagesOf ![⟨0, 4, 2, 0⟩] }
      = some (.roundSumMismatch 0) := by
  decide

/-- The challenge is bound to the operand openings: replaying the same claims
under another challenge is refused at the point check, not by luck. -/
theorem swapped_challenge_refused :
    failure stmt { tr with challenges := ![5] } = some .leftPointMismatch := by
  decide

/-! ### The instance IS the honest one -/

theorem rootA_honest : rootA = S7.commit (basefoldWord dom₇₄ (flatten₂ eA)) := by
  funext i
  rw [idealCommitment_commit]
  simp only [basefoldWord, booleanMobiusPolynomial_two_eval]
  fin_cases i <;> decide

theorem rootB_honest : rootB = S7.commit (basefoldWord dom₇₄ (flatten₂ eB)) := by
  funext i
  rw [idealCommitment_commit]
  simp only [basefoldWord, booleanMobiusPolynomial_two_eval]
  fin_cases i <;> decide

theorem rootC_honest :
    rootC = S7.commit (basefoldWord dom₇₄ (flatten₂ (matmulTable eA eB))) := by
  funext i
  rw [idealCommitment_commit]
  simp only [basefoldWord, booleanMobiusPolynomial_two_eval]
  fin_cases i <;> decide

/-- The literal message is the honest prover's round-0 polynomial. -/
theorem message_honest :
    message = messageOf (matmulHonest eA eB ![3] ![5] (chalOf ![4]) 0) := by
  simp only [messageOf, matmulHonest, cubicHonest, dif_pos (show 0 < 1 by decide),
    cubicRoundPoly, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp only [message, RoundMessage.mk.injEq]
  simp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem instance_statement_honest :
    stmt = honestStatement S7 S7 S7 dom₇₄ dom₇₄ dom₇₄ eA eB (matmulTable eA eB) ![3] ![5] 5 := by
  simp only [stmt, honestStatement, rootA_honest, rootB_honest, rootC_honest]

theorem instance_transcript_honest :
    tr = honestTranscript S7 S7 S7 dom₇₄ dom₇₄ dom₇₄ eA eB ![3] ![5] ![4] := by
  have hrounds : (messagesOf ![message] : ℕ → RoundMessage F7) =
      fun i => messageOf (matmulHonest eA eB ![3] ![5] (chalOf ![4]) i) := by
    funext i
    cases i with
    | zero => exact message_honest
    | succ n =>
      simp only [messagesOf, matmulHonest, cubicHonest, messageOf]
      rw [dif_neg (by omega), dif_neg (by omega)]
      simp
  have hvC : mle₂ (matmulTable eA eB) ![3] ![5] = (5 : F7) := by decide
  have hvA : mle (rowPartial eA ![3]) ![4] = (4 : F7) := by decide
  have hvB : mle (colPartial eB ![5]) ![4] = (4 : F7) := by decide
  unfold tr honestTranscript honestMatmulMleClaims
  rw [hrounds, ← rootA_honest, ← rootB_honest, ← rootC_honest, hvA, hvB, hvC]

/-- The complete budget at the toy instance is larger than one: the runnable
shape is not a secure parameterization. -/
theorem budget_f7 : matmulSuccinctSoundnessBudget F7 1 1 1 = (23 : ℝ) / 7 := by
  rw [matmulSuccinctSoundnessBudget_eq, ZMod.card]
  norm_num

end SuccinctExample

/-! ## §9. Axiom pins -/

/-- info: 'Minidregg.Assurance.ZkmlMatmulSuccinctChecker.accepts_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepts_iff
/-- info: 'Minidregg.Assurance.ZkmlMatmulSuccinctChecker.checked_sumcheckAccepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checked_sumcheckAccepts
/-- info: 'Minidregg.Assurance.ZkmlMatmulSuccinctChecker.checker_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checker_complete
/-- info: 'Minidregg.Assurance.ZkmlMatmulSuccinctChecker.strategy_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms strategy_sound
/-- info: 'Minidregg.Assurance.ZkmlMatmulSuccinctChecker.strategy_sound_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms strategy_sound_budget
/-- info: 'Minidregg.Assurance.ZkmlMatmulSuccinctChecker.fullWord_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fullWord_sound
/-- info: 'Minidregg.Assurance.ZkmlMatmulSuccinctChecker.SuccinctExample.checker_complete_f7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SuccinctExample.checker_complete_f7
/-- info: 'Minidregg.Assurance.ZkmlMatmulSuccinctChecker.SuccinctExample.instance_transcript_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SuccinctExample.instance_transcript_honest
/-- info: 'Minidregg.Assurance.ZkmlMatmulSuccinctChecker.SuccinctExample.forged_left_opening_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SuccinctExample.forged_left_opening_refused

end Minidregg.Assurance.ZkmlMatmulSuccinctChecker
