/-
# Kernel.HyperedgeTier — the hyperedge turn meets the finality lattice

Law 2 (ordering, `Theory/Finality.lean`) connected to the ONE turn model
(`Kernel/Turn.lean`) and to the conservation aggregate that turn model already carries:

  * **the commit tier of a turn** is the join of the tiers of the cells it writes —
    `commitTier tierOf := Finset.univ.sup tierOf` over the hyperedge's incidence type.
    Every leg is dominated (`leg_le_commitTier`); the join is always some written
    cell's tier (`commitTier_attained`); and a turn runs coordination-free iff EVERY
    written cell is tier 1 (`commitTier_eq_causal_iff`).
  * **canonicity through the join-tier rule only** (`hyperedge_commit_at_join`): the
    finality rule installed at the commit tier commits the hyperedge's apex id, and
    — through the cone condition `agree` — every leg's post-step id is canonical.
    The one apex is what the rule commits; the legs inherit it as a theorem.
  * **Law 1 and Law 2 are orthogonal, definitionally**: the tier-annotated
    conservation verdict is the hyperedge's own `balanced` aggregate
    (`Σᵢ halfEdge i (xᵢ) t = 0`) with the tier DISCARDED, so
    `conservation_tier_independent` is `rfl`, `conservedAtTier_holds` is
    `H.balanced` at every tier, and the tooth — `Hyperedge.binding_is_proper`'s
    `Σ = 1` cone — is refused at every tier (`binding_tooth_tier_blind`).
    Re-tagging a cell's tier can neither create nor destroy resource.

The conservation section is MODEL-NEUTRAL on purpose: it reads the aggregate off
`Hyperedge`, not off a concrete state model (`docs/KERNEL-TWIN-AUDIT.md`: the tree
carries two twin state models whose fate is undecided; this file depends on neither).
Witnesses reuse `Kernel/TurnLimit.lean`'s `stepId`/`zeroRead` and
`Kernel/TurnBalancedLimit.lean`'s `stateHalf`/`transferBalanced`/`lopTuple`.

Residuals (prose, not `Prop := True`):

  [TIER-of-cell]  no state model carries a per-cell tier field yet — `tierOf` is a
                  parameter of every statement here. Making it a cell attribute (and
                  the frame rule for it — a turn leaves the tiers of cells outside its
                  footprint untouched) is future vocabulary.
  [TIER-gate]     the admission gate (`Kernel/Gate.lean` `admit`) does not yet
                  consult tiers: the join-tier hold ("effects wait for the join-tier
                  rule's commit") is stated on the rule, not enforced by the gate.
-/
import Theory.Finality
import Kernel.Turn
import Kernel.TurnLimit
import Kernel.TurnBalancedLimit

namespace Minidregg.Kernel.HyperedgeTier

open Minidregg.Theory.Finality

set_option autoImplicit false

universe v uCarrier uTurn uTurnId uBal

/-! ## §1. The commit tier of a turn. -/

/-- **The commit tier of a hyperedge** whose incidence `i` writes a cell of tier
`tierOf i`: the join of the written cells' tiers. -/
def commitTier {ι : Type v} [Fintype ι] (tierOf : ι → Tier) : Tier :=
  Finset.univ.sup tierOf

/-- Every written cell's tier is dominated by the commit tier. -/
theorem leg_le_commitTier {ι : Type v} [Fintype ι] (tierOf : ι → Tier) (i : ι) :
    tierOf i ≤ commitTier tierOf :=
  Finset.le_sup (Finset.mem_univ i)

/-- The commit tier of a turn writing at least one cell IS the tier of one of the
cells it writes — the join never invents a level. -/
theorem commitTier_attained {ι : Type v} [Fintype ι] [Nonempty ι] (tierOf : ι → Tier) :
    ∃ i, commitTier tierOf = tierOf i :=
  join_attained tierOf

/-- **A turn runs coordination-free iff EVERY written cell is tier 1.** One
higher-tier cell in the footprint lifts the whole turn to its rule. -/
theorem commitTier_eq_causal_iff {ι : Type v} [Fintype ι] (tierOf : ι → Tier) :
    commitTier tierOf = .causal ↔ ∀ i, tierOf i = .causal := by
  unfold commitTier
  rw [← Tier.bot_eq_causal, Finset.sup_eq_bot_iff]
  simp

section Hyperedge

variable {ι : Type v} [Fintype ι]
variable {Carrier : Type uCarrier} {Turn : Type uTurn} {TurnId : Type uTurnId} {Bal : Type uBal}
variable [AddCommMonoid Bal] [DecidableEq TurnId]
variable {step : Carrier → Turn → Carrier} {turnId : ι → Carrier → TurnId}
variable {halfEdge : ι → Carrier → Turn → Bal}

/-! ## §2. Canonicity is granted through the join-tier rule only. -/

/-- **The hyperedge commits at the join of its written cells' tiers.** For a
hyperedge `H` over incidences `ι` with cell tiers `tierOf`, and the finality rule
installed at `commitTier tierOf` over apex ids: once that rule commits `H.tid`,
(i) every leg's tier is dominated by the rule's tier, (ii) the apex is canonical,
and (iii) every leg's post-step id is canonical — by the cone condition `agree`,
not by any per-leg commit. -/
theorem hyperedge_commit_at_join
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge)
    (tierOf : ι → Tier)
    (rule : FinalityRule TurnId) (hrule : rule.tier = commitTier tierOf)
    (hcommit : rule.committed H.tid) :
    (∀ i, tierOf i ≤ rule.tier)
      ∧ rule.canonical H.tid
      ∧ ∀ i, rule.canonical (turnId i (step (H.x i) H.t)) := by
  obtain ⟨hdom, hcanon⟩ := commit_at_join_of_tiers tierOf rule hrule H.tid hcommit
  exact ⟨hdom, hcanon, fun i => (H.agree i).symm ▸ hcanon⟩

/-! ## §3. Law 1 (conservation) is tier-independent. -/

/-- **The tier-annotated balance verdict on cone DATA**: a participant tuple `x`
firing turn `t` conserves under `halfEdge` iff its half-edge sum is `0` — the
`balanced` field of `Hyperedge`, asked of data that may or may not be a hyperedge.
The `Tier` argument is DISCARDED: that discarding is precisely "the tier does not
enter the conservation measure". -/
def balancedAtTier (_t : Tier) (halfEdge : ι → Carrier → Turn → Bal)
    (x : ι → Carrier) (t : Turn) : Prop :=
  (Finset.univ.sum fun i => halfEdge i (x i) t) = 0

/-- **The tier-annotated conservation verdict of a built hyperedge**: its own
aggregate `Σᵢ halfEdge i (H.x i) H.t = 0`, annotated at tier `t` and discarding it. -/
def conservedAtTier (_t : Tier) (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge) :
    Prop :=
  balancedAtTier _t halfEdge H.x H.t

/-- The verdict has content: at every tier it is exactly the hyperedge's `balanced`
field, which mentions no tier. -/
theorem conservedAtTier_holds (t : Tier)
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge) :
    conservedAtTier t H :=
  H.balanced

/-- **Conservation is tier-independent** (paper2 §2.4 closing clause). For any two
tiers the verdict is the SAME proposition — `rfl`, because the tier is discarded.
Law 1 (conservation) and Law 2 (ordering) are orthogonal. -/
theorem conservation_tier_independent (t₁ t₂ : Tier)
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge) :
    conservedAtTier t₁ H = conservedAtTier t₂ H :=
  rfl

end Hyperedge

/-- **The binding tooth is tier-blind.** `Hyperedge.binding_is_proper`'s data — a
one-incidence cone (the cone condition holds) whose half-edge sum is `1` — is refused
at EVERY tier: no tier annotation makes an unbalanced cone conserve, so no
`Hyperedge` exists on it at any tier. -/
theorem binding_tooth_tier_blind :
    ∃ (x : Unit → ℤ) (t : ℤ) (tid : ℤ)
      (step : ℤ → ℤ → ℤ) (turnId : Unit → ℤ → ℤ) (halfEdge : Unit → ℤ → ℤ → ℤ),
      (∀ i, turnId i (step (x i) t) = tid)
      ∧ ∀ tier : Tier, ¬ balancedAtTier tier halfEdge x t := by
  obtain ⟨x, t, tid, step, turnId, halfEdge, hagree, hbal⟩ := Hyperedge.binding_is_proper
  exact ⟨x, t, tid, step, turnId, halfEdge, hagree, fun _ h => hbal h⟩

/-! ## §4. Keystones — decided on the two-incidence transfer of
`Kernel/TurnBalancedLimit.lean` (`stepId`/`zeroRead`/`stateHalf`, tuple `![5, -5]`). -/

/-- A `causal`/`bft` transfer commits at `bft`. -/
example : commitTier ![Tier.causal, Tier.bft] = .bft := by decide

/-- A transfer between two tier-1 cells commits at `causal` — coordination-free. -/
example : commitTier ![Tier.causal, Tier.causal] = .causal := by decide

/-- Teeth for `commitTier_eq_causal_iff`: one `bft` cell in the footprint and the
turn is NOT coordination-free. -/
example : ¬ commitTier ![Tier.causal, Tier.bft] = .causal := by decide

/-- The join is attained by leg `1` of the transfer. -/
example : commitTier ![Tier.causal, Tier.bft] = ![Tier.causal, Tier.bft] 1 := by decide

/-- The transfer's apex is `0`: every leg reads `zeroRead`, so the cone condition at
leg `0` pins the (chosen) apex. -/
theorem transfer_tid : transferBalanced.toHyperedge.tid = 0 :=
  (transferBalanced.toHyperedge.agree 0).symm

/-- The transfer's verdict at tier `bft` is its `balanced` field … -/
example : conservedAtTier .bft transferBalanced.toHyperedge :=
  transferBalanced.toHyperedge.balanced

/-- … and at tier `causal`, the SAME term: the tier is not in the proof. -/
example : conservedAtTier .causal transferBalanced.toHyperedge :=
  transferBalanced.toHyperedge.balanced

/-- The two verdicts are the same proposition (not merely both true). -/
example : conservedAtTier .bft transferBalanced.toHyperedge
    = conservedAtTier .causal transferBalanced.toHyperedge :=
  conservation_tier_independent .bft .causal transferBalanced.toHyperedge

/-- The data-level verdict on the transfer tuple, at yet another tier, is the equalizer
membership `TurnBalancedLimit` already built (`(+5) + (−5) = 0`). -/
example : balancedAtTier .constitutional stateHalf transferTuple 0 := transferBalanced.2

/-- Teeth at the SAME instance: the lopsided tuple `![1, 1]` (in the agreement limit,
`lopPoint`) sums to `2` and is refused at every tier. -/
theorem lop_refused_at_every_tier (tier : Tier) : ¬ balancedAtTier tier stateHalf lopTuple 0 := by
  simp [balancedAtTier, stateHalf, lopTuple, Fin.sum_univ_two]

example : ¬ balancedAtTier .causal stateHalf lopTuple 0 := lop_refused_at_every_tier .causal
example : ¬ balancedAtTier .bft stateHalf lopTuple 0 := lop_refused_at_every_tier .bft

/-! ### The join rule FIRES on the built transfer.

The rule runs over apex ids `ℤ`: apex `z` is committed when `0 ≤ z`, canonical when
`-1 ≤ z`. The transfer's apex is `0` (`transfer_tid`), so the rule at the join `bft`
of a `causal`/`bft` transfer commits it and all three conjuncts are obtained. -/

/-- A concrete rule over apex ids `ℤ` at a given tier. -/
def apexRule (t : Tier) : FinalityRule ℤ where
  tier := t
  config := ⟨3, 1, Config.halfQuorum 3 1⟩
  committed z := 0 ≤ z
  canonical z := -1 ≤ z
  commit_canonical _ h := le_trans (by decide) h

/-- Satisfiable: domination, apex canonicity, and leg canonicity for the transfer at
the join `bft`. -/
example :
    (∀ i, ![Tier.causal, Tier.bft] i ≤ (apexRule .bft).tier)
      ∧ (apexRule .bft).canonical transferBalanced.toHyperedge.tid
      ∧ ∀ i, (apexRule .bft).canonical
          (zeroRead i (stepId (transferBalanced.toHyperedge.x i) transferBalanced.toHyperedge.t)) :=
  hyperedge_commit_at_join transferBalanced.toHyperedge ![Tier.causal, Tier.bft] (apexRule .bft)
    (by decide) (le_of_eq transfer_tid.symm)

/-- Teeth: the rule's `committed` is a genuine threshold — apex `-1` is not committed. -/
example : ¬ (apexRule .bft).committed (-1) := show ¬ ((0 : ℤ) ≤ -1) by decide

/-- Teeth: the rule at the WRONG tier (`causal`, below the join) is not pinned to the
join — `hrule` is what ties the rule to the turn's commit tier. -/
example : ¬ (apexRule .causal).tier = commitTier ![Tier.causal, Tier.bft] := by decide

/-! ## §5. Axiom pins.

`conservation_tier_independent` is `rfl`, yet its pin is not empty: `#print axioms`
walks the statement's TYPE, and the aggregate is a `Finset.sum` (`Quot`-quotiented).
Every footprint here is within `{propext, Classical.choice, Quot.sound}`. -/

/-- info: 'Minidregg.Kernel.HyperedgeTier.commitTier_eq_causal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms commitTier_eq_causal_iff

/-- info: 'Minidregg.Kernel.HyperedgeTier.hyperedge_commit_at_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hyperedge_commit_at_join

/-- info: 'Minidregg.Kernel.HyperedgeTier.conservation_tier_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms conservation_tier_independent

/-- info: 'Minidregg.Kernel.HyperedgeTier.binding_tooth_tier_blind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms binding_tooth_tier_blind

end Minidregg.Kernel.HyperedgeTier
