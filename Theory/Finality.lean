/-
# Theory.Finality — the finality lattice (Law 2, ordering)

paper2 §2.4: *when is a fact final?* Canonicity — which valid history is THE history
— is a per-cell pluggable tier layered over ONE Merkle-CRDT DAG. This module is the
ordering logic of the constitution: the four-tier ladder `Tier` as a bounded linear
order, the finality-rule plugin `FinalityRule`, the per-group quorum configuration
(`Config` / `Selector.tau_unified`), and the three ordering laws —

  * **commit at the join**: a turn writing cells of several tiers commits at the
    lattice join of those tiers, and canonicity is granted only by the join-tier
    rule's commit (`commit_at_join_of_tiers`);
  * **no downgrade**: along the finalization-event relation `TierStep` a value's
    tier never weakens (`reachable_no_downgrade`), with the tooth that the step
    `bft → causal` is not admissible and not reachable (`downgrade_not_a_step`,
    `downgrade_unreachable`);
  * **tier 1 requires I-confluence**: a cell may run the causal rule only when its
    invariant is confluent — the static classifier is what guarantees it
    (`tier1_requires_iconfluent`, over `Theory.Confluence.IConfluent`).

Ported from breadstuffs `metatheory/Dregg2/Finality.lean` (`Dregg2.Finality`) with
the following re-expressions:

  * the cross-tier rule IS the lattice join — `⊔`/`max` of the `LinearOrder`, no
    `crossTierJoin` synonym; `commit_at_join_of_tiers` takes a `Fintype`-indexed
    family and `Finset.univ.sup` instead of `List.foldr … head!` (the `ts ≠ []`
    hypothesis disappears with `OrderBot`: the empty family joins to `⊥ = causal`);
  * the ancestor's `Execution.System`/`Execution.Run` no-downgrade form becomes
    `Relation.ReflTransGen TierStep` — reachability in the finalization relation;
  * the ancestor's type synonyms `History := Type u`, `Committed H := H → Prop`,
    `Canonical H := H → Prop` are inlined (three names for two types);
  * `tier1_requires_iconfluent` keeps the ancestor's classifier + soundness form but
    lets the classifier range over a SYNTAX `G` with semantics `sem : G → Invariant S`
    and asks soundness only on the well-formed syntax `Γ` (the ancestor's statement is
    `G := Invariant S`, `sem := id`, `Γ := Set.univ`) — so the static `Guard`
    classifier of `Theory.Confluence` can be plugged in, and its teeth built;
  * `conservedAtTier` / `conservation_tier_independent` are stated in
    `Kernel/HyperedgeTier.lean` over the kernel's own `move`/`totalAsset` spine
    (there is no `Core.Conservation` here, and `Theory/` cannot see the kernel).

No `FinalityRule` field is dropped: `tier`, `config`, `committed`, `canonical`,
`commit_canonical` are the ancestor's five.

Residuals (prose, not `Prop := True`):

  [FINALITY-blocklace]     tier-3 τ-BFT (blocklace waves, per-wave leader, 3-step
                           ratification, the node's computed tau rule — breadstuffs
                           `Distributed/BlocklaceFinality.lean`) is not modeled; the
                           rule's `committed` stays an abstract predicate.
  [FINALITY-quorum-config] the per-group quorum configuration IS ported (`Config`,
                           `Config.halfQuorum`, `Group`, `Selector`,
                           `Selector.tau_unified`, `tau_unified_tier`); what is NOT
                           ported is any theorem tying `threshold` to safety — the
                           ancestor had none either (`Consensus` carried it).
  [FINALITY-liveness]      `PostGSTProgress` (tier-3/4 resume after GST) is a
                           separate carrier lane.
-/
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Theory.Confluence

namespace Minidregg.Theory.Finality

set_option autoImplicit false

universe u v

/-! ## §1. The ladder. -/

/-- **The pluggable finality tier** (paper2 §2.4 table). Four canonicity mechanisms
over the one CvRDT DAG; strength increases with the constructor ordinal (`rank`). -/
inductive Tier where
  /-- **Tier 1 — causal-only / CRDT.** n ≥ 1, no synchrony, never blocks under
  partition. Eligible ONLY for I-confluent state (`tier1_requires_iconfluent`). -/
  | causal
  /-- **Tier 2 — ack-threshold.** k-of-m acks, leaderless; no synchrony for safety;
  under partition it degrades to tier 1 rather than stalling. -/
  | ackThreshold
  /-- **Tier 3 — Cordial-Miners τ-BFT.** Blocklace waves + per-wave leader + 3-step
  ratification; committee n ≥ 3; GST; stalls in partition, resumes after GST. -/
  | bft
  /-- **Tier 4 — constitutional.** τ-BFT + self-amending constitution (P, σ, Δ);
  PKI; partial synchrony; stalls with a deadline. -/
  | constitutional
  deriving DecidableEq, Repr, Inhabited

/-- Tier strength as an ordinal: the position on the ladder. -/
def Tier.rank : Tier → ℕ
  | .causal         => 1
  | .ackThreshold   => 2
  | .bft            => 3
  | .constitutional => 4

/-- Distinct tiers have distinct strength — the rank order is a genuine total order,
not a preorder collapsing tiers. -/
theorem Tier.rank_injective : Function.Injective Tier.rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [Tier.rank]

/-- **`Tier` is a linear order** under `rank`: `causal < ackThreshold < bft <
constitutional`. Its `max` (= `⊔`) is the cross-tier commit rule. -/
instance : LinearOrder Tier := LinearOrder.lift' Tier.rank Tier.rank_injective

/-- The causal tier is the weakest: it lies below every tier. -/
theorem Tier.causal_le (t : Tier) : Tier.causal ≤ t := by
  cases t <;> decide

/-- `causal` is the bottom of the ladder, so `Finset.sup` over families of tiers is
available (the empty family of written cells commits at tier 1). -/
instance : OrderBot Tier where
  bot := .causal
  bot_le := Tier.causal_le

@[simp] theorem Tier.bot_eq_causal : (⊥ : Tier) = Tier.causal := rfl

/-! ### Keystones of the ladder — decided, not asserted. -/

example : Tier.causal < Tier.bft := by decide
example : Tier.ackThreshold < Tier.constitutional := by decide
example : ¬ Tier.bft ≤ Tier.ackThreshold := by decide
/-- The cross-tier rule is the lattice join: the stronger requirement dominates. -/
example : max Tier.ackThreshold Tier.bft = Tier.bft := by decide
example : Tier.ackThreshold ⊔ Tier.bft = Tier.bft := by decide
/-- The join of a finite set of written-cell tiers. -/
example : ({Tier.causal, Tier.bft} : Finset Tier).sup id = Tier.bft := by decide
/-- The join of a `Fin 2`-indexed family (the transfer shape). -/
example : Finset.univ.sup ![Tier.causal, Tier.bft] = Tier.bft := by decide
example : Finset.univ.sup ![Tier.causal, Tier.causal] = Tier.causal := by decide

/-! ## §2. The finality-rule plugin and the per-group quorum configuration. -/

/-- **Per reference-group consensus config.** The `½(n+f)` quorum the naive design
hardcodes is lifted here: `n` participants, `f` tolerated faults, `threshold` the
acks/votes a commit needs. `n = 1` is permitted (the "fixed σ-quorum forbidding
n = 1" globalism seam is rejected). -/
structure Config where
  /-- Number of participants in the reference group. -/
  n : ℕ
  /-- Number of Byzantine / crash faults tolerated. -/
  f : ℕ
  /-- Commit threshold (acks or BFT votes) — config, not law. -/
  threshold : ℕ
  deriving DecidableEq, Repr

/-- The standard lifted quorum: strict majority of the fault-adjusted set. A helper
to build a `Config`; groups MAY override it. -/
def Config.halfQuorum (n f : ℕ) : ℕ := (n + f) / 2 + 1

example : Config.halfQuorum 3 1 = 3 := by decide
example : Config.halfQuorum 1 0 = 1 := by decide

/-- **A finality rule (the §2.4 plugin).** Selects a `tier` and supplies the predicate
that decides canonicity at that tier over the history type `H`: tier 1 admits any
causal extension; tier 2 needs the ack threshold; tiers 3/4 need a τ-BFT quorum.
`commit_canonical` is the rule's soundness obligation — a committed history is the
canonical one — carried as a FIELD, so a `FinalityRule` value is by definition a rule
whose commits are canonical. -/
structure FinalityRule (H : Type u) where
  /-- Which tier of the ladder this rule realizes. -/
  tier : Tier
  /-- The group/threshold configuration the quorum is read from. -/
  config : Config
  /-- The tier's commit predicate (the quorum kept abstract). -/
  committed : H → Prop
  /-- The canonicity selector the rule installs. -/
  canonical : H → Prop
  /-- Commit soundness: once the tier's quorum has committed `h`, `h` is canonical. -/
  commit_canonical : ∀ h, committed h → canonical h

/-- **Reference group** — the participants `τ_unified` runs per group; its identity
selects which rule applies. -/
structure Group where
  /-- Opaque group identity (a committee / cell-set hash in the deployed system). -/
  id : ℕ
  deriving DecidableEq, Repr

/-- **`τ_unified(B, G, C)` — the unified finality selector.** A per-group tier
assignment plus a rule builder under the config; the `½(n+f)` constant enters only
through `config` / `ruleOf`. -/
structure Selector (H : Type u) where
  /-- Which tier each reference group is assigned. -/
  groupTier : Group → Tier
  /-- The config in force for the selection. -/
  config : Config
  /-- Build the concrete rule realizing a tier under the config. -/
  ruleOf : Tier → FinalityRule H

/-- The selector body: `τ_unified` resolves group `G` to the rule for `G`'s tier. -/
def Selector.tau_unified {H : Type u} (s : Selector H) (G : Group) : FinalityRule H :=
  s.ruleOf (s.groupTier G)

/-- A well-formed selector (its `ruleOf` preserves the tier label it is asked for)
runs group `G` at exactly `G`'s assigned tier. -/
theorem tau_unified_tier {H : Type u} (s : Selector H) (G : Group)
    (hwf : ∀ t, (s.ruleOf t).tier = t) :
    (s.tau_unified G).tier = s.groupTier G :=
  hwf (s.groupTier G)

/-! ## §3. Commit at the join of the written cells' tiers. -/

/-- **A turn commits at the join of its written cells' tiers; effects are held until
the join-tier rule commits** (paper2 §2.4 cross-tier rule). For a `Fintype`-indexed
family `tierOf` (incidence `i` writes a cell of tier `tierOf i`) and a rule installed
at the join `Finset.univ.sup tierOf`: the join dominates every written cell's tier,
and the turn's canonicity is granted only through THAT rule's commit. -/
theorem commit_at_join_of_tiers {H : Type u} {ι : Type v} [Fintype ι]
    (tierOf : ι → Tier)
    (rule : FinalityRule H) (hrule : rule.tier = Finset.univ.sup tierOf)
    (h : H) (hcommit : rule.committed h) :
    (∀ i, tierOf i ≤ rule.tier) ∧ rule.canonical h :=
  ⟨fun i => hrule ▸ Finset.le_sup (Finset.mem_univ i), rule.commit_canonical h hcommit⟩

/-- The join of a NONEMPTY family of tiers is attained by one of its members — the
commit tier is always the tier of some cell the turn actually writes, never an
invented level. (`Finset.exists_mem_eq_sup` on the linear order.) -/
theorem join_attained {ι : Type v} [Fintype ι] [Nonempty ι] (tierOf : ι → Tier) :
    ∃ i, Finset.univ.sup tierOf = tierOf i := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty tierOf
  exact ⟨i, hi⟩

/-! ### Keystone — the join rule FIRES on a rule whose `committed` is genuinely
partial (`H := ℕ`, committed `n` iff `2 ≤ n`), and REFUSES below the threshold. -/

/-- A concrete rule at a given tier over histories `ℕ`: history `n` is committed
when `2 ≤ n` and canonical when `1 ≤ n`. -/
def demoRule (t : Tier) : FinalityRule ℕ where
  tier := t
  config := ⟨3, 1, Config.halfQuorum 3 1⟩
  committed n := 2 ≤ n
  canonical n := 1 ≤ n
  commit_canonical _ h := Nat.le_trans (by decide) h

/-- Satisfiable: at the join `bft` of a `causal`/`bft` transfer, history `2` is
committed, so both conjuncts are obtained — every leg is dominated and `2` is
canonical. -/
example :
    (∀ i, ![Tier.causal, Tier.bft] i ≤ (demoRule .bft).tier)
      ∧ (demoRule .bft).canonical 2 :=
  commit_at_join_of_tiers ![Tier.causal, Tier.bft] (demoRule .bft) (by decide) 2
    (show 2 ≤ 2 by decide)

/-- Teeth: history `1` is NOT committed by the rule — the second conjunct is not
obtainable through `commit_at_join_of_tiers` for it (the rule's `committed` is a
genuine threshold, not `True`). -/
example : ¬ (demoRule .bft).committed 1 := show ¬ (2 ≤ 1) by decide

/-- Teeth on the first conjunct: a rule installed BELOW the join does not dominate
every leg — `causal` is not ≥ the `bft` leg. -/
example : ¬ (∀ i, ![Tier.causal, Tier.bft] i ≤ (demoRule .causal).tier) := by decide

/-! ## §4. No downgrade — the finalization relation. -/

/-- **The finalization-event step.** A configuration is a value's currently-finalized
tier; a (re-)finalization event is admissible only when it does not weaken the tier.
This replaces the ancestor's `finalitySystem : Execution.System` (`Step t t' := t ≤ t'`);
reachability is `Relation.ReflTransGen TierStep`. -/
def TierStep (a b : Tier) : Prop := a ≤ b

instance : DecidableRel TierStep := fun a b => inferInstanceAs (Decidable (a ≤ b))

/-- **No downgrade** (paper2 §2.4): along any run of finalization events, the final
tier is no weaker than the initial one (replaces the ancestor's `no_downgrade` over
`Execution.Run finalitySystem`). -/
theorem reachable_no_downgrade {t₀ t : Tier} (hrun : Relation.ReflTransGen TierStep t₀ t) :
    t₀ ≤ t := by
  induction hrun with
  | refl => exact le_rfl
  | tail _ hstep ih => exact le_trans ih hstep

/-- The tooth, one step: weakening `bft` to `causal` is not an admissible event. -/
theorem downgrade_not_a_step : ¬ TierStep .bft .causal := by decide

/-- The tooth, any run: no sequence of admissible events reaches `causal` from `bft`. -/
theorem downgrade_unreachable : ¬ Relation.ReflTransGen TierStep .bft .causal :=
  fun hrun => absurd (reachable_no_downgrade hrun) (by decide)

/-- Satisfiable: strengthening is reachable — `causal` climbs to `constitutional` in
two admissible events. -/
example : Relation.ReflTransGen TierStep .causal .constitutional :=
  .tail (.single (by decide : TierStep .causal .bft)) (by decide : TierStep .bft .constitutional)

/-! ## §5. Tier 1 requires I-confluence — the link to `Theory.Confluence`.

A cell may run the `causal` rule ONLY if its invariant is `IConfluent`. An arbitrary
invariant is not confluent for free: the static CLASSIFIER is what guarantees it, so
the law is stated parametrically in the classifier and its soundness. The classifier
ranges over a syntax `G` with semantics `sem : G → Invariant S`, and its soundness is
asked only on the well-formed syntax `Γ` — the guards whose `monotone` claims are
discharged. -/

/-- **Tier 1 requires I-confluence.** If a rule at `causal` is what the classifier
assigned to `g`, and the classifier is sound over `Γ ∋ g`, then `g`'s invariant is
I-confluent — `Theory.Confluence`'s coordination-free verdict, read from the finality
side. -/
theorem tier1_requires_iconfluent {S : Type u} [SemilatticeSup S] {G : Type v}
    (sem : G → Confluence.Invariant S) (Γ : Set G) (g : G) (hg : g ∈ Γ)
    (rule : FinalityRule S) (hcausal : rule.tier = Tier.causal)
    (classify : G → Tier) (hmatch : rule.tier = classify g)
    (hsound : ∀ g' ∈ Γ, classify g' = Tier.causal → Confluence.IConfluent (sem g')) :
    Confluence.IConfluent (sem g) :=
  hsound g hg (hmatch.symm.trans hcausal)

/-- **The static guard classifier**: `monotone` guards run at tier 1; `bounded` and
`relational` guards are sent to τ-BFT. -/
def guardTier {S : Type u} : Confluence.Guard S → Tier
  | .monotone _ _ => .causal
  | .bounded _ _  => .bft
  | .relational _ => .bft

/-- **Well-formed guards**: every `monotone proj c` claim is true of `proj`. The
`Guard.monotone` constructor is a CLAIM; this is the discharged claim the classifier
is entitled to trust. -/
def WellFormed {S : Type u} [Preorder S] (g : Confluence.Guard S) : Prop :=
  ∀ proj c, g = .monotone proj c → Monotone proj

/-- `guardTier` is sound over well-formed guards — `monotone_free` discharges every
tier-1 verdict it issues. -/
theorem guardTier_sound {S : Type u} [SemilatticeSup S] :
    ∀ g ∈ {g : Confluence.Guard S | WellFormed g},
      guardTier g = Tier.causal → Confluence.IConfluent g.inv := by
  intro g hwf hc
  cases g with
  | monotone proj c => exact Confluence.monotone_free (hwf proj c rfl) c
  | bounded _ _ => simp [guardTier] at hc
  | relational _ => simp [guardTier] at hc

/-- A concrete tier-1 rule over histories `Finset ℕ`: committed iff `0` was written,
canonical iff nonempty. -/
def causalRule : FinalityRule (Finset ℕ) where
  tier := .causal
  config := ⟨1, 0, Config.halfQuorum 1 0⟩
  committed s := 0 ∈ s
  canonical s := s.Nonempty
  commit_canonical _ h := ⟨0, h⟩

/-- Satisfiable: on `Finset ℕ` the floor guard `c ≤ card` is well-formed
(`Finset.card_mono`), `guardTier` assigns it `causal`, and the parametric law fires —
its invariant is I-confluent. -/
theorem card_floor_guard_tier1 (c : ℕ) :
    Confluence.IConfluent (Confluence.Guard.monotone (Finset.card : Finset ℕ → ℕ) c).inv :=
  tier1_requires_iconfluent Confluence.Guard.inv {g | WellFormed g}
    (.monotone Finset.card c)
    (fun _ _ h => by injection h with h₁ _; subst h₁; exact Finset.card_mono)
    causalRule rfl guardTier rfl guardTier_sound

example : guardTier (Confluence.Guard.monotone (Finset.card : Finset ℕ → ℕ) 0) = .causal := rfl
example : ¬ causalRule.committed ∅ := show ¬ (0 ∈ (∅ : Finset ℕ)) by decide

/-- **The naive classifier** — sends BOUNDED guards to tier 1. -/
def naiveTier {S : Type u} : Confluence.Guard S → Tier
  | .bounded _ _ => .causal
  | _ => .bft

/-- Teeth: `naiveTier` is UNSOUND, even restricted to well-formed guards. The ceiling
guard `card ≤ 1` on `Finset ℕ` admits the clashing pair `{0}`, `{1}` (each of card
`1 ≤ 1`, their join `{0, 1}` of card `2`), so `bounded_breaks` refutes the tier-1
verdict `naiveTier` issues for it. -/
theorem naiveTier_unsound :
    ¬ ∀ g ∈ {g : Confluence.Guard (Finset ℕ) | WellFormed g},
        naiveTier g = Tier.causal → Confluence.IConfluent g.inv := by
  intro hsound
  have hwf : WellFormed (Confluence.Guard.bounded (Finset.card : Finset ℕ → ℕ) 1) :=
    fun _ _ h => nomatch h
  exact Confluence.bounded_breaks Finset.card 1 (x := {0}) (y := {1})
    (by decide) (by decide) (by decide) (hsound _ hwf rfl)

/-! ## §6. Axiom pins. -/

/-- info: 'Minidregg.Theory.Finality.commit_at_join_of_tiers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms commit_at_join_of_tiers

/-- info: 'Minidregg.Theory.Finality.reachable_no_downgrade' depends on axioms: [propext] -/
#guard_msgs in #print axioms reachable_no_downgrade

/-- info: 'Minidregg.Theory.Finality.downgrade_unreachable' depends on axioms: [propext] -/
#guard_msgs in #print axioms downgrade_unreachable

/-- info: 'Minidregg.Theory.Finality.tier1_requires_iconfluent' does not depend on any axioms -/
#guard_msgs in #print axioms tier1_requires_iconfluent

/-- info: 'Minidregg.Theory.Finality.guardTier_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms guardTier_sound

/-- info: 'Minidregg.Theory.Finality.naiveTier_unsound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms naiveTier_unsound

end Minidregg.Theory.Finality
