/-
# `Kernel/HyperedgeKnowledge.lean` — the epistemic reading of `Hyperedge.legs_agree`.

`Kernel/Turn.lean` proves pairwise agreement of a hyperedge's legs as a THEOREM
(`legs_agree`, from the one apex). This file says what that agreement *means*
epistemically, in the frame of `Theory/EpistemicConsensus.lean`: the legs are the
agents, a world is an assignment of an observed apex id to every leg, leg `i` can tell
two worlds apart exactly when its own reading differs (`obsFrame`), and the apex is the
proposition "every honest leg reads `tid`" (`apexKnown`). Then:

* `agreement_is_distributed_knowledge` — for ANY hyperedge and ANY faulty set, the apex
  is DISTRIBUTED KNOWLEDGE among the honest legs (`H.agree` is exactly the premise the
  `D_B` clause consumes). `legs_agree_is_distributed_knowledge` routes the same fact
  literally through `legs_agree` from an arbitrary reference leg, honest or not.
* `distKnows_apex_iff_honest_agree` — the characterization: distributed knowledge of an
  apex among the honest legs is exactly honest agreement on it.
* `fork_has_no_distributed_apex` — two honest legs reading different ids is precisely
  the absence of ANY distributed apex. A fork is where the hyperedge is not
  (`splitTuple_no_hyperedge`: the forking tuple underlies no `Hyperedge`).

Ported from breadstuffs `Dregg2/Apps/SheafHyperedge.lean` (`obsFrame`, `apexKnown`, the
bridge and the fork), over minidregg's `Hyperedge` with
`legObs H i := turnId i (step (H.x i) H.t)`. Differences: the ancestor's frame had no
`indist_refl` field (here it is `rfl`); the ancestor lived at `Type 0`, this is
universe-polymorphic; `distKnows_apex_iff_honest_agree` and `splitTuple_no_hyperedge`
are new. No extra hypothesis (such as an honest leg existing) is needed for the bridge —
when no leg is honest, `apexKnown` is vacuous and the theorem says nothing, which is
why the fork tooth is stated with two explicitly honest legs.

Residual: `[HYPEREDGE-operational]` — that a live commit PRODUCES this hyperedge (the
operational half; breadstuffs `Spec/Choreography.lean` OPEN) is not here.
-/
import Theory.EpistemicConsensus
import Kernel.Turn
import Kernel.TurnLimit

namespace Minidregg.Kernel.HyperedgeKnowledge

open Minidregg.Theory.EpistemicConsensus

universe uCarrier uTurn uTurnId uBal v

/-! ### The observation frame of a leg-observation family. -/

section Observation

variable {ι : Type v} {TurnId : Type uTurnId}

/-- **`obsFrame legObs Faulty`** — worlds are assignments `ι → TurnId` of an observed
apex id to every leg; the actual world is what the legs really read; leg `i` confuses
two worlds iff its own component agrees. -/
def obsFrame (legObs : ι → TurnId) (Faulty : ι → Prop) : Frame (ι → TurnId) ι where
  actual := legObs
  Indist := fun i a b => a i = b i
  indist_refl := fun _ _ => rfl
  Faulty := Faulty

/-- **`apexKnown Faulty tid`** — the apex as a proposition: every honest leg reads
`tid`. Restricting to honest legs is what makes it knowable — a faulty leg's component
is unconstrained in every world the honest legs confuse with the actual one. -/
def apexKnown (Faulty : ι → Prop) (tid : TurnId) : Prop' (ι → TurnId) :=
  fun w => ∀ i, ¬ Faulty i → w i = tid

/-- The general bridge: honest agreement on `tid` gives distributed knowledge of it. -/
theorem obs_agreement_is_distributed_knowledge
    (legObs : ι → TurnId) (Faulty : ι → Prop) (tid : TurnId)
    (hagree : ∀ i, ¬ Faulty i → legObs i = tid) :
    (obsFrame legObs Faulty).DistKnows (obsFrame legObs Faulty).Honest
      (apexKnown Faulty tid) (obsFrame legObs Faulty).actual :=
  fun _ hconf j hj => (hconf j hj).trans (hagree j hj)

/-- The converse engine: distributed knowledge of an apex forces every honest leg to
have read it (evaluate at the actual world, which every leg confuses with itself). -/
theorem distributed_apex_forces_agreement
    (legObs : ι → TurnId) (Faulty : ι → Prop) (tid : TurnId)
    (hdk : (obsFrame legObs Faulty).DistKnows (obsFrame legObs Faulty).Honest
            (apexKnown Faulty tid) (obsFrame legObs Faulty).actual) :
    ∀ i, ¬ Faulty i → legObs i = tid :=
  fun i hi => hdk (obsFrame legObs Faulty).actual (fun _ _ => rfl) i hi

/-- **Distributed knowledge of an apex among the honest legs IS honest agreement on
it.** -/
theorem distKnows_apex_iff_honest_agree
    (legObs : ι → TurnId) (Faulty : ι → Prop) (tid : TurnId) :
    (obsFrame legObs Faulty).DistKnows (obsFrame legObs Faulty).Honest
        (apexKnown Faulty tid) (obsFrame legObs Faulty).actual
      ↔ ∀ i, ¬ Faulty i → legObs i = tid :=
  ⟨distributed_apex_forces_agreement legObs Faulty tid,
   obs_agreement_is_distributed_knowledge legObs Faulty tid⟩

/-- **The fork has no distributed apex.** Two honest legs reading different ids: no
`tid` is distributed knowledge of the honest legs. -/
theorem fork_has_no_distributed_apex
    (legObs : ι → TurnId) (Faulty : ι → Prop)
    (i j : ι) (hi : ¬ Faulty i) (hj : ¬ Faulty j) (hfork : legObs i ≠ legObs j) :
    ¬ ∃ tid : TurnId, (obsFrame legObs Faulty).DistKnows (obsFrame legObs Faulty).Honest
        (apexKnown Faulty tid) (obsFrame legObs Faulty).actual := by
  rintro ⟨tid, hdk⟩
  have hagree := distributed_apex_forces_agreement legObs Faulty tid hdk
  exact hfork ((hagree i hi).trans (hagree j hj).symm)

end Observation

/-! ### At a `Hyperedge`: the cone condition is the distributed apex. -/

section AtHyperedge

variable {ι : Type v} [Fintype ι]
variable {Carrier : Type uCarrier} {Turn : Type uTurn}
variable {TurnId : Type uTurnId} {Bal : Type uBal}
variable [AddCommMonoid Bal] [DecidableEq TurnId]
variable {step : Carrier → Turn → Carrier}
variable {turnId : ι → Carrier → TurnId} {halfEdge : ι → Carrier → Turn → Bal}

/-- What leg `i` of the hyperedge reads after the turn fires. -/
def legObs (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge) : ι → TurnId :=
  fun i => turnId i (step (H.x i) H.t)

/-- **THE BRIDGE.** For any hyperedge and any faulty set, the apex `H.tid` is
distributed knowledge among the honest legs: `H.agree` is the premise. -/
theorem agreement_is_distributed_knowledge
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge) (Faulty : ι → Prop) :
    (obsFrame (legObs H) Faulty).DistKnows (obsFrame (legObs H) Faulty).Honest
      (apexKnown Faulty H.tid) (obsFrame (legObs H) Faulty).actual :=
  obs_agreement_is_distributed_knowledge (legObs H) Faulty H.tid (fun i _ => H.agree i)

/-- The same, routed literally through `Hyperedge.legs_agree` from a reference leg `i₀`
that need not be honest — the apex forces every leg, so any incidence anchors the pool. -/
theorem legs_agree_is_distributed_knowledge
    (H : Hyperedge ι Carrier Turn TurnId Bal step turnId halfEdge) (Faulty : ι → Prop)
    (i₀ : ι) :
    (obsFrame (legObs H) Faulty).DistKnows (obsFrame (legObs H) Faulty).Honest
      (apexKnown Faulty H.tid) (obsFrame (legObs H) Faulty).actual :=
  fun _ hconf j hj => (hconf j hj).trans ((H.legs_agree j i₀).trans (H.agree i₀))

end AtHyperedge

/-! ### Keystones at `ι = Fin 2`, everything `ℤ` (reusing `Kernel/TurnLimit.lean`'s
`stepId`/`zeroRead`/`readId`/`splitTuple`). -/

section Keystones

/-- The transfer's half-edges: `+1` at leg `0`, `−1` at leg `1`. -/
def swapHalf : Fin 2 → ℤ → ℤ → ℤ := fun i _ _ => if i = 0 then 1 else -1

/-- The agreeing hyperedge: both legs read apex `0` under `zeroRead`, balanced. -/
def zeroEdge : Hyperedge (Fin 2) ℤ ℤ ℤ ℤ stepId zeroRead swapHalf where
  x := fun _ => 0
  t := 0
  tid := 0
  agree := fun _ => rfl
  balanced := by rw [Fin.sum_univ_two]; decide

/-- No leg is faulty. -/
def noFaults : Fin 2 → Prop := fun _ => False

/-- Leg `1` is faulty. -/
def oneFaulty : Fin 2 → Prop := fun i => i = 1

/-- satisfiable, computed: both legs of `zeroEdge` read `0`. -/
theorem zeroEdge_legs_read_zero : ∀ i : Fin 2, legObs zeroEdge i = 0 := by decide

/-- satisfiable: apex `0` is distributed knowledge of `zeroEdge`'s legs. -/
theorem zeroEdge_apex_distKnown :
    (obsFrame (legObs zeroEdge) noFaults).DistKnows (obsFrame (legObs zeroEdge) noFaults).Honest
      (apexKnown noFaults 0) (obsFrame (legObs zeroEdge) noFaults).actual :=
  agreement_is_distributed_knowledge zeroEdge noFaults

/-- … and still is when leg `1` is faulty — the honest leg `0` alone carries it. -/
theorem zeroEdge_apex_distKnown_oneFaulty :
    (obsFrame (legObs zeroEdge) oneFaulty).DistKnows (obsFrame (legObs zeroEdge) oneFaulty).Honest
      (apexKnown oneFaulty 0) (obsFrame (legObs zeroEdge) oneFaulty).actual :=
  agreement_is_distributed_knowledge zeroEdge oneFaulty

/-- The forking observation: `splitTuple` under `readId` — leg `0` reads `0`, leg `1`
reads `1`. -/
def forkObs : Fin 2 → ℤ := fun i => readId i (stepId (splitTuple i) 0)

/-- teeth, computed: the legs genuinely disagree. -/
theorem forkObs_disagree : forkObs 0 ≠ forkObs 1 := by decide

/-- teeth: the fork has NO distributed apex. -/
theorem forkObs_no_apex :
    ¬ ∃ tid : ℤ, (obsFrame forkObs noFaults).DistKnows (obsFrame forkObs noFaults).Honest
        (apexKnown noFaults tid) (obsFrame forkObs noFaults).actual :=
  fork_has_no_distributed_apex forkObs noFaults 0 1 (fun h => h) (fun h => h) forkObs_disagree

/-- The fork is where the hyperedge is not: no `Hyperedge` under `readId` has
`splitTuple` as its tuple at turn `0` (`Kernel/TurnLimit.lean`'s `no_common_apex`). -/
theorem splitTuple_no_hyperedge (halfEdge : Fin 2 → ℤ → ℤ → ℤ) :
    ¬ ∃ H : Hyperedge (Fin 2) ℤ ℤ ℤ ℤ stepId readId halfEdge, H.x = splitTuple ∧ H.t = 0 := by
  rintro ⟨H, hx, ht⟩
  refine no_common_apex ⟨H.tid, fun i => ?_⟩
  have h := H.agree i
  rwa [hx, ht] at h

end Keystones

/-! ### Axiom pins. -/

/-- info: 'Minidregg.Kernel.HyperedgeKnowledge.agreement_is_distributed_knowledge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms agreement_is_distributed_knowledge

/-- info: 'Minidregg.Kernel.HyperedgeKnowledge.legs_agree_is_distributed_knowledge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms legs_agree_is_distributed_knowledge

/-- info: 'Minidregg.Kernel.HyperedgeKnowledge.distKnows_apex_iff_honest_agree' does not depend on any axioms -/
#guard_msgs in #print axioms distKnows_apex_iff_honest_agree

/-- info: 'Minidregg.Kernel.HyperedgeKnowledge.fork_has_no_distributed_apex' does not depend on any axioms -/
#guard_msgs in #print axioms fork_has_no_distributed_apex

/-- info: 'Minidregg.Kernel.HyperedgeKnowledge.zeroEdge_apex_distKnown' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms zeroEdge_apex_distKnown

/-- info: 'Minidregg.Kernel.HyperedgeKnowledge.forkObs_no_apex' depends on axioms: [propext] -/
#guard_msgs in #print axioms forkObs_no_apex

/-- info: 'Minidregg.Kernel.HyperedgeKnowledge.splitTuple_no_hyperedge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms splitTuple_no_hyperedge

end Minidregg.Kernel.HyperedgeKnowledge
