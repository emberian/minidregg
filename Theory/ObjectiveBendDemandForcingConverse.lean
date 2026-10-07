/- The difference is resources only (forcing transparency, part 10).

A kernel checkpoint is the program's own yield normalized: its Plan's cells forced
(`ForcesBy`), their origins settled (`Agree`), the heap collected (`Related`). `Chain` is
any composite of those three relations. Along a chain, read backward (lazy `s`, normalized
`t`):

* `Chain.back`: whatever segment the normalized state commits under some resources (a yield
  whose Plan extracts, a completion that extracts, a divergence, a refusal: `endsWith`), the
  lazy state commits the SAME ending under every resource vector above a threshold (heap and
  stack room, ticks, extraction ticks), with the same output nodes and bytes
  (`EndsAbove`). That is GPT-6's converse, `N(s)⇓_B o ⇒ ∃B'. s⇓_{B'} o' ∧ o≈o'`, with `B` a
  vector and `B'` any vector above the threshold.
* The ends are again related: a yield commits with the lazy yield in a chain with the
  normalized yield (the continuation STATES, not only the Plan), and every response resumes a
  chain to a chain (`Chain.resume`). So `Chain` is preserved segment after segment
  (`Chain.next`), which is what an activity needs.
* `Chain.spins`: if the lazy run never halts (silent divergence), the normalized run commits
  nothing under any resources. Spinning forever is never equated with a visible ending. -/
import Theory.ObjectiveBendDemandForcingBack
import Theory.ObjectiveBendDemandSettleProofs
import Theory.ObjectiveBendDemandForceProofs
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendDemandData
set_option autoImplicit false

/-! ## Settling is a backward simulation -/

theorem settle_exec {s t : State} (agree : Agree s t) : ∀ n, Agree (exec n s) (exec n t) := by
  intro n
  induction n with
  | zero => exact agree
  | succ n ih => rw [exec_succ, exec_succ]; exact ObjectiveBendDemandCollect.agree_stepRaw ih

theorem renameControl_idMap (c : Control) : renameControl id c = c := renameControl_id (f := id) (fun _ _ => rfl)

theorem renameStack_idMap (S : List Frame) : S.map (renameFrame id) = S :=
  renameStack_id (f := id) (fun _ _ _ _ => rfl)

/-- **Settling (origins erased) is a backward simulation**: exact lockstep, identity map. -/
theorem settleSim : BackSim (fun F s t => F = id ∧ Agree s t) (fun _ _ => True) where
  renames h := by
    obtain ⟨rfl, a⟩ := h
    exact ⟨by rw [renameControl_idMap]; exact a.control.symm, by rw [renameStack_idMap]; exact a.stack.symm⟩
  controlIn _ := fun _ _ => trivial
  stackIn _ := fun _ _ _ _ => trivial
  reenter c S h _ _ := by
    obtain ⟨rfl, a⟩ := h
    refine ⟨rfl, Agree.mk' a.heap ?_ ?_⟩
    · exact (renameControl_idMap c).symm
    · exact (renameStack_idMap S).symm
  back h halts := by
    obtain ⟨rfl, a⟩ := h
    have all := settle_exec a
    refine ⟨_, id, ⟨fun j lt => ?_, ?_⟩, ⟨rfl, all _⟩, fun _ _ => ⟨trivial, rfl⟩⟩
    · have := halts.1 j lt; rwa [← (all j).control] at this
    · have := halts.2; rwa [← (all _).control] at this

/-! ## Endings -/

/-- How a segment ends, as what a kernel commits from it. -/
inductive Ending where
  | yielded (plan : Data)
  | finished (result : Data)
  | divergent
  | refused (reason : Refusal)

/-- The segment from `s` under limits `L`, `T` ticks and extraction budget `budget`: its
ending and the state the run stopped in (for a yield, the yielded state), or `none` (out of
ticks or room, or an extraction that did not succeed). -/
def endsWith (L : Limits) (T : Nat) (budget : Budget) (s : State) : Option (Ending × State) :=
  match runBounded L T s with
  | .yielded _ y => match yieldedPlan L budget y with
    | .ok r => some (.yielded r.value, y)
    | .error _ => none
  | .finished _ y => match complete L budget y with
    | .ok r => some (.finished r.value, y)
    | .error _ => none
  | .divergent _ y => some (.divergent, y)
  | .refused reason y => some (.refused reason, y)
  | .suspended _ _ => none

/-- **The ending above a threshold**: under every resource vector at least `(L0, T0, E0)`
(the same output nodes and bytes as `budget`), the segment from `s` ends with `e`, stopping in
`y` (which does not depend on the resources). -/
def EndsAbove (s : State) (budget : Budget) (e : Ending) (y : State) : Prop :=
  ∃ (L0 : Limits) (T0 E0 : Nat), ∀ (L : Limits) (T k : Nat), LimitsLe L0 L → T0 ≤ T →
    endsWith L T ⟨budget.nodes, E0 + k, budget.bytes⟩ s = some (e, y)

/-- **A backward simulation's segment, as endings**: whatever the forced side ends with, the
lazy side ends with above a threshold, stopping in a related state. -/
theorem BackSim.ends {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {s t : State} (rel : R F s t) {L' : Limits} {T' : Nat}
    {budget' : Budget} {e : Ending} {y' : State} (ran : endsWith L' T' budget' t = some (e, y')) :
    ∃ y F', R F' y y' ∧ EndsAbove s budget' e y := by
  unfold endsWith at ran
  have notSusp : ∀ r st, ObjectiveBendDemandMachine.runBounded L' T' t ≠ .suspended r st := by
    intro r st h; rw [h] at ran; cases ran
  obtain ⟨n, n', L1, F1, rel1, eqT, _, lazy⟩ := sim.runBounded rel notSusp
  have ctl := (sim.renames rel1).1
  rw [eqT] at ran
  cases hc : (exec n s).control with
  | yielded p =>
    rw [hc] at ctl
    simp only [ObjectiveBendDemandMachine.runBounded, ctl, renameControl] at ran
    split at ran
    · rename_i r' found
      simp only [Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      obtain ⟨L2, E0, st, F2, _, _, extract⟩ := sim.yieldedPlan rel1 found
      refine ⟨exec n s, F1, rel1, limitsMax L1 L2, n, E0, fun L T k le nle => ?_⟩
      have run := lazy L T (limitsLe_trans (limitsLe_max_left _ _) le) nle
      have ext := extract L k (limitsLe_trans (limitsLe_max_right _ _) le)
      simp [endsWith, run, ObjectiveBendDemandMachine.runBounded, hc, ext]
    · cases ran
  | complete v =>
    rw [hc] at ctl
    simp only [ObjectiveBendDemandMachine.runBounded, ctl, renameControl] at ran
    split at ran
    · rename_i r' found
      simp only [Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨rfl, rfl⟩ := ran
      obtain ⟨L2, E0, st, F2, _, _, extract⟩ := sim.complete rel1 found
      refine ⟨exec n s, F1, rel1, limitsMax L1 L2, n, E0, fun L T k le nle => ?_⟩
      have run := lazy L T (limitsLe_trans (limitsLe_max_left _ _) le) nle
      have ext := extract L k (limitsLe_trans (limitsLe_max_right _ _) le)
      simp [endsWith, run, ObjectiveBendDemandMachine.runBounded, hc, ext]
    · cases ran
  | blackhole a =>
    rw [hc] at ctl
    simp only [ObjectiveBendDemandMachine.runBounded, ctl, renameControl, Option.some.injEq, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    refine ⟨exec n s, F1, rel1, L1, n, 0, fun L T k le nle => ?_⟩
    simp [endsWith, lazy L T le nle, ObjectiveBendDemandMachine.runBounded, hc]
  | refused r =>
    rw [hc] at ctl
    simp only [ObjectiveBendDemandMachine.runBounded, ctl, renameControl, Option.some.injEq, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    refine ⟨exec n s, F1, rel1, L1, n, 0, fun L T k le nle => ?_⟩
    simp [endsWith, lazy L T le nle, ObjectiveBendDemandMachine.runBounded, hc]
  | evaluate _ _ | enter _ | returned _ =>
    rw [hc] at ctl
    simp [ObjectiveBendDemandMachine.runBounded, ctl, renameControl] at ran

/-! ## Chains of normalizations -/

/-- **A chain** from a lazy state to a normalized one: forcing (`ForcesBy`), settling
(`Agree`) and collection (`Related`) steps, composed. A kernel checkpoint is in a chain
with the yield it was made from (`chain_checkpoint`). -/
inductive Chain : State → State → Prop where
  | forces {gap : Nat} {F : Nat → Nat} {s t : State} : ForcesBy gap F s t → Chain s t
  | settles {s t : State} : Agree s t → Chain s t
  | collects {f : Nat → Nat} {D : Nat → Prop} {s t : State} : Related f D s t → Chain s t
  | trans {s m t : State} : Chain s m → Chain m t → Chain s t

/-- **The converse, along a chain: the difference is resources only.** Whatever segment the
normalized state ends with (under some resources), the lazy state ends with the SAME ending
under every resource vector above a threshold, with the same output nodes and bytes, and
stops in a state in a chain with the normalized one's. -/
theorem Chain.back {s t : State} (h : Chain s t) :
    ∀ {L' : Limits} {T' : Nat} {budget' : Budget} {e : Ending} {y' : State},
      endsWith L' T' budget' t = some (e, y') → ∃ y, Chain y y' ∧ EndsAbove s budget' e y := by
  induction h with
  | forces r =>
    intro L' T' budget' e y' ran
    obtain ⟨y, _, rel, above⟩ := (forcesSim _).ends r ran
    exact ⟨y, .forces rel, above⟩
  | settles a =>
    intro L' T' budget' e y' ran
    obtain ⟨y, _, rel, above⟩ := settleSim.ends ⟨rfl, a⟩ ran
    exact ⟨y, .settles rel.2, above⟩
  | @collects f D _ _ r =>
    intro L' T' budget' e y' ran
    obtain ⟨y, _, rel, above⟩ := (relatedSim f D).ends ⟨rfl, r⟩ ran
    exact ⟨y, .collects rel.2, above⟩
  | trans _ _ ih1 ih2 =>
    intro L' T' budget' e y' ran
    obtain ⟨ym, cm, L0, T0, E0, above⟩ := ih2 ran
    obtain ⟨y, cs, above'⟩ := ih1 (above L0 T0 0 (limitsLe_refl _) (Nat.le_refl _))
    exact ⟨y, .trans cs cm, above'⟩

/-- **Every response resumes a chain to a chain** (the response captures no address). -/
theorem Chain.resume {s t : State} (h : Chain s t) (response : Term) :
    ∀ {s0 : State}, ObjectiveBendDemandMachine.resume response s = some s0 →
      ∃ t0, ObjectiveBendDemandMachine.resume response t = some t0 ∧ Chain s0 t0 := by
  induction h with
  | @forces gap F s t r =>
    intro s0 resumed
    obtain ⟨plan, yielded⟩ := resume_requires_yield response s (by rw [resumed]; rfl)
    have ctlT : t.control = .yielded (F plan) := by rw [r.renames.1, yielded]; rfl
    simp only [ObjectiveBendDemandMachine.resume, yielded, Option.some.injEq] at resumed
    subst resumed
    refine ⟨⟨t.heap, .evaluate response [], t.stack⟩, by simp [ObjectiveBendDemandMachine.resume, ctlT], ?_⟩
    have := r.reenter (.evaluate response []) s.stack (fun _ m => by cases m) r.lazyValid.stack
    rw [← r.renames.2] at this
    exact .forces this
  | settles a =>
    intro s0 resumed
    obtain ⟨t0, again, a0⟩ := agree_resume a response resumed
    exact ⟨t0, again, .settles a0⟩
  | collects r =>
    intro s0 resumed
    obtain ⟨t0, again, r0⟩ := related_resume r response resumed
    exact ⟨t0, again, .collects r0⟩
  | trans _ _ ih1 ih2 =>
    intro s0 resumed
    obtain ⟨m0, againM, c1⟩ := ih1 resumed
    obtain ⟨t0, againT, c2⟩ := ih2 againM
    exact ⟨t0, againT, .trans c1 c2⟩

/-- **A checkpoint is in a chain with its yield**: the Plan extraction forces (`yieldedPlan_forces`),
settling erases origins, collection renames. -/
theorem chain_checkpoint {L : Limits} {budget : Budget} {y : State} {r : Result} (valid : AddrValid y)
    (found : ObjectiveBendDemandData.yieldedPlan L budget y = .ok r) : Chain y (checkpoint r.state) := by
  obtain ⟨F, forces⟩ := yieldedPlan_forces valid found y.control valid.control
  obtain ⟨sameControl, sameStack⟩ := yieldedPlanWith_control found
  have eq : (⟨r.state.heap, y.control, y.stack⟩ : State) = r.state := by
    rw [← sameControl, ← sameStack]
  rw [eq] at forces
  exact .trans (.forces forces) (.trans (.settles (agree_settle r.state)) (.collects (related_collect (settle r.state))))

/-- A run that halts is a bounded run that does not suspend, read back. -/
theorem halts_of_endsWith {L : Limits} {T : Nat} {budget : Budget} {s : State} {e : Ending} {y : State}
    (ran : endsWith L T budget s = some (e, y)) : ∃ n, Halts s n := by
  have notSusp : ∀ r st, ObjectiveBendDemandMachine.runBounded L T s ≠ .suspended r st := by
    intro r st h; unfold endsWith at ran; rw [h] at ran; cases ran
  obtain ⟨n, _, halts, _, _⟩ := runBounded_halts L T s notSusp
  exact ⟨n, halts⟩

/-- **Silent divergence is never a visible ending**: if the lazy run never halts, the
normalized run ends no segment, under any resources. -/
theorem Chain.spins {s t : State} (h : Chain s t) (spins : ∀ n, ¬ Halts s n) (L : Limits) (T : Nat)
    (budget : Budget) : endsWith L T budget t = none := by
  cases ran : endsWith L T budget t with
  | none => rfl
  | some ending =>
    obtain ⟨e, y'⟩ := ending
    obtain ⟨y, _, L0, T0, E0, above⟩ := h.back ran
    obtain ⟨n, halts⟩ := halts_of_endsWith (above L0 T0 0 (limitsLe_refl _) (Nat.le_refl _))
    exact absurd halts (spins n)

#assert_axioms settle_exec renameControl_idMap renameStack_idMap settleSim BackSim.ends Chain.back Chain.resume chain_checkpoint
#assert_axioms halts_of_endsWith Chain.spins

/-- **The continuation states after equal next Plans.** If the normalized state yields Plan
`d` and the kernel stores the checkpoint of that yield's extraction, the lazy state yields the
same `d` above a threshold, and the lazy state's OWN yield is in a chain with the stored
checkpoint: so every later response resumes them to a chain again (`Chain.resume`). -/
theorem Chain.next {s t : State} (h : Chain s t) {L' : Limits} {T' : Nat} {budget' : Budget} {d : Data}
    {y' : State} (ran : endsWith L' T' budget' t = some (.yielded d, y')) (valid : AddrValid y') {r' : Result}
    (found : ObjectiveBendDemandData.yieldedPlan L' budget' y' = .ok r') :
    ∃ y, EndsAbove s budget' (.yielded d) y ∧ Chain y (checkpoint r'.state) := by
  obtain ⟨y, c, above⟩ := h.back ran
  exact ⟨y, above, .trans c (chain_checkpoint valid found)⟩

/-- A chain renames the control. -/
theorem Chain.control {s t : State} (h : Chain s t) : ∃ G, t.control = renameControl G s.control := by
  induction h with
  | forces r => exact ⟨_, r.renames.1⟩
  | settles a => exact ⟨id, by rw [renameControl_idMap]; exact a.control.symm⟩
  | collects r => exact ⟨_, r.control⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨G1, e1⟩ := ih1
    obtain ⟨G2, e2⟩ := ih2
    exact ⟨G2 ∘ G1, by rw [e2, e1, renameControl_comp]⟩

/-- **A response the normalized state accepts, the lazy state accepts**, to a chain. -/
theorem Chain.resume_back {s t : State} (h : Chain s t) (response : Term) {t0 : State}
    (resumed : ObjectiveBendDemandMachine.resume response t = some t0) :
    ∃ s0, ObjectiveBendDemandMachine.resume response s = some s0 ∧ Chain s0 t0 := by
  obtain ⟨plan, yielded⟩ := resume_requires_yield response t (by rw [resumed]; rfl)
  obtain ⟨G, ctl⟩ := h.control
  have sYield : ∃ p, s.control = .yielded p := by
    rw [yielded] at ctl
    cases hc : s.control <;> rw [hc] at ctl <;> simp [renameControl] at ctl
    exact ⟨_, rfl⟩
  obtain ⟨p, sp⟩ := sYield
  have sResumed : ObjectiveBendDemandMachine.resume response s = some ⟨s.heap, .evaluate response [], s.stack⟩ := by
    simp [ObjectiveBendDemandMachine.resume, sp]
  obtain ⟨t1, again, chain⟩ := h.resume response sResumed
  rw [resumed] at again
  cases again
  exact ⟨_, sResumed, chain⟩

#assert_axioms Chain.next Chain.control Chain.resume_back

end Minidregg.Theory.ObjectiveBendDemandForcing
