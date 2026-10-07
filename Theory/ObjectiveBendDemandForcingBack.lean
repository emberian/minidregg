/- The converse of forcing transparency: the forced side halts only where the lazy side halts
(forcing transparency, part 9).

`ObjectiveBendDemandForcingExtract.forces_segment` is one direction: along a forcing chain,
whatever the lazy run commits, the forced run commits alike, with heap room for the chain's
gap. This module is the other: whatever the forced run commits, the lazy run commits alike,
given ENOUGH of each resource. The difference between the two runs is resources only.

* `forces_halts_back`: a forced run that halts has a lazy run that halts. The lazy run does
  the work the forced run cached (`pend_switch`: when it enters a pending cell it runs that
  cell's closed demand, which is known to finish); every other transition is lockstep.
* `BackSim`: what a backward simulation needs (a relation that renames controls and stacks,
  re-enters cells, and transfers halting backward). `forcesSim` (forcing chains) and
  `relatedSim` (the collection renaming) are instances.
* `BackSim.forceWith` / `BackSim.materialize` / `BackSim.yieldedPlan` / `BackSim.complete` /
  `BackSim.runBounded` (and `BackSim.ends`, in `ObjectiveBendDemandForcingConverse`): a forced run, forcing, extraction or segment that commits has a lazy one
  that commits alike, to the same Data, under every resource vector above a threshold
  (`LimitsLe L0 L`, ticks `≥ T0`, extraction ticks `≥ E0`), with the SAME output nodes and
  bytes, ending again related (the continuation states, not only the Data). -/
import Theory.ObjectiveBendDemandForcingExtract
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendDemandData
set_option autoImplicit false

/-! ## Halting, backward -/

theorem halts_prepend {s : State} {m k : Nat} (live : ∀ j, j < m → active (exec j s).control = true)
    (h : Halts (exec m s) k) : Halts s (m + k) := by
  refine ⟨fun j lt => ?_, ?_⟩
  · by_cases jm : j < m
    · exact live j jm
    · have := h.1 (j - m) (by omega)
      rwa [← exec_add, show m + (j - m) = j by omega] at this
  · rw [exec_add]; exact h.2

/-- Exactly agreeing runs halt together, read backward. -/
theorem agree_halts_back {f : Nat → Nat} {σ τ : State} (rel : AgreeRel f σ τ) {n : Nat} (halts : Halts τ n) :
    Halts σ n := by
  have all : ∀ j, StateAgree f everywhere (fun _ => False) (exec j σ) (exec j τ) :=
    fun j => agree_exec rel.agree j (fun _ _ _ _ h => h)
  exact ⟨fun j lt => by rw [← (all j).active_eq]; exact halts.1 j lt,
    by rw [← (all n).active_eq]; exact halts.2⟩

/-- **Through a pending demand, backward**: if the forced run halts, the lazy run halts. When
the lazy run enters the pending cell it runs the cell's closed demand (`pend_switch`, which
needs no halting premise: the demand is the one the extraction finished), then agrees
exactly with the forced run, which returned the cached value in one transition. -/
theorem pend_halts_back {e : Pending} {f : Nat → Nat} :
    ∀ (n : Nat) (σ τ : State), PendRel e f σ τ → Halts τ n → ∃ m, Halts σ m := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro σ τ rel halts
  have activeT : active τ.control = active σ.control := by rw [rel.control, active_rename]
  cases act : active σ.control with
  | false => exact ⟨0, fun _ h => by omega, by simp only [exec]; exact act⟩
  | true =>
    have npos : 1 ≤ n := by
      apply Classical.byContradiction; intro h
      have := halts.2; rw [show n = 0 by omega] at this; simp only [exec] at this
      rw [activeT, act] at this; cases this
    have tail : Halts (stepRaw τ) (n - 1) := halts_tail (by rw [show n - 1 + 1 = n by omega]; exact halts)
    by_cases reads : readsAt σ = some e.cell
    · cases ctl : σ.control with
      | enter b =>
        have bEq : b = e.cell := by simp [readsAt, ctl] at reads; exact reads
        subst bEq
        obtain ⟨_, liveLazy, _, _, _, _, agreeNew, _, _⟩ := pend_switch rel ctl
        exact ⟨_, halts_prepend (fun j lt => liveLazy j (by omega)) (agree_halts_back agreeNew tail)⟩
      | returned v =>
        obtain ⟨rest, st⟩ : ∃ rest, σ.stack = .update e.cell :: rest := by
          cases st : σ.stack with
          | nil => simp [readsAt, ctl, st] at reads
          | cons fr rest =>
            cases fr <;> simp [readsAt, ctl, st] at reads
            exact ⟨rest, by rw [reads]⟩
        obtain ⟨_, inactive⟩ := pend_update_read rel ctl st
        exact ⟨1, fun j lt => by rw [show j = 0 by omega]; exact act, by rw [exec_one]; exact inactive⟩
      | _ => simp [readsAt, ctl] at reads
    · obtain ⟨m, hm⟩ := ih (n - 1) (by omega) _ _ (pend_step rel reads) tail
      exact ⟨m + 1, halts_succ act hm⟩

/-- **Along a forcing chain, backward**: a forced run that halts has a lazy run that halts. -/
theorem forces_halts_back {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) :
    ∀ n, Halts τ n → ∃ m, Halts σ m := by
  induction h with
  | pend r _ => exact fun n halts => pend_halts_back n _ _ r halts
  | agree r _ => exact fun n halts => ⟨n, agree_halts_back r halts⟩
  | trans _ _ _ ih1 ih2 =>
    intro n halts
    obtain ⟨k, hk⟩ := ih2 n halts
    exact ih1 k hk

/-- **Backward transfer**: the forced run halting at `n'`, the lazy run halts no earlier, and
the two ends are again in a chain (the forward theorem `forces_transfer` read at the lazy
run's own halting time, which `forces_halts_back` supplies). -/
theorem forces_transfer_back {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ)
    {n' : Nat} (halts : Halts τ n') :
    ∃ n F', n' ≤ n ∧ Halts σ n ∧ Bounded σ τ n n' gap ∧ ForcesBy gap F' (exec n σ) (exec n' τ) ∧
      ∀ a, a < σ.heap.size → F' a = F a := by
  obtain ⟨n, hn⟩ := forces_halts_back h n' halts
  obtain ⟨n'', F', le, haltsT, bounded, rel, ext⟩ := forces_transfer h n hn
  have same := halts_unique haltsT halts
  subst same
  exact ⟨n, F', le, hn, bounded, rel, ext⟩

/-! ## Resource vectors -/

/-- `L` gives at least the room `L0` gives. -/
def LimitsLe (L0 L : Limits) : Prop := L0.heap ≤ L.heap ∧ L0.stack ≤ L.stack

def limitsMax (L L' : Limits) : Limits := ⟨max L.heap L'.heap, max L.stack L'.stack⟩

theorem limitsLe_refl (L : Limits) : LimitsLe L L := ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem limitsLe_trans {L1 L2 L3 : Limits} (a : LimitsLe L1 L2) (b : LimitsLe L2 L3) : LimitsLe L1 L3 :=
  ⟨Nat.le_trans a.1 b.1, Nat.le_trans a.2 b.2⟩

theorem limitsLe_max_left (L L' : Limits) : LimitsLe L (limitsMax L L') :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

theorem limitsLe_max_right (L L' : Limits) : LimitsLe L' (limitsMax L L') :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

theorem fitsFrom_mono {L L' : Limits} (le : LimitsLe L L') {s : State} {n : Nat} (h : FitsFrom L s n) :
    FitsFrom L' s n :=
  fun j lo hi => let ⟨a, b⟩ := h j lo hi; ⟨Nat.le_trans a le.1, Nat.le_trans b le.2⟩

/-- Every finite run fits some limits (the peak heap and stack it reaches). -/
theorem fitsFrom_exists (s : State) : ∀ n, ∃ L, FitsFrom L s n := by
  intro n
  induction n with
  | zero => exact ⟨⟨0, 0⟩, fun j lo hi => by omega⟩
  | succ n ih =>
    obtain ⟨L, fit⟩ := ih
    refine ⟨⟨max L.heap (exec (n + 1) s).heap.size, max L.stack (exec (n + 1) s).stack.length⟩,
      fun j lo hi => ?_⟩
    by_cases jn : j = n + 1
    · subst jn; exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
    · obtain ⟨a, b⟩ := fit j lo (by omega)
      exact ⟨Nat.le_trans a (Nat.le_max_left _ _), Nat.le_trans b (Nat.le_max_left _ _)⟩

/-! ## Backward simulations -/

/-- **A backward simulation** `R F s t` (lazy `s`, forced `t`, address map `F`), over a domain
`Dom` of lazy addresses that depends only on the heap: controls and stacks are renamed, held
addresses are in the domain, any domain control and stack re-enter related, and a forced run
that halts has a lazy run that halts, ending related, under a map that extends `F` on the
domain (which only grows). -/
structure BackSim (R : (Nat → Nat) → State → State → Prop) (Dom : Array Cell → Nat → Prop) : Prop where
  renames : ∀ {F : Nat → Nat} {s t : State}, R F s t →
    t.control = renameControl F s.control ∧ t.stack = s.stack.map (renameFrame F)
  controlIn : ∀ {F : Nat → Nat} {s t : State}, R F s t → AllIn (Dom s.heap) (controlAddresses s.control)
  stackIn : ∀ {F : Nat → Nat} {s t : State}, R F s t → ∀ fr ∈ s.stack, AllIn (Dom s.heap) (frameAddresses fr)
  reenter : ∀ {F : Nat → Nat} {s t : State} (c : Control) (S : List Frame), R F s t →
    AllIn (Dom s.heap) (controlAddresses c) → (∀ fr ∈ S, AllIn (Dom s.heap) (frameAddresses fr)) →
    R F ⟨s.heap, c, S⟩ ⟨t.heap, renameControl F c, S.map (renameFrame F)⟩
  back : ∀ {F : Nat → Nat} {s t : State} {n' : Nat}, R F s t → Halts t n' →
    ∃ n F', Halts s n ∧ R F' (exec n s) (exec n' t) ∧ ∀ a, Dom s.heap a → Dom (exec n s).heap a ∧ F' a = F a

/-- The threshold form of "the lazy side commits too": every resource vector at least
`(L0, T0)` commits, to `out`, with `T - T0` ticks left. -/
def ForceAbove (L0 : Limits) (n : Nat) (s : State) (v : RuntimeValue) (st : State) : Prop :=
  ∀ (L : Limits) (T : Nat), LimitsLe L0 L → n ≤ T → forceWith (fun _ => true) L T s = (.finished v st, T - n)

/-- **Forcing, backward.** -/
theorem BackSim.forceWith {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {s t : State} (rel : R F s t)
    {L' : Limits} {T' : Nat} {v' : RuntimeValue} {st' : State} {r' : Nat}
    (ran : ObjectiveBendDemandData.forceWith (fun _ => true) L' T' t = (.finished v' st', r')) :
    ∃ (n : Nat) (L0 : Limits) (v : RuntimeValue) (F' : Nat → Nat),
      ForceAbove L0 n s v (exec n s) ∧ renameValue F' v = v' ∧ R F' (exec n s) st' ∧
      AllIn (Dom (exec n s).heap) (valueAddresses v) ∧
      (∀ a, Dom s.heap a → Dom (exec n s).heap a ∧ F' a = F a) := by
  obtain ⟨n', _, haltsT, _, eq, ctl, _⟩ := forceWith_finished L' T' t v' st' r' ran
  obtain ⟨n, F', halts, rel', ext⟩ := sim.back rel haltsT
  rw [eq] at rel'
  obtain ⟨L0, fits⟩ := fitsFrom_exists s n
  have ctlR := (sim.renames rel').1
  have inside := sim.controlIn rel'
  rw [ctl] at ctlR
  cases hc : (exec n s).control with
  | complete v =>
    rw [hc] at ctlR inside
    simp only [renameControl, Control.complete.injEq] at ctlR
    subst ctlR
    exact ⟨n, L0, v, F', fun L T le nle => forceWith_of_halts L T s n v halts nle (fitsFrom_mono le fits) hc,
      rfl, rel', inside, ext⟩
  | _ => rw [hc] at ctlR; simp [renameControl] at ctlR

/-- Materialization backward at one depth: the forced side's success has, above a threshold,
a lazy success to the same Data with the same nodes and bytes left, `k` ticks left for every
`T0 + k` given, ending in a related state that does not depend on the resources given. -/
def MaterializeBack (R : (Nat → Nat) → State → State → Prop) (Dom : Array Cell → Nat → Prop)
    (L' : Limits) (depth : Nat) : Prop :=
  ∀ (budget' : Budget) (v : RuntimeValue) (s t : State) (F : Nat → Nat) (r' : Result),
    R F s t → AllIn (Dom s.heap) (valueAddresses v) →
    materializeWith (fun _ => true) L' depth budget' (renameValue F v) t = .ok r' →
    ∃ (L0 : Limits) (T0 : Nat) (st : State) (F' : Nat → Nat), R F' st r'.state ∧
      (∀ a, Dom s.heap a → Dom st.heap a ∧ F' a = F a) ∧
      ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
        materializeWith (fun _ => true) L depth ⟨budget'.nodes, T0 + k, budget'.bytes⟩ v s =
          .ok ⟨r'.value, st, ⟨r'.remaining.nodes, k, r'.remaining.bytes⟩⟩

/-- **The record fold, backward.** -/
theorem BackSim.fold {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {L' : Limits} {depth : Nat} (ih : MaterializeBack R Dom L' depth) :
    ∀ (fields : List (String × Nat)) (acc : List (String × Data)) (s t : State) (b' : Budget)
      (F : Nat → Nat) (out' : List (String × Data) × State × Budget),
      R F s t → AllIn (Dom s.heap) (fields.map Prod.snd) →
      (fields.map fun field => (field.1, F field.2)).foldlM (recordStep (fun _ => true) L' depth)
        (acc, t, b') = .ok out' →
      ∃ (L0 : Limits) (T0 : Nat) (st : State) (F' : Nat → Nat), R F' st out'.2.1 ∧
        (∀ a, Dom s.heap a → Dom st.heap a ∧ F' a = F a) ∧
        ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
          fields.foldlM (recordStep (fun _ => true) L depth) (acc, s, ⟨b'.nodes, T0 + k, b'.bytes⟩) =
            .ok (out'.1, st, ⟨out'.2.2.nodes, k, out'.2.2.bytes⟩) := by
  intro fields
  induction fields with
  | nil =>
    intro acc s t b' F out' rel _ folded
    simp at folded
    subst folded
    exact ⟨⟨0, 0⟩, 0, s, F, rel, fun a h => ⟨h, rfl⟩, fun L k _ => by simp [List.foldlM]⟩
  | cons field rest ihf =>
    intro acc s t b' F out' rel inside folded
    simp only [List.map_cons, List.foldlM_cons, except_bind_ok] at folded
    obtain ⟨mid', first', restFolded⟩ := folded
    have fieldIn : Dom s.heap field.2 := inside field.2 (by simp)
    obtain ⟨nodes, ticks', bytes⟩ := b'
    simp [recordStep] at first'
    split at first'
    · simp at first'
    · rename_i cond
      have entered := sim.reenter (.enter field.2) [] rel (by simpa [controlAddresses] using fieldIn)
        (fun _ m => by cases m)
      cases forced : ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks' ⟨t.heap, .enter (F field.2), []⟩ with
      | mk outcome rest' =>
        rw [forced] at first'
        cases outcome with
        | finished value' retained' =>
          simp at first'
          obtain ⟨a', materialized, rfl⟩ := first'
          obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
          subst vEq
          obtain ⟨L2, T2, st2, F2, rel2, ext2, child⟩ := ih _ v _ _ F1 a' rel1 vIn materialized
          have restIn : AllIn (Dom st2.heap) (rest.map Prod.snd) := fun x m =>
            (ext2 x (ext1 x (inside x (by simp at m ⊢; exact Or.inr m))).1).1
          have restMap : rest.map (fun field => (field.1, F field.2)) =
              rest.map (fun field => (field.1, F2 field.2)) := by
            apply List.map_congr_left
            intro fld m
            have dx : Dom s.heap fld.2 := inside fld.2 (by simp; exact Or.inr ⟨fld.1, m⟩)
            rw [(ext2 _ (ext1 _ dx).1).2, (ext1 _ dx).2]
          rw [restMap] at restFolded
          obtain ⟨L3, T3, st3, F3, rel3, ext3, tail⟩ := ihf _ st2 _ _ F2 out' rel2 restIn restFolded
          refine ⟨limitsMax L1 (limitsMax L2 L3), n + (T2 + T3), st3, F3, rel3, fun x hx => ?_, fun L k le => ?_⟩
          · obtain ⟨d1, f1⟩ := ext1 x hx
            obtain ⟨d2, f2⟩ := ext2 x d1
            obtain ⟨d3, f3⟩ := ext3 x d2
            exact ⟨d3, by rw [f3, f2, f1]⟩
          · have le1 := limitsLe_trans (limitsLe_max_left _ _) le
            have le2 := limitsLe_trans (limitsLe_trans (limitsLe_max_left _ _) (limitsLe_max_right _ _)) le
            have le3 := limitsLe_trans (limitsLe_trans (limitsLe_max_right _ _) (limitsLe_max_right _ _)) le
            have runL := above L (n + (T2 + T3) + k) le1 (by omega)
            rw [show n + (T2 + T3) + k - n = T2 + (T3 + k) by omega] at runL
            have childL := child L (T3 + k) le2
            simp only [List.foldlM_cons, except_bind_ok]
            refine ⟨((field.1, a'.value) :: acc, st2, ⟨a'.remaining.nodes, T3 + k, a'.remaining.bytes⟩), ?_, tail L k le3⟩
            simp [recordStep, cond, runL, childL]
        | _ => simp at first'

/-- **Materialization, backward.** -/
theorem BackSim.materialize {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) (L' : Limits) : ∀ depth, MaterializeBack R Dom L' depth := by
  intro depth
  induction depth with
  | zero => intro budget' v s t F r' _ _ found; simp [materializeWith] at found
  | succ depth ih =>
    intro budget' v s t F r' rel valueIn found
    obtain ⟨nodes, ticks', bytes⟩ := budget'
    cases v with
    | natural m =>
      simp [materializeWith, renameValue] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          subst found
          exact ⟨⟨0, 0⟩, 0, s, F, rel, fun a h => ⟨h, rfl⟩, fun L k _ => by simp [materializeWith, c1, c2]⟩
    | boolean b =>
      simp [materializeWith, renameValue] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          subst found
          exact ⟨⟨0, 0⟩, 0, s, F, rel, fun a h => ⟨h, rfl⟩, fun L k _ => by simp [materializeWith, c1, c2]⟩
    | label l =>
      simp [materializeWith, renameValue] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          subst found
          exact ⟨⟨0, 0⟩, 0, s, F, rel, fun a h => ⟨h, rfl⟩, fun L k _ => by simp [materializeWith, c1, c2]⟩
    | closure body environment =>
      simp [materializeWith, renameValue] at found; split at found <;> simp at found
    | specification metadata extension =>
      simp [materializeWith, renameValue] at found; split at found <;> simp at found
    | prototype spec target =>
      simp [materializeWith, renameValue] at found; split at found <;> simp at found
    | variant label payload =>
      have payloadIn : Dom s.heap payload := valueIn payload (by simp [valueAddresses])
      simp [materializeWith, renameValue] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          have entered := sim.reenter (.enter payload) [] rel (by simpa [controlAddresses] using payloadIn)
            (fun _ m => by cases m)
          cases forced : ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks' ⟨t.heap, .enter (F payload), []⟩ with
          | mk outcome rest =>
            rw [forced] at found
            cases outcome with
            | finished value' retained' =>
              simp at found
              obtain ⟨a', materialized, rfl⟩ := found
              obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
              subst vEq
              obtain ⟨L2, T2, st2, F2, rel2, ext2, child⟩ := ih _ v _ _ F1 a' rel1 vIn materialized
              refine ⟨limitsMax L1 L2, n + T2, st2, F2, rel2, fun x hx => ?_, fun L k le => ?_⟩
              · obtain ⟨d1, f1⟩ := ext1 x hx
                obtain ⟨d2, f2⟩ := ext2 x d1
                exact ⟨d2, by rw [f2, f1]⟩
              · have runL := above L (n + T2 + k) (limitsLe_trans (limitsLe_max_left _ _) le) (by omega)
                rw [show n + T2 + k - n = T2 + k by omega] at runL
                have childL := child L k (limitsLe_trans (limitsLe_max_right _ _) le)
                simp [materializeWith, c1, c2, runL, childL]
            | _ => simp at found
    | record fields =>
      have fieldsIn : AllIn (Dom s.heap) (fields.map Prod.snd) := valueIn
      simp only [renameValue] at found
      simp [materializeWith_record] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · split at found
            · simp at found
            · rename_i c1 c2 c3 c4
              obtain ⟨out', folded, rfl⟩ := (except_map_ok _ _ _).mp found
              obtain ⟨L0, T0, st, F', rel', ext', fold⟩ :=
                sim.fold (ih) fields [] s t _ F out' rel fieldsIn folded
              refine ⟨L0, T0, st, F', rel', ext', fun L k le => ?_⟩
              have foldL := fold L k le
              have c3' : (fields.map Prod.fst).eraseDups.length = fields.length := by
                simpa [Function.comp_def] using c3
              simp [materializeWith_record, c1, c2, c3', c4, foldL]
          · simp at found

/-- Renaming a held state by two maps that agree on the domain gives the same state. -/
theorem rename_state_congr {Dom : Array Cell → Nat → Prop} {F G : Nat → Nat} {H : Array Cell} {c : Control}
    {S : List Frame} (cIn : AllIn (Dom H) (controlAddresses c)) (sIn : ∀ fr ∈ S, AllIn (Dom H) (frameAddresses fr))
    (same : ∀ a, Dom H a → G a = F a) :
    renameControl G c = renameControl F c ∧ S.map (renameFrame G) = S.map (renameFrame F) :=
  ⟨renameControl_congr (fun x m => same x (cIn x m)),
    List.map_congr_left (fun fr m => renameFrame_congr (fun x mx => same x (sIn fr m x mx)))⟩

/-- **Plan extraction, backward**: the forced yield's Plan extracts, so the lazy yield's Plan
extracts to the same Data above a threshold (heap and stack room, extraction ticks), with the
same nodes and bytes left, ending in a related state (the checkpoint candidates). -/
theorem BackSim.yieldedPlan {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {y y' : State} (rel : R F y y') {L' : Limits} {budget' : Budget}
    {r' : Result} (found : ObjectiveBendDemandData.yieldedPlan L' budget' y' = .ok r') :
    ∃ (L0 : Limits) (E0 : Nat) (st : State) (F' : Nat → Nat), R F' st r'.state ∧
      (∀ a, Dom y.heap a → Dom st.heap a ∧ F' a = F a) ∧
      ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
        ObjectiveBendDemandData.yieldedPlan L ⟨budget'.nodes, E0 + k, budget'.bytes⟩ y =
          .ok ⟨r'.value, st, ⟨r'.remaining.nodes, k, r'.remaining.bytes⟩⟩ := by
  obtain ⟨ctlEq, stEq⟩ := sim.renames rel
  have cIn := sim.controlIn rel
  have sIn := sim.stackIn rel
  unfold ObjectiveBendDemandData.yieldedPlan yieldedPlanWith at found ⊢
  cases hc : y.control with
  | yielded plan =>
    rw [ctlEq, hc] at found
    rw [hc] at cIn
    simp only [renameControl] at found
    have planIn : Dom y.heap plan := cIn plan (by simp [controlAddresses])
    have entered := sim.reenter (.enter plan) [] rel (by simpa [controlAddresses] using planIn) (fun _ m => by cases m)
    obtain ⟨nodes, ticks', bytes⟩ := budget'
    cases forced : ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks' ⟨y'.heap, .enter (F plan), []⟩ with
    | mk outcome rest =>
      simp only at found
      rw [forced] at found
      cases outcome with
      | finished value' retained' =>
        simp at found
        obtain ⟨a', materialized, rfl⟩ := found
        obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
        subst vEq
        obtain ⟨L2, T2, st2, F2, rel2, ext2, child⟩ := sim.materialize L' _ _ v _ _ F1 a' rel1 vIn materialized
        have ext : ∀ a, Dom y.heap a → Dom st2.heap a ∧ F2 a = F a := fun x hx => by
          obtain ⟨d1, f1⟩ := ext1 x hx
          obtain ⟨d2, f2⟩ := ext2 x d1
          exact ⟨d2, by rw [f2, f1]⟩
        have cIn' : AllIn (Dom st2.heap) (controlAddresses (.yielded plan)) := fun x m => (ext x (cIn x m)).1
        have sIn' : ∀ fr ∈ y.stack, AllIn (Dom st2.heap) (frameAddresses fr) := fun fr m x mx => (ext x (sIn fr m x mx)).1
        have back := sim.reenter (.yielded plan) y.stack rel2 cIn' sIn'
        obtain ⟨cSame, sSame⟩ := rename_state_congr (Dom := Dom) (H := y.heap) (c := .yielded plan) (S := y.stack)
          cIn sIn (fun a h => (ext a h).2)
        rw [cSame, sSame, ← stEq] at back
        refine ⟨limitsMax L1 L2, n + T2, ⟨st2.heap, .yielded plan, y.stack⟩, F2, back, fun x hx => ⟨(ext x hx).1, (ext x hx).2⟩,
          fun L k le => ?_⟩
        have runL := above L (n + T2 + k) (limitsLe_trans (limitsLe_max_left _ _) le) (by omega)
        rw [show n + T2 + k - n = T2 + k by omega] at runL
        have childL := child L k (limitsLe_trans (limitsLe_max_right _ _) le)
        simp [runL, childL]
      | _ => simp at found
  | _ => rw [ctlEq, hc] at found; simp [renameControl] at found

/-- **Completion, backward.** -/
theorem BackSim.complete {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {y y' : State} (rel : R F y y') {L' : Limits} {budget' : Budget}
    {r' : Result} (found : ObjectiveBendDemandData.complete L' budget' y' = .ok r') :
    ∃ (L0 : Limits) (E0 : Nat) (st : State) (F' : Nat → Nat), R F' st r'.state ∧
      (∀ a, Dom y.heap a → Dom st.heap a ∧ F' a = F a) ∧
      ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
        ObjectiveBendDemandData.complete L ⟨budget'.nodes, E0 + k, budget'.bytes⟩ y =
          .ok ⟨r'.value, st, ⟨r'.remaining.nodes, k, r'.remaining.bytes⟩⟩ := by
  obtain ⟨ctlEq, stEq⟩ := sim.renames rel
  have cIn := sim.controlIn rel
  unfold ObjectiveBendDemandData.complete completeWith at found ⊢
  obtain ⟨nodes, ticks', bytes⟩ := budget'
  cases hc : y.control with
  | complete v =>
    cases hs : y.stack with
    | nil =>
      rw [ctlEq, stEq, hc, hs] at found
      rw [hc] at cIn
      simp only [renameControl, List.map_nil] at found
      simp at found
      obtain ⟨a', materialized, rest⟩ := found
      obtain ⟨L0, T0, st, F', rel', ext', child⟩ := sim.materialize L' _ _ v _ _ F a' rel cIn materialized
      split at rest
      · rename_i encodedBytes encodedAt
        split at rest
        · simp at rest
        · rename_i small
          simp at rest
          subst rest
          refine ⟨L0, T0, st, F', rel', ext', fun L k le => ?_⟩
          have childL := child L k le
          simp [childL, encodedAt, small]
      · simp at rest
    | cons fr rest => rw [ctlEq, stEq, hc, hs] at found; simp at found
  | _ => rw [ctlEq, hc] at found; simp [renameControl] at found

/-- **Bounded runs, backward**: a forced bounded run that does not suspend has a lazy run that,
under every limits and ticks above a threshold, is its halting raw run, the two ends related. -/
theorem BackSim.runBounded {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {s t : State} (rel : R F s t) {L' : Limits} {T' : Nat}
    (notSusp : ∀ r st, ObjectiveBendDemandMachine.runBounded L' T' t ≠ .suspended r st) :
    ∃ (n n' : Nat) (L0 : Limits) (F' : Nat → Nat), R F' (exec n s) (exec n' t) ∧
      ObjectiveBendDemandMachine.runBounded L' T' t = ObjectiveBendDemandMachine.runBounded L' 0 (exec n' t) ∧
      (∀ a, Dom s.heap a → Dom (exec n s).heap a ∧ F' a = F a) ∧
      ∀ (L : Limits) (T : Nat), LimitsLe L0 L → n ≤ T →
        ObjectiveBendDemandMachine.runBounded L T s = ObjectiveBendDemandMachine.runBounded L 0 (exec n s) := by
  obtain ⟨n', _, haltsT, _, eqT⟩ := runBounded_halts L' T' t notSusp
  obtain ⟨n, F', halts, rel', ext⟩ := sim.back rel haltsT
  obtain ⟨L0, fits⟩ := fitsFrom_exists s n
  exact ⟨n, n', L0, F', rel', eqT, ext,
    fun L T le nle => runBounded_of_halts L T s n halts nle (fitsFrom_mono le fits)⟩

/-! ## Terminal states -/

theorem runBounded_zero_yielded {L : Limits} {s y : State} {p : Nat} :
    ObjectiveBendDemandMachine.runBounded L 0 s = .yielded p y ↔ s.control = .yielded p ∧ y = s := by
  cases hc : s.control <;> simp [ObjectiveBendDemandMachine.runBounded, hc, eq_comm]

theorem runBounded_zero_finished {L : Limits} {s y : State} {v : RuntimeValue} :
    ObjectiveBendDemandMachine.runBounded L 0 s = .finished v y ↔ s.control = .complete v ∧ y = s := by
  cases hc : s.control <;> simp [ObjectiveBendDemandMachine.runBounded, hc, eq_comm]

theorem runBounded_zero_divergent {L : Limits} {s y : State} {a : Nat} :
    ObjectiveBendDemandMachine.runBounded L 0 s = .divergent a y ↔ s.control = .blackhole a ∧ y = s := by
  cases hc : s.control <;> simp [ObjectiveBendDemandMachine.runBounded, hc, eq_comm]

theorem runBounded_zero_refused {L : Limits} {s y : State} {reason : Refusal} :
    ObjectiveBendDemandMachine.runBounded L 0 s = .refused reason y ↔ s.control = .refused reason ∧ y = s := by
  cases hc : s.control <;> simp [ObjectiveBendDemandMachine.runBounded, hc, eq_comm]

/-! ## Instances -/

/-- **Forcing chains are backward simulations.** -/
theorem forcesSim (gap : Nat) : BackSim (ForcesBy gap) (fun H a => a < H.size) where
  renames h := h.renames
  controlIn h := h.lazyValid.control
  stackIn h := h.lazyValid.stack
  reenter c S h cIn sIn := h.reenter c S cIn sIn
  back h halts := by
    obtain ⟨n, F', _, hn, _, rel, ext⟩ := forces_transfer_back h halts
    exact ⟨n, F', hn, rel, fun a lt => ⟨Nat.lt_of_lt_of_le lt (exec_size_mono _ n), ext a lt⟩⟩

theorem related_exec {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t) :
    ∀ n, Related f D (exec n s) (exec n t) := by
  intro n
  induction n with
  | zero => exact related
  | succ n ih => rw [exec_succ, exec_succ]; exact related_stepRaw ih

/-- **A renaming relation (the collection's) is a backward simulation**: it is lockstep, so
the original halts exactly when the renamed state does. -/
theorem relatedSim (f : Nat → Nat) (D : Nat → Prop) :
    BackSim (fun F s t => F = f ∧ Related f D s t) (fun _ a => D a) where
  renames h := by obtain ⟨rfl, r⟩ := h; exact ⟨r.control, r.stack⟩
  controlIn h := h.2.controlIn
  stackIn h := h.2.stackIn
  reenter c S h cIn sIn := by obtain ⟨rfl, r⟩ := h; exact ⟨rfl, ⟨r.heap, cIn, rfl, sIn, rfl⟩⟩
  back h halts := by
    obtain ⟨rfl, r⟩ := h
    have all := related_exec r
    refine ⟨_, _, ⟨fun j lt => ?_, ?_⟩, ⟨rfl, all _⟩, fun a d => ⟨d, rfl⟩⟩
    · have := halts.1 j lt; rwa [(all j).control, active_rename] at this
    · have := halts.2; rwa [(all _).control, active_rename] at this

#assert_axioms halts_prepend agree_halts_back pend_halts_back forces_halts_back forces_transfer_back
#assert_axioms fitsFrom_mono fitsFrom_exists rename_state_congr
#assert_axioms BackSim.forceWith BackSim.fold BackSim.materialize BackSim.yieldedPlan BackSim.complete
#assert_axioms BackSim.runBounded forcesSim related_exec relatedSim

end Minidregg.Theory.ObjectiveBendDemandForcing
