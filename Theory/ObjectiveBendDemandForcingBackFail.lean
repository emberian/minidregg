/- Extraction failures, backward (forcing transparency, part 11).

`ObjectiveBendDemandForcingBack` transfers SUCCESS backward along a normalization: a forced
extraction that succeeds has a lazy one that succeeds alike above a threshold. This module
transfers FAILURE. Every non-resource extraction failure is the program's own: a forced
extraction that fails with `budget` (the output's nodes or bytes), `duplicateField`,
`executableValue`, `divergent`, `refused` or `yielded` has a lazy extraction that fails with
the SAME failure, under every resource vector above a threshold (heap and stack room, ticks,
extraction ticks), with the same output nodes and bytes (`BackSim.materializeFail`,
`BackSim.yieldedPlanFail`, `BackSim.completeFail`, `Chain.failsBack`). The output sizes are
the deployment's, not a resource: a `budget` failure is a property of the Data.

The exceptions are `tickExhausted` (extraction ticks) and `suspended` (heap/stack room
or policy): both are RESOURCE failures and do not transfer (`suspended_is_resource`: one state
whose extraction suspends with no extraction ticks and succeeds with more).

So (`node_malformed_of_chain`) a normalized state whose segment halts in a yield or a
completion whose extraction fails semantically is in a chain with a lazy state whose reference
node is `malformed`: no resources make its Plan or result Data within the output sizes. -/
import Theory.ObjectiveBendDemandForcingConverse
import Theory.ObjectiveBendInteraction
import Theory.ObjectiveBendDemandDataSoundness
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendDemandData
set_option autoImplicit false

/-- The failure an extraction throws for a forcing outcome (`none`: it finished). -/
def failureOf : Outcome → Option Failure
  | .finished _ _ => none
  | .suspended reason _ => some (suspensionFailure reason)
  | .divergent _ _ => some .divergent
  | .refused _ _ => some .refused
  | .yielded _ _ => some .yielded

@[simp] theorem suspensionFailure_ne_divergent (reason : Suspension) :
    suspensionFailure reason ≠ .divergent := by cases reason <;> simp [suspensionFailure]

@[simp] theorem suspensionFailure_ne_refused (reason : Suspension) :
    suspensionFailure reason ≠ .refused := by cases reason <;> simp [suspensionFailure]

@[simp] theorem suspensionFailure_ne_yielded (reason : Suspension) :
    suspensionFailure reason ≠ .yielded := by cases reason <;> simp [suspensionFailure]

/-- A terminal outcome's failure depends only on the control, up to renaming. -/
theorem failureOf_rename {L L' : Limits} {x y : State} {G : Nat → Nat}
    (ctl : y.control = renameControl G x.control) :
    failureOf (ObjectiveBendDemandMachine.runBounded L 0 x) = failureOf (ObjectiveBendDemandMachine.runBounded L' 0 y) := by
  cases hc : x.control <;> rw [hc] at ctl <;>
    simp [ObjectiveBendDemandMachine.runBounded, hc, ctl, renameControl, failureOf]

/-- **A forcing that fails, backward.** A forced forcing whose outcome is a failure other
than `suspended` has a lazy forcing with the same failure above a threshold. -/
theorem BackSim.forceFail {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {s t : State} (rel : R F s t) {L' : Limits} {T' : Nat}
    {f : Failure} (fails : failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L' T' t).1 = some f) (semantic : f ≠ .suspended ∧ f ≠ .tickExhausted) :
    ∃ (L0 : Limits) (n : Nat), ∀ (L : Limits) (T : Nat), LimitsLe L0 L → n ≤ T →
      failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L T s).1 = some f := by
  rw [ObjectiveBendDemandDataSoundness.forceWith_unrestricted] at fails
  have notSusp : ∀ r st, ObjectiveBendDemandMachine.runBounded L' T' t ≠ .suspended r st := by
    intro r st h
    rw [h] at fails
    cases r with
    | ticks => simp [failureOf, suspensionFailure] at fails; exact semantic.2 fails.symm
    | capacity => simp [failureOf, suspensionFailure] at fails; exact semantic.1 fails.symm
  obtain ⟨n, n', L0, F', rel', eqT, _, lazy⟩ := sim.runBounded rel notSusp
  have ctl := (sim.renames rel').1
  refine ⟨L0, n, fun L T le nle => ?_⟩
  rw [ObjectiveBendDemandDataSoundness.forceWith_unrestricted, lazy L T le nle, failureOf_rename ctl (L' := L'),
    ← eqT]
  exact fails

theorem except_map_error {ε α β : Type} (g : α → β) (x : Except ε α) (e : ε) :
    (g <$> x) = .error e ↔ x = .error e := by
  cases x <;> simp [Functor.map, Except.map]

theorem except_bind_error {ε α β : Type} (x : Except ε α) (k : α → Except ε β) (e : ε) :
    (x >>= k) = .error e ↔ x = .error e ∨ ∃ a, x = .ok a ∧ k a = .error e := by
  cases x <;> simp [bind, Except.bind]

/-- Materialization failure backward at one depth. -/
def MaterializeFailBack (R : (Nat → Nat) → State → State → Prop) (Dom : Array Cell → Nat → Prop)
    (L' : Limits) (depth : Nat) : Prop :=
  ∀ (budget' : Budget) (v : RuntimeValue) (s t : State) (F : Nat → Nat) (f : Failure) (st' : State × Budget),
    R F s t → AllIn (Dom s.heap) (valueAddresses v) → (f ≠ .suspended ∧ f ≠ .tickExhausted) →
    materializeWith (fun _ => true) L' depth budget' (renameValue F v) t = .error (f, st') →
    ∃ (L0 : Limits) (T0 : Nat), ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
      ∃ st, materializeWith (fun _ => true) L depth ⟨budget'.nodes, T0 + k, budget'.bytes⟩ v s = .error (f, st)

/-- **The record fold's failure, backward.** -/
theorem BackSim.foldFail {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {L' : Limits} {depth : Nat} (ih : MaterializeFailBack R Dom L' depth) :
    ∀ (fields : List (String × Nat)) (acc : List (String × Data)) (s t : State) (b' : Budget)
      (F : Nat → Nat) (f : Failure) (st' : State × Budget),
      R F s t → AllIn (Dom s.heap) (fields.map Prod.snd) → (f ≠ .suspended ∧ f ≠ .tickExhausted) →
      (fields.map fun field => (field.1, F field.2)).foldlM (recordStep (fun _ => true) L' depth)
        (acc, t, b') = .error (f, st') →
      ∃ (L0 : Limits) (T0 : Nat), ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
        ∃ st, fields.foldlM (recordStep (fun _ => true) L depth) (acc, s, ⟨b'.nodes, T0 + k, b'.bytes⟩) =
          .error (f, st) := by
  intro fields
  induction fields with
  | nil =>
    intro acc s t b' F f st' _ _ _ folded
    simp [List.foldlM, pure, Except.pure] at folded
  | cons field rest ihf =>
    intro acc s t b' F f st' rel inside semantic folded
    simp only [List.map_cons, List.foldlM_cons, except_bind_error] at folded
    have fieldIn : Dom s.heap field.2 := inside field.2 (by simp)
    obtain ⟨nodes, ticks', bytes⟩ := b'
    have entered := sim.reenter (.enter field.2) [] rel (by simpa [controlAddresses] using fieldIn)
      (fun _ m => by cases m)
    rcases folded with first' | ⟨mid', first', restFolded⟩
    · simp [recordStep] at first'
      split at first'
      · rename_i cond
        change Except.error _ = Except.error _ at first'
        simp only [Except.error.injEq, Prod.mk.injEq] at first'
        obtain ⟨rfl, -⟩ := first'
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [List.foldlM_cons, recordStep, cond] <;> rfl⟩⟩
      · rename_i cond
        cases forced : ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks' ⟨t.heap, .enter (F field.2), []⟩ with
        | mk outcome rest' =>
        rw [forced] at first'
        cases outcome with
        | finished value' retained' =>
          rw [except_map_error] at first'
          obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
          subst vEq
          obtain ⟨L2, T2, child⟩ := ih _ v _ _ F1 f st' rel1 vIn semantic first'
          refine ⟨limitsMax L1 L2, n + T2, fun L k le => ?_⟩
          have runL := above L (n + T2 + k) (limitsLe_trans (limitsLe_max_left _ _) le) (by omega)
          rw [show n + T2 + k - n = T2 + k by omega] at runL
          obtain ⟨st, childL⟩ := child L k (limitsLe_trans (limitsLe_max_right _ _) le)
          exact ⟨st, by simp [List.foldlM_cons, except_bind_error, except_map_error, recordStep, cond, runL, childL]⟩
        | suspended reason _ =>
          change Except.error _ = Except.error _ at first'
          simp only [Except.error.injEq, Prod.mk.injEq] at first'
          cases reason with
          | ticks => exact absurd first'.1.symm semantic.2
          | capacity => exact absurd first'.1.symm semantic.1
        | divergent _ _ =>
          change Except.error _ = Except.error _ at first'
          simp only [Except.error.injEq, Prod.mk.injEq] at first'
          obtain ⟨rfl, -⟩ := first'
          have fail : failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks'
              ⟨t.heap, .enter (F field.2), []⟩).1 = some .divergent := by rw [forced]; rfl
          obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
          refine ⟨L1, n, fun L k le => ?_⟩
          have lz := lazy L (n + k) le (by omega)
          cases lf : ObjectiveBendDemandData.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter field.2, []⟩ with
          | mk o r =>
            rw [lf] at lz
            cases o <;> simp [failureOf] at lz <;>
              exact ⟨_, by simp [List.foldlM_cons, except_bind_error, recordStep, cond, lf] <;> rfl⟩
        | refused _ _ =>
          change Except.error _ = Except.error _ at first'
          simp only [Except.error.injEq, Prod.mk.injEq] at first'
          obtain ⟨rfl, -⟩ := first'
          have fail : failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks'
              ⟨t.heap, .enter (F field.2), []⟩).1 = some .refused := by rw [forced]; rfl
          obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
          refine ⟨L1, n, fun L k le => ?_⟩
          have lz := lazy L (n + k) le (by omega)
          cases lf : ObjectiveBendDemandData.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter field.2, []⟩ with
          | mk o r =>
            rw [lf] at lz
            cases o <;> simp [failureOf] at lz <;>
              exact ⟨_, by simp [List.foldlM_cons, except_bind_error, recordStep, cond, lf] <;> rfl⟩
        | yielded _ _ =>
          change Except.error _ = Except.error _ at first'
          simp only [Except.error.injEq, Prod.mk.injEq] at first'
          obtain ⟨rfl, -⟩ := first'
          have fail : failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks'
              ⟨t.heap, .enter (F field.2), []⟩).1 = some .yielded := by rw [forced]; rfl
          obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
          refine ⟨L1, n, fun L k le => ?_⟩
          have lz := lazy L (n + k) le (by omega)
          cases lf : ObjectiveBendDemandData.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter field.2, []⟩ with
          | mk o r =>
            rw [lf] at lz
            cases o <;> simp [failureOf] at lz <;>
              exact ⟨_, by simp [List.foldlM_cons, except_bind_error, recordStep, cond, lf] <;> rfl⟩
    · simp [recordStep] at first'
      split at first'
      · simp at first'
      · rename_i cond
        cases forced : ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks' ⟨t.heap, .enter (F field.2), []⟩ with
        | mk outcome rest' =>
          rw [forced] at first'
          cases outcome with
          | finished value' retained' =>
            simp at first'
            obtain ⟨a', materialized, rfl⟩ := first'
            obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
            subst vEq
            obtain ⟨L2, T2, st2, F2, rel2, ext2, child⟩ := sim.materialize L' _ _ v _ _ F1 a' rel1 vIn materialized
            have restIn : AllIn (Dom st2.heap) (rest.map Prod.snd) := fun x m =>
              (ext2 x (ext1 x (inside x (by simp at m ⊢; exact Or.inr m))).1).1
            have restMap : rest.map (fun field => (field.1, F field.2)) =
                rest.map (fun field => (field.1, F2 field.2)) := by
              apply List.map_congr_left
              intro fld m
              have dx : Dom s.heap fld.2 := inside fld.2 (by simp; exact Or.inr ⟨fld.1, m⟩)
              rw [(ext2 _ (ext1 _ dx).1).2, (ext1 _ dx).2]
            rw [restMap] at restFolded
            obtain ⟨L3, T3, tail⟩ := ihf _ st2 _ _ F2 f st' rel2 restIn semantic restFolded
            refine ⟨limitsMax L1 (limitsMax L2 L3), n + (T2 + T3), fun L k le => ?_⟩
            have le1 := limitsLe_trans (limitsLe_max_left _ _) le
            have le2 := limitsLe_trans (limitsLe_trans (limitsLe_max_left _ _) (limitsLe_max_right _ _)) le
            have le3 := limitsLe_trans (limitsLe_trans (limitsLe_max_right _ _) (limitsLe_max_right _ _)) le
            have runL := above L (n + (T2 + T3) + k) le1 (by omega)
            rw [show n + (T2 + T3) + k - n = T2 + (T3 + k) by omega] at runL
            have childL := child L (T3 + k) le2
            obtain ⟨st, tailL⟩ := tail L k le3
            refine ⟨st, ?_⟩
            simp only [List.foldlM_cons, except_bind_error]
            refine .inr ⟨((field.1, a'.value) :: acc, st2, ⟨a'.remaining.nodes, T3 + k, a'.remaining.bytes⟩), ?_, tailL⟩
            simp [recordStep, cond, runL, childL]
          | _ => simp at first'

theorem BackSim.materializeFail {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) (L' : Limits) : ∀ depth, MaterializeFailBack R Dom L' depth := by
  intro depth
  induction depth with
  | zero =>
    intro budget' v s t F f st' _ _ _ found
    simp [materializeWith] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith] <;> rfl⟩⟩
  | succ depth ih =>
    intro budget' v s t F f st' rel valueIn semantic found
    obtain ⟨nodes, ticks', bytes⟩ := budget'
    cases v with
    | natural m =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        split at found
        · rename_i c2
          simp at found
          obtain ⟨rfl, -⟩ := found
          exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1, c2] <;> rfl⟩⟩
        · cases found
    | boolean b =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        split at found
        · rename_i c2
          simp at found
          obtain ⟨rfl, -⟩ := found
          exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1, c2] <;> rfl⟩⟩
        · cases found
    | label l =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        split at found
        · rename_i c2
          simp at found
          obtain ⟨rfl, -⟩ := found
          exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1, c2] <;> rfl⟩⟩
        · cases found
    | closure body environment =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
    | specification metadata extension =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
    | prototype spec target =>
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
    | variant label payload =>
      have payloadIn : Dom s.heap payload := valueIn payload (by simp [valueAddresses])
      simp [materializeWith, renameValue] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1] <;> rfl⟩⟩
      · rename_i c1
        split at found
        · rename_i c2
          change Except.error _ = Except.error _ at found
          simp only [Except.error.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, -⟩ := found
          exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith, c1, c2] <;> rfl⟩⟩
        · rename_i c2
          have entered := sim.reenter (.enter payload) [] rel (by simpa [controlAddresses] using payloadIn)
            (fun _ m => by cases m)
          cases forced : ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks' ⟨t.heap, .enter (F payload), []⟩ with
          | mk outcome rest =>
            rw [forced] at found
            cases outcome with
            | finished value' retained' =>
              simp only [except_map_error] at found
              obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
              subst vEq
              obtain ⟨L2, T2, child⟩ := ih _ v _ _ F1 f st' rel1 vIn semantic found
              refine ⟨limitsMax L1 L2, n + T2, fun L k le => ?_⟩
              have runL := above L (n + T2 + k) (limitsLe_trans (limitsLe_max_left _ _) le) (by omega)
              rw [show n + T2 + k - n = T2 + k by omega] at runL
              obtain ⟨st, childL⟩ := child L k (limitsLe_trans (limitsLe_max_right _ _) le)
              exact ⟨st, by simp [materializeWith, c1, c2, runL, except_map_error, childL]⟩
            | suspended reason _ =>
              change Except.error _ = Except.error _ at found
              simp only [Except.error.injEq, Prod.mk.injEq] at found
              cases reason with
              | ticks => exact absurd found.1.symm semantic.2
              | capacity => exact absurd found.1.symm semantic.1
            | divergent _ _ =>
              change Except.error _ = Except.error _ at found
              simp only [Except.error.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, -⟩ := found
              have fail : failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks'
                  ⟨t.heap, .enter (F payload), []⟩).1 = some .divergent := by rw [forced]; rfl
              obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
              refine ⟨L1, n, fun L k le => ?_⟩
              have lz := lazy L (n + k) le (by omega)
              cases lf : ObjectiveBendDemandData.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter payload, []⟩ with
              | mk o r =>
                rw [lf] at lz
                cases o <;> simp [failureOf] at lz <;>
                  exact ⟨_, by simp [materializeWith, c1, c2, lf] <;> rfl⟩
            | refused _ _ =>
              change Except.error _ = Except.error _ at found
              simp only [Except.error.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, -⟩ := found
              have fail : failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks'
                  ⟨t.heap, .enter (F payload), []⟩).1 = some .refused := by rw [forced]; rfl
              obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
              refine ⟨L1, n, fun L k le => ?_⟩
              have lz := lazy L (n + k) le (by omega)
              cases lf : ObjectiveBendDemandData.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter payload, []⟩ with
              | mk o r =>
                rw [lf] at lz
                cases o <;> simp [failureOf] at lz <;>
                  exact ⟨_, by simp [materializeWith, c1, c2, lf] <;> rfl⟩
            | yielded _ _ =>
              change Except.error _ = Except.error _ at found
              simp only [Except.error.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, -⟩ := found
              have fail : failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks'
                  ⟨t.heap, .enter (F payload), []⟩).1 = some .yielded := by rw [forced]; rfl
              obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
              refine ⟨L1, n, fun L k le => ?_⟩
              have lz := lazy L (n + k) le (by omega)
              cases lf : ObjectiveBendDemandData.forceWith (fun _ => true) L (n + k) ⟨s.heap, .enter payload, []⟩ with
              | mk o r =>
                rw [lf] at lz
                cases o <;> simp [failureOf] at lz <;>
                  exact ⟨_, by simp [materializeWith, c1, c2, lf] <;> rfl⟩
    | record fields =>
      have fieldsIn : AllIn (Dom s.heap) (fields.map Prod.snd) := valueIn
      simp only [renameValue] at found
      simp [materializeWith_record] at found
      split at found
      · rename_i c1
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith_record, c1] <;> rfl⟩⟩
      · rename_i c1
        split at found
        · rename_i c2
          change Except.error _ = Except.error _ at found
          simp only [Except.error.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, -⟩ := found
          exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith_record, c1, c2] <;> rfl⟩⟩
        · rename_i c2
          split at found
          · rename_i c3
            have c3' : (fields.map Prod.fst).eraseDups.length = fields.length := by
              simpa [Function.comp_def] using c3
            split at found
            · rename_i c4
              change Except.error _ = Except.error _ at found
              simp only [Except.error.injEq, Prod.mk.injEq] at found
              obtain ⟨rfl, -⟩ := found
              exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith_record, c1, c2, c3', c4] <;> rfl⟩⟩
            · rename_i c4
              rw [except_map_error] at found
              obtain ⟨L0, T0, fold⟩ := sim.foldFail ih fields [] s t _ F f st' rel fieldsIn semantic found
              refine ⟨L0, T0, fun L k le => ?_⟩
              obtain ⟨st, foldL⟩ := fold L k le
              exact ⟨st, by simp [materializeWith_record, c1, c2, c3', c4, foldL, except_map_error]⟩
          · rename_i c3
            have c3' : ¬ (fields.map Prod.fst).eraseDups.length = fields.length := by
              simpa [Function.comp_def] using c3
            change Except.error _ = Except.error _ at found
            simp only [Except.error.injEq, Prod.mk.injEq] at found
            obtain ⟨rfl, -⟩ := found
            exact ⟨⟨0, 0⟩, 0, fun L k _ => ⟨(s, _), by simp [materializeWith_record, c1, c2, c3'] <;> rfl⟩⟩

/-- **Plan extraction's failure, backward**: a forced yield whose Plan extraction fails with
a failure other than `suspended` or `tickExhausted` has a lazy yield whose extraction fails with the same
failure above a threshold, with the same output nodes and bytes. -/
theorem BackSim.yieldedPlanFail {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {y y' : State} (rel : R F y y') {L' : Limits} {budget' : Budget}
    {f : Failure} {st' : State × Budget} (found : ObjectiveBendDemandData.yieldedPlan L' budget' y' = .error (f, st'))
    (semantic : (f ≠ .suspended ∧ f ≠ .tickExhausted)) :
    ∃ (L0 : Limits) (E0 : Nat), ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
      ∃ st, ObjectiveBendDemandData.yieldedPlan L ⟨budget'.nodes, E0 + k, budget'.bytes⟩ y = .error (f, st) := by
  obtain ⟨ctlEq, _⟩ := sim.renames rel
  have cIn := sim.controlIn rel
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
        simp only [except_bind_error] at found
        rcases found with childFail | ⟨_, _, bad⟩
        · obtain ⟨n, L1, v, F1, above, vEq, rel1, vIn, ext1⟩ := sim.forceWith entered forced
          subst vEq
          obtain ⟨L2, T2, child⟩ := sim.materializeFail L' _ _ v _ _ F1 f st' rel1 vIn semantic childFail
          refine ⟨limitsMax L1 L2, n + T2, fun L k le => ?_⟩
          have runL := above L (n + T2 + k) (limitsLe_trans (limitsLe_max_left _ _) le) (by omega)
          rw [show n + T2 + k - n = T2 + k by omega] at runL
          obtain ⟨st, childL⟩ := child L k (limitsLe_trans (limitsLe_max_right _ _) le)
          exact ⟨st, by simp [runL, childL] <;> rfl⟩
        · cases bad
      | suspended reason _ =>
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        cases reason with
        | ticks => exact absurd found.1.symm semantic.2
        | capacity => exact absurd found.1.symm semantic.1
      | divergent _ _ =>
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        have fail : failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks'
            ⟨y'.heap, .enter (F plan), []⟩).1 = some .divergent := by rw [forced]; rfl
        obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
        refine ⟨L1, n, fun L k le => ?_⟩
        have lz := lazy L (n + k) le (by omega)
        cases lf : ObjectiveBendDemandData.forceWith (fun _ => true) L (n + k) ⟨y.heap, .enter plan, []⟩ with
        | mk o r =>
          rw [lf] at lz
          cases o <;> simp [failureOf] at lz <;>
            exact ⟨_, by simp [hc, lf] <;> rfl⟩
      | refused _ _ =>
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        have fail : failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks'
            ⟨y'.heap, .enter (F plan), []⟩).1 = some .refused := by rw [forced]; rfl
        obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
        refine ⟨L1, n, fun L k le => ?_⟩
        have lz := lazy L (n + k) le (by omega)
        cases lf : ObjectiveBendDemandData.forceWith (fun _ => true) L (n + k) ⟨y.heap, .enter plan, []⟩ with
        | mk o r =>
          rw [lf] at lz
          cases o <;> simp [failureOf] at lz <;>
            exact ⟨_, by simp [hc, lf] <;> rfl⟩
      | yielded _ _ =>
        change Except.error _ = Except.error _ at found
        simp only [Except.error.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, -⟩ := found
        have fail : failureOf (ObjectiveBendDemandData.forceWith (fun _ => true) L' ticks'
            ⟨y'.heap, .enter (F plan), []⟩).1 = some .yielded := by rw [forced]; rfl
        obtain ⟨L1, n, lazy⟩ := sim.forceFail entered fail semantic
        refine ⟨L1, n, fun L k le => ?_⟩
        have lz := lazy L (n + k) le (by omega)
        cases lf : ObjectiveBendDemandData.forceWith (fun _ => true) L (n + k) ⟨y.heap, .enter plan, []⟩ with
        | mk o r =>
          rw [lf] at lz
          cases o <;> simp [failureOf] at lz <;>
            exact ⟨_, by simp [hc, lf] <;> rfl⟩
  | _ =>
    rw [ctlEq, hc] at found
    simp only [renameControl] at found
    change Except.error _ = Except.error _ at found
    simp only [Except.error.injEq, Prod.mk.injEq] at found
    exact absurd found.1.symm semantic.1

/-- **Completion's failure, backward.** -/
theorem BackSim.completeFail {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {y y' : State} (rel : R F y y') {L' : Limits} {budget' : Budget}
    {f : Failure} {st' : State × Budget} (found : ObjectiveBendDemandData.complete L' budget' y' = .error (f, st'))
    (semantic : (f ≠ .suspended ∧ f ≠ .tickExhausted)) :
    ∃ (L0 : Limits) (E0 : Nat), ∀ (L : Limits) (k : Nat), LimitsLe L0 L →
      ∃ st, ObjectiveBendDemandData.complete L ⟨budget'.nodes, E0 + k, budget'.bytes⟩ y = .error (f, st) := by
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
      rw [except_bind_error] at found
      rcases found with mFail | ⟨a', materialized, rest⟩
      · obtain ⟨L0, T0, m⟩ := sim.materializeFail L' nodes ⟨nodes, ticks', bytes⟩ v y y' F f st' rel cIn semantic mFail
        refine ⟨L0, T0, fun L k le => ?_⟩
        obtain ⟨st, mL⟩ := m L k le
        exact ⟨st, by simp [hc, hs, mL, bind, Except.bind]⟩
      · obtain ⟨L0, T0, st, F', rel', ext', child⟩ := sim.materialize L' _ _ v _ _ F a' rel cIn materialized
        refine ⟨L0, T0, fun L k le => ?_⟩
        have childL := child L k le
        split at rest
        · rename_i encodedBytes encodedAt
          split at rest
          · rename_i big
            change Except.error _ = Except.error _ at rest
            simp only [Except.error.injEq, Prod.mk.injEq] at rest
            obtain ⟨rfl, -⟩ := rest
            exact ⟨(st, _), by simp [hc, hs, childL, encodedAt, big, bind, Except.bind] <;> rfl⟩
          · cases rest
        · rename_i noEnc
          change Except.error _ = Except.error _ at rest
          simp only [Except.error.injEq, Prod.mk.injEq] at rest
          obtain ⟨rfl, -⟩ := rest
          cases enc : encoded nodes a'.value with
          | some b => exact absurd enc (noEnc b)
          | none => exact ⟨(st, _), by simp [hc, hs, childL, enc, bind, Except.bind] <;> rfl⟩
    | cons fr rest =>
      rw [ctlEq, stEq, hc, hs] at found
      simp at found
      exact absurd found.1.symm semantic.1
  | _ =>
    rw [ctlEq, hc] at found
    simp [renameControl] at found
    exact absurd found.1.symm semantic.1

/-! ## Segments that end in a failed extraction -/

/-- The extraction failure a segment ends with: its bounded run halted in a yield or a
completion, and that extraction failed (`none`: anything else). -/
def failsWith (L : Limits) (T : Nat) (budget : Budget) (s : State) : Option Failure :=
  match ObjectiveBendDemandMachine.runBounded L T s with
  | .yielded _ y => match ObjectiveBendDemandData.yieldedPlan L budget y with
    | .error (f, _) => some f
    | .ok _ => none
  | .finished _ y => match ObjectiveBendDemandData.complete L budget y with
    | .error (f, _) => some f
    | .ok _ => none
  | _ => none

/-- **A failure above a threshold**: under every resource vector at least `(L0, T0, E0)`, with
the same output nodes and bytes, the segment from `s` ends with extraction failure `f`. -/
def FailsAbove (s : State) (budget : Budget) (f : Failure) : Prop :=
  ∃ (L0 : Limits) (T0 E0 : Nat), ∀ (L : Limits) (T k : Nat), LimitsLe L0 L → T0 ≤ T →
    failsWith L T ⟨budget.nodes, E0 + k, budget.bytes⟩ s = some f

/-- A segment that ends in a failed extraction halted. -/
theorem failsWith_halts {L : Limits} {T : Nat} {budget : Budget} {s : State} {f : Failure}
    (ran : failsWith L T budget s = some f) : ∃ n, Halts s n := by
  have notSusp : ∀ r st, ObjectiveBendDemandMachine.runBounded L T s ≠ .suspended r st := by
    intro r st h; unfold failsWith at ran; rw [h] at ran; cases ran
  obtain ⟨n, _, halts, _, _⟩ := runBounded_halts L T s notSusp
  exact ⟨n, halts⟩

/-- A segment that ends in a failed extraction ends no segment. -/
theorem endsWith_of_failsWith {L : Limits} {T : Nat} {budget : Budget} {s : State} {f : Failure}
    (ran : failsWith L T budget s = some f) : endsWith L T budget s = none := by
  unfold failsWith at ran
  unfold endsWith
  cases hr : ObjectiveBendDemandMachine.runBounded L T s with
  | yielded p y =>
    rw [hr] at ran
    simp only at ran ⊢
    cases hp : ObjectiveBendDemandData.yieldedPlan L budget y with
    | ok r => rw [hp] at ran; cases ran
    | error e => try simp [hp]
  | finished v y =>
    rw [hr] at ran
    simp only at ran ⊢
    cases hp : ObjectiveBendDemandData.complete L budget y with
    | ok r => rw [hp] at ran; cases ran
    | error e => try simp [hp]
  | _ => simp only [hr] at ran; cases ran

/-- **A segment's extraction failure, backward.** -/
theorem BackSim.failsBack {R : (Nat → Nat) → State → State → Prop} {Dom : Array Cell → Nat → Prop}
    (sim : BackSim R Dom) {F : Nat → Nat} {s t : State} (rel : R F s t) {L' : Limits} {T' : Nat}
    {budget' : Budget} {f : Failure} (ran : failsWith L' T' budget' t = some f) (semantic : (f ≠ .suspended ∧ f ≠ .tickExhausted)) :
    FailsAbove s budget' f := by
  have notSusp : ∀ r st, ObjectiveBendDemandMachine.runBounded L' T' t ≠ .suspended r st := by
    intro r st h; unfold failsWith at ran; rw [h] at ran; cases ran
  obtain ⟨n, n', L1, F1, rel1, eqT, _, lazy⟩ := sim.runBounded rel notSusp
  have ctl := (sim.renames rel1).1
  unfold failsWith at ran
  rw [eqT] at ran
  cases hc : (exec n s).control with
  | yielded p =>
    rw [hc] at ctl
    simp only [ObjectiveBendDemandMachine.runBounded, ctl, renameControl] at ran
    split at ran
    · rename_i f' st' found
      cases ran
      obtain ⟨L2, E0, h⟩ := sim.yieldedPlanFail rel1 found semantic
      refine ⟨limitsMax L1 L2, n, E0, fun L T k le nle => ?_⟩
      have run := lazy L T (limitsLe_trans (limitsLe_max_left _ _) le) nle
      obtain ⟨st, ext⟩ := h L k (limitsLe_trans (limitsLe_max_right _ _) le)
      simp [failsWith, run, ObjectiveBendDemandMachine.runBounded, hc, ext]
    · cases ran
  | complete v =>
    rw [hc] at ctl
    simp only [ObjectiveBendDemandMachine.runBounded, ctl, renameControl] at ran
    split at ran
    · rename_i f' st' found
      cases ran
      obtain ⟨L2, E0, h⟩ := sim.completeFail rel1 found semantic
      refine ⟨limitsMax L1 L2, n, E0, fun L T k le nle => ?_⟩
      have run := lazy L T (limitsLe_trans (limitsLe_max_left _ _) le) nle
      obtain ⟨st, ext⟩ := h L k (limitsLe_trans (limitsLe_max_right _ _) le)
      simp [failsWith, run, ObjectiveBendDemandMachine.runBounded, hc, ext]
    · cases ran
  | _ =>
    rw [hc] at ctl
    simp [ObjectiveBendDemandMachine.runBounded, ctl, renameControl] at ran

/-- **Along a chain: a semantic extraction failure is the lazy state's own.** Whatever
extraction failure other than `suspended` or `tickExhausted` the normalized state's segment ends with (under
some resources), the lazy state's segment ends with the SAME failure under every resource
vector above a threshold, with the same output nodes and bytes. -/
theorem Chain.failsBack {s t : State} (h : Chain s t) :
    ∀ {L' : Limits} {T' : Nat} {budget' : Budget} {f : Failure},
      failsWith L' T' budget' t = some f → (f ≠ .suspended ∧ f ≠ .tickExhausted) → FailsAbove s budget' f := by
  induction h with
  | forces r => exact fun ran semantic => (forcesSim _).failsBack r ran semantic
  | settles a => exact fun ran semantic => settleSim.failsBack ⟨rfl, a⟩ ran semantic
  | @collects f D _ _ r => exact fun ran semantic => (relatedSim f D).failsBack ⟨rfl, r⟩ ran semantic
  | trans _ _ ih1 ih2 =>
    intro L' T' budget' f ran semantic
    obtain ⟨L0, T0, E0, above⟩ := ih2 ran semantic
    exact ih1 (budget' := ⟨budget'.nodes, E0 + 0, budget'.bytes⟩) (above L0 T0 0 (limitsLe_refl _) (Nat.le_refl _))
      semantic

open Minidregg.Theory.ObjectiveBendInteraction (node ending Node) in
/-- **A semantic extraction failure is the reference's `malformed`.** A normalized state
whose segment ends (under some resources) in a yield or a completion whose extraction fails
with anything but `suspended` or `tickExhausted` is in a chain with a lazy state whose reference node is
`malformed`: it halts, and no resources make its Plan or result Data within the output
sizes. -/
theorem node_malformed_of_chain {s t : State} (h : Chain s t) {L' : Limits} {T' : Nat} {budget : Budget}
    {f : Failure} (ran : failsWith L' T' budget t = some f) (semantic : (f ≠ .suspended ∧ f ≠ .tickExhausted)) :
    node budget s = .malformed := by
  obtain ⟨L0, T0, E0, fails⟩ := h.failsBack ran semantic
  obtain ⟨n, halts⟩ := failsWith_halts (fails L0 T0 0 (limitsLe_refl _) (Nat.le_refl _))
  unfold node
  cases hEnd : ending budget s with
  | some p =>
    exfalso
    unfold ending at hEnd
    split at hEnd
    · rename_i hex
      have spec := Classical.choose_spec hex
      rw [Option.some.injEq] at hEnd
      rw [hEnd] at spec
      obtain ⟨L1, T1, E1, above⟩ := spec
      have a := above (limitsMax L0 L1) (T0 + T1) E0 (limitsLe_max_right _ _) (by omega)
      have c := fails (limitsMax L0 L1) (T0 + T1) E1 (limitsLe_max_left _ _) (by omega)
      rw [Nat.add_comm E0 E1] at c
      rw [endsWith_of_failsWith c] at a
      cases a
    · cases hEnd
  | none =>
    simp only
    rw [if_pos ⟨n, halts⟩]

/-! ## `suspended` is a resource failure -/

/-- A yield whose Plan is one suspended cell. -/
def suspendedYield : State := ⟨#[.suspended ⟨.nat 1, []⟩], .yielded 0, []⟩

def suspendedCheck : Bool :=
  (match ObjectiveBendDemandData.yieldedPlan ⟨8, 8⟩ ⟨8, 0, 64⟩ suspendedYield with
    | .error (.tickExhausted, _) => true
    | _ => false) &&
  (match ObjectiveBendDemandData.yieldedPlan ⟨8, 8⟩ ⟨8, 16, 64⟩ suspendedYield with
    | .ok _ => true
    | .error _ => false)

theorem suspendedCheck_true : suspendedCheck = true := by decide +kernel

/-- **Tick suspension does not transfer: it is a resource failure.** One yield, one heap and stack
room, the same output nodes and bytes: with no extraction ticks its Plan extraction fails
`tickExhausted`, with 16 it succeeds. (So the backward theorems above exclude it, and a kernel
fault "plan extraction: tickExhausted" is a statement about the envelope, not the program.) -/
theorem suspended_is_resource :
    ∃ st r, ObjectiveBendDemandData.yieldedPlan ⟨8, 8⟩ ⟨8, 0, 64⟩ suspendedYield = .error (.tickExhausted, st) ∧
      ObjectiveBendDemandData.yieldedPlan ⟨8, 8⟩ ⟨8, 16, 64⟩ suspendedYield = .ok r := by
  have checked := suspendedCheck_true
  unfold suspendedCheck at checked
  rw [Bool.and_eq_true] at checked
  obtain ⟨one, two⟩ := checked
  split at one
  · rename_i st found
    split at two
    · rename_i r ok
      exact ⟨st, r, found, ok⟩
    · cases two
  · cases one

#assert_axioms failureOf_rename BackSim.forceFail except_map_error except_bind_error
#assert_axioms BackSim.foldFail BackSim.materializeFail BackSim.yieldedPlanFail BackSim.completeFail
#assert_axioms failsWith_halts endsWith_of_failsWith BackSim.failsBack Chain.failsBack node_malformed_of_chain
#assert_axioms suspendedCheck_true suspended_is_resource

end Minidregg.Theory.ObjectiveBendDemandForcing
