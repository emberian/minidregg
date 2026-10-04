/- The update-frame discipline and closed demands (forcing transparency, part 2).

* `persist_step`: an update frame below the top stays until a returned value pops it.
* `nested_pop` / `nested_demand`: an entered suspended cell's frame stays, with no other
  frame for that cell above it, and the cell stays evaluating, until a returned value pops
  the frame and caches the cell; the run until then is the cell's closed demand with the
  outer stack appended, and that demand finishes (`Demand`).
* `demand_props`: a finished closed demand of a suspended cell takes at least four
  transitions, caches the cell with its result, and runs the same over any outer stack. -/
import Theory.ObjectiveBendDemandForcingRun
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
set_option autoImplicit false

/-- Away from a returned value, a transition keeps the stack or pushes one frame. -/
theorem stepRaw_stack_grows (s : State) (notReturned : ∀ v, s.control ≠ .returned v) :
    (stepRaw s).stack = s.stack ∨ ∃ fr, (stepRaw s).stack = fr :: s.stack := by
  obtain ⟨heap, control, stack⟩ := s
  cases control with
  | returned v => exact absurd rfl (notReturned v)
  | complete _ | refused _ | blackhole _ | yielded _ => left; rfl
  | enter a => simp only [stepRaw]; split <;> simp
  | evaluate term env => cases term <;> simp only [stepRaw] <;> (try split) <;> simp

/-- Only a returned value consumes the top frame. -/
theorem stepRaw_consumes_returned (s : State) {fr : Frame} {rest : List Frame} (stack : s.stack = fr :: rest)
    (consumed : (stepRaw s).stack = rest ∨ ∃ fr', (stepRaw s).stack = fr' :: rest ∧ fr' ≠ fr) :
    ∃ v, s.control = .returned v := by
  by_cases r : ∃ v, s.control = .returned v
  · exact r
  · have notReturned : ∀ v, s.control ≠ .returned v := fun v h => r ⟨v, h⟩
    rcases stepRaw_stack_grows s notReturned with same | ⟨fr'', push⟩ <;>
      rcases consumed with h | ⟨fr', h, ne⟩
    · rw [same, stack] at h; have := congrArg List.length h; simp at this
    · rw [same, stack] at h; simp at h; exact absurd h.symm ne
    · rw [push, stack] at h; have := congrArg List.length h; simp at this; omega
    · rw [push, stack] at h; simp at h

/-- The update-frame discipline: an update frame below the top stays until popped,
and it is popped only from a returned value. -/
theorem persist_step {s : State} {w : Nat} {R Y : List Frame} (h : s.stack = Y ++ .update w :: R) :
    (∃ Y', (stepRaw s).stack = Y' ++ .update w :: R) ∨
      (Y = [] ∧ (stepRaw s).stack = R ∧ ∃ v, s.control = .returned v) := by
  rcases stepRaw_stack_shape s with same | ⟨fr, push⟩ | ⟨fr, rest, eq, notUpdate, fr', next⟩ | ⟨fr, rest, eq, next⟩
  · exact Or.inl ⟨Y, by rw [same, h]⟩
  · exact Or.inl ⟨fr :: Y, by rw [push, h]; rfl⟩
  · cases Y with
    | nil =>
      rw [h] at eq; simp at eq; exact absurd eq.1.symm (notUpdate w)
    | cons y ys =>
      rw [h] at eq; simp at eq
      exact Or.inl ⟨fr' :: ys, by rw [next, ← eq.2]; rfl⟩
  · cases Y with
    | nil =>
      rw [h] at eq; simp at eq
      refine Or.inr ⟨rfl, by rw [next, ← eq.2], ?_⟩
      exact stepRaw_consumes_returned s (by rw [h]; rfl) (Or.inl (by rw [next, ← eq.2]))
    | cons y ys =>
      rw [h] at eq; simp at eq
      exact Or.inl ⟨ys, by rw [next, ← eq.2]⟩


/-- Only entering a cell pushes its update frame. -/
theorem stepRaw_push_update (s : State) {fr : Frame} (push : (stepRaw s).stack = fr :: s.stack)
    {a : Nat} (isUpdate : fr = .update a) : s.control = .enter a := by
  subst isUpdate
  obtain ⟨heap, control, stack⟩ := s
  have lenFalse : ∀ (l : List Frame) (x : Frame), l ≠ x :: l := fun l x h => by
    have := congrArg List.length h; simp at this
  have lenFalse2 : ∀ (l : List Frame) (x y : Frame), l ≠ x :: y :: l := fun l x y h => by
    have := congrArg List.length h; simp at this; omega
  cases control with
  | enter b =>
    simp only [stepRaw] at push
    split at push <;> simp at push
    all_goals first | (subst push; rfl) | exact absurd push (lenFalse _ _)
  | complete _ | refused _ | blackhole _ | yielded _ =>
    simp [stepRaw] at push <;> exact absurd push (lenFalse _ _)
  | evaluate term env =>
    cases term <;> simp only [stepRaw] at push <;> (try split at push) <;> simp at push <;>
      exact absurd push (lenFalse _ _)
  | returned v =>
    cases stack with
    | nil => simp [stepRaw] at push
    | cons frame rest =>
      cases frame <;> simp only [stepRaw] at push <;> (try split at push) <;> (try split at push) <;>
        (try split at push) <;> simp at push <;>
        first | exact absurd push (lenFalse2 _ _ _) | exact absurd push.2 (lenFalse2 _ _ _) | skip

/-- A transition never writes an update frame over another top frame. -/
theorem stepRaw_top_update (s : State) {fr : Frame} {rest : List Frame} (stack : s.stack = fr :: rest)
    {a : Nat} (next : (stepRaw s).stack = .update a :: rest) : fr = .update a := by
  by_cases r : ∃ v, s.control = .returned v
  · obtain ⟨v, hv⟩ := r
    obtain ⟨heap, control, stack'⟩ := s
    simp only at stack hv; subst stack hv
    cases fr <;> simp only [stepRaw] at next <;> (try split at next) <;> (try split at next) <;>
      (try split at next) <;> simp at next <;>
      first | rfl | (have := congrArg List.length next; simp at this) | skip
  · have notReturned : ∀ v, s.control ≠ .returned v := fun v h => r ⟨v, h⟩
    rcases stepRaw_stack_grows s notReturned with same | ⟨fr'', push⟩
    · rw [same, stack] at next; simp at next; exact next
    · rw [push, stack] at next; have := congrArg List.length next; simp at this

theorem exec_zero (s : State) : exec 0 s = s := rfl

theorem stepRaw_enter_evaluating {s : State} {b : Nat} {o : Closure} (ctl : s.control = .enter b)
    (ev : s.heap[b]? = some (.evaluating o)) : (stepRaw s).control = .blackhole b := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl ev; subst ctl
  simp [stepRaw, ev]

theorem stepRaw_pop_update {s : State} {w : Nat} {o : Closure} {v : RuntimeValue} {R : List Frame}
    (ctl : s.control = .returned v) (st : s.stack = .update w :: R) (ev : s.heap[w]? = some (.evaluating o)) :
    stepRaw s = ⟨s.heap.set! w (.cached o v), .returned v, R⟩ := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl st ev; subst ctl st
  simp [stepRaw, ev]

theorem stepRaw_enter_suspended {s : State} {b : Nat} {o : Closure} (ctl : s.control = .enter b)
    (su : s.heap[b]? = some (.suspended o)) :
    stepRaw s = ⟨s.heap.set! b (.evaluating o), .evaluate o.term o.environment, .update b :: s.stack⟩ := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl su; subst ctl
  simp [stepRaw, su]

theorem exists_first_fail {P : Nat → Prop} (h : ∃ m, ¬ P m) : ∃ m, ¬ P m ∧ ∀ m', m' < m → P m' := by
  classical
  obtain ⟨m, hm⟩ := h
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases all : ∀ m', m' < m → P m'
    · exact ⟨m, hm, all⟩
    · have : ∃ m', m' < m ∧ ¬ P m' := by
        apply Classical.byContradiction; intro hc; apply all; intro m' lt
        apply Classical.byContradiction; intro hp; exact hc ⟨m', lt, hp⟩
      obtain ⟨m', lt, hp⟩ := this
      exact ih m' lt hp

/-- **An entered suspended cell's evaluation.** Its update frame stays on the stack, with
no other update frame for it above, and the cell stays evaluating, until a returned value
pops the frame and caches the cell. -/
theorem nested_pop {σ : State} {w : Nat} {o : Closure} {R : List Frame} {k : Nat}
    (enter : σ.control = .enter w) (stack : σ.stack = R) (susp : σ.heap[w]? = some (.suspended o))
    (pos : 1 ≤ k) (alive : ∀ j, j < k → active (exec j σ).control = true)
    (gone : ∀ Y, (exec k σ).stack ≠ Y ++ .update w :: R) :
    ∃ p v, 1 ≤ p ∧ p < k ∧
      (∀ j, 1 ≤ j → j ≤ p → (∃ Y, (exec j σ).stack = Y ++ .update w :: R ∧ ∀ fr ∈ Y, fr ≠ .update w) ∧
        (exec j σ).heap[w]? = some (.evaluating o)) ∧
      (exec p σ).stack = .update w :: R ∧ (exec p σ).control = .returned v ∧
      exec (p+1) σ = ⟨(exec p σ).heap.set! w (.cached o v), .returned v, R⟩ := by
  classical
  have wBound : w < σ.heap.size := bound_of_some susp
  have one : exec 1 σ = ⟨σ.heap.set! w (.evaluating o), .evaluate o.term o.environment, .update w :: R⟩ := by
    rw [exec_one, stepRaw_enter_suspended enter susp, stack]
  let P : Nat → Prop := fun m => ∃ Y, (exec (m+1) σ).stack = Y ++ .update w :: R
  have exists_fail : ∃ m, ¬ P m := ⟨k - 1, fun ⟨Y, h⟩ => gone Y (by rw [show k = k - 1 + 1 by omega]; exact h)⟩
  obtain ⟨p, pFail, pMin⟩ := exists_first_fail exists_fail
  have pPos : 1 ≤ p := by
    by_cases zero : p = 0
    · exfalso; apply pFail; rw [zero]; exact ⟨[], by rw [one]; rfl⟩
    · omega
  have pLt : p < k := by
    apply Classical.byContradiction; intro ge
    obtain ⟨Y, h⟩ := pMin (k - 1) (by omega)
    exact gone Y (by rw [show k = k - 1 + 1 by omega]; exact h)
  -- the invariant from 1 to p
  have inv : ∀ j, 1 ≤ j → j ≤ p →
      (∃ Y, (exec j σ).stack = Y ++ .update w :: R ∧ ∀ fr ∈ Y, fr ≠ .update w) ∧
        (exec j σ).heap[w]? = some (.evaluating o) := by
    intro j hj hjp
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases jzero : j = 0
      · subst jzero
        rw [one]
        refine ⟨⟨[], rfl, fun _ m => by cases m⟩, ?_⟩
        simp [wBound]
      · obtain ⟨⟨Y, hY, noW⟩, evalW⟩ := ih (by omega) (by omega)
        obtain ⟨Y', hY'⟩ := pMin j (by omega)
        have hY'' : (exec (j+1) σ).stack = Y' ++ .update w :: R := hY'
        rw [exec_succ] at hY''
        -- no read of w at step j
        have noRead : readsAt (exec j σ) ≠ some w := by
          intro reads
          cases ctl : (exec j σ).control with
          | enter b =>
            have : b = w := by simp [readsAt, ctl] at reads; exact reads
            subst this
            have blk : (stepRaw (exec j σ)).control = .blackhole b := stepRaw_enter_evaluating ctl evalW
            have := alive (j + 1) (by omega)
            rw [exec_succ, blk] at this; simp [active] at this
          | returned v =>
            have top : ∃ rest, (exec j σ).stack = .update w :: rest := by
              cases st : (exec j σ).stack with
              | nil => simp [readsAt, ctl, st] at reads
              | cons fr rest =>
                cases fr <;> simp [readsAt, ctl, st] at reads
                exact ⟨rest, by rw [reads]⟩
            obtain ⟨rest, top⟩ := top
            have yNil : Y = [] := by
              cases Y with
              | nil => rfl
              | cons y ys =>
                rw [hY] at top; simp at top
                exact absurd top.1 (noW y (List.mem_cons_self ..))
            subst yNil
            simp at hY
            have popped : (stepRaw (exec j σ)).stack = R := by
              rw [stepRaw_pop_update ctl hY evalW]
            rw [popped] at hY''
            have := congrArg List.length hY''; simp at this; omega
          | _ => simp [readsAt, ctl] at reads
        have keepW : (stepRaw (exec j σ)).heap[w]? = (exec j σ).heap[w]? :=
          stepRaw_heap_keep _ (bound_of_some evalW) noRead
        refine ⟨⟨Y', by rw [exec_succ]; exact hY'', ?_⟩, by rw [exec_succ, keepW]; exact evalW⟩
        -- no update w in Y'
        rcases stepRaw_stack_shape (exec j σ) with same | ⟨fr, push⟩ | ⟨fr, rest, eq, notUpd, fr', next⟩ |
            ⟨fr, rest, eq, next⟩
        · rw [same, hY] at hY''
          have := List.append_cancel_right hY''
          subst this; exact noW
        · rw [push, hY] at hY''
          have := List.append_cancel_right (show (fr :: Y) ++ Frame.update w :: R = Y' ++ Frame.update w :: R by
            simpa using hY'')
          subst this
          intro f mem
          rcases List.mem_cons.mp mem with rfl | mem
          · intro isW
            have := stepRaw_push_update _ push isW
            exact noRead (by simp [readsAt, this])
          · exact noW f mem
        · cases Y with
          | nil => rw [hY] at eq; simp at eq; exact absurd eq.1.symm (notUpd w)
          | cons y ys =>
            rw [hY] at eq; simp at eq
            obtain ⟨rfl, rfl⟩ := eq
            rw [next] at hY''
            have := List.append_cancel_right (show (fr' :: ys) ++ Frame.update w :: R = Y' ++ Frame.update w :: R by
              simpa using hY'')
            subst this
            intro f mem
            rcases List.mem_cons.mp mem with rfl | mem
            · intro isW
              have := stepRaw_top_update (exec j σ) hY (by rw [next, isW]; rfl)
              exact noW _ (List.mem_cons_self ..) this
            · exact noW f (List.mem_cons_of_mem _ mem)
        · cases Y with
          | nil =>
            rw [hY] at eq; simp at eq
            rw [next, ← eq.2] at hY''
            have := congrArg List.length hY''; simp at this; omega
          | cons y ys =>
            rw [hY] at eq; simp at eq
            rw [next, ← eq.2] at hY''
            have := List.append_cancel_right hY''
            subst this
            exact fun f mem => noW f (List.mem_cons_of_mem _ mem)
  obtain ⟨⟨Yp, hYp, noWp⟩, evalp⟩ := inv p pPos (Nat.le_refl _)
  rcases persist_step hYp with ⟨Y', h⟩ | ⟨rfl, popped, v, ctl⟩
  · exact absurd ⟨Y', by rw [exec_succ]; exact h⟩ pFail
  · refine ⟨p, v, pPos, pLt, inv, by simpa using hYp, ctl, ?_⟩
    rw [exec_succ]
    exact stepRaw_pop_update ctl (by simpa using hYp) evalp

/-! ## Halting runs and closed demands -/

/-- The run from `s` is active for its first `n` states and stops at the `n`-th. -/
def Halts (s : State) (n : Nat) : Prop :=
  (∀ j, j < n → active (exec j s).control = true) ∧ active (exec n s).control = false

theorem halts_unique {s : State} {n m : Nat} (one : Halts s n) (two : Halts s m) : n = m := by
  apply Classical.byContradiction; intro ne
  rcases Nat.lt_or_gt_of_ne ne with lt | lt
  · have := two.1 n lt; rw [one.2] at this; cases this
  · have := one.1 m lt; rw [two.2] at this; cases this

/-- The closed demand of `w` on `P`: enter it with an empty stack. -/
def demandStart (P : Array Cell) (w : Nat) : State := ⟨P, .enter w, []⟩

/-- The closed demand of `w` on `P` finishes in `n` transitions with `v`, leaving `Pf`. -/
structure Demand (P : Array Cell) (w n : Nat) (Pf : Array Cell) (v : RuntimeValue) : Prop where
  halts : Halts (demandStart P w) n
  final : exec n (demandStart P w) = ⟨Pf, .complete v, []⟩

theorem withStack_nil (s : State) : withStack s [] = s := by
  obtain ⟨h, c, st⟩ := s; simp [withStack]

theorem frame_run {s : State} {R : List Frame} {m : Nat} (safe : ∀ j, j < m → FrameSafe (exec j s)) :
    ∀ j, j ≤ m → exec j (withStack s R) = withStack (exec j s) R := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih => rw [exec_succ, exec_succ, ih (by omega), stepRaw_withStack _ _ (safe j (by omega))]

theorem frameSafe_of_update {s : State} {w : Nat} {Y : List Frame} (h : s.stack = Y ++ [.update w]) :
    FrameSafe s := by
  refine ⟨fun _ _ => by rw [h]; simp, fun _ _ _ => ?_⟩
  rw [h]; simp [forcingShared]

theorem frameSafe_enter {s : State} {w : Nat} (h : s.control = .enter w) : FrameSafe s :=
  ⟨fun _ hv => (by rw [h] at hv; cases hv), fun _ _ hp => (by rw [h] at hp; cases hp)⟩

theorem withStack_inj {s : State} {h : Array Cell} {c : Control} {st R : List Frame}
    (eq : withStack s R = ⟨h, c, st ++ R⟩) : s = ⟨h, c, st⟩ := by
  obtain ⟨h', c', st'⟩ := s
  simp only [withStack, State.mk.injEq] at eq
  obtain ⟨rfl, rfl, e⟩ := eq
  rw [List.append_cancel_right e]

/-- **The nested evaluation is a closed demand.** Until the entered cell's frame pops, the
run is the closed demand of that cell with the outer stack appended, and that demand
finishes. -/
theorem nested_demand {σ : State} {w : Nat} {o : Closure} {R : List Frame} {k : Nat}
    (enter : σ.control = .enter w) (stack : σ.stack = R) (susp : σ.heap[w]? = some (.suspended o))
    (pos : 1 ≤ k) (alive : ∀ j, j < k → active (exec j σ).control = true)
    (gone : ∀ Y, (exec k σ).stack ≠ Y ++ .update w :: R) :
    ∃ p v, 1 ≤ p ∧ p < k ∧
      (∀ j, 1 ≤ j → j ≤ p → (∃ Y, (exec j σ).stack = Y ++ .update w :: R ∧ ∀ fr ∈ Y, fr ≠ .update w) ∧
        (exec j σ).heap[w]? = some (.evaluating o)) ∧
      (exec p σ).stack = .update w :: R ∧ (exec p σ).control = .returned v ∧
      exec (p+1) σ = ⟨(exec p σ).heap.set! w (.cached o v), .returned v, R⟩ ∧
      (∀ j, j ≤ p + 1 → exec j σ = withStack (exec j (demandStart σ.heap w)) R) ∧
      Demand σ.heap w (p + 2) ((exec p σ).heap.set! w (.cached o v)) v := by
  obtain ⟨p, v, pPos, pLt, inv, stP, ctlP, nextP⟩ := nested_pop enter stack susp pos alive gone
  have start : σ = withStack (demandStart σ.heap w) R := by
    obtain ⟨h, c, st⟩ := σ; simp only at enter stack; subst enter stack; rfl
  have strip : ∀ j, j ≤ p + 1 → exec j σ = withStack (exec j (demandStart σ.heap w)) R := by
    -- frame safety, proved together with the stripping by induction
    intro j hj
    induction j with
    | zero => exact start
    | succ j ih =>
      have eq := ih (by omega)
      have safe : FrameSafe (exec j (demandStart σ.heap w)) := by
        by_cases jz : j = 0
        · subst jz; exact frameSafe_enter (w := w) rfl
        · obtain ⟨⟨Y, hY, _⟩, _⟩ := inv j (by omega) (by omega)
          rw [eq] at hY
          have : (exec j (demandStart σ.heap w)).stack ++ R = (Y ++ [.update w]) ++ R := by
            simpa [withStack] using hY
          exact frameSafe_of_update (List.append_cancel_right this)
      rw [exec_succ, exec_succ, eq, stepRaw_withStack _ _ safe]
  have lastEq : exec (p+1) (demandStart σ.heap w) = ⟨(exec p σ).heap.set! w (.cached o v), .returned v, []⟩ := by
    have := strip (p + 1) (Nat.le_refl _)
    rw [nextP] at this
    exact withStack_inj (st := []) (by rw [← this]; rfl)
  refine ⟨p, v, pPos, pLt, inv, stP, ctlP, nextP, strip, ⟨fun j hj => ?_, ?_⟩, ?_⟩
  · by_cases last : j = p + 1
    · subst last; rw [lastEq]; rfl
    · have := strip j (by omega)
      have ctl := congrArg State.control this
      simp only [withStack] at ctl
      rw [← ctl]; exact alive j (by omega)
  · rw [show p + 2 = (p + 1) + 1 by omega, exec_succ, lastEq]; rfl
  · rw [show p + 2 = (p + 1) + 1 by omega, exec_succ, lastEq]; rfl

/-- **A finished closed demand of a suspended cell**: it takes at least four transitions,
caches the cell with its result, returns that result one transition before it stops, and
runs the same over any stack appended below. -/
theorem demand_props {P : Array Cell} {w n : Nat} {Pf : Array Cell} {v : RuntimeValue} {o : Closure}
    (d : Demand P w n Pf v) (susp : P[w]? = some (.suspended o)) :
    4 ≤ n ∧ Pf[w]? = some (.cached o v) ∧ exec (n-1) (demandStart P w) = ⟨Pf, .returned v, []⟩ ∧
      (∀ j, 1 ≤ j → j ≤ n - 2 → ∃ Y, (exec j (demandStart P w)).stack = Y ++ [.update w]) ∧
      (∀ (R : List Frame) j, j ≤ n - 1 → exec j ⟨P, .enter w, R⟩ = withStack (exec j (demandStart P w)) R) := by
  have pos : 1 ≤ n := by
    apply Classical.byContradiction; intro h
    have := d.halts.2; rw [show n = 0 by omega] at this; simp [exec, demandStart, active] at this
  have gone : ∀ Y, (exec n (demandStart P w)).stack ≠ Y ++ [.update w] := by
    intro Y h; rw [d.final] at h; have := congrArg List.length h; simp at this
  obtain ⟨p, v', pPos, pLt, inv, stP, ctlP, nextP, strip, d'⟩ :=
    nested_demand (σ := demandStart P w) (R := []) rfl rfl susp pos d.halts.1 gone
  have nEq : n = p + 2 := halts_unique d.halts d'.halts
  subst nEq
  have finEq := d.final.symm.trans d'.final
  simp only [State.mk.injEq, Control.complete.injEq] at finEq
  obtain ⟨heapEq, valEq, -⟩ := finEq
  subst valEq
  have p2 : 2 ≤ p := by
    apply Classical.byContradiction; intro h
    have p1 : p = 1 := by omega
    subst p1
    have := stepRaw_enter_suspended (s := demandStart P w) rfl susp
    rw [← exec_one] at this
    rw [this] at ctlP; cases ctlP
  have wBound : w < (exec p (demandStart P w)).heap.size := bound_of_some (inv p pPos (Nat.le_refl _)).2
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [heapEq]; simp [wBound]
  · rw [show p + 2 - 1 = p + 1 by omega, nextP, heapEq]
  · intro j hj hjp
    obtain ⟨⟨Y, hY, _⟩, _⟩ := inv j hj (by omega)
    exact ⟨Y, hY⟩
  · intro R j hj
    have safe : ∀ i, i < p + 1 → FrameSafe (exec i (demandStart P w)) := by
      intro i hi
      by_cases iz : i = 0
      · subst iz; exact frameSafe_enter (w := w) rfl
      · obtain ⟨⟨Y, hY, _⟩, _⟩ := inv i (by omega) (by omega)
        exact frameSafe_of_update hY
    exact frame_run safe j (by omega)

#assert_axioms stepRaw_stack_grows
#assert_axioms stepRaw_consumes_returned
#assert_axioms persist_step
#assert_axioms stepRaw_push_update
#assert_axioms stepRaw_top_update
#assert_axioms exists_first_fail
#assert_axioms stepRaw_enter_evaluating
#assert_axioms stepRaw_pop_update
#assert_axioms stepRaw_enter_suspended
#assert_axioms nested_pop
#assert_axioms halts_unique
#assert_axioms withStack_nil
#assert_axioms frame_run
#assert_axioms frameSafe_of_update
#assert_axioms withStack_inj
#assert_axioms nested_demand
#assert_axioms demand_props

end Minidregg.Theory.ObjectiveBendDemandForcing
