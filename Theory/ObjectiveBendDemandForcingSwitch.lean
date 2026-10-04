/- The switch and the transfer through a pending demand (forcing transparency, part 4).

* `renameValue_congr` / `renameCell_congr` / `renameFrame_congr` / `renameControl_congr`:
  renamings that agree on the addresses an object holds rename it alike.
* `pend_switch`: when the lazy run enters the pending cell it runs the pending demand over
  its own stack and returns that demand's result renamed; the forced run returns the
  cached result in one transition; from there the two agree exactly (`AgreeRel`) under
  `switchMap`, the forced heap is covered, and the map is the identity on the base.
* `pend_update_read`: a stale update frame for the pending cell refuses alike on both sides.
* `pend_transfer`: through a pending demand, the forced run halts no later, every forced
  state is bounded by a lazy state no earlier (heap within `e.gap`, stack no deeper), and
  the final states are still pending or, once the lazy run entered the pending cell, agree
  exactly with equal heaps, the forced run then strictly shorter. -/
import Theory.ObjectiveBendDemandForcingPend
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendDemandInvariant (PreservesCached stepRaw_preservesCached)
set_option autoImplicit false

/-! ## Renamings that agree on the addresses held -/

theorem renameValue_congr {f g : Nat → Nat} {v : RuntimeValue} (same : ∀ x ∈ valueAddresses v, f x = g x) :
    renameValue f v = renameValue g v := by
  cases v with
  | closure body env => simp only [renameValue]; congr 1; exact List.map_congr_left same
  | natural _ => rfl
  | boolean _ => rfl
  | label _ => rfl
  | record fields =>
    simp only [renameValue]; congr 1
    apply List.map_congr_left; intro x m
    exact Prod.ext rfl (same _ (List.mem_map_of_mem (f := Prod.snd) m))
  | specification a b =>
    simp only [renameValue]; rw [same a (by simp [valueAddresses]), same b (by simp [valueAddresses])]
  | prototype a b =>
    simp only [renameValue]; rw [same a (by simp [valueAddresses]), same b (by simp [valueAddresses])]
  | variant l a => simp only [renameValue]; rw [same a (by simp [valueAddresses])]

theorem renameClosure_id {f : Nat → Nat} {c : Closure} (same : ∀ x ∈ c.environment, f x = x) :
    renameClosure f c = c := by
  obtain ⟨t, env⟩ := c
  simp only [renameClosure] at same ⊢
  congr 1
  conv => rhs; rw [← List.map_id env]
  exact List.map_congr_left same

theorem renameValue_id {f : Nat → Nat} {v : RuntimeValue} (same : ∀ x ∈ valueAddresses v, f x = x) :
    renameValue f v = v := by
  rw [renameValue_congr (g := id) same]; cases v <;> simp [renameValue]

theorem renameCell_congr {f g : Nat → Nat} {c : Cell} (same : ∀ x ∈ cellAddresses c, f x = g x) :
    renameCell f c = renameCell g c := by
  cases c with
  | suspended o => simp only [renameCell, renameClosure]; congr 2; exact List.map_congr_left same
  | evaluating o => simp only [renameCell, renameClosure]; congr 2; exact List.map_congr_left same
  | cached o v =>
    simp only [renameCell, renameClosure, cellAddresses] at same ⊢
    rw [List.map_congr_left (fun x m => same x (List.mem_append_left _ m)),
      renameValue_congr (fun x m => same x (List.mem_append_right _ m))]

theorem renameCell_id {f : Nat → Nat} {c : Cell} (same : ∀ x ∈ cellAddresses c, f x = x) :
    renameCell f c = c := by
  rw [renameCell_congr (g := id) same]; cases c <;> simp [renameCell, renameClosure, renameValue_id]

theorem renameFrame_congr {f g : Nat → Nat} {fr : Frame} (same : ∀ x ∈ frameAddresses fr, f x = g x) :
    renameFrame f fr = renameFrame g fr := by
  cases fr <;> simp only [renameFrame, frameAddresses] at same ⊢ <;>
    first
      | rfl
      | (congr 1; exact List.map_congr_left same)
      | (rw [same _ (List.mem_singleton_self _)])
      | (congr 1; exact renameValue_congr same)

theorem renameControl_congr {f g : Nat → Nat} {c : Control} (same : ∀ x ∈ controlAddresses c, f x = g x) :
    renameControl f c = renameControl g c := by
  cases c <;> simp only [renameControl, controlAddresses] at same ⊢ <;>
    first
      | rfl
      | (congr 1; exact List.map_congr_left same)
      | (rw [same _ (List.mem_singleton_self _)])
      | (congr 1; exact renameValue_congr same)

/-! ## The switch -/

/-- `e` on its base, carried to the lazy heap (its fresh cells after the lazy end). -/
def liftMap (base lazySize : Nat) : Nat → Nat := fun a => if a < base then a else a + (lazySize - base)

/-- After the switch: the lazy run's copy of `e`'s cells lands on `e`'s block. -/
def switchMap (e : Pending) (f : Nat → Nat) (lazySize : Nat) : Nat → Nat := fun a =>
  if a < lazySize then f a else if a < lazySize + e.gap then e.base.size + (a - lazySize) else a

theorem stepRaw_enter_cached {s : State} {b : Nat} {o : Closure} {v : RuntimeValue} (ctl : s.control = .enter b)
    (ca : s.heap[b]? = some (.cached o v)) : stepRaw s = ⟨s.heap, .returned v, s.stack⟩ := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl ca; subst ctl
  simp [stepRaw, ca]

theorem state_ext {s : State} : s = ⟨s.heap, s.control, s.stack⟩ := rfl

theorem heapValid_exec {s : State} (valid : AddrValid s) (n : Nat) : HeapValid (exec n s).heap :=
  (addrValid_exec valid n).heap

theorem addrValid_demandStart {P : Array Cell} {w : Nat} (valid : HeapValid P) (lt : w < P.size) :
    AddrValid (demandStart P w) :=
  ⟨valid, by simp [demandStart, controlAddresses, lt], fun _ m => by simp [demandStart] at m⟩

/-- **The switch.** When the lazy run enters the pending cell, it runs the pending demand
(over its own stack) to the demand's result, renamed; the forced run returns the cached
result in one transition; and the two then agree exactly, the forced heap covering the
lazy heap, the renaming the identity on the demand's base. -/
theorem pend_switch {e : Pending} {f : Nat → Nat} {σ τ : State} (rel : PendRel e f σ τ)
    (enter : σ.control = .enter e.cell) :
    4 ≤ e.steps ∧ (∀ j, j ≤ e.steps - 1 → active (exec j σ).control = true) ∧
      (∀ j, j ≤ e.steps - 1 → σ.stack.length ≤ (exec j σ).stack.length) ∧
      (exec (e.steps - 1) σ).heap.size = τ.heap.size ∧ (exec (e.steps - 1) σ).stack = σ.stack ∧
      stepRaw τ = ⟨τ.heap, (stepRaw τ).control, τ.stack⟩ ∧
      AgreeRel (switchMap e f σ.heap.size) (exec (e.steps - 1) σ) (stepRaw τ) ∧
      Covers (switchMap e f σ.heap.size) (exec (e.steps - 1) σ).heap (stepRaw τ).heap ∧
      (∀ a, a < e.base.size → switchMap e f σ.heap.size a = a) := by
  have ph := rel.heap
  have ev := ph.valid
  have baseLe := ph.grows
  have finalGe := Pending.final_ge ev
  have cellLt := Pending.cell_lt ev
  have tSize := ph.sizes
  let g := liftMap e.base.size σ.heap.size
  let U' : Nat → Prop := fun a => a < e.base.size ∧ ¬ Footprint e.base e.cell a
  -- e on its base, against e on the lazy heap
  have startAgree : StateAgree g everywhere U' (demandStart e.base e.cell) (demandStart σ.heap e.cell) := by
    refine ⟨⟨?_, ?_, ?_⟩, allIn_everywhere _, ?_, fun _ _ => allIn_everywhere _, rfl⟩
    · intro a past
      have past' : e.base.size ≤ a := past
      refine ⟨trivial, fun h => by simp only [U'] at h; omega, ?_⟩
      simp only [g, liftMap, show ¬ a < e.base.size by omega, if_false]
      show a + (σ.heap.size - e.base.size) + e.base.size = a + σ.heap.size
      omega
    · intro a b _ _ eq
      simp only [g, liftMap] at eq
      split at eq <;> split at eq <;> omega
    · intro a _ notU bound
      have bnd : a < e.base.size := bound
      have fp : Footprint e.base e.cell a := by
        apply Classical.byContradiction; intro h; exact notU ⟨bnd, h⟩
      have gId : ∀ x, x < e.base.size → g x = x := fun x lt => by simp [g, liftMap, lt]
      rcases fp with rfl | ⟨o, w, ca⟩
      · refine ⟨_, ev.susp, ?_, allIn_everywhere _⟩
        rw [show g e.cell = e.cell from gId _ cellLt, renameCell_id (fun x m => gId x (ev.baseValid _ _ ev.susp x m))]
        exact ph.cellKept
      · refine ⟨_, ca, ?_, allIn_everywhere _⟩
        rw [show g a = a from gId _ bnd, renameCell_id (fun x m => gId x (ev.baseValid _ _ ca x m))]
        exact ph.cachedKept a o w ca
    · show Control.enter e.cell = Control.enter (g e.cell)
      simp only [g, liftMap, cellLt, if_true]
  have avoids : ∀ j, j < e.steps → Avoids U' (exec j (demandStart e.base e.cell)) := by
    intro j lt a reads isU
    rcases ev.shallow j lt a reads isU.1 with fp
    exact isU.2 fp
  have agreeAt : ∀ j, j ≤ e.steps →
      StateAgree g everywhere U' (exec j (demandStart e.base e.cell)) (exec j (demandStart σ.heap e.cell)) :=
    fun j hj => agree_exec startAgree j (fun i lt => avoids i (by omega))
  have finalAgree := agreeAt e.steps (Nat.le_refl _)
  rw [ev.demand.final] at finalAgree
  -- the demand on the lazy heap
  let Hf := (exec e.steps (demandStart σ.heap e.cell)).heap
  have lazyDemand : Demand σ.heap e.cell e.steps Hf (renameValue g e.value) := by
    refine ⟨⟨fun j lt => ?_, ?_⟩, ?_⟩
    · rw [(agreeAt j (by omega)).active_eq]; exact ev.demand.halts.1 j lt
    · rw [(agreeAt e.steps (Nat.le_refl _)).active_eq]; exact ev.demand.halts.2
    · have ctl := finalAgree.control
      have st := finalAgree.stack
      simp only [renameControl, List.map_nil] at ctl st
      rw [state_ext (s := exec e.steps (demandStart σ.heap e.cell)), ctl, st]
  obtain ⟨four, cachedLazy, lastLazy, _, frame⟩ := demand_props lazyDemand ph.cellKept
  obtain ⟨_, cachedFinal, _, _, _⟩ := demand_props ev.demand ev.susp
  have σEq : σ = ⟨σ.heap, .enter e.cell, σ.stack⟩ := by rw [state_ext (s := σ), enter]
  have lazyAt : ∀ j, j ≤ e.steps - 1 → exec j σ = withStack (exec j (demandStart σ.heap e.cell)) σ.stack := by
    intro j hj; rw [σEq]; exact frame σ.stack j hj
  have σ1 : exec (e.steps - 1) σ = ⟨Hf, .returned (renameValue g e.value), σ.stack⟩ := by
    rw [lazyAt _ (Nat.le_refl _), lastLazy]; rfl
  -- sizes
  have hfSize : Hf.size = σ.heap.size + e.gap := by
    have := finalAgree.heap.image_size.1
    simp only [g, liftMap, show ¬ e.final.size < e.base.size by omega, if_false] at this
    show (exec e.steps (demandStart σ.heap e.cell)).heap.size = _
    rw [← this]; unfold Pending.gap; show e.final.size + (σ.heap.size - e.base.size) = σ.heap.size + (e.final.size - e.base.size)
    omega
  -- the forced side
  have τEnter : τ.control = .enter e.cell := by
    rw [rel.control, enter]; simp [renameControl, ph.mapOld _ cellLt]
  have τCached : τ.heap[e.cell]? = some (.cached e.origin e.value) := by rw [ph.cached]; exact cachedFinal
  have τ1 := stepRaw_enter_cached τEnter τCached
  -- the map after the switch
  let f' := switchMap e f σ.heap.size
  have f'Old : ∀ a, a < σ.heap.size → f' a = f a := fun a lt => by simp [f', switchMap, lt]
  have f'G : ∀ x, x < e.final.size → f' (g x) = x := by
    intro x lt
    by_cases small : x < e.base.size
    · simp [g, liftMap, small, f', switchMap, Nat.lt_of_lt_of_le small baseLe, ph.mapOld x small]
    · simp only [g, liftMap, small, if_false, f', switchMap]
      have : ¬ x + (σ.heap.size - e.base.size) < σ.heap.size := by omega
      simp only [this, if_false]
      have : x + (σ.heap.size - e.base.size) < σ.heap.size + e.gap := by unfold Pending.gap; omega
      simp only [this, if_true]; omega
  have finalValid : HeapValid e.final := by
    have := heapValid_exec (addrValid_demandStart ev.baseValid cellLt) e.steps
    rw [ev.demand.final] at this; exact this
  have valueValid : AllIn (· < e.final.size) (valueAddresses e.value) := by
    have := (addrValid_exec (addrValid_demandStart ev.baseValid cellLt) e.steps).control
    rw [ev.demand.final] at this; exact this
  have lazyValid := rel.valid
  have nb := ph.not_block
  have img : ∀ x, x < σ.heap.size → f x < τ.heap.size := fun x lt => ph.agree.image_lt trivial lt
  have grows := ph.grows
  have gapEq : e.gap = e.final.size - e.base.size := rfl
  have fNew : ∀ x, e.base.size ≤ x → f x = x + e.gap := ph.mapNew
  have fOld : ∀ x, x < e.base.size → f x = x := ph.mapOld
  -- the new agreement, on the concrete states
  have agreeNew : AgreeRel f' ⟨Hf, .returned (renameValue g e.value), σ.stack⟩ ⟨τ.heap, .returned e.value, τ.stack⟩ := by
    refine ⟨⟨⟨?_, ?_, ?_⟩, allIn_everywhere _, ?_, fun _ _ => allIn_everywhere _, ?_⟩, ?_⟩
    · intro a past
      simp only at past
      refine ⟨trivial, fun h => h, ?_⟩
      simp only [f', switchMap, show ¬ a < σ.heap.size by omega, show ¬ a < σ.heap.size + e.gap by omega, if_false]
      omega
    · intro a b _ _ eq
      simp only [f', switchMap] at eq
      by_cases ha : a < σ.heap.size <;> by_cases hb : b < σ.heap.size <;> simp only [ha, hb, if_true, if_false] at eq
      · exact ph.agree.inj a b trivial trivial eq
      · by_cases hb2 : b < σ.heap.size + e.gap <;> simp only [hb2, if_true, if_false] at eq
        · rcases nb a with h | h <;> omega
        · have := img a ha; omega
      · by_cases ha2 : a < σ.heap.size + e.gap <;> simp only [ha2, if_true, if_false] at eq
        · rcases nb b with h | h <;> omega
        · have := img b hb; omega
      · by_cases ha2 : a < σ.heap.size + e.gap <;> by_cases hb2 : b < σ.heap.size + e.gap <;>
          simp only [ha2, hb2, if_true, if_false] at eq <;> omega
    · intro a _ _ bound
      simp only at bound ⊢
      by_cases old : a < σ.heap.size
      · by_cases isCell : a = e.cell
        · subst isCell
          refine ⟨_, cachedLazy, ?_, allIn_everywhere _⟩
          rw [f'Old _ old, fOld _ cellLt, τCached]
          simp only [renameCell, renameValue_comp]
          rw [renameClosure_id (fun x m => by
              have xlt := ev.baseValid _ _ ev.susp x m
              rw [f'Old _ (by omega), fOld _ xlt]),
            renameValue_id (f := f' ∘ g) (fun x m => f'G x (valueValid x m))]
        · obtain ⟨c, found⟩ : ∃ c, σ.heap[a]? = some c := by
            cases h : σ.heap[a]? with
            | none => simp [Array.getElem?_eq_none_iff] at h; omega
            | some c => exact ⟨c, rfl⟩
          have kept : Hf[a]? = some c := by
            by_cases isCached : ∃ o w, c = .cached o w
            · obtain ⟨o, w, rfl⟩ := isCached
              exact exec_preservesCached _ e.steps a o w found
            · have unread : ∀ j, j < e.steps → readsAt (exec j (demandStart σ.heap e.cell)) ≠ some a := by
                intro j lt reads
                rw [(agreeAt j (by omega)).readsAt_eq] at reads
                cases r : readsAt (exec j (demandStart e.base e.cell)) with
                | none => rw [r] at reads; cases reads
                | some a' =>
                  rw [r] at reads; simp only [Option.map_some, Option.some.injEq] at reads
                  by_cases small : a' < e.base.size
                  · simp only [g, liftMap, small, if_true] at reads
                    subst reads
                    rcases ev.shallow j lt a' r small with rfl | ⟨o, w, ca⟩
                    · exact isCell rfl
                    · have := ph.cachedKept a' o w ca
                      rw [found] at this; cases this
                      exact isCached ⟨o, w, rfl⟩
                  · simp only [g, liftMap, small, if_false] at reads; omega
              have := exec_heap_keep (demandStart σ.heap e.cell) (show a < (demandStart σ.heap e.cell).heap.size from old)
                e.steps unread
              rw [this]; exact found
          refine ⟨c, kept, ?_, allIn_everywhere _⟩
          obtain ⟨c', found', found'', _⟩ := ph.agree.cells a trivial isCell old
          rw [found] at found'; cases found'
          rw [f'Old _ old, found'']
          congr 1
          exact renameCell_congr (fun x m => (f'Old x (rel.valid.heap _ _ found x m)).symm)
      · have hiA : a < σ.heap.size + e.gap := by rw [hfSize] at bound; exact bound
        let b := e.base.size + (a - σ.heap.size)
        have bLt : b < e.final.size := by simp only [b]; omega
        have gb : g b = a := by simp only [g, liftMap, b, show ¬ e.base.size + (a - σ.heap.size) < e.base.size by omega, if_false]; omega
        obtain ⟨c, foundF, foundL, _⟩ := finalAgree.heap.cells b trivial (fun h => by simp only [U', b] at h; omega) bLt
        rw [gb] at foundL
        refine ⟨_, foundL, ?_, allIn_everywhere _⟩
        have fa : f' a = b := by simp only [f', switchMap, old, hiA, if_false, if_true, b]
        rw [fa, ph.block b (by simp [b]) bLt, foundF, renameCell_comp,
          renameCell_id (f := f' ∘ g) (fun x m => f'G x (finalValid _ _ foundF x m))]
    · simp only [renameControl, renameValue_comp]
      rw [renameValue_id (f := f' ∘ g) (fun x m => f'G x (valueValid x m))]
    · simp only; rw [rel.stack]
      apply List.map_congr_left; intro fr m
      exact renameFrame_congr (fun x mx => (f'Old x (rel.valid.stack fr m x mx)).symm)
    · rw [← σ1]; exact addrValid_exec rel.valid _
  have cover : Covers f' Hf τ.heap := by
    intro b bLt
    by_cases small : b < e.base.size
    · exact ⟨b, by omega, by rw [f'Old _ (by omega), fOld _ small]⟩
    · by_cases mid : b < e.final.size
      · refine ⟨σ.heap.size + (b - e.base.size), by rw [hfSize]; unfold Pending.gap; omega, ?_⟩
        simp only [f', switchMap, show ¬ σ.heap.size + (b - e.base.size) < σ.heap.size by omega,
          show σ.heap.size + (b - e.base.size) < σ.heap.size + e.gap by unfold Pending.gap; omega, if_false, if_true]
        omega
      · refine ⟨b - e.gap, by rw [hfSize]; unfold Pending.gap at *; omega, ?_⟩
        rw [f'Old _ (by unfold Pending.gap at *; omega), fNew _ (by unfold Pending.gap at *; omega)]
        unfold Pending.gap at *; omega
  refine ⟨four, fun j hj => ?_, fun j hj => ?_, by rw [σ1]; simp only; rw [hfSize, tSize], by rw [σ1], by rw [τ1],
    by rw [σ1, τ1]; exact agreeNew, by rw [σ1, τ1]; exact cover, fun a lt => ?_⟩
  · rw [lazyAt j hj]; simp only [withStack]; exact lazyDemand.halts.1 j (by omega)
  · rw [lazyAt j hj]; simp [withStack]
  · simp only [switchMap, show a < σ.heap.size by omega, if_true]; exact fOld a lt

#assert_axioms renameValue_congr
#assert_axioms renameCell_congr
#assert_axioms renameFrame_congr
#assert_axioms renameControl_congr
#assert_axioms pend_switch
#assert_axioms renameClosure_id
#assert_axioms renameCell_id
#assert_axioms renameValue_id
#assert_axioms stepRaw_enter_cached

theorem stepRaw_update_not_evaluating {s : State} {v : RuntimeValue} {a : Nat} {rest : List Frame}
    (ctl : s.control = .returned v) (st : s.stack = .update a :: rest)
    (notEval : ∀ o, s.heap[a]? ≠ some (.evaluating o)) :
    stepRaw s = ⟨s.heap, .refused .invalidUpdate, rest⟩ := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl st notEval; subst ctl st
  simp only [stepRaw]
  try (split <;> first | (rename_i o h; exact absurd h (notEval o)) | rfl)

/-- A lazy update frame for the pending cell finds it suspended, the forced one finds it
cached: both refuse alike. -/
theorem pend_update_read {e : Pending} {f : Nat → Nat} {σ τ : State} (rel : PendRel e f σ τ) {v : RuntimeValue}
    {rest : List Frame} (ctl : σ.control = .returned v) (st : σ.stack = .update e.cell :: rest) :
    PendRel e f (stepRaw σ) (stepRaw τ) ∧ active (stepRaw σ).control = false := by
  have ph := rel.heap
  have cellLt := Pending.cell_lt ph.valid
  have σStep := stepRaw_update_not_evaluating ctl st (fun o h => by rw [ph.cellKept] at h; cases h)
  have τCtl : τ.control = .returned (renameValue f v) := by rw [rel.control, ctl]; rfl
  have τSt : τ.stack = .update e.cell :: rest.map (renameFrame f) := by
    rw [rel.stack, st]; simp [renameFrame, ph.mapOld _ cellLt]
  have τStep := stepRaw_update_not_evaluating τCtl τSt (fun o h => by
    rw [ph.cached, (demand_props ph.valid.demand ph.valid.susp).2.1] at h; cases h)
  rw [σStep, τStep]
  refine ⟨⟨ph, rfl, rfl, ?_⟩, rfl⟩
  have := addrValid_stepRaw rel.valid
  rw [σStep] at this; exact this

/-- **Transfer through a pending demand.** -/
theorem pend_transfer {e : Pending} {f : Nat → Nat} :
    ∀ (n : Nat) (σ τ : State), PendRel e f σ τ → Halts σ n →
      ∃ n', n' ≤ n ∧ Halts τ n' ∧ Bounded σ τ n n' e.gap ∧
        (PendRel e f (exec n σ) (exec n' τ) ∨
          ∃ g, AgreeRel g (exec n σ) (exec n' τ) ∧ Covers g (exec n σ).heap (exec n' τ).heap ∧
            (∀ a, a < e.base.size → g a = a) ∧ n' < n ∧ (exec n' τ).heap.size = (exec n σ).heap.size) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro σ τ rel halts
  have ph := rel.heap
  have sizes := ph.sizes
  have activeT : active τ.control = active σ.control := by rw [rel.control, active_rename]
  have stackT : τ.stack.length = σ.stack.length := by rw [rel.stack, List.length_map]
  cases act : active σ.control with
  | false =>
    have n0 : n = 0 := by
      apply Classical.byContradiction; intro h
      have := halts.1 0 (by omega); simp only [exec] at this; rw [act] at this; cases this
    subst n0
    refine ⟨0, Nat.le_refl _, ⟨fun _ h => by omega, by simp only [exec]; rw [activeT, act]⟩, ?_, Or.inl rel⟩
    intro j' hj'
    refine ⟨0, Nat.le_refl _, hj', ?_⟩
    have : j' = 0 := by omega
    subst this; simp only [exec]; exact ⟨by omega, by omega⟩
  | true =>
    have npos : 1 ≤ n := by
      apply Classical.byContradiction; intro h
      have := halts.2; rw [show n = 0 by omega] at this; simp only [exec] at this; rw [act] at this; cases this
    by_cases reads : readsAt σ = some e.cell
    · cases ctl : σ.control with
      | enter b =>
        have bEq : b = e.cell := by simp [readsAt, ctl] at reads; exact reads
        subst bEq
        obtain ⟨four, liveLazy, _, sizeEq, _, heapT0, agreeNew, cover, ident⟩ := pend_switch rel ctl
        generalize hm : e.steps - 1 = m at liveLazy sizeEq agreeNew cover
        have mlt : m < n := by
          apply Classical.byContradiction; intro h
          have := liveLazy n (by omega); rw [halts.2] at this; cases this
        have haltsRest : Halts (exec m σ) (n - m) := halts_drop (by rw [show m + (n - m) = n by omega]; exact halts)
        obtain ⟨haltsT1, agreeEnd, sizesT1, coverEnd⟩ := agree_transfer agreeNew haltsRest
        have τActive : active τ.control = true := by rw [activeT, act]
        have finalSize : (exec ((n - m) + 1) τ).heap.size = (exec n σ).heap.size := by
          have ⟨sz, _⟩ := sizesT1 (n - m) (Nat.le_refl _)
          have e1 : exec n σ = exec (n - m) (exec m σ) := by rw [← exec_add, show m + (n - m) = n by omega]
          rw [show exec ((n - m) + 1) τ = exec (n - m) (stepRaw τ) from rfl, e1]
          have hT : (stepRaw τ).heap.size = τ.heap.size := by rw [heapT0]
          omega
        refine ⟨(n - m) + 1, by omega, halts_succ τActive haltsT1, ?_, Or.inr ⟨_, ?_, ?_, ident, by omega, finalSize⟩⟩
        · intro j' hj'
          cases j' with
          | zero => exact ⟨0, Nat.zero_le _, Nat.le_refl _, by simp only [exec]; omega, by simp only [exec]; omega⟩
          | succ i =>
            refine ⟨m + i, by omega, by omega, ?_⟩
            have ⟨sz, stk⟩ := sizesT1 i (by omega)
            have heapT : (stepRaw τ).heap = τ.heap := by rw [heapT0]
            rw [show exec (i + 1) τ = exec i (stepRaw τ) from rfl, exec_add]
            rw [heapT, ← sizeEq] at sz
            exact ⟨by omega, by omega⟩
        · have := agreeEnd; rw [← exec_add, show m + (n - m) = n by omega] at this; exact this
        · have := coverEnd cover; rw [← exec_add, show m + (n - m) = n by omega] at this; exact this
      | returned v =>
        obtain ⟨rest, st⟩ : ∃ rest, σ.stack = .update e.cell :: rest := by
          cases st : σ.stack with
          | nil => simp [readsAt, ctl, st] at reads
          | cons fr rest =>
            cases fr <;> simp [readsAt, ctl, st] at reads
            exact ⟨rest, by rw [reads]⟩
        obtain ⟨next, inactive⟩ := pend_update_read rel ctl st
        have n1 : n = 1 := by
          apply Classical.byContradiction; intro h
          have := halts.1 1 (by omega); rw [exec_one, inactive] at this; cases this
        subst n1
        have τActive : active τ.control = true := by rw [activeT, act]
        have τInactive : active (stepRaw τ).control = false := by rw [next.control, active_rename, inactive]
        refine ⟨1, Nat.le_refl _, ⟨fun j h => by rw [show j = 0 by omega]; exact τActive, τInactive⟩, ?_,
          Or.inl next⟩
        intro j' hj'
        refine ⟨j', hj', Nat.le_refl _, ?_⟩
        cases j' with
        | zero => simp only [exec]; omega
        | succ i =>
          have : i = 0 := by omega
          subst this
          have s1 := next.heap.sizes
          have k1 : (stepRaw τ).stack.length = (stepRaw σ).stack.length := by rw [next.stack, List.length_map]
          simp only [exec]; omega
      | _ => simp [readsAt, ctl] at reads
    · have next := pend_step rel reads
      obtain ⟨n'', le, haltsT, bounded, result⟩ := ih (n - 1) (by omega) _ _ next
        (halts_tail (by rw [show n - 1 + 1 = n by omega]; exact halts))
      have τActive : active τ.control = true := by rw [activeT, act]
      have eqS : exec n σ = exec (n - 1) (stepRaw σ) := by
        rw [show n = (n - 1) + 1 by omega]; rfl
      refine ⟨n'' + 1, by omega, halts_succ τActive haltsT, ?_, ?_⟩
      · intro j' hj'
        cases j' with
        | zero => exact ⟨0, Nat.zero_le _, Nat.le_refl _, by simp only [exec]; omega, by simp only [exec]; omega⟩
        | succ i =>
          obtain ⟨j, hj, hij, sz, stk⟩ := bounded i (by omega)
          refine ⟨j + 1, by omega, by omega, ?_, ?_⟩
          · show (exec i (stepRaw τ)).heap.size ≤ (exec j (stepRaw σ)).heap.size + e.gap; exact sz
          · show (exec i (stepRaw τ)).stack.length ≤ (exec j (stepRaw σ)).stack.length; exact stk
      · rw [eqS]
        show PendRel e f (exec (n - 1) (stepRaw σ)) (exec n'' (stepRaw τ)) ∨ _
        rcases result with p | ⟨g, a, c, i, lt, sz⟩
        · exact Or.inl p
        · exact Or.inr ⟨g, a, c, i, by omega, sz⟩

#assert_axioms pend_update_read
#assert_axioms pend_transfer
#assert_axioms stepRaw_update_not_evaluating

end Minidregg.Theory.ObjectiveBendDemandForcing
