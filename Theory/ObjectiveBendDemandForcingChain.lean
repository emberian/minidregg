/- Forcing chains (forcing transparency, part 5).

`ForcesBy gap F σ τ`: a finite chain of pending demands (`PendRel`) and exact agreements
(`AgreeRel`) carries the lazy state `σ` to the forced state `τ`, under the composite
address map `F`, with heap headroom `gap`.

* `forces_transfer`: a halting lazy run is matched by a forced run that halts no later,
  each forced state bounded by a lazy state no earlier, ending again in a chain whose map
  extends the first on every address the lazy state held.
* `ForcesBy.reenter`: a chain relates heaps: any valid control and stack of the lazy heap,
  renamed, are related alike (what extraction needs: it re-enters cells with an empty stack).
* `agree_inverse`: a covering exact agreement between equal-size heaps inverts. -/
import Theory.ObjectiveBendDemandForcingSwitch
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
set_option autoImplicit false

/-- **`σ` forces to `τ`** under the address map `F`, with heap headroom `gap`: a finite
chain of pending demands and exact agreements. -/
inductive ForcesBy : Nat → (Nat → Nat) → State → State → Prop where
  | pend {e : Pending} {f : Nat → Nat} {gap : Nat} {σ τ : State} :
      PendRel e f σ τ → e.gap ≤ gap → ForcesBy gap f σ τ
  | agree {f : Nat → Nat} {gap : Nat} {σ τ : State} :
      AgreeRel f σ τ → τ.heap.size ≤ σ.heap.size + gap → ForcesBy gap f σ τ
  | trans {g1 g2 gap : Nat} {F1 F2 : Nat → Nat} {σ μ τ : State} :
      ForcesBy g1 F1 σ μ → ForcesBy g2 F2 μ τ → g1 + g2 ≤ gap → ForcesBy gap (F2 ∘ F1) σ τ

namespace ForcesBy

theorem mono {gap gap' : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) (le : gap ≤ gap') :
    ForcesBy gap' F σ τ := by
  cases h with
  | pend r g => exact .pend r (Nat.le_trans g le)
  | agree r g => exact .agree r (by omega)
  | trans a b g => exact .trans a b (Nat.le_trans g le)

theorem renames {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) :
    τ.control = renameControl F σ.control ∧ τ.stack = σ.stack.map (renameFrame F) := by
  induction h with
  | pend r _ => exact ⟨r.control, r.stack⟩
  | agree r _ => exact ⟨r.agree.control, r.agree.stack⟩
  | trans _ _ _ ih1 ih2 =>
    refine ⟨by rw [ih2.1, ih1.1, renameControl_comp], ?_⟩
    rw [ih2.2, ih1.2, List.map_map]; congr 1; funext fr; exact renameFrame_comp _ _ fr

theorem lazyValid {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) : AddrValid σ := by
  induction h with
  | pend r _ => exact r.valid
  | agree r _ => exact r.valid
  | trans _ _ _ ih1 _ => exact ih1

theorem image {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) :
    ∀ x, x < σ.heap.size → F x < τ.heap.size := by
  induction h with
  | pend r _ => exact fun x lt => r.heap.agree.image_lt trivial lt
  | agree r _ => exact fun x lt => r.agree.heap.image_lt trivial lt
  | trans _ _ _ ih1 ih2 => exact fun x lt => ih2 _ (ih1 x lt)

/-- **Re-entry**: the relation is a relation of heaps; any valid control and stack of the
lazy heap, renamed, are related to the forced heap alike. -/
theorem reenter {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) (c : Control) (S : List Frame)
    (cIn : AllIn (· < σ.heap.size) (controlAddresses c))
    (sIn : ∀ fr ∈ S, AllIn (· < σ.heap.size) (frameAddresses fr)) :
    ForcesBy gap F ⟨σ.heap, c, S⟩ ⟨τ.heap, renameControl F c, S.map (renameFrame F)⟩ := by
  induction h generalizing c S with
  | pend r g =>
    exact .pend ⟨r.heap, rfl, rfl, ⟨r.valid.heap, cIn, sIn⟩⟩ g
  | agree r g =>
    exact .agree ⟨⟨r.agree.heap, allIn_everywhere _, rfl, fun _ _ => allIn_everywhere _, rfl⟩,
      ⟨r.valid.heap, cIn, sIn⟩⟩ g
  | @trans g1 g2 gap F1 F2 σ μ τ one two g ih1 ih2 =>
    have img := one.image
    have l1 := ih1 c S cIn sIn
    have l2 := ih2 (renameControl F1 c) (S.map (renameFrame F1))
      (by rw [controlAddresses_rename]; intro x m; obtain ⟨y, my, rfl⟩ := List.mem_map.mp m; exact img y (cIn y my))
      (by intro fr m; obtain ⟨fr0, m0, rfl⟩ := List.mem_map.mp m
          rw [frameAddresses_rename]; intro x mx; obtain ⟨y, my, rfl⟩ := List.mem_map.mp mx
          exact img y (sIn fr0 m0 y my))
    have := ForcesBy.trans l1 l2 g
    rw [renameControl_comp, List.map_map] at this
    have eq : (renameFrame F2 ∘ renameFrame F1) = renameFrame (F2 ∘ F1) := by
      funext fr; exact renameFrame_comp _ _ fr
    rw [eq] at this; exact this

end ForcesBy

/-- Bounds compose along a chain. -/
theorem bounded_trans {σ μ τ : State} {n n1 n2 g1 g2 : Nat} (one : Bounded σ μ n n1 g1) (two : Bounded μ τ n1 n2 g2) :
    Bounded σ τ n n2 (g1 + g2) := by
  intro j' hj'
  obtain ⟨j1, hj1, le1, sz1, st1⟩ := two j' hj'
  obtain ⟨j, hj, le, sz, st⟩ := one j1 hj1
  exact ⟨j, hj, by omega, by omega, by omega⟩

theorem bounded_mono {σ τ : State} {n n' g g' : Nat} (b : Bounded σ τ n n' g) (le : g ≤ g') : Bounded σ τ n n' g' := by
  intro j' hj'
  obtain ⟨j, hj, lj, sz, st⟩ := b j' hj'
  exact ⟨j, hj, lj, by omega, st⟩

/-- **Transfer along a forcing chain.** -/
theorem forces_transfer {gap : Nat} {F : Nat → Nat} {σ τ : State} (h : ForcesBy gap F σ τ) :
    ∀ n, Halts σ n → ∃ n' F', n' ≤ n ∧ Halts τ n' ∧ Bounded σ τ n n' gap ∧ ForcesBy gap F' (exec n σ) (exec n' τ) ∧
      ∀ a, a < σ.heap.size → F' a = F a := by
  induction h with
  | @pend e f gap σ τ r g =>
    intro n halts
    obtain ⟨n', le, haltsT, bounded, result⟩ := pend_transfer n σ τ r halts
    rcases result with p | ⟨g', a, _, _, ext, _, sz⟩
    · exact ⟨n', f, le, haltsT, bounded_mono bounded g, .pend p g, fun _ _ => rfl⟩
    · exact ⟨n', g', le, haltsT, bounded_mono bounded g, .agree a (by omega), ext⟩
  | @agree f gap σ τ r g =>
    intro n halts
    obtain ⟨haltsT, agreeEnd, sizes, _⟩ := agree_transfer r halts
    refine ⟨n, f, Nat.le_refl _, haltsT, ?_, .agree agreeEnd ?_, fun _ _ => rfl⟩
    · intro j' hj'
      have ⟨sz, st⟩ := sizes j' hj'
      exact ⟨j', hj', Nat.le_refl _, by omega, by omega⟩
    · have ⟨sz, _⟩ := sizes n (Nat.le_refl _); omega
  | trans one two g ih1 ih2 =>
    intro n halts
    obtain ⟨n1, F1', le1, halts1, b1, r1, e1⟩ := ih1 n halts
    obtain ⟨n2, F2', le2, halts2, b2, r2, e2⟩ := ih2 n1 halts1
    refine ⟨n2, _, by omega, halts2, bounded_mono (bounded_trans b1 b2) g, .trans r1 r2 g, fun a lt => ?_⟩
    simp only [Function.comp_apply]
    rw [e1 a lt, e2 _ (one.image a lt)]

/-! ## Exact agreements: the identity, and the inverse of a covering one -/

theorem agreeRel_refl {σ : State} (valid : AddrValid σ) : AgreeRel id σ σ := by
  refine ⟨⟨⟨fun a _ => ⟨trivial, fun h => h, rfl⟩, fun _ _ _ _ h => h, ?_⟩, allIn_everywhere _, ?_,
    fun _ _ => allIn_everywhere _, ?_⟩, valid⟩
  · intro a _ _ lt
    obtain ⟨c, found⟩ : ∃ c, σ.heap[a]? = some c := ⟨σ.heap[a], by simp [lt]⟩
    exact ⟨c, found, by rw [renameCell_id (f := id) (fun _ _ => rfl)]; exact found, allIn_everywhere _⟩
  · cases h : σ.control <;> simp [renameControl, renameValue_id (f := id) (fun _ _ => rfl)]
  · conv => lhs; rw [← List.map_id σ.stack]
    apply List.map_congr_left; intro fr _
    rw [renameFrame_congr (g := id) (fun _ _ => rfl)]; cases fr <;> simp [renameFrame, renameValue_id (f := id) (fun _ _ => rfl)]

/-- **The inverse of a covering exact agreement** between equal-size heaps. -/
theorem agree_inverse {g : Nat → Nat} {H1 H2 : Array Cell} (hr : HeapAgree g everywhere (fun _ => False) H1 H2)
    (cov : Covers g H1 H2) (sizes : H2.size = H1.size) (valid : HeapValid H1) :
    ∃ ginv : Nat → Nat, HeapAgree ginv everywhere (fun _ => False) H2 H1 ∧
      (∀ a, a < H1.size → ginv (g a) = a) := by
  classical
  let ginv : Nat → Nat := fun b => if h : b < H2.size then Classical.choose (cov b h) else b - H2.size + H1.size
  have spec : ∀ b (h : b < H2.size), ginv b < H1.size ∧ g (ginv b) = b := by
    intro b h; simp only [ginv, h, dif_pos]; exact Classical.choose_spec (cov b h)
  have left : ∀ a, a < H1.size → ginv (g a) = a := by
    intro a lt
    have gl := hr.image_lt trivial lt
    obtain ⟨l1, l2⟩ := spec (g a) gl
    exact hr.inj _ _ trivial trivial l2
  refine ⟨ginv, ⟨?_, ?_, ?_⟩, left⟩
  · intro b past
    refine ⟨trivial, fun h => h, ?_⟩
    simp only [ginv, show ¬ b < H2.size by omega, dif_neg, not_false_eq_true]; omega
  · have beyondEq : ∀ b, ¬ b < H2.size → ginv b = b - H2.size + H1.size := by
      intro b h; simp only [ginv, h, dif_neg, not_false_eq_true]
    intro b1 b2 _ _ eq
    by_cases h1 : b1 < H2.size <;> by_cases h2 : b2 < H2.size
    · have := congrArg g eq; rw [(spec b1 h1).2, (spec b2 h2).2] at this; exact this
    · have v1 := (spec b1 h1).1; rw [beyondEq b2 h2] at eq; omega
    · have v2 := (spec b2 h2).1; rw [beyondEq b1 h1] at eq; omega
    · rw [beyondEq b1 h1, beyondEq b2 h2] at eq; omega
  · intro b _ _ lt
    obtain ⟨al, ga⟩ := spec b lt
    obtain ⟨c, found, found', _⟩ := hr.cells (ginv b) trivial (fun h => h) al
    rw [ga] at found'
    refine ⟨_, found', ?_, allIn_everywhere _⟩
    rw [found, renameCell_comp, renameCell_id (f := ginv ∘ g) (fun x m => left x (valid _ _ found x m))]

/-- When the transition enters an unsuspended cell, nothing in the heap or stack changes. -/
theorem stepRaw_enter_cases {s : State} {b : Nat} (ctl : s.control = .enter b) :
    (∃ o, s.heap[b]? = some (.suspended o)) ∨ ((stepRaw s).heap = s.heap ∧ (stepRaw s).stack = s.stack) := by
  obtain ⟨heap, control, stack⟩ := s
  simp only at ctl; subst ctl
  cases h : heap[b]? with
  | none => right; simp [stepRaw, h]
  | some c => cases c with
    | suspended o => left; exact ⟨o, rfl⟩
    | evaluating o => right; simp [stepRaw, h]
    | cached o v => right; simp [stepRaw, h]

theorem StateAgree.readsIn {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (rel : StateAgree f D U s t)
    {a : Nat} (reads : readsAt s = some a) : D a := by
  obtain ⟨heap, control, stack⟩ := s
  have cIn := rel.controlIn; have sIn := rel.stackIn
  simp only at cIn sIn
  cases control with
  | enter b => simp [readsAt] at reads; subst reads; exact cIn _ (List.mem_singleton_self _)
  | returned v =>
    cases stack with
    | nil => simp [readsAt] at reads
    | cons fr rest =>
      cases fr <;> simp [readsAt] at reads
      subst reads; exact sIn _ (List.mem_cons_self ..) _ (List.mem_singleton_self _)
  | _ => simp [readsAt] at reads
#assert_axioms ForcesBy.mono
#assert_axioms ForcesBy.renames
#assert_axioms ForcesBy.lazyValid
#assert_axioms ForcesBy.image
#assert_axioms ForcesBy.reenter
#assert_axioms bounded_trans
#assert_axioms forces_transfer
#assert_axioms agreeRel_refl
#assert_axioms agree_inverse
#assert_axioms stepRaw_enter_cases
#assert_axioms StateAgree.readsIn

end Minidregg.Theory.ObjectiveBendDemandForcing
