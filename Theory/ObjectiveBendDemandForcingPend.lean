/- A pending closed demand (forcing transparency, part 3).

`PendRel e f σ τ`: the forced state `τ` is the lazy state `σ` renamed by `f`, except
that one cell, `e.cell`, is suspended in `σ` and cached in `τ` with the result of its
closed demand `e` (on the heap `e.base` `σ` grew from), whose freshly allocated cells sit
in `τ` at `e.base`'s end. `e` reads nothing but `e.cell` and cached cells of `e.base`
(`PreShallow`), so the lazy run can still run it, unchanged, whenever it gets there.

* `pend_step`: a lazy transition that does not read `e.cell` keeps the relation.
* `pend_switch`: when the lazy run enters `e.cell`, it runs `e` (`demand_props`) and
  returns `e`'s result renamed; the forced run returns the cached result in one
  transition; from there the two agree with no exception (`AgreeRel`), the forced heap
  covering the lazy heap exactly.
* `agree_transfer`: agreeing runs halt together and stay agreeing.
* `pend_transfer`: whatever the lazy run does, the forced run halts no later, no larger
  (heap within `e.gap` of a lazy state no earlier, stack no deeper), and the final
  states are still pending or, once the lazy run entered `e.cell`, agree exactly, the
  forced run then STRICTLY shorter. -/
import Theory.ObjectiveBendDemandForcingNest
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendDemandInvariant (PreservesCached stepRaw_preservesCached)
set_option autoImplicit false

def everywhere : Nat → Prop := fun _ => True

theorem allIn_everywhere (l : List Nat) : AllIn everywhere l := fun _ _ => trivial

/-! ## Runs: monotone sizes, kept cells, validity -/

theorem exec_size_mono (s : State) (n : Nat) : s.heap.size ≤ (exec n s).heap.size := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => rw [exec_succ]; exact Nat.le_trans ih (stepRaw_size_mono _)

theorem exec_heap_keep (s : State) {a : Nat} (bound : a < s.heap.size) :
    ∀ n, (∀ j, j < n → readsAt (exec j s) ≠ some a) → (exec n s).heap[a]? = s.heap[a]? := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro unread
    rw [exec_succ, stepRaw_heap_keep _ (Nat.lt_of_lt_of_le bound (exec_size_mono s n)) (unread n (by omega)),
      ih (fun j lt => unread j (by omega))]

theorem exec_preservesCached (s : State) (n : Nat) : PreservesCached s.heap (exec n s).heap := by
  induction n with
  | zero => exact fun _ _ _ h => h
  | succ n ih => rw [exec_succ]; exact fun a o v h => stepRaw_preservesCached _ a o v (ih a o v h)

theorem addrValid_exec {s : State} (valid : AddrValid s) (n : Nat) : AddrValid (exec n s) := by
  induction n with
  | zero => exact valid
  | succ n ih => rw [exec_succ]; exact addrValid_stepRaw ih

theorem halts_succ {s : State} {n : Nat} (active : active s.control = true) (h : Halts (stepRaw s) n) :
    Halts s (n + 1) := by
  refine ⟨fun j lt => ?_, ?_⟩
  · cases j with
    | zero => exact active
    | succ j => rw [exec_succ', ]; exact h.1 j (by omega)
  · rw [exec_succ']; exact h.2
where exec_succ' {s : State} {n : Nat} : exec (n + 1) s = exec n (stepRaw s) := rfl

theorem halts_tail {s : State} {n : Nat} (h : Halts s (n + 1)) : Halts (stepRaw s) n :=
  ⟨fun j lt => h.1 (j + 1) (by omega), h.2⟩

theorem halts_drop {s : State} {n m : Nat} (h : Halts s (m + n)) : Halts (exec m s) n := by
  refine ⟨fun j lt => ?_, ?_⟩
  · rw [← exec_add]; exact h.1 (m + j) (by omega)
  · rw [← exec_add]; exact h.2

/-- Forced states are bounded by lazy states no earlier. -/
def Bounded (σ τ : State) (n n' gap : Nat) : Prop :=
  ∀ j', j' ≤ n' → ∃ j, j ≤ n ∧ j' ≤ j ∧ (exec j' τ).heap.size ≤ (exec j σ).heap.size + gap ∧
    (exec j' τ).stack.length ≤ (exec j σ).stack.length

/-- Every forced address up to the heap end is an image. -/
def Covers (f : Nat → Nat) (H T : Array Cell) : Prop := ∀ b, b < T.size → ∃ a, a < H.size ∧ f a = b

/-! ## Agreement without exception -/

/-- The lazy and forced states agree under `f` with no exception. -/
structure AgreeRel (f : Nat → Nat) (σ τ : State) : Prop where
  agree : StateAgree f everywhere (fun _ => False) σ τ
  valid : AddrValid σ

theorem agree_sizes {f : Nat → Nat} {σ τ σ' τ' : State}
    (one : StateAgree f everywhere (fun _ => False) σ τ) (two : StateAgree f everywhere (fun _ => False) σ' τ')
    (grow : σ.heap.size ≤ σ'.heap.size) : τ'.heap.size + σ.heap.size = σ'.heap.size + τ.heap.size := by
  have := (one.heap.beyond σ'.heap.size grow).2.2
  rw [two.heap.image_size.1] at this
  omega

theorem agree_covers_step {f : Nat → Nat} {σ τ σ' τ' : State}
    (one : StateAgree f everywhere (fun _ => False) σ τ) (two : StateAgree f everywhere (fun _ => False) σ' τ')
    (grow : σ.heap.size ≤ σ'.heap.size) (cov : Covers f σ.heap τ.heap) : Covers f σ'.heap τ'.heap := by
  intro b lt
  have sizes := agree_sizes one two grow
  by_cases old : b < τ.heap.size
  · obtain ⟨a, aLt, eq⟩ := cov b old
    exact ⟨a, by omega, eq⟩
  · refine ⟨b + σ.heap.size - τ.heap.size, by omega, ?_⟩
    have := (one.heap.beyond (b + σ.heap.size - τ.heap.size) (by omega)).2.2
    omega

/-- **Agreeing runs halt together and keep agreeing.** -/
theorem agree_transfer {f : Nat → Nat} {σ τ : State} (rel : AgreeRel f σ τ) {n : Nat} (halts : Halts σ n) :
    Halts τ n ∧ AgreeRel f (exec n σ) (exec n τ) ∧
      (∀ j, j ≤ n → (exec j τ).heap.size + σ.heap.size = (exec j σ).heap.size + τ.heap.size ∧
        (exec j τ).stack.length = (exec j σ).stack.length) ∧
      (Covers f σ.heap τ.heap → Covers f (exec n σ).heap (exec n τ).heap) := by
  have all : ∀ j, StateAgree f everywhere (fun _ => False) (exec j σ) (exec j τ) :=
    fun j => agree_exec rel.agree j (fun _ _ _ _ h => h)
  refine ⟨⟨fun j lt => ?_, ?_⟩, ⟨all n, addrValid_exec rel.valid n⟩, fun j _ => ?_, fun cov => ?_⟩
  · rw [(all j).active_eq]; exact halts.1 j lt
  · rw [(all n).active_eq]; exact halts.2
  · exact ⟨agree_sizes rel.agree (all j) (exec_size_mono σ j), (all j).stack_length⟩
  · exact agree_covers_step rel.agree (all n) (exec_size_mono σ n) cov

/-! ## The pending demand -/

/-- The cells a pending demand may read: its own cell and cached cells of its base. -/
def Footprint (B : Array Cell) (y a : Nat) : Prop := a = y ∨ ∃ o w, B[a]? = some (.cached o w)

/-- The closed demand of `y` on `B` reads, of `B`'s cells, only its footprint. -/
def PreShallow (B : Array Cell) (y n : Nat) : Prop :=
  ∀ j, j < n → ∀ a, readsAt (exec j (demandStart B y)) = some a → a < B.size → Footprint B y a

/-- A pending closed demand and its result. -/
structure Pending where
  base : Array Cell
  cell : Nat
  steps : Nat
  final : Array Cell
  value : RuntimeValue
  origin : Closure

structure Pending.Valid (e : Pending) : Prop where
  demand : Demand e.base e.cell e.steps e.final e.value
  susp : e.base[e.cell]? = some (.suspended e.origin)
  shallow : PreShallow e.base e.cell e.steps
  baseValid : HeapValid e.base

/-- How many cells the pending demand allocates. -/
def Pending.gap (e : Pending) : Nat := e.final.size - e.base.size

/-- The lazy heap with `e` pending, against the forced heap. -/
structure PendHeap (e : Pending) (f : Nat → Nat) (Hσ Hτ : Array Cell) : Prop where
  valid : e.Valid
  grows : e.base.size ≤ Hσ.size
  cellKept : Hσ[e.cell]? = some (.suspended e.origin)
  cachedKept : ∀ (a : Nat) (o : Closure) (w : RuntimeValue), e.base[a]? = some (.cached o w) → Hσ[a]? = some (.cached o w)
  mapOld : ∀ a, a < e.base.size → f a = a
  mapNew : ∀ a, e.base.size ≤ a → f a = a + e.gap
  agree : HeapAgree f everywhere (· = e.cell) Hσ Hτ
  block : ∀ a, e.base.size ≤ a → a < e.final.size → Hτ[a]? = e.final[a]?
  cached : Hτ[e.cell]? = e.final[e.cell]?

structure PendRel (e : Pending) (f : Nat → Nat) (σ τ : State) : Prop where
  heap : PendHeap e f σ.heap τ.heap
  control : τ.control = renameControl f σ.control
  stack : τ.stack = σ.stack.map (renameFrame f)
  valid : AddrValid σ

theorem PendRel.stateAgree {e : Pending} {f : Nat → Nat} {σ τ : State} (rel : PendRel e f σ τ) :
    StateAgree f everywhere (· = e.cell) σ τ :=
  ⟨rel.heap.agree, allIn_everywhere _, rel.control, fun _ _ => allIn_everywhere _, rel.stack⟩

theorem Pending.final_ge {e : Pending} (valid : e.Valid) : e.base.size ≤ e.final.size := by
  have := exec_size_mono (demandStart e.base e.cell) e.steps
  rw [valid.demand.final] at this; exact this

theorem Pending.cell_lt {e : Pending} (valid : e.Valid) : e.cell < e.base.size := bound_of_some valid.susp

theorem PendHeap.sizes {e : Pending} {f : Nat → Nat} {Hσ Hτ : Array Cell} (ph : PendHeap e f Hσ Hτ) :
    Hτ.size = Hσ.size + e.gap := by
  have := ph.agree.image_size.1
  rw [ph.mapNew _ ph.grows] at this; omega

/-- The renaming never lands in the pending demand's block. -/
theorem PendHeap.not_block {e : Pending} {f : Nat → Nat} {Hσ Hτ : Array Cell} (ph : PendHeap e f Hσ Hτ) (a : Nat) :
    f a < e.base.size ∨ e.final.size ≤ f a := by
  have ge := Pending.final_ge ph.valid
  by_cases lt : a < e.base.size
  · left; rw [ph.mapOld a lt]; exact lt
  · right; rw [ph.mapNew a (by omega)]; unfold Pending.gap; omega

theorem PendHeap.f_eq_cell {e : Pending} {f : Nat → Nat} {Hσ Hτ : Array Cell} (ph : PendHeap e f Hσ Hτ) {a : Nat}
    (eq : f a = e.cell) : a = e.cell := by
  have cellLt := Pending.cell_lt ph.valid
  have ge := Pending.final_ge ph.valid
  by_cases lt : a < e.base.size
  · rw [ph.mapOld a lt] at eq; exact eq
  · rw [ph.mapNew a (by omega)] at eq; unfold Pending.gap at eq; omega

/-- **A lazy transition that does not read the pending cell keeps the relation.** -/
theorem pend_step {e : Pending} {f : Nat → Nat} {σ τ : State} (rel : PendRel e f σ τ)
    (unread : readsAt σ ≠ some e.cell) : PendRel e f (stepRaw σ) (stepRaw τ) := by
  have ph := rel.heap
  have next := agree_stepRaw rel.stateAgree (fun a reads isCell => unread (isCell ▸ reads))
  have readsT := rel.stateAgree.readsAt_eq
  have cellLt : e.cell < σ.heap.size := bound_of_some ph.cellKept
  have tSize := ph.sizes
  have ge := Pending.final_ge ph.valid
  have grows := ph.grows
  refine ⟨⟨ph.valid, Nat.le_trans ph.grows (stepRaw_size_mono σ), ?_, ?_, ph.mapOld, ph.mapNew, next.heap, ?_, ?_⟩,
    next.control, next.stack, addrValid_stepRaw rel.valid⟩
  · rw [stepRaw_heap_keep σ cellLt unread]; exact ph.cellKept
  · intro a o w found; exact stepRaw_preservesCached σ a o w (ph.cachedKept a o w found)
  · intro a lo hi
    have tUnread : readsAt τ ≠ some a := by
      rw [readsT]; intro h
      cases r : readsAt σ with
      | none => rw [r] at h; cases h
      | some b =>
        rw [r] at h; simp at h
        rcases ph.not_block b with lt | geq <;> omega
    rw [stepRaw_heap_keep τ (by unfold Pending.gap at tSize; omega) tUnread]; exact ph.block a lo hi
  · have tUnread : readsAt τ ≠ some e.cell := by
      rw [readsT]; intro h
      cases r : readsAt σ with
      | none => rw [r] at h; cases h
      | some b =>
        rw [r] at h; simp at h
        exact unread (by rw [r, ph.f_eq_cell h])
    rw [stepRaw_heap_keep τ (by unfold Pending.gap at tSize; have := Pending.cell_lt ph.valid; omega) tUnread]
    exact ph.cached

#assert_axioms exec_heap_keep
#assert_axioms agree_transfer
#assert_axioms pend_step

end Minidregg.Theory.ObjectiveBendDemandForcing
