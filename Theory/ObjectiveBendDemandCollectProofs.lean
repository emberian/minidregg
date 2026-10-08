/- The behaviour theorem for collecting the Core4 heap at a yield (design B4/T5), and
the typing transfer. Definitions: `Theory.ObjectiveBendDemandCollect`.

The relation is a renaming simulation. `Related f D s t` says `t` is `s` renamed by `f`
on a domain `D` that contains the roots and everything past `s`'s heap and is closed
under the heap: same control, same stack, and every `D`-cell of `s` is, renamed, the
`f`-image cell of `t`; `f` is injective on `D` and shifts the addresses past the heap.
Cells outside `D` (the garbage) are unconstrained. Because `f` and `D` never change,
lockstep allocation needs no extension of the renaming: both machines allocate at their
heap ends and `f` maps one end to the other.

* `related_collect`: `Related (collectRenaming s) (liveDomain s) s (collect s)`.
* `related_stepRaw`, `related_resume`, `related_runBounded` (outcomes agree unless the
  original ran out of heap, under any limits that give the related state the original's
  room, `RoomFor`), `related_runBounded_exact` (exact, capacity included, when
  the collected run is charged the heap it freed), `related_forceWith`,
  `related_materializeWith`, `related_completeWith`, `related_yieldedPlanWith` (the
  extracted Data and remaining budget agree), `related_segment` (the shape of the
  kernel's `runSegment`), `Related.trans` (collecting at every yield stays related to
  never collecting).
* `typed_related` / `typed_collect`: `StateTyping` (heap, control, stack typing and the
  lexical, busy and final-stack invariants) transfers at `collectTypes`.
* Inhabitants: a typed state with a garbage cell (`garbageTyping`) and a closed program
  that yields with a garbage cell (`yieldingTerm`), whose Plan extracts to the same
  encoded Data before and after collection. -/
import Theory.ObjectiveBendDemandCollect
import Theory.ObjectiveBendDemandData
import Theory.ObjectiveBendDemandTyping
namespace Minidregg.Theory.ObjectiveBendDemandCollect
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
set_option autoImplicit false

/-! ## Marking is sound: the marks contain the roots and are closed -/

theorem pending_nil {marks : Array Bool} {work : List Nat} (drained : pending marks work = []) :
    ∀ x ∈ work, marks[x]? ≠ some false := by
  induction work with
  | nil => intro x member; cases member
  | cons head rest ih =>
    intro x member
    simp only [pending] at drained
    split at drained
    · cases drained
    · rename_i notFalse
      rcases List.mem_cons.mp member with rfl | member
      · exact notFalse
      · exact ih drained x member

theorem pending_cons {marks : Array Bool} {work rest : List Nat} {address : Nat}
    (next : pending marks work = address :: rest) :
    marks[address]? = some false ∧ ∀ x ∈ work, marks[x]? ≠ some false ∨ x ∈ address :: rest := by
  induction work with
  | nil => simp [pending] at next
  | cons head tail ih =>
    simp only [pending] at next
    split at next
    · rename_i isFalse
      cases next
      exact ⟨isFalse, fun x member => .inr member⟩
    · rename_i notFalse
      obtain ⟨first, others⟩ := ih next
      refine ⟨first, fun x member => ?_⟩
      rcases List.mem_cons.mp member with rfl | member
      · exact .inl notFalse
      · exact others x member

theorem bound_of_some {α : Type} {xs : Array α} {i : Nat} {v : α} (found : xs[i]? = some v) :
    i < xs.size := (Array.getElem?_eq_some_iff.mp found).1

theorem count_false_set {marks : Array Bool} {address : Nat}
    (unmarked : marks[address]? = some false) :
    (marks.set! address true).count false + 1 = marks.count false := by
  have bound : address < marks.size := bound_of_some unmarked
  have entry : marks[address] = false := by simpa [Array.getElem?_eq_getElem bound] using unmarked
  have positive : 0 < marks.count false := by
    have member : false ∈ marks := Array.mem_of_getElem? unmarked
    exact Nat.pos_of_ne_zero (fun h => (Array.count_eq_zero.mp h) member)
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, bound, dite_true]
  rw [Array.count_set bound]
  simp [entry]
  omega

theorem all_marked {marks : Array Bool} (none : marks.count false = 0) (address : Nat) :
    marks[address]? ≠ some false := by
  intro isFalse
  have member : false ∈ marks := Array.mem_of_getElem? isFalse
  exact (Array.count_eq_zero.mp none) member

/-- The marking invariant: every unmarked child of a marked cell is still to be traced. -/
def Traced (heap : Array Cell) (marks : Array Bool) (work : List Nat) : Prop :=
  ∀ a x : Nat, marks[a]? = some true → x ∈ children heap a → marks[x]? = some false → x ∈ work

theorem markFrom_spec (heap : Array Cell) :
    ∀ (fuel : Nat) (marks : Array Bool) (work : List Nat),
      marks.size = heap.size → marks.count false ≤ fuel → Traced heap marks work →
      (markFrom heap fuel marks work).size = heap.size ∧
      (∀ a : Nat, marks[a]? = some true → (markFrom heap fuel marks work)[a]? = some true) ∧
      (∀ x ∈ work, (markFrom heap fuel marks work)[x]? ≠ some false) ∧
      (∀ a x : Nat, (markFrom heap fuel marks work)[a]? = some true → x ∈ children heap a →
        (markFrom heap fuel marks work)[x]? ≠ some false) := by
  intro fuel
  induction fuel with
  | zero =>
    intro marks work size count _
    have none : marks.count false = 0 := by omega
    simp only [markFrom]
    exact ⟨size, fun _ h => h, fun x _ => all_marked none x, fun _ x _ _ => all_marked none x⟩
  | succ fuel ih =>
    intro marks work size count traced
    simp only [markFrom]
    split
    · rename_i drained
      have done := pending_nil drained
      refine ⟨size, fun _ h => h, done, ?_⟩
      intro a x marked child isFalse
      exact done x (traced a x marked child isFalse) isFalse
    · rename_i address rest next
      obtain ⟨unmarked, covered⟩ := pending_cons next
      have bound : address < marks.size := bound_of_some unmarked
      have setAt : ∀ b, (marks.set! address true)[b]? = if address = b then some true else marks[b]? := by
        intro b; simp [Array.getElem?_setIfInBounds, bound]
      have size' : (marks.set! address true).size = heap.size := by simpa using size
      have count' : (marks.set! address true).count false ≤ fuel := by
        have := count_false_set unmarked; omega
      have traced' : Traced heap (marks.set! address true) (children heap address ++ rest) := by
        intro b x marked child isFalse
        rw [setAt] at marked isFalse
        by_cases same : address = b
        · subst same; exact List.mem_append_left _ child
        · rw [if_neg same] at marked
          by_cases sameX : address = x
          · rw [if_pos sameX] at isFalse; cases isFalse
          · rw [if_neg sameX] at isFalse
            have inWork := traced b x marked child isFalse
            rcases covered x inWork with notFalse | member
            · exact absurd isFalse notFalse
            · rcases List.mem_cons.mp member with rfl | member
              · exact absurd rfl sameX
              · exact List.mem_append_right _ member
      obtain ⟨outSize, monotone, drains, closed⟩ := ih _ _ size' count' traced'
      refine ⟨outSize, ?_, ?_, closed⟩
      · intro a marked
        apply monotone
        rw [setAt]; split
        · rfl
        · exact marked
      · intro x member
        rcases covered x member with notFalse | member
        · intro isFalse
          by_cases sameX : address = x
          · subst sameX
            have := monotone address (by rw [setAt]; simp)
            rw [this] at isFalse; cases isFalse
          · cases hx : marks[x]? with
            | none =>
              have : x ≥ marks.size := Array.getElem?_eq_none_iff.mp hx
              have : (markFrom heap fuel (marks.set! address true) (children heap address ++ rest))[x]? = none :=
                Array.getElem?_eq_none (by rw [outSize, ← size]; exact this)
              rw [this] at isFalse; cases isFalse
            | some value =>
              cases value with
              | false => exact notFalse hx
              | true =>
                have := monotone x (by rw [setAt, if_neg sameX]; exact hx)
                rw [this] at isFalse; cases isFalse
        · rcases List.mem_cons.mp member with same | member
          · have := monotone address (by rw [setAt]; simp)
            rw [same, this]; simp
          · exact drains x (List.mem_append_right _ member)

/-- **Marking soundness.** The live marks cover the heap, contain every root in the
heap, and are closed: a marked cell's in-heap children are marked. -/
theorem liveMarks_spec (state : State) :
    (liveMarks state).size = state.heap.size ∧
    (∀ x ∈ rootAddresses state, (liveMarks state)[x]? ≠ some false) ∧
    (∀ a x : Nat, (liveMarks state)[a]? = some true → x ∈ children state.heap a →
      (liveMarks state)[x]? ≠ some false) := by
  have initial := markFrom_spec state.heap state.heap.size (Array.replicate state.heap.size false)
    (rootAddresses state) (by simp) (by simp)
    (by intro a x marked; simp [Array.getElem?_replicate] at marked)
  exact ⟨initial.1, initial.2.2.1, initial.2.2.2⟩


/-! ## Ranks and compaction -/

theorem foldl_rankStep (l : List Bool) : ∀ (acc : Array Nat) (c : Nat),
    (l.foldl rankStep (acc, c)).2 = c + l.count true ∧
    (l.foldl rankStep (acc, c)).1.size = acc.size + l.length ∧
    (∀ i, i < acc.size → (l.foldl rankStep (acc, c)).1[i]? = acc[i]?) ∧
    (∀ i, i < l.length → (l.foldl rankStep (acc, c)).1[acc.size + i]? = some (c + (l.take i).count true)) := by
  induction l with
  | nil => intro acc c; simp
  | cons m rest ih =>
    intro acc c
    obtain ⟨count, size, prefix_, entries⟩ := ih (acc.push c) (if m then c + 1 else c)
    simp only [List.foldl_cons, rankStep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [count]; cases m <;> simp <;> omega
    · rw [size]; simp; omega
    · intro i bound
      rw [prefix_ i (by simp; omega)]
      simp [Array.getElem?_push, show i ≠ acc.size by omega]
    · intro i bound
      cases i with
      | zero =>
        simpa [Array.getElem?_push] using prefix_ acc.size (by simp)
      | succ j =>
        have := entries j (by simpa using bound)
        rw [show acc.size + (j + 1) = (acc.push c).size + j by simp; omega, this]
        cases m <;> simp <;> omega

theorem rankTable_spec (marks : Array Bool) :
    (rankTable marks).2 = marks.count true ∧
    (rankTable marks).1.size = marks.size ∧
    ∀ i, i < marks.size → (rankTable marks).1[i]? = some ((marks.toList.take i).count true) := by
  have spec := foldl_rankStep marks.toList #[] 0
  simp only [rankTable, ← Array.foldl_toList]
  refine ⟨by simpa using spec.1, by simpa using spec.2.1, ?_⟩
  intro i bound
  simpa using spec.2.2.2 i (by simpa using bound)

theorem filterMap_zip_getElem {α β : Type} (h : α → β) :
    ∀ (L : List α) (M : List Bool) (i : Nat) (c : α), L[i]? = some c → M[i]? = some true →
      ((L.zip M).filterMap fun entry => if entry.2 then some (h entry.1) else none)[(M.take i).count true]? =
        some (h c) := by
  intro L
  induction L with
  | nil => intro M i c found; simp at found
  | cons a L ih =>
    intro M i c found marked
    cases M with
    | nil => simp at marked
    | cons m M =>
      cases i with
      | zero =>
        simp at found marked
        subst found; subst marked
        simp
      | succ j =>
        simp only [List.getElem?_cons_succ] at found marked
        have := ih M j c found marked
        cases m <;> simpa [List.count_cons] using this

theorem filterMap_zip_length {α β : Type} (h : α → β) :
    ∀ (L : List α) (M : List Bool), L.length = M.length →
      ((L.zip M).filterMap fun entry => if entry.2 then some (h entry.1) else none).length = M.count true := by
  intro L
  induction L with
  | nil => intro M same; cases M <;> simp_all
  | cons a L ih =>
    intro M same
    cases M with
    | nil => simp at same
    | cons m M =>
      have := ih M (by simpa using same)
      cases m <;> simp [this]

theorem count_take_le (M : List Bool) {a b : Nat} (le : a ≤ b) :
    (M.take a).count true ≤ (M.take b).count true := by
  have : (M.take b).take a = M.take a := by rw [List.take_take]; congr 1; omega
  rw [← this]
  exact (List.take_sublist _ _).count_le _

theorem count_take_succ (M : List Bool) {i : Nat} (marked : M[i]? = some true) :
    (M.take (i + 1)).count true = (M.take i).count true + 1 := by
  rw [List.take_add_one, marked]; simp

theorem count_take_lt (M : List Bool) {i j : Nat} (lt : i < j) (marked : M[i]? = some true) :
    (M.take i).count true < (M.take j).count true := by
  have := count_take_le M (show i + 1 ≤ j by omega)
  rw [count_take_succ M marked] at this; omega

theorem count_take_lt_count (M : List Bool) {i : Nat} (marked : M[i]? = some true) :
    (M.take i).count true < M.count true := by
  have bound : i < M.length := (List.getElem?_eq_some_iff.mp marked).1
  have := count_take_lt M bound marked
  rwa [List.take_length] at this

theorem compact_size (f : Nat → Nat) (heap : Array Cell) (marks : Array Bool)
    (size : marks.size = heap.size) : (compact f heap marks).size = marks.count true := by
  rw [← Array.length_toList, compact, Array.toList_filterMap, Array.toList_zip, ← Array.count_toList]
  exact filterMap_zip_length _ _ _ (by simpa using size.symm)

theorem compact_getElem (f : Nat → Nat) (heap : Array Cell) (marks : Array Bool)
    {a : Nat} {c : Cell} (found : heap[a]? = some c) (marked : marks[a]? = some true) :
    (compact f heap marks)[(marks.toList.take a).count true]? = some (renameCell f c) := by
  rw [← Array.getElem?_toList, compact, Array.toList_filterMap, Array.toList_zip]
  exact filterMap_zip_getElem _ _ _ _ _ (by simpa using found) (by simpa using marked)

/-! ## The renaming simulation -/

def AllIn (D : Nat → Prop) (addresses : List Nat) : Prop := ∀ x ∈ addresses, D x

/-- Two heaps agree under a renaming `f` on a domain `D`: `D` contains everything past
the first heap (where `f` is the shift between the two ends), `f` is injective on `D`,
and every `D`-cell of the first heap is, renamed, the `f`-image cell of the second, with
its addresses again in `D`. Nothing is said about cells outside `D` (the garbage). -/
structure HeapRel (f : Nat → Nat) (D : Nat → Prop) (heap heap' : Array Cell) : Prop where
  size_le : heap'.size ≤ heap.size
  beyond : ∀ a, heap.size ≤ a → D a ∧ f a + heap.size = a + heap'.size
  inj : ∀ a b, D a → D b → f a = f b → a = b
  cells : ∀ a, D a → a < heap.size →
    ∃ c, heap[a]? = some c ∧ heap'[f a]? = some (renameCell f c) ∧ AllIn D (cellAddresses c)

/-- **The simulation relation.** `t` is `s` renamed by `f` on everything `s` can reach
(`D` is closed under the heap and contains the roots): same control, same stack, and
the `D`-cells agree. -/
structure Related (f : Nat → Nat) (D : Nat → Prop) (s t : State) : Prop where
  heap : HeapRel f D s.heap t.heap
  controlIn : AllIn D (controlAddresses s.control)
  control : t.control = renameControl f s.control
  stackIn : ∀ frame ∈ s.stack, AllIn D (frameAddresses frame)
  stack : t.stack = s.stack.map (renameFrame f)

/-- The domain `collect` traces: the live cells and everything past the heap. -/
def liveDomain (state : State) (a : Nat) : Prop :=
  state.heap.size ≤ a ∨ (liveMarks state)[a]? = some true

theorem liveDomain_of_not_false {state : State} {x : Nat}
    (notFalse : (liveMarks state)[x]? ≠ some false) : liveDomain state x := by
  by_cases bound : x < state.heap.size
  · right
    have size := (liveMarks_spec state).1
    have : x < (liveMarks state).size := by omega
    rw [Array.getElem?_eq_getElem this] at notFalse ⊢
    cases value : (liveMarks state)[x]
    · rw [value] at notFalse; exact absurd rfl notFalse
    · rfl
  · left; omega

theorem collectRenaming_live {state : State} {a : Nat} (marked : (liveMarks state)[a]? = some true) :
    collectRenaming state a = ((liveMarks state).toList.take a).count true := by
  have size := (liveMarks_spec state).1
  have bound : a < state.heap.size := by rw [← size]; exact bound_of_some marked
  have ranks := rankTable_spec (liveMarks state)
  simp only [collectRenaming, relocate, bound, if_true]
  rw [Array.getD_eq_getD_getElem?, ranks.2.2 a (by omega)]
  rfl

theorem collectRenaming_beyond {state : State} {a : Nat} (past : state.heap.size ≤ a) :
    collectRenaming state a = a - state.heap.size + (liveMarks state).count true := by
  have ranks := rankTable_spec (liveMarks state)
  simp only [collectRenaming, relocate, show ¬ a < state.heap.size by omega, if_false]
  rw [ranks.1]

theorem collect_heap_size (state : State) :
    (collect state).heap.size = (liveMarks state).count true :=
  compact_size _ _ _ (liveMarks_spec state).1

/-- **Collection is a renaming of the state it collects.** -/
theorem related_collect (state : State) :
    Related (collectRenaming state) (liveDomain state) state (collect state) := by
  obtain ⟨size, roots, closed⟩ := liveMarks_spec state
  have live_lt : ∀ a, (liveMarks state)[a]? = some true →
      collectRenaming state a < (liveMarks state).count true := by
    intro a marked
    rw [collectRenaming_live marked, ← Array.count_toList]
    exact count_take_lt_count _ (by simpa using marked)
  have count_le : (liveMarks state).count true ≤ state.heap.size := by
    rw [← size, ← Array.count_toList, ← Array.length_toList]; exact List.count_le_length
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, rfl, ?_, rfl⟩
  · rw [collect_heap_size]; exact count_le
  · intro a past
    refine ⟨.inl past, ?_⟩
    rw [collectRenaming_beyond past, collect_heap_size]; omega
  · intro a b inA inB same
    rcases inA with pastA | markedA <;> rcases inB with pastB | markedB
    · rw [collectRenaming_beyond pastA, collectRenaming_beyond pastB] at same; omega
    · have := live_lt b markedB; rw [collectRenaming_beyond pastA] at same; omega
    · have := live_lt a markedA; rw [collectRenaming_beyond pastB] at same; omega
    · rw [collectRenaming_live markedA, collectRenaming_live markedB] at same
      rcases Nat.lt_trichotomy a b with lt | eq | gt
      · have := count_take_lt (liveMarks state).toList lt (by simpa using markedA); omega
      · exact eq
      · have := count_take_lt (liveMarks state).toList gt (by simpa using markedB); omega
  · intro a inA bound
    have marked : (liveMarks state)[a]? = some true := by
      rcases inA with past | marked
      · omega
      · exact marked
    obtain ⟨c, found⟩ : ∃ c, state.heap[a]? = some c := ⟨_, Array.getElem?_eq_getElem bound⟩
    refine ⟨c, found, ?_, ?_⟩
    · rw [collectRenaming_live marked]
      exact compact_getElem _ _ _ found marked
    · intro x member
      apply liveDomain_of_not_false
      exact closed a x marked (by simp [children, found, member])
  · intro x member
    exact liveDomain_of_not_false (roots x (List.mem_append_left _ member))
  · intro frame member x inFrame
    exact liveDomain_of_not_false (roots x (List.mem_append_right _ (List.mem_flatMap.mpr ⟨frame, member, inFrame⟩)))


/-! ## Heap agreement is preserved by allocation and update -/

namespace HeapRel
variable {f : Nat → Nat} {D : Nat → Prop} {heap heap' : Array Cell}

theorem lookup (hr : HeapRel f D heap heap') {a : Nat} (inD : D a) :
    heap'[f a]? = (heap[a]?).map (renameCell f) := by
  by_cases bound : a < heap.size
  · obtain ⟨c, found, found', _⟩ := hr.cells a inD bound
    rw [found, found']; rfl
  · have shift := (hr.beyond a (Nat.le_of_not_lt bound)).2
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt bound), Array.getElem?_eq_none (by omega)]
    rfl

theorem cellIn (hr : HeapRel f D heap heap') {a : Nat} {c : Cell} (inD : D a)
    (found : heap[a]? = some c) : AllIn D (cellAddresses c) := by
  obtain ⟨c', found', _, inC⟩ := hr.cells a inD (bound_of_some found)
  rw [found] at found'; cases found'; exact inC

theorem image_size (hr : HeapRel f D heap heap') : f heap.size = heap'.size ∧ D heap.size := by
  have := hr.beyond heap.size (Nat.le_refl _); exact ⟨by omega, this.1⟩

theorem image_size_succ (hr : HeapRel f D heap heap') :
    f (heap.size + 1) = heap'.size + 1 ∧ D (heap.size + 1) := by
  have := hr.beyond (heap.size + 1) (Nat.le_succ _); exact ⟨by omega, this.1⟩

theorem push (hr : HeapRel f D heap heap') {c : Cell} (cIn : AllIn D (cellAddresses c)) :
    HeapRel f D (heap.push c) (heap'.push (renameCell f c)) := by
  have sizeLe := hr.size_le
  refine ⟨by simp; omega, ?_, hr.inj, ?_⟩
  · intro a past
    simp at past
    have := hr.beyond a (by omega)
    exact ⟨this.1, by simp; omega⟩
  · intro a inD bound
    simp at bound
    by_cases old : a < heap.size
    · obtain ⟨c', found, found', inC⟩ := hr.cells a inD old
      have lt : f a < heap'.size := bound_of_some found'
      refine ⟨c', ?_, ?_, inC⟩
      · simp [Array.getElem?_push, Nat.ne_of_lt old, found]
      · simp [Array.getElem?_push, Nat.ne_of_lt lt, found']
    · have eq : a = heap.size := by omega
      subst eq
      refine ⟨c, by simp, ?_, cIn⟩
      rw [hr.image_size.1]; simp

theorem set (hr : HeapRel f D heap heap') {a : Nat} {c : Cell} (inD : D a) (bound : a < heap.size)
    (cIn : AllIn D (cellAddresses c)) :
    HeapRel f D (heap.set! a c) (heap'.set! (f a) (renameCell f c)) := by
  obtain ⟨_, _, found', _⟩ := hr.cells a inD bound
  have lt : f a < heap'.size := bound_of_some found'
  refine ⟨by simp; exact hr.size_le, ?_, hr.inj, ?_⟩
  · intro b past; simp at past; have := hr.beyond b past; exact ⟨this.1, by simp; exact this.2⟩
  · intro b inB boundB
    simp at boundB
    by_cases same : a = b
    · subst same
      exact ⟨c, by simp [bound],
        by simp [lt], cIn⟩
    · obtain ⟨c', found, found'', inC⟩ := hr.cells b inB boundB
      have diff : f a ≠ f b := fun h => same (hr.inj a b inD inB h)
      exact ⟨c', by simp [same, found],
        by simp [diff, found''], inC⟩

end HeapRel

theorem allocateFields_foldl {f : Nat → Nat} {D : Nat → Prop} (environment : List Nat)
    (environmentIn : AllIn D environment) (fields : List (String × Term)) :
    ∀ (heap heap' : Array Cell) (acc : List (String × Nat)),
      HeapRel f D heap heap' → AllIn D (acc.map Prod.snd) →
      HeapRel f D
          (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (heap,acc)).1
          (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment.map f⟩),(field.1,prior.1.size)::prior.2))
            (heap',acc.map fun field => (field.1, f field.2))).1 ∧
        (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment.map f⟩),(field.1,prior.1.size)::prior.2))
            (heap',acc.map fun field => (field.1, f field.2))).2 =
          (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2))
            (heap,acc)).2.map (fun field => (field.1, f field.2)) ∧
        AllIn D ((fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2))
            (heap,acc)).2.map Prod.snd) := by
  induction fields with
  | nil => intro heap heap' acc hr accIn; exact ⟨hr, rfl, accIn⟩
  | cons field rest ih =>
    intro heap heap' acc hr accIn
    have ⟨image, sizeIn⟩ := hr.image_size
    have pushed := hr.push (c := .suspended ⟨field.2, environment⟩) environmentIn
    have accIn' : AllIn D (((field.1, heap.size) :: acc).map Prod.snd) := by
      intro x member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact sizeIn
      · exact accIn x member
    have := ih _ _ _ pushed accIn'
    simp only [List.foldl_cons]
    simp only [List.map_cons, image] at this
    exact this

theorem allocateFields_related {f : Nat → Nat} {D : Nat → Prop} {heap heap' : Array Cell}
    (hr : HeapRel f D heap heap') {environment : List Nat} (environmentIn : AllIn D environment)
    (fields : List (String × Term)) :
    HeapRel f D (allocateFields heap environment fields).1
        (allocateFields heap' (environment.map f) fields).1 ∧
      (allocateFields heap' (environment.map f) fields).2 =
        (allocateFields heap environment fields).2.map (fun field => (field.1, f field.2)) ∧
      AllIn D ((allocateFields heap environment fields).2.map Prod.snd) := by
  obtain ⟨hr', same, inside⟩ := allocateFields_foldl environment environmentIn fields heap heap' []
    hr (fun _ member => by cases member)
  refine ⟨hr', ?_, ?_⟩
  · simp only [allocateFields]
    simp only [List.map_nil] at same
    rw [same, List.map_reverse]
  · intro x member
    simp only [allocateFields, List.map_reverse, List.mem_reverse] at member
    exact inside x member


/-! ## Lockstep: one machine transition -/

theorem forcingShared_rename (f : Nat → Nat) (stack : List Frame) :
    forcingShared (stack.map (renameFrame f)) = forcingShared stack := by
  induction stack with
  | nil => rfl
  | cons frame rest ih =>
    simp only [forcingShared, List.map_cons, List.any_cons] at ih ⊢
    rw [ih]; cases frame <;> rfl

theorem valueTerm_rename (f : Nat → Nat) (value : RuntimeValue) :
    valueTerm (renameValue f value) = valueTerm value := by
  cases value <;> rfl

theorem scalarValue_rename {f : Nat → Nat} {result : Term} {next : RuntimeValue}
    (scalar : scalarValue result = some next) : renameValue f next = next ∧ valueAddresses next = [] := by
  cases result <;> simp [scalarValue] at scalar <;> subst scalar <;> exact ⟨rfl, rfl⟩

theorem allIn_nil (D : Nat → Prop) : AllIn D [] := fun _ member => by cases member

theorem allIn_cons {D : Nat → Prop} {a : Nat} {rest : List Nat} (head : D a) (tail : AllIn D rest) :
    AllIn D (a :: rest) := by
  intro x member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail x member

theorem allIn_append {D : Nat → Prop} {first second : List Nat} (one : AllIn D first)
    (two : AllIn D second) : AllIn D (first ++ second) := by
  intro x member
  rcases List.mem_append.mp member with member | member
  · exact one x member
  · exact two x member

theorem frames_cons {D : Nat → Prop} {frame : Frame} {rest : List Frame}
    (head : AllIn D (frameAddresses frame)) (tail : ∀ frame ∈ rest, AllIn D (frameAddresses frame)) :
    ∀ frame' ∈ frame :: rest, AllIn D (frameAddresses frame') :=
  List.forall_mem_cons.mpr ⟨head, tail⟩

/-- **Lockstep.** A related pair steps to a related pair: the renaming and its domain
are fixed, and the two machines allocate at the two heap ends (`f heap.size = heap'.size`). -/
theorem related_stepRaw {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t) :
    Related f D (stepRaw s) (stepRaw t) := by
  obtain ⟨hr, controlIn, controlEq, stackIn, stackEq⟩ := related
  obtain ⟨heap, control, stack⟩ := s
  obtain ⟨heap', control', stack'⟩ := t
  simp only at hr controlIn controlEq stackIn stackEq
  subst controlEq stackEq
  have ⟨image, sizeIn⟩ := hr.image_size
  have ⟨image1, sizeIn1⟩ := hr.image_size_succ
  cases control with
  | complete v => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
  | refused r => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
  | blackhole a => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
  | yielded p => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
  | enter a =>
    have inA : D a := controlIn a (List.mem_singleton_self a)
    simp only [stepRaw, renameControl]
    rw [hr.lookup inA]
    cases found : heap[a]? with
    | none => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | some cell =>
      have cellIn := hr.cellIn inA found
      cases cell with
      | evaluating o => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
      | cached o v => exact ⟨hr, fun x member => cellIn x (List.mem_append_right _ member), rfl, stackIn, rfl⟩
      | suspended o =>
        exact ⟨hr.set inA (bound_of_some found) (c := .evaluating o) cellIn, cellIn, rfl,
          frames_cons (allIn_cons inA (allIn_nil D)) stackIn, rfl⟩
  | evaluate term env =>
    have envIn : AllIn D env := controlIn
    cases term with
    | bound i =>
      simp only [stepRaw, renameControl]
      rw [List.getElem?_map]
      cases found : env[i]? with
      | none => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
      | some a => exact ⟨hr, allIn_cons (envIn a (List.mem_of_getElem? found)) (allIn_nil D), rfl, stackIn, rfl⟩
    | lam body => exact ⟨hr, envIn, rfl, stackIn, rfl⟩
    | nat n => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | boolean b => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | label l => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | app fn arg => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | mix lower upper => exact ⟨hr, envIn, rfl, stackIn, rfl⟩
    | fix spec inherited =>
      have pushed := hr.push (c := .suspended ⟨Term.app (Term.app (spec.rename Nat.succ) (.bound 0))
        (inherited.rename Nat.succ), heap.size :: env⟩) (allIn_cons sizeIn envIn)
      simp only [renameCell, renameClosure, List.map_cons, image] at pushed
      refine ⟨pushed, allIn_cons sizeIn (allIn_nil D), ?_, stackIn, rfl⟩
      simp [stepRaw, renameControl, image]
    | specification descriptor extension =>
      have pushed := (hr.push (c := .suspended ⟨descriptor, env⟩) envIn).push
        (c := .suspended ⟨extension, env⟩) envIn
      refine ⟨pushed, allIn_cons sizeIn (allIn_cons sizeIn1 (allIn_nil D)), ?_, stackIn, rfl⟩
      simp [stepRaw, renameControl, renameValue, image, image1]
    | prototype spec target =>
      have pushed := (hr.push (c := .suspended ⟨spec, env⟩) envIn).push
        (c := .suspended ⟨target, env⟩) envIn
      refine ⟨pushed, allIn_cons sizeIn (allIn_cons sizeIn1 (allIn_nil D)), ?_, stackIn, rfl⟩
      simp [stepRaw, renameControl, renameValue, image, image1]
    | reflect body => exact ⟨hr, envIn, rfl, frames_cons (allIn_nil D) stackIn, rfl⟩
    | metadata body => exact ⟨hr, envIn, rfl, frames_cons (allIn_nil D) stackIn, rfl⟩
    | project body => exact ⟨hr, envIn, rfl, frames_cons (allIn_nil D) stackIn, rfl⟩
    | record fields =>
      obtain ⟨hr', same, inside⟩ := allocateFields_related hr envIn fields
      refine ⟨hr', inside, ?_, stackIn, rfl⟩
      simp only [stepRaw, renameControl, renameValue, same]
    | get target name => exact ⟨hr, envIn, rfl, frames_cons (allIn_nil D) stackIn, rfl⟩
    | extend inherited fields => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | ifZero value zero successorBody => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | binary primitive left right => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | inject tag payload =>
      have pushed := hr.push (c := .suspended ⟨payload, env⟩) envIn
      refine ⟨pushed, allIn_cons sizeIn (allIn_nil D), ?_, stackIn, rfl⟩
      simp [stepRaw, renameControl, renameValue, image]
    | case scrutinee arms => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | ifBool condition whenTrue whenFalse => exact ⟨hr, envIn, rfl, frames_cons envIn stackIn, rfl⟩
    | done value => exact ⟨hr, envIn, rfl, stackIn, rfl⟩
    | perform plan =>
      simp only [stepRaw, renameControl, forcingShared_rename]
      cases shared : forcingShared stack with
      | true => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
      | false =>
        have pushed := hr.push (c := .suspended ⟨plan, env⟩) envIn
        refine ⟨pushed, allIn_cons sizeIn (allIn_nil D), ?_, stackIn, rfl⟩
        simp [renameControl, image]
  | returned v =>
    have valueIn : AllIn D (valueAddresses v) := controlIn
    cases stack with
    | nil => exact ⟨hr, valueIn, rfl, stackIn, rfl⟩
    | cons frame rest =>
      have ⟨frameIn, restIn⟩ := List.forall_mem_cons.mp stackIn
      cases frame with
      | update a =>
        have inA : D a := frameIn a (List.mem_singleton_self a)
        simp only [stepRaw, renameControl, List.map_cons, renameFrame]
        rw [hr.lookup inA]
        cases found : heap[a]? with
        | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
        | some cell =>
          have cellIn := hr.cellIn inA found
          cases cell with
          | suspended o => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | cached o w => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | evaluating o =>
            exact ⟨hr.set inA (bound_of_some found) (c := .cached o v) (allIn_append cellIn valueIn),
              valueIn, rfl, restIn, rfl⟩
      | reflect =>
        cases v with
        | prototype spec target =>
          exact ⟨hr, allIn_cons (valueIn spec (by simp [valueAddresses])) (allIn_nil D), rfl, restIn, rfl⟩
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | metadata =>
        cases v with
        | specification descriptor extension =>
          exact ⟨hr, allIn_cons (valueIn descriptor (by simp [valueAddresses])) (allIn_nil D), rfl, restIn, rfl⟩
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | project =>
        cases v with
        | prototype spec target =>
          exact ⟨hr, allIn_cons (valueIn target (by simp [valueAddresses])) (allIn_nil D), rfl, restIn, rfl⟩
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | argument argument environment =>
        cases v with
        | specification descriptor extension =>
          exact ⟨hr, allIn_cons (valueIn extension (by simp [valueAddresses])) (allIn_nil D), rfl, stackIn, rfl⟩
        | closure body captured =>
          have environmentIn : AllIn D environment := frameIn
          have capturedIn : AllIn D captured := valueIn
          have pushed := hr.push (c := .suspended ⟨argument, environment⟩) environmentIn
          refine ⟨pushed, allIn_cons sizeIn capturedIn, ?_, restIn, rfl⟩
          simp [stepRaw, renameControl, renameValue, renameFrame, image]
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | field name =>
        cases v with
        | record fields =>
          simp only [stepRaw, renameControl, renameValue, List.map_cons, renameFrame, List.find?_map,
            Function.comp_def]
          cases found : fields.find? (fun field => field.1 == name) with
          | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | some entry =>
            have member := List.mem_of_find?_eq_some found
            exact ⟨hr, allIn_cons (valueIn entry.2 (List.mem_map_of_mem member)) (allIn_nil D), rfl, restIn, rfl⟩
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | extend fields environment =>
        cases v with
        | record inherited =>
          have environmentIn : AllIn D environment := frameIn
          obtain ⟨hr', same, inside⟩ := allocateFields_related hr environmentIn fields
          refine ⟨hr', ?_, ?_, restIn, rfl⟩
          · have retainedIn : AllIn D ((inherited.filter
                (fun prior => !(fields.any fun field => field.1 == prior.1))).map Prod.snd) := by
              intro x member
              obtain ⟨entry, kept, eq⟩ := List.mem_map.mp member
              rw [← eq]; exact valueIn _ (List.mem_map_of_mem (List.mem_filter.mp kept).1)
            have := allIn_append inside retainedIn
            rw [← List.map_append] at this
            exact this
          · simp only [stepRaw, renameControl, renameValue, List.map_cons, renameFrame, same,
              List.filter_map, Function.comp_def, List.map_append]
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | condition zero successorBody environment =>
        cases v with
        | natural n =>
          cases n with
          | zero => exact ⟨hr, frameIn, rfl, restIn, rfl⟩
          | succ n =>
            have environmentIn : AllIn D environment := frameIn
            have pushed := hr.push (c := .cached ⟨.nat n, []⟩ (.natural n)) (allIn_nil D)
            refine ⟨pushed, allIn_cons sizeIn environmentIn, ?_, restIn, rfl⟩
            simp [stepRaw, renameControl, renameFrame, renameValue, image]
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | binaryLeft primitive right environment =>
        exact ⟨hr, frameIn, rfl, frames_cons valueIn restIn, rfl⟩
      | binaryRight primitive left =>
        simp only [stepRaw, renameControl, List.map_cons, renameFrame, valueTerm_rename]
        cases computed : (valueTerm left).bind (fun l => (valueTerm v).bind (primitiveResult primitive l)) with
        | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
        | some result =>
          dsimp only
          cases scalar : scalarValue result with
          | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | some next =>
            have ⟨renamed, empty⟩ := scalarValue_rename (f := f) scalar
            refine ⟨hr, ?_, ?_, restIn, rfl⟩
            · show AllIn D (valueAddresses next); rw [empty]; exact allIn_nil D
            · simp [renameControl, renamed]
      | case arms environment =>
        cases v with
        | variant tag payload =>
          simp only [stepRaw, renameControl, renameValue, List.map_cons, renameFrame]
          cases found : arms.find? (fun arm => arm.1 == tag) with
          | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | some arm =>
            have environmentIn : AllIn D environment := frameIn
            have pushed := hr.push (c := .suspended ⟨.bound 0, [payload]⟩) valueIn
            refine ⟨pushed, allIn_cons sizeIn environmentIn, ?_, restIn, rfl⟩
            simp [renameControl, image]
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
      | ifBool whenTrue whenFalse environment =>
        cases v with
        | boolean b => cases b <;> exact ⟨hr, frameIn, rfl, restIn, rfl⟩
        | _ => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩


/-! ## Bounded runs, resumption and composition -/

/-- Outcomes agree under the renaming: same constructor, same reason, renamed payload,
related retained states. -/
def OutcomeRel (f : Nat → Nat) (D : Nat → Prop) : Outcome → Outcome → Prop
  | .finished value s, .finished value' t =>
    value' = renameValue f value ∧ AllIn D (valueAddresses value) ∧ Related f D s t
  | .suspended reason s, .suspended reason' t => reason' = reason ∧ Related f D s t
  | .divergent address s, .divergent address' t => address' = f address ∧ Related f D s t
  | .refused reason s, .refused reason' t => reason' = reason ∧ Related f D s t
  | .yielded plan s, .yielded plan' t => plan' = f plan ∧ Related f D s t
  | _, _ => False

/-- The one outcome a collected state may improve on: running out of heap. -/
def ranOutOfHeap : Outcome → Bool
  | .suspended .capacity _ => true
  | _ => false

theorem Related.stack_length {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t) :
    t.stack.length = s.stack.length := by
  rw [related.stack, List.length_map]

/-- The gap between the two heap ends is fixed by the renaming: every pair related by
`f` has the same gap (allocation is lockstep). -/
theorem Related.gap {f : Nat → Nat} {D : Nat → Prop} {s t s' t' : State} (one : Related f D s t)
    (two : Related f D s' t') : s.heap.size - t.heap.size = s'.heap.size - t'.heap.size := by
  have a := (one.heap.beyond (s.heap.size + s'.heap.size) (by omega)).2
  have b := (two.heap.beyond (s.heap.size + s'.heap.size) (by omega)).2
  have c := one.heap.size_le
  have d := two.heap.size_le
  omega

theorem runBounded_zero_related {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t)
    (limits limits' : Limits) : OutcomeRel f D (runBounded limits 0 s) (runBounded limits' 0 t) := by
  have controlEq := related.control
  cases control : s.control <;> rw [control] at controlEq <;>
    simp only [runBounded, control, controlEq, renameControl, OutcomeRel, true_and] <;>
    first
      | exact related
      | exact ⟨by have inside := related.controlIn; rw [control] at inside; exact inside, related⟩

/-- An active control is the only one `step` advances. -/
def active : Control → Bool
  | .evaluate _ _ | .enter _ | .returned _ => true
  | _ => false

theorem runBounded_succ_active {limits : Limits} {ticks : Nat} {s : State} (isActive : active s.control = true) :
    runBounded limits (ticks + 1) s =
      if (stepRaw s).heap.size ≤ limits.heap ∧ (stepRaw s).stack.length ≤ limits.stack then
        runBounded limits ticks (stepRaw s) else .suspended .capacity s := by
  have stepEq : step limits s =
      if (stepRaw s).heap.size ≤ limits.heap ∧ (stepRaw s).stack.length ≤ limits.stack then
        .suspended .ticks (stepRaw s) else .suspended .capacity s := by
    cases control : s.control <;> rw [control] at isActive <;> simp [active] at isActive <;>
      simp [step, control]
  simp only [runBounded, stepEq]
  by_cases fits : (stepRaw s).heap.size ≤ limits.heap ∧ (stepRaw s).stack.length ≤ limits.stack <;>
    simp [fits]

theorem runBounded_succ_inactive {limits : Limits} {ticks : Nat} {s : State} (inactive : active s.control = false) :
    runBounded limits (ticks + 1) s = runBounded limits 0 s := by
  cases control : s.control <;> rw [control] at inactive <;> simp [active] at inactive <;>
    simp [runBounded, step, control]

theorem active_rename (f : Nat → Nat) (control : Control) :
    active (renameControl f control) = active control := by
  cases control <;> rfl

/-- `limits'` gives the related state `t` at least the room `limits` gives `s`: a heap
limit short by at most the gap between the two heaps (the cells collection freed), and
no smaller a stack limit. The gap is the same for every pair one renaming relates
(`Related.gap`), so the room is too (`RoomFor.shift`). Two instances: the same limits
(`RoomFor.same`), and limits counted from each state's own heap end
(`collect_resume_segment`'s use in `Kernel.ObjectiveResumeContract`). -/
structure RoomFor (limits limits' : Limits) (s t : State) : Prop where
  heap : limits.heap ≤ limits'.heap + (s.heap.size - t.heap.size)
  stack : limits.stack ≤ limits'.stack

theorem RoomFor.same (limits : Limits) (s t : State) : RoomFor limits limits s t :=
  ⟨Nat.le_add_right _ _, Nat.le_refl _⟩

theorem RoomFor.shift {f : Nat → Nat} {D : Nat → Prop} {limits limits' : Limits} {s t s' t' : State}
    (one : Related f D s t) (two : Related f D s' t') (room : RoomFor limits limits' s t) :
    RoomFor limits limits' s' t' :=
  ⟨by rw [← one.gap two]; exact room.heap, room.stack⟩

/-- `RoomFor`'s refuting pole: one more cell of limit than the related side gets, with no gap
to cover it (its satisfying pole is `RoomFor.same`). -/
theorem not_roomFor_short : ¬ RoomFor ⟨1, 0⟩ ⟨0, 0⟩ (initial (.nat 0)) (initial (.nat 0)) := by
  intro room
  have := room.heap
  simp [initial] at this

/-- **Bounded runs agree**, except where the original ran out of heap, for any limits that
give the related state at least the original's room (`RoomFor`: the collected state, whose
heap is no larger, may go further). -/
theorem related_runBounded {f : Nat → Nat} {D : Nat → Prop} (limits limits' : Limits) :
    ∀ (ticks : Nat) (s t : State), Related f D s t → RoomFor limits limits' s t →
      ranOutOfHeap (runBounded limits ticks s) = false →
      OutcomeRel f D (runBounded limits ticks s) (runBounded limits' ticks t) := by
  intro ticks
  induction ticks with
  | zero => intro s t related _ _; exact runBounded_zero_related related limits limits'
  | succ ticks ih =>
    intro s t related room notCapacity
    have activeT : active t.control = active s.control := by rw [related.control, active_rename]
    cases isActive : active s.control with
    | false =>
      rw [runBounded_succ_inactive isActive, runBounded_succ_inactive (by rw [activeT, isActive])]
      exact runBounded_zero_related related limits limits'
    | true =>
      have next := related_stepRaw related
      have gap := related.gap next
      have nextLe := next.heap.size_le
      have heapRoom := room.heap
      rw [runBounded_succ_active isActive] at notCapacity ⊢
      rw [runBounded_succ_active (by rw [activeT, isActive])]
      by_cases fits : (stepRaw s).heap.size ≤ limits.heap ∧ (stepRaw s).stack.length ≤ limits.stack
      · have fitsT : (stepRaw t).heap.size ≤ limits'.heap ∧ (stepRaw t).stack.length ≤ limits'.stack :=
          ⟨by have := fits.1; omega, by rw [next.stack_length]; exact Nat.le_trans fits.2 room.stack⟩
        rw [if_pos fits] at notCapacity ⊢
        rw [if_pos fitsT]
        exact ih _ _ next (room.shift related next) notCapacity
      · rw [if_neg fits] at notCapacity
        simp [ranOutOfHeap] at notCapacity

/-- **Exact agreement.** Given back the heap it freed (the gap `s.heap.size - t.heap.size`),
the collected run takes exactly the original's transitions, capacity suspensions included. -/
theorem related_runBounded_exact {f : Nat → Nat} {D : Nat → Prop} (limits : Limits) :
    ∀ (ticks : Nat) (s t : State), Related f D s t → s.heap.size ≤ limits.heap →
      OutcomeRel f D (runBounded limits ticks s)
        (runBounded ⟨limits.heap - (s.heap.size - t.heap.size), limits.stack⟩ ticks t) := by
  intro ticks
  induction ticks with
  | zero => intro s t related _; exact runBounded_zero_related related _ _
  | succ ticks ih =>
    intro s t related fitsNow
    have activeT : active t.control = active s.control := by rw [related.control, active_rename]
    cases isActive : active s.control with
    | false =>
      rw [runBounded_succ_inactive isActive, runBounded_succ_inactive (by rw [activeT, isActive])]
      exact runBounded_zero_related related _ _
    | true =>
      have next := related_stepRaw related
      have gap := related.gap next
      have sizeLe := related.heap.size_le
      have nextLe := next.heap.size_le
      rw [runBounded_succ_active isActive, runBounded_succ_active (by rw [activeT, isActive])]
      by_cases fits : (stepRaw s).heap.size ≤ limits.heap ∧ (stepRaw s).stack.length ≤ limits.stack
      · have fitsT : (stepRaw t).heap.size ≤ limits.heap - (s.heap.size - t.heap.size) ∧
            (stepRaw t).stack.length ≤ limits.stack := ⟨by omega, by rw [next.stack_length]; exact fits.2⟩
        rw [if_pos fits, if_pos fitsT]
        have := ih _ _ next fits.1
        rwa [← gap] at this
      · have notT : ¬ ((stepRaw t).heap.size ≤ limits.heap - (s.heap.size - t.heap.size) ∧
            (stepRaw t).stack.length ≤ limits.stack) := by
          intro fitsT; apply fits
          exact ⟨by omega, by rw [← next.stack_length]; exact fitsT.2⟩
        rw [if_neg fits, if_neg notT]
        exact ⟨rfl, related⟩

/-- **Resumption agrees**, with any response term (a response captures no address). -/
theorem related_resume {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t)
    (response : Term) {s' : State} (resumed : resume response s = some s') :
    ∃ t', resume response t = some t' ∧ Related f D s' t' := by
  obtain ⟨plan, yielded⟩ := resume_requires_yield response s (by rw [resumed]; rfl)
  have controlT : t.control = .yielded (f plan) := by rw [related.control, yielded]; rfl
  simp only [resume, yielded] at resumed
  cases resumed
  refine ⟨{t with control := .evaluate response []}, by simp [resume, controlT], ?_⟩
  exact ⟨related.heap, allIn_nil D, rfl, related.stackIn, related.stack⟩


/-! ## Extracted Data agrees -/

section ExceptLemmas
variable {ε α β : Type}
@[simp] theorem except_throw_bind (e : ε) (k : α → Except ε β) : (throw e >>= k : Except ε β) = .error e := rfl
@[simp] theorem except_map_throw (g : α → β) (e : ε) : (g <$> (throw e : Except ε α)) = .error e := rfl
@[simp] theorem except_throw_ok (e : ε) (a : α) : ((throw e : Except ε α) = .ok a) ↔ False := by
  constructor <;> intro h <;> cases h
@[simp] theorem except_error_ok (e : ε) (a : α) : ((Except.error e : Except ε α) = .ok a) ↔ False := by
  constructor <;> intro h <;> cases h
@[simp] theorem except_bind_ok (x : Except ε α) (k : α → Except ε β) (r : β) :
    (x >>= k) = .ok r ↔ ∃ a, x = .ok a ∧ k a = .ok r := by
  cases x <;> simp [bind, Except.bind]
@[simp] theorem except_map_ok (g : α → β) (x : Except ε α) (r : β) :
    (g <$> x) = .ok r ↔ ∃ a, x = .ok a ∧ g a = r := by
  cases x <;> simp [Functor.map, Except.map]
@[simp] theorem except_pure_ok (a b : α) : ((pure a : Except ε α) = .ok b) ↔ a = b := by
  simp [pure, Except.pure]
end ExceptLemmas

open Minidregg.Theory.ObjectiveBendDemandData

/-- The continuation `forceWith` takes after one bounded transition. -/
def continueForce (policy : State → Bool) (limits : Limits) (ticks : Nat) : Outcome → Outcome × Nat
  | .suspended .ticks next => forceWith policy limits ticks next
  | other => (other, ticks)

theorem forceWith_succ_inactive {policy : State → Bool} {limits : Limits} {ticks : Nat} {s : State}
    (inactive : active s.control = false) :
    forceWith policy limits (ticks + 1) s = (runBounded limits 0 s, ticks + 1) := by
  cases control : s.control <;> rw [control] at inactive <;> simp [active] at inactive <;>
    simp [forceWith, control]

theorem forceWith_succ_active {policy : State → Bool} {limits : Limits} {ticks : Nat} {s : State}
    (isActive : active s.control = true) :
    forceWith policy limits (ticks + 1) s =
      if policy s = false then (.suspended .capacity s, ticks + 1)
      else continueForce policy limits ticks (runBounded limits 1 s) := by
  cases control : s.control <;> rw [control] at isActive <;> simp [active] at isActive <;>
    simp only [forceWith, control] <;> cases policy s <;> simp <;>
    cases runBounded limits 1 s <;> simp [continueForce] <;> rename_i reason _ <;> cases reason <;> rfl

/-- **Forcing agrees** (the bounded forcing every extraction runs), for any policy that
a related state passes whenever the original does (the kernel's is constantly true). -/
theorem related_forceWith {f : Nat → Nat} {D : Nat → Prop} {policy : State → Bool}
    (respects : ∀ s t, Related f D s t → policy s = true → policy t = true) (limits limits' : Limits) :
    ∀ (ticks : Nat) (s t : State), Related f D s t → RoomFor limits limits' s t →
      ranOutOfHeap (forceWith policy limits ticks s).1 = false →
      OutcomeRel f D (forceWith policy limits ticks s).1 (forceWith policy limits' ticks t).1 ∧
        (forceWith policy limits' ticks t).2 = (forceWith policy limits ticks s).2 := by
  intro ticks
  induction ticks with
  | zero => intro s t related _ _; exact ⟨runBounded_zero_related related limits limits', rfl⟩
  | succ ticks ih =>
    intro s t related room notCapacity
    have activeT : active t.control = active s.control := by rw [related.control, active_rename]
    cases isActive : active s.control with
    | false =>
      rw [forceWith_succ_inactive isActive, forceWith_succ_inactive (by rw [activeT, isActive])]
      exact ⟨runBounded_zero_related related limits limits', rfl⟩
    | true =>
      rw [forceWith_succ_active isActive] at notCapacity ⊢
      rw [forceWith_succ_active (by rw [activeT, isActive])]
      cases allowed : policy s with
      | false => simp [allowed, ranOutOfHeap] at notCapacity
      | true =>
        have allowedT := respects s t related allowed
        simp only [allowed, allowedT, Bool.true_eq_false, if_false] at notCapacity ⊢
        cases ran : runBounded limits 1 s with
        | suspended reason next =>
          cases reason with
          | ticks =>
            have rel := related_runBounded limits limits' 1 s t related room (by rw [ran]; rfl)
            rw [ran] at rel
            cases ranT : runBounded limits' 1 t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
            obtain ⟨same, nextRel⟩ := rel
            subst same
            rw [ran] at notCapacity
            exact ih _ _ nextRel (room.shift related nextRel) notCapacity
          | capacity => rw [ran] at notCapacity; simp [continueForce, ranOutOfHeap] at notCapacity
        | finished value next | divergent value next | refused value next | yielded value next =>
          have rel := related_runBounded limits limits' 1 s t related room (by rw [ran]; rfl)
          rw [ran] at rel
          cases ranT : runBounded limits' 1 t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
          all_goals exact ⟨rel, rfl⟩


/-- Extraction results agree: same Data, same remaining budget, related states. -/
def ResultRel (f : Nat → Nat) (D : Nat → Prop) (r r' : Result) : Prop :=
  r'.value = r.value ∧ r'.remaining = r.remaining ∧ Related f D r.state r'.state

/-- One field of a record's materialization (the body of `materializeWith`'s fold). -/
def recordStep (policy : State → Bool) (limits : Limits) (depth : Nat)
    (prior : List (String × Data) × State × Budget) (field : String × Nat) :
    Except (Failure × State × Budget) (List (String × Data) × State × Budget) := do
  let bytes := field.1.utf8ByteSize+(toString field.1.utf8ByteSize).utf8ByteSize+1
  if bytes > prior.2.2.bytes || prior.2.2.nodes = 0 then throw (.budget,prior.2.1,prior.2.2)
  let entered : State := {prior.2.1 with control:=.enter field.2,stack:=[]}
  let (outcome,ticks) := forceWith policy limits prior.2.2.ticks entered
  let nextBudget := {prior.2.2 with ticks:=ticks,bytes:=prior.2.2.bytes-bytes}
  match outcome with
  | .finished forced retained =>
    let child ← materializeWith policy limits depth nextBudget forced retained
    pure ((field.1,child.value)::prior.1,child.state,child.remaining)
  | .suspended reason retained => throw (suspensionFailure reason,retained,nextBudget)
  | .divergent _ retained => throw (.divergent,retained,nextBudget)
  | .refused _ retained => throw (.refused,retained,nextBudget)
  | .yielded _ retained => throw (.yielded,retained,nextBudget)

theorem materializeWith_record (policy : State → Bool) (limits : Limits) (depth : Nat) (budget : Budget)
    (fields : List (String × Nat)) (state : State) :
    materializeWith policy limits (depth+1) budget (.record fields) state = (do
      if budget.nodes = 0 then throw (.budget,state,budget)
      let remaining := {budget with nodes:=budget.nodes-1}
      let headerBytes := (toString fields.length).utf8ByteSize+2
      if headerBytes > remaining.bytes then throw (.budget,state,remaining)
      let remaining := {remaining with bytes:=remaining.bytes-headerBytes}
      if (fields.map Prod.fst).eraseDups.length != fields.length then throw (.duplicateField,state,remaining)
      if fields.length > remaining.nodes then throw (.budget,state,remaining)
      let pair ← fields.foldlM (recordStep policy limits depth) ([],state,remaining)
      pure ⟨.record pair.1.reverse,pair.2.1,pair.2.2⟩) := rfl

theorem foldlM_related {f : Nat → Nat} {D : Nat → Prop}
    {step step' : List (String × Data) × State × Budget → String × Nat →
      Except (Failure × State × Budget) (List (String × Data) × State × Budget)}
    (stepRel : ∀ (acc : List (String × Data)) (st st' : State) (b : Budget) (field : String × Nat)
        (out : List (String × Data) × State × Budget),
      Related f D st st' → D field.2 → step (acc, st, b) field = .ok out →
      ∃ out', step' (acc, st', b) (field.1, f field.2) = .ok out' ∧ out'.1 = out.1 ∧ out'.2.2 = out.2.2 ∧
        Related f D out.2.1 out'.2.1) :
    ∀ (fields : List (String × Nat)) (acc : List (String × Data)) (st st' : State) (b : Budget)
      (out : List (String × Data) × State × Budget),
      Related f D st st' → AllIn D (fields.map Prod.snd) → fields.foldlM step (acc, st, b) = .ok out →
      ∃ out', (fields.map fun field => (field.1, f field.2)).foldlM step' (acc, st', b) = .ok out' ∧
        out'.1 = out.1 ∧ out'.2.2 = out.2.2 ∧ Related f D out.2.1 out'.2.1 := by
  intro fields
  induction fields with
  | nil =>
    intro acc st st' b out related _ folded
    simp [List.foldlM] at folded
    subst folded
    exact ⟨_, rfl, rfl, rfl, related⟩
  | cons field rest ih =>
    intro acc st st' b out related inside folded
    simp only [List.foldlM_cons, except_bind_ok] at folded
    obtain ⟨mid, first, restFolded⟩ := folded
    obtain ⟨mid', first', same1, same2, midRel⟩ :=
      stepRel acc st st' b field mid related (inside field.2 (by simp)) first
    obtain ⟨out', folded', outSame1, outSame2, outRel⟩ :=
      ih mid.1 mid.2.1 mid'.2.1 mid.2.2 out midRel (fun x member => inside x (by simp [member]))
        restFolded
    refine ⟨out', ?_, outSame1, outSame2, outRel⟩
    simp only [List.map_cons, List.foldlM_cons, except_bind_ok]
    refine ⟨mid', first', ?_⟩
    have shape : mid' = (mid.1, mid'.2.1, mid.2.2) := by
      obtain ⟨a, b, c⟩ := mid'
      simp only at same1 same2
      rw [same1, same2]
    rw [shape]; exact folded'

/-- **Materialization agrees**: a related state and the renamed value materialize the
same Data with the same remaining budget, whenever the original succeeds. -/
theorem related_materializeWith {f : Nat → Nat} {D : Nat → Prop} {policy : State → Bool}
    (respects : ∀ s t, Related f D s t → policy s = true → policy t = true) (limits limits' : Limits) :
    ∀ (depth : Nat) (budget : Budget) (value : RuntimeValue) (s t : State) (r : Result),
      Related f D s t → RoomFor limits limits' s t → AllIn D (valueAddresses value) →
      materializeWith policy limits depth budget value s = .ok r →
      ∃ r', materializeWith policy limits' depth budget (renameValue f value) t = .ok r' ∧
        ResultRel f D r r' := by
  intro depth
  induction depth with
  | zero => intro budget value s t r _ _ _ found; simp [materializeWith] at found
  | succ depth ih =>
    intro budget value s t r related room valueIn found
    cases value with
    | natural n =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨{ r with state := t }, ?_, rfl, rfl, ?_⟩
          · rw [← found]; simp [materializeWith, renameValue, c1, c2]
          · rw [← found]; exact related
    | boolean b =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨{ r with state := t }, ?_, rfl, rfl, ?_⟩
          · rw [← found]; simp [materializeWith, renameValue, c1, c2]
          · rw [← found]; exact related
    | label l =>
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          simp at found
          refine ⟨{ r with state := t }, ?_, rfl, rfl, ?_⟩
          · rw [← found]; simp [materializeWith, renameValue, c1, c2]
          · rw [← found]; exact related
    | closure body environment => simp [materializeWith] at found; split at found <;> simp at found
    | specification metadata extension => simp [materializeWith] at found; split at found <;> simp at found
    | prototype spec target => simp [materializeWith] at found; split at found <;> simp at found
    | variant label payload =>
      have payloadIn : D payload := valueIn payload (by simp [valueAddresses])
      simp [materializeWith] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · rename_i c1 c2
          have enteredRel : Related f D ⟨s.heap, .enter payload, []⟩ ⟨t.heap, .enter (f payload), []⟩ :=
            ⟨related.heap, allIn_cons payloadIn (allIn_nil D), rfl, by simp, rfl⟩
          cases forced : (forceWith policy limits budget.ticks ⟨s.heap, .enter payload, []⟩).1 with
          | finished value retained =>
            rw [forced] at found
            have ⟨rel, ticksEq⟩ := related_forceWith respects limits limits' budget.ticks _ _ enteredRel
              ⟨room.heap, room.stack⟩ (by rw [forced]; rfl)
            rw [forced] at rel
            cases forcedT : (forceWith policy limits' budget.ticks ⟨t.heap, .enter (f payload), []⟩).1 <;>
              rw [forcedT] at rel <;> simp only [OutcomeRel] at rel
            obtain ⟨valueEq, valueIn', retainedRel⟩ := rel
            simp at found
            obtain ⟨a, materialized, rfl⟩ := found
            obtain ⟨a', materialized', aValue, aRemaining, aRel⟩ :=
              ih _ _ _ _ _ retainedRel (room.shift related retainedRel) valueIn' materialized
            refine ⟨⟨.variant label a'.value, a'.state, a'.remaining⟩, ?_, by simp [aValue], aRemaining, aRel⟩
            rw [show renameValue f (.variant label payload) = .variant label (f payload) from rfl]
            simp [materializeWith, c1, c2, forcedT, ticksEq, valueEq, materialized']
          | _ => rw [forced] at found; simp at found
    | record fields =>
      have fieldsIn : AllIn D (fields.map Prod.snd) := valueIn
      simp [materializeWith_record] at found
      split at found
      · simp at found
      · split at found
        · simp at found
        · split at found
          · split at found
            · simp at found
            · rename_i c1 c2 c3 c4
              obtain ⟨out, folded, rfl⟩ := (except_map_ok _ _ _).mp found
              have key := foldlM_related (f := f) (D := D) (step := recordStep policy limits depth)
                (step' := recordStep policy limits' depth) ?_ fields [] s t _ out related fieldsIn folded
              · obtain ⟨out', folded', same1, same2, outRel⟩ := key
                refine ⟨⟨.record out'.1.reverse, out'.2.1, out'.2.2⟩, ?_, by simp [same1], by simp [same2], outRel⟩
                simp [materializeWith_record, renameValue, c1, c2, c3, c4, folded', Function.comp_def]
              · intro acc st st' b field out stRel inField stepped
                simp [recordStep] at stepped
                split at stepped
                · simp at stepped
                · rename_i cond
                  have enteredRel : Related f D ⟨st.heap, .enter field.2, []⟩ ⟨st'.heap, .enter (f field.2), []⟩ :=
                    ⟨stRel.heap, allIn_cons inField (allIn_nil D), rfl, by simp, rfl⟩
                  have stRoom : RoomFor limits limits' st st' := room.shift related stRel
                  cases forced : forceWith policy limits b.ticks ⟨st.heap, .enter field.2, []⟩ with
                  | mk outcome rest =>
                    rw [forced] at stepped
                    cases outcome with
                    | finished value retained =>
                      have ⟨rel, ticksEq⟩ := related_forceWith respects limits limits' b.ticks _ _ enteredRel
                        ⟨stRoom.heap, stRoom.stack⟩ (by rw [forced]; rfl)
                      rw [forced] at rel ticksEq
                      cases forcedT : forceWith policy limits' b.ticks ⟨st'.heap, .enter (f field.2), []⟩ with
                      | mk outcome' rest' =>
                        rw [forcedT] at rel ticksEq
                        simp only at rel ticksEq
                        subst ticksEq
                        cases outcome' <;> simp only [OutcomeRel] at rel
                        obtain ⟨valueEq, valueIn', retainedRel⟩ := rel
                        subst valueEq
                        simp at stepped
                        obtain ⟨a, materialized, rfl⟩ := stepped
                        obtain ⟨a', materialized', aValue, aRemaining, aRel⟩ :=
                          ih _ _ _ _ _ retainedRel (room.shift related retainedRel) valueIn' materialized
                        refine ⟨((field.1, a'.value) :: acc, a'.state, a'.remaining), ?_, by simp [aValue],
                          aRemaining, aRel⟩
                        simp [recordStep, cond, forcedT, materialized']
                    | _ => simp at stepped
          · simp at found


/-- **Completion agrees**: a finished related state completes to the same Data. -/
theorem related_completeWith {f : Nat → Nat} {D : Nat → Prop} {policy : State → Bool}
    (respects : ∀ s t, Related f D s t → policy s = true → policy t = true) (limits limits' : Limits)
    (budget : Budget) {s t : State} {r : Result} (related : Related f D s t) (room : RoomFor limits limits' s t)
    (found : completeWith policy limits budget s = .ok r) :
    ∃ r', completeWith policy limits' budget t = .ok r' ∧ ResultRel f D r r' := by
  cases allowed : policy s with
  | false => simp [completeWith, allowed] at found
  | true =>
    have allowedT := respects s t related allowed
    obtain ⟨hr, controlIn, controlEq, stackIn, stackEq⟩ := related
    obtain ⟨heap, control, stack⟩ := s
    obtain ⟨heap', control', stack'⟩ := t
    simp only at hr controlIn controlEq stackIn stackEq allowed allowedT
    subst controlEq stackEq
    have related : Related f D ⟨heap, control, stack⟩ ⟨heap', renameControl f control, stack.map (renameFrame f)⟩ :=
      ⟨hr, controlIn, rfl, stackIn, rfl⟩
    cases control with
    | complete value =>
      cases stack with
      | nil =>
        simp [completeWith, allowed] at found
        obtain ⟨a, materialized, rest⟩ := found
        obtain ⟨a', materialized', aValue, aRemaining, aRel⟩ :=
          related_materializeWith respects limits limits' _ _ _ _ _ _ related room controlIn materialized
        split at rest
        · rename_i bytes encodedAt
          split at rest
          · simp at rest
          · rename_i small
            simp at rest; subst rest
            refine ⟨a', ?_, aValue, aRemaining, aRel⟩
            simp only [renameControl, List.map_nil] at allowedT materialized'
            simp [completeWith, allowedT, renameControl, materialized', aValue, encodedAt, small]
        · simp at rest
      | cons frame rest => simp [completeWith, allowed] at found
    | _ => simp [completeWith, allowed] at found

/-- **Plan extraction agrees**: a yielded related state's Plan is the same Data. -/
theorem related_yieldedPlanWith {f : Nat → Nat} {D : Nat → Prop} {policy : State → Bool}
    (respects : ∀ s t, Related f D s t → policy s = true → policy t = true) (limits limits' : Limits)
    (budget : Budget) {s t : State} {r : Result} (related : Related f D s t) (room : RoomFor limits limits' s t)
    (found : yieldedPlanWith policy limits budget s = .ok r) :
    ∃ r', yieldedPlanWith policy limits' budget t = .ok r' ∧ ResultRel f D r r' := by
  obtain ⟨hr, controlIn, controlEq, stackIn, stackEq⟩ := related
  obtain ⟨heap, control, stack⟩ := s
  obtain ⟨heap', control', stack'⟩ := t
  simp only at hr controlIn controlEq stackIn stackEq
  subst controlEq stackEq
  cases control with
  | yielded plan =>
    have planIn : D plan := controlIn plan (List.mem_singleton_self plan)
    have enteredRel : Related f D ⟨heap, .enter plan, []⟩ ⟨heap', .enter (f plan), []⟩ :=
      ⟨hr, controlIn, rfl, by simp, rfl⟩
    simp only [yieldedPlanWith, renameControl] at found ⊢
    have enteredRoom : RoomFor limits limits' ⟨heap, .enter plan, []⟩ ⟨heap', .enter (f plan), []⟩ :=
      ⟨room.heap, room.stack⟩
    have ⟨rel, ticksEq⟩ := related_forceWith respects limits limits' budget.ticks _ _ enteredRel enteredRoom (by
      cases forced : forceWith policy limits budget.ticks ⟨heap, .enter plan, []⟩ with
      | mk outcome ticks =>
        rw [forced] at found
        cases outcome <;> simp at found
        rfl)
    cases forced : forceWith policy limits budget.ticks ⟨heap, .enter plan, []⟩ with
    | mk outcome ticks =>
      rw [forced] at found rel ticksEq
      cases outcome with
      | finished value retained =>
        cases forcedT : forceWith policy limits' budget.ticks ⟨heap', .enter (f plan), []⟩ with
        | mk outcome' ticks' =>
          rw [forcedT] at rel ticksEq
          simp only at rel ticksEq
          subst ticksEq
          cases outcome' <;> simp only [OutcomeRel] at rel
          obtain ⟨valueEq, valueIn, retainedRel⟩ := rel
          subst valueEq
          simp at found
          obtain ⟨a, materialized, rfl⟩ := found
          obtain ⟨a', materialized', aValue, aRemaining, aRel⟩ :=
            related_materializeWith respects limits limits' _ _ _ _ _ _ retainedRel
              (enteredRoom.shift enteredRel retainedRel) valueIn materialized
          refine ⟨{a' with state := {a'.state with control := .yielded (f plan), stack := stack.map (renameFrame f)}},
            ?_, aValue, aRemaining, aRel.heap, controlIn, rfl, stackIn, rfl⟩
          simp [materialized']
      | _ => simp at found
  | _ => simp [yieldedPlanWith] at found


/-! ## The kernel's segment -/

/-- **One activity segment agrees** (the shape of `Kernel.ObjectiveActivity.runSegment`):
if the original yields and its Plan extracts, the related state yields at the renamed
Plan address with a related state whose Plan is the same Data; a finished original
completes to the same result Data; a divergent or refused original diverges or is
refused for the same reason. -/
theorem related_segment {f : Nat → Nat} {D : Nat → Prop} {s t : State} (related : Related f D s t)
    (limits limits' : Limits) (room : RoomFor limits limits' s t) (ticks : Nat) (budget : Budget) :
    (∀ plan y r, runBounded limits ticks s = .yielded plan y → yieldedPlan limits budget y = .ok r →
      ∃ y' r', runBounded limits' ticks t = .yielded (f plan) y' ∧ Related f D y y' ∧
        yieldedPlan limits' budget y' = .ok r' ∧ r'.value = r.value) ∧
    (∀ value y r, runBounded limits ticks s = .finished value y → complete limits budget y = .ok r →
      ∃ y' r', runBounded limits' ticks t = .finished (renameValue f value) y' ∧
        complete limits' budget y' = .ok r' ∧ r'.value = r.value) ∧
    (∀ address y, runBounded limits ticks s = .divergent address y →
      ∃ y', runBounded limits' ticks t = .divergent (f address) y') ∧
    (∀ reason y, runBounded limits ticks s = .refused reason y →
      ∃ y', runBounded limits' ticks t = .refused reason y') := by
  have always : ∀ s t, Related f D s t → (fun _ => true : State → Bool) s = true →
      (fun _ => true : State → Bool) t = true := fun _ _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro plan y r ran extracted
    have rel := related_runBounded limits limits' ticks s t related room (by rw [ran]; rfl)
    rw [ran] at rel
    cases ranT : runBounded limits' ticks t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
    obtain ⟨planEq, yRel⟩ := rel
    obtain ⟨r', extracted', value, _, _⟩ :=
      related_yieldedPlanWith always limits limits' budget yRel (room.shift related yRel) extracted
    exact ⟨_, r', by rw [planEq], yRel, extracted', value⟩
  · intro value y r ran completed
    have rel := related_runBounded limits limits' ticks s t related room (by rw [ran]; rfl)
    rw [ran] at rel
    cases ranT : runBounded limits' ticks t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
    obtain ⟨valueEq, _, yRel⟩ := rel
    obtain ⟨r', completed', same, _, _⟩ :=
      related_completeWith always limits limits' budget yRel (room.shift related yRel) completed
    exact ⟨_, r', by rw [valueEq], completed', same⟩
  · intro address y ran
    have rel := related_runBounded limits limits' ticks s t related room (by rw [ran]; rfl)
    rw [ran] at rel
    cases ranT : runBounded limits' ticks t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
    exact ⟨_, by rw [rel.1]⟩
  · intro reason y ran
    have rel := related_runBounded limits limits' ticks s t related room (by rw [ran]; rfl)
    rw [ran] at rel
    cases ranT : runBounded limits' ticks t <;> rw [ranT] at rel <;> simp only [OutcomeRel] at rel
    exact ⟨_, by rw [rel.1]⟩

/-! ## Composition: collecting at every yield -/

theorem renameValue_comp (f g : Nat → Nat) (value : RuntimeValue) :
    renameValue g (renameValue f value) = renameValue (g ∘ f) value := by
  cases value <;> simp [renameValue, Function.comp_def]

theorem renameCell_comp (f g : Nat → Nat) (cell : Cell) :
    renameCell g (renameCell f cell) = renameCell (g ∘ f) cell := by
  cases cell <;> simp [renameCell, renameClosure, renameValue_comp, Function.comp_def]

theorem renameFrame_comp (f g : Nat → Nat) (frame : Frame) :
    renameFrame g (renameFrame f frame) = renameFrame (g ∘ f) frame := by
  cases frame <;> simp [renameFrame, renameValue_comp, Function.comp_def]

theorem renameControl_comp (f g : Nat → Nat) (control : Control) :
    renameControl g (renameControl f control) = renameControl (g ∘ f) control := by
  cases control <;> simp [renameControl, renameValue_comp, Function.comp_def]

theorem valueAddresses_rename (f : Nat → Nat) (value : RuntimeValue) :
    valueAddresses (renameValue f value) = (valueAddresses value).map f := by
  cases value <;> simp [renameValue, valueAddresses, Function.comp_def]

theorem cellAddresses_rename (f : Nat → Nat) (cell : Cell) :
    cellAddresses (renameCell f cell) = (cellAddresses cell).map f := by
  cases cell <;> simp [renameCell, renameClosure, cellAddresses, valueAddresses_rename]

theorem frameAddresses_rename (f : Nat → Nat) (frame : Frame) :
    frameAddresses (renameFrame f frame) = (frameAddresses frame).map f := by
  cases frame <;> simp [renameFrame, frameAddresses, valueAddresses_rename]

theorem controlAddresses_rename (f : Nat → Nat) (control : Control) :
    controlAddresses (renameControl f control) = (controlAddresses control).map f := by
  cases control <;> simp [renameControl, controlAddresses, valueAddresses_rename]

/-- **Relations compose**, so a history that collects at every yield stays related to
the history that never collects. -/
theorem Related.trans {f g : Nat → Nat} {D E : Nat → Prop} {s t u : State}
    (one : Related f D s t) (two : Related g E t u) :
    Related (g ∘ f) (fun a => D a ∧ E (f a)) s u := by
  have sizeOne := one.heap.size_le
  have sizeTwo := two.heap.size_le
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro a past
    have ⟨inD, shift⟩ := one.heap.beyond a past
    have ⟨inE, shift2⟩ := two.heap.beyond (f a) (by omega)
    exact ⟨⟨inD, inE⟩, by simp only [Function.comp_apply]; omega⟩
  · intro a b inA inB same
    exact one.heap.inj a b inA.1 inB.1 (two.heap.inj _ _ inA.2 inB.2 same)
  · intro a inA bound
    obtain ⟨c, found, foundT, inC⟩ := one.heap.cells a inA.1 bound
    obtain ⟨c2, foundT2, foundU, inC2⟩ := two.heap.cells (f a) inA.2 (bound_of_some foundT)
    rw [foundT] at foundT2; cases foundT2
    refine ⟨c, found, by rw [Function.comp_apply, foundU, renameCell_comp], ?_⟩
    intro x member
    refine ⟨inC x member, ?_⟩
    rw [cellAddresses_rename] at inC2
    exact inC2 (f x) (List.mem_map_of_mem member)
  · intro x member
    refine ⟨one.controlIn x member, ?_⟩
    have := two.controlIn
    rw [one.control, controlAddresses_rename] at this
    exact this (f x) (List.mem_map_of_mem member)
  · rw [two.control, one.control, renameControl_comp]
  · intro frame member x inFrame
    refine ⟨one.stackIn frame member x inFrame, ?_⟩
    have := two.stackIn (renameFrame f frame) (by rw [one.stack]; exact List.mem_map_of_mem member)
    rw [frameAddresses_rename] at this
    exact this (f x) (List.mem_map_of_mem inFrame)
  · rw [two.stack, one.stack, List.map_map]
    congr 1
    funext frame
    exact renameFrame_comp f g frame


/-! ## Typing transfers to a related state -/

section Typing
open Minidregg.Theory.ObjectiveBendTypes Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandTyping Minidregg.Theory.ObjectiveBendDemandInvariant

variable {f : Nat → Nat} {D : Nat → Prop} {assumptions : Assumptions} {types types' : AddressTypes}

/-- `types'` assigns each renamed address the type `types` assigns the original. -/
def TypesRel (f : Nat → Nat) (D : Nat → Prop) (types types' : AddressTypes) : Prop :=
  ∀ a, D a → types'[f a]? = types[a]?

theorem environmentTyping_rename (rel : TypesRel f D types types') {context : Context}
    {environment : List Nat} (inside : AllIn D environment)
    (typed : EnvironmentTyping types context environment) :
    EnvironmentTyping types' context (environment.map f) := by
  refine ⟨by simp [typed.length], ?_⟩
  intro index declared lookup
  obtain ⟨address, member, assigned⟩ := typed.binding index declared lookup
  refine ⟨f address, by simp [member], ?_⟩
  rw [rel address (inside address (List.mem_of_getElem? member)), assigned]

def closureTyping_rename (rel : TypesRel f D types types') {closure : Closure} {type : Ty}
    (inside : AllIn D closure.environment) (typed : ClosureTyping assumptions types closure type) :
    ClosureTyping assumptions types' (renameClosure f closure) type where
  context := typed.context
  uses := typed.uses
  environment := environmentTyping_rename rel inside typed.environment
  source := typed.source
  safe := typed.safe
  contextValid := typed.contextValid

theorem valueTyping_rename (rel : TypesRel f D types types') {value : RuntimeValue} {type : Ty}
    (typed : ValueTyping assumptions types value type) :
    AllIn D (valueAddresses value) → ValueTyping assumptions types' (renameValue f value) type := by
  induction typed with
  | natural value => intro _; exact .natural value
  | boolean value => intro _; exact .boolean value
  | label value => intro _; exact .label value
  | closure environmentTyped body safe valid reusable =>
    intro inside
    exact .closure (environmentTyping_rename rel inside environmentTyped) body safe valid reusable
  | @record fields row isRow lookup =>
    intro inside
    refine .record isRow ?_
    intro fuel name member found
    obtain ⟨address, actual, findEq, assigned, path⟩ := lookup fuel name member found
    refine ⟨f address, actual, ?_, ?_, path⟩
    · simp only [List.find?_map, Function.comp_def, findEq]; rfl
    · have member := List.mem_of_find?_eq_some findEq
      rw [rel address (inside address (List.mem_map_of_mem (f := Prod.snd) member)), assigned]
  | @specification metadata extension _ _ one two =>
    intro inside
    refine .specification ?_ ?_
    · rw [rel metadata (inside metadata (by simp [valueAddresses])), one]
    · rw [rel extension (inside extension (by simp [valueAddresses])), two]
  | @prototype spec target _ _ one two =>
    intro inside
    refine .prototype ?_ ?_
    · rw [rel spec (inside spec (by simp [valueAddresses])), one]
    · rw [rel target (inside target (by simp [valueAddresses])), two]
  | conversion _ same ih => intro inside; exact .conversion (ih inside) same
  | @variant tag address _ _ _ _ lookup assigned path =>
    intro inside
    exact .variant lookup (by rw [rel address (inside address (by simp [valueAddresses])), assigned]) path

theorem cellTyping_rename (rel : TypesRel f D types types') {cell : Cell} {type : Ty}
    (inside : AllIn D (cellAddresses cell)) (typed : CellTyping assumptions types cell type) :
    CellTyping assumptions types' (renameCell f cell) type := by
  cases typed with
  | suspended closureTyped plain => exact .suspended (closureTyping_rename rel inside closureTyped) plain
  | evaluating closureTyped plain => exact .evaluating (closureTyping_rename rel inside closureTyped) plain
  | cached closureTyped valueTyped plain =>
    exact .cached (closureTyping_rename rel (fun x member => inside x (List.mem_append_left _ member)) closureTyped)
      (valueTyping_rename rel valueTyped (fun x member => inside x (List.mem_append_right _ member))) plain

theorem frameTyping_rename (rel : TypesRel f D types types') {frame : Frame} {input output : Ty}
    (inside : AllIn D (frameAddresses frame)) (typed : FrameTyping assumptions types frame input output) :
    FrameTyping assumptions types' (renameFrame f frame) input output := by
  cases typed with
  | argument argumentTyped callableEq allowed =>
    exact .argument (closureTyping_rename rel inside argumentTyped) callableEq allowed
  | @update address _ assigned plain =>
    exact .update (by rw [rel address (inside address (by simp [frameAddresses])), assigned]) plain
  | field lookup => exact .field lookup
  | reflect => exact .reflect _ _
  | metadata => exact .metadata _ _
  | project => exact .project _ _
  | extend environmentTyped fieldsTyped safe valid isRow =>
    exact .extend (environmentTyping_rename rel inside environmentTyped) fieldsTyped safe valid isRow
  | condition zeroTyped environmentTyped successor safe valid =>
    exact .condition (closureTyping_rename rel inside zeroTyped)
      (environmentTyping_rename rel inside environmentTyped) successor safe valid
  | binaryLeft rightTyped => exact .binaryLeft (closureTyping_rename rel inside rightTyped)
  | binaryRight leftTyped => exact .binaryRight (valueTyping_rename rel leftTyped inside)
  | case environmentTyped armsTyped valid =>
    exact .case (environmentTyping_rename rel inside environmentTyped) armsTyped valid
  | ifBool trueTyped falseTyped =>
    exact .ifBool (closureTyping_rename rel inside trueTyped) (closureTyping_rename rel inside falseTyped)
  | effectCase environmentTyped armsTyped valid plain =>
    exact .effectCase (environmentTyping_rename rel inside environmentTyped) armsTyped valid plain

theorem stackTyping_rename (rel : TypesRel f D types types') {stack : List Frame} {input output : Ty}
    (typed : StackTyping assumptions types stack input output) :
    (∀ frame ∈ stack, AllIn D (frameAddresses frame)) →
      StackTyping assumptions types' (stack.map (renameFrame f)) input output := by
  induction typed with
  | nil type => intro _; exact .nil type
  | cons frameTyped _ ih =>
    intro inside
    have ⟨head, tail⟩ := List.forall_mem_cons.mp inside
    exact .cons (frameTyping_rename rel head frameTyped) (ih tail)
  | conversion same _ ih => intro inside; exact .conversion same (ih inside)
  | returns plain _ ih => intro inside; exact .returns plain (ih inside)

theorem controlTyping_rename (rel : TypesRel f D types types') {control : Control} {type : Ty}
    (inside : AllIn D (controlAddresses control)) (typed : ControlTyping assumptions types control type) :
    ControlTyping assumptions types' (renameControl f control) type := by
  cases typed with
  | evaluate closureTyped => exact .evaluate (closureTyping_rename rel inside closureTyped)
  | @enter address _ assigned =>
    exact .enter (by rw [rel address (inside address (List.mem_singleton_self _)), assigned])
  | returned valueTyped => exact .returned (valueTyping_rename rel valueTyped inside)
  | complete valueTyped => exact .complete (valueTyping_rename rel valueTyped inside)
  | @blackhole address _ assigned =>
    exact .blackhole (by rw [rel address (inside address (List.mem_singleton_self _)), assigned])
  | @yielded plan _ _ assigned isPlan isData =>
    exact .yielded (by rw [rel plan (inside plan (List.mem_singleton_self _)), assigned]) isPlan isData

/-- Every cell of the second heap is the image of a cell of the first. -/
def Covers (f : Nat → Nat) (D : Nat → Prop) (heap heap' : Array Cell) : Prop :=
  ∀ k, k < heap'.size → ∃ a, D a ∧ a < heap.size ∧ f a = k

theorem heapTyping_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap')
    (rel : TypesRel f D types types') (length : types'.length = heap'.size) (cover : Covers f D heap heap')
    (typed : HeapTyping assumptions types heap) : HeapTyping assumptions types' heap' := by
  refine ⟨length, ?_⟩
  intro k type found
  have bound : k < heap'.size := by rw [← length]; exact (List.getElem?_eq_some_iff.mp found).1
  obtain ⟨a, inA, boundA, rfl⟩ := cover k bound
  rw [rel a inA] at found
  obtain ⟨stored, at_, cellTyped⟩ := typed.cell a type found
  obtain ⟨c, foundC, foundC', inC⟩ := hr.cells a inA boundA
  rw [at_] at foundC; cases foundC
  exact ⟨_, foundC', cellTyping_rename rel inC cellTyped⟩

/-! ### The representation invariants -/

theorem image_lt {heap heap' : Array Cell} (hr : HeapRel f D heap heap') {a : Nat} (inA : D a)
    (bound : a < heap.size) : f a < heap'.size := by
  obtain ⟨_, _, found', _⟩ := hr.cells a inA bound
  exact bound_of_some found'

theorem environmentValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap')
    {environment : List Nat} (inside : AllIn D environment) (valid : EnvironmentValid heap.size environment) :
    EnvironmentValid heap'.size (environment.map f) := by
  intro x member
  obtain ⟨a, memberA, rfl⟩ := List.mem_map.mp member
  exact image_lt hr (inside a memberA) (valid a memberA)

theorem runtimeValueValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap')
    {value : RuntimeValue} (inside : AllIn D (valueAddresses value)) (valid : RuntimeValueValid heap.size value) :
    RuntimeValueValid heap'.size (renameValue f value) := by
  cases value with
  | closure body environment =>
    exact ⟨by simpa [renameValue] using valid.1, environmentValid_rename hr inside valid.2⟩
  | natural _ | boolean _ | label _ => trivial
  | record fields =>
    intro field member
    simp only [List.mem_map] at member
    obtain ⟨original, memberO, rfl⟩ := member
    exact image_lt hr (inside _ (List.mem_map_of_mem memberO)) (valid original memberO)
  | specification metadata extension =>
    exact ⟨image_lt hr (inside metadata (by simp [valueAddresses])) valid.1,
      image_lt hr (inside extension (by simp [valueAddresses])) valid.2⟩
  | prototype spec target =>
    exact ⟨image_lt hr (inside spec (by simp [valueAddresses])) valid.1,
      image_lt hr (inside target (by simp [valueAddresses])) valid.2⟩
  | variant _ payload => exact image_lt hr (inside payload (by simp [valueAddresses])) valid

theorem closureValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap') {closure : Closure}
    (inside : AllIn D closure.environment) (valid : ClosureValid heap.size closure) :
    ClosureValid heap'.size (renameClosure f closure) :=
  ⟨by simpa [renameClosure] using valid.1, environmentValid_rename hr inside valid.2⟩

theorem cellValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap') {cell : Cell}
    (inside : AllIn D (cellAddresses cell)) (valid : CellValid heap.size cell) :
    CellValid heap'.size (renameCell f cell) := by
  cases cell with
  | suspended origin => exact closureValid_rename hr inside valid
  | evaluating origin => exact closureValid_rename hr inside valid
  | cached origin value =>
    exact ⟨closureValid_rename hr (fun x member => inside x (List.mem_append_left _ member)) valid.1,
      runtimeValueValid_rename hr (fun x member => inside x (List.mem_append_right _ member)) valid.2⟩

theorem frameValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap') {frame : Frame}
    (inside : AllIn D (frameAddresses frame)) (valid : FrameValid heap.size frame) :
    FrameValid heap'.size (renameFrame f frame) := by
  cases frame with
  | argument term environment => exact closureValid_rename hr inside valid
  | binaryLeft primitive term environment => exact closureValid_rename hr inside valid
  | update address => exact image_lt hr (inside address (List.mem_singleton_self _)) valid
  | field _ | reflect | metadata | project => trivial
  | extend fields environment =>
    exact ⟨environmentValid_rename hr inside valid.1, by simpa [renameFrame] using valid.2⟩
  | condition zero successorBody environment =>
    exact ⟨environmentValid_rename hr inside valid.1, by simpa [renameFrame] using valid.2⟩
  | binaryRight primitive value => exact runtimeValueValid_rename hr inside valid
  | case arms environment =>
    exact ⟨environmentValid_rename hr inside valid.1, by simpa [renameFrame] using valid.2⟩
  | ifBool whenTrue whenFalse environment =>
    exact ⟨environmentValid_rename hr inside valid.1, by simpa [renameFrame] using valid.2⟩

theorem controlValid_rename {heap heap' : Array Cell} (hr : HeapRel f D heap heap') {control : Control}
    (inside : AllIn D (controlAddresses control)) (valid : ControlValid heap.size control) :
    ControlValid heap'.size (renameControl f control) := by
  cases control with
  | evaluate term environment => exact closureValid_rename (closure := ⟨term, environment⟩) hr inside valid
  | enter address => exact image_lt hr (inside address (List.mem_singleton_self _)) valid
  | blackhole address => exact image_lt hr (inside address (List.mem_singleton_self _)) valid
  | returned value => exact runtimeValueValid_rename hr inside valid
  | complete value => exact runtimeValueValid_rename hr inside valid
  | refused _ => trivial
  | yielded plan => exact image_lt hr (inside plan (List.mem_singleton_self _)) valid

theorem lexical_related {s t : State} (related : Related f D s t) (cover : Covers f D s.heap t.heap)
    (lexical : LexicalInvariant s) : LexicalInvariant t := by
  obtain ⟨cells, control, frames⟩ := lexical
  refine ⟨?_, ?_, ?_⟩
  · intro k cell found
    obtain ⟨a, inA, boundA, rfl⟩ := cover k (bound_of_some found)
    obtain ⟨c, foundC, foundC', inC⟩ := related.heap.cells a inA boundA
    rw [found] at foundC'; cases foundC'
    exact cellValid_rename related.heap inC (cells a c foundC)
  · rw [related.control]; exact controlValid_rename related.heap related.controlIn control
  · intro frame member
    rw [related.stack] at member
    obtain ⟨original, memberO, rfl⟩ := List.mem_map.mp member
    exact frameValid_rename related.heap (related.stackIn original memberO) (frames original memberO)

theorem stackUpdates_rename (stack : List Frame) :
    stackUpdates (stack.map (renameFrame f)) = (stackUpdates stack).map f := by
  induction stack with
  | nil => rfl
  | cons frame rest ih => cases frame <;> simp [stackUpdates, renameFrame, ih]

theorem stackUpdates_in {stack : List Frame} (inside : ∀ frame ∈ stack, AllIn D (frameAddresses frame)) :
    AllIn D (stackUpdates stack) := by
  induction stack with
  | nil => exact allIn_nil D
  | cons frame rest ih =>
    have ⟨head, tail⟩ := List.forall_mem_cons.mp inside
    cases frame <;> simp only [stackUpdates] <;> first
      | exact ih tail
      | exact allIn_cons (head _ (List.mem_singleton_self _)) (ih tail)

theorem nodup_map_on {l : List Nat} (inside : AllIn D l) (inj : ∀ a b, D a → D b → f a = f b → a = b)
    (nodup : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons head rest ih =>
    rw [List.nodup_cons] at nodup
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (fun x member => inside x (List.mem_cons_of_mem _ member)) nodup.2⟩
    intro member
    obtain ⟨other, memberO, same⟩ := List.mem_map.mp member
    have := inj other head (inside other (List.mem_cons_of_mem _ memberO)) (inside head (List.mem_cons_self ..)) same
    exact nodup.1 (this ▸ memberO)

theorem busy_related {s t : State} (related : Related f D s t) (cover : Covers f D s.heap t.heap)
    (busy : BusyInvariant s) : BusyInvariant t := by
  obtain ⟨nodup, marks⟩ := busy
  have updatesIn := stackUpdates_in related.stackIn
  unfold BusyInvariant Busy
  rw [related.stack, stackUpdates_rename]
  refine ⟨nodup_map_on updatesIn related.heap.inj nodup, ?_⟩
  intro k
  constructor
  · intro member
    obtain ⟨a, memberA, rfl⟩ := List.mem_map.mp member
    obtain ⟨origin, found⟩ := (marks a).mp memberA
    exact ⟨_, by rw [related.heap.lookup (updatesIn a memberA), found]; rfl⟩
  · rintro ⟨origin, found⟩
    obtain ⟨a, inA, boundA, rfl⟩ := cover k (bound_of_some found)
    rw [related.heap.lookup inA] at found
    cases foundA : s.heap[a]? with
    | none => rw [foundA] at found; cases found
    | some cell =>
      rw [foundA] at found
      cases cell with
      | evaluating o => exact List.mem_map_of_mem ((marks a).mpr ⟨o, foundA⟩)
      | suspended o => cases found
      | cached o v => cases found

theorem finalStack_related {s t : State} (related : Related f D s t) (final : FinalStackInvariant s) :
    FinalStackInvariant t := by
  intro value complete
  rw [related.stack]
  rw [related.control] at complete
  cases control : s.control <;> rw [control] at complete <;> simp [renameControl] at complete
  rw [final _ control]; rfl

/-- **Typing transfers along a covering renaming.** -/
def typed_related {s t : State} {result : Ty} (related : Related f D s t) (cover : Covers f D s.heap t.heap)
    (rel : TypesRel f D types types') (length : types'.length = t.heap.size)
    (typed : StateTyping assumptions types s result) : StateTyping assumptions types' t result where
  current := typed.current
  heap := heapTyping_rename related.heap rel length cover typed.heap
  control := by rw [related.control]; exact controlTyping_rename rel related.controlIn typed.control
  stack := by rw [related.stack]; exact stackTyping_rename rel typed.stack related.stackIn
  assumptionsValid := typed.assumptionsValid
  lexical := lexical_related related cover typed.lexical
  busy := busy_related related cover typed.busy
  terminalStack := finalStack_related related typed.terminalStack

end Typing


/-! ## Collection: covering, typing, and the T5 statements -/

theorem count_take_surj : ∀ (M : List Bool) (k : Nat), k < M.count true →
    ∃ i, M[i]? = some true ∧ (M.take i).count true = k
  | [], k, bound => by simp at bound
  | m :: M, k, bound => by
    cases m with
    | true =>
      cases k with
      | zero => exact ⟨0, rfl, by simp⟩
      | succ k =>
        obtain ⟨i, marked, rank⟩ := count_take_surj M k (by simp at bound; omega)
        exact ⟨i + 1, by simpa using marked, by simp [rank]⟩
    | false =>
      obtain ⟨i, marked, rank⟩ := count_take_surj M k (by simpa [List.count_cons] using bound)
      exact ⟨i + 1, by simpa using marked, by simp [rank]⟩

/-- Every collected cell is the image of a live cell. -/
theorem collect_covers (state : State) :
    Covers (collectRenaming state) (liveDomain state) state.heap (collect state).heap := by
  intro k bound
  rw [collect_heap_size, ← Array.count_toList] at bound
  obtain ⟨i, marked, rank⟩ := count_take_surj _ k bound
  have markedA : (liveMarks state)[i]? = some true := by simpa using marked
  refine ⟨i, .inr markedA, ?_, ?_⟩
  · rw [← (liveMarks_spec state).1]; exact bound_of_some markedA
  · rw [collectRenaming_live markedA, rank]

section CollectTyping
open Minidregg.Theory.ObjectiveBendTypes Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandTyping Minidregg.Theory.ObjectiveBendDemandInvariant

/-- The address types of the collected heap: the live cells' types, in order. -/
def collectTypes (state : State) (types : AddressTypes) : AddressTypes :=
  (types.zip (liveMarks state).toList).filterMap fun entry => if entry.2 then some entry.1 else none

theorem collectTypes_length {state : State} {types : AddressTypes} (length : types.length = state.heap.size) :
    (collectTypes state types).length = (collect state).heap.size := by
  rw [collect_heap_size, ← Array.count_toList]
  exact filterMap_zip_length (fun x => x) _ _ (by simp [length, (liveMarks_spec state).1])

theorem collectTypes_rel {state : State} {types : AddressTypes} (length : types.length = state.heap.size) :
    TypesRel (collectRenaming state) (liveDomain state) types (collectTypes state types) := by
  intro a inA
  rcases inA with past | marked
  · rw [List.getElem?_eq_none (by omega : types.length ≤ a)]
    apply List.getElem?_eq_none
    have := collectRenaming_beyond past
    rw [collectTypes_length length, collect_heap_size]; omega
  · have bound : a < types.length := by
      rw [length, ← (liveMarks_spec state).1]; exact bound_of_some marked
    rw [List.getElem?_eq_getElem bound, collectRenaming_live marked]
    exact filterMap_zip_getElem (fun x => x) _ _ _ _ (List.getElem?_eq_getElem bound) (by simpa using marked)

/-- **Typing transfers to the collected state** (heap typing, control and stack
typing, and the lexical, busy and final-stack invariants), at the live cells' types. -/
def typed_collect {assumptions : Assumptions} {types : AddressTypes} {state : State} {result : Ty}
    (typed : StateTyping assumptions types state result) :
    StateTyping assumptions (collectTypes state types) (collect state) result :=
  typed_related (related_collect state) (collect_covers state) (collectTypes_rel typed.heap.length)
    (collectTypes_length typed.heap.length) typed

theorem typed_collect_exists {assumptions : Assumptions} {types : AddressTypes} {state : State} {result : Ty}
    (typed : StateTyping assumptions types state result) :
    ∃ types', Nonempty (StateTyping assumptions types' (collect state) result) :=
  ⟨_, ⟨typed_collect typed⟩⟩

/-! ### Inhabitants -/

/-- A typed state with garbage: a cached natural no root reaches. -/
def garbageTyped : State := ⟨#[.cached ⟨.nat 0, []⟩ (.natural 0)], .evaluate (.nat 5) [], []⟩

def garbageTyping : StateTyping {} [.natural] garbageTyped .natural where
  current := .natural
  heap := ⟨rfl, by
    intro address type found
    cases address with
    | zero =>
      simp at found; subst found
      exact ⟨_, rfl, .cached ⟨[], [], EnvironmentTyping.empty _, .natural [] 0, rfl, rfl⟩ (.natural 0) rfl⟩
    | succ n => simp at found⟩
  control := .evaluate ⟨[], [], EnvironmentTyping.empty _, .natural [] 5, rfl, rfl⟩
  stack := .nil _
  assumptionsValid := rfl
  lexical := ⟨by
      intro address cell found
      cases address with
      | zero => simp [garbageTyped] at found; subst found; exact ⟨⟨.natural 0, fun _ h => by cases h⟩, trivial⟩
      | succ n => simp [garbageTyped] at found,
    ⟨.natural 5, fun _ h => by cases h⟩, fun _ h => by cases h⟩
  busy := by
    refine ⟨List.nodup_nil, fun address => ?_⟩
    simp only [garbageTyped, stackUpdates, List.not_mem_nil, false_iff]
    rintro ⟨origin, found⟩
    cases address with
    | zero => simp at found
    | succ n => simp at found
  terminalStack := fun _ complete => by cases complete

/-- The collected typed state drops the garbage cell and keeps its typing. -/
theorem garbageTyped_collected : garbageTyped.heap.size = 1 ∧ (collect garbageTyped).heap.size = 0 := by
  decide +kernel

theorem garbageTyped_collect_typed :
    Nonempty (StateTyping {} (collectTypes garbageTyped [.natural]) (collect garbageTyped) .natural) :=
  ⟨typed_collect garbageTyping⟩

end CollectTyping

/-! ### A run that yields with garbage, and its collected Plan

`ifZero ((λx. x) 0) (perform 5) 9`: the argument thunk is forced and cached, the
condition takes the zero branch, and the program yields Plan `5`. The forced argument
is garbage at the yield. -/

def yieldingTerm : Term := .ifZero (.app (.lam (.bound 0)) (.nat 0)) (.perform (.nat 5)) (.nat 9)
def exampleLimits : Limits := ⟨16, 16⟩
def exampleBudget : Budget := ⟨8, 64, 64⟩

def exampleYield : State :=
  match runBounded exampleLimits 32 (initial yieldingTerm) with
  | .yielded _ yielded => yielded
  | _ => initial yieldingTerm

theorem yieldingTerm_yields : runBounded exampleLimits 32 (initial yieldingTerm) = .yielded 1 exampleYield := by
  rfl

/-- The yield leaves one garbage cell of two; collection drops it. -/
theorem exampleYield_collected : exampleYield.heap.size = 2 ∧ (collect exampleYield).heap.size = 1 := by
  decide +kernel

/-- Both Plans extract, to the same encoded Data. -/
theorem exampleYield_plan_agrees :
    ((yieldedPlan exampleLimits exampleBudget exampleYield).toOption.map fun r => encoded 4 r.value) =
      some (some [0, 53, 0]) ∧
    ((yieldedPlan exampleLimits exampleBudget (collect exampleYield)).toOption.map fun r => encoded 4 r.value) =
      some (some [0, 53, 0]) := by
  decide +kernel

theorem exampleYield_plan_extracts : ∃ r, yieldedPlan exampleLimits exampleBudget exampleYield = .ok r := by
  have agrees := exampleYield_plan_agrees.1
  cases extracted : yieldedPlan exampleLimits exampleBudget exampleYield with
  | ok r => exact ⟨r, rfl⟩
  | error e => rw [extracted] at agrees; simp [Except.toOption] at agrees

/-- The segment premises are inhabited: the original yields and its Plan extracts. -/
theorem exampleYield_segment_premises :
    ∃ plan y r, runBounded exampleLimits 32 (initial yieldingTerm) = .yielded plan y ∧
      yieldedPlan exampleLimits exampleBudget y = .ok r := by
  obtain ⟨r, extracted⟩ := exampleYield_plan_extracts
  exact ⟨1, exampleYield, r, yieldingTerm_yields, extracted⟩


/-! ## The T5 statements for `collect` -/

/-- Collection never grows the heap. -/
theorem collect_heap_le (state : State) : (collect state).heap.size ≤ state.heap.size :=
  (related_collect state).heap.size_le

/-- A yielded state stays yielded, at its Plan cell's new address. -/
theorem collect_yielded {state : State} {plan : Nat} (yielded : state.control = .yielded plan) :
    (collect state).control = .yielded (collectRenaming state plan) := by
  rw [(related_collect state).control, yielded]; rfl

/-- **Resuming the collected state runs as resuming the original**: with any response,
for any tick budget, the outcomes agree (same constructor and reason, renamed payload,
related retained state) unless the original ran out of heap. -/
theorem collect_resume_runBounded {state resumed : State} {response : Term}
    (yielded : resume response state = some resumed) (limits : Limits) (ticks : Nat)
    (notCapacity : ranOutOfHeap (runBounded limits ticks resumed) = false) :
    ∃ resumed', resume response (collect state) = some resumed' ∧
      OutcomeRel (collectRenaming state) (liveDomain state)
        (runBounded limits ticks resumed) (runBounded limits ticks resumed') := by
  obtain ⟨resumed', again, related⟩ := related_resume (related_collect state) response yielded
  exact ⟨resumed', again, related_runBounded limits limits ticks _ _ related (RoomFor.same _ _ _) notCapacity⟩

/-- **Exactly**, capacity included, once the collected run is charged the heap it freed. -/
theorem collect_resume_runBounded_exact {state resumed : State} {response : Term}
    (yielded : resume response state = some resumed) (limits : Limits) (ticks : Nat)
    (fits : state.heap.size ≤ limits.heap) :
    ∃ resumed', resume response (collect state) = some resumed' ∧
      OutcomeRel (collectRenaming state) (liveDomain state) (runBounded limits ticks resumed)
        (runBounded ⟨limits.heap - (state.heap.size - (collect state).heap.size), limits.stack⟩ ticks resumed') := by
  obtain ⟨resumed', again, related⟩ := related_resume (related_collect state) response yielded
  have sameHeap : resumed.heap = state.heap := (resume_keeps_heap_and_stack _ _ _ yielded).1
  have sameHeap' : resumed'.heap = (collect state).heap := (resume_keeps_heap_and_stack _ _ _ again).1
  have := related_runBounded_exact limits ticks _ _ related (by rw [sameHeap]; exact fits)
  rw [sameHeap, sameHeap'] at this
  exact ⟨resumed', again, this⟩

/-- **The kernel's segment from a collected checkpoint** agrees with the segment from the
uncollected one: Plan Data, result Data, divergence and refusal reasons. -/
theorem collect_resume_segment {state resumed : State} {response : Term}
    (yielded : resume response state = some resumed) (limits limits' : Limits)
    (heapRoom : limits.heap ≤ limits'.heap + (state.heap.size - (collect state).heap.size))
    (stackRoom : limits.stack ≤ limits'.stack) (ticks : Nat) (budget : Budget) :
    ∃ resumed', resume response (collect state) = some resumed' ∧
      (∀ plan y r, runBounded limits ticks resumed = .yielded plan y → yieldedPlan limits budget y = .ok r →
        ∃ y' r', runBounded limits' ticks resumed' = .yielded (collectRenaming state plan) y' ∧
          Related (collectRenaming state) (liveDomain state) y y' ∧
          yieldedPlan limits' budget y' = .ok r' ∧ r'.value = r.value) ∧
      (∀ value y r, runBounded limits ticks resumed = .finished value y → complete limits budget y = .ok r →
        ∃ y' r', runBounded limits' ticks resumed' = .finished (renameValue (collectRenaming state) value) y' ∧
          complete limits' budget y' = .ok r' ∧ r'.value = r.value) ∧
      (∀ address y, runBounded limits ticks resumed = .divergent address y →
        ∃ y', runBounded limits' ticks resumed' = .divergent (collectRenaming state address) y') ∧
      (∀ reason y, runBounded limits ticks resumed = .refused reason y →
        ∃ y', runBounded limits' ticks resumed' = .refused reason y') := by
  obtain ⟨resumed', again, related⟩ := related_resume (related_collect state) response yielded
  have sameHeap : resumed.heap = state.heap := (resume_keeps_heap_and_stack _ _ _ yielded).1
  have sameHeap' : resumed'.heap = (collect state).heap := (resume_keeps_heap_and_stack _ _ _ again).1
  have room : RoomFor limits limits' resumed resumed' :=
    ⟨by rw [sameHeap, sameHeap']; exact heapRoom, stackRoom⟩
  exact ⟨resumed', again, related_segment related limits limits' room ticks budget⟩

/-- The Plan of a yielded state extracts from its collection to the same Data. -/
theorem collect_yieldedPlan {state : State} {limits : Limits} {budget : Budget} {r : Result}
    (extracted : yieldedPlan limits budget state = .ok r) :
    ∃ r', yieldedPlan limits budget (collect state) = .ok r' ∧ r'.value = r.value := by
  obtain ⟨r', extracted', same, _, _⟩ :=
    related_yieldedPlanWith (fun _ _ _ _ => rfl) limits limits budget (related_collect state) (RoomFor.same _ _ _)
      extracted
  exact ⟨r', extracted', same⟩


#assert_axioms pending_nil
#assert_axioms pending_cons
#assert_axioms bound_of_some
#assert_axioms count_false_set
#assert_axioms all_marked
#assert_axioms markFrom_spec
#assert_axioms liveMarks_spec
#assert_axioms foldl_rankStep
#assert_axioms rankTable_spec
#assert_axioms filterMap_zip_getElem
#assert_axioms filterMap_zip_length
#assert_axioms count_take_le
#assert_axioms count_take_succ
#assert_axioms count_take_lt
#assert_axioms count_take_lt_count
#assert_axioms compact_size
#assert_axioms compact_getElem
#assert_axioms liveDomain_of_not_false
#assert_axioms collectRenaming_live
#assert_axioms collectRenaming_beyond
#assert_axioms collect_heap_size
#assert_axioms related_collect
#assert_axioms HeapRel.lookup
#assert_axioms HeapRel.cellIn
#assert_axioms HeapRel.image_size
#assert_axioms HeapRel.image_size_succ
#assert_axioms HeapRel.push
#assert_axioms HeapRel.set
#assert_axioms allocateFields_foldl
#assert_axioms allocateFields_related
#assert_axioms forcingShared_rename
#assert_axioms valueTerm_rename
#assert_axioms scalarValue_rename
#assert_axioms allIn_nil
#assert_axioms allIn_cons
#assert_axioms allIn_append
#assert_axioms frames_cons
#assert_axioms related_stepRaw
#assert_axioms Related.stack_length
#assert_axioms Related.gap
#assert_axioms runBounded_zero_related
#assert_axioms runBounded_succ_active
#assert_axioms runBounded_succ_inactive
#assert_axioms active_rename
#assert_axioms materializeWith_record
#assert_axioms RoomFor.same
#assert_axioms RoomFor.shift
#assert_axioms not_roomFor_short
#assert_axioms related_runBounded
#assert_axioms related_runBounded_exact
#assert_axioms related_resume
#assert_axioms forceWith_succ_inactive
#assert_axioms forceWith_succ_active
#assert_axioms related_forceWith
#assert_axioms foldlM_related
#assert_axioms related_materializeWith
#assert_axioms related_completeWith
#assert_axioms related_yieldedPlanWith
#assert_axioms related_segment
#assert_axioms renameValue_comp
#assert_axioms renameCell_comp
#assert_axioms renameFrame_comp
#assert_axioms renameControl_comp
#assert_axioms valueAddresses_rename
#assert_axioms cellAddresses_rename
#assert_axioms frameAddresses_rename
#assert_axioms controlAddresses_rename
#assert_axioms Related.trans
#assert_axioms environmentTyping_rename
#assert_axioms valueTyping_rename
#assert_axioms cellTyping_rename
#assert_axioms frameTyping_rename
#assert_axioms stackTyping_rename
#assert_axioms controlTyping_rename
#assert_axioms heapTyping_rename
#assert_axioms image_lt
#assert_axioms environmentValid_rename
#assert_axioms runtimeValueValid_rename
#assert_axioms closureValid_rename
#assert_axioms cellValid_rename
#assert_axioms frameValid_rename
#assert_axioms controlValid_rename
#assert_axioms lexical_related
#assert_axioms stackUpdates_rename
#assert_axioms stackUpdates_in
#assert_axioms nodup_map_on
#assert_axioms busy_related
#assert_axioms finalStack_related
#assert_axioms count_take_surj
#assert_axioms collect_covers
#assert_axioms collectTypes_length
#assert_axioms collectTypes_rel
#assert_axioms typed_collect_exists
#assert_axioms garbageTyped_collected
#assert_axioms garbageTyped_collect_typed
#assert_axioms yieldingTerm_yields
#assert_axioms exampleYield_collected
#assert_axioms exampleYield_plan_agrees
#assert_axioms exampleYield_plan_extracts
#assert_axioms exampleYield_segment_premises
#assert_axioms collect_heap_le
#assert_axioms collect_yielded
#assert_axioms collect_resume_runBounded
#assert_axioms collect_resume_runBounded_exact
#assert_axioms collect_resume_segment
#assert_axioms collect_yieldedPlan
#assert_axioms closureTyping_rename
#assert_axioms typed_related
#assert_axioms typed_collect
#assert_axioms garbageTyping

end Minidregg.Theory.ObjectiveBendDemandCollect
