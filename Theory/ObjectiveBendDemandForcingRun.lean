/- Runs of the demand machine: the stack discipline, the frame lemma, address validity,
and the closed demand a nested evaluation is.

* `stepRaw_stack_shape`: a transition keeps the stack, pushes one frame, replaces the top
  (never an update frame) or pops the top (only from a returned value).
* `stepRaw_withStack`: a transition commutes with appending frames below the stack,
  while the run is inside a shared-cell evaluation (`FrameSafe`).
* `AddrValid` (every held address allocated; `LexicalInvariant` without scoping) is
  preserved by every transition (`addrValid_stepRaw`).
* `stepRaw_heap_keep`: a cell the transition does not read is unchanged.
* `nested_pop`: an entered suspended cell's update frame stays on the stack until it is
  popped, caching the cell, and the run until then is the closed demand of that cell
  with the outer stack appended (`nested_demand`). -/
import Theory.ObjectiveBendDemandForcingAgree
import Theory.ObjectiveBendDemandInvariant
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
set_option autoImplicit false


theorem stepRaw_stack_shape (s : State) :
    (stepRaw s).stack = s.stack ∨ (∃ fr, (stepRaw s).stack = fr :: s.stack) ∨
    (∃ fr rest, s.stack = fr :: rest ∧ (∀ a, fr ≠ .update a) ∧ ∃ fr', (stepRaw s).stack = fr' :: rest) ∨
    (∃ fr rest, s.stack = fr :: rest ∧ (stepRaw s).stack = rest) := by
  obtain ⟨heap, control, stack⟩ := s
  cases control with
  | complete _ | refused _ | blackhole _ | yielded _ => left; rfl
  | enter a =>
    simp only [stepRaw]
    split <;> simp
  | evaluate term env =>
    cases term <;> simp only [stepRaw] <;> (try split) <;> (try split) <;> simp
  | returned v =>
    cases stack with
    | nil => left; rfl
    | cons frame rest =>
      cases frame <;> simp only [stepRaw] <;> (try split) <;> (try split) <;> (try split) <;> simp

def withStack (s : State) (R : List Frame) : State := ⟨s.heap, s.control, s.stack ++ R⟩

def FrameSafe (s : State) : Prop :=
  (∀ v, s.control = .returned v → s.stack ≠ []) ∧
  (∀ p e, s.control = .evaluate (.perform p) e → forcingShared s.stack = true)

theorem forcingShared_append_true {S : List Frame} (R : List Frame) (h : forcingShared S = true) :
    forcingShared (S ++ R) = true := by
  simp only [forcingShared, List.any_append, Bool.or_eq_true] at h ⊢
  exact Or.inl h

theorem stepRaw_withStack (s : State) (R : List Frame) (safe : FrameSafe s) :
    stepRaw (withStack s R) = withStack (stepRaw s) R := by
  obtain ⟨heap, control, stack⟩ := s
  obtain ⟨safeR, safeP⟩ := safe
  simp only at safeR safeP
  cases control with
  | complete _ | refused _ | blackhole _ | yielded _ => rfl
  | enter a =>
    simp only [stepRaw, withStack]
    split <;> simp
  | evaluate term env =>
    cases term with
    | perform plan =>
      have shared := safeP plan env rfl
      simp [stepRaw, withStack, shared, forcingShared_append_true R shared]
    | _ => simp only [stepRaw, withStack] <;> (try split) <;> simp
  | returned v =>
    cases stack with
    | nil => exact absurd rfl (safeR v rfl)
    | cons frame rest =>
      cases frame <;> simp only [stepRaw, withStack, List.cons_append] <;> (try split) <;> (try split) <;>
        (try split) <;> simp



/-- Every address a heap's cells hold is allocated. -/
def HeapValid (heap : Array Cell) : Prop :=
  ∀ (a : Nat) (c : Cell), heap[a]? = some c → AllIn (· < heap.size) (cellAddresses c)

/-- Every address a state holds is allocated (`LexicalInvariant` without the scoping). -/
structure AddrValid (s : State) : Prop where
  heap : HeapValid s.heap
  control : AllIn (· < s.heap.size) (controlAddresses s.control)
  stack : ∀ frame ∈ s.stack, AllIn (· < s.heap.size) (frameAddresses frame)

theorem allIn_mono {P Q : Nat → Prop} {l : List Nat} (h : AllIn P l) (pq : ∀ a, P a → Q a) : AllIn Q l :=
  fun a member => pq a (h a member)

theorem allBelow_mono {n m : Nat} {l : List Nat} (h : AllIn (· < n) l) (le : n ≤ m) : AllIn (· < m) l :=
  allIn_mono h (fun _ lt => Nat.lt_of_lt_of_le lt le)

@[simp] theorem allIn_nil_iff {P : Nat → Prop} : AllIn P [] ↔ True := ⟨fun _ => trivial, fun _ _ m => by cases m⟩

@[simp] theorem allIn_cons_iff {P : Nat → Prop} {a : Nat} {l : List Nat} : AllIn P (a :: l) ↔ P a ∧ AllIn P l :=
  ⟨fun h => ⟨h a (List.mem_cons_self ..), fun x m => h x (List.mem_cons_of_mem _ m)⟩,
   fun h => allIn_cons h.1 h.2⟩

theorem frames_mono {stack : List Frame} {n m : Nat} (h : ∀ frame ∈ stack, AllIn (· < n) (frameAddresses frame))
    (le : n ≤ m) : ∀ frame ∈ stack, AllIn (· < m) (frameAddresses frame) :=
  fun frame member => allBelow_mono (h frame member) le

theorem heapValid_push {heap : Array Cell} {c : Cell} (valid : HeapValid heap)
    (cIn : AllIn (· < heap.size + 1) (cellAddresses c)) : HeapValid (heap.push c) := by
  intro a c' found
  show AllIn (· < (heap.push c).size) _
  simp only [Array.size_push]
  by_cases eq : a = heap.size
  · subst eq; simp at found; subst found; exact cIn
  · have : heap[a]? = some c' := by simpa [Array.getElem?_push, eq] using found
    exact allBelow_mono (valid a c' this) (Nat.le_succ _)

theorem heapValid_set {heap : Array Cell} {a : Nat} {c : Cell} (valid : HeapValid heap)
    (cIn : AllIn (· < heap.size) (cellAddresses c)) : HeapValid (heap.set! a c) := by
  intro b c' found
  show AllIn (· < (heap.set! a c).size) _
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  by_cases eq : a = b
  · subst eq
    by_cases bound : a < heap.size
    · simp [bound] at found; subst found; exact cIn
    · simp [bound] at found
  · have : heap[b]? = some c' := by simpa [eq] using found
    exact valid b c' this

theorem allocateFields_valid' {heap : Array Cell} {environment : List Nat} (valid : HeapValid heap)
    (envIn : AllIn (· < heap.size) environment) (fields : List (String × Term)) :
    HeapValid (allocateFields heap environment fields).1 ∧
      heap.size ≤ (allocateFields heap environment fields).1.size ∧
      AllIn (· < (allocateFields heap environment fields).1.size)
        ((allocateFields heap environment fields).2.map Prod.snd) := by
  suffices ∀ (h : Array Cell) (acc : List (String × Nat)), HeapValid h → heap.size ≤ h.size →
      AllIn (· < h.size) (acc.map Prod.snd) →
      HeapValid (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (h,acc)).1 ∧
      h.size ≤ (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (h,acc)).1.size ∧
      AllIn (· < (fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (h,acc)).1.size)
        ((fields.foldl (fun (prior : Array Cell × List (String × Address)) field =>
            (prior.1.push (.suspended ⟨field.2,environment⟩),(field.1,prior.1.size)::prior.2)) (h,acc)).2.map Prod.snd) by
    obtain ⟨v, le, inside⟩ := this heap [] valid (Nat.le_refl _) (allIn_nil _)
    refine ⟨v, le, ?_⟩
    intro x member
    simp only [allocateFields, List.map_reverse, List.mem_reverse] at member ⊢
    exact inside x member
  induction fields with
  | nil => intro h acc v le accIn; exact ⟨v, Nat.le_refl _, accIn⟩
  | cons field rest ih =>
    intro h acc v le accIn
    simp only [List.foldl_cons]
    have v' : HeapValid (h.push (.suspended ⟨field.2, environment⟩)) :=
      heapValid_push v (allBelow_mono envIn (by omega))
    have accIn' : AllIn (· < (h.push (.suspended ⟨field.2, environment⟩)).size)
        (((field.1, h.size) :: acc).map Prod.snd) := by
      intro x member
      simp only [List.map_cons, List.mem_cons, Array.size_push] at member ⊢
      rcases member with rfl | member
      · omega
      · exact Nat.lt_succ_of_lt (accIn x member)
    obtain ⟨a, b, c⟩ := ih _ _ v' (by simp; omega) accIn'
    exact ⟨a, by simp at b ⊢; omega, c⟩

theorem addrValid_stepRaw {s : State} (valid : AddrValid s) : AddrValid (stepRaw s) := by
  obtain ⟨hv, cv, sv⟩ := valid
  obtain ⟨heap, control, stack⟩ := s
  simp only at hv cv sv
  have sizeSet : ∀ (a : Nat) (c : Cell), (heap.set! a c).size = heap.size := by intro a c; simp
  cases control with
  | complete v => exact ⟨hv, cv, sv⟩
  | refused r => exact ⟨hv, cv, sv⟩
  | blackhole a => exact ⟨hv, cv, sv⟩
  | yielded p => exact ⟨hv, cv, sv⟩
  | enter a =>
    simp only [stepRaw]
    cases found : heap[a]? with
    | none => exact ⟨hv, by simp [controlAddresses], sv⟩
    | some cell =>
      have cellIn := hv a cell found
      cases cell with
      | evaluating o => exact ⟨hv, cv, sv⟩
      | cached o v =>
        exact ⟨hv, fun x member => cellIn x (List.mem_append_right _ member), sv⟩
      | suspended o =>
        refine ⟨heapValid_set hv (c := .evaluating o) cellIn, ?_, ?_⟩
        · show AllIn _ o.environment; rw [sizeSet]; exact cellIn
        · intro frame member
          show AllIn (· < (heap.set! a (.evaluating o)).size) _
          rw [sizeSet]
          rcases List.mem_cons.mp member with rfl | member
          · exact cv
          · exact sv frame member
  | evaluate term env =>
    have envIn : AllIn (· < heap.size) env := cv
    cases term with
    | bound i =>
      simp only [stepRaw]
      cases found : env[i]? with
      | none => exact ⟨hv, by simp [controlAddresses], sv⟩
      | some a => exact ⟨hv, by simpa [controlAddresses] using envIn a (List.mem_of_getElem? found), sv⟩
    | lam body => exact ⟨hv, envIn, sv⟩
    | nat n => exact ⟨hv, by simp [stepRaw, controlAddresses, valueAddresses], by simpa [stepRaw] using sv⟩
    | boolean b => exact ⟨hv, by simp [stepRaw, controlAddresses, valueAddresses], by simpa [stepRaw] using sv⟩
    | label l => exact ⟨hv, by simp [stepRaw, controlAddresses, valueAddresses], by simpa [stepRaw] using sv⟩
    | app fn arg => exact ⟨hv, envIn, frames_cons envIn sv⟩
    | mix lower upper => exact ⟨hv, envIn, sv⟩
    | fix spec inherited =>
      simp only [stepRaw]
      refine ⟨heapValid_push hv ?_, ?_, frames_mono sv (by simp only [Array.size_push]; omega)⟩
      · simp only [cellAddresses, allIn_cons_iff]
        exact ⟨by omega, allBelow_mono envIn (by omega)⟩
      · simp [controlAddresses]
    | specification descriptor extension =>
      simp only [stepRaw]
      refine ⟨heapValid_push (heapValid_push hv (allBelow_mono envIn (by omega)))
        (allBelow_mono envIn (by simp only [Array.size_push]; omega)), ?_, frames_mono sv (by simp only [Array.size_push]; omega)⟩
      simp [controlAddresses, valueAddresses] <;> omega
    | prototype spec target =>
      simp only [stepRaw]
      refine ⟨heapValid_push (heapValid_push hv (allBelow_mono envIn (by omega)))
        (allBelow_mono envIn (by simp only [Array.size_push]; omega)), ?_, frames_mono sv (by simp only [Array.size_push]; omega)⟩
      simp [controlAddresses, valueAddresses] <;> omega
    | reflect body => exact ⟨hv, envIn, frames_cons (allIn_nil _) sv⟩
    | metadata body => exact ⟨hv, envIn, frames_cons (allIn_nil _) sv⟩
    | project body => exact ⟨hv, envIn, frames_cons (allIn_nil _) sv⟩
    | record fields =>
      simp only [stepRaw]
      obtain ⟨v', le, inside⟩ := allocateFields_valid' hv envIn fields
      exact ⟨v', inside, frames_mono sv le⟩
    | get target name => exact ⟨hv, envIn, frames_cons (allIn_nil _) sv⟩
    | extend inherited fields => exact ⟨hv, envIn, frames_cons envIn sv⟩
    | ifZero value zero successorBody => exact ⟨hv, envIn, frames_cons envIn sv⟩
    | binary primitive left right => exact ⟨hv, envIn, frames_cons envIn sv⟩
    | inject tag payload =>
      simp only [stepRaw]
      refine ⟨heapValid_push hv (allBelow_mono envIn (by omega)), ?_, frames_mono sv (by simp only [Array.size_push]; omega)⟩
      simp [controlAddresses, valueAddresses] <;> omega
    | case scrutinee arms => exact ⟨hv, envIn, frames_cons envIn sv⟩
    | ifBool condition whenTrue whenFalse => exact ⟨hv, envIn, frames_cons envIn sv⟩
    | done value => exact ⟨hv, envIn, sv⟩
    | perform plan =>
      simp only [stepRaw]
      cases shared : forcingShared stack with
      | true => exact ⟨hv, by simp [controlAddresses], sv⟩
      | false =>
        simp only [Bool.false_eq_true, if_false]
        refine ⟨heapValid_push hv (allBelow_mono envIn (by omega)), ?_, frames_mono sv (by simp only [Array.size_push]; omega)⟩
        simp [controlAddresses] <;> omega
  | returned v =>
    have valueIn : AllIn (· < heap.size) (valueAddresses v) := cv
    cases stack with
    | nil => exact ⟨hv, valueIn, sv⟩
    | cons frame rest =>
      have ⟨frameIn, restIn⟩ := List.forall_mem_cons.mp sv
      cases frame with
      | update a =>
        simp only [stepRaw]
        cases found : heap[a]? with
        | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
        | some cell =>
          have cellIn := hv a cell found
          cases cell with
          | suspended o => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | cached o w => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | evaluating o =>
            refine ⟨heapValid_set hv (c := .cached o v) (allIn_append cellIn valueIn), ?_, ?_⟩
            · show AllIn (· < (heap.set! a (.cached o v)).size) _; rw [sizeSet]; exact valueIn
            · intro fr member
              show AllIn (· < (heap.set! a (.cached o v)).size) _; rw [sizeSet]; exact restIn fr member
      | reflect =>
        simp only [stepRaw]
        cases v with
        | prototype spec target =>
          exact ⟨hv, by simpa [controlAddresses] using valueIn spec (by simp [valueAddresses]), restIn⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | metadata =>
        simp only [stepRaw]
        cases v with
        | specification descriptor extension =>
          exact ⟨hv, by simpa [controlAddresses] using valueIn descriptor (by simp [valueAddresses]), restIn⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | project =>
        simp only [stepRaw]
        cases v with
        | prototype spec target =>
          exact ⟨hv, by simpa [controlAddresses] using valueIn target (by simp [valueAddresses]), restIn⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | argument argument environment =>
        simp only [stepRaw]
        cases v with
        | specification descriptor extension =>
          exact ⟨hv, by simpa [controlAddresses] using valueIn extension (by simp [valueAddresses]), sv⟩
        | closure body captured =>
          have environmentIn : AllIn (· < heap.size) environment := frameIn
          have capturedIn : AllIn (· < heap.size) captured := valueIn
          simp only [stepRaw]
          refine ⟨heapValid_push hv (allBelow_mono environmentIn (by omega)), ?_, frames_mono restIn (by simp only [Array.size_push]; omega)⟩
          simp only [controlAddresses, allIn_cons_iff, Array.size_push]
          exact ⟨by omega, allBelow_mono capturedIn (by omega)⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | field name =>
        simp only [stepRaw]
        cases v with
        | record fields =>
          simp only [stepRaw]
          cases found : fields.find? (fun field => field.1 == name) with
          | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | some entry =>
            have member := List.mem_of_find?_eq_some found
            exact ⟨hv, by simpa [controlAddresses] using valueIn entry.2 (List.mem_map_of_mem member), restIn⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | extend fields environment =>
        simp only [stepRaw]
        cases v with
        | record inherited =>
          have environmentIn : AllIn (· < heap.size) environment := frameIn
          simp only [stepRaw]
          obtain ⟨v', le, inside⟩ := allocateFields_valid' hv environmentIn fields
          refine ⟨v', ?_, frames_mono restIn le⟩
          have retainedIn : AllIn (· < (allocateFields heap environment fields).1.size)
              ((inherited.filter (fun prior => !(fields.any fun field => field.1 == prior.1))).map Prod.snd) := by
            intro x member
            obtain ⟨entry, kept, eq⟩ := List.mem_map.mp member
            rw [← eq]; exact Nat.lt_of_lt_of_le (valueIn _ (List.mem_map_of_mem (List.mem_filter.mp kept).1)) le
          have := allIn_append inside retainedIn
          rw [← List.map_append] at this
          exact this
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | condition zero successorBody environment =>
        simp only [stepRaw]
        cases v with
        | natural n =>
          cases n with
          | zero => exact ⟨hv, frameIn, restIn⟩
          | succ n =>
            have environmentIn : AllIn (· < heap.size) environment := frameIn
            simp only [stepRaw]
            refine ⟨heapValid_push hv (by simp [cellAddresses, valueAddresses]), ?_, frames_mono restIn (by simp only [Array.size_push]; omega)⟩
            simp only [controlAddresses, allIn_cons_iff, Array.size_push]
            exact ⟨by omega, allBelow_mono environmentIn (by omega)⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | binaryLeft primitive right environment =>
        exact ⟨hv, frameIn, frames_cons valueIn restIn⟩
      | binaryRight primitive left =>
        simp only [stepRaw]
        cases computed : (valueTerm left).bind (fun l => (valueTerm v).bind (primitiveResult primitive l)) with
        | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
        | some result =>
          dsimp only
          cases scalar : scalarValue result with
          | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | some next =>
            have ⟨_, empty⟩ := scalarValue_rename (f := id) scalar
            refine ⟨hv, ?_, restIn⟩
            show AllIn _ (valueAddresses next); rw [empty]; exact allIn_nil _
      | case arms environment =>
        simp only [stepRaw]
        cases v with
        | variant tag payload =>
          simp only [stepRaw]
          cases found : arms.find? (fun arm => arm.1 == tag) with
          | none => exact ⟨hv, by simp [controlAddresses], restIn⟩
          | some arm =>
            have environmentIn : AllIn (· < heap.size) environment := frameIn
            refine ⟨heapValid_push hv (allBelow_mono valueIn (by omega)), ?_, frames_mono restIn (by simp only [Array.size_push]; omega)⟩
            simp only [controlAddresses, allIn_cons_iff, Array.size_push]
            exact ⟨by omega, allBelow_mono environmentIn (by omega)⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩
      | ifBool whenTrue whenFalse environment =>
        simp only [stepRaw]
        cases v with
        | boolean b => cases b <;> exact ⟨hv, frameIn, restIn⟩
        | _ => exact ⟨hv, by simp [controlAddresses], restIn⟩



/-- `after` extends `before`: every allocated cell is unchanged. -/
def PrefixExt (before after : Array Cell) : Prop :=
  before.size ≤ after.size ∧ ∀ b, b < before.size → after[b]? = before[b]?

theorem prefixExt_refl (h : Array Cell) : PrefixExt h h := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem prefixExt_trans {a b c : Array Cell} (ab : PrefixExt a b) (bc : PrefixExt b c) : PrefixExt a c :=
  ⟨Nat.le_trans ab.1 bc.1, fun x lt => by rw [bc.2 x (Nat.lt_of_lt_of_le lt ab.1), ab.2 x lt]⟩

theorem prefixExt_push (h : Array Cell) (c : Cell) : PrefixExt h (h.push c) :=
  ⟨by simp, fun b lt => by simp [Array.getElem?_push, Nat.ne_of_lt lt]⟩

theorem prefixExt_alloc (heap : Array Cell) (environment : Environment) (fields : List (String × Term)) :
    PrefixExt heap (allocateFields heap environment fields).1 := by
  have loop : ∀ (fields : List (String × Term)) (pair : Array Cell × List (String × Address)),
      PrefixExt pair.1
        (fields.foldl (fun prior field => (prior.1.push (.suspended ⟨field.2,environment⟩),
          (field.1,prior.1.size)::prior.2)) pair).1 := by
    intro fields
    induction fields with
    | nil => intro pair; exact prefixExt_refl _
    | cons field fields ih =>
      intro pair
      simpa only [List.foldl_cons] using prefixExt_trans (prefixExt_push pair.1 (.suspended ⟨field.2,environment⟩))
        (ih (pair.1.push (.suspended ⟨field.2,environment⟩),(field.1,pair.1.size)::pair.2))
  exact loop fields (heap,[])

/-- A transition leaves the heap, writes the cell it reads, or only allocates. -/
theorem stepRaw_heap_cases (s : State) :
    (stepRaw s).heap = s.heap ∨ (∃ a c, readsAt s = some a ∧ (stepRaw s).heap = s.heap.set! a c) ∨
      PrefixExt s.heap (stepRaw s).heap := by
  obtain ⟨heap, control, stack⟩ := s
  unfold stepRaw
  split <;> repeat' first | split
  all_goals try dsimp only
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inr (prefixExt_push _ _))
    | exact Or.inr (Or.inr (prefixExt_trans (prefixExt_push _ _) (prefixExt_push _ _)))
    | exact Or.inr (Or.inr (prefixExt_alloc _ _ _))
    | (refine Or.inr (Or.inl ⟨_, _, ?_, rfl⟩); simp_all [readsAt])

/-- **A cell no transition reads is unchanged.** -/
theorem stepRaw_heap_keep (s : State) {b : Nat} (bound : b < s.heap.size) (unread : readsAt s ≠ some b) :
    (stepRaw s).heap[b]? = s.heap[b]? := by
  rcases stepRaw_heap_cases s with same | ⟨a, c, reads, eq⟩ | ext
  · rw [same]
  · rw [eq]
    have ne : a ≠ b := fun h => unread (h ▸ reads)
    simp [ne]
  · exact ext.2 b bound

theorem stepRaw_size_mono (s : State) : s.heap.size ≤ (stepRaw s).heap.size := by
  rcases stepRaw_heap_cases s with same | ⟨a, c, _, eq⟩ | ext
  · rw [same]; exact Nat.le_refl _
  · rw [eq]; simp
  · exact ext.1


end Minidregg.Theory.ObjectiveBendDemandForcing
