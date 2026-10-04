/- Agreement up to renaming, except on cells a run never reads.

`StateAgree f D U s t`: `t` is `s` renamed by `f` on the domain `D` (which contains
everything past `s`'s heap, where `f` is the shift between the two heap ends), except
that the cells at the addresses of `U` may differ arbitrarily. A transition that does
not read a `U` cell (`readsAt`) keeps the relation (`agree_stepRaw`), so a run that
never reads one is mirrored step for step (`agree_exec`).

This generalizes `ObjectiveBendDemandCollect.Related` (the collect relation, `U` empty,
the image heap no larger) to the shapes the forcing-transparency proof needs: the forced
heap may be LARGER (it holds the cells a demand allocated), and a cell may be suspended
on one side and cached on the other while nothing reads it. -/
import Theory.ObjectiveBendDemandCollectProofs
namespace Minidregg.Theory.ObjectiveBendDemandForcing
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandCollect
set_option autoImplicit false

/-- Heaps agree under `f` on `D`, except at `U`. -/
structure HeapAgree (f : Nat → Nat) (D U : Nat → Prop) (heap heap' : Array Cell) : Prop where
  beyond : ∀ a, heap.size ≤ a → D a ∧ ¬ U a ∧ f a + heap.size = a + heap'.size
  inj : ∀ a b, D a → D b → f a = f b → a = b
  cells : ∀ a, D a → ¬ U a → a < heap.size →
    ∃ c, heap[a]? = some c ∧ heap'[f a]? = some (renameCell f c) ∧ AllIn D (cellAddresses c)

/-- States agree: heaps agree, control and stack are renamed. -/
structure StateAgree (f : Nat → Nat) (D U : Nat → Prop) (s t : State) : Prop where
  heap : HeapAgree f D U s.heap t.heap
  controlIn : AllIn D (controlAddresses s.control)
  control : t.control = renameControl f s.control
  stackIn : ∀ frame ∈ s.stack, AllIn D (frameAddresses frame)
  stack : t.stack = s.stack.map (renameFrame f)

/-- The heap cell a transition reads: the entered address, or the cell an update
frame on top of a returned value caches. -/
def readsAt (state : State) : Option Nat :=
  match state.control, state.stack with
  | .enter address, _ => some address
  | .returned _, .update address :: _ => some address
  | _, _ => none

/-- The transition reads no cell of `U`. -/
def Avoids (U : Nat → Prop) (state : State) : Prop := ∀ a, readsAt state = some a → ¬ U a

namespace HeapAgree
variable {f : Nat → Nat} {D U : Nat → Prop} {heap heap' : Array Cell}

theorem lookup (hr : HeapAgree f D U heap heap') {a : Nat} (inD : D a) (notU : ¬ U a) :
    heap'[f a]? = (heap[a]?).map (renameCell f) := by
  by_cases bound : a < heap.size
  · obtain ⟨c, found, found', _⟩ := hr.cells a inD notU bound
    rw [found, found']; rfl
  · have shift := (hr.beyond a (Nat.le_of_not_lt bound)).2.2
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt bound), Array.getElem?_eq_none (by omega)]
    rfl

theorem cellIn (hr : HeapAgree f D U heap heap') {a : Nat} {c : Cell} (inD : D a) (notU : ¬ U a)
    (found : heap[a]? = some c) : AllIn D (cellAddresses c) := by
  obtain ⟨c', found', _, inC⟩ := hr.cells a inD notU (bound_of_some found)
  rw [found] at found'; cases found'; exact inC

theorem image_size (hr : HeapAgree f D U heap heap') : f heap.size = heap'.size ∧ D heap.size := by
  have := hr.beyond heap.size (Nat.le_refl _); exact ⟨by omega, this.1⟩

theorem image_size_succ (hr : HeapAgree f D U heap heap') :
    f (heap.size + 1) = heap'.size + 1 ∧ D (heap.size + 1) := by
  have := hr.beyond (heap.size + 1) (Nat.le_succ _); exact ⟨by omega, this.1⟩

theorem image_lt (hr : HeapAgree f D U heap heap') {a : Nat} (inD : D a) (bound : a < heap.size) :
    f a < heap'.size := by
  by_cases lt : f a < heap'.size
  · exact lt
  · have past : heap.size ≤ f a + heap.size - heap'.size := by omega
    have ⟨inD', _, shift⟩ := hr.beyond (f a + heap.size - heap'.size) past
    have same := hr.inj _ _ inD inD' (by omega)
    omega

theorem push (hr : HeapAgree f D U heap heap') {c : Cell} (cIn : AllIn D (cellAddresses c)) :
    HeapAgree f D U (heap.push c) (heap'.push (renameCell f c)) := by
  refine ⟨?_, hr.inj, ?_⟩
  · intro a past
    simp at past
    have := hr.beyond a (by omega)
    exact ⟨this.1, this.2.1, by simp; omega⟩
  · intro a inD notU bound
    simp at bound
    by_cases old : a < heap.size
    · obtain ⟨c', found, found', inC⟩ := hr.cells a inD notU old
      have lt : f a < heap'.size := bound_of_some found'
      refine ⟨c', ?_, ?_, inC⟩
      · simp [Array.getElem?_push, Nat.ne_of_lt old, found]
      · simp [Array.getElem?_push, Nat.ne_of_lt lt, found']
    · have eq : a = heap.size := by omega
      subst eq
      refine ⟨c, by simp, ?_, cIn⟩
      rw [hr.image_size.1]; simp

theorem set (hr : HeapAgree f D U heap heap') {a : Nat} {c : Cell} (inD : D a) (notU : ¬ U a)
    (bound : a < heap.size) (cIn : AllIn D (cellAddresses c)) :
    HeapAgree f D U (heap.set! a c) (heap'.set! (f a) (renameCell f c)) := by
  obtain ⟨_, _, found', _⟩ := hr.cells a inD notU bound
  have lt : f a < heap'.size := bound_of_some found'
  refine ⟨?_, hr.inj, ?_⟩
  · intro b past; simp at past; have := hr.beyond b past; exact ⟨this.1, this.2.1, by simp; exact this.2.2⟩
  · intro b inB notUB boundB
    simp at boundB
    by_cases same : a = b
    · subst same
      exact ⟨c, by simp [bound], by simp [lt], cIn⟩
    · obtain ⟨c', found, found'', inC⟩ := hr.cells b inB notUB boundB
      have diff : f a ≠ f b := fun h => same (hr.inj a b inD inB h)
      exact ⟨c', by simp [same, found], by simp [diff, found''], inC⟩

end HeapAgree

theorem allocateFields_foldl_agree {f : Nat → Nat} {D U : Nat → Prop} (environment : List Nat)
    (environmentIn : AllIn D environment) (fields : List (String × Term)) :
    ∀ (heap heap' : Array Cell) (acc : List (String × Nat)),
      HeapAgree f D U heap heap' → AllIn D (acc.map Prod.snd) →
      HeapAgree f D U
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

theorem allocateFields_agree {f : Nat → Nat} {D U : Nat → Prop} {heap heap' : Array Cell}
    (hr : HeapAgree f D U heap heap') {environment : List Nat} (environmentIn : AllIn D environment)
    (fields : List (String × Term)) :
    HeapAgree f D U (allocateFields heap environment fields).1
        (allocateFields heap' (environment.map f) fields).1 ∧
      (allocateFields heap' (environment.map f) fields).2 =
        (allocateFields heap environment fields).2.map (fun field => (field.1, f field.2)) ∧
      AllIn D ((allocateFields heap environment fields).2.map Prod.snd) := by
  obtain ⟨hr', same, inside⟩ := allocateFields_foldl_agree environment environmentIn fields heap heap' []
    hr (fun _ member => by cases member)
  refine ⟨hr', ?_, ?_⟩
  · simp only [allocateFields]
    simp only [List.map_nil] at same
    rw [same, List.map_reverse]
  · intro x member
    simp only [allocateFields, List.map_reverse, List.mem_reverse] at member
    exact inside x member

/-- **Lockstep.** An agreeing pair steps to an agreeing pair, provided the transition
reads no cell of `U`. -/
theorem agree_stepRaw {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (related : StateAgree f D U s t)
    (avoids : Avoids U s) : StateAgree f D U (stepRaw s) (stepRaw t) := by
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
    have notU : ¬ U a := avoids a (by simp [readsAt])
    simp only [stepRaw, renameControl]
    rw [hr.lookup inA notU]
    cases found : heap[a]? with
    | none => exact ⟨hr, allIn_nil D, rfl, stackIn, rfl⟩
    | some cell =>
      have cellIn := hr.cellIn inA notU found
      cases cell with
      | evaluating o => exact ⟨hr, controlIn, rfl, stackIn, rfl⟩
      | cached o v => exact ⟨hr, fun x member => cellIn x (List.mem_append_right _ member), rfl, stackIn, rfl⟩
      | suspended o =>
        exact ⟨hr.set inA notU (bound_of_some found) (c := .evaluating o) cellIn, cellIn, rfl,
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
      obtain ⟨hr', same, inside⟩ := allocateFields_agree hr envIn fields
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
        have notU : ¬ U a := avoids a (by simp [readsAt])
        simp only [stepRaw, renameControl, List.map_cons, renameFrame]
        rw [hr.lookup inA notU]
        cases found : heap[a]? with
        | none => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
        | some cell =>
          have cellIn := hr.cellIn inA notU found
          cases cell with
          | suspended o => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | cached o w => exact ⟨hr, allIn_nil D, rfl, restIn, rfl⟩
          | evaluating o =>
            exact ⟨hr.set inA notU (bound_of_some found) (c := .cached o v) (allIn_append cellIn valueIn),
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
          obtain ⟨hr', same, inside⟩ := allocateFields_agree hr environmentIn fields
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

/-! ## Runs -/

/-- `n` raw transitions (no capacity, no tick budget). -/
def exec : Nat → State → State
  | 0, state => state
  | n + 1, state => exec n (stepRaw state)

theorem exec_add (m n : Nat) (state : State) : exec (m + n) state = exec n (exec m state) := by
  induction m generalizing state with
  | zero => simp [exec]
  | succ m ih => rw [Nat.succ_add]; simp only [exec]; exact ih _

theorem exec_succ (n : Nat) (state : State) : exec (n + 1) state = stepRaw (exec n state) := by
  rw [exec_add n 1]; rfl

theorem exec_one (state : State) : exec 1 state = stepRaw state := rfl

/-- **A run that reads no `U` cell is mirrored step for step.** -/
theorem agree_exec {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (related : StateAgree f D U s t)
    (n : Nat) (avoids : ∀ j, j < n → Avoids U (exec j s)) : StateAgree f D U (exec n s) (exec n t) := by
  induction n with
  | zero => exact related
  | succ n ih =>
    rw [exec_succ, exec_succ]
    exact agree_stepRaw (ih (fun j lt => avoids j (by omega))) (avoids n (by omega))

theorem StateAgree.active_eq {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (related : StateAgree f D U s t) :
    active t.control = active s.control := by
  rw [related.control, active_rename]

theorem StateAgree.stack_length {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (related : StateAgree f D U s t) :
    t.stack.length = s.stack.length := by
  rw [related.stack, List.length_map]

theorem StateAgree.readsAt_eq {f : Nat → Nat} {D U : Nat → Prop} {s t : State} (related : StateAgree f D U s t) :
    readsAt t = (readsAt s).map f := by
  obtain ⟨_, _, controlEq, _, stackEq⟩ := related
  obtain ⟨heap, control, stack⟩ := s
  obtain ⟨heap', control', stack'⟩ := t
  simp only at controlEq stackEq
  subst controlEq stackEq
  cases control <;> simp [readsAt, renameControl]
  rename_i v
  cases stack with
  | nil => simp
  | cons frame rest => cases frame <;> simp [renameFrame]

#assert_axioms HeapAgree.lookup
#assert_axioms HeapAgree.image_lt
#assert_axioms HeapAgree.push
#assert_axioms HeapAgree.set
#assert_axioms allocateFields_agree
#assert_axioms agree_stepRaw
#assert_axioms exec_add
#assert_axioms agree_exec
#assert_axioms StateAgree.readsAt_eq

end Minidregg.Theory.ObjectiveBendDemandForcing
