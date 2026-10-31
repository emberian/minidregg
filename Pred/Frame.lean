/-
# Pred.Frame — a law reads only its slots (the demand-driven projection's statement)

A policy state is a list of named slots, and a projection that names every byte of a
cell (`resource/bytes/<i>`, three times over) costs O(cell) formatted names per check
even when the law reads two slots (docs/HOT-PATH-STATE.md, the flatness submit red).
This module states what lets a projection build only the slots its law reads:

- `Pred.reads p`: the slots `p` reads, on either side.
- `State.restrict keys s`: `s`'s slots whose names are in `keys`, in order.
- `eval_restrict`: a law's verdict on the restricted states is its verdict on the whole
  states. `evalWith_frame` is the general form, for any oracle that ignores the states
  (the policy path's `eval` uses `failClosed`).

Teeth (`restrict_needs_reads`): the restriction to too few names changes a verdict, so
`reads` is not vacuous. Satisfiable: every law and pair of states (`eval_restrict`).
-/
module

public import Pred.Core

import all Init.Data.List.Basic

@[expose] public section

namespace Minidregg.Pred

mutual
  /-- The slots a law reads, on either side of the step. `witnessed` reads none of its
  own (its oracle is an argument); `hashEq` reads the cell slot, its values, the blinder
  and the commit. -/
  def Pred.reads : Pred → List Slot
    | .eq s _ => [s]
    | .le s _ => [s]
    | .memberOf s _ => [s]
    | .writeOnce s => [s]
    | .monotone s => [s]
    | .eqSlots a b => [a, b]
    | .leSlots a b => [a, b]
    | .leSlotsOff a b _ => [a, b]
    | .sumEq l r => l ++ r
    | .witnessed _ => []
    | .hashEq vs b c => hashEqCellSlot :: b :: c :: vs
    | .ran program => [ranSlot program]
    | .not q => q.reads
    | .allL ps => ps.reads
    | .anyL ps => ps.reads
  /-- The slots a list of laws reads. -/
  def PredList.reads : PredList → List Slot
    | .nil => []
    | .cons q rest => q.reads ++ rest.reads
end

/-- Two states read alike at every name in `keys`. -/
def State.AgreeOn (keys : List Slot) (s s' : State) : Prop :=
  ∀ k ∈ keys, s.get k = s'.get k

/-- The slots of `s` whose names are in `keys`, in their order. -/
def State.restrict (keys : List Slot) (s : State) : State :=
  ⟨s.slots.filter fun slot => keys.contains slot.1⟩

/-- **Restriction keeps every read it is restricted to.** -/
theorem State.get_restrict {keys : List Slot} {k : Slot} (member : k ∈ keys) (s : State) :
    (s.restrict keys).get k = s.get k := by
  unfold State.restrict State.get
  congr 1
  induction s.slots with
  | nil => rfl
  | cons slot rest ih =>
      by_cases same : slot.1 = k
      · subst same
        simp [member]
      · have differ : (slot.1 == k) = false := by simp [same]
        by_cases kept : keys.contains slot.1 = true
        · simp only [List.filter_cons, kept, ite_true, List.find?_cons, differ]
          exact ih
        · simp only [List.filter_cons, kept, List.find?_cons, differ]
          simpa using ih

theorem State.agreeOn_restrict (keys : List Slot) (s : State) :
    State.AgreeOn keys (s.restrict keys) s :=
  fun _ member => State.get_restrict member s

theorem State.AgreeOn.mono {keys keys' : List Slot} {s s' : State}
    (agree : State.AgreeOn keys s s') (sub : ∀ k ∈ keys', k ∈ keys) : State.AgreeOn keys' s s' :=
  fun k member => agree k (sub k member)

private theorem sumOf_agree {s s' : State} :
    ∀ (slots : List Slot), State.AgreeOn slots s s' → sumOf s slots = sumOf s' slots
  | [], _ => rfl
  | slot :: rest, agree => by
      simp only [sumOf, agree slot (by simp),
        sumOf_agree rest (agree.mono fun k member => by simp [member])]

private theorem getAll_agree {s s' : State} :
    ∀ (slots : List Slot), State.AgreeOn slots s s' → s.getAll slots = s'.getAll slots
  | [], _ => rfl
  | slot :: rest, agree => by
      simp only [State.getAll, agree slot (by simp),
        getAll_agree rest (agree.mono fun k member => by simp [member])]

private theorem hashEqHolds_agree (H : Theory.HashBytes.Hash) {s s' : State}
    (vs : List Slot) (b c : Slot) (agree : State.AgreeOn (hashEqCellSlot :: b :: c :: vs) s s') :
    hashEqHolds H s vs b c = hashEqHolds H s' vs b c := by
  have cell := agree hashEqCellSlot (by simp)
  have blinder := agree b (by simp)
  have commit := agree c (by simp)
  have values := getAll_agree vs (agree.mono fun k member => by simp [member])
  simp only [hashEqHolds, hashEqOpening, cell, blinder, commit, values]

mutual
  /-- **A law reads only its slots**: states that agree on `p.reads`, on both sides, get
  the same verdict, for an oracle that ignores the states. -/
  theorem evalWith_frame (O : Oracle) (constant : ∀ vk old new old' new', O vk old new = O vk old' new') :
      ∀ (p : Pred) {old new old' new' : State},
        State.AgreeOn p.reads old old' → State.AgreeOn p.reads new new' →
        evalWith O p old new = evalWith O p old' new'
    | .eq s v, _, _, _, _, _, n => by simp only [evalWith, n s (by simp [Pred.reads])]
    | .le s v, _, _, _, _, _, n => by simp only [evalWith, n s (by simp [Pred.reads])]
    | .memberOf s xs, _, _, _, _, _, n => by simp only [evalWith, n s (by simp [Pred.reads])]
    | .writeOnce s, _, _, _, _, o, n => by
        simp only [evalWith, o s (by simp [Pred.reads]), n s (by simp [Pred.reads])]
    | .monotone s, _, _, _, _, o, n => by
        simp only [evalWith, o s (by simp [Pred.reads]), n s (by simp [Pred.reads])]
    | .eqSlots a b, _, _, _, _, _, n => by
        simp only [evalWith, n a (by simp [Pred.reads]), n b (by simp [Pred.reads])]
    | .leSlots a b, _, _, _, _, _, n => by
        simp only [evalWith, n a (by simp [Pred.reads]), n b (by simp [Pred.reads])]
    | .leSlotsOff a b k, _, _, _, _, _, n => by
        simp only [evalWith, n a (by simp [Pred.reads]), n b (by simp [Pred.reads])]
    | .sumEq l r, _, _, _, _, _, n => by
        simp only [evalWith,
          sumOf_agree l (n.mono fun k member => by simp [Pred.reads, member]),
          sumOf_agree r (n.mono fun k member => by simp [Pred.reads, member])]
    | .witnessed vk, _, _, _, _, _, _ => by simp only [evalWith]; exact constant vk _ _ _ _
    | .hashEq vs b c, _, _, _, _, _, n => by
        simp only [evalWith]; exact hashEqHolds_agree _ vs b c n
    | .ran program, _, _, _, _, _, n => by
        simp only [evalWith, n (ranSlot program) (by simp [Pred.reads])]
    | .not q, _, _, _, _, o, n => by
        simp only [evalWith, evalWith_frame O constant q o n]
    | .allL ps, _, _, _, _, o, n => by
        simp only [evalWith]; exact evalWithAll_frame O constant ps o n
    | .anyL ps, _, _, _, _, o, n => by
        simp only [evalWith]; exact evalWithAny_frame O constant ps o n
  theorem evalWithAll_frame (O : Oracle) (constant : ∀ vk old new old' new', O vk old new = O vk old' new') :
      ∀ (ps : PredList) {old new old' new' : State},
        State.AgreeOn ps.reads old old' → State.AgreeOn ps.reads new new' →
        evalWithAll O ps old new = evalWithAll O ps old' new'
    | .nil, _, _, _, _, _, _ => rfl
    | .cons q rest, _, _, _, _, o, n => by
        simp only [evalWithAll,
          evalWith_frame O constant q (o.mono fun k member => by simp [PredList.reads, member])
            (n.mono fun k member => by simp [PredList.reads, member]),
          evalWithAll_frame O constant rest (o.mono fun k member => by simp [PredList.reads, member])
            (n.mono fun k member => by simp [PredList.reads, member])]
  theorem evalWithAny_frame (O : Oracle) (constant : ∀ vk old new old' new', O vk old new = O vk old' new') :
      ∀ (ps : PredList) {old new old' new' : State},
        State.AgreeOn ps.reads old old' → State.AgreeOn ps.reads new new' →
        evalWithAny O ps old new = evalWithAny O ps old' new'
    | .nil, _, _, _, _, _, _ => rfl
    | .cons q rest, _, _, _, _, o, n => by
        simp only [evalWithAny,
          evalWith_frame O constant q (o.mono fun k member => by simp [PredList.reads, member])
            (n.mono fun k member => by simp [PredList.reads, member]),
          evalWithAny_frame O constant rest (o.mono fun k member => by simp [PredList.reads, member])
            (n.mono fun k member => by simp [PredList.reads, member])]
end

/-- **The verdict on the law's slots is the verdict** (`eval`, the policy path's evaluator):
a projection may build only `p.reads`. -/
theorem eval_restrict (p : Pred) (old new : State) :
    eval p (old.restrict p.reads) (new.restrict p.reads) = eval p old new :=
  evalWith_frame failClosed (fun _ _ _ _ _ => rfl) p
    (State.agreeOn_restrict p.reads old) (State.agreeOn_restrict p.reads new)

/-- Any superset of the reads will do: a projection may build a coarser demanded set. -/
theorem eval_restrict_of_sub (p : Pred) {keys : List Slot} (sub : ∀ k ∈ p.reads, k ∈ keys)
    (old new : State) :
    eval p (old.restrict keys) (new.restrict keys) = eval p old new :=
  evalWith_frame failClosed (fun _ _ _ _ _ => rfl) p
    ((State.agreeOn_restrict keys old).mono sub) ((State.agreeOn_restrict keys new).mono sub)

/-- **Teeth**: restricting to fewer names than the law reads changes its verdict, so the
read set is load-bearing, not a vacuous bound. -/
theorem restrict_needs_reads :
    eval (.eq "a" 1) (State.restrict [] ⟨[("a", 1)]⟩) (State.restrict [] ⟨[("a", 1)]⟩) = false ∧
      eval (.eq "a" 1) ⟨[("a", 1)]⟩ ⟨[("a", 1)]⟩ = true := by
  decide

end Minidregg.Pred
