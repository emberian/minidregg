/- Persistent append and indexed selection; the chronological list is its specification. -/
module

public import Std.Data.ExtTreeMap.Lemmas
public import Theory.AssertAxioms

@[expose] public section
namespace Minidregg.Kernel
set_option autoImplicit false
universe u

/-- A persistent sequence. Appending shares the old list and all but one tree
path; it never copies a shared flat array. The list projection is for proofs
and explicitly requested full exports. Operational selection uses `get?`. -/
structure PersistentHistory (α : Type u) where
  -- Not private: the exactness fields carry the guarantee, so any construction must prove them
  -- (TokenCensus: no guarantee rests on who builds it).
  newest : List α
  size : Nat
  sizeExact : newest.length = size
  index : Std.ExtTreeMap Nat α compare
  indexExact : ∀ i : Nat, index[i]? = newest.reverse[i]?

namespace PersistentHistory
variable {α : Type u}

def toList (history : PersistentHistory α) : List α := history.newest.reverse

def get? (history : PersistentHistory α) (i : Nat) : Option α := history.index[i]?

@[simp] theorem length_toList (history : PersistentHistory α) :
    history.toList.length = history.size := by
  simpa [toList] using history.sizeExact

theorem get?_eq (history : PersistentHistory α) (i : Nat) :
    history.get? i = history.toList[i]? := history.indexExact i

def empty : PersistentHistory α := ⟨[], 0, rfl, ∅, by simp⟩

def push (history : PersistentHistory α) (value : α) : PersistentHistory α :=
  ⟨value :: history.newest, history.size + 1, by simp [history.sizeExact],
    history.index.insert history.size value, by
      intro i
      rw [Std.ExtTreeMap.getElem?_insert, List.reverse_cons, List.getElem?_append]
      simp only [List.length_reverse, history.sizeExact, Nat.compare_eq_eq]
      by_cases same : history.size = i
      · subst i; simp
      · by_cases before : i < history.size
        · simp [same, before, history.indexExact]
        · have beyond : history.size < i := by omega
          have absent : history.newest.reverse[i]? = none :=
            List.getElem?_eq_none_iff.mpr (by simp only [List.length_reverse, history.sizeExact]; omega)
          have diff : i - history.size ≠ 0 := by omega
          simp [same, before, history.indexExact, absent, diff]⟩

@[simp] theorem toList_empty : (empty : PersistentHistory α).toList = [] := rfl

@[simp] theorem size_push (history : PersistentHistory α) (value : α) :
    (history.push value).size = history.size + 1 := rfl

@[simp] theorem toList_push (history : PersistentHistory α) (value : α) :
    (history.push value).toList = history.toList ++ [value] := by
  simp only [toList, push, List.reverse_cons]

def append (history : PersistentHistory α) (values : List α) : PersistentHistory α :=
  values.foldl push history

@[simp] theorem toList_append (history : PersistentHistory α) (values : List α) :
    (history.append values).toList = history.toList ++ values := by
  induction values generalizing history with
  | nil => simp [append]
  | cons value values ih =>
      simp only [append, List.foldl_cons] at *
      rw [ih, toList_push]
      simp only [List.append_assoc, List.singleton_append]

def ofList (values : List α) : PersistentHistory α := empty.append values

@[simp] theorem toList_ofList (values : List α) : (ofList values).toList = values := by
  simp [ofList]

theorem get?_push_last (history : PersistentHistory α) (value : α) :
    (history.push value).get? history.size = some value := by
  rw [get?_eq, toList_push, List.getElem?_append_right (by simp)]
  simp

theorem get?_push_before (history : PersistentHistory α) (value : α) (i : Nat)
    (before : i < history.size) :
    (history.push value).get? i = history.get? i := by
  rw [get?_eq, toList_push, List.getElem?_append_left (by simpa using before), get?_eq]

#assert_axioms get?_eq toList_push toList_append toList_ofList get?_push_last get?_push_before
end PersistentHistory
end Minidregg.Kernel
