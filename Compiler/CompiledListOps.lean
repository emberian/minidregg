/-
# Compiler.CompiledListOps -- list decisions the Host runs per turn, at compiled speed

Compiled `DecidableEq (List α)` walks both lists element by element, calling the
element decision through a closure per element. The Host compares whole cell
images this way on every session advance (`cellsLawfulFrom`, the directory's
`decodeRowFrom`, `loadDeploymentFrom`), and an unchanged cell's bytes in the
next image are the very same object as in the prior one. `listDecEq` answers
`true` at once for one object (`withPtrEqDecEq`) and otherwise runs the
ordinary decision. Decidability is a subsingleton, so the `@[csimp]` swap is an
equality of instances; no statement sees it.

Also: `nodupNat` (a hashed one-pass `List.Nodup` decision on identifiers,
`nodupNat_iff`), `rowTable` (an identifier table that answers `List.lookup`,
`rowTable_get?`) and `usedSet` (a hashed dedup that is `List.toFinset`,
`usedSet_eq`): the quadratic list forms stay the statements, these run.
-/

module

public import Init.Util
public import Std.Data.HashSet
public import Std.Data.HashMap
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace Minidregg.Compiler.CompiledListOps

set_option autoImplicit false

universe u

/-- `DecidableEq (List α)`, object identity first. -/
def listDecEq {α : Type u} [DecidableEq α] (left right : List α) : Decidable (left = right) :=
  withPtrEqDecEq left right (fun _ => instDecidableEqList left right)

@[csimp] theorem instDecidableEqList_eq_listDecEq : @instDecidableEqList = @listDecEq := by
  funext α _ left right
  exact Subsingleton.elim _ _

def nodupGo : List Nat → Std.HashSet Nat → Bool
  | [], _ => true
  | x :: xs, seen => if seen.contains x then false else nodupGo xs (seen.insert x)

theorem nodupGo_iff : ∀ (l : List Nat) (seen : Std.HashSet Nat),
    nodupGo l seen = true ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ seen
  | [], _ => by simp [nodupGo]
  | x :: xs, seen => by
      unfold nodupGo
      by_cases hx : seen.contains x
      · have : x ∈ seen := Std.HashSet.contains_iff_mem.mp hx
        simp only [hx, if_true, Bool.false_eq_true, false_iff, not_and, not_forall]
        intro _
        exact ⟨x, by simp, by simpa using this⟩
      · simp only [hx, Bool.false_eq_true, if_false, nodupGo_iff xs (seen.insert x), List.nodup_cons,
          List.mem_cons, forall_eq_or_imp, Std.HashSet.mem_insert]
        have notIn : x ∉ seen := fun h => hx (Std.HashSet.contains_iff_mem.mpr h)
        constructor
        · rintro ⟨nd, fresh⟩
          refine ⟨⟨fun mem => (fresh x mem) (Or.inl (by simp)), nd⟩, notIn, fun y mem inSeen => fresh y mem (Or.inr inSeen)⟩
        · rintro ⟨⟨notMem, nd⟩, -, fresh⟩
          refine ⟨nd, fun y mem h => ?_⟩
          rcases h with same | inSeen
          · have : x = y := by simpa using same
            subst this; exact notMem mem
          · exact fresh y mem inSeen

def nodupNat (l : List Nat) : Bool := nodupGo l ∅

theorem nodupNat_iff (l : List Nat) : nodupNat l = true ↔ l.Nodup := by
  rw [nodupNat, nodupGo_iff]; simp

def rowTable {β : Type} (rows : List (Nat × β)) : Std.HashMap Nat β :=
  rows.foldr (fun row table => table.insert row.1 row.2) ∅

theorem rowTable_get? {β : Type} : ∀ (rows : List (Nat × β)) (id : Nat), (rowTable rows)[id]? = rows.lookup id
  | [], id => by simp [rowTable]
  | (key, value) :: rest, id => by
      have ih := rowTable_get? rest id
      simp only [rowTable, List.foldr_cons] at ih ⊢
      rw [Std.HashMap.getElem?_insert, ih, List.lookup_cons]
      by_cases h : key = id
      · subst h; simp
      · have : (id == key) = false := by simp [Ne.symm h]
        simp [h, this]

def usedSet (keys : List Nat) : Finset Nat :=
  let seen : Std.HashSet Nat := keys.foldl (fun seen key => seen.insert key) ∅
  ⟨(seen.toList : Multiset Nat), Multiset.coe_nodup.mpr (seen.distinct_toList.imp fun h => by simpa using h)⟩

theorem mem_usedSet (keys : List Nat) (key : Nat) : key ∈ usedSet keys ↔ key ∈ keys := by
  suffices h : ∀ (seen : Std.HashSet Nat), key ∈ keys.foldl (fun seen key => seen.insert key) seen ↔ key ∈ keys ∨ key ∈ seen by
    simp only [usedSet, Finset.mem_mk, Multiset.mem_coe, Std.HashSet.mem_toList]
    simpa using h ∅
  induction keys with
  | nil => intro seen; simp
  | cons head rest ih =>
      intro seen
      rw [List.foldl_cons, ih, Std.HashSet.mem_insert]
      simp only [List.mem_cons, beq_iff_eq]
      constructor
      · rintro (h | h | h) <;> [exact Or.inl (Or.inr h); exact Or.inl (Or.inl h.symm); exact Or.inr h]
      · rintro ((h | h) | h) <;> [exact Or.inr (Or.inl h.symm); exact Or.inl h; exact Or.inr (Or.inr h)]

theorem usedSet_eq (keys : List Nat) : usedSet keys = keys.toFinset := by
  ext key; rw [mem_usedSet, List.mem_toFinset]

end Minidregg.Compiler.CompiledListOps
