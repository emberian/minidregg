/-
K-DOC-HISTORY: the atom-level difference between two renderings of one page.

A page is rendered as its atom rows in store order (`doc show`'s numbered
lines). `diff left right` names, by key, every row added, removed or changed
between the two renderings, and nothing else: the three `_iff` theorems say
that each change is exactly what a reader comparing the two `doc show` tables
row by row would find, so `doc diff H1 H2` agrees with `doc show --at H1` and
`doc show --at H2` by construction rather than by a second renderer.
-/

namespace Minidregg.Kernel.DocumentHistory

/-- One row-level difference, keyed. -/
inductive Change (κ ν : Type) where
  | added (key : κ) (after : ν)
  | removed (key : κ) (before : ν)
  | changed (key : κ) (before after : ν)
  deriving DecidableEq, Repr

variable {κ ν : Type} [DecidableEq κ] [DecidableEq ν]

/-- Rows of `left` gone or changed in `right` (in `left`'s order), then rows of
`right` absent from `left` (in `right`'s order). -/
def diff (left right : List (κ × ν)) : List (Change κ ν) :=
  left.filterMap (fun row =>
      match right.lookup row.1 with
      | none => some (.removed row.1 row.2)
      | some after => if row.2 = after then none else some (.changed row.1 row.2 after)) ++
    right.filterMap (fun row =>
      match left.lookup row.1 with
      | none => some (.added row.1 row.2)
      | some _ => none)

theorem added_iff {left right : List (κ × ν)} {key : κ} {after : ν} :
    Change.added key after ∈ diff left right ↔ (key, after) ∈ right ∧ left.lookup key = none := by
  simp only [diff, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (⟨⟨k, v⟩, _, made⟩ | ⟨⟨k, v⟩, member, made⟩)
    · simp only at made
      split at made
      · cases made
      · split at made <;> cases made
    · simp only at made
      split at made
      · rename_i absent
        cases made
        exact ⟨member, absent⟩
      · cases made
  · rintro ⟨member, absent⟩
    exact Or.inr ⟨(key, after), member, by simp [absent]⟩

theorem removed_iff {left right : List (κ × ν)} {key : κ} {before : ν} :
    Change.removed key before ∈ diff left right ↔ (key, before) ∈ left ∧ right.lookup key = none := by
  simp only [diff, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (⟨⟨k, v⟩, member, made⟩ | ⟨⟨k, v⟩, _, made⟩)
    · simp only at made
      split at made
      · rename_i absent
        cases made
        exact ⟨member, absent⟩
      · split at made <;> cases made
    · simp only at made
      split at made
      · cases made
      · cases made
  · rintro ⟨member, absent⟩
    exact Or.inl ⟨(key, before), member, by simp [absent]⟩

theorem changed_iff {left right : List (κ × ν)} {key : κ} {before after : ν} :
    Change.changed key before after ∈ diff left right ↔
      (key, before) ∈ left ∧ right.lookup key = some after ∧ before ≠ after := by
  simp only [diff, List.mem_append, List.mem_filterMap]
  constructor
  · rintro (⟨⟨k, v⟩, member, made⟩ | ⟨⟨k, v⟩, _, made⟩)
    · simp only at made
      split at made
      · cases made
      · rename_i found
        split at made
        · cases made
        · rename_i differ
          cases made
          exact ⟨member, found, differ⟩
    · simp only at made
      split at made
      · cases made
      · cases made
  · rintro ⟨member, found, differ⟩
    exact Or.inl ⟨(key, before), member, by simp [found, differ]⟩

/-- Refuting pole: a row whose value is the same on both sides is never reported. -/
theorem unchanged_not_reported {left right : List (κ × ν)} {key : κ} {value : ν} :
    Change.changed key value value ∉ diff left right := by
  rw [changed_iff]
  exact fun ⟨_, _, differ⟩ => differ rfl

/-- Satisfiable pole: one edited row between two one-row pages is exactly one change. -/
theorem one_edit_one_change : diff [(1, 10)] [(1, 11)] = [Change.changed 1 10 11] := by decide

/-- Satisfiable pole: an appended row is exactly one addition. -/
theorem one_append_one_addition : diff [(1, 10)] [(1, 10), (2, 20)] = [Change.added 2 20] := by decide

/-- info: 'Minidregg.Kernel.DocumentHistory.added_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms added_iff
/-- info: 'Minidregg.Kernel.DocumentHistory.removed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms removed_iff
/-- info: 'Minidregg.Kernel.DocumentHistory.changed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_iff
/-- info: 'Minidregg.Kernel.DocumentHistory.unchanged_not_reported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unchanged_not_reported
/-- info: 'Minidregg.Kernel.DocumentHistory.one_edit_one_change' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms one_edit_one_change
/-- info: 'Minidregg.Kernel.DocumentHistory.one_append_one_addition' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms one_append_one_addition

end Minidregg.Kernel.DocumentHistory
