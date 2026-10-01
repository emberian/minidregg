/-
K-DOC-HISTORY: the difference between two renderings of one page.

A page is rendered as its lines in the kernel's document order: `lines store
document` pairs each element of `ContentResource.documentOrder` (the pre-order
walk of the element tree, `view-document`'s `order`) with what stands there — an
atom record, a transclusion's embed, a section.  `diff left right` names, by key,
every row added, removed or changed between the two renderings, and every row
whose predecessor among the rows on both sides changed (`moved`), and nothing
else: the four `_iff` theorems say each change is exactly what a reader
comparing the two `doc show` tables row by row would find, so `doc diff H1 H2`
agrees with `doc show --at H1` and `doc show --at H2` by construction rather
than by a second renderer.
-/
import Kernel.ContentElementTree

namespace Minidregg.Kernel.DocumentHistory

open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.ContentResource

/-- One row-level difference, keyed. A `moved` row names its predecessor among
the rows present on both sides, before and after. -/
inductive Change (κ ν : Type) where
  | added (key : κ) (after : ν)
  | removed (key : κ) (before : ν)
  | changed (key : κ) (before after : ν)
  | moved (key : κ) (before after : Option κ)
  deriving DecidableEq, Repr

variable {κ ν : Type} [DecidableEq κ] [DecidableEq ν]

/-- The keys of `rows` that `other` also has, in `rows`' order. -/
def common (rows other : List (κ × ν)) : List κ :=
  (rows.map Prod.fst).filter fun key => (other.lookup key).isSome

/-- The key immediately before `key` in `keys` (none for the first, or absent). -/
def predecessor (keys : List κ) (key : κ) : Option κ :=
  ((keys.zip keys.tail).find? fun pair => pair.2 = key).map Prod.fst

/-- Rows on both sides whose predecessor among the rows on both sides changed:
an insertion or a removal moves nothing; a reorder moves the rows at its seams. -/
def moves (left right : List (κ × ν)) : List (Change κ ν) :=
  (common left right).filterMap fun key =>
    if predecessor (common left right) key = predecessor (common right left) key then none
    else some (.moved key (predecessor (common left right) key) (predecessor (common right left) key))

/-- Rows of `left` gone or changed in `right` (in `left`'s order), then rows of
`right` absent from `left` (in `right`'s order), then the moved rows. -/
def diff (left right : List (κ × ν)) : List (Change κ ν) :=
  left.filterMap (fun row =>
      match right.lookup row.1 with
      | none => some (.removed row.1 row.2)
      | some after => if row.2 = after then none else some (.changed row.1 row.2 after)) ++
    right.filterMap (fun row =>
      match left.lookup row.1 with
      | none => some (.added row.1 row.2)
      | some _ => none) ++
    moves left right

omit [DecidableEq ν] in
private theorem not_in_moves {left right : List (κ × ν)} {change : Change κ ν}
    (notMove : ∀ key before after, change ≠ .moved key before after) :
    change ∉ moves left right := by
  simp only [moves, List.mem_filterMap, not_exists, not_and]
  intro key _ made
  split at made
  · cases made
  · cases made
    exact notMove _ _ _ rfl

theorem added_iff {left right : List (κ × ν)} {key : κ} {after : ν} :
    Change.added key after ∈ diff left right ↔ (key, after) ∈ right ∧ left.lookup key = none := by
  have noMove : Change.added key after ∉ moves left right :=
    not_in_moves (by intro _ _ _ h; cases h)
  simp only [diff, List.mem_append, List.mem_filterMap]
  constructor
  · rintro ((⟨⟨k, v⟩, _, made⟩ | ⟨⟨k, v⟩, member, made⟩) | inMoves)
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
    · exact absurd inMoves noMove
  · rintro ⟨member, absent⟩
    exact Or.inl (Or.inr ⟨(key, after), member, by simp [absent]⟩)

theorem removed_iff {left right : List (κ × ν)} {key : κ} {before : ν} :
    Change.removed key before ∈ diff left right ↔ (key, before) ∈ left ∧ right.lookup key = none := by
  have noMove : Change.removed key before ∉ moves left right :=
    not_in_moves (by intro _ _ _ h; cases h)
  simp only [diff, List.mem_append, List.mem_filterMap]
  constructor
  · rintro ((⟨⟨k, v⟩, member, made⟩ | ⟨⟨k, v⟩, _, made⟩) | inMoves)
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
    · exact absurd inMoves noMove
  · rintro ⟨member, absent⟩
    exact Or.inl (Or.inl ⟨(key, before), member, by simp [absent]⟩)

theorem changed_iff {left right : List (κ × ν)} {key : κ} {before after : ν} :
    Change.changed key before after ∈ diff left right ↔
      (key, before) ∈ left ∧ right.lookup key = some after ∧ before ≠ after := by
  have noMove : Change.changed key before after ∉ moves left right :=
    not_in_moves (by intro _ _ _ h; cases h)
  simp only [diff, List.mem_append, List.mem_filterMap]
  constructor
  · rintro ((⟨⟨k, v⟩, member, made⟩ | ⟨⟨k, v⟩, _, made⟩) | inMoves)
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
    · exact absurd inMoves noMove
  · rintro ⟨member, found, differ⟩
    exact Or.inl (Or.inl ⟨(key, before), member, by simp [found, differ]⟩)

/-- A row is reported moved exactly when it is on both sides and its
predecessor among the rows on both sides differs. -/
theorem moved_iff {left right : List (κ × ν)} {key : κ} {before after : Option κ} :
    Change.moved key before after ∈ diff left right ↔
      key ∈ common left right ∧ predecessor (common left right) key = before ∧
        predecessor (common right left) key = after ∧ before ≠ after := by
  simp only [diff, List.mem_append, List.mem_filterMap, moves]
  constructor
  · rintro ((⟨⟨k, v⟩, _, made⟩ | ⟨⟨k, v⟩, _, made⟩) | ⟨k, member, made⟩)
    · simp only at made
      split at made
      · cases made
      · split at made <;> cases made
    · simp only at made
      split at made
      · cases made
      · cases made
    · split at made
      · cases made
      · rename_i differ
        cases made
        exact ⟨member, rfl, rfl, differ⟩
  · rintro ⟨member, rfl, rfl, differ⟩
    exact Or.inr ⟨key, member, by simp [differ]⟩

/-- Refuting pole: a row whose value is the same on both sides is never reported changed. -/
theorem unchanged_not_reported {left right : List (κ × ν)} {key : κ} {value : ν} :
    Change.changed key value value ∉ diff left right := by
  rw [changed_iff]
  exact fun ⟨_, _, differ⟩ => differ rfl

/-- Refuting pole: when the rows on both sides stand in the same order, nothing moved. -/
theorem same_order_no_moves {left right : List (κ × ν)} (same : common left right = common right left)
    {key : κ} {before after : Option κ} : Change.moved key before after ∉ diff left right := by
  rw [moved_iff, same]
  exact fun ⟨_, first, second, differ⟩ => differ (first.symm.trans second)

/-- Satisfiable pole: one edited row between two one-row pages is exactly one change. -/
theorem one_edit_one_change : diff [(1, 10)] [(1, 11)] = [Change.changed 1 10 11] := by decide

/-- Satisfiable pole: an appended row is exactly one addition. -/
theorem one_append_one_addition : diff [(1, 10)] [(1, 10), (2, 20)] = [Change.added 2 20] := by decide

/-- Satisfiable pole: a row inserted between two others is one addition, not a move. -/
theorem insert_between_is_no_move :
    diff [(1, 10), (2, 20)] [(1, 10), (3, 30), (2, 20)] = [Change.added 3 30] := by decide

/-- Satisfiable pole: swapping two rows reports both, each with its new predecessor. -/
theorem swap_is_two_moves :
    diff [(1, 10), (2, 20)] [(2, 20), (1, 10)] =
      [Change.moved 1 none (some 2), Change.moved 2 (some 1) none] := by decide

/-! ## A page's lines are the kernel's document order -/

/-- What stands at one element of the document order. A section carries the
revision of its children's positions, so a reorder inside it is a change of it. -/
inductive Line where
  | atom (atom : AtomId) (record : Option AtomRecord)
  | embed (transclusion : TransclusionId)
  | section (revision : OperationId)
  | runs
  | opaque
  | missing
  deriving DecidableEq, Repr

def lineOf (store : ContentStore) (element : ElementId) : Line :=
  match elementAt store element with
  | none => .missing
  | some record =>
      match record.body with
      | .atom atom => .atom atom (lookup store .atoms atom)
      | .embed transclusion => .embed transclusion
      | .container _ => .section record.revision
      | .runs _ => .runs
      | .opaque _ _ => .opaque

/-- The page's lines: `view-document`'s order, each element with its line. -/
def lines (store : ContentStore) (document : DocumentId) : List (ElementId × Line) :=
  (documentOrder store document).map fun element => (element, lineOf store element)

/-- The keys of a page's lines are exactly the document order. -/
theorem lines_keys (store : ContentStore) (document : DocumentId) :
    (lines store document).map Prod.fst = documentOrder store document := by
  simp [lines, List.map_map, Function.comp_def]

/-- On an admitted tree each line's key appears once (`order_total`). -/
theorem lines_nodup {store : ContentStore} {document : DocumentId} {root : ElementId}
    (tree : DocumentTree store document) (rooted : rootOf store document = some root) :
    ((lines store document).map Prod.fst).Nodup := by
  rw [lines_keys]
  exact (order_total tree rooted).1

private theorem lookup_graph (order : List ElementId) (f : ElementId → Line) (key : ElementId) :
    (order.map fun element => (element, f element)).lookup key =
      if key ∈ order then some (f key) else none := by
  induction order with
  | nil => simp
  | cons head rest induction =>
      by_cases same : key = head
      · subst same; simp
      · have differ : (key == head) = false := by simpa using same
        simp [List.lookup, differ, induction, same]

theorem mem_lines {store : ContentStore} {document : DocumentId} {element : ElementId} {line : Line} :
    (element, line) ∈ lines store document ↔
      element ∈ documentOrder store document ∧ line = lineOf store element := by
  simp only [lines, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨e, member, rfl, rfl⟩; exact ⟨member, rfl⟩
  · rintro ⟨member, rfl⟩; exact ⟨element, member, rfl, rfl⟩

theorem lookup_lines (store : ContentStore) (document : DocumentId) (element : ElementId) :
    (lines store document).lookup element =
      if element ∈ documentOrder store document then some (lineOf store element) else none :=
  lookup_graph _ _ _

/-- `added_iff` over two pages: an element added between `doc show --at H1`
and `--at H2` is in the order at H2, not in the order at H1, with its line. -/
theorem line_added_iff {before after : ContentStore} {document : DocumentId} {element : ElementId}
    {line : Line} :
    Change.added element line ∈ diff (lines before document) (lines after document) ↔
      element ∈ documentOrder after document ∧ line = lineOf after element ∧
        element ∉ documentOrder before document := by
  rw [added_iff, mem_lines, lookup_lines]
  by_cases present : element ∈ documentOrder before document <;> simp [present]

/-- `removed_iff` over two pages. -/
theorem line_removed_iff {before after : ContentStore} {document : DocumentId} {element : ElementId}
    {line : Line} :
    Change.removed element line ∈ diff (lines before document) (lines after document) ↔
      element ∈ documentOrder before document ∧ line = lineOf before element ∧
        element ∉ documentOrder after document := by
  rw [removed_iff, mem_lines, lookup_lines]
  by_cases present : element ∈ documentOrder after document <;> simp [present]

/-- `changed_iff` over two pages: an element in both orders whose line differs. -/
theorem line_changed_iff {before after : ContentStore} {document : DocumentId} {element : ElementId}
    {old new : Line} :
    Change.changed element old new ∈ diff (lines before document) (lines after document) ↔
      element ∈ documentOrder before document ∧ old = lineOf before element ∧
        element ∈ documentOrder after document ∧ new = lineOf after element ∧ old ≠ new := by
  rw [changed_iff, mem_lines, lookup_lines]
  by_cases present : element ∈ documentOrder after document
  · rw [if_pos present, Option.some.injEq]
    constructor
    · rintro ⟨⟨member, rfl⟩, rfl, differ⟩; exact ⟨member, rfl, present, rfl, differ⟩
    · rintro ⟨member, rfl, _, rfl, differ⟩; exact ⟨⟨member, rfl⟩, rfl, differ⟩
  · simp [present]

/-- info: 'Minidregg.Kernel.DocumentHistory.added_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms added_iff
/-- info: 'Minidregg.Kernel.DocumentHistory.removed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms removed_iff
/-- info: 'Minidregg.Kernel.DocumentHistory.changed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms changed_iff
/-- info: 'Minidregg.Kernel.DocumentHistory.moved_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms moved_iff
/-- info: 'Minidregg.Kernel.DocumentHistory.unchanged_not_reported' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unchanged_not_reported
/-- info: 'Minidregg.Kernel.DocumentHistory.same_order_no_moves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms same_order_no_moves
/-- info: 'Minidregg.Kernel.DocumentHistory.one_edit_one_change' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms one_edit_one_change
/-- info: 'Minidregg.Kernel.DocumentHistory.one_append_one_addition' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms one_append_one_addition
/-- info: 'Minidregg.Kernel.DocumentHistory.insert_between_is_no_move' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms insert_between_is_no_move
/-- info: 'Minidregg.Kernel.DocumentHistory.swap_is_two_moves' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms swap_is_two_moves
/-- info: 'Minidregg.Kernel.DocumentHistory.lines_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lines_keys
/-- info: 'Minidregg.Kernel.DocumentHistory.lines_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lines_nodup
/-- info: 'Minidregg.Kernel.DocumentHistory.line_added_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms line_added_iff
/-- info: 'Minidregg.Kernel.DocumentHistory.line_removed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms line_removed_iff
/-- info: 'Minidregg.Kernel.DocumentHistory.line_changed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms line_changed_iff

end Minidregg.Kernel.DocumentHistory
