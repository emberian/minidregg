/-
# Both poles of `View.Forest`, named

`View.Forest` (Kernel/ContentElementTree.lean) is the premise of thirteen
theorems (`walk_nodup`, `below_in_walk`, `splice_places`, the `Forest.attach` /
`reorder` / `detach` / `insertTop` steps, …).  `tree_acyclic` derives it only
under the hypothesis that a state was admitted from genesis, so on its own the
tree never exhibited a view the premise accepts or one it refuses: the
hypothesis ledger (scripts/HypothesisLedger.lean) read it TOOTHLESS.

This file names both poles over concrete views:

* `rootLeaf_forest` — a document root listing one child that names the root as
  its parent is a forest (every clause, including the strict rank, holds);
* `selfParent_not_forest` — an element that is its own parent and lists itself
  is refuted by the rank clause alone (no rank is below itself);
* `unlisted_not_forest` — a child naming a parent that does not list it is
  refuted by the parent/children agreement clause, with no cycle present.
-/
import Kernel.ContentElementTree

namespace Minidregg.Kernel.ContentResource.ForestInstances

open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.ContentResource

set_option autoImplicit false

def ident {domain : IdDomain} (n : Nat) : Identifier .v1 domain := ⟨⟨n⟩⟩

def author : PrincipalRef := ⟨⟨0⟩, .object, ⟨0⟩⟩

def record (parent : Option ElementId) (body : ElementBody) : ElementRecord :=
  ⟨ident 0, parent, body, author, ident 0, ident 0, none⟩

def rootId : ElementId := ident 1
def leafId : ElementId := ident 2

theorem leafId_ne_rootId : leafId ≠ rootId := by decide

/-- A root container listing one leaf; the leaf names the root as its parent. -/
def rootLeaf : View := fun element =>
  if element = rootId then some (record none (.container [leafId]))
  else if element = leafId then some (record (some rootId) (.container []))
  else none

theorem rootLeaf_parent (element : ElementId) :
    rootLeaf.parent element = if element = leafId then some rootId else none := by
  by_cases root : element = rootId
  · subst root
    simp [View.parent, rootLeaf, record, leafId_ne_rootId.symm]
  · by_cases leaf : element = leafId
    · subst leaf
      simp [View.parent, rootLeaf, record, leafId_ne_rootId]
    · simp [View.parent, rootLeaf, root, leaf]

theorem rootLeaf_children (element : ElementId) :
    rootLeaf.children element = if element = rootId then [leafId] else [] := by
  by_cases root : element = rootId
  · subst root
    simp [View.children, rootLeaf, record, bodyChildren]
  · by_cases leaf : element = leafId
    · subst leaf
      simp [View.children, rootLeaf, record, bodyChildren, leafId_ne_rootId]
    · simp [View.children, rootLeaf, root, leaf]

/-- The satisfying pole: a two-element document tree is a forest. -/
theorem rootLeaf_forest : View.Forest rootLeaf where
  listed := by
    intro child parent parentIs
    rw [rootLeaf_parent] at parentIs
    by_cases leaf : child = leafId
    · simp only [leaf, if_true, Option.some.injEq] at parentIs
      subst leaf parentIs
      simp [rootLeaf_children]
    · simp [leaf] at parentIs
  parented := by
    intro parent child listed
    rw [rootLeaf_children] at listed
    by_cases root : parent = rootId
    · simp only [root, if_true, List.mem_singleton] at listed
      subst root listed
      simp [rootLeaf_parent]
    · simp [root] at listed
  nodup := by
    intro element
    rw [rootLeaf_children]
    split <;> simp
  ranked := by
    refine ⟨fun element => if element = leafId then 1 else 0, ?_⟩
    intro child parent parentIs
    rw [rootLeaf_parent] at parentIs
    by_cases leaf : child = leafId
    · simp only [leaf, if_true, Option.some.injEq] at parentIs
      subst leaf parentIs
      simp [leafId_ne_rootId.symm]
    · simp [leaf] at parentIs

/-- An element that is its own parent and lists itself among its children. -/
def selfParent : View := fun element =>
  if element = rootId then some (record (some rootId) (.container [rootId])) else none

/-- The refuting pole, by the rank clause: a self-parent has no strict rank. -/
theorem selfParent_not_forest : ¬ View.Forest selfParent := by
  intro forest
  obtain ⟨rank, ranked⟩ := forest.ranked
  have parentIs : selfParent.parent rootId = some rootId := by
    simp [View.parent, selfParent, record]
  exact Nat.lt_irrefl _ (ranked rootId rootId parentIs)

/-- A leaf names the root as its parent, but the root lists no child. -/
def unlisted : View := fun element =>
  if element = rootId then some (record none (.container []))
  else if element = leafId then some (record (some rootId) (.container []))
  else none

/-- The refuting pole, by the agreement clause: the view is acyclic (rank holds)
but the parent's children do not list the child. -/
theorem unlisted_not_forest : ¬ View.Forest unlisted := by
  intro forest
  have parentIs : unlisted.parent leafId = some rootId := by
    simp [View.parent, unlisted, record, leafId_ne_rootId]
  have listed := forest.listed leafId rootId parentIs
  simp [View.children, unlisted, record, bodyChildren] at listed

#assert_axioms leafId_ne_rootId
#assert_axioms rootLeaf_forest
#assert_axioms selfParent_not_forest
#assert_axioms unlisted_not_forest

end Minidregg.Kernel.ContentResource.ForestInstances
