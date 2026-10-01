/-
# The element tree of a content cell: one forest, one document root, an explicit order

`ContentResource` gives a document an element tree: `ElementRecord.parent`,
and `ElementBody.container`'s ordered `children` (the Theory's one ordering
representation).  `createDocument` makes the root, an empty container;
`createAtom` and `transclude` append their leaf (`atom` / `embed`, carrying the
record's own identifier) to the root, `createContainer` an empty section; `editElement` splices a detached element
into a container, moves a child within one, or removes (detaches) one, each
checked against the revision of the container its author read.  Document order
is `documentOrder`, the pre-order walk below the root.

What is proved here, over the kernel's own `step` / `run`:

* `tree_acyclic` — every state admitted from genesis is a forest (parent and
  children agree, no element is its own proper ancestor) whose document root
  has no parent;
* `order_total` — the order lists every element placed under the root exactly
  once, and nothing else;
* `splice_places`, `move_preserves_set`, `remove_detaches` — what each edit
  does to one container, and that a removed element (and so its atoms) leaves
  the order while its records stay;
* `transclusion_at_line` — a transclusion moved to position `i` of a flat
  document is line `i` of the order;
* `editElement_requires_grant` — an element edit is a write of the `body`
  field and of nothing in `annotations`;
* `cycle_refused`, `stale_element_refused` — refused by name, with the
  admitted poles `splice_admitted_shape` and `move_admitted`.
-/
import Kernel.ContentResource

namespace Minidregg.Kernel.ContentResource

open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations

set_option autoImplicit false

/-! ## The tree as a view of the elements namespace -/

/-- The elements namespace of a store, as a function. -/
abbrev View := ElementId → Option ElementRecord

namespace View

def parent (view : View) (element : ElementId) : Option ElementId :=
  (view element).bind ElementRecord.parent

def children (view : View) (element : ElementId) : List ElementId :=
  match view element with
  | some record => bodyChildren record.body
  | none => []

/-- `ancestor` is `element` itself or one of its ancestors. -/
inductive Below (view : View) : ElementId → ElementId → Prop
  | refl (element : ElementId) : Below view element element
  | up {element parent ancestor : ElementId} (parentIs : view.parent element = some parent)
      (rest : Below view parent ancestor) : Below view element ancestor

/-- A forest: parent and children agree, no container lists a child twice, and
some rank strictly increases from parent to child, so no element is its own
proper ancestor. -/
structure Forest (view : View) : Prop where
  listed : ∀ child parent, view.parent child = some parent → child ∈ view.children parent
  parented : ∀ parent child, child ∈ view.children parent → view.parent child = some parent
  nodup : ∀ element, (view.children element).Nodup
  ranked : ∃ rank : ElementId → Nat,
    ∀ child parent, view.parent child = some parent → rank parent < rank child

variable {view : View}

theorem Below.cases' {element ancestor : ElementId} (below : view.Below element ancestor) :
    element = ancestor ∨ ∃ parent, view.parent element = some parent ∧ view.Below parent ancestor := by
  cases below with
  | refl => exact Or.inl rfl
  | up parentIs rest => exact Or.inr ⟨_, parentIs, rest⟩

theorem Below.trans {first second third : ElementId} (left : view.Below first second)
    (right : view.Below second third) : view.Below first third := by
  induction left with
  | refl => exact right
  | up parentIs _ induction => exact .up parentIs (induction right)

theorem Below.rank_le {rank : ElementId → Nat}
    (ranked : ∀ child parent, view.parent child = some parent → rank parent < rank child)
    {element ancestor : ElementId} (below : view.Below element ancestor) :
    rank ancestor ≤ rank element := by
  induction below with
  | refl => exact Nat.le_refl _
  | up parentIs _ induction => exact Nat.le_trans induction (Nat.le_of_lt (ranked _ _ parentIs))

/-- Two ancestors of one element lie on one chain. -/
theorem Below.linear {element first second : ElementId} (left : view.Below element first)
    (right : view.Below element second) : view.Below first second ∨ view.Below second first := by
  induction left generalizing second with
  | refl => exact Or.inl right
  | up parentIs rest induction =>
      rcases right.cases' with same | ⟨other, otherIs, otherRest⟩
      · subst same
        exact Or.inr (.up parentIs rest)
      · rw [parentIs] at otherIs
        obtain rfl := Option.some.inj otherIs
        exact induction otherRest

theorem parent_of_absent {element : ElementId} (absent : view element = none) :
    view.parent element = none := by
  simp [parent, absent]

theorem children_of_absent {element : ElementId} (absent : view element = none) :
    view.children element = [] := by
  simp [children, absent]

theorem present_of_parent {element parent : ElementId} (parentIs : view.parent element = some parent) :
    (view element).isSome := by
  cases found : view element with
  | none => simp [View.parent, found] at parentIs
  | some _ => rfl

namespace Forest

theorem parent_ne (forest : view.Forest) {element parent : ElementId}
    (parentIs : view.parent element = some parent) : parent ≠ element := by
  obtain ⟨rank, ranked⟩ := forest.ranked
  intro same
  subst same
  exact Nat.lt_irrefl _ (ranked _ _ parentIs)

/-- No element is below its own child: there is no cycle. -/
theorem not_below_child (forest : view.Forest) {element parent : ElementId}
    (parentIs : view.parent element = some parent) : ¬ view.Below parent element := by
  obtain ⟨rank, ranked⟩ := forest.ranked
  intro below
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (ranked _ _ parentIs) (below.rank_le ranked))

theorem parent_present (forest : view.Forest) {element parent : ElementId}
    (parentIs : view.parent element = some parent) : (view parent).isSome := by
  have listed := forest.listed _ _ parentIs
  cases found : view parent with
  | none => simp [children, found] at listed
  | some _ => rfl

theorem not_below_absent (forest : view.Forest) {absentOne : ElementId}
    (absent : view absentOne = none) {element : ElementId} (different : element ≠ absentOne) :
    ¬ view.Below element absentOne := by
  intro below
  induction below with
  | refl => exact different rfl
  | @up child parent ancestor parentIs _ induction =>
      by_cases same : parent = ancestor
      · subst same
        have listed := forest.listed _ _ parentIs
        rw [children_of_absent absent] at listed
        cases listed
      · exact induction absent same

end Forest

end View

/-- The store's `parentOf` and `childrenOf` are the view's. -/
theorem parentOf_eq (store : ContentStore) : parentOf store = (View.parent (elementAt store)) := rfl
theorem childrenOf_eq (store : ContentStore) : childrenOf store = (View.children (elementAt store)) := by
  funext element
  unfold childrenOf View.children
  rfl

/-- The document's tree: its elements form a forest, and its root element is
stored and has no parent. -/
structure DocumentTree (store : ContentStore) (document : DocumentId) : Prop where
  forest : (View.Forest (elementAt store))
  root : ∀ root, rootOf store document = some root →
    (elementAt store root).isSome ∧ (View.parent (elementAt store)) root = none

/-! ## Store writes as view updates -/

theorem elementAt_set_element (store : ContentStore) (element : ElementId) (record : ElementRecord) :
    elementAt (store.set ⟨.elements, element⟩ (some record)) =
      Function.update (elementAt store) element (some record) := by
  funext other
  by_cases same : other = element
  · subst same
    rw [Function.update_self]
    unfold elementAt Hyperdocument.lookup
    exact Store.Store.set_eq _ _ _
  · rw [Function.update_of_ne same]
    unfold elementAt Hyperdocument.lookup
    exact Store.Store.set_ne _ _ _ _ (fun eq => same (by cases eq; rfl))

theorem elementAt_set_other (store : ContentStore) {space : Namespace} (key : Key space)
    (value : Option (Value space)) (other : space ≠ .elements) :
    elementAt (store.set ⟨space, key⟩ value) = elementAt store := by
  funext element
  unfold elementAt Hyperdocument.lookup
  exact Store.Store.set_ne _ _ _ _ (fun same => other (congrArg Sigma.fst same).symm)

theorem rootOf_set_other (store : ContentStore) (document : DocumentId) {space : Namespace}
    (key : Key space) (value : Option (Value space)) (other : space ≠ .documents) :
    rootOf (store.set ⟨space, key⟩ value) document = rootOf store document := by
  unfold rootOf Hyperdocument.lookup
  rw [Store.Store.set_ne _ _ _ _ (fun same => other (congrArg Sigma.fst same).symm)]

theorem elementAt_of_elementStep {progress next : Progress} (stepped : ElementStep progress next)
    (other : ∀ element, next.1 ⟨.elements, element⟩ = progress.1 ⟨.elements, element⟩) :
    elementAt next.1 = elementAt progress.1 :=
  funext fun element => other element

theorem rootOf_of_elementStep {progress next : Progress} (stepped : ElementStep progress next)
    (document : DocumentId) : rootOf next.1 document = rootOf progress.1 document := by
  unfold rootOf Hyperdocument.lookup
  rw [stepped.2 ⟨.documents, document⟩ (by simp)]

theorem update_parent (view : View) (element : ElementId) (record : ElementRecord) (other : ElementId) :
    (View.parent (Function.update view element (some record))) other =
      if other = element then record.parent else view.parent other := by
  by_cases same : other = element
  · subst same
    simp [View.parent]
  · simp [View.parent, Function.update_of_ne same, same]

theorem update_children (view : View) (element : ElementId) (record : ElementRecord) (other : ElementId) :
    (View.children (Function.update view element (some record))) other =
      if other = element then bodyChildren record.body else view.children other := by
  by_cases same : other = element
  · subst same
    simp [View.children]
  · simp [View.children, Function.update_of_ne same, same]

theorem update_isSome {view : View} {element : ElementId} {record : ElementRecord} {other : ElementId}
    (present : (view other).isSome) : ((Function.update view element (some record)) other).isSome := by
  by_cases same : other = element
  · subst same
    simp
  · rwa [Function.update_of_ne same]

/-! ## The three shapes of an edit preserve a forest -/

namespace View.Forest

variable {view : View}

/-- Attaching a detached element (or a fresh leaf) under a container. -/
theorem attach (forest : view.Forest) {parent child : ElementId}
    {record record' childRecord : ElementRecord} {children children' : List ElementId}
    (found : view parent = some record) (body : record.body = .container children)
    (body' : record'.body = .container children') (sameParent : record'.parent = record.parent)
    (perm : children'.Perm (child :: children)) (distinct : child ≠ parent)
    (detached : view.parent child = none)
    (childBody : bodyChildren childRecord.body = view.children child)
    (childParent : childRecord.parent = some parent)
    (acyclic : ¬ view.Below parent child) :
    (View.Forest (Function.update (Function.update view parent (some record')) child (some childRecord))) := by
  classical
  have oldChildren : view.children parent = children := by simp [View.children, found, body, bodyChildren]
  have notThere : child ∉ children := by
    intro member
    rw [← oldChildren] at member
    rw [forest.parented _ _ member] at detached
    cases detached
  have parents : ∀ other, (View.parent (Function.update (Function.update view parent (some record')) child
      (some childRecord))) other = if other = child then some parent else view.parent other := by
    intro other
    rw [update_parent, update_parent]
    by_cases isChild : other = child
    · simp [isChild, childParent]
    · by_cases isParent : other = parent
      · subst isParent
        simp [isChild, sameParent, View.parent, found]
      · simp [isChild, isParent]
  have kids : ∀ other, (View.children (Function.update (Function.update view parent (some record')) child
      (some childRecord))) other = if other = parent then children' else view.children other := by
    intro other
    rw [update_children, update_children]
    by_cases isChild : other = child
    · subst isChild
      simp [distinct, childBody]
    · by_cases isParent : other = parent
      · subst isParent
        simp [Ne.symm distinct, body', bodyChildren]
      · simp [isChild, isParent]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro element above parentIs
    rw [parents] at parentIs
    rw [kids]
    by_cases isChild : element = child
    · simp only [isChild, if_true, Option.some.injEq] at parentIs
      subst parentIs
      simp only [if_true]
      exact perm.symm.subset (by simp [isChild])
    · simp only [isChild, if_false] at parentIs
      have listed := forest.listed _ _ parentIs
      by_cases isParent : above = parent
      · subst isParent
        simp only [if_true]
        rw [oldChildren] at listed
        exact perm.symm.subset (List.mem_cons_of_mem _ listed)
      · simpa [isParent] using listed
  · intro above element member
    rw [kids] at member
    rw [parents]
    by_cases isParent : above = parent
    · subst isParent
      simp only [if_true] at member
      rcases List.mem_cons.mp (perm.subset member) with same | old
      · simp [same]
      · by_cases isChild : element = child
        · subst isChild
          exact absurd old notThere
        · simp only [isChild, if_false]
          exact forest.parented _ _ (oldChildren ▸ old)
    · simp only [isParent, if_false] at member
      have parentIs := forest.parented _ _ member
      by_cases isChild : element = child
      · subst isChild
        rw [detached] at parentIs
        cases parentIs
      · simpa [isChild] using parentIs
  · intro element
    rw [kids]
    by_cases isParent : element = parent
    · simp only [isParent, if_true]
      apply perm.nodup_iff.mpr
      exact List.nodup_cons.mpr ⟨notThere, oldChildren ▸ forest.nodup parent⟩
    · simp only [isParent, if_false]
      exact forest.nodup element
  · obtain ⟨rank, ranked⟩ := forest.ranked
    refine ⟨fun element => rank element + if view.Below element child then rank parent + 1 else 0, ?_⟩
    intro element above parentIs
    rw [parents] at parentIs
    by_cases isChild : element = child
    · simp only [isChild, if_true, Option.some.injEq] at parentIs
      subst parentIs
      subst isChild
      simp only [View.Below.refl, if_true, acyclic, if_false]
      omega
    · simp only [isChild, if_false] at parentIs
      have step := ranked _ _ parentIs
      by_cases below : view.Below element child
      · have aboveBelow : view.Below above child := by
          rcases below.cases' with same | ⟨other, otherIs, rest⟩
          · exact absurd same isChild
          · rw [parentIs] at otherIs
            obtain rfl := Option.some.inj otherIs
            exact rest
        simp only [below, aboveBelow, if_true]
        omega
      · have aboveNot : ¬ view.Below above child := fun aboveBelow => below (.up parentIs aboveBelow)
        simp only [below, aboveNot, if_false]
        omega

/-- Reordering one container's children. -/
theorem reorder (forest : view.Forest) {parent : ElementId}
    {record record' : ElementRecord} {children children' : List ElementId}
    (found : view parent = some record) (body : record.body = .container children)
    (body' : record'.body = .container children') (sameParent : record'.parent = record.parent)
    (perm : children'.Perm children) :
    (View.Forest (Function.update view parent (some record'))) := by
  have oldChildren : view.children parent = children := by simp [View.children, found, body, bodyChildren]
  have parents : ∀ other, (View.parent (Function.update view parent (some record'))) other =
      view.parent other := by
    intro other
    rw [update_parent]
    by_cases isParent : other = parent
    · subst isParent
      simp [sameParent, View.parent, found]
    · simp [isParent]
  have kids : ∀ other, (View.children (Function.update view parent (some record'))) other =
      if other = parent then children' else view.children other := by
    intro other
    rw [update_children]
    by_cases isParent : other = parent
    · simp [isParent, body', bodyChildren]
    · simp [isParent]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro element above parentIs
    rw [parents] at parentIs
    rw [kids]
    have listed := forest.listed _ _ parentIs
    by_cases isParent : above = parent
    · subst isParent
      simp only [if_true]
      exact perm.symm.subset (oldChildren ▸ listed)
    · simpa [isParent] using listed
  · intro above element member
    rw [kids] at member
    rw [parents]
    by_cases isParent : above = parent
    · subst isParent
      simp only [if_true] at member
      exact forest.parented _ _ (oldChildren ▸ perm.subset member)
    · simp only [isParent, if_false] at member
      exact forest.parented _ _ member
  · intro element
    rw [kids]
    by_cases isParent : element = parent
    · simp only [isParent, if_true]
      exact perm.nodup_iff.mpr (oldChildren ▸ forest.nodup parent)
    · simp only [isParent, if_false]
      exact forest.nodup element
  · obtain ⟨rank, ranked⟩ := forest.ranked
    exact ⟨rank, fun element above parentIs => ranked _ _ ((parents element).symm.trans parentIs)⟩

/-- Detaching one child from its container. -/
theorem detach (forest : view.Forest) {parent child : ElementId}
    {record record' childRecord : ElementRecord} {children : List ElementId}
    (found : view parent = some record) (body : record.body = .container children)
    (body' : record'.body = .container (children.erase child)) (sameParent : record'.parent = record.parent)
    (member : child ∈ children) (childFound : view child = some childRecord) :
    (View.Forest (Function.update (Function.update view parent (some record')) child
      (some { childRecord with parent := none }))) := by
  have oldChildren : view.children parent = children := by simp [View.children, found, body, bodyChildren]
  have childParent : view.parent child = some parent := forest.parented _ _ (oldChildren ▸ member)
  have distinct : child ≠ parent := (forest.parent_ne childParent).symm
  have parents : ∀ other, (View.parent (Function.update (Function.update view parent (some record')) child
      (some { childRecord with parent := none }))) other =
        if other = child then none else view.parent other := by
    intro other
    rw [update_parent, update_parent]
    by_cases isChild : other = child
    · simp [isChild]
    · by_cases isParent : other = parent
      · subst isParent
        simp [isChild, sameParent, View.parent, found]
      · simp [isChild, isParent]
  have kids : ∀ other, (View.children (Function.update (Function.update view parent (some record')) child
      (some { childRecord with parent := none }))) other =
        if other = parent then children.erase child else view.children other := by
    intro other
    rw [update_children, update_children]
    by_cases isChild : other = child
    · subst isChild
      simp [distinct, View.children, childFound]
    · by_cases isParent : other = parent
      · subst isParent
        simp [Ne.symm distinct, body', bodyChildren]
      · simp [isChild, isParent]
  have nodupOld : children.Nodup := oldChildren ▸ forest.nodup parent
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro element above parentIs
    rw [parents] at parentIs
    rw [kids]
    by_cases isChild : element = child
    · simp [isChild] at parentIs
    · simp only [isChild, if_false] at parentIs
      have listed := forest.listed _ _ parentIs
      by_cases isParent : above = parent
      · subst isParent
        simp only [if_true]
        exact (List.mem_erase_of_ne isChild).mpr (oldChildren ▸ listed)
      · simpa [isParent] using listed
  · intro above element member'
    rw [kids] at member'
    rw [parents]
    by_cases isParent : above = parent
    · subst isParent
      simp only [if_true] at member'
      obtain ⟨different, old⟩ := (List.Nodup.mem_erase_iff nodupOld).mp member'
      simp only [different, if_false]
      exact forest.parented _ _ (oldChildren ▸ old)
    · simp only [isParent, if_false] at member'
      have parentIs := forest.parented _ _ member'
      by_cases isChild : element = child
      · subst isChild
        rw [childParent] at parentIs
        exact absurd (Option.some.inj parentIs).symm isParent
      · simpa [isChild] using parentIs
  · intro element
    rw [kids]
    by_cases isParent : element = parent
    · simp only [isParent, if_true]
      exact nodupOld.erase child
    · simp only [isParent, if_false]
      exact forest.nodup element
  · obtain ⟨rank, ranked⟩ := forest.ranked
    refine ⟨rank, fun element above parentIs => ?_⟩
    rw [parents] at parentIs
    by_cases isChild : element = child
    · simp [isChild] at parentIs
    · simp only [isChild, if_false] at parentIs
      exact ranked _ _ parentIs

/-- A new top-level element with no children. -/
theorem insertTop (forest : view.Forest) {element : ElementId} {record : ElementRecord}
    (absent : view element = none) (top : record.parent = none) (leaf : bodyChildren record.body = []) :
    (View.Forest (Function.update view element (some record))) := by
  have parents : ∀ other, (View.parent (Function.update view element (some record))) other =
      if other = element then none else view.parent other := by
    intro other
    rw [update_parent]
    by_cases same : other = element <;> simp [same, top]
  have kids : ∀ other, (View.children (Function.update view element (some record))) other =
      view.children other := by
    intro other
    rw [update_children]
    by_cases same : other = element
    · subst same
      simp [leaf, View.children_of_absent absent]
    · simp [same]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro child above parentIs
    rw [parents] at parentIs
    rw [kids]
    by_cases same : child = element
    · simp [same] at parentIs
    · simp only [same, if_false] at parentIs
      exact forest.listed _ _ parentIs
  · intro above child member
    rw [kids] at member
    rw [parents]
    have parentIs := forest.parented _ _ member
    by_cases same : child = element
    · subst same
      rw [View.parent_of_absent absent] at parentIs
      cases parentIs
    · simpa [same] using parentIs
  · intro other
    rw [kids]
    exact forest.nodup other
  · obtain ⟨rank, ranked⟩ := forest.ranked
    refine ⟨rank, fun child above parentIs => ?_⟩
    rw [parents] at parentIs
    by_cases same : child = element
    · simp [same] at parentIs
    · simp only [same, if_false] at parentIs
      exact ranked _ _ parentIs

end View.Forest

/-! ## Document trees transfer along frames -/

theorem DocumentTree.congr {store store' : ContentStore} {document : DocumentId}
    (tree : DocumentTree store document) (sameElements : elementAt store' = elementAt store)
    (sameRoot : rootOf store' document = rootOf store document) : DocumentTree store' document := by
  constructor
  · rw [sameElements]
    exact tree.forest
  · intro root rooted
    rw [sameElements]
    exact tree.root root (sameRoot.symm.trans rooted)

theorem DocumentTree.set_other {store : ContentStore} {document : DocumentId}
    (tree : DocumentTree store document) {space : Namespace} (key : Key space)
    (value : Option (Value space)) (notElements : space ≠ .elements) (notDocuments : space ≠ .documents) :
    DocumentTree (store.set ⟨space, key⟩ value) document :=
  tree.congr (elementAt_set_other store key value notElements)
    (rootOf_set_other store document key value notDocuments)

theorem genesis_tree (document : DocumentId) : DocumentTree initialStore document := by
  have empty : elementAt initialStore = fun _ => none := rfl
  constructor
  · rw [empty]
    refine ⟨?_, ?_, ?_, ⟨fun _ => 0, ?_⟩⟩
    · intro child parent parentIs
      simp [View.parent] at parentIs
    · intro parent child member
      simp [View.children] at member
    · intro element
      simp [View.children]
    · intro child parent parentIs
      simp [View.parent] at parentIs
  · intro root rooted
    simp [rootOf, Hyperdocument.lookup, initialStore] at rooted

/-! ## The cycle check -/

theorem clearOf_ne : ∀ {fuel : Nat} {store : ContentStore} {element child : ElementId},
    clearOf fuel store element child = true → element ≠ child
  | 0, _, _, _, clear => by simp [clearOf] at clear
  | _ + 1, _, _, _, clear => by
      simp only [clearOf, Bool.and_eq_true, decide_eq_true_eq] at clear
      exact clear.1

/-- The check is sound: `clearOf` admits only a container that is not below the
spliced element. -/
theorem clearOf_sound : ∀ (fuel : Nat) (store : ContentStore) (element child : ElementId),
    clearOf fuel store element child = true → ¬ (View.Below (elementAt store)) element child
  | 0, _, _, _, clear => by simp [clearOf] at clear
  | fuel + 1, store, element, child, clear => by
      intro below
      simp only [clearOf, Bool.and_eq_true, decide_eq_true_eq] at clear
      obtain ⟨different, rest⟩ := clear
      rcases below.cases' with same | ⟨parent, parentIs, above⟩
      · exact different same
      · have parentIs' : parentOf store element = some parent := parentIs
        simp only [parentIs'] at rest
        exact clearOf_sound fuel store parent child rest above

/-! ## What each accepted action writes, read back -/

theorem appendLeaf_ok {author : PrincipalRef} {operation : OperationId} {document : DocumentId}
    {progress next : Progress} {leaf : ElementId} {body : ElementBody} {root : ElementId}
    (rooted : rootOf progress.1 document = some root)
    (accepted : appendLeaf author operation document progress leaf body = .ok next) :
    ∃ record children, elementAt progress.1 root = some record ∧ record.body = .container children ∧
      elementAt progress.1 leaf = none ∧ leaf ≠ root ∧
      elementAt next.1 = Function.update (Function.update (elementAt progress.1) root
        (some { record with body := .container (children ++ [leaf]) })) leaf
        (some (leafRecord author operation document root body)) := by
  unfold appendLeaf at accepted
  simp only [rooted] at accepted
  cases found : elementAt progress.1 root with
  | none => simp [found] at accepted
  | some record =>
      simp only [found] at accepted
      cases isContainer : record.body with
      | container children =>
          simp only [isContainer] at accepted
          obtain ⟨middle, first, rest⟩ := bind_eq_ok accepted
          obtain ⟨_, _, rfl⟩ := rewriteElement_ok first
          obtain ⟨fresh, rfl⟩ := allocate_ok rest
          have distinct : leaf ≠ root := by
            intro same
            subst same
            simp at fresh
          have absent : elementAt progress.1 leaf = none := by
            have := fresh
            unfold elementAt Hyperdocument.lookup
            rwa [Store.Store.set_ne _ _ _ _ (fun eq => distinct (by cases eq; rfl))] at this
          refine ⟨record, children, rfl, isContainer, absent, distinct, ?_⟩
          dsimp only
          rw [elementAt_set_element, elementAt_set_element]
      | runs _ => simp [isContainer] at accepted
      | embed _ => simp [isContainer] at accepted
      | atom _ => simp [isContainer] at accepted
      | «opaque» _ _ => simp [isContainer] at accepted

theorem appendLeaf_tree (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    {progress next : Progress} {leaf : ElementId} {body : ElementBody}
    (leafBody : bodyChildren body = [])
    (tree : DocumentTree progress.1 document)
    (accepted : appendLeaf author operation document progress leaf body = .ok next) :
    DocumentTree next.1 document := by
  have sameRoot := rootOf_of_elementStep (appendLeaf_step author operation document accepted) document
  cases rooted : rootOf progress.1 document with
  | none =>
      unfold appendLeaf at accepted
      simp only [rooted] at accepted
      cases accepted
      exact tree
  | some root =>
      obtain ⟨record, children, found, recordBody, absent, distinct, post⟩ := appendLeaf_ok rooted accepted
      have rootTop := tree.root root rooted
      constructor
      · rw [post]
        exact tree.forest.attach found recordBody rfl rfl
          (List.perm_append_comm.trans (by simp)) distinct (View.parent_of_absent absent)
          (by simp [leafRecord, leafBody, View.children_of_absent absent]) rfl
          (tree.forest.not_below_absent absent distinct.symm)
      · intro other otherRooted
        rw [sameRoot, rooted] at otherRooted
        obtain rfl := Option.some.inj otherRooted
        rw [post]
        refine ⟨update_isSome (update_isSome rootTop.1), ?_⟩
        have top : record.parent = none := by simpa [View.parent, found] using rootTop.2
        rw [update_parent, update_parent]
        simp [distinct.symm, top]

theorem splice_ok {operation : OperationId} {document : DocumentId} {progress next : Progress}
    {element : ElementId} {revision : OperationId} {index : Nat} {child : ElementId}
    (accepted : editElementStep operation document progress ⟨element, revision, .splice index child⟩ =
      .ok next) :
    ∃ record children childRecord,
      elementAt progress.1 element = some record ∧ record.document = document ∧
      record.body = .container children ∧
      (record.revision = revision ∨ record.revision = operation) ∧
      index ≤ children.length ∧ elementAt progress.1 child = some childRecord ∧
      childRecord.document = document ∧ childRecord.parent = none ∧
      rootOf progress.1 document ≠ some child ∧
      clearOf (treeFuel progress.1) progress.1 element child = true ∧
      next.1 = (progress.1.set ⟨.elements, element⟩
          (some (withChildren record (children.insertIdx index child) operation))).set
        ⟨.elements, child⟩ (some { childRecord with parent := some element }) := by
  unfold editElementStep at accepted
  obtain ⟨⟨record, children⟩, opened, rest⟩ := bind_eq_ok accepted
  obtain ⟨found, local_, body, current⟩ := openContainer_ok opened
  simp only at rest
  split at rest
  · rename_i inRange
    cases childFound : elementAt progress.1 child with
    | none => simp [childFound] at rest
    | some childRecord =>
        simp only [childFound] at rest
        split at rest
        · cases rest
        · rename_i childLocal
          split at rest
          · cases rest
          · rename_i notAttached
            split at rest
            · rename_i clear
              obtain ⟨middle, first, last⟩ := bind_eq_ok rest
              obtain ⟨_, _, rfl⟩ := rewriteElement_ok first
              obtain ⟨before, beforeFound, rfl⟩ := reparent_ok last
              have distinct := clearOf_ne clear
              dsimp only at beforeFound
              rw [elementAt_set_element, Function.update_of_ne distinct.symm, childFound] at beforeFound
              obtain rfl : childRecord = before := Option.some.inj beforeFound
              have noParent : childRecord.parent = none := by
                cases parentIs : childRecord.parent with
                | none => rfl
                | some _ => simp [parentIs] at notAttached
              have notRoot : rootOf progress.1 document ≠ some child := by
                intro isRoot
                simp [isRoot] at notAttached
              exact ⟨record, children, childRecord, found, local_, body, current, inRange, rfl,
                not_not.mp childLocal, noParent, notRoot, clear, rfl⟩
            · cases rest
  · cases rest

theorem move_ok {operation : OperationId} {document : DocumentId} {progress next : Progress}
    {element : ElementId} {revision : OperationId} {child : ElementId} {index : Nat}
    (accepted : editElementStep operation document progress ⟨element, revision, .move child index⟩ =
      .ok next) :
    ∃ record children,
      elementAt progress.1 element = some record ∧ record.document = document ∧
      record.body = .container children ∧
      (record.revision = revision ∨ record.revision = operation) ∧
      child ∈ children ∧ index < children.length ∧
      next.1 = progress.1.set ⟨.elements, element⟩
        (some (withChildren record ((children.erase child).insertIdx index child) operation)) := by
  unfold editElementStep at accepted
  obtain ⟨⟨record, children⟩, opened, rest⟩ := bind_eq_ok accepted
  obtain ⟨found, local_, body, current⟩ := openContainer_ok opened
  simp only at rest
  split at rest
  · rename_i member
    split at rest
    · rename_i inRange
      obtain ⟨_, _, rfl⟩ := rewriteElement_ok rest
      exact ⟨record, children, found, local_, body, current, member, inRange, rfl⟩
    · cases rest
  · cases rest

theorem remove_ok {operation : OperationId} {document : DocumentId} {progress next : Progress}
    {element : ElementId} {revision : OperationId} {child : ElementId}
    (accepted : editElementStep operation document progress ⟨element, revision, .remove child⟩ =
      .ok next) :
    ∃ record children childRecord,
      elementAt progress.1 element = some record ∧ record.document = document ∧
      record.body = .container children ∧
      (record.revision = revision ∨ record.revision = operation) ∧
      child ∈ children ∧
      elementAt (progress.1.set ⟨.elements, element⟩
        (some (withChildren record (children.erase child) operation))) child = some childRecord ∧
      next.1 = (progress.1.set ⟨.elements, element⟩
          (some (withChildren record (children.erase child) operation))).set
        ⟨.elements, child⟩ (some { childRecord with parent := none }) := by
  unfold editElementStep at accepted
  obtain ⟨⟨record, children⟩, opened, rest⟩ := bind_eq_ok accepted
  obtain ⟨found, local_, body, current⟩ := openContainer_ok opened
  simp only at rest
  split at rest
  · rename_i member
    obtain ⟨middle, first, last⟩ := bind_eq_ok rest
    obtain ⟨_, _, rfl⟩ := rewriteElement_ok first
    obtain ⟨before, beforeFound, rfl⟩ := reparent_ok last
    exact ⟨record, children, before, found, local_, body, current, member, beforeFound, rfl⟩
  · cases rest

theorem editElementStep_tree {operation : OperationId} {document : DocumentId}
    {progress next : Progress} {edit : EditElement}
    (tree : DocumentTree progress.1 document)
    (accepted : editElementStep operation document progress edit = .ok next) :
    DocumentTree next.1 document := by
  have sameRoot := rootOf_of_elementStep (editElementStep_step operation document accepted) document
  obtain ⟨element, revision, op⟩ := edit
  cases op with
  | splice index child =>
      obtain ⟨record, children, childRecord, found, _, body, _, inRange, childFound, _, detached,
        notRoot, clear, post⟩ := splice_ok accepted
      have distinct := clearOf_ne clear
      have elements : elementAt next.1 = Function.update (Function.update (elementAt progress.1) element
          (some (withChildren record (children.insertIdx index child) operation))) child
          (some { childRecord with parent := some element }) := by
        rw [post, elementAt_set_element, elementAt_set_element]
      constructor
      · rw [elements]
        exact tree.forest.attach found body rfl rfl (List.perm_insertIdx child children inRange)
          distinct.symm (by simp [View.parent, childFound, detached])
          (by simp [View.children, childFound]) rfl (clearOf_sound _ _ _ _ clear)
      · intro root rooted
        rw [sameRoot] at rooted
        have rootTop := tree.root root rooted
        rw [elements]
        refine ⟨update_isSome (update_isSome rootTop.1), ?_⟩
        have notChild : root ≠ child := fun same => notRoot (same ▸ rooted)
        rw [update_parent, update_parent]
        by_cases isElement : root = element
        · subst isElement
          simp [notChild, withChildren, ← rootTop.2, View.parent, found]
        · simp [notChild, isElement, rootTop.2]
  | move child index =>
      obtain ⟨record, children, found, _, body, _, member, inRange, post⟩ := move_ok accepted
      have elements : elementAt next.1 = Function.update (elementAt progress.1) element
          (some (withChildren record ((children.erase child).insertIdx index child) operation)) := by
        rw [post, elementAt_set_element]
      have fits : index ≤ (children.erase child).length := by
        rw [List.length_erase_of_mem member]
        omega
      constructor
      · rw [elements]
        exact tree.forest.reorder found body rfl rfl
          ((List.perm_insertIdx child _ fits).trans (List.perm_cons_erase member).symm)
      · intro root rooted
        rw [sameRoot] at rooted
        have rootTop := tree.root root rooted
        rw [elements]
        refine ⟨update_isSome rootTop.1, ?_⟩
        rw [update_parent]
        by_cases isElement : root = element
        · subst isElement
          simp [withChildren, ← rootTop.2, View.parent, found]
        · simp [isElement, rootTop.2]
  | remove child =>
      obtain ⟨record, children, childRecord, found, _, body, _, member, childFound, post⟩ :=
        remove_ok accepted
      have oldChildren : (View.children (elementAt progress.1)) element = children := by
        simp [View.children, found, body, bodyChildren]
      have childParent := tree.forest.parented _ _ (oldChildren ▸ member)
      have distinct : child ≠ element := (tree.forest.parent_ne childParent).symm
      rw [elementAt_set_element, Function.update_of_ne distinct] at childFound
      have elements : elementAt next.1 = Function.update (Function.update (elementAt progress.1) element
          (some (withChildren record (children.erase child) operation))) child
          (some { childRecord with parent := none }) := by
        rw [post, elementAt_set_element, elementAt_set_element]
      constructor
      · rw [elements]
        exact tree.forest.detach found body rfl rfl member childFound
      · intro root rooted
        rw [sameRoot] at rooted
        have rootTop := tree.root root rooted
        rw [elements]
        refine ⟨update_isSome (update_isSome rootTop.1), ?_⟩
        rw [update_parent, update_parent]
        by_cases isChild : root = child
        · simp [isChild]
        · by_cases isElement : root = element
          · subst isElement
            simp [isChild, withChildren, ← rootTop.2, View.parent, found]
          · simp [isChild, isElement, rootTop.2]

/-! ## Every admitted state is a document tree -/

theorem step_tree (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (context : Context) {progress next : Progress} {action : Action}
    (tree : DocumentTree progress.1 document)
    (accepted : step author operation document context progress action = .ok next) :
    DocumentTree next.1 document := by
  cases action with
  | createDocument root schema =>
      simp only [step] at accepted
      obtain ⟨middle, first, rest⟩ := bind_eq_ok accepted
      obtain ⟨freshDocument, rfl⟩ := allocate_ok first
      obtain ⟨freshRoot, rfl⟩ := allocate_ok rest
      dsimp only at freshRoot ⊢
      have absent : elementAt progress.1 root = none := by
        unfold elementAt Hyperdocument.lookup
        rwa [Store.Store.set_ne _ _ _ _ (by simp)] at freshRoot
      have elements : elementAt ((progress.1.set ⟨.documents, document⟩ (some ⟨root, schema, author,
          operation⟩)).set ⟨.elements, root⟩ (some ⟨document, none, .container [], author, operation,
          operation, none⟩)) = Function.update (elementAt progress.1) root
          (some ⟨document, none, .container [], author, operation, operation, none⟩) := by
        rw [elementAt_set_element, elementAt_set_other _ _ _ (by simp)]
      have rooted : rootOf ((progress.1.set ⟨.documents, document⟩ (some ⟨root, schema, author,
          operation⟩)).set ⟨.elements, root⟩ (some ⟨document, none, .container [], author, operation,
          operation, none⟩)) document = some root := by
        rw [rootOf_set_other _ _ _ _ (by simp)]
        unfold rootOf Hyperdocument.lookup
        rw [Store.Store.set_eq]
        rfl
      constructor
      · rw [elements]
        exact tree.forest.insertTop absent rfl rfl
      · intro other otherRooted
        rw [rooted] at otherRooted
        obtain rfl := Option.some.inj otherRooted
        rw [elements, update_parent]
        simp
  | createAtom atom kind payload =>
      simp only [step] at accepted
      obtain ⟨middle, first, rest⟩ := bind_eq_ok accepted
      obtain ⟨_, rfl⟩ := allocate_ok first
      exact appendLeaf_tree author operation document rfl
        (tree.set_other _ _ (by simp) (by simp)) rest
  | editAtom edit =>
      simp only [step] at accepted
      unfold replaceAtom at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted
        · cases accepted
          exact tree.set_other _ _ (by simp) (by simp)
  | link link source target relation =>
      simp only [step] at accepted
      split at accepted
      · obtain ⟨_, rfl⟩ := allocate_ok accepted
        exact tree.set_other _ _ (by simp) (by simp)
      · cases accepted
  | createRun runId atoms =>
      simp only [step] at accepted
      split at accepted
      · obtain ⟨_, rfl⟩ := allocate_ok accepted
        exact tree.set_other _ _ (by simp) (by simp)
      · cases accepted
  | annotate annotationId atom revision body =>
      simp only [step] at accepted
      split at accepted
      · obtain ⟨_, rfl⟩ := allocate_ok accepted
        exact tree.set_other _ _ (by simp) (by simp)
      · cases accepted
  | transclude transclusion link request =>
      cases covered : context.sourceRead request.source with
      | none => simp [step, covered] at accepted
      | some read =>
          simp only [step, covered] at accepted
          obtain ⟨first, firstOk, rest⟩ := bind_eq_ok accepted
          obtain ⟨second, secondOk, last⟩ := bind_eq_ok rest
          obtain ⟨_, rfl⟩ := allocate_ok firstOk
          obtain ⟨_, rfl⟩ := allocate_ok secondOk
          exact appendLeaf_tree author operation document rfl
            ((tree.set_other _ _ (by simp) (by simp)).set_other _ _ (by simp) (by simp)) last
  | editElement edit =>
      exact editElementStep_tree tree accepted
  | createContainer element =>
      simp only [step] at accepted
      split at accepted
      · cases accepted
      · exact appendLeaf_tree author operation document rfl tree accepted

theorem run_tree (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (context : Context) {pre : ContentStore} {command : Command} {next : Progress}
    (tree : DocumentTree pre document)
    (accepted : run author operation document context pre command = .ok next) :
    DocumentTree next.1 document := by
  suffices general : ∀ (actions : List Action) (progress : Progress),
      DocumentTree progress.1 document →
      actions.foldlM (step author operation document context) progress = .ok next →
        DocumentTree next.1 document from general command.actions (pre, []) tree accepted
  intro actions
  induction actions with
  | nil =>
      intro progress holds done
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at done
      rw [← done]
      exact holds
  | cons action rest induction =>
      intro progress holds done
      simp only [List.foldlM_cons, bind, Except.bind] at done
      cases stepped : step author operation document context progress action with
      | error reason => simp [stepped] at done
      | ok middle =>
          simp only [stepped] at done
          exact induction middle (step_tree author operation document context holds stepped) done

/-- The states of one document's cell admitted from genesis: the empty store,
then any number of accepted content runs on it. -/
inductive Admitted (document : DocumentId) : ContentStore → Prop
  | genesis : Admitted document initialStore
  | run {pre : ContentStore} {progress : Progress} (author : PrincipalRef) (operation : OperationId)
      (context : Context) (command : Command) (admitted : Admitted document pre)
      (accepted : ContentResource.run author operation document context pre command = .ok progress) :
      Admitted document progress.1

theorem Admitted.tree {document : DocumentId} {store : ContentStore}
    (admitted : Admitted document store) : DocumentTree store document := by
  induction admitted with
  | genesis => exact genesis_tree document
  | run author operation context command _ accepted induction =>
      exact run_tree author operation document context induction accepted

/-- Every admitted state is a forest — parent and children agree, and no element
is below its own child (no cycle) — whose document root is stored and is the
top of its tree: it has no parent. -/
theorem tree_acyclic {document : DocumentId} {store : ContentStore}
    (admitted : Admitted document store) :
    (View.Forest (elementAt store)) ∧
      (∀ element parent, parentOf store element = some parent →
        ¬ (View.Below (elementAt store)) parent element) ∧
      ∀ root, rootOf store document = some root →
        (elementAt store root).isSome ∧ parentOf store root = none := by
  have tree := admitted.tree
  exact ⟨tree.forest, fun _ _ parentIs => tree.forest.not_below_child parentIs, tree.root⟩

/-! ## The order -/

theorem walk_below {store : ContentStore} (forest : (View.Forest (elementAt store))) :
    ∀ (fuel : Nat) (element member : ElementId), member ∈ walk fuel store element →
      (View.Below (elementAt store)) member element
  | 0, _, _, inside => by simp [walk] at inside
  | fuel + 1, element, member, inside => by
      simp only [walk, List.mem_cons, List.mem_flatMap] at inside
      rcases inside with same | ⟨child, childIn, deeper⟩
      · subst same
        exact .refl _
      · rw [childrenOf_eq] at childIn
        exact (walk_below forest fuel child member deeper).trans
          (.up (forest.parented _ _ childIn) (.refl _))

theorem walk_nodup {store : ContentStore} (forest : (View.Forest (elementAt store))) :
    ∀ (fuel : Nat) (element : ElementId), (walk fuel store element).Nodup
  | 0, _ => by simp [walk]
  | fuel + 1, element => by
      obtain ⟨rank, ranked⟩ := forest.ranked
      simp only [walk]
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · intro inside
        obtain ⟨child, childIn, deeper⟩ := List.mem_flatMap.mp inside
        rw [childrenOf_eq] at childIn
        have parentIs := forest.parented _ _ childIn
        exact forest.not_below_child parentIs (walk_below forest fuel child element deeper)
      · refine List.nodup_flatMap.mpr ⟨fun child _ => walk_nodup forest fuel child, ?_⟩
        have kids := forest.nodup element
        rw [← childrenOf_eq] at kids
        refine kids.imp_of_mem ?_
        intro first second firstIn secondIn different
        intro member inFirst inSecond
        rw [childrenOf_eq] at firstIn secondIn
        have firstParent := forest.parented _ _ firstIn
        have secondParent := forest.parented _ _ secondIn
        rcases (walk_below forest fuel first member inFirst).linear
          (walk_below forest fuel second member inSecond) with below | below
        · rcases below.cases' with same | ⟨above, aboveIs, rest⟩
          · exact different same
          · rw [firstParent] at aboveIs
            obtain rfl := Option.some.inj aboveIs
            exact forest.not_below_child secondParent rest
        · rcases below.cases' with same | ⟨above, aboveIs, rest⟩
          · exact different same.symm
          · rw [secondParent] at aboveIs
            obtain rfl := Option.some.inj aboveIs
            exact forest.not_below_child firstParent rest

theorem walk_mono {store : ContentStore} :
    ∀ {fuel more : Nat} {element member : ElementId}, member ∈ walk fuel store element →
      fuel ≤ more → member ∈ walk more store element
  | 0, _, _, _, inside, _ => by simp [walk] at inside
  | _ + 1, 0, _, _, _, enough => by omega
  | fuel + 1, more + 1, element, member, inside, enough => by
      have unfolded : member ∈ element :: (childrenOf store element).flatMap (walk fuel store) := inside
      show member ∈ element :: (childrenOf store element).flatMap (walk more store)
      rcases List.mem_cons.mp unfolded with same | deeper
      · exact List.mem_cons.mpr (Or.inl same)
      · obtain ⟨child, childIn, further⟩ := List.mem_flatMap.mp deeper
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, childIn, walk_mono further (by omega)⟩)

theorem walk_child {store : ContentStore} :
    ∀ {fuel : Nat} {element parent child : ElementId}, parent ∈ walk fuel store element →
      child ∈ childrenOf store parent → child ∈ walk (fuel + 1) store element
  | 0, _, _, _, inside, _ => by simp [walk] at inside
  | fuel + 1, element, parent, child, inside, childIn => by
      have unfolded : parent ∈ element :: (childrenOf store element).flatMap (walk fuel store) := inside
      show child ∈ element :: (childrenOf store element).flatMap (walk (fuel + 1) store)
      rcases List.mem_cons.mp unfolded with same | deeper
      · subst same
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, childIn, List.mem_cons_self⟩)
      · obtain ⟨other, otherIn, further⟩ := List.mem_flatMap.mp deeper
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨other, otherIn, walk_child further childIn⟩)

/-- A chain from `element` up to `ancestor`: distinct stored elements, and
`element` is in the walk from `ancestor` as deep as the chain is long. -/
theorem below_chain {store : ContentStore} (forest : (View.Forest (elementAt store)))
    {element ancestor : ElementId} (below : (View.Below (elementAt store)) element ancestor)
    (present : (elementAt store ancestor).isSome) :
    ∃ path : List ElementId, path.Nodup ∧ (∀ other ∈ path, (elementAt store other).isSome) ∧
      (∀ other ∈ path, (View.Below (elementAt store)) element other) ∧
      element ∈ walk path.length store ancestor := by
  induction below with
  | refl top =>
      refine ⟨[top], List.nodup_singleton _, by simpa using present, ?_, ?_⟩
      · intro other member
        rw [List.mem_singleton.mp member]
        exact .refl _
      · exact List.mem_cons_self
  | @up child parent ancestor parentIs rest induction =>
      obtain ⟨path, nodup, stored, above, inside⟩ := induction present
      refine ⟨child :: path, List.nodup_cons.mpr ⟨?_, nodup⟩, ?_, ?_, ?_⟩
      · intro member
        exact forest.not_below_child parentIs (above _ member)
      · intro other member
        rcases List.mem_cons.mp member with same | old
        · subst same
          exact View.present_of_parent parentIs
        · exact stored other old
      · intro other member
        rcases List.mem_cons.mp member with same | old
        · subst same
          exact .refl _
        · exact .up parentIs (above other old)
      · exact walk_child inside (by rw [childrenOf_eq]; exact forest.listed _ _ parentIs)

theorem chain_length_le {store : ContentStore} {path : List ElementId} (nodup : path.Nodup)
    (stored : ∀ other ∈ path, (elementAt store other).isSome) : path.length ≤ store.support.card := by
  classical
  let address : ElementId → Hyperdocument.Address := fun element => ⟨.elements, element⟩
  have injective : Function.Injective address := fun first second same => by cases same; rfl
  have mappedNodup : (path.map address).Nodup := nodup.map injective
  have subset : (path.map address).toFinset ⊆ store.support := by
    intro entry member
    obtain ⟨element, inside, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    apply DFinsupp.mem_support_iff.mpr
    intro zero
    have absent : elementAt store element = none := zero
    have := stored element inside
    rw [absent] at this
    cases this
  have := Finset.card_le_card subset
  rwa [List.toFinset_card_of_nodup mappedNodup, List.length_map] at this

theorem below_in_walk {store : ContentStore} (forest : (View.Forest (elementAt store)))
    {element ancestor : ElementId} (below : (View.Below (elementAt store)) element ancestor)
    (present : (elementAt store ancestor).isSome) :
    element ∈ walk (treeFuel store) store ancestor := by
  obtain ⟨path, nodup, stored, _, inside⟩ := below_chain forest below present
  exact walk_mono inside (by have := chain_length_le nodup stored; unfold treeFuel; omega)

/-- The order lists every element placed under the document's root exactly once,
and nothing else: each live line once, never a detached one, never twice. -/
theorem order_total {store : ContentStore} {document : DocumentId} {root : ElementId}
    (tree : DocumentTree store document) (rooted : rootOf store document = some root) :
    (documentOrder store document).Nodup ∧
      ∀ element, element ∈ documentOrder store document ↔
        element ≠ root ∧ (View.Below (elementAt store)) element root := by
  have full := walk_nodup tree.forest (treeFuel store) root
  have walkEq : walk (treeFuel store) store root =
      root :: (childrenOf store root).flatMap (walk store.support.card store) := by
    simp [treeFuel, walk]
  have order : documentOrder store document =
      (childrenOf store root).flatMap (walk store.support.card store) := by
    simp [documentOrder, rooted, walkEq]
  rw [walkEq] at full
  obtain ⟨rootOut, restNodup⟩ := List.nodup_cons.mp full
  refine ⟨order ▸ restNodup, ?_⟩
  intro element
  rw [order]
  constructor
  · intro inside
    refine ⟨fun same => rootOut (same ▸ inside), ?_⟩
    apply walk_below tree.forest (treeFuel store)
    rw [walkEq]
    exact List.mem_cons_of_mem _ inside
  · rintro ⟨different, below⟩
    have inside := below_in_walk tree.forest below (tree.root root rooted).1
    rw [walkEq] at inside
    rcases List.mem_cons.mp inside with same | rest
    · exact absurd same different
    · exact rest

/-- In a flat document — every child of the root a leaf — the order is the
root's children, in order. -/
theorem documentOrder_flat {store : ContentStore} {document : DocumentId} {root : ElementId}
    (rooted : rootOf store document = some root) (present : (elementAt store root).isSome)
    (flat : ∀ child ∈ childrenOf store root, childrenOf store child = []) :
    documentOrder store document = childrenOf store root := by
  have positive : 0 < store.support.card := by
    apply Finset.card_pos.mpr
    refine ⟨⟨.elements, root⟩, DFinsupp.mem_support_iff.mpr ?_⟩
    intro zero
    have absent : elementAt store root = none := zero
    rw [absent] at present
    cases present
  obtain ⟨depth, hdepth⟩ : ∃ depth, store.support.card = depth + 1 := ⟨_, (Nat.succ_pred_eq_of_pos positive).symm⟩
  have leaves : ∀ children : List ElementId, (∀ child ∈ children, childrenOf store child = []) →
      children.flatMap (walk (depth + 1) store) = children := by
    intro children allFlat
    induction children with
    | nil => rfl
    | cons child rest induction =>
        have one : walk (depth + 1) store child = [child] := by
          show child :: (childrenOf store child).flatMap (walk depth store) = [child]
          rw [allFlat child List.mem_cons_self]
          rfl
        rw [List.flatMap_cons, one, induction (fun other member => allFlat other (List.mem_cons_of_mem _ member))]
        rfl
  simp only [documentOrder, rooted, treeFuel, hdepth, walk, List.tail_cons]
  exact leaves _ flat

/-! ## What each edit does -/

theorem insertIdx_erase_self {child : ElementId} :
    ∀ {children : List ElementId} {index : Nat}, child ∉ children → index ≤ children.length →
      (children.insertIdx index child).erase child = children
  | children, 0, _, _ => by simp [List.insertIdx_zero]
  | [], _ + 1, _, inRange => by simp at inRange
  | head :: tail, index + 1, absent, inRange => by
      have headNe : head ≠ child := fun same => absent (same ▸ List.mem_cons_self)
      rw [List.insertIdx_succ_cons, List.erase_cons_tail (by simpa using headNe),
        insertIdx_erase_self (fun member => absent (List.mem_cons_of_mem _ member))
          (by simpa using inRange)]

/-- After `splice(index, child)` the child is at `index`, every other child keeps
its relative order, and the child names the container as its parent. -/
theorem splice_places (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (context : Context) {progress next : Progress} {element : ElementId} {revision : OperationId}
    {index : Nat} {child : ElementId} (forest : (View.Forest (elementAt progress.1)))
    (accepted : step author operation document context progress
      (.editElement ⟨element, revision, .splice index child⟩) = .ok next) :
    (childrenOf next.1 element)[index]? = some child ∧
      (childrenOf next.1 element).erase child = childrenOf progress.1 element ∧
      parentOf next.1 child = some element := by
  obtain ⟨record, children, childRecord, found, _, body, _, inRange, childFound, _, detached,
    _, clear, post⟩ := splice_ok accepted
  have distinct := clearOf_ne clear
  have oldChildren : childrenOf progress.1 element = children := by
    simp [childrenOf, found, body, bodyChildren]
  have notThere : child ∉ children := by
    intro member
    have parentIs := forest.parented element child (by rw [← childrenOf_eq, oldChildren]; exact member)
    simp [View.parent, childFound, detached] at parentIs
  have newChildren : childrenOf next.1 element = children.insertIdx index child := by
    rw [childrenOf_eq, post, elementAt_set_element, elementAt_set_element, update_children,
      update_children]
    simp [distinct, withChildren, bodyChildren]
  refine ⟨?_, ?_, ?_⟩
  · rw [newChildren, List.getElem?_insertIdx_self]
    simp [inRange]
  · rw [newChildren, oldChildren, insertIdx_erase_self notThere inRange]
  · rw [parentOf_eq, post, elementAt_set_element, update_parent]
    simp

/-- A move changes a child's position and never the set of children, nor any
element's parent. -/
theorem move_preserves_set (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (context : Context) {progress next : Progress} {element : ElementId} {revision : OperationId}
    {child : ElementId} {index : Nat}
    (accepted : step author operation document context progress
      (.editElement ⟨element, revision, .move child index⟩) = .ok next) :
    (childrenOf next.1 element).Perm (childrenOf progress.1 element) ∧
      (childrenOf next.1 element)[index]? = some child ∧
      ∀ other, parentOf next.1 other = parentOf progress.1 other := by
  obtain ⟨record, children, found, _, body, _, member, inRange, post⟩ := move_ok accepted
  have oldChildren : childrenOf progress.1 element = children := by
    simp [childrenOf, found, body, bodyChildren]
  have fits : index ≤ (children.erase child).length := by
    rw [List.length_erase_of_mem member]
    omega
  have newChildren : childrenOf next.1 element = (children.erase child).insertIdx index child := by
    rw [childrenOf_eq, post, elementAt_set_element, update_children]
    simp [withChildren, bodyChildren]
  refine ⟨?_, ?_, ?_⟩
  · rw [newChildren, oldChildren]
    exact (List.perm_insertIdx child _ fits).trans (List.perm_cons_erase member).symm
  · rw [newChildren, List.getElem?_insertIdx_self]
    simp [fits]
  · intro other
    rw [parentOf_eq, parentOf_eq, post, elementAt_set_element, update_parent]
    by_cases same : other = element
    · subst same
      simp [withChildren, View.parent, found]
    · simp [same]

/-- A removed child is in no container and has no parent; neither it nor anything
below it (its atoms' leaves) is in the order; every atom record stays. -/
theorem remove_detaches (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (context : Context) {progress next : Progress} {element : ElementId} {revision : OperationId}
    {child : ElementId} (tree : DocumentTree progress.1 document)
    (accepted : step author operation document context progress
      (.editElement ⟨element, revision, .remove child⟩) = .ok next) :
    (∀ container, child ∉ childrenOf next.1 container) ∧
      parentOf next.1 child = none ∧
      (∀ below, (View.Below (elementAt next.1)) below child → below ∉ documentOrder next.1 document) ∧
      (∀ atom, Hyperdocument.lookup next.1 .atoms atom = Hyperdocument.lookup progress.1 .atoms atom) ∧
      (elementAt next.1 child).isSome := by
  have treeNext : DocumentTree next.1 document := step_tree author operation document context tree accepted
  have stepped := editElementStep_step operation document accepted
  obtain ⟨record, children, childRecord, found, _, body, _, member, childFound, post⟩ :=
    remove_ok accepted
  have oldChildren : (View.children (elementAt progress.1)) element = children := by
    simp [View.children, found, body, bodyChildren]
  have childParent := tree.forest.parented _ _ (oldChildren ▸ member)
  have distinct : child ≠ element := (tree.forest.parent_ne childParent).symm
  have detached : parentOf next.1 child = none := by
    rw [parentOf_eq, post, elementAt_set_element, update_parent]
    simp
  refine ⟨?_, detached, ?_, ?_, ?_⟩
  · intro container inside
    rw [childrenOf_eq] at inside
    have := treeNext.forest.parented _ _ inside
    rw [← parentOf_eq, detached] at this
    cases this
  · intro below underChild inOrder
    cases rooted : rootOf next.1 document with
    | none => simp [documentOrder, rooted] at inOrder
    | some root =>
        have underRoot := ((order_total treeNext rooted).2 below).mp inOrder
        have rootTop := treeNext.root root rooted
        rcases underChild.linear underRoot.2 with up | down
        · rcases up.cases' with same | ⟨above, aboveIs, _⟩
          · subst same
            have rootBefore : rootOf progress.1 document = some child := by
              rw [← rootOf_of_elementStep stepped]; exact rooted
            have := (tree.root child rootBefore).2
            rw [childParent] at this
            cases this
          · rw [← parentOf_eq, detached] at aboveIs
            cases aboveIs
        · rcases down.cases' with same | ⟨above, aboveIs, _⟩
          · subst same
            have rootBefore : rootOf progress.1 document = some root := by
              rw [← rootOf_of_elementStep stepped]; exact rooted
            have := (tree.root root rootBefore).2
            rw [childParent] at this
            cases this
          · rw [rootTop.2] at aboveIs
            cases aboveIs
  · intro atom
    unfold Hyperdocument.lookup
    exact stepped.2 ⟨.atoms, atom⟩ (by simp)
  · rw [post, elementAt_set_element]
    simp

/-! ## Refusals by name, and their admitted poles -/

/-- A splice that would place an element under itself or its own descendant is
refused `cycle`, before anything is written. -/
theorem cycle_refused (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (context : Context) (progress : Progress) {element child : ElementId} {revision : OperationId}
    {index : Nat} {record childRecord : ElementRecord} {children : List ElementId}
    (found : elementAt progress.1 element = some record) (local_ : record.document = document)
    (body : record.body = .container children) (current : record.revision = revision)
    (inRange : index ≤ children.length) (childFound : elementAt progress.1 child = some childRecord)
    (childLocal : childRecord.document = document) (detached : childRecord.parent = none)
    (notRoot : rootOf progress.1 document ≠ some child)
    (under : (View.Below (elementAt progress.1)) element child) :
    step author operation document context progress
      (.editElement ⟨element, revision, .splice index child⟩) = .error .cycle := by
  have unclear : clearOf (treeFuel progress.1) progress.1 element child = false := by
    cases clear : clearOf (treeFuel progress.1) progress.1 element child with
    | false => rfl
    | true => exact absurd under (clearOf_sound _ _ _ _ clear)
  have opened : openContainer progress.1 document element revision operation = .ok (record, children) := by
    simp [openContainer, found, local_, body, current]
  simp only [step, editElementStep, opened, bind, Except.bind, inRange, if_true, childFound,
    childLocal, detached, ne_eq, not_true_eq_false, if_false, Option.isSome_none, Bool.false_or,
    decide_eq_true_eq, notRoot, unclear, decide_false]
  rfl

/-- An edit against a container whose children moved since the revision its
author read — by another operation — is refused `staleElement`. -/
theorem stale_element_refused (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress : Progress) (edit : EditElement)
    {record : ElementRecord} {children : List ElementId}
    (found : elementAt progress.1 edit.element = some record) (local_ : record.document = document)
    (body : record.body = .container children)
    (moved : record.revision ≠ edit.revision) (byAnother : record.revision ≠ operation) :
    step author operation document context progress (.editElement edit) = .error .staleElement := by
  have opened : openContainer progress.1 document edit.element edit.revision operation =
      .error .staleElement := by
    simp [openContainer, found, local_, body, moved, byAnother]
  simp only [step, editElementStep, opened, bind, Except.bind]

/-- The admitted pole of the stale check: a move against the revision its author
read, of a child of the container, to a position inside it, is admitted. -/
theorem move_admitted (author : PrincipalRef) (operation : OperationId) (document : DocumentId)
    (context : Context) (progress : Progress) {element child : ElementId} {revision : OperationId}
    {index : Nat} {record : ElementRecord} {children : List ElementId}
    (found : elementAt progress.1 element = some record) (local_ : record.document = document)
    (body : record.body = .container children) (current : record.revision = revision)
    (member : child ∈ children) (inRange : index < children.length) :
    ∃ next, step author operation document context progress
      (.editElement ⟨element, revision, .move child index⟩) = .ok next := by
  have opened : openContainer progress.1 document element revision operation = .ok (record, children) := by
    simp [openContainer, found, local_, body, current]
  simp only [step, editElementStep, opened, bind, Except.bind, member, if_true, inRange,
    rewriteElement, found]
  exact ⟨_, rfl⟩

/-- The admitted pole of the cycle check: a splice whose check passes is
admitted, and (by `clearOf_sound`) such a splice never places an element under
itself. -/
theorem splice_admitted_shape (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress : Progress) {element child : ElementId}
    {revision : OperationId} {index : Nat} {record childRecord : ElementRecord}
    {children : List ElementId}
    (found : elementAt progress.1 element = some record) (local_ : record.document = document)
    (body : record.body = .container children) (current : record.revision = revision)
    (inRange : index ≤ children.length) (childFound : elementAt progress.1 child = some childRecord)
    (childLocal : childRecord.document = document) (detached : childRecord.parent = none)
    (notRoot : rootOf progress.1 document ≠ some child)
    (clear : clearOf (treeFuel progress.1) progress.1 element child = true) :
    ∃ next, step author operation document context progress
      (.editElement ⟨element, revision, .splice index child⟩) = .ok next := by
  have opened : openContainer progress.1 document element revision operation = .ok (record, children) := by
    simp [openContainer, found, local_, body, current]
  have distinct := clearOf_ne clear
  simp only [step, editElementStep, opened, bind, Except.bind, inRange, if_true, childFound,
    childLocal, detached, ne_eq, not_true_eq_false, if_false, Option.isSome_none, Bool.false_or,
    decide_eq_true_eq, notRoot, clear, decide_false, rewriteElement, found, reparent]
  rw [if_neg Bool.false_ne_true, elementAt_set_element, Function.update_of_ne (Ne.symm distinct),
    childFound]
  exact ⟨_, rfl⟩

/-! ## The field an element edit writes -/

/-- An element edit is a write of the document's `body` field — the tree is
the body's structure: reordering lines changes what the document says — and
writes nothing in `annotations`.  So the holder's scope must name `body` on the
document: a law or a K-FIELDS scope naming only `annotations` refuses it, as it
refuses an atom edit (`edit_is_body_write`).  An annotation has no place of its
own to edit: its place is its anchor's. -/
theorem editElement_requires_grant (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) {progress next : Progress} (edit : EditElement)
    (accepted : step author operation document context progress (.editElement edit) = .ok next)
    (notYetMoved : ∀ record, elementAt progress.1 edit.element = some record →
      record.revision ≠ operation) :
    0 < bodyWrites progress.1 next.1 ∧ annotationWrites progress.1 next.1 = 0 := by
  have stepped := editElementStep_step operation document accepted
  have stamped : ∃ before after, elementAt progress.1 edit.element = some before ∧
      elementAt next.1 edit.element = some after ∧ after.revision = operation := by
    obtain ⟨element, revision, op⟩ := edit
    cases op with
    | splice index child =>
        obtain ⟨record, children, _, found, _, _, _, _, _, _, _, _, clear, post⟩ := splice_ok accepted
        refine ⟨record, withChildren record (children.insertIdx index child) operation, found, ?_, rfl⟩
        rw [post, elementAt_set_element, elementAt_set_element,
          Function.update_of_ne (clearOf_ne clear), Function.update_self]
    | move child index =>
        obtain ⟨record, children, found, _, _, _, _, _, post⟩ := move_ok accepted
        refine ⟨record, withChildren record ((children.erase child).insertIdx index child) operation,
          found, ?_, rfl⟩
        rw [post, elementAt_set_element, Function.update_self]
    | remove child =>
        obtain ⟨record, children, childRecord, found, _, _, _, _, childFound, post⟩ := remove_ok accepted
        by_cases same : element = child
        · subst same
          rw [elementAt_set_element, Function.update_self] at childFound
          obtain rfl := Option.some.inj childFound
          refine ⟨record, { withChildren record (children.erase element) operation with parent := none },
            found, ?_, rfl⟩
          rw [post, elementAt_set_element, Function.update_self]
        · refine ⟨record, withChildren record (children.erase child) operation, found, ?_, rfl⟩
          rw [post, elementAt_set_element, elementAt_set_element, Function.update_of_ne same,
            Function.update_self]
  obtain ⟨before, after, found, written, revised⟩ := stamped
  refine ⟨?_, ?_⟩
  · apply Finset.card_pos.mpr
    refine ⟨⟨.elements, edit.element⟩, ?_⟩
    simp only [changedIn, Finset.mem_filter, Finset.mem_union, DFinsupp.mem_support_iff]
    have pre : progress.1 ⟨.elements, edit.element⟩ = some before := found
    have post : next.1 ⟨.elements, edit.element⟩ = some after := written
    refine ⟨Or.inl ?_, rfl, ?_⟩
    · rw [pre]
      exact Option.some_ne_none before
    · rw [pre, post]
      intro same
      exact notYetMoved before found (by rw [Option.some.inj same]; exact revised)
  · unfold annotationWrites
    rw [changedIn_empty_of_agree true progress.1 next.1]
    · rfl
    intro address annotation
    apply stepped.2
    intro isElements
    rw [isElements] at annotation
    exact Bool.noConfusion annotation

/-! ## A transclusion placed at line N -/

/-- The exit row, in the kernel: in a flat document, the command "transclude,
then move the transclusion's embed to position `index` of the root" puts the
transclusion at line `index` of the document order, and that line is the
`embed` of exactly that transclusion. -/
theorem transclusion_at_line (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) {pre : ContentStore} {next : Progress}
    {root : ElementId} {transclusion : TransclusionId} {link : LinkId}
    {request : TranscludeRequest} {revision : OperationId} {index : Nat}
    (tree : DocumentTree pre document) (rooted : rootOf pre document = some root)
    (flat : ∀ child ∈ childrenOf pre root, childrenOf pre child = [])
    (accepted : run author operation document context pre
      ⟨[.transclude transclusion link request,
        .editElement ⟨root, revision, .move (transclusionElement transclusion) index⟩]⟩ = .ok next) :
    (documentOrder next.1 document)[index]? = some (transclusionElement transclusion) ∧
      (elementAt next.1 (transclusionElement transclusion)).map ElementRecord.body =
        some (.embed transclusion) := by
  simp only [run, List.foldlM_cons, List.foldlM_nil, bind, Except.bind] at accepted
  cases first : step author operation document context (pre, []) (.transclude transclusion link request) with
  | error reason => simp [first] at accepted
  | ok middle =>
  have stepOne := first
  simp only [first] at accepted
  cases second : step author operation document context middle
      (.editElement ⟨root, revision, .move (transclusionElement transclusion) index⟩) with
  | error reason => simp [second] at accepted
  | ok final =>
  simp only [second, pure, Except.pure, Except.ok.injEq] at accepted
  subst accepted
  -- the transclude step: two allocations off the tree, then the append
  cases covered : context.sourceRead request.source with
  | none => simp [step, covered] at first
  | some read =>
  simp only [step, covered] at first
  obtain ⟨one, oneOk, rest⟩ := bind_eq_ok first
  obtain ⟨two, twoOk, last⟩ := bind_eq_ok rest
  obtain ⟨_, rfl⟩ := allocate_ok oneOk
  obtain ⟨_, rfl⟩ := allocate_ok twoOk
  dsimp only at last
  have sameElements : ∀ (one : Option (Value .transclusions)) (two : Option (Value .links)),
      elementAt ((pre.set ⟨.transclusions, transclusion⟩ one).set ⟨.links, link⟩ two) =
        elementAt pre := by
    intro one two
    rw [elementAt_set_other _ _ _ (by simp), elementAt_set_other _ _ _ (by simp)]
  have sameRoot : ∀ (one : Option (Value .transclusions)) (two : Option (Value .links)),
      rootOf ((pre.set ⟨.transclusions, transclusion⟩ one).set ⟨.links, link⟩ two) document =
        rootOf pre document := by
    intro one two
    rw [rootOf_set_other _ _ _ _ (by simp), rootOf_set_other _ _ _ _ (by simp)]
  obtain ⟨record, children, found, body, absent, distinct, appended⟩ :=
    appendLeaf_ok ((sameRoot _ _).trans rooted) last
  rw [sameElements] at found absent appended
  have treeMiddle : DocumentTree middle.1 document :=
    step_tree author operation document context (progress := (pre, []))
      (action := .transclude transclusion link request) tree stepOne
  have rootedMiddle : rootOf middle.1 document = some root := by
    rw [rootOf_of_elementStep (appendLeaf_step author operation document last)]
    exact (sameRoot _ _).trans rooted
  -- the move step
  obtain ⟨recordM, childrenM, foundM, _, bodyM, _, member, inRange, post⟩ := move_ok second
  have fits : index ≤ (childrenM.erase (transclusionElement transclusion)).length := by
    rw [List.length_erase_of_mem member]
    omega
  have finalChildren : childrenOf final.1 root =
      (childrenM.erase (transclusionElement transclusion)).insertIdx index
        (transclusionElement transclusion) := by
    rw [childrenOf_eq, post, elementAt_set_element, update_children]
    simp [withChildren, bodyChildren]
  have middleChildren : childrenOf middle.1 root = childrenM := by
    simp [childrenOf, foundM, bodyM, bodyChildren]
  have oldChildren : childrenOf pre root = children := by
    simp [childrenOf, found, body, bodyChildren]
  have appendedChildren : childrenOf middle.1 root = children ++ [transclusionElement transclusion] := by
    rw [childrenOf_eq, appended, update_children, update_children]
    simp [distinct.symm, bodyChildren]
  -- every child of the root stays a leaf
  have leafAt : ∀ child ∈ childrenOf final.1 root, childrenOf final.1 child = [] := by
    intro child inside
    rw [finalChildren] at inside
    have inMiddle : child ∈ childrenM := by
      rcases List.mem_cons.mp ((List.perm_insertIdx _ _ fits).subset inside) with same | old
      · rw [same]
        exact member
      · exact List.mem_of_mem_erase old
    have notRoot : child ≠ root := by
      intro same
      subst same
      have := treeMiddle.forest.parented _ _ (by rw [← childrenOf_eq, middleChildren]; exact inMiddle)
      rw [(treeMiddle.root _ rootedMiddle).2] at this
      cases this
    have finalEq : childrenOf final.1 child = childrenOf middle.1 child := by
      rw [childrenOf_eq, childrenOf_eq, post, elementAt_set_element, update_children]
      simp [notRoot]
    rw [finalEq, childrenOf_eq, appended, update_children, update_children]
    by_cases isLeaf : child = transclusionElement transclusion
    · simp [isLeaf, leafRecord, bodyChildren]
    · rw [← middleChildren, appendedChildren] at inMiddle
      rcases List.mem_append.mp inMiddle with old | new
      · simp only [isLeaf, notRoot, if_false]
        rw [← childrenOf_eq]
        exact flat child (oldChildren ▸ old)
      · simp at new
        exact absurd new isLeaf
  have presentFinal : (elementAt final.1 root).isSome := by
    rw [post, elementAt_set_element]
    simp
  have rootedFinal : rootOf final.1 document = some root := by
    rw [rootOf_of_elementStep (editElementStep_step operation document second)]
    exact rootedMiddle
  refine ⟨?_, ?_⟩
  · rw [documentOrder_flat rootedFinal presentFinal leafAt, finalChildren, List.getElem?_insertIdx_self]
    simp [fits]
  · have notRoot : transclusionElement transclusion ≠ root := distinct
    rw [post, elementAt_set_element, Function.update_of_ne notRoot, appended, Function.update_self]
    rfl

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.ContentResource.tree_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tree_acyclic
/-- info: 'Minidregg.Kernel.ContentResource.order_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms order_total
/-- info: 'Minidregg.Kernel.ContentResource.splice_places' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms splice_places
/-- info: 'Minidregg.Kernel.ContentResource.move_preserves_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms move_preserves_set
/-- info: 'Minidregg.Kernel.ContentResource.remove_detaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms remove_detaches
/-- info: 'Minidregg.Kernel.ContentResource.transclusion_at_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transclusion_at_line
/-- info: 'Minidregg.Kernel.ContentResource.editElement_requires_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms editElement_requires_grant
/-- info: 'Minidregg.Kernel.ContentResource.cycle_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cycle_refused
/-- info: 'Minidregg.Kernel.ContentResource.stale_element_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_element_refused
/-- info: 'Minidregg.Kernel.ContentResource.move_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms move_admitted
/-- info: 'Minidregg.Kernel.ContentResource.splice_admitted_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms splice_admitted_shape
/-- info: 'Minidregg.Kernel.ContentResource.clearOf_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms clearOf_sound

end Minidregg.Kernel.ContentResource
