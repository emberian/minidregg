/-
# Kernel.ContentMarks — marks on a line, in the annotations field (K-MARKS)

A `mark` lays a `MarkRecord` on one atom (a line) or one element at the
revision its author read; a `link` mark also writes one ordinary `LinkRecord`,
which is primary (backlinks and `Kernel.LinkIndex` read it) while the mark
names it and places it on the line.  `unmark` retires a live mark — its author
or the document's owner only — and a link mark's link with it.

What is proved here, over the kernel's own `step`:

* `mark_preserves_body` — a mark or unmark changes no record outside the
  annotations field (so no body byte, `bodyWrites = 0`) and leaves the
  document order exactly as it was;
* `mark_pinned_by_revision` — an admitted mark stands on a target that was at
  the named revision, stores exactly that anchor, and is fresh after;
  `stale_mark_refused` / `no_such_target_refused` are the refused poles;
* `mark_stale_after_edit` — an edit of the marked line by any other operation
  makes the mark stale (it is never re-anchored);
* `mark_requires_grant` — a mark writes the annotations field and nothing in
  the body, so `fields = {annotations}` covers it and covers no edit
  (`edit_is_body_write`);
* `unmark_requires_author_or_owner` — an admitted unmark was by the mark's
  author or the document's owner; `not_mark_owner_refused` and
  `mark_not_found_refused` are the refused poles;
* `link_mark_is_a_link` — a link mark yields exactly one new live link in the
  cell's link fold (`LinkIndex.linksOfStore`, what the backlink index reads),
  with the mark's target;
* `unmark_removes_link` — after unmark of a link mark its link is no longer
  live in that fold, and the mark is retired.
-/
import Kernel.ContentElementTree
import Kernel.LinkIndex

namespace Minidregg.Kernel.ContentResource

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations

set_option autoImplicit false

/-! ## The order is a function of the tree -/

theorem elementCount_congr {store store' : ContentStore}
    (same : ∀ element : ElementId, store' ⟨.elements, element⟩ = store ⟨.elements, element⟩) :
    elementCount store' = elementCount store := by
  unfold elementCount
  congr 1
  ext address
  rcases address with ⟨space, key⟩
  cases space
  case elements =>
    simp only [Finset.mem_filter, DFinsupp.mem_support_iff]
    rw [same key]
  all_goals simp

theorem walk_congr {store store' : ContentStore} (same : elementAt store' = elementAt store) :
    ∀ (fuel : Nat) (element : ElementId), walk fuel store' element = walk fuel store element
  | 0, _ => rfl
  | fuel + 1, element => by
      have inner : walk fuel store' = walk fuel store := funext (walk_congr same fuel)
      have children : childrenOf store' element = childrenOf store element := by
        rw [childrenOf_eq, childrenOf_eq, same]
      simp only [walk, children, inner]

theorem documentOrder_congr {store store' : ContentStore} {document : DocumentId}
    (sameElements : ∀ element : ElementId, store' ⟨.elements, element⟩ = store ⟨.elements, element⟩)
    (sameRoot : rootOf store' document = rootOf store document) :
    documentOrder store' document = documentOrder store document := by
  have elements : elementAt store' = elementAt store := funext fun element => sameElements element
  have fuel : treeFuel store' = treeFuel store := by
    unfold treeFuel
    rw [elementCount_congr sameElements]
  unfold documentOrder
  rw [sameRoot]
  cases rootOf store document with
  | none => rfl
  | some root => simp only [fuel, walk_congr elements]

/-! ## Frames of the two actions -/

theorem markTargetRevision_of_markStep {progress next : Progress} (stepped : MarkStep progress next)
    (document : DocumentId) (target : MarkTarget) :
    markTargetRevision next.1 document target = markTargetRevision progress.1 document target := by
  cases target with
  | atom line =>
      have same : Hyperdocument.lookup next.1 .atoms line = Hyperdocument.lookup progress.1 .atoms line :=
        stepped.2 ⟨.atoms, line⟩ (by simp) (by simp)
      simp only [markTargetRevision, same]
  | element target =>
      simp only [markTargetRevision, elementAt_of_markStep stepped]

theorem markLinkStep_links {author : PrincipalRef} {operation : OperationId} {document : DocumentId}
    {progress next : Progress} {spec : MarkSpec}
    (accepted : markLinkStep author operation document progress spec = .ok next)
    (address : Hyperdocument.Address) (notLinks : address.1 ≠ .links) :
    next.1 address = progress.1 address := by
  cases spec with
  | link linkId target =>
      obtain ⟨_, rfl⟩ := allocate_ok accepted
      exact Store.Store.set_ne _ _ _ address (fun same => notLinks (congrArg Sigma.fst same))
  | bold | italic | code | heading =>
      simp only [markLinkStep, Except.ok.injEq] at accepted
      subst accepted
      rfl

theorem retireMarkLink_links {document : DocumentId} {operation : OperationId}
    {progress next : Progress} {kind : MarkKind}
    (accepted : retireMarkLink document operation progress kind = .ok next)
    (address : Hyperdocument.Address) (notLinks : address.1 ≠ .links) :
    next.1 address = progress.1 address := by
  cases kind with
  | link linkId =>
      simp only [retireMarkLink] at accepted
      split at accepted
      · cases accepted
        rfl
      · obtain ⟨_, _, _, _, rfl⟩ := retireLink_ok accepted
        exact Store.Store.set_ne _ _ _ address (fun same => notLinks (congrArg Sigma.fst same))
  | bold | italic | code | heading =>
      simp only [retireMarkLink, Except.ok.injEq] at accepted
      subst accepted
      rfl

/-- The record an admitted mark stores, at the mark's address of the post. -/
theorem mark_stored {author : PrincipalRef} {operation : OperationId} {document : DocumentId}
    {progress next : Progress} {mark : MarkId} {request : MarkRequest}
    (accepted : markStep author operation document progress mark request = .ok next) :
    Hyperdocument.lookup next.1 .marks mark = some (markRecordOf author operation document request) ∧
      Hyperdocument.lookup progress.1 .marks mark = none := by
  obtain ⟨_, _, middle, first, rest⟩ := markStep_ok accepted
  obtain ⟨fresh, rfl⟩ := allocate_ok first
  refine ⟨?_, fresh⟩
  unfold Hyperdocument.lookup
  rw [markLinkStep_links rest ⟨.marks, mark⟩ (by simp), Store.Store.set_eq]
  try exact rfl

/-! ## The theorems -/

/-- A mark or unmark changes no record outside the annotations field — no
atom, run, element or document, so no body byte — and the document order is
exactly what it was.  The `annotate_preserves_body` analog for marks. -/
theorem mark_preserves_body (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) {progress next : Progress} {action : Action}
    (marking : (∃ mark request, action = .mark mark request) ∨ ∃ mark, action = .unmark mark)
    (accepted : step author operation document context progress action = .ok next) :
    (∀ address : Hyperdocument.Address, annotationNamespace address.1 = false →
      next.1 address = progress.1 address) ∧
      bodyWrites progress.1 next.1 = 0 ∧
      documentOrder next.1 document = documentOrder progress.1 document := by
  have stepped : MarkStep progress next := by
    rcases marking with ⟨mark, request, rfl⟩ | ⟨mark, rfl⟩
    · exact markStep_markStep accepted
    · exact unmarkStep_markStep accepted
  have body : ∀ address : Hyperdocument.Address, annotationNamespace address.1 = false →
      next.1 address = progress.1 address := by
    intro address outside
    apply stepped.2 address
    · intro marks
      rw [marks] at outside
      cases outside
    · intro links
      rw [links] at outside
      cases outside
  refine ⟨body, ?_, ?_⟩
  · unfold bodyWrites
    rw [changedIn_empty_of_agree false progress.1 next.1 body]
    rfl
  · exact documentOrder_congr (fun element => body ⟨.elements, element⟩ rfl)
      (rootOf_of_markStep stepped document)

/-- An admitted mark was laid on a target of this document standing at the
named revision (not a write of this same command); it stores exactly that
anchor and kind, and it is fresh in the post. -/
theorem mark_pinned_by_revision (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) {progress next : Progress} {mark : MarkId}
    {request : MarkRequest}
    (accepted : step author operation document context progress (.mark mark request) = .ok next) :
    markTargetRevision progress.1 document request.target = some request.revision ∧
      request.revision ≠ operation ∧
      Hyperdocument.lookup next.1 .marks mark = some (markRecordOf author operation document request) ∧
      (markRecordOf author operation document request).anchor =
        request.target.anchor request.revision ∧
      markFresh next.1 (markRecordOf author operation document request) = true := by
  simp only [step] at accepted
  obtain ⟨found, unread, _⟩ := markStep_ok accepted
  have stepped := markStep_markStep accepted
  refine ⟨found, unread, (mark_stored accepted).1, rfl, ?_⟩
  have kept := markTargetRevision_of_markStep stepped document request.target
  rw [found] at kept
  cases target : request.target with
  | atom line =>
      rw [target] at kept
      simp [markFresh, markRecordOf, MarkTarget.anchor, target, kept]
  | element element =>
      rw [target] at kept
      simp [markFresh, markRecordOf, MarkTarget.anchor, target, kept]

/-- A mark whose target stands at another revision is refused `staleMark`,
before anything is written. -/
theorem stale_mark_refused (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress : Progress) (mark : MarkId)
    (request : MarkRequest) {current : OperationId}
    (found : markTargetRevision progress.1 document request.target = some current)
    (moved : current ≠ request.revision) :
    step author operation document context progress (.mark mark request) = .error .staleMark := by
  simp [step, markStep, found, moved]

/-- A mark naming no atom or element of this document is refused `noSuchTarget`. -/
theorem no_such_target_refused (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress : Progress) (mark : MarkId)
    (request : MarkRequest) (absent : markTargetRevision progress.1 document request.target = none) :
    step author operation document context progress (.mark mark request) = .error .noSuchTarget := by
  simp [step, markStep, absent]

/-- An admitted edit of the marked line, by any operation other than the
anchored revision, leaves the mark stale: never re-anchored, never shown as
current. -/
theorem mark_stale_after_edit (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) {progress next : Progress}
    (edit : EditAtomPayload) (record : MarkRecord) {revision : OperationId}
    (anchored : record.anchor = .atom edit.atomId revision) (later : operation ≠ revision)
    (accepted : step author operation document context progress (.editAtom edit) = .ok next) :
    markFresh next.1 record = false := by
  simp only [step] at accepted
  unfold replaceAtom at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · cases accepted
      have stored : Hyperdocument.lookup
          (progress.1.set ⟨.atoms, edit.atomId⟩ (some (editAtomRecord operation edit))) .atoms
          edit.atomId = some (editAtomRecord operation edit) := by
        unfold Hyperdocument.lookup
        rw [Store.Store.set_eq]
        try exact rfl
      simp only [markFresh, anchored, markTargetRevision, stored, editAtomRecord_revision]
      split <;> simp [later]

/-- A mark writes the annotations field and nothing of the body: a capability
scoped to `fields = {annotations}` covers it, and (`edit_is_body_write`) such
a capability covers no edit of the line. -/
theorem mark_requires_grant (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) {progress next : Progress} {mark : MarkId}
    {request : MarkRequest}
    (accepted : step author operation document context progress (.mark mark request) = .ok next) :
    0 < annotationWrites progress.1 next.1 ∧ bodyWrites progress.1 next.1 = 0 := by
  refine ⟨?_, (mark_preserves_body author operation document context
    (Or.inl ⟨mark, request, rfl⟩) accepted).2.1⟩
  simp only [step] at accepted
  obtain ⟨stored, fresh⟩ := mark_stored accepted
  unfold Hyperdocument.lookup at stored fresh
  apply Finset.card_pos.mpr
  refine ⟨⟨.marks, mark⟩, Finset.mem_filter.mpr ⟨?_, rfl, ?_⟩⟩
  · apply Finset.mem_union_right
    apply DFinsupp.mem_support_iff.mpr
    intro zero
    have absent : (next.1 ⟨.marks, mark⟩ : Option MarkRecord) = none := zero
    rw [stored] at absent
    cases absent
  · intro same
    have both : (progress.1 ⟨.marks, mark⟩ : Option MarkRecord) = next.1 ⟨.marks, mark⟩ := same
    rw [stored, fresh] at both
    cases both

/-- An admitted unmark retired a live mark of this document, and its author
was the mark's author or the document's owner. -/
theorem unmark_requires_author_or_owner (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) {progress next : Progress} {mark : MarkId}
    (accepted : step author operation document context progress (.unmark mark) = .ok next) :
    ∃ record, Hyperdocument.lookup progress.1 .marks mark = some record ∧
      record.document = document ∧ record.tombstonedAt = none ∧
      (author = record.author ∨ documentOwner progress.1 document = some author) := by
  simp only [step] at accepted
  obtain ⟨record, present, local_, live, may, _⟩ := unmarkStep_ok accepted
  exact ⟨record, present, local_, live, may⟩

/-- Anyone else is refused `notMarkOwner`, before anything is written. -/
theorem not_mark_owner_refused (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress : Progress) (mark : MarkId)
    {record : MarkRecord} (found : Hyperdocument.lookup progress.1 .marks mark = some record)
    (local_ : record.document = document) (live : record.tombstonedAt = none)
    (stranger : author ≠ record.author) (notOwner : documentOwner progress.1 document ≠ some author) :
    step author operation document context progress (.unmark mark) = .error .notMarkOwner := by
  unfold Hyperdocument.lookup at found
  simp [step, unmarkStep, found, local_, live, stranger, notOwner]

/-- An unmark naming no mark is refused `markNotFound`. -/
theorem mark_not_found_refused (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) (progress : Progress) (mark : MarkId)
    (absent : Hyperdocument.lookup progress.1 .marks mark = none) :
    step author operation document context progress (.unmark mark) = .error .markNotFound := by
  unfold Hyperdocument.lookup at absent
  simp [step, unmarkStep, absent]

/-! ## A link mark is a link -/

theorem mem_entries {L : Store.Layout} (W : StoreCodec.Wire L) (store : Store.Store L)
    (address : Store.Address L) (value : L.Value address.1) :
    (⟨address, value⟩ : Store.Entry L) ∈ StoreCodec.entries W store ↔ store address = some value := by
  unfold StoreCodec.entries
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨other, _, found⟩
    cases present : store other with
    | none => simp [present] at found
    | some stored =>
        simp only [present, Option.map_some, Option.some.injEq, Sigma.mk.injEq] at found
        obtain ⟨rfl, same⟩ := found
        cases same
        exact present
  · intro present
    refine ⟨address, (StoreCodec.mem_sortedSupport W store address).mpr (by simp [present]), ?_⟩
    simp [present]

/-- The live-link fold of a content store, which the link index is built from,
holds exactly the stored links that are not tombstoned. -/
theorem mem_linksOfStore {store : ContentStore} {link : LinkId} {record : LinkRecord} :
    (link, record) ∈ LinkIndex.linksOfStore store ↔
      Hyperdocument.lookup store .links link = some record ∧ record.tombstonedAt = none := by
  unfold LinkIndex.linksOfStore
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨⟨space, key⟩, value⟩, member, found⟩
    cases space
    case links =>
      simp only at found
      split at found
      · rename_i live
        simp only [Option.some.injEq, Prod.mk.injEq] at found
        obtain ⟨rfl, rfl⟩ := found
        exact ⟨(mem_entries HyperdocumentCell.contentWire store _ _).mp member, live⟩
      · cases found
    all_goals simp at found
  · rintro ⟨found, live⟩
    refine ⟨⟨⟨.links, link⟩, record⟩, (mem_entries HyperdocumentCell.contentWire store _ _).mpr found, ?_⟩
    simp [live]

/-- A link mark yields exactly one new live link of the cell, with the mark's
target and the mark relation, and the stored mark names it: backlinks (the
index built from `linksOfStore`) see it as an ordinary link. -/
theorem link_mark_is_a_link (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) {progress next : Progress} {mark : MarkId}
    {target : MarkTarget} {revision : OperationId} {link : LinkId} {linkTarget : LinkTarget}
    (accepted : step author operation document context progress
      (.mark mark ⟨target, revision, .link link linkTarget⟩) = .ok next) :
    (link, markLinkRecord author operation document linkTarget) ∈ LinkIndex.linksOfStore next.1 ∧
      (markLinkRecord author operation document linkTarget).target = linkTarget ∧
      (∀ other record, (other, record) ∈ LinkIndex.linksOfStore next.1 →
        (other, record) ∉ LinkIndex.linksOfStore progress.1 → other = link) ∧
      ∃ record, Hyperdocument.lookup next.1 .marks mark = some record ∧ record.kind = .link link := by
  simp only [step] at accepted
  obtain ⟨stored, _⟩ := mark_stored accepted
  obtain ⟨_, _, middle, first, rest⟩ := markStep_ok accepted
  obtain ⟨_, rfl⟩ := allocate_ok first
  simp only [markLinkStep] at rest
  obtain ⟨_, rfl⟩ := allocate_ok rest
  refine ⟨mem_linksOfStore.mpr ⟨?_, rfl⟩, rfl, ?_, ⟨_, stored, rfl⟩⟩
  · unfold Hyperdocument.lookup
    rw [Store.Store.set_eq]
    try exact rfl
  · intro other record inNext notBefore
    by_contra different
    apply notBefore
    obtain ⟨found, live⟩ := mem_linksOfStore.mp inNext
    refine mem_linksOfStore.mpr ⟨?_, live⟩
    unfold Hyperdocument.lookup at found ⊢
    rw [Store.Store.set_ne _ _ _ _ (fun same => different (by cases same; rfl)),
      Store.Store.set_ne _ _ _ _ (fun same => by cases same)] at found
    exact found

/-- After an admitted unmark of a link mark, that link is no longer live in
the cell's link fold (so backlinks drop it), and the mark itself is retired
by this operation. -/
theorem unmark_removes_link (author : PrincipalRef) (operation : OperationId)
    (document : DocumentId) (context : Context) {progress next : Progress} {mark : MarkId}
    {record : MarkRecord} {link : LinkId}
    (found : Hyperdocument.lookup progress.1 .marks mark = some record)
    (linked : record.kind = .link link)
    (accepted : step author operation document context progress (.unmark mark) = .ok next) :
    (∀ linkRecord, (link, linkRecord) ∉ LinkIndex.linksOfStore next.1) ∧
      ∃ after, Hyperdocument.lookup next.1 .marks mark = some after ∧
        after.tombstonedAt = some operation := by
  simp only [step] at accepted
  obtain ⟨before, present, _, _, _, rest⟩ := unmarkStep_ok accepted
  unfold Hyperdocument.lookup at found
  have same : before = record := by
    have both : (some before : Option MarkRecord) = some record := present.symm.trans found
    exact Option.some.inj both
  subst same
  refine ⟨?_, ⟨{ before with tombstonedAt := some operation }, ?_, rfl⟩⟩
  · intro linkRecord member
    obtain ⟨inNext, live⟩ := mem_linksOfStore.mp member
    rw [linked] at rest
    simp only [retireMarkLink] at rest
    split at rest
    · rename_i retired
      cases rest
      unfold linkRetired at retired
      unfold Hyperdocument.lookup at inNext retired
      rw [Store.Store.set_ne _ _ _ _ (fun same => by cases same)] at inNext retired
      rw [inNext] at retired
      simp [live] at retired
    · obtain ⟨_, _, _, _, rfl⟩ := retireLink_ok rest
      unfold Hyperdocument.lookup at inNext
      rw [Store.Store.set_eq] at inNext
      cases inNext
      simp at live
  · unfold Hyperdocument.lookup
    rw [retireMarkLink_links rest ⟨.marks, mark⟩ (by simp), Store.Store.set_eq]
    try exact rfl

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.ContentResource.mark_preserves_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mark_preserves_body
/-- info: 'Minidregg.Kernel.ContentResource.mark_pinned_by_revision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mark_pinned_by_revision
/-- info: 'Minidregg.Kernel.ContentResource.stale_mark_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_mark_refused
/-- info: 'Minidregg.Kernel.ContentResource.no_such_target_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_such_target_refused
/-- info: 'Minidregg.Kernel.ContentResource.mark_stale_after_edit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mark_stale_after_edit
/-- info: 'Minidregg.Kernel.ContentResource.mark_requires_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mark_requires_grant
/-- info: 'Minidregg.Kernel.ContentResource.unmark_requires_author_or_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unmark_requires_author_or_owner
/-- info: 'Minidregg.Kernel.ContentResource.not_mark_owner_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_mark_owner_refused
/-- info: 'Minidregg.Kernel.ContentResource.mark_not_found_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mark_not_found_refused
/-- info: 'Minidregg.Kernel.ContentResource.link_mark_is_a_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms link_mark_is_a_link
/-- info: 'Minidregg.Kernel.ContentResource.unmark_removes_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unmark_removes_link

end Minidregg.Kernel.ContentResource
