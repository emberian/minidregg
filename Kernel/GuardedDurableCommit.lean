/-
# Kernel.GuardedDurableCommit -- authority-guarded Hyperdocument settlement

`HyperdocumentPublication` proves that the content cell and its causal event
log form one accepted two-cell hyperedge.  Authorization for both legs is,
however, projected from an authority cell which that hyperedge reads but does
not write.  A handler which compares only the two written pre-roots can install
an effect after the authority root has rotated or acquired a revocation.

This module closes that exact admission/commit race by adapting an accepted
publication to `DurableDataIntent.DataIntent` with three exact observations:

* content and event-log cells are data-bearing writes;
* the canonical authority cell is a read-only root guard;
* all three cells use one deployment digest function.

The resulting negative tooth is independent of why the authority root moved:
epoch rotation, revocation, capability attenuation, or nullifier consumption
all make an intent admitted against the old authority cell stale.  This is a
logical durable-settlement model.  Physical snapshot isolation and durability
still require `DurableDataIntent.ImplementationRefinement`.
-/
import Kernel.DurableDataIntent
import Kernel.HyperdocumentPublication

namespace Minidregg.Kernel.GuardedDurableCommit

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

/-! ## Exact wire projection of one accepted publication -/

/-- The stable envelopes which remain deployment-specific.  Nullifier
encoding is a function of each exact joint nullifier; the event envelope is
the value priced and journaled by the bounded durable quote below. -/
structure WireProjection (Nullifier : Type) where
  nullifier : Nullifier -> StableNullifier
  event : StableEvent

/-- One digest implementation serves the three deployed schemas.  Packaging
both equalities prevents an adapter from proving only the two write lanes while
silently comparing the authority lane under a different root function. -/
structure SharedDigestAgreement
    (MDoc : Hyperdocument.Materializer Digest)
    (MAuth : CredentialAuthorityState.Materializer)
    (representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest) :
    Prop where
  eventRootFunction : representation.rootBytes = MDoc.rootBytes
  authorityRootFunction : MAuth.rootBytes = MDoc.rootBytes

/-! ## Read-only installation invariant -/

private theorem lookupPost_none_of_not_mem
    (cellId : CellId) (writes : List (RootWrite CellId))
    (absent : cellId ∉ writes.map RootWrite.cellId) :
    Snapshot.lookupPost cellId writes = none := by
  induction writes with
  | nil => rfl
  | cons write rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp only [Snapshot.lookupPost]
      rw [if_neg (Ne.symm absent.1)]
      exact ih absent.2

private theorem lookupPostBytes_none_of_not_mem
    (cellId : CellId) (writes : List DataWrite)
    (absent : cellId ∉ writes.map DataWrite.cellId) :
    DataSnapshot.lookupPostBytes cellId writes = none := by
  induction writes with
  | nil => rfl
  | cons write rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      simp only [DataSnapshot.lookupPostBytes]
      rw [if_neg (Ne.symm absent.1)]
      exact ih absent.2

/-- Installation changes only write lanes.  A declared read guard retains both
its old root and its old canonical bytes in the atomically installed snapshot. -/
theorem install_preserves_read_guard
    {rootBytes : List UInt8 -> Digest}
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (guard : ReadGuard) (member : guard ∈ intent.readGuards) :
    (DataSnapshot.install before intent).model.roots guard.cellId =
        before.model.roots guard.cellId /\
      (DataSnapshot.install before intent).canonicalBytes guard.cellId =
        before.canonicalBytes guard.cellId := by
  have absent := intent.guardsReadOnly guard member
  have rootAbsent : guard.cellId ∉
      intent.erase.rootWrites.map RootWrite.cellId := by
    simpa [DataIntent.erase] using absent
  have rootNone := lookupPost_none_of_not_mem guard.cellId
    intent.erase.rootWrites rootAbsent
  have bytesNone := lookupPostBytes_none_of_not_mem guard.cellId
    intent.writes absent
  constructor
  · change (Snapshot.install before.model intent.erase).roots guard.cellId =
      before.model.roots guard.cellId
    rw [Snapshot.install_roots]
    change (Snapshot.lookupPost guard.cellId intent.erase.rootWrites).getD
      (before.model.roots guard.cellId) = before.model.roots guard.cellId
    rw [rootNone]
    rfl
  · change (DataSnapshot.lookupPostBytes guard.cellId intent.writes).getD
      (before.canonicalBytes guard.cellId) = before.canonicalBytes guard.cellId
    rw [bytesNone]
    rfl

/-- Adapt one accepted Hyperdocument content+event publication to the
payload-bearing durable protocol, adding the authority cell as a read guard.

The equalities between materializer root functions are not hash-security
claims.  They state that these three deployed schemas use the same digest
algorithm, which is necessary for one coherent `DataSnapshot` to store them.
The exact post bytes come from the two accepted `CellState.Materialized`
values, not from a handler-supplied byte buffer. -/
noncomputable def ofHyperdocumentPublication
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Kernel.HyperdocumentPublication.ContentAccepted
      contentConfig projection authorityPre documentPre contentPortal
      contentDeclaration}
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    {event : Minidregg.Kernel.HyperdocumentPublication.EventAccepted content
      representation store eventConfig eventPortal eventDeclaration}
    {header : Minidregg.Kernel.HyperdocumentPublication.Header}
    {contentCellId eventCellId authorityCellId : Digest}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (Minidregg.Kernel.HyperdocumentPublication.declaration content event header
        contentCellId eventCellId)}
    {publication : Minidregg.Kernel.MultiCellHyperedge.Commit
      (Minidregg.Kernel.HyperdocumentPublication.zeroResourceLaw content event header
        contentCellId eventCellId)
      (Minidregg.Kernel.HyperdocumentPublication.acceptedLegs content event header
        contentCellId eventCellId) boundary}
    (wire : WireProjection (Minidregg.Kernel.MultiCellHyperedge.JointNullifier
      (Minidregg.Kernel.HyperdocumentPublication.acceptedLegs content event header
        contentCellId eventCellId)))
    (bounded : BoundedMultiCellCommit publication StableEvent wire.event)
    (digestAgreement : SharedDigestAgreement MDoc MAuth representation)
    (authorityDistinctContent : authorityCellId ≠ contentCellId)
    (authorityDistinctEvent : authorityCellId ≠ eventCellId) :
    DataIntent MDoc.rootBytes where
  transactionId := header.turnId
  writes :=
    [{ cellId := contentCellId
       expectedPre := documentPre.root
       exactPost := (publication.post .content).root
       canonicalPostBytes := (publication.post .content).bytes },
     { cellId := eventCellId
       expectedPre := event.accepted.prepared.preRoot
       exactPost := (publication.post .eventLog).root
       canonicalPostBytes := (publication.post .eventLog).bytes }]
  readGuards :=
    [{ cellId := authorityCellId
       expectedRoot := MDoc.rootBytes authorityPre.bytes }]
  nullifiers := publication.nullifiers.map wire.nullifier
  exactCharge := bounded.quote.exact
  event := wire.event
  postRootsBound := by
    intro write member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · rfl
    · exact congrFun digestAgreement.eventRootFunction
        (publication.post .eventLog).bytes |>.symm
  guardsReadOnly := by
    intro guard member
    simp only [List.mem_singleton] at member
    subst guard
    simp [authorityDistinctContent, authorityDistinctEvent]

/-! ## Projection facts: two writes and one read-only authority guard -/

@[simp] theorem ofHyperdocumentPublication_readGuards
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Kernel.HyperdocumentPublication.ContentAccepted
      contentConfig projection authorityPre documentPre contentPortal
      contentDeclaration}
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    {event : Minidregg.Kernel.HyperdocumentPublication.EventAccepted content
      representation store eventConfig eventPortal eventDeclaration}
    {header : Minidregg.Kernel.HyperdocumentPublication.Header}
    {contentCellId eventCellId authorityCellId : Digest}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (Minidregg.Kernel.HyperdocumentPublication.declaration content event header
        contentCellId eventCellId)}
    {publication : Minidregg.Kernel.MultiCellHyperedge.Commit
      (Minidregg.Kernel.HyperdocumentPublication.zeroResourceLaw content event header
        contentCellId eventCellId)
      (Minidregg.Kernel.HyperdocumentPublication.acceptedLegs content event header
        contentCellId eventCellId) boundary}
    (wire : WireProjection (Minidregg.Kernel.MultiCellHyperedge.JointNullifier
      (Minidregg.Kernel.HyperdocumentPublication.acceptedLegs content event header
        contentCellId eventCellId)))
    (bounded : BoundedMultiCellCommit publication StableEvent wire.event)
    (digestAgreement : SharedDigestAgreement MDoc MAuth representation)
    (authorityDistinctContent : authorityCellId ≠ contentCellId)
    (authorityDistinctEvent : authorityCellId ≠ eventCellId) :
    (ofHyperdocumentPublication wire bounded digestAgreement
      authorityDistinctContent authorityDistinctEvent).readGuards =
      [{ cellId := authorityCellId, expectedRoot := authorityPre.root }] := by
  simp [ofHyperdocumentPublication, CellState.Materialized.root,
    digestAgreement.authorityRootFunction]

@[simp] theorem ofHyperdocumentPublication_writes_length
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Kernel.HyperdocumentPublication.ContentAccepted
      contentConfig projection authorityPre documentPre contentPortal
      contentDeclaration}
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    {event : Minidregg.Kernel.HyperdocumentPublication.EventAccepted content
      representation store eventConfig eventPortal eventDeclaration}
    {header : Minidregg.Kernel.HyperdocumentPublication.Header}
    {contentCellId eventCellId authorityCellId : Digest}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (Minidregg.Kernel.HyperdocumentPublication.declaration content event header
        contentCellId eventCellId)}
    {publication : Minidregg.Kernel.MultiCellHyperedge.Commit
      (Minidregg.Kernel.HyperdocumentPublication.zeroResourceLaw content event header
        contentCellId eventCellId)
      (Minidregg.Kernel.HyperdocumentPublication.acceptedLegs content event header
        contentCellId eventCellId) boundary}
    (wire : WireProjection (Minidregg.Kernel.MultiCellHyperedge.JointNullifier
      (Minidregg.Kernel.HyperdocumentPublication.acceptedLegs content event header
        contentCellId eventCellId)))
    (bounded : BoundedMultiCellCommit publication StableEvent wire.event)
    (digestAgreement : SharedDigestAgreement MDoc MAuth representation)
    (authorityDistinctContent : authorityCellId ≠ contentCellId)
    (authorityDistinctEvent : authorityCellId ≠ eventCellId) :
    (ofHyperdocumentPublication wire bounded digestAgreement
      authorityDistinctContent authorityDistinctEvent).writes.length = 2 :=
  rfl

/-! ## Authority TOCTOU rejection -/

/-- **Authority TOCTOU tooth.**  If the canonical authority root observed at
admission is no longer current, the old content+event publication is rejected
at the durable barrier.  Any authority-cell mutation is covered, including an
epoch rotation or insertion of a revocation, without reinterpreting its
logical payload in the handler. -/
theorem authority_rotation_or_revocation_rejects_old_publication
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Kernel.HyperdocumentPublication.ContentAccepted
      contentConfig projection authorityPre documentPre contentPortal
      contentDeclaration}
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    {event : Minidregg.Kernel.HyperdocumentPublication.EventAccepted content
      representation store eventConfig eventPortal eventDeclaration}
    {header : Minidregg.Kernel.HyperdocumentPublication.Header}
    {contentCellId eventCellId authorityCellId : Digest}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (Minidregg.Kernel.HyperdocumentPublication.declaration content event header
        contentCellId eventCellId)}
    {publication : Minidregg.Kernel.MultiCellHyperedge.Commit
      (Minidregg.Kernel.HyperdocumentPublication.zeroResourceLaw content event header
        contentCellId eventCellId)
      (Minidregg.Kernel.HyperdocumentPublication.acceptedLegs content event header
        contentCellId eventCellId) boundary}
    (wire : WireProjection (Minidregg.Kernel.MultiCellHyperedge.JointNullifier
      (Minidregg.Kernel.HyperdocumentPublication.acceptedLegs content event header
        contentCellId eventCellId)))
    (bounded : BoundedMultiCellCommit publication StableEvent wire.event)
    (digestAgreement : SharedDigestAgreement MDoc MAuth representation)
    (authorityDistinctContent : authorityCellId ≠ contentCellId)
    (authorityDistinctEvent : authorityCellId ≠ eventCellId)
    (current : DataSnapshot MDoc.rootBytes)
    (authorityMoved : current.model.roots authorityCellId ≠ authorityPre.root) :
    (ofHyperdocumentPublication wire bounded digestAgreement
      authorityDistinctContent authorityDistinctEvent).preflight current =
      .error .staleReadGuard := by
  apply stale_read_guard_rejected
  let guard : ReadGuard :=
    { cellId := authorityCellId
      expectedRoot := MDoc.rootBytes authorityPre.bytes }
  have expectedExact : guard.expectedRoot = authorityPre.root :=
    congrFun digestAgreement.authorityRootFunction authorityPre.bytes |>.symm
  refine ⟨guard, ?_, ?_⟩
  · simp [guard, ofHyperdocumentPublication]
  · have notEqual :
        current.model.roots guard.cellId ≠ guard.expectedRoot := by
      intro equal
      apply authorityMoved
      exact equal.trans expectedExact
    simpa using notEqual

end Minidregg.Kernel.GuardedDurableCommit

/-! Kernel-facing theorem audit. -/

/-- info: 'Minidregg.Kernel.GuardedDurableCommit.install_preserves_read_guard' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Kernel.GuardedDurableCommit.install_preserves_read_guard
/-- info: 'Minidregg.Kernel.GuardedDurableCommit.authority_rotation_or_revocation_rejects_old_publication' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Kernel.GuardedDurableCommit.authority_rotation_or_revocation_rejects_old_publication
