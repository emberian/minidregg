/-
# Assurance.HyperdocumentGuardedDurable -- one published operation, durably

`HyperdocumentAgentOperation.PublishedOperation` already retains the exact
accepted content effect and the exact content+event publication.  This module
connects that value directly to `GuardedDurableCommit`: there is no second
opaque joint input which may drift from the publication being installed.

The resulting plan is deliberately narrow.  It retains:

* the exact `PublishedOperation.publication` as its only commit;
* canonical bytes for both publication posts;
* the exact authority root observed by request-indexed authorization;
* stable nullifier and event envelopes in replay identity; and
* complete-install, retry, and stale-authority behavior.

This is still a logical durable-settlement boundary.  A database, filesystem,
or replicated service must separately discharge
`DurableDataIntent.ImplementationRefinement`; no physical durability is
asserted here.
-/
import Assurance.HyperdocumentAgentOperation
import Kernel.GuardedDurableCommit

namespace Minidregg.Assurance.HyperdocumentGuardedDurable

open Minidregg.Kernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.GuardedDurableCommit
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

variable
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : HyperdocumentOperations.Declaration}
    {content : HyperdocumentOperations.Accepted contentConfig projection
      authorityPre documentPre contentPortal contentDeclaration}
    {representation : HyperdocumentEventLog.Representation Digest}
    {store : HyperdocumentEventLog.Sparse.Store}
    {eventConfig : HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : HyperdocumentVersionEffects.Declaration}
    {event : HyperdocumentVersionEffects.Accepted content representation store
      eventConfig eventPortal eventDeclaration}
    {header : HyperdocumentPublication.Header}
    {contentCellId eventCellId : Digest}
    {boundary : MultiCellHyperedge.HandlerBoundary
      (HyperdocumentPublication.declaration content event header contentCellId
        eventCellId)}

local notation "PubAccepted" =>
  HyperdocumentPublication.acceptedLegs content event header contentCellId
    eventCellId

local notation "Published" =>
  HyperdocumentAgentOperation.PublishedOperation event header contentCellId
    eventCellId boundary

/-! ## The stronger, publication-indexed durable plan -/

/-- A payload-bearing durable plan indexed by the exact already-published
operation.  In contrast to `HyperdocumentAgentOperation.DurablePlan`, this
plan does not accept an additional opaque `JointCommitInput`: its bounded quote
is indexed by `operation.publication` itself, and its stable event becomes part
of the durable replay envelope. -/
structure PublicationPlan (operation : Published) (authorityCellId : Digest) where
  wire : WireProjection (MultiCellHyperedge.JointNullifier PubAccepted)
  bounded : BoundedMultiCellCommit operation.publication StableEvent wire.event
  digestAgreement : SharedDigestAgreement MDoc MAuth representation
  authorityDistinctContent : authorityCellId ≠ contentCellId
  authorityDistinctEvent : authorityCellId ≠ eventCellId

variable
    {operation : HyperdocumentAgentOperation.PublishedOperation event header
      contentCellId eventCellId boundary}
    {authorityCellId : Digest}

namespace PublicationPlan

/-- There is exactly one publication in this adapter: the value already
retained by the accepted user/agent operation. -/
def publication (_plan : PublicationPlan operation authorityCellId) :
    MultiCellHyperedge.Commit
      (HyperdocumentPublication.zeroResourceLaw content event header
        contentCellId eventCellId)
      PubAccepted boundary :=
  operation.publication

@[simp] theorem publication_eq_operation
    (plan : PublicationPlan operation authorityCellId) :
    plan.publication = operation.publication := rfl

/-- The published content post remains definitionally connected to the
finalized accepted content effect. -/
theorem publication_content_post_exact
    (plan : PublicationPlan operation authorityCellId) :
    plan.publication.post .content = content.accepted.prepared.post :=
  operation.contentPostExact

/-- The guarded durable intent is derived from the exact publication above.
Its two post images come from the publication, and its third observed cell is
the authorization state, retained as a read-only root guard. -/
noncomputable def toDataIntent
    (plan : PublicationPlan operation authorityCellId) :
    DataIntent MDoc.rootBytes :=
  ofHyperdocumentPublication plan.wire plan.bounded plan.digestAgreement
    plan.authorityDistinctContent plan.authorityDistinctEvent

@[simp] theorem intent_transactionId
    (plan : PublicationPlan operation authorityCellId) :
    plan.toDataIntent.transactionId = header.turnId := rfl

/-- Exact canonical post bytes and exact publication roots are retained for
both written cells.  This is the payload-bearing fact absent from the weaker
opaque durable plan. -/
@[simp] theorem intent_writes
    (plan : PublicationPlan operation authorityCellId) :
    plan.toDataIntent.writes =
      ([({ cellId := contentCellId
           expectedPre := documentPre.root
           exactPost := (operation.publication.post .content).root
           canonicalPostBytes := (operation.publication.post .content).bytes } :
          DataWrite),
        ({ cellId := eventCellId
           expectedPre := event.accepted.prepared.preRoot
           exactPost := (operation.publication.post .eventLog).root
           canonicalPostBytes := (operation.publication.post .eventLog).bytes } :
          DataWrite)] : List DataWrite) :=
  rfl

/-- The authority observation is exact: the admitted authority root, not an
adapter-selected digest, is the singleton durable read guard. -/
@[simp] theorem intent_readGuards
    (plan : PublicationPlan operation authorityCellId) :
    plan.toDataIntent.readGuards =
      ([({ cellId := authorityCellId, expectedRoot := authorityPre.root } :
          ReadGuard)] : List ReadGuard) := by
  exact ofHyperdocumentPublication_readGuards plan.wire plan.bounded
    plan.digestAgreement plan.authorityDistinctContent
    plan.authorityDistinctEvent

@[simp] theorem intent_writes_length
    (plan : PublicationPlan operation authorityCellId) :
    plan.toDataIntent.writes.length = 2 :=
  ofHyperdocumentPublication_writes_length plan.wire plan.bounded
    plan.digestAgreement plan.authorityDistinctContent
    plan.authorityDistinctEvent

/-- Erasure to the generic atomic protocol does not erase the payload-bearing
semantics: exact post bytes, exact authority guard, and the stable semantic
event are the journaled replay identity. -/
@[simp] theorem erased_replay_identity
    (plan : PublicationPlan operation authorityCellId) :
    plan.toDataIntent.erase.event =
      ({ writes := plan.toDataIntent.writes
         readGuards := plan.toDataIntent.readGuards
         event := plan.wire.event } : ReplayEnvelope) :=
  rfl

include authorityPre
/-- The exact authority cell remains read-only through a successful logical
installation, including its canonical bytes. -/
theorem install_preserves_authority
    (plan : PublicationPlan operation authorityCellId)
    (before : DataSnapshot MDoc.rootBytes) :
    (DataSnapshot.install before plan.toDataIntent).model.roots authorityCellId =
        before.model.roots authorityCellId /\
      (DataSnapshot.install before plan.toDataIntent).canonicalBytes
          authorityCellId = before.canonicalBytes authorityCellId := by
  let guard : ReadGuard :=
    { cellId := authorityCellId, expectedRoot := authorityPre.root }
  apply install_preserves_read_guard before plan.toDataIntent guard
  change guard ∈
    [({ cellId := authorityCellId
        expectedRoot := MDoc.rootBytes authorityPre.bytes } : ReadGuard)]
  simp [guard, CellState.Materialized.root,
    plan.digestAgreement.authorityRootFunction]

/-! ## Positive install and replay teeth -/

/-- A fresh publication whose exact writes, charge, nullifiers, and authority
guard all pass preflight reaches the complete data-bearing installation. -/
theorem complete_ready
    (plan : PublicationPlan operation authorityCellId)
    (before : DataSnapshot MDoc.rootBytes)
    (unrecorded : Snapshot.lookupRecorded plan.toDataIntent.transactionId
      before.model.journal = none)
    (ready : plan.toDataIntent.preflight before =
      (Except.ok () : Except
        Minidregg.Kernel.DurableDataIntent.RejectReason Unit)) :
    Minidregg.Kernel.DurableDataIntent.execute .complete before plan.toDataIntent =
      .accepted (DataSnapshot.install before plan.toDataIntent) :=
  Minidregg.Kernel.DurableDataIntent.execute_complete_ready before plan.toDataIntent
    unrecorded ready

/-- Any retry after the complete installation returns the exact erased replay
envelope.  It cannot append a second event or reinstall either post image. -/
@[simp] theorem retry_after_install
    (plan : PublicationPlan operation authorityCellId)
    (schedule : Schedule)
    (before : DataSnapshot MDoc.rootBytes) :
    Minidregg.Kernel.DurableDataIntent.execute schedule
        (DataSnapshot.install before plan.toDataIntent) plan.toDataIntent =
      .replayed plan.toDataIntent.erase := by
  have recorded :
      Snapshot.lookupRecorded plan.toDataIntent.transactionId
          (Snapshot.install before.model plan.toDataIntent.erase).journal =
        some plan.toDataIntent.erase := by
    simpa using Snapshot.lookupRecorded_install before.model
      plan.toDataIntent.erase
  unfold Minidregg.Kernel.DurableDataIntent.execute
  rw [DataSnapshot.install_model, recorded]
  simp

/-! ## Negative authority-rotation teeth -/

/-- An authority rotation, revocation, or attenuation between admission and
durable settlement invalidates the old accepted publication at preflight. -/
theorem stale_authority_rejected
    (plan : PublicationPlan operation authorityCellId)
    (current : DataSnapshot MDoc.rootBytes)
    (authorityMoved :
      current.model.roots authorityCellId ≠ authorityPre.root) :
    plan.toDataIntent.preflight current =
      (Except.error
        Minidregg.Kernel.DurableDataIntent.RejectReason.staleReadGuard :
        Except Minidregg.Kernel.DurableDataIntent.RejectReason Unit) :=
  authority_rotation_or_revocation_rejects_old_publication plan.wire
    plan.bounded plan.digestAgreement plan.authorityDistinctContent
    plan.authorityDistinctEvent current authorityMoved

/-- The executable barrier rejects that stale publication without exposing a
logical post-state, provided this transaction id was not already journaled.
Journal-first replay remains the intended lost-response behavior. -/
theorem stale_authority_execute_rejected
    (plan : PublicationPlan operation authorityCellId)
    (current : DataSnapshot MDoc.rootBytes)
    (authorityMoved :
      current.model.roots authorityCellId ≠ authorityPre.root)
    (unrecorded : Snapshot.lookupRecorded plan.toDataIntent.transactionId
      current.model.journal = none) :
    Minidregg.Kernel.DurableDataIntent.execute .complete current plan.toDataIntent =
      Outcome.rejected
        Minidregg.Kernel.DurableDataIntent.RejectReason.staleReadGuard := by
  have stale : plan.toDataIntent.preflight current =
      (Except.error
        Minidregg.Kernel.DurableDataIntent.RejectReason.staleReadGuard :
        Except Minidregg.Kernel.DurableDataIntent.RejectReason Unit) :=
    authority_rotation_or_revocation_rejects_old_publication plan.wire
      plan.bounded plan.digestAgreement plan.authorityDistinctContent
      plan.authorityDistinctEvent current authorityMoved
  unfold Minidregg.Kernel.DurableDataIntent.execute
  rw [unrecorded, stale]

/-- Atomicity remains conditional on the explicit logical execution model:
every schedule exposes either the complete old snapshot or the complete
payload-bearing installation. -/
theorem no_partial_install
    (plan : PublicationPlan operation authorityCellId)
    (schedule : Schedule)
    (before : DataSnapshot MDoc.rootBytes) :
    (Minidregg.Kernel.DurableDataIntent.execute schedule before plan.toDataIntent).storeAfter
          before = before \/
      (Minidregg.Kernel.DurableDataIntent.execute schedule before plan.toDataIntent).storeAfter
          before = DataSnapshot.install before plan.toDataIntent :=
  execute_no_partial_data_commit schedule before plan.toDataIntent

end PublicationPlan

end

end Minidregg.Assurance.HyperdocumentGuardedDurable

/-! Assurance-facing theorem audit. -/

/-- info: 'Minidregg.Assurance.HyperdocumentGuardedDurable.PublicationPlan.intent_writes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.HyperdocumentGuardedDurable.PublicationPlan.intent_writes
/-- info: 'Minidregg.Assurance.HyperdocumentGuardedDurable.PublicationPlan.retry_after_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.HyperdocumentGuardedDurable.PublicationPlan.retry_after_install
/-- info: 'Minidregg.Assurance.HyperdocumentGuardedDurable.PublicationPlan.stale_authority_execute_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.HyperdocumentGuardedDurable.PublicationPlan.stale_authority_execute_rejected
/-- info: 'Minidregg.Assurance.HyperdocumentGuardedDurable.PublicationPlan.no_partial_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Assurance.HyperdocumentGuardedDurable.PublicationPlan.no_partial_install
