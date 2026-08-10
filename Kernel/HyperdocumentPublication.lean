/-
# Kernel.HyperdocumentPublication -- atomic content + causal-log publication

The mutable Hyperdocument post and its derived causal event-log append are two
separately authorized `AcceptedCellEffect`s.  This module makes them the two
incidences of one genuine `MultiCellHyperedge` declaration.  A successful
publication therefore carries the complete all-legs semantic barrier, distinct
cell identities, one request domain, zero invented resource delta, one apex,
and handler evidence indexed by both exact accepted effects.

`HandlerBoundary` remains the honest seam for physical transaction/CAS,
persistence and cryptographic joint binding.  This module does not infer those
facts from logical acceptance.
-/
import Kernel.HyperdocumentVersionEffects
import Kernel.MultiCellHyperedge

namespace Minidregg.Kernel.HyperdocumentPublication

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument

set_option autoImplicit false

inductive Incidence where
  | content
  | eventLog
  deriving DecidableEq, Fintype, Repr

structure Header where
  turnId : Digest
  apex : Digest
  deriving DecidableEq, Repr

abbrev ContentAccepted
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    (contentConfig : Minidregg.Theory.HyperdocumentOperations.Config)
    (projection : CredentialAuthorityState.ProjectionUniverse)
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (documentPre : Hyperdocument.Cell MDoc)
    (contentPortal : Portal)
    (contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration) :=
  Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection
    authorityPre documentPre contentPortal contentDeclaration

abbrev EventAccepted
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    (content : ContentAccepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration)
    (representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest)
    (store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store)
    (eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config)
    (eventPortal : Portal)
    (eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration) :=
  Minidregg.Kernel.HyperdocumentVersionEffects.Accepted content representation
    store eventConfig eventPortal eventDeclaration

def cells
    {MAuth : CredentialAuthorityState.Materializer}
    (projection : CredentialAuthorityState.ProjectionUniverse)
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (documentMaterializer : Hyperdocument.Materializer Digest)
    (representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest)
    (contentPortal eventPortal : Portal)
    (contentCellId eventCellId : Digest) :
    Minidregg.Kernel.MultiCellHyperedge.CellFamily Incidence where
  schema
    | .content => Hyperdocument.cellSchema
    | .eventLog => Minidregg.Kernel.HyperdocumentEventLog.cellSchema
  fieldDecidableEq incidence := by
    cases incidence <;> infer_instance
  resourceDecidableEq incidence := by
    cases incidence <;> infer_instance
  materializer
    | .content => documentMaterializer
    | .eventLog => representation.cellMaterializer
  portal
    | .content => contentPortal
    | .eventLog => eventPortal
  projectAuthority := fun _ _ =>
    CredentialAuthorityState.authState projection authorityPre
  cellId
    | .content => contentCellId
    | .eventLog => eventCellId

def declaration
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    (content : ContentAccepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration)
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    (event : EventAccepted content representation store eventConfig eventPortal
      eventDeclaration)
    (header : Header) (contentCellId eventCellId : Digest) :
    Minidregg.Kernel.MultiCellHyperedge.Declaration
      (cells projection authorityPre MDoc representation contentPortal
        eventPortal contentCellId eventCellId) where
  header :=
    { domain := contentConfig.requestDomain
      turnId := header.turnId
      apex := header.apex }
  pre
    | .content => documentPre
    | .eventLog =>
        Minidregg.Kernel.HyperdocumentVersionEffects.cellPre representation store
  legs
    | .content =>
        { Nullifier := Nat
          family := Minidregg.Theory.HyperdocumentOperations.family
            (M := MDoc) contentConfig
          kind := .object
          request := contentDeclaration.toRequest contentConfig
          declaration := contentDeclaration
          outcome := () }
    | .eventLog =>
        { Nullifier := Nat
          family := Minidregg.Kernel.HyperdocumentVersionEffects.family
            representation eventConfig
          kind := .object
          request := eventDeclaration.toRequest eventConfig
          declaration := eventDeclaration
          outcome := () }

def acceptedLegs
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    (content : ContentAccepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration)
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    (event : EventAccepted content representation store eventConfig eventPortal
      eventDeclaration)
    (header : Header) (contentCellId eventCellId : Digest) :
    (declaration content event header contentCellId eventCellId).AcceptedLegs
  | .content => content.accepted
  | .eventLog => event.accepted

def zeroResourceLaw
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    (content : ContentAccepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration)
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    (event : EventAccepted content representation store eventConfig eventPortal
      eventDeclaration)
    (header : Header) (contentCellId eventCellId : Digest) :
    Minidregg.Kernel.MultiCellHyperedge.ResourceLaw
      (declaration content event header contentCellId eventCellId) Unit Nat where
  delta := fun _ _ _ => 0

theorem cellIds_injective
    {MAuth : CredentialAuthorityState.Materializer}
    (projection : CredentialAuthorityState.ProjectionUniverse)
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (documentMaterializer : Hyperdocument.Materializer Digest)
    (representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest)
    (contentPortal eventPortal : Portal)
    {contentCellId eventCellId : Digest}
    (distinct : contentCellId ≠ eventCellId) :
    Function.Injective
      (cells projection authorityPre documentMaterializer representation
        contentPortal eventPortal contentCellId eventCellId).cellId := by
  intro left right equal
  cases left <;> cases right
  · rfl
  · exact False.elim (distinct equal)
  · exact False.elim (distinct equal.symm)
  · rfl

theorem aggregate_zero
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    (content : ContentAccepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration)
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    (event : EventAccepted content representation store eventConfig eventPortal
      eventDeclaration)
    (header : Header) (contentCellId eventCellId : Digest) :
    Minidregg.Kernel.MultiCellHyperedge.aggregateDelta
      (zeroResourceLaw content event header contentCellId eventCellId)
      (acceptedLegs content event header contentCellId eventCellId) = 0 := by
  funext coordinate
  simp [Minidregg.Kernel.MultiCellHyperedge.aggregateDelta, zeroResourceLaw]

/-! ## One atomic logical publication -/

def commit
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    (content : ContentAccepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration)
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    (event : EventAccepted content representation store eventConfig eventPortal
      eventDeclaration)
    (header : Header) (contentCellId eventCellId : Digest)
    (domainExact : eventConfig.requestDomain = contentConfig.requestDomain)
    (cellIdsDistinct : contentCellId ≠ eventCellId)
    (boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (declaration content event header contentCellId eventCellId))
    (jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput)
    (jointCommitExact : jointInput.jointCommit = header.apex)
    (jointEvidence : boundary.Evidence
      (acceptedLegs content event header contentCellId eventCellId) jointInput) :
    Minidregg.Kernel.MultiCellHyperedge.Commit
      (zeroResourceLaw content event header contentCellId eventCellId)
      (acceptedLegs content event header contentCellId eventCellId) boundary where
  cellIdsDistinct := cellIds_injective projection authorityPre MDoc representation
    contentPortal eventPortal cellIdsDistinct
  sharedDomain := by
    intro incidence
    cases incidence
    · rfl
    · exact domainExact
  aggregateBalanced := aggregate_zero content event header contentCellId eventCellId
  jointInput := jointInput
  jointCommitExact := jointCommitExact
  jointEvidence := jointEvidence

@[simp] theorem commit_content_post_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : ContentAccepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration}
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    {event : EventAccepted content representation store eventConfig eventPortal
      eventDeclaration}
    {header : Header} {contentCellId eventCellId : Digest}
    {domainExact : eventConfig.requestDomain = contentConfig.requestDomain}
    {cellIdsDistinct : contentCellId ≠ eventCellId}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (declaration content event header contentCellId eventCellId)}
    {jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput}
    {jointCommitExact : jointInput.jointCommit = header.apex}
    {jointEvidence : boundary.Evidence
      (acceptedLegs content event header contentCellId eventCellId) jointInput} :
    (commit content event header contentCellId eventCellId domainExact
      cellIdsDistinct boundary jointInput jointCommitExact jointEvidence).post
        .content = content.accepted.prepared.post :=
  rfl

@[simp] theorem commit_event_post_contains
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : ContentAccepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration}
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal}
    {eventDeclaration : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration}
    {event : EventAccepted content representation store eventConfig eventPortal
      eventDeclaration}
    {header : Header} {contentCellId eventCellId : Digest}
    {domainExact : eventConfig.requestDomain = contentConfig.requestDomain}
    {cellIdsDistinct : contentCellId ≠ eventCellId}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (declaration content event header contentCellId eventCellId)}
    {jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput}
    {jointCommitExact : jointInput.jointCommit = header.apex}
    {jointEvidence : boundary.Evidence
      (acceptedLegs content event header contentCellId eventCellId) jointInput} :
    ((commit content event header contentCellId eventCellId domainExact
      cellIdsDistinct boundary jointInput jointCommitExact jointEvidence).post
        .eventLog).logical.fields
      ⟨Minidregg.Kernel.HyperdocumentEventLog.Sparse.Namespace.events,
        eventDeclaration.key eventConfig⟩ = some eventDeclaration.record :=
  event.post_contains

/-- info: 'Minidregg.Kernel.HyperdocumentPublication.commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit
/-- info: 'Minidregg.Kernel.HyperdocumentPublication.commit_content_post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit_content_post_exact
/-- info: 'Minidregg.Kernel.HyperdocumentPublication.commit_event_post_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit_event_post_contains

end Minidregg.Kernel.HyperdocumentPublication
