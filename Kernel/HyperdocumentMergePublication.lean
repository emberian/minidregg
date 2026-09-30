/-
# Kernel.HyperdocumentMergePublication -- atomic merge + causal-event turn

This module closes an accepted offline/concurrent Hyperdocument merge through
the existing causal event-log effect family and the generic two-incidence
`MultiCellHyperedge` publication path.

The event declaration is definitionally derived from the retained merge
`AcceptedCellEffect`: neither content root, parent frontier, request id nor
effect id is caller-authored.  Event-log acceptance separately requires exact
request-indexed authority, causal well-formedness, a fresh typed sparse slot,
authorization, and a validated canonical patch.  The final logical commit
contains both exact accepted effects and one handler-evidence seam.

Physical compare-and-swap, persistence, consensus, finality and cryptographic
binding remain obligations of `HandlerBoundary`.  No ancestry/common-base fact
is introduced here.
-/
import Kernel.HyperdocumentMerge
import Kernel.MultiCellHyperedge

namespace Minidregg.Kernel.HyperdocumentMergePublication

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument

set_option autoImplicit false

universe uState uEvidence

section EventAdapter

variable {State : Type uState}
variable {scheme : CausalVersionDag.ContentAddressing}
variable {causalFamily : CausalVersionDag.SemanticFamily.{uState, uEvidence} State}
variable {anchor : CausalVersionDag.Anchor}

abbrev MergeAccepted
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    (history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor)
    (mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config)
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (documentPre : Hyperdocument.Cell MDoc)
    (mergePortal : Portal) (mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration) :=
  Minidregg.Kernel.HyperdocumentMerge.Accepted history mergeConfig authorityPre documentPre
    mergePortal mergeDeclaration

def derivedEventDeclaration
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration)
    (expectedLogRoot : Digest) : Minidregg.Kernel.HyperdocumentVersionEffects.Declaration :=
  Minidregg.Kernel.HyperdocumentMerge.eventDeclaration merge expectedLogRoot

@[simp] theorem derivedEventDeclaration_record_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration)
    (expectedLogRoot : Digest) :
    (derivedEventDeclaration merge expectedLogRoot).record =
      Minidregg.Kernel.HyperdocumentMerge.recordOfAccepted merge :=
  rfl

@[simp] theorem derivedEventDeclaration_log_root_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration)
    (expectedLogRoot : Digest) :
    (derivedEventDeclaration merge expectedLogRoot).expectedLogRoot =
      expectedLogRoot :=
  rfl

/-- The actual accepted event-log incidence for one exact merge.  This reuses
the existing version-event family and sparse event-log MLog; only
the source adapter is merge-specific. -/
structure EventAccepted
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration)
    (MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer)
    (store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store)
    (eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config)
    (eventPortal : Portal) (expectedLogRoot : Digest) : Type _ where
  inputs : Minidregg.Kernel.HyperdocumentMerge.PublicationInputs merge eventConfig expectedLogRoot
  principal : AuthenticatedPrincipal authorityPre
    mergeDeclaration.request.height mergeDeclaration.intent.author
  namedCapabilityAdmissible :
    (Minidregg.Theory.HyperdocumentOperations.authenticatedObjectHead
      principal merge.semantic.objectCapability).Admissible
    (CredentialAuthorityState.authState authorityPre)
    ((derivedEventDeclaration merge expectedLogRoot).toRequest eventConfig)
  accepted : AcceptedCellEffect
    (portal := eventPortal)
    (authState := CredentialAuthorityState.authState authorityPre)
    (Minidregg.Kernel.HyperdocumentVersionEffects.family MLog eventConfig
      (Minidregg.Kernel.HyperdocumentVersionEffects.cellPre MLog store))
    ((derivedEventDeclaration merge expectedLogRoot).toRequest eventConfig)
    (Minidregg.Kernel.HyperdocumentVersionEffects.cellPre MLog store)
    (derivedEventDeclaration merge expectedLogRoot) ()

def acceptEvent
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    {merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration}
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    (inputs : Minidregg.Kernel.HyperdocumentMerge.PublicationInputs merge eventConfig expectedLogRoot)
    (namedCapabilityAdmissible :
      (Minidregg.Theory.HyperdocumentOperations.authenticatedObjectHead
        merge.principal merge.semantic.objectCapability).Admissible
      (CredentialAuthorityState.authState authorityPre)
      ((derivedEventDeclaration merge expectedLogRoot).toRequest eventConfig))
    (fresh : store (Minidregg.Kernel.HyperdocumentEventLog.Sparse.eventAddress
      ((derivedEventDeclaration merge expectedLogRoot).key eventConfig)) = none)
    (domainExact : (derivedEventDeclaration merge expectedLogRoot).record.historyDomain =
      eventConfig.historyDomain)
    (authorization : Authorized eventPortal
      (CredentialAuthorityState.authState authorityPre)
      ((derivedEventDeclaration merge expectedLogRoot).toRequest eventConfig))
    (validated : CellState.ValidatedPatch MLog
      (Minidregg.Kernel.HyperdocumentVersionEffects.cellPre MLog store)
      ((derivedEventDeclaration merge expectedLogRoot).toRequest eventConfig).preStateRoot
      ((derivedEventDeclaration merge expectedLogRoot).patch eventConfig)) :
    EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot where
  inputs := inputs
  principal := merge.principal
  namedCapabilityAdmissible := namedCapabilityAdmissible
  accepted :=
    { authorization := authorization
      preStateBound := rfl
      requestBound := rfl
      effectsDigestBound := rfl
      modeEvidence := ⟨⟨inputs.eventWellFormed, fresh, domainExact⟩⟩
      validated := validated
      postcondition := validated.resultAt
      disclosure := .sealed
      disclosureAllowed := trivial }

@[simp] theorem EventAccepted.post_contains
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    {merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration}
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    (event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot) :
    event.accepted.prepared.post.logical
      (Minidregg.Kernel.HyperdocumentEventLog.Sparse.eventAddress
        ((derivedEventDeclaration merge expectedLogRoot).key eventConfig)) =
      some (derivedEventDeclaration merge expectedLogRoot).record := by
  change Minidregg.Theory.Store.Patch.run store
    [(derivedEventDeclaration merge expectedLogRoot).appendOp eventConfig]
    (Minidregg.Kernel.HyperdocumentEventLog.Sparse.eventAddress
      ((derivedEventDeclaration merge expectedLogRoot).key eventConfig)) =
      some (derivedEventDeclaration merge expectedLogRoot).record
  simp [Minidregg.Kernel.HyperdocumentVersionEffects.Declaration.appendOp,
    Minidregg.Theory.Store.Op.apply, Minidregg.Kernel.HyperdocumentEventLog.Sparse.eventAddress]
  rfl

theorem EventAccepted.pre_fresh
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    {merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration}
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    (event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot) :
    store (Minidregg.Kernel.HyperdocumentEventLog.Sparse.eventAddress
      ((derivedEventDeclaration merge expectedLogRoot).key eventConfig)) = none :=
  event.accepted.modeEvidence.down.fresh

/-- Every accepted merge event names the log's history domain. -/
theorem EventAccepted.domain_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    {merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration}
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    (event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot) :
    mergeDeclaration.intent.historyDomain = eventConfig.historyDomain :=
  event.accepted.modeEvidence.down.domainExact

/-! ## One two-incidence merge publication -/

inductive Incidence where
  | content
  | eventLog
  deriving DecidableEq, Fintype, Repr

structure Header where
  turnId : Digest
  apex : Digest
  deriving DecidableEq, Repr

def cells
    {MAuth : CredentialAuthorityState.Materializer}
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (documentMaterializer : Hyperdocument.Materializer Digest)
    (MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer)
    (mergePortal eventPortal : Portal)
    (contentCellId eventCellId : Digest) :
    Minidregg.Kernel.MultiCellHyperedge.CellFamily Incidence where
  storeLayout
    | .content => Hyperdocument.layout
    | .eventLog => Minidregg.Kernel.HyperdocumentEventLog.Sparse.layout
  materializer
    | .content => documentMaterializer
    | .eventLog => MLog
  portal
    | .content => mergePortal
    | .eventLog => eventPortal
  projectAuthority := fun _ _ =>
    CredentialAuthorityState.authState authorityPre
  cellId
    | .content => contentCellId
    | .eventLog => eventCellId

def declaration
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration)
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    (_event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot)
    (header : Header) (contentCellId eventCellId : Digest) :
    Minidregg.Kernel.MultiCellHyperedge.Declaration
      (cells authorityPre MDoc MLog mergePortal eventPortal
        contentCellId eventCellId) where
  header :=
    { domain := mergeConfig.requestDomain
      turnId := header.turnId
      apex := header.apex }
  pre
    | .content => documentPre
    | .eventLog => Minidregg.Kernel.HyperdocumentVersionEffects.cellPre MLog store
  legs
    | .content =>
        { Nullifier := Nat
          family := Minidregg.Kernel.HyperdocumentMerge.family (M := MDoc) mergeConfig documentPre
          kind := .object
          request := mergeDeclaration.toRequest mergeConfig
          declaration := mergeDeclaration
          outcome := () }
    | .eventLog =>
        { Nullifier := Nat
          family := Minidregg.Kernel.HyperdocumentVersionEffects.family MLog eventConfig
            (Minidregg.Kernel.HyperdocumentVersionEffects.cellPre MLog store)
          kind := .object
          request :=
            (derivedEventDeclaration merge expectedLogRoot).toRequest eventConfig
          declaration := derivedEventDeclaration merge expectedLogRoot
          outcome := () }

def acceptedLegs
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration)
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    (event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot)
    (header : Header) (contentCellId eventCellId : Digest) :
    (declaration merge event header contentCellId eventCellId).AcceptedLegs
  | .content => merge.accepted
  | .eventLog => event.accepted

def zeroResourceLaw
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration)
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    (event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot)
    (header : Header) (contentCellId eventCellId : Digest) :
    Minidregg.Kernel.MultiCellHyperedge.ResourceLaw
      (declaration merge event header contentCellId eventCellId) Unit Nat where
  delta := fun _ _ _ => 0

theorem cellIds_injective
    {MAuth : CredentialAuthorityState.Materializer}
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (documentMaterializer : Hyperdocument.Materializer Digest)
    (MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer)
    (mergePortal eventPortal : Portal)
    {contentCellId eventCellId : Digest}
    (distinct : contentCellId ≠ eventCellId) :
    Function.Injective
      (cells authorityPre documentMaterializer MLog
        mergePortal eventPortal contentCellId eventCellId).cellId := by
  intro left right equal
  cases left <;> cases right
  · rfl
  · exact False.elim (distinct equal)
  · exact False.elim (distinct equal.symm)
  · rfl

theorem aggregate_zero
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration)
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    (event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot)
    (header : Header) (contentCellId eventCellId : Digest) :
    Minidregg.Kernel.MultiCellHyperedge.aggregateDelta
      (zeroResourceLaw merge event header contentCellId eventCellId)
      (acceptedLegs merge event header contentCellId eventCellId) = 0 := by
  funext coordinate
  simp [Minidregg.Kernel.MultiCellHyperedge.aggregateDelta, zeroResourceLaw]

def commit
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration)
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    (event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot)
    (header : Header) (contentCellId eventCellId : Digest)
    (domainExact : eventConfig.requestDomain = mergeConfig.requestDomain)
    (cellIdsDistinct : contentCellId ≠ eventCellId)
    (boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (declaration merge event header contentCellId eventCellId))
    (jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput)
    (jointCommitExact : jointInput.jointCommit = header.apex)
    (jointEvidence : boundary.Evidence
      (acceptedLegs merge event header contentCellId eventCellId) jointInput) :
    Minidregg.Kernel.MultiCellHyperedge.Commit
      (zeroResourceLaw merge event header contentCellId eventCellId)
      (acceptedLegs merge event header contentCellId eventCellId) boundary where
  cellIdsDistinct := cellIds_injective authorityPre MDoc MLog
    mergePortal eventPortal cellIdsDistinct
  sharedDomain := by
    intro incidence
    cases incidence
    · rfl
    · exact domainExact
  aggregateBalanced := aggregate_zero merge event header contentCellId eventCellId
  jointInput := jointInput
  jointCommitExact := jointCommitExact
  jointEvidence := jointEvidence

@[simp] theorem commit_content_post_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    {merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration}
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    {event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot}
    {header : Header} {contentCellId eventCellId : Digest}
    {domainExact : eventConfig.requestDomain = mergeConfig.requestDomain}
    {cellIdsDistinct : contentCellId ≠ eventCellId}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (declaration merge event header contentCellId eventCellId)}
    {jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput}
    {jointCommitExact : jointInput.jointCommit = header.apex}
    {jointEvidence : boundary.Evidence
      (acceptedLegs merge event header contentCellId eventCellId) jointInput} :
    (commit merge event header contentCellId eventCellId domainExact
      cellIdsDistinct boundary jointInput jointCommitExact jointEvidence).post
        .content = merge.accepted.prepared.post :=
  rfl

@[simp] theorem commit_event_post_contains
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    {merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration}
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    {event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot}
    {header : Header} {contentCellId eventCellId : Digest}
    {domainExact : eventConfig.requestDomain = mergeConfig.requestDomain}
    {cellIdsDistinct : contentCellId ≠ eventCellId}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (declaration merge event header contentCellId eventCellId)}
    {jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput}
    {jointCommitExact : jointInput.jointCommit = header.apex}
    {jointEvidence : boundary.Evidence
      (acceptedLegs merge event header contentCellId eventCellId) jointInput} :
    ((commit merge event header contentCellId eventCellId domainExact
      cellIdsDistinct boundary jointInput jointCommitExact jointEvidence).post
        .eventLog).logical
      (Minidregg.Kernel.HyperdocumentEventLog.Sparse.eventAddress
        ((derivedEventDeclaration merge expectedLogRoot).key eventConfig)) =
      some (derivedEventDeclaration merge expectedLogRoot).record :=
  event.post_contains

/-! ## Conflict-preserving publication teeth -/

def ConflictFreeState (state : Minidregg.Theory.Store.Store layout) : Prop :=
  ∀ id, lookup state .conflicts id = none

theorem commit_conflict_retained
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    {merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration}
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    {event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot}
    {header : Header} {contentCellId eventCellId : Digest}
    {domainExact : eventConfig.requestDomain = mergeConfig.requestDomain}
    {cellIdsDistinct : contentCellId ≠ eventCellId}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (declaration merge event header contentCellId eventCellId)}
    {jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput}
    {jointCommitExact : jointInput.jointCommit = header.apex}
    {jointEvidence : boundary.Evidence
      (acceptedLegs merge event header contentCellId eventCellId) jointInput}
    (plan : Minidregg.Kernel.HyperdocumentMerge.FieldPlan) (planPresent : plan ∈ mergeDeclaration.body.fields)
    (first second : Minidregg.Kernel.HyperdocumentMerge.FieldSource) (rest : List Minidregg.Kernel.HyperdocumentMerge.FieldSource)
    (sourcesExact : plan.sources = first :: second :: rest) :
    lookup
      ((commit merge event header contentCellId eventCellId domainExact
        cellIdsDistinct boundary jointInput jointCommitExact jointEvidence).post
          .content).logical
      .conflicts
      (plan.conflictId mergeConfig (mergeDeclaration.operationId mergeConfig)) =
      some (plan.conflictRecord (mergeDeclaration.operationId mergeConfig)) := by
  rw [commit_content_post_exact]
  apply merge.post_contains_guardedSet (space := .conflicts)
    (key := plan.conflictId mergeConfig (mergeDeclaration.operationId mergeConfig))
    (expected := none)
  unfold Minidregg.Kernel.HyperdocumentMerge.Declaration.patch
  apply List.mem_append_left
  apply List.mem_flatMap.2
  refine ⟨plan, planPresent, ?_⟩
  simp [Minidregg.Kernel.HyperdocumentMerge.FieldPlan.ops, sourcesExact]

theorem commit_conflict_cannot_be_erased
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal} {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    {merge : MergeAccepted history mergeConfig authorityPre
      documentPre mergePortal mergeDeclaration}
    {MLog : Minidregg.Kernel.HyperdocumentVersionEffects.LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    {event : EventAccepted merge MLog store eventConfig eventPortal
      expectedLogRoot}
    {header : Header} {contentCellId eventCellId : Digest}
    {domainExact : eventConfig.requestDomain = mergeConfig.requestDomain}
    {cellIdsDistinct : contentCellId ≠ eventCellId}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (declaration merge event header contentCellId eventCellId)}
    {jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput}
    {jointCommitExact : jointInput.jointCommit = header.apex}
    {jointEvidence : boundary.Evidence
      (acceptedLegs merge event header contentCellId eventCellId) jointInput}
    (plan : Minidregg.Kernel.HyperdocumentMerge.FieldPlan) (planPresent : plan ∈ mergeDeclaration.body.fields)
    (first second : Minidregg.Kernel.HyperdocumentMerge.FieldSource) (rest : List Minidregg.Kernel.HyperdocumentMerge.FieldSource)
    (sourcesExact : plan.sources = first :: second :: rest) :
    ¬ ConflictFreeState
      ((commit merge event header contentCellId eventCellId domainExact
        cellIdsDistinct boundary jointInput jointCommitExact jointEvidence).post
          .content).logical := by
  intro conflictFree
  have retained := commit_conflict_retained
    (merge := merge) (event := event) (header := header)
    (contentCellId := contentCellId) (eventCellId := eventCellId)
    (domainExact := domainExact) (cellIdsDistinct := cellIdsDistinct)
    (boundary := boundary) (jointInput := jointInput)
    (jointCommitExact := jointCommitExact) (jointEvidence := jointEvidence)
    plan planPresent first second rest sourcesExact
  rw [conflictFree
    (plan.conflictId mergeConfig
      (mergeDeclaration.operationId mergeConfig))] at retained
  cases retained

/-- info: 'Minidregg.Kernel.HyperdocumentMergePublication.derivedEventDeclaration_record_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms derivedEventDeclaration_record_exact
/-- info: 'Minidregg.Kernel.HyperdocumentMergePublication.EventAccepted.post_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms EventAccepted.post_contains
/-- info: 'Minidregg.Kernel.HyperdocumentMergePublication.EventAccepted.pre_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms EventAccepted.pre_fresh
/-- info: 'Minidregg.Kernel.HyperdocumentMergePublication.EventAccepted.domain_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms EventAccepted.domain_exact
/-- info: 'Minidregg.Kernel.HyperdocumentMergePublication.commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit
/-- info: 'Minidregg.Kernel.HyperdocumentMergePublication.commit_content_post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit_content_post_exact
/-- info: 'Minidregg.Kernel.HyperdocumentMergePublication.commit_event_post_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit_event_post_contains
/-- info: 'Minidregg.Kernel.HyperdocumentMergePublication.commit_conflict_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit_conflict_retained
/-- info: 'Minidregg.Kernel.HyperdocumentMergePublication.commit_conflict_cannot_be_erased' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commit_conflict_cannot_be_erased

end EventAdapter

end Minidregg.Kernel.HyperdocumentMergePublication
