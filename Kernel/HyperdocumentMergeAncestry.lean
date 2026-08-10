/-
# Kernel.HyperdocumentMergeAncestry -- ancestry-backed merge bases

This module exposes the proof-relevant base-selection surface now retained by
`HyperdocumentMerge.Accepted` and carries it into the existing causal-event and
multi-cell publication path.

`some base` is possible only for a certified lowest common base of every exact
resolved parent in the same built causal history.  The selected base retains a
canonical materialization whose root is the base event's post-state root.
`none` is possible only with explicit incomparable-maximal-base ambiguity or a
proof that no common base exists.  No arbitrary DAG is claimed to have a unique
LCA.
-/
import Kernel.HyperdocumentMergePublication

namespace Minidregg.Kernel.HyperdocumentMergeAncestry

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument

set_option autoImplicit false

universe uState uEvidence

section AncestryMerge

variable {State : Type uState}
variable {scheme : CausalVersionDag.ContentAddressing}
variable {causalFamily : CausalVersionDag.SemanticFamily.{uState, uEvidence} State}
variable {anchor : CausalVersionDag.Anchor}

abbrev Accepted
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    (history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor)
    (config : Minidregg.Kernel.HyperdocumentMerge.Config)
    (projection : CredentialAuthorityState.ProjectionUniverse)
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (documentPre : Hyperdocument.Cell MDoc)
    (portal : Portal)
    (declaration : Minidregg.Kernel.HyperdocumentMerge.Declaration) :=
  Minidregg.Kernel.HyperdocumentMerge.Accepted history config projection
    authorityPre documentPre portal declaration

/-! ## Exact selected/absent base projections -/

theorem Accepted.selected_plan_base_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Minidregg.Kernel.HyperdocumentMerge.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal}
    {declaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (accepted : Accepted history config projection authorityPre documentPre
      portal declaration)
    (certificate : Minidregg.Kernel.HyperdocumentMerge.SelectedBase
      accepted.parents)
    (decisionExact : accepted.baseDecision =
      .selected certificate)
    (plan : Minidregg.Kernel.HyperdocumentMerge.FieldPlan)
    (present : plan ∈ declaration.body.fields) :
    plan.base = some
      (Minidregg.Kernel.HyperdocumentMerge.causalEventId
        certificate.causal.selected.base) := by
  have exact := accepted.basesExact
  rw [decisionExact] at exact
  exact exact plan present

theorem Accepted.ambiguous_plan_base_absent
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Minidregg.Kernel.HyperdocumentMerge.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal}
    {declaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (accepted : Accepted history config projection authorityPre documentPre
      portal declaration)
    (certificate : Minidregg.Kernel.HyperdocumentMerge.AmbiguousCommonBases
      accepted.parents)
    (decisionExact : accepted.baseDecision =
      .ambiguous certificate)
    (plan : Minidregg.Kernel.HyperdocumentMerge.FieldPlan)
    (present : plan ∈ declaration.body.fields) :
    plan.base = none := by
  have exact := accepted.basesExact
  rw [decisionExact] at exact
  exact exact plan present

theorem Accepted.unavailable_plan_base_absent
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Minidregg.Kernel.HyperdocumentMerge.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal}
    {declaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (accepted : Accepted history config projection authorityPre documentPre
      portal declaration)
    (noCommon : Minidregg.Kernel.HyperdocumentMerge.CommonBase
      accepted.parents → False)
    (decisionExact : accepted.baseDecision =
      .unavailable noCommon)
    (plan : Minidregg.Kernel.HyperdocumentMerge.FieldPlan)
    (present : plan ∈ declaration.body.fields) :
    plan.base = none := by
  have exact := accepted.basesExact
  rw [decisionExact] at exact
  exact exact plan present

def Accepted.selectedReachesParent
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Minidregg.Kernel.HyperdocumentMerge.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal}
    {declaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (accepted : Accepted history config projection authorityPre documentPre
      portal declaration)
    (certificate : Minidregg.Kernel.HyperdocumentMerge.SelectedBase
      accepted.parents)
    (node : CausalVersionDag.VerifiedEvent scheme causalFamily)
    (present : node ∈ accepted.parents.resolved) :
    CausalVersionAncestry.Reaches history
      certificate.causal.selected.base node :=
  certificate.causal.selected.reachesEvery node present

theorem Accepted.selected_realization_root_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Minidregg.Kernel.HyperdocumentMerge.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal}
    {declaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (accepted : Accepted history config projection authorityPre documentPre
      portal declaration)
    (certificate : Minidregg.Kernel.HyperdocumentMerge.SelectedBase
      accepted.parents) :
    certificate.realization.root =
      certificate.causal.selected.base.preimage.postStateRoot :=
  certificate.realizationRootExact

theorem Accepted.parent_realization_root_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Minidregg.Kernel.HyperdocumentMerge.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal}
    {declaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (accepted : Accepted history config projection authorityPre documentPre
      portal declaration)
    (parent : Minidregg.Kernel.HyperdocumentMerge.Parent)
    (present : parent ∈ declaration.body.parents) :
    (accepted.parents.realization parent present).root =
      parent.record.postStateRoot :=
  accepted.parents.realizationRootExact parent present

/-! ## Existing causal publication input -/

/-- An ancestry-backed accepted merge feeds the existing event/publication
surface without a second event record or parent relation. -/
def publicationInputs
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Minidregg.Kernel.HyperdocumentMerge.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal}
    {declaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (accepted : Accepted history config projection authorityPre documentPre
      portal declaration)
    (eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config)
    (expectedLogRoot : Digest)
    (addressingExact : scheme = eventConfig.scheme)
    (parentCompatibility : causalFamily.ParentCompatible
      (accepted.parents.resolved.map CausalVersionDag.VerifiedEvent.preimage)
      (Minidregg.Kernel.HyperdocumentMerge.recordOfAccepted accepted).toCausalPreimage)
    (eventWellFormed :
      (Minidregg.Kernel.HyperdocumentMerge.recordOfAccepted accepted).CausallyWellFormed) :
    Minidregg.Kernel.HyperdocumentMerge.PublicationInputs accepted eventConfig
      expectedLogRoot where
  addressingExact := addressingExact
  parentCompatibility := parentCompatibility
  eventWellFormed := eventWellFormed

@[simp] theorem publicationInputs_record_unchanged
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Minidregg.Kernel.HyperdocumentMerge.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal}
    {declaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    (accepted : Accepted history config projection authorityPre documentPre
      portal declaration)
    (expectedLogRoot : Digest) :
    (Minidregg.Kernel.HyperdocumentMergePublication.derivedEventDeclaration
      accepted expectedLogRoot).record =
      Minidregg.Kernel.HyperdocumentMerge.recordOfAccepted accepted :=
  rfl

/-! ## Selected-base conflict publication tooth -/

theorem selected_base_conflict_is_published
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {mergeConfig : Minidregg.Kernel.HyperdocumentMerge.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {mergePortal : Portal}
    {mergeDeclaration : Minidregg.Kernel.HyperdocumentMerge.Declaration}
    {merge : Accepted history mergeConfig projection authorityPre documentPre
      mergePortal mergeDeclaration}
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store}
    {eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config}
    {eventPortal : Portal} {expectedLogRoot : Digest}
    {event : Minidregg.Kernel.HyperdocumentMergePublication.EventAccepted merge
      representation store eventConfig eventPortal expectedLogRoot}
    {header : Minidregg.Kernel.HyperdocumentMergePublication.Header}
    {contentCellId eventCellId : Digest}
    {domainExact : eventConfig.requestDomain = mergeConfig.requestDomain}
    {cellIdsDistinct : contentCellId ≠ eventCellId}
    {boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
      (Minidregg.Kernel.HyperdocumentMergePublication.declaration merge event
        header contentCellId eventCellId)}
    {jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput}
    {jointCommitExact : jointInput.jointCommit = header.apex}
    {jointEvidence : boundary.Evidence
      (Minidregg.Kernel.HyperdocumentMergePublication.acceptedLegs merge event
        header contentCellId eventCellId) jointInput}
    (certificate : Minidregg.Kernel.HyperdocumentMerge.SelectedBase merge.parents)
    (decisionExact : merge.baseDecision = .selected certificate)
    (plan : Minidregg.Kernel.HyperdocumentMerge.FieldPlan)
    (planPresent : plan ∈ mergeDeclaration.body.fields)
    (first second : Minidregg.Kernel.HyperdocumentMerge.FieldSource)
    (rest : List Minidregg.Kernel.HyperdocumentMerge.FieldSource)
    (sourcesExact : plan.sources = first :: second :: rest) :
    lookup
      ((Minidregg.Kernel.HyperdocumentMergePublication.commit merge event header
        contentCellId eventCellId domainExact cellIdsDistinct boundary jointInput
        jointCommitExact jointEvidence).post .content).logical
      .conflicts
      (plan.conflictId mergeConfig
        (mergeDeclaration.operationId mergeConfig)) =
      some
        { plan.conflictRecord (mergeDeclaration.operationId mergeConfig) with
          base := some (Minidregg.Kernel.HyperdocumentMerge.causalEventId
            certificate.causal.selected.base) } := by
  have retained :=
    Minidregg.Kernel.HyperdocumentMergePublication.commit_conflict_retained
      (merge := merge) (event := event) (header := header)
      (contentCellId := contentCellId) (eventCellId := eventCellId)
      (domainExact := domainExact) (cellIdsDistinct := cellIdsDistinct)
      (boundary := boundary) (jointInput := jointInput)
      (jointCommitExact := jointCommitExact) (jointEvidence := jointEvidence)
      plan planPresent first second rest sourcesExact
  have baseExact := merge.selected_plan_base_exact certificate decisionExact
    plan planPresent
  calc
    _ = some (plan.conflictRecord
        (mergeDeclaration.operationId mergeConfig)) := retained
    _ = some
        { plan.conflictRecord (mergeDeclaration.operationId mergeConfig) with
          base := some (Minidregg.Kernel.HyperdocumentMerge.causalEventId
            certificate.causal.selected.base) } := by
      congr 2
      cases plan
      simp_all [Minidregg.Kernel.HyperdocumentMerge.FieldPlan.conflictRecord]

/-- info: 'Minidregg.Kernel.HyperdocumentMergeAncestry.Accepted.selected_plan_base_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.selected_plan_base_exact
/-- info: 'Minidregg.Kernel.HyperdocumentMergeAncestry.Accepted.ambiguous_plan_base_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.ambiguous_plan_base_absent
/-- info: 'Minidregg.Kernel.HyperdocumentMergeAncestry.Accepted.unavailable_plan_base_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.unavailable_plan_base_absent
/-- info: 'Minidregg.Kernel.HyperdocumentMergeAncestry.Accepted.selectedReachesParent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.selectedReachesParent
/-- info: 'Minidregg.Kernel.HyperdocumentMergeAncestry.Accepted.selected_realization_root_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.selected_realization_root_exact
/-- info: 'Minidregg.Kernel.HyperdocumentMergeAncestry.Accepted.parent_realization_root_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.parent_realization_root_exact
/-- info: 'Minidregg.Kernel.HyperdocumentMergeAncestry.publicationInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms publicationInputs
/-- info: 'Minidregg.Kernel.HyperdocumentMergeAncestry.publicationInputs_record_unchanged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms publicationInputs_record_unchanged
/-- info: 'Minidregg.Kernel.HyperdocumentMergeAncestry.selected_base_conflict_is_published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms selected_base_conflict_is_published

end AncestryMerge

end Minidregg.Kernel.HyperdocumentMergeAncestry
