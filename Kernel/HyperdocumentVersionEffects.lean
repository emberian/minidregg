/-
# Kernel.HyperdocumentVersionEffects -- accepted causal-event publication

One accepted Hyperdocument content effect determines the complete causal event
record: its pre/post roots, operation id, request id, effect id, parents,
author, schema and semantic version are all projections of that exact accepted
effect.  The event-log effect then allocates the derived final event key in the
separate append-only sparse log.  No caller authors either content root.

This module deliberately stops before receipt-history membership, observation
coordinates, finality, and physical transaction evidence.  Those are explicit
downstream seams, not facts inferred from a successful sparse allocation.
-/
import Kernel.HyperdocumentEventLog
import Theory.HyperdocumentOperations

namespace Minidregg.Kernel.HyperdocumentVersionEffects

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument

set_option autoImplicit false

/-! ## First-order event-log declaration -/

structure Declaration where
  expectedLogRoot : Digest
  request : Minidregg.Theory.HyperdocumentOperations.RequestEnvelope
  record : VersionEventRecord

structure Config where
  declarationCodec : LawfulCodec Declaration
  requestCodec : LawfulCodec (Request .object)
  effectDerivation : DigestDerivation
  requestDerivation : DigestDerivation
  eventCodec : LawfulCodec CausalVersionDag.EventPreimage
  eventDerivation : DigestDerivation
  requestDomain : Digest
  semanticRelation : Digest

def Config.scheme (config : Config) : CausalVersionDag.ContentAddressing :=
  causalVersionAddressing config.eventCodec config.eventDerivation

def Declaration.key (config : Config) (declaration : Declaration) :
    VersionEventId :=
  deriveVersionEventId config.eventCodec config.eventDerivation
    declaration.record

def Declaration.stored (config : Config) (declaration : Declaration)
    (wellFormed : declaration.record.CausallyWellFormed) :
    StoredVersionEvent config.scheme :=
  StoredVersionEvent.derive config.eventCodec config.eventDerivation
    declaration.record wellFormed

/-- The one operation of an event publication: allocate the derived key. -/
def Declaration.appendOp (config : Config) (declaration : Declaration) :
    Minidregg.Kernel.HyperdocumentEventLog.Sparse.Op :=
  .allocate .events (declaration.key config) declaration.record

def Declaration.patch (config : Config) (declaration : Declaration) :
    Minidregg.Kernel.HyperdocumentEventLog.Sparse.Patch :=
  [declaration.appendOp config]

/-- The declaration's operation is exactly the event log's append of the
stored event it derives. -/
theorem Declaration.appendOp_stored (config : Config) (declaration : Declaration)
    (wellFormed : declaration.record.CausallyWellFormed) :
    declaration.appendOp config =
      Minidregg.Kernel.HyperdocumentEventLog.Sparse.appendOp
        (declaration.stored config wellFormed) :=
  rfl

def Declaration.effectDigest (config : Config)
    (declaration : Declaration) : Digest :=
  config.effectDerivation.digestBytes
    (config.declarationCodec.encode declaration)

def Declaration.toRequest (config : Config) (declaration : Declaration) :
    Request .object where
  domain := config.requestDomain
  semantics := config.semanticRelation
  federation := declaration.request.federation
  subject := declaration.record.author.subject
  subjectKeyEpoch := declaration.request.subjectKeyEpoch
  target := ⟨declaration.record.document.digest.value⟩
  verb := .mutateObject
  argsDigest := (declaration.key config).digest
  effectsDigest := declaration.effectDigest config
  nonce := declaration.record.operation.digest.value
  height := declaration.request.height
  preStateRoot := declaration.expectedLogRoot
  policyId := declaration.request.policyId
  policyEpoch := declaration.request.policyEpoch
  policyRevision := declaration.request.policyRevision
  cost := declaration.request.cost

def Declaration.requestId (config : Config) (declaration : Declaration) : Digest :=
  config.requestDerivation.digestBytes
    (config.requestCodec.encode (declaration.toRequest config))

/-! ## Derivation from one exact accepted content effect -/

def recordOfContent
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    (content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration) : VersionEventRecord :=
  content.versionEventRecord

/-- This equality is the no-caller-authored-root boundary.  A candidate log
declaration is admissible only when its complete record is the projection of
the retained accepted content token. -/
structure SourceExact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    (content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration)
    (declaration : Declaration) : Prop where
  recordExact : declaration.record = recordOfContent content
  requestExact : declaration.request = contentDeclaration.request

theorem SourceExact.pre_root_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration}
    {declaration : Declaration}
    (source : SourceExact content declaration) :
    declaration.record.preStateRoot = documentPre.root := by
  rw [source.recordExact]
  rfl

theorem SourceExact.post_root_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration}
    {declaration : Declaration}
    (source : SourceExact content declaration) :
    declaration.record.postStateRoot =
      content.accepted.prepared.post.root := by
  rw [source.recordExact]
  rfl

theorem SourceExact.request_id_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration}
    {declaration : Declaration}
    (source : SourceExact content declaration) :
    declaration.record.requestId =
      contentDeclaration.requestId contentConfig := by
  rw [source.recordExact]
  rfl

theorem SourceExact.effect_id_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration}
    {declaration : Declaration}
    (source : SourceExact content declaration) :
    declaration.record.effectId =
      contentDeclaration.effectDigest contentConfig := by
  rw [source.recordExact]
  rfl

theorem SourceExact.object_capability
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig
      projection authorityPre documentPre contentPortal contentDeclaration}
    {declaration : Declaration}
    (source : SourceExact content declaration) :
    declaration.record.author.capabilityKind = .object := by
  rw [source.recordExact]
  exact content.semantic.canonical.objectCapability

/-! ## Accepted event-log effect: one append at the canonical log cell -/

open Minidregg.Kernel.HyperdocumentEventLog.Sparse (eventAddress)

abbrev LogMaterializer := Minidregg.Kernel.HyperdocumentEventLog.Sparse.Materializer Digest

def cellPre (M : LogMaterializer)
    (store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store) :
    CellState.Materialized M :=
  CellState.materialize M store

def sealedOnly : DisclosureDecision Unit Unit (fun _ => Unit) → Prop
  | .sealed => True
  | .reveal _ _ => False
  | .declassify _ _ _ => False

/-- A generic event-log effect is an append at its actual canonical pre-cell.
Freshness is retained here, so projecting away the publication wrapper cannot
turn its immutable event allocation into an overwrite.  Content provenance is
the separate `SourceExact` relation consumed by the publication constructor. -/
structure ValidAppend (M : LogMaterializer)
    (config : Config) (pre : CellState.Materialized M)
    (declaration : Declaration) : Prop where
  wellFormed : declaration.record.CausallyWellFormed
  fresh : pre.logical (eventAddress (declaration.key config)) = none

def family (M : LogMaterializer)
    (config : Config) (pre : CellState.Materialized M) :
    SemanticEffectFamily Minidregg.Kernel.HyperdocumentEventLog.Sparse.layout M Nat where
  Declaration := Declaration
  declarationCodec := config.declarationCodec
  pre := pre
  request := fun declaration => ⟨.object, declaration.toRequest config⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => Minidregg.Theory.HyperdocumentOperations.unitCodec
  ModeEvidence := fun declaration _ => PLift (ValidAppend M config pre declaration)
  Postcondition := fun declaration _ post =>
    (declaration.patch config).ResultAt pre.logical post
  effectDigest := Declaration.effectDigest config
  patch := fun declaration _ => declaration.patch config
  nullifier := fun declaration _ => some declaration.record.operation.digest.value
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

/-- An occupied final event key cannot be overwritten through a bare generic
accepted effect.  This does not depend on retaining the outer publication
wrapper. -/
theorem no_accepted_at_occupied_key
    {M : LogMaterializer}
    {config : Config} {pre : CellState.Materialized M}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {declaration : Declaration}
    (occupied : pre.logical (eventAddress (declaration.key config)) ≠ none) :
    IsEmpty (AcceptedCellEffect (portal := portal) (authState := authState)
      (family M config pre) request pre declaration ()) :=
  ⟨fun accepted => occupied accepted.modeEvidence.down.fresh⟩

/-- The accepted event publication.  Its one validated patch is the append of
the derived event; there is no second (sparse) view of the same allocation. -/
structure Accepted
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    (content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration)
    (M : LogMaterializer)
    (store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store) (config : Config)
    (portal : Portal) (declaration : Declaration) : Type where
  source : SourceExact content declaration
  principal : AuthenticatedPrincipal projection authorityPre
    declaration.request.height declaration.record.author
  namedCapabilityAdmissible :
    (Minidregg.Theory.HyperdocumentOperations.authenticatedObjectHead
      principal source.object_capability).Admissible
    (CredentialAuthorityState.authState projection authorityPre)
    (declaration.toRequest config)
  accepted : AcceptedCellEffect
    (portal := portal)
    (authState := CredentialAuthorityState.authState projection authorityPre)
    (family M config (cellPre M store)) (declaration.toRequest config)
    (cellPre M store) declaration ()

def accept
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration}
    {M : LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store} {config : Config}
    {portal : Portal} {declaration : Declaration}
    (source : SourceExact content declaration)
    (principal : AuthenticatedPrincipal projection authorityPre
      declaration.request.height declaration.record.author)
    (namedCapabilityAdmissible :
      (Minidregg.Theory.HyperdocumentOperations.authenticatedObjectHead
        principal source.object_capability).Admissible
      (CredentialAuthorityState.authState projection authorityPre)
      (declaration.toRequest config))
    (wellFormed : declaration.record.CausallyWellFormed)
    (fresh : store (eventAddress (declaration.key config)) = none)
    (authorization : Authorized portal
      (CredentialAuthorityState.authState projection authorityPre)
      (declaration.toRequest config))
    (validated : CellState.ValidatedPatch M (cellPre M store)
      (declaration.toRequest config).preStateRoot (declaration.patch config)) :
    Accepted content M store config portal declaration where
  source := source
  principal := principal
  namedCapabilityAdmissible := namedCapabilityAdmissible
  accepted :=
    { authorization := authorization
      preStateBound := rfl
      requestBound := rfl
      effectsDigestBound := rfl
      modeEvidence := ⟨⟨wellFormed, fresh⟩⟩
      validated := validated
      postcondition := validated.resultAt
      disclosure := .sealed
      disclosureAllowed := trivial }

section AcceptedLaws

variable
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration}
    {M : LogMaterializer}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store} {config : Config}
    {portal : Portal} {declaration : Declaration}

theorem Accepted.wellFormed (accepted : Accepted content M store config portal declaration) :
    declaration.record.CausallyWellFormed :=
  accepted.accepted.modeEvidence.down.wellFormed

theorem Accepted.pre_fresh (accepted : Accepted content M store config portal declaration) :
    store (eventAddress (declaration.key config)) = none :=
  accepted.accepted.modeEvidence.down.fresh

@[simp] theorem Accepted.post_contains
    (accepted : Accepted content M store config portal declaration) :
    accepted.accepted.prepared.post.logical (eventAddress (declaration.key config)) =
      some declaration.record := by
  change Minidregg.Theory.Store.Patch.run store [declaration.appendOp config]
    (eventAddress (declaration.key config)) = some declaration.record
  simp [Declaration.appendOp, Minidregg.Theory.Store.Op.apply, eventAddress]
  rfl

/-- The same event cannot be appended again to the accepted post. -/
theorem Accepted.duplicate_rejected
    (accepted : Accepted content M store config portal declaration) :
    ¬ (Minidregg.Kernel.HyperdocumentEventLog.Sparse.appendOp
      (declaration.stored config accepted.wellFormed)).Enabled
      accepted.accepted.prepared.post.logical := by
  intro enabled
  have fresh := (Minidregg.Kernel.HyperdocumentEventLog.Sparse.appendOp_enabled_iff _ _).1 enabled
  have present := accepted.post_contains
  change accepted.accepted.prepared.post.logical
    (eventAddress (declaration.key config)) = none at fresh
  rw [present] at fresh
  contradiction

end AcceptedLaws

/-- info: 'Minidregg.Kernel.HyperdocumentVersionEffects.SourceExact.post_root_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceExact.post_root_exact
/-- info: 'Minidregg.Kernel.HyperdocumentVersionEffects.SourceExact.request_id_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceExact.request_id_exact
/-- info: 'Minidregg.Kernel.HyperdocumentVersionEffects.Accepted.post_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.post_contains
/-- info: 'Minidregg.Kernel.HyperdocumentVersionEffects.Accepted.duplicate_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.duplicate_rejected

end Minidregg.Kernel.HyperdocumentVersionEffects
