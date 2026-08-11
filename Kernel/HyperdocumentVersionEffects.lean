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

def Declaration.fieldWrite (config : Config) (declaration : Declaration) :
    CellState.FieldWrite Minidregg.Kernel.HyperdocumentEventLog.cellSchema where
  field := ⟨Minidregg.Kernel.HyperdocumentEventLog.Sparse.Namespace.events, declaration.key config⟩
  value := some declaration.record

def Declaration.patch (config : Config) (declaration : Declaration) :
    CellState.Patch Minidregg.Kernel.HyperdocumentEventLog.cellSchema Digest where
  expectedPreRoot := declaration.expectedLogRoot
  fieldFootprint := {declaration.fieldWrite config |>.field}
  resourceFootprint := ∅
  fieldWrites := [declaration.fieldWrite config]
  resourceWrites := []

@[simp] theorem Declaration.patch_namedFields
    (config : Config) (declaration : Declaration) :
    (declaration.patch config).namedFields =
      (declaration.patch config).fieldFootprint := by
  simp [Declaration.patch, CellState.Patch.namedFields]

@[simp] theorem Declaration.patch_namedResources
    (config : Config) (declaration : Declaration) :
    (declaration.patch config).namedResources =
      (declaration.patch config).resourceFootprint := by
  simp [Declaration.patch, CellState.Patch.namedResources]

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

/-! ## Accepted event-log effect plus typed sparse allocation -/

def sparsePre (representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest)
    (store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store) :
    Minidregg.Kernel.HyperdocumentEventLog.Sparse.Cell representation.sparseMaterializer :=
  Minidregg.Kernel.SparseAuthenticatedState.materialize
    representation.sparseMaterializer store

def cellPre (representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest)
    (store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store) :
    CellState.Materialized representation.cellMaterializer :=
  CellState.materialize representation.cellMaterializer store.toCellState

def sealedOnly : DisclosureDecision Unit Unit (fun _ => Unit) → Prop
  | .sealed => True
  | .reveal _ _ => False
  | .declassify _ _ _ => False

def family (representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest)
    (config : Config) :
    SemanticEffectFamily Minidregg.Kernel.HyperdocumentEventLog.cellSchema
      representation.cellMaterializer Nat where
  Declaration := Declaration
  declarationCodec := config.declarationCodec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => Minidregg.Theory.HyperdocumentOperations.unitCodec
  ModeEvidence := fun declaration _ => PLift declaration.record.CausallyWellFormed
  effectDigest := Declaration.effectDigest config
  patch := fun declaration _ => declaration.patch config
  nullifier := fun declaration _ => some declaration.record.operation.digest.value
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

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
    (representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest)
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
  sourceWellFormed : declaration.record.CausallyWellFormed
  sparse : Minidregg.Kernel.HyperdocumentEventLog.Sparse.AcceptedAppend representation.sparseMaterializer
    (sparsePre representation store)
    (declaration.stored config sourceWellFormed)
  accepted : AcceptedCellEffect
    (portal := portal)
    (authState := CredentialAuthorityState.authState projection authorityPre)
    (family representation config) (declaration.toRequest config)
    (cellPre representation store) declaration ()

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
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
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
    (fresh : store Minidregg.Kernel.HyperdocumentEventLog.Sparse.Namespace.events
      (declaration.key config) = none)
    (authorization : Authorized portal
      (CredentialAuthorityState.authState projection authorityPre)
      (declaration.toRequest config))
    (validated : CellState.ValidatedPatch representation.cellMaterializer
      (cellPre representation store) (declaration.patch config)) :
    Accepted content representation store config portal declaration where
  source := source
  principal := principal
  namedCapabilityAdmissible := namedCapabilityAdmissible
  sourceWellFormed := wellFormed
  sparse := Minidregg.Kernel.HyperdocumentEventLog.Sparse.accept (declaration.stored config wellFormed) fresh
  accepted :=
    { authorization := authorization
      effectsDigestBound := rfl
      preRootBound := validated.preRoot_bound
      modeEvidence := ⟨wellFormed⟩
      validated := validated
      disclosure := .sealed
      disclosureAllowed := trivial }

@[simp] theorem Accepted.post_contains
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration}
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store} {config : Config}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted content representation store config portal declaration) :
    accepted.accepted.prepared.post.logical.fields
      ⟨Minidregg.Kernel.HyperdocumentEventLog.Sparse.Namespace.events, declaration.key config⟩ =
      some declaration.record := by
  change CellState.applyFieldWrites [declaration.fieldWrite config]
    (cellPre representation store).logical.fields
    ⟨Minidregg.Kernel.HyperdocumentEventLog.Sparse.Namespace.events,
      declaration.key config⟩ = some declaration.record
  simp [CellState.applyFieldWrites, CellState.FieldStore.assign,
    Declaration.fieldWrite]
  rfl

theorem Accepted.pre_fresh
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration}
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store} {config : Config}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted content representation store config portal declaration) :
    store Minidregg.Kernel.HyperdocumentEventLog.Sparse.Namespace.events (declaration.key config) = none := by
  exact accepted.sparse.pre_fresh

theorem Accepted.duplicate_rejected
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Minidregg.Theory.HyperdocumentOperations.Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal} {contentDeclaration : Minidregg.Theory.HyperdocumentOperations.Declaration}
    {content : Minidregg.Theory.HyperdocumentOperations.Accepted contentConfig projection authorityPre
      documentPre contentPortal contentDeclaration}
    {representation : Minidregg.Kernel.HyperdocumentEventLog.Representation Digest}
    {store : Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store} {config : Config}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted content representation store config portal declaration) :
    ¬ (Minidregg.Kernel.HyperdocumentEventLog.Sparse.appendOp
      (declaration.stored config accepted.sourceWellFormed)).Enabled
      accepted.sparse.post.logical :=
  accepted.sparse.duplicate_rejected

/-- info: 'Minidregg.Kernel.HyperdocumentVersionEffects.SourceExact.post_root_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceExact.post_root_exact
/-- info: 'Minidregg.Kernel.HyperdocumentVersionEffects.SourceExact.request_id_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceExact.request_id_exact
/-- info: 'Minidregg.Kernel.HyperdocumentVersionEffects.Accepted.post_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.post_contains
/-- info: 'Minidregg.Kernel.HyperdocumentVersionEffects.Accepted.duplicate_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.duplicate_rejected

end Minidregg.Kernel.HyperdocumentVersionEffects
