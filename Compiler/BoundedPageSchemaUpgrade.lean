/-
# Compiler.BoundedPageSchemaUpgrade -- admitted V1 -> V2 page/catalog cutover

The bounded content, event-history, and authority-policy pages have exact V1
wire formats and a dependent extension catalog.  This module defines one
concrete V2 protocol generation for all three page kinds.  V2 deliberately
keeps the finite sparse logical carriers and their canonical semantic
projections unchanged while changing every page frame, page-codec pin,
controller pin, schema pin, root domain, and the catalog generation.

Consequently migration is an exact identity on typed logical state, but it is
not an identity on bytes.  Both generations remain separately decodable, and
a mixed fleet can compare their canonical semantic projections without
pretending that V1 and V2 roots are equal.  Catalog transition admission is
fail closed: the current generation, monotone direction, exact old/new
controller rows, exact policy pins, and an operator authorization token are all
checked before an admitted witness exists.

**Trust ceiling.**  The authorization token below is a governance input, not a
signature verifier.  A deployment must refine its operator/quorum procedure to
that exact token.  Distinct cSHAKE roots require the explicit pair-scoped
digest-separation premise below; no finite digest is claimed globally
injective.  This module says nothing about physical persistence, replica
delivery, or availability; those boundaries are kept explicit by the cutover
module which consumes this admission witness.
-/
import Compiler.BoundedPageExtensionCatalog

namespace Minidregg.Compiler.BoundedPageSchemaUpgrade

open Minidregg.Compiler.BoundedPageExtensionCatalog
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Exact V2 codecs over the existing typed state carriers -/

def contentWireFrameV2 : List UInt8 :=
  [76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 67, 79, 78, 84, 69, 78, 84, 80,
    65, 71, 69, 2, 4]

def eventWireFrameV2 : List UInt8 :=
  [76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 69, 86, 69, 78, 84, 80, 65, 71,
    69, 2, 4]

def authorityWireFrameV2 : List UInt8 :=
  [76, 79, 79, 77, 47, 65, 85, 84, 72, 47, 80, 79, 76, 73, 67, 89, 80, 65,
    71, 69, 2, 4]

def decodeContentV2 : List UInt8 -> Option PageKind.content.State
  | 76 :: 79 :: 79 :: 77 :: 47 :: 72 :: 68 :: 79 :: 67 :: 47 :: 67 :: 79 ::
      78 :: 84 :: 69 :: 78 :: 84 :: 80 :: 65 :: 71 :: 69 :: 2 :: 4 :: payload =>
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.stateStream.toLawful.decode
        payload
  | _ => none

def decodeEventV2 : List UInt8 -> Option PageKind.eventHistory.State
  | 76 :: 79 :: 79 :: 77 :: 47 :: 72 :: 68 :: 79 :: 67 :: 47 :: 69 :: 86 ::
      69 :: 78 :: 84 :: 80 :: 65 :: 71 :: 69 :: 2 :: 4 :: payload =>
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.stateStream.toLawful.decode
        payload
  | _ => none

def decodeAuthorityV2 : List UInt8 -> Option PageKind.authorityPolicy.State
  | 76 :: 79 :: 79 :: 77 :: 47 :: 65 :: 85 :: 84 :: 72 :: 47 :: 80 :: 79 ::
      76 :: 73 :: 67 :: 89 :: 80 :: 65 :: 71 :: 69 :: 2 :: 4 :: payload =>
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.stateStream.toLawful.decode
        payload
  | _ => none

def contentStateCodecV2 : LawfulCodec PageKind.content.State where
  encode state := contentWireFrameV2 ++
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.stateStream.encode state
  decode := decodeContentV2
  decode_encode := by
    intro state
    change
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.stateStream.toLawful.decode
        (Minidregg.Compiler.HyperdocumentContentPageMaterializer.stateStream.encode state) =
          some state
    exact
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.stateStream.toLawful.decode_encode
        state

def eventStateCodecV2 : LawfulCodec PageKind.eventHistory.State where
  encode state := eventWireFrameV2 ++
    Minidregg.Compiler.HyperdocumentEventPageMaterializer.stateStream.encode state
  decode := decodeEventV2
  decode_encode := by
    intro state
    change
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.stateStream.toLawful.decode
        (Minidregg.Compiler.HyperdocumentEventPageMaterializer.stateStream.encode state) =
          some state
    exact
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.stateStream.toLawful.decode_encode
        state

def authorityStateCodecV2 : LawfulCodec PageKind.authorityPolicy.State where
  encode state := authorityWireFrameV2 ++
    Minidregg.Compiler.CredentialAuthorityPageMaterializer.stateStream.encode state
  decode := decodeAuthorityV2
  decode_encode := by
    intro state
    change
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.stateStream.toLawful.decode
        (Minidregg.Compiler.CredentialAuthorityPageMaterializer.stateStream.encode state) =
          some state
    exact
      Minidregg.Compiler.CredentialAuthorityPageMaterializer.stateStream.toLawful.decode_encode
        state

def contentRootCustomizationV2 : List UInt8 :=
  [76, 79, 79, 77, 46, 72, 68, 79, 67, 46, 67, 79, 78, 84, 69, 78, 84, 80,
    65, 71, 69, 46, 82, 79, 79, 84, 47, 118, 50]

def eventRootCustomizationV2 : List UInt8 :=
  [76, 79, 79, 77, 46, 72, 68, 79, 67, 46, 69, 86, 69, 78, 84, 80, 65, 71,
    69, 46, 82, 79, 79, 84, 47, 118, 50]

def authorityRootCustomizationV2 : List UInt8 :=
  [76, 79, 79, 77, 46, 65, 85, 84, 72, 46, 80, 79, 76, 73, 67, 89, 80, 65,
    71, 69, 46, 82, 79, 79, 84, 47, 118, 50]

def rootV2 (customization bytes : List UInt8) : Digest :=
  (Minidregg.Compiler.Sp800185Cshake256.hash customization bytes).digest

def controllerV2 : (kind : PageKind) -> Controller kind
  | .content =>
      { schemaId := ⟨91101⟩
        pageCodecId := ⟨92101⟩
        controllerId := ⟨94101⟩
        rootAlgorithmId := ⟨93001⟩
        wireVersion := 2
        capacity := 4
        wireFrame := contentWireFrameV2
        rootCustomization := contentRootCustomizationV2
        codec := contentStateCodecV2
        rootBytes := rootV2 contentRootCustomizationV2 }
  | .eventHistory =>
      { schemaId := ⟨91102⟩
        pageCodecId := ⟨92102⟩
        controllerId := ⟨94102⟩
        rootAlgorithmId := ⟨93001⟩
        wireVersion := 2
        capacity := 4
        wireFrame := eventWireFrameV2
        rootCustomization := eventRootCustomizationV2
        codec := eventStateCodecV2
        rootBytes := rootV2 eventRootCustomizationV2 }
  | .authorityPolicy =>
      { schemaId := ⟨91103⟩
        pageCodecId := ⟨92103⟩
        controllerId := ⟨94103⟩
        rootAlgorithmId := ⟨93001⟩
        wireVersion := 2
        capacity := 4
        wireFrame := authorityWireFrameV2
        rootCustomization := authorityRootCustomizationV2
        codec := authorityStateCodecV2
        rootBytes := rootV2 authorityRootCustomizationV2 }

@[simp] theorem controllerV2_version (kind : PageKind) :
    (controllerV2 kind).wireVersion = 2 := by
  cases kind <;> rfl

@[simp] theorem controllerV2_capacity (kind : PageKind) :
    (controllerV2 kind).capacity = (controller kind).capacity := by
  cases kind <;> rfl

/-! ## Typed migration and semantic projection -/

/-- V2 changes representation identity, not the typed logical carrier. -/
def migrate (kind : PageKind) (state : kind.State) : kind.State := state

def oldCanonicalBytes (kind : PageKind) (state : kind.State) : List UInt8 :=
  (controller kind).codec.encode state

def newCanonicalBytes (kind : PageKind) (state : kind.State) : List UInt8 :=
  (controllerV2 kind).codec.encode (migrate kind state)

@[simp] theorem migrate_exact (kind : PageKind) (state : kind.State) :
    migrate kind state = state := rfl

@[simp] theorem decode_new_migration (kind : PageKind) (state : kind.State) :
    (controllerV2 kind).codec.decode (newCanonicalBytes kind state) = some state := by
  exact (controllerV2 kind).codec.decode_encode state

theorem new_decoder_rejects_old (kind : PageKind) (state : kind.State) :
    (controllerV2 kind).codec.decode (oldCanonicalBytes kind state) = none := by
  cases kind <;> rfl

theorem old_decoder_rejects_new (kind : PageKind) (state : kind.State) :
    (controller kind).codec.decode (newCanonicalBytes kind state) = none := by
  cases kind <;> rfl

theorem migration_changes_canonical_bytes (kind : PageKind)
    (state : kind.State) :
    oldCanonicalBytes kind state ≠ newCanonicalBytes kind state := by
  intro same
  have rejected := new_decoder_rejects_old kind state
  have accepted := decode_new_migration kind state
  rw [same, accepted] at rejected
  contradiction

/-- The canonical semantic carrier for each bounded representation shard. -/
def Semantic : PageKind -> Type
  | .content => Option (LogicalState Theory.Hyperdocument.cellSchema)
  | .eventHistory =>
      Option Minidregg.Kernel.HyperdocumentEventLog.Sparse.Store
  | .authorityPolicy =>
      Option (LogicalState Theory.CredentialAuthorityState.schema)

def semanticProjection : (kind : PageKind) -> kind.State -> Semantic kind
  | .content, state =>
      (Minidregg.Compiler.HyperdocumentContentPageMaterializer.pageAt state).map
        Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page.toCanonicalState
  | .eventHistory, state =>
      (Minidregg.Compiler.HyperdocumentEventPageMaterializer.pageAt state).map
        Minidregg.Compiler.HyperdocumentEventPageMaterializer.Page.toSparseStore
  | .authorityPolicy, state =>
      (Minidregg.Compiler.CredentialAuthorityPageMaterializer.pageAt state).map
        Minidregg.Compiler.CredentialAuthorityPageMaterializer.Page.toCanonicalState

@[simp] theorem migration_preserves_semantic_projection (kind : PageKind)
    (state : kind.State) :
    semanticProjection kind (migrate kind state) = semanticProjection kind state :=
  rfl

/-! ## Root changes require a pair-scoped cryptographic premise -/

structure MigrationRootCollision (kind : PageKind) (state : kind.State) : Prop where
  bytesDifferent : oldCanonicalBytes kind state ≠ newCanonicalBytes kind state
  rootsEqual :
    (controller kind).rootBytes (oldCanonicalBytes kind state) =
      (controllerV2 kind).rootBytes (newCanonicalBytes kind state)

structure MigrationDigestSeparation (kind : PageKind)
    (state : kind.State) : Prop where
  noCollision : ¬ MigrationRootCollision kind state

theorem migration_roots_differ (kind : PageKind) (state : kind.State)
    (binding : MigrationDigestSeparation kind state) :
    (controller kind).rootBytes (oldCanonicalBytes kind state) ≠
      (controllerV2 kind).rootBytes (newCanonicalBytes kind state) := by
  intro equal
  exact binding.noCollision ⟨migration_changes_canonical_bytes kind state, equal⟩

/-! ## Exact upgraded catalog -/

def upgradedCatalog : Catalog where
  catalogVersion := 2
  content := (controllerV2 .content).catalogEntry
  eventHistory := (controllerV2 .eventHistory).catalogEntry
  authorityPolicy := (controllerV2 .authorityPolicy).catalogEntry

@[simp] theorem upgradedCatalog_lookup_exact (kind : PageKind) :
    upgradedCatalog.lookup kind = some (controllerV2 kind).catalogEntry := by
  cases kind <;> rfl

@[simp] theorem upgradedCatalog_entry_exact (kind : PageKind) :
    upgradedCatalog.entry kind = (controllerV2 kind).catalogEntry := by
  cases kind <;> rfl

theorem upgradedCatalog_ne_deployed : upgradedCatalog ≠ deployedCatalog := by
  intro same
  have version := congrArg Catalog.catalogVersion same
  simp [upgradedCatalog, deployedCatalog] at version

theorem catalog_migration_changes_canonical_bytes :
    catalogCodec.encode upgradedCatalog ≠ catalogCodec.encode deployedCatalog := by
  intro same
  exact upgradedCatalog_ne_deployed (catalogCodec_encode_injective same)

theorem catalog_migration_changes_content_address :
    upgradedCatalog.contentAddress ≠ deployedCatalog.contentAddress :=
  contentAddress_ne_of_catalog_ne upgradedCatalog_ne_deployed

/-! ## Policy/controller gated transition admission -/

/-- Governance pins are canonical data.  `authorizationToken` is the exact
result which an external operator/signature procedure must justify. -/
structure OperatorPolicy where
  policyId : Digest
  operatorSetRoot : Digest
  operatorEpoch : Nat
  fromVersion : Nat
  toVersion : Nat
  oldCatalogBytes : List UInt8
  newCatalogBytes : List UInt8
  oldCatalogDigest : Digest
  newCatalogDigest : Digest
  authorizationToken : Digest
  deriving DecidableEq, Repr

def approvedPolicy : OperatorPolicy where
  policyId := ⟨96001⟩
  operatorSetRoot := ⟨96002⟩
  operatorEpoch := 7
  fromVersion := 1
  toVersion := 2
  oldCatalogBytes := catalogCodec.encode deployedCatalog
  newCatalogBytes := catalogCodec.encode upgradedCatalog
  oldCatalogDigest := deployedCatalog.contentAddress.digest
  newCatalogDigest := upgradedCatalog.contentAddress.digest
  authorizationToken := ⟨96003⟩

structure UpgradeRequest where
  fromCatalog : Catalog
  toCatalog : Catalog
  fromVersion : Nat
  toVersion : Nat
  policy : OperatorPolicy
  presentedAuthorization : Digest
  deriving DecidableEq, Repr

def ControllersCompatible (old new : Catalog) : Prop :=
  old.entry .content = (controller .content).catalogEntry ∧
  new.entry .content = (controllerV2 .content).catalogEntry ∧
  old.entry .eventHistory = (controller .eventHistory).catalogEntry ∧
  new.entry .eventHistory = (controllerV2 .eventHistory).catalogEntry ∧
  old.entry .authorityPolicy = (controller .authorityPolicy).catalogEntry ∧
  new.entry .authorityPolicy = (controllerV2 .authorityPolicy).catalogEntry

instance controllersCompatibleDecidable (old new : Catalog) :
    Decidable (ControllersCompatible old new) := by
  unfold ControllersCompatible
  infer_instance

def PolicyMatches (request : UpgradeRequest) : Prop :=
  request.policy = approvedPolicy ∧
  request.presentedAuthorization = approvedPolicy.authorizationToken ∧
  request.fromVersion = approvedPolicy.fromVersion ∧
  request.toVersion = approvedPolicy.toVersion ∧
  request.policy.oldCatalogBytes = catalogCodec.encode request.fromCatalog ∧
  request.policy.newCatalogBytes = catalogCodec.encode request.toCatalog ∧
  request.policy.oldCatalogDigest = request.fromCatalog.contentAddress.digest ∧
  request.policy.newCatalogDigest = request.toCatalog.contentAddress.digest

instance policyMatchesDecidable (request : UpgradeRequest) :
    Decidable (PolicyMatches request) := by
  unfold PolicyMatches
  infer_instance

inductive AdmissionError where
  | staleCurrentVersion
  | nonIncreasingVersion
  | incompatibleControllers
  | policyRejected
  deriving DecidableEq, Repr

structure AdmittedUpgrade (currentVersion : Nat) where
  request : UpgradeRequest
  currentExact : currentVersion = request.fromVersion
  monotone : request.fromVersion < request.toVersion
  controllersCompatible :
    ControllersCompatible request.fromCatalog request.toCatalog
  policyMatches : PolicyMatches request

def admit (currentVersion : Nat) (request : UpgradeRequest) :
    Except AdmissionError (AdmittedUpgrade currentVersion) :=
  if currentExact : currentVersion = request.fromVersion then
    if monotone : request.fromVersion < request.toVersion then
      if compatible : ControllersCompatible request.fromCatalog request.toCatalog then
        if policy : PolicyMatches request then
          .ok ⟨request, currentExact, monotone, compatible, policy⟩
        else .error .policyRejected
      else .error .incompatibleControllers
    else .error .nonIncreasingVersion
  else .error .staleCurrentVersion

def approvedRequest : UpgradeRequest where
  fromCatalog := deployedCatalog
  toCatalog := upgradedCatalog
  fromVersion := 1
  toVersion := 2
  policy := approvedPolicy
  presentedAuthorization := approvedPolicy.authorizationToken

theorem approved_current_exact : 1 = approvedRequest.fromVersion := rfl

theorem approved_monotone :
    approvedRequest.fromVersion < approvedRequest.toVersion := by decide

theorem approved_controllers_compatible :
    ControllersCompatible approvedRequest.fromCatalog approvedRequest.toCatalog :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem approved_policy_matches : PolicyMatches approvedRequest :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def approvedWitness : AdmittedUpgrade 1 where
  request := approvedRequest
  currentExact := approved_current_exact
  monotone := approved_monotone
  controllersCompatible := approved_controllers_compatible
  policyMatches := approved_policy_matches

theorem approved_request_admitted :
    ∃ witness : AdmittedUpgrade 1, admit 1 approvedRequest = .ok witness := by
  refine ⟨approvedWitness, ?_⟩
  simp only [admit, dif_pos approved_current_exact, dif_pos approved_monotone,
    dif_pos approved_controllers_compatible, dif_pos approved_policy_matches]
  rfl

/-- Once generation 2 is active, replaying the old 1 -> 2 request is stale. -/
@[simp] theorem rollback_after_cutover_rejected :
    admit 2 approvedRequest = .error .staleCurrentVersion := by
  rfl

def downgradeRequest : UpgradeRequest where
  fromCatalog := upgradedCatalog
  toCatalog := deployedCatalog
  fromVersion := 2
  toVersion := 1
  policy := approvedPolicy
  presentedAuthorization := approvedPolicy.authorizationToken

@[simp] theorem downgrade_rejected :
    admit 2 downgradeRequest = .error .nonIncreasingVersion := by
  rfl

def mixedControllerRequest : UpgradeRequest :=
  { approvedRequest with
    toCatalog := upgradedCatalog.setEntry .eventHistory
      (controller .eventHistory).catalogEntry }

@[simp] theorem mixed_controller_catalog_rejected :
    admit 1 mixedControllerRequest = .error .incompatibleControllers := by
  rfl

/-! ## Mixed-generation page recovery remains semantically coherent -/

inductive Generation where
  | v1
  | v2
  deriving DecidableEq, Repr

structure RecoveredPage (kind : PageKind) where
  generation : Generation
  state : kind.State
  canonicalBytes : List UInt8
  bytesExact : canonicalBytes =
    match generation with
    | .v1 => oldCanonicalBytes kind state
    | .v2 => newCanonicalBytes kind state

def recoverOld (kind : PageKind) (state : kind.State) : RecoveredPage kind where
  generation := .v1
  state := state
  canonicalBytes := oldCanonicalBytes kind state
  bytesExact := rfl

def recoverNew (kind : PageKind) (state : kind.State) : RecoveredPage kind where
  generation := .v2
  state := migrate kind state
  canonicalBytes := newCanonicalBytes kind state
  bytesExact := rfl

def RecoveredPage.semantics {kind : PageKind}
    (page : RecoveredPage kind) : Semantic kind :=
  semanticProjection kind page.state

theorem mixed_generation_semantics_agree (kind : PageKind) (state : kind.State) :
    (recoverOld kind state).semantics = (recoverNew kind state).semantics :=
  rfl

theorem mixed_generation_bytes_differ (kind : PageKind) (state : kind.State) :
    (recoverOld kind state).canonicalBytes ≠
      (recoverNew kind state).canonicalBytes :=
  migration_changes_canonical_bytes kind state

/-! ## Axiom pins -/

/-- info: 'Minidregg.Compiler.BoundedPageSchemaUpgrade.migration_preserves_semantic_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms migration_preserves_semantic_projection
/-- info: 'Minidregg.Compiler.BoundedPageSchemaUpgrade.catalog_migration_changes_content_address' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms catalog_migration_changes_content_address
/-- info: 'Minidregg.Compiler.BoundedPageSchemaUpgrade.downgrade_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms downgrade_rejected

end Minidregg.Compiler.BoundedPageSchemaUpgrade
