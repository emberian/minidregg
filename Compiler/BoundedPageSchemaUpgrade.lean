/-
# Compiler.BoundedPageSchemaUpgrade -- admitted next-catalogue representation cutover

The current bounded content, event-history, and authority-policy pages have
independent wire versions in one dependent extension catalogue. This module
constructs the next catalogue generation over those CURRENT typed carriers.
Each page wire version advances from its own pinned version; in this source
that is content 1→2, events 1→2, and authority 4→5. It does not reconstruct a
historical parser using today's expanded authority vocabulary.

The next generation preserves the finite sparse logical carriers and their
canonical semantic projections while changing each page frame, page-codec
pin, controller pin, schema pin, root domain, and the catalogue generation.

Consequently migration is an exact identity on typed logical state, but it is
not an identity on bytes.  Both generations remain separately decodable, and
a mixed fleet can compare their canonical semantic projections without
equating current and next page roots.  Catalog transition admission is
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

/-! ## Exact next-generation codecs over the current typed state carriers -/

/-- Page wire versions advance from their own deployed pins, independently of
catalog generations. In this catalogue: content 1→2, events 1→2, authority 4→5. -/
def nextWireVersion (kind : PageKind) : Nat := (controller kind).wireVersion + 1

theorem nextWireVersion_fits (kind : PageKind) : nextWireVersion kind < 256 := by
  cases kind <;> decide

/-- The proof argument prevents a future version increment from wrapping. -/
def nextWireVersionByte (kind : PageKind) : UInt8 :=
  UInt8.ofNatLT (nextWireVersion kind) (nextWireVersion_fits kind)

@[simp] theorem nextWireVersionByte_exact (kind : PageKind) :
    (nextWireVersionByte kind).toNat = nextWireVersion kind := rfl

theorem nextWireVersion_strict (kind : PageKind) :
    (controller kind).wireVersion < nextWireVersion kind := Nat.lt_succ_self _

def stateStreamNext : (kind : PageKind) → StreamCodec kind.State
  | .content => HyperdocumentContentPageMaterializer.stateStream
  | .eventHistory => HyperdocumentEventPageMaterializer.stateStream
  | .authorityPolicy => CredentialAuthorityPageMaterializer.stateStream

/-- Retain the source-owned kind prefix and capacity, advance only its version. -/
def wireFrameNext (kind : PageKind) : List UInt8 :=
  let old := (controller kind).wireFrame
  old.take (old.length - 2) ++ [nextWireVersionByte kind, 4]

def encodeNext (kind : PageKind) (state : kind.State) : List UInt8 :=
  wireFrameNext kind ++ (stateStreamNext kind).encode state

def decodeNextRaw (kind : PageKind) (bytes : List UInt8) : Option kind.State :=
  if bytes.take (wireFrameNext kind).length = wireFrameNext kind then
    (stateStreamNext kind).toLawful.decode (bytes.drop (wireFrameNext kind).length)
  else none

@[simp] theorem decodeNextRaw_encode (kind : PageKind) (state : kind.State) :
    decodeNextRaw kind (encodeNext kind state) = some state := by
  have payload := (stateStreamNext kind).toLawful.decode_encode state
  change (stateStreamNext kind).toLawful.decode
    ((stateStreamNext kind).encode state) = some state at payload
  simp [decodeNextRaw, encodeNext, payload]

def decodeNext (kind : PageKind) (bytes : List UInt8) : Option kind.State := do
  let state ← decodeNextRaw kind bytes
  if encodeNext kind state = bytes then some state else none

@[simp] theorem decodeNext_encode (kind : PageKind) (state : kind.State) :
    decodeNext kind (encodeNext kind state) = some state := by simp [decodeNext]

theorem decodeNext_canonical (kind : PageKind) {bytes : List UInt8}
    {state : kind.State} (accepted : decodeNext kind bytes = some state) :
    encodeNext kind state = bytes := by
  unfold decodeNext at accepted
  cases raw : decodeNextRaw kind bytes with
  | none => simp [raw] at accepted
  | some selected =>
      simp only [raw, bind, Option.bind] at accepted
      split at accepted
      next canonical => cases Option.some.inj accepted; exact canonical
      next => contradiction

def stateCodecNext (kind : PageKind) : LawfulCodec kind.State where
  encode := encodeNext kind
  decode := decodeNext kind
  decode_encode := decodeNext_encode kind

def rootCustomizationNext (kind : PageKind) : List UInt8 :=
  let stem := match kind with
    | .content => "LOOM.HDOC.CONTENTPAGE.ROOT/v"
    | .eventHistory => "LOOM.HDOC.EVENTPAGE.ROOT/v"
    | .authorityPolicy => "LOOM.AUTH.POLICYPAGE.ROOT/v"
  (stem ++ toString (nextWireVersion kind)).toUTF8.toList

def rootNext (kind : PageKind) (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash (rootCustomizationNext kind) bytes).digest

def controllerNext (kind : PageKind) : Controller kind where
  schemaId := match kind with
    | .content => ⟨91101⟩ | .eventHistory => ⟨91102⟩ | .authorityPolicy => ⟨91103⟩
  pageCodecId := match kind with
    | .content => ⟨92101⟩ | .eventHistory => ⟨92102⟩ | .authorityPolicy => ⟨92103⟩
  controllerId := match kind with
    | .content => ⟨94101⟩ | .eventHistory => ⟨94102⟩ | .authorityPolicy => ⟨94103⟩
  rootAlgorithmId := ⟨93001⟩
  wireVersion := nextWireVersion kind
  capacity := (controller kind).capacity
  wireFrame := wireFrameNext kind
  rootCustomization := rootCustomizationNext kind
  codec := stateCodecNext kind
  rootBytes := rootNext kind

@[simp] theorem controllerNext_version (kind : PageKind) :
    (controllerNext kind).wireVersion = (controller kind).wireVersion + 1 := rfl

@[simp] theorem controllerNext_capacity (kind : PageKind) :
    (controllerNext kind).capacity = (controller kind).capacity := rfl

/-! ## Typed migration and semantic projection -/

/-- The next catalogue changes representation identity, not the typed logical carrier. -/
def migrate (kind : PageKind) (state : kind.State) : kind.State := state

def oldCanonicalBytes (kind : PageKind) (state : kind.State) : List UInt8 :=
  (controller kind).codec.encode state

def newCanonicalBytes (kind : PageKind) (state : kind.State) : List UInt8 :=
  (controllerNext kind).codec.encode (migrate kind state)

@[simp] theorem migrate_exact (kind : PageKind) (state : kind.State) :
    migrate kind state = state := rfl

@[simp] theorem decode_new_migration (kind : PageKind) (state : kind.State) :
    (controllerNext kind).codec.decode (newCanonicalBytes kind state) = some state := by
  exact (controllerNext kind).codec.decode_encode state

theorem new_decoder_rejects_old (kind : PageKind) (state : kind.State) :
    (controllerNext kind).codec.decode (oldCanonicalBytes kind state) = none := by
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
      (controllerNext kind).rootBytes (newCanonicalBytes kind state)

structure MigrationDigestSeparation (kind : PageKind)
    (state : kind.State) : Prop where
  noCollision : ¬ MigrationRootCollision kind state

theorem migration_roots_differ (kind : PageKind) (state : kind.State)
    (binding : MigrationDigestSeparation kind state) :
    (controller kind).rootBytes (oldCanonicalBytes kind state) ≠
      (controllerNext kind).rootBytes (newCanonicalBytes kind state) := by
  intro equal
  exact binding.noCollision ⟨migration_changes_canonical_bytes kind state, equal⟩

/-! ## Exact upgraded catalog -/

def upgradedCatalog : Catalog where
  catalogVersion := 2
  content := (controllerNext .content).catalogEntry
  eventHistory := (controllerNext .eventHistory).catalogEntry
  authorityPolicy := (controllerNext .authorityPolicy).catalogEntry

@[simp] theorem upgradedCatalog_lookup_exact (kind : PageKind) :
    upgradedCatalog.lookup kind = some (controllerNext kind).catalogEntry := by
  cases kind <;> rfl

@[simp] theorem upgradedCatalog_entry_exact (kind : PageKind) :
    upgradedCatalog.entry kind = (controllerNext kind).catalogEntry := by
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
  new.entry .content = (controllerNext .content).catalogEntry ∧
  old.entry .eventHistory = (controller .eventHistory).catalogEntry ∧
  new.entry .eventHistory = (controllerNext .eventHistory).catalogEntry ∧
  old.entry .authorityPolicy = (controller .authorityPolicy).catalogEntry ∧
  new.entry .authorityPolicy = (controllerNext .authorityPolicy).catalogEntry

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
  have currentExact : 1 = mixedControllerRequest.fromVersion := rfl
  have monotone : mixedControllerRequest.fromVersion < mixedControllerRequest.toVersion := by decide
  have incompatible : ¬ ControllersCompatible mixedControllerRequest.fromCatalog
      mixedControllerRequest.toCatalog := by
    intro compatible
    have pins := congrArg CatalogEntry.schemaId compatible.2.2.2.1
    change (⟨91002⟩ : Digest) = ⟨91102⟩ at pins
    cases pins
  simp only [admit, dif_pos currentExact, dif_pos monotone, dif_neg incompatible]

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
