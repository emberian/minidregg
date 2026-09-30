/-
# Theory.DeployedMaterializerWitness -- the deployed layouts are inhabited

The old total-function field carrier made several deployed schemas provably
unmaterializable (`MaterializerCardinality.totalEffectMaterializer_isEmpty` keeps
that tooth).  Every cell is now one `Store L`, a finitely supported dependent
map, and a `Store L` is countable whenever its namespaces, keys and values are.
This file closes the three Theory-side layouts (declared effects, canonical
authority, Hyperdocument) with actual lawful codecs, materializers, and
materialized empty cells.

The codecs chosen from `Countable` are existence witnesses, not deployment wire
formats.  Their role is to refute carrier vacuity.  A deployed artifact must
still select and pin a concrete codec and root function (`Compiler.StoreCodec`).
-/
import Mathlib.Tactic.DeriveCountable
import Theory.CredentialAuthorityState
import Theory.Hyperdocument
import Theory.MaterializerCardinality

namespace Minidregg.Theory.DeployedMaterializerWitness

open CellState
open IndexedProgram
open TypedAuthorization
open CredentialAuthorityState
open Hyperdocument
open Minidregg.Theory.Store

set_option autoImplicit false

/-! ## Countability of the authority layout -/

deriving instance Countable for SubjectId
deriving instance Countable for IssuerId
deriving instance Countable for PolicyId
deriving instance Countable for FederationId
deriving instance Countable for CapabilityId
deriving instance Countable for ChannelId
deriving instance Countable for Digest
deriving instance Countable for ResourceKind
deriving instance Countable for ResourceId
deriving instance Countable for Verb
deriving instance Countable for Holder
deriving instance Countable for Scope
deriving instance Countable for Capability
deriving instance Countable for RevocationKey
deriving instance Countable for Request
deriving instance Countable for Minidregg.Theory.CredentialAuthorityFamily.LineageOrigin
deriving instance Countable for Minidregg.Theory.CredentialAuthorityFamily.ParentLink
deriving instance Countable for StoredCapability
deriving instance Countable for AuthorityPlane

instance authorityKeyCountable (plane : AuthorityPlane) : Countable plane.Key := by
  cases plane <;> simp only [AuthorityPlane.Key] <;> infer_instance

instance authorityValueCountable (plane : AuthorityPlane) : Countable plane.Value := by
  cases plane <;> simp only [AuthorityPlane.Value] <;> infer_instance

/-! ## Countability of the Hyperdocument value tree -/

deriving instance Countable for CodecVersion
deriving instance Countable for IdDomain
deriving instance Countable for IdPreimage
deriving instance Countable for Identifier
deriving instance Countable for PrincipalRef
deriving instance Countable for AtomKind
deriving instance Countable for AtomRecord
deriving instance Countable for RunRecord
deriving instance Countable for EmbedRef
deriving instance Countable for ElementBody
deriving instance Countable for ElementRecord
deriving instance Countable for AnchorBias
deriving instance Countable for EndpointDeathPolicy
deriving instance Countable for StablePoint
deriving instance Countable for StableRange
deriving instance Countable for MergeRegime
deriving instance Countable for FieldType

instance fieldTypeValueCountable (fieldType : FieldType) :
    Countable fieldType.Value := by
  cases fieldType <;> simp only [FieldType.Value] <;> infer_instance

deriving instance Countable for FieldOwner
deriving instance Countable for FieldKey
deriving instance Countable for FieldRecord
deriving instance Countable for ConflictAlternative
deriving instance Countable for ConflictRecord
deriving instance Countable for TransclusionMode
deriving instance Countable for StoredSourceIdentity
deriving instance Countable for StoredOpeningShape
deriving instance Countable for OpeningDescriptor
deriving instance Countable for DisclosureAtom
deriving instance Countable for StoredTransclusionRef
deriving instance Countable for LinkTarget
deriving instance Countable for LinkRecord
deriving instance Countable for TransclusionRecord
deriving instance Countable for MarkRecord
deriving instance Countable for AnnotationRecord
deriving instance Countable for CausalVersionDag.SchemaRef
deriving instance Countable for VersionEventRecord
deriving instance Countable for DocumentRecord
deriving instance Countable for Hyperdocument.Namespace

instance hyperdocumentKeyCountable (space : Hyperdocument.Namespace) :
    Countable (Hyperdocument.Key space) := by
  cases space <;> simp only [Hyperdocument.Key] <;> infer_instance

instance hyperdocumentValueCountable (space : Hyperdocument.Namespace) :
    Countable (Hyperdocument.Value space) := by
  cases space <;> simp only [Hyperdocument.Value] <;> infer_instance


/-! ## One honest existence materializer -/

/-- A deterministic, non-cryptographic root used only by the non-vacuity
witnesses below.  It makes no binding or collision-resistance claim. -/
def lengthRoot (bytes : List UInt8) : Digest :=
  ⟨bytes.length⟩

noncomputable def codecOfCountable (alpha : Type)
    [Countable alpha] [Nonempty alpha] : LawfulCodec alpha :=
  Classical.choice
    MaterializerCardinality.nonempty_lawfulCodec_of_countable

/-- The existence materializer of any layout whose namespaces, keys and values
are countable.  The store type is inhabited by the empty store `0`. -/
noncomputable def materializerOfCountable (L : Layout.{0, 0, 0})
    [Countable L.Namespace] [∀ space, Countable (L.Key space)]
    [∀ space, Countable (L.Value space)] : CellState.Materializer L Digest :=
  haveI : Nonempty (Store L) := ⟨0⟩
  { codec := codecOfCountable (Store L)
    rootBytes := lengthRoot }

/-! ## The three Theory-side deployed layouts -/

noncomputable def effectMaterializer :
    CellState.Materializer EffectDeclaration.effectLayout Digest :=
  materializerOfCountable EffectDeclaration.effectLayout

noncomputable def effectCell : Materialized effectMaterializer :=
  materialize effectMaterializer 0

noncomputable def authorityMaterializer : CredentialAuthorityState.Materializer :=
  materializerOfCountable CredentialAuthorityState.layout

noncomputable def authorityCell : Materialized authorityMaterializer :=
  materialize authorityMaterializer 0

noncomputable def hyperdocumentMaterializer : Hyperdocument.Materializer Digest :=
  materializerOfCountable Hyperdocument.layout

noncomputable def hyperdocumentCell : Materialized hyperdocumentMaterializer :=
  materialize hyperdocumentMaterializer 0

/-- The canonical authority layout has an actual canonical cell. -/
theorem authority_materializer_nonempty :
    Nonempty CredentialAuthorityState.Materializer :=
  ⟨authorityMaterializer⟩

/-- The canonical Hyperdocument layout has an actual canonical cell. -/
theorem hyperdocument_materializer_nonempty :
    Nonempty (Hyperdocument.Materializer Digest) :=
  ⟨hyperdocumentMaterializer⟩

/-! ## The witnessed cells are the empty store, read exactly

The witnesses are real cells whose typed reads return the absence value (or the
reader's declared default), not an arbitrary one. -/

@[simp] theorem effectCell_absent
    (address : Address EffectDeclaration.effectLayout) :
    effectCell.logical address = none :=
  rfl

@[simp] theorem authorityCell_capability_absent
    (kind : ResourceKind) (id : CapabilityId) :
    readCapability authorityCell kind id = none :=
  rfl

@[simp] theorem authorityCell_epochs_zero
    (issuer : IssuerId) (policy : PolicyId) (subject : SubjectId) :
    issuerEpochAt authorityCell issuer = 0 ∧
      policyEpochAt authorityCell policy = 0 ∧
      subjectKeyEpochAt authorityCell subject = 0 :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem hyperdocumentCell_absent
    (address : Hyperdocument.Address) :
    hyperdocumentCell.logical address = none :=
  rfl

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.DeployedMaterializerWitness.authority_materializer_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authority_materializer_nonempty
/-- info: 'Minidregg.Theory.DeployedMaterializerWitness.hyperdocument_materializer_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hyperdocument_materializer_nonempty

end Minidregg.Theory.DeployedMaterializerWitness
