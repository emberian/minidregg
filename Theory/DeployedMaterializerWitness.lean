/-
# Theory.DeployedMaterializerWitness -- the repaired schemas are inhabited

The old total-function field carrier made several deployed schemas provably
unmaterializable.  The sparse migration is not complete merely because generic
`DFinsupp` instances exist: this file closes the three Theory-side cases with
actual lawful codecs, materializers, and materialized empty cells.

The codecs chosen from `Countable` are existence witnesses, not deployment wire
formats.  Their role is to refute carrier vacuity.  A deployed artifact must
still select and pin a concrete codec and root function.
-/
import Mathlib.Tactic.DeriveCountable
import Theory.CredentialAuthorityState
import Theory.Hyperdocument
import Theory.SparseLogicalState

namespace Minidregg.Theory.DeployedMaterializerWitness

open CellState
open IndexedProgram
open TypedAuthorization
open CredentialAuthorityState
open Hyperdocument

set_option autoImplicit false

/-! ## Countability of the authority value tree -/

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
deriving instance Countable for AuthorityField
deriving instance Countable for StoredCapability

instance authorityValueCountable (field : AuthorityField) :
    Countable (AuthorityField.Value field) := by
  cases field <;> simp only [AuthorityField.Value] <;> infer_instance

instance : Countable CredentialAuthorityState.schema.Field :=
  inferInstanceAs (Countable AuthorityField)

instance (field : CredentialAuthorityState.schema.Field) :
    Countable (CredentialAuthorityState.schema.FieldType field) :=
  authorityValueCountable field

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

deriving instance Countable for Hyperdocument.Address

instance : Countable Hyperdocument.cellSchema.Field :=
  inferInstanceAs (Countable Hyperdocument.Address)

instance (field : Hyperdocument.cellSchema.Field) :
    Countable (Hyperdocument.cellSchema.FieldType field) :=
  hyperdocumentValueCountable field.1

/-! ## One honest existence materializer -/

/-- A deterministic, non-cryptographic root used only by the non-vacuity
witnesses below.  It makes no binding or collision-resistance claim. -/
def lengthRoot (bytes : List UInt8) : Digest :=
  ⟨bytes.length⟩

noncomputable def codecOfCountable (alpha : Type)
    [Countable alpha] [Nonempty alpha] : LawfulCodec alpha :=
  Classical.choice
    MaterializerCardinality.nonempty_lawfulCodec_of_countable

noncomputable def logicalCodecOfCountable (S : Schema.{0, 0, 0, 0})
    [Countable S.Field] [∀ field, Countable (S.FieldType field)]
    (resourceEmpty : S.Resource → Empty) : LawfulCodec (LogicalState S) := by
  let fieldCodec := codecOfCountable (FieldStore S)
  exact
    { encode := fun state => fieldCodec.encode state.fields
      decode := fun bytes => (fieldCodec.decode bytes).map fun fields =>
        { fields := fields
          resources := fun resource => nomatch resourceEmpty resource }
      decode_encode := by
        intro state
        rw [fieldCodec.decode_encode]
        apply congrArg some
        cases state with
        | mk fields resources =>
            have resourcesExact :
                (fun resource => nomatch resourceEmpty resource) = resources := by
              funext resource
              exact Empty.elim (resourceEmpty resource)
            cases resourcesExact
            rfl }

noncomputable def materializerOfCountable (S : Schema.{0, 0, 0, 0})
    [Countable S.Field] [∀ field, Countable (S.FieldType field)]
    (resourceEmpty : S.Resource → Empty) : Materializer S Digest where
  codec := logicalCodecOfCountable S resourceEmpty
  rootBytes := lengthRoot

def emptyLogical (S : Schema.{0, 0, 0, 0})
    (resourceEmpty : S.Resource → Empty) : LogicalState S where
  fields := 0
  resources := fun resource => nomatch resourceEmpty resource

/-! ## The three Theory-side deployed schemas -/

noncomputable def effectMaterializer :
    Materializer DeclaredTurn.effectSchema.{0, 0} Digest :=
  materializerOfCountable DeclaredTurn.effectSchema Empty.elim

noncomputable def effectCell : Materialized effectMaterializer :=
  materialize effectMaterializer
    (emptyLogical DeclaredTurn.effectSchema Empty.elim)

noncomputable def authorityMaterializer :
    Materializer CredentialAuthorityState.schema.{0, 0} Digest :=
  materializerOfCountable CredentialAuthorityState.schema Empty.elim

noncomputable def authorityCell : Materialized authorityMaterializer :=
  materialize authorityMaterializer
    (emptyLogical CredentialAuthorityState.schema Empty.elim)

noncomputable def hyperdocumentMaterializer :
    Materializer Hyperdocument.cellSchema.{0, 0} Digest :=
  materializerOfCountable Hyperdocument.cellSchema Empty.elim

noncomputable def hyperdocumentCell : Materialized hyperdocumentMaterializer :=
  materialize hyperdocumentMaterializer
    (emptyLogical Hyperdocument.cellSchema Empty.elim)

/-- The kernel's declared-effect schema has an actual canonical cell. -/
theorem effect_materializer_nonempty :
    Nonempty (Materializer DeclaredTurn.effectSchema.{0, 0} Digest) :=
  ⟨effectMaterializer⟩

/-- The canonical authority schema has an actual canonical cell. -/
theorem authority_materializer_nonempty :
    Nonempty
      (Materializer CredentialAuthorityState.schema.{0, 0} Digest) :=
  ⟨authorityMaterializer⟩

/-- The canonical Hyperdocument schema has an actual canonical cell. -/
theorem hyperdocument_materializer_nonempty :
    Nonempty (Materializer Hyperdocument.cellSchema.{0, 0} Digest) :=
  ⟨hyperdocumentMaterializer⟩

@[simp] theorem authorityCell_capability_absent
    (kind : ResourceKind) (id : CapabilityId) :
    readCapability authorityCell kind id = none :=
  rfl

@[simp] theorem authorityCell_epochs_zero
    (issuer : IssuerId) (policy : PolicyId) (subject : SubjectId) :
    issuerEpochAt authorityCell issuer = 0 ∧
      policyEpochAt authorityCell policy = 0 ∧
      subjectKeyEpochAt authorityCell subject = 0 :=
  by exact ⟨rfl, rfl, rfl⟩

@[simp] theorem hyperdocumentCell_absent
    (address : Hyperdocument.Address) :
    hyperdocumentCell.logical.fields address = none :=
  rfl

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.DeployedMaterializerWitness.effect_materializer_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms effect_materializer_nonempty
/-- info: 'Minidregg.Theory.DeployedMaterializerWitness.authority_materializer_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authority_materializer_nonempty
/-- info: 'Minidregg.Theory.DeployedMaterializerWitness.hyperdocument_materializer_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hyperdocument_materializer_nonempty

end Minidregg.Theory.DeployedMaterializerWitness
