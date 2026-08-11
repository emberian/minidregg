/-
# Theory.HyperdocumentCausalFamily -- accepted content is causal semantics

`CausalVersionDag.SemanticFamily` and `Anchor` were widely consumed but no
module constructed either one.  Hyperdocument publication already carried the
right data: one `HyperdocumentOperations.Accepted` fixes the exact pre-cell,
the sole verifier-minted post-cell, and the complete causal event preimage.
This module makes that relationship the actual semantic family.

The family is intentionally ordinary/genesis-or-linear.  Its parent law admits
an empty genesis or one parent whose post-root is the child's pre-root.  The
offline multi-parent merge path has additional ancestry/conflict evidence and
must enter through its own family rather than weakening this law.

The final section constructs a real accepted create operation, addressed
genesis event, anchor, valid append, and one-entry history over the deployed
Hyperdocument and authority schemas.  It uses the existing countability codecs,
byte-length root, and permissive witness portal, so it proves inhabitation and
semantic wiring -- not deployment encoding, cryptographic binding, or policy
security.
-/
import Mathlib.Tactic.DeriveCountable
import Theory.DeployedMaterializerWitness
import Theory.HyperdocumentOperations
import Theory.TypedAuthorizationWitness

namespace Minidregg.Theory.HyperdocumentCausalFamily

open CellState
open CredentialAuthorityState
open Hyperdocument
open HyperdocumentOperationIntent
open HyperdocumentOperations
open IndexedProgram
open TypedAuthorization

set_option autoImplicit false

universe u

noncomputable section

/-! ## The actual ordinary Hyperdocument semantic family -/

/-- One causal event backed by the exact accepted content effect from which its
preimage is derived. -/
structure EventEvidence
    (MDoc : Hyperdocument.Materializer Digest)
    {MAuth : CredentialAuthorityState.Materializer}
    (config : HyperdocumentOperations.Config)
    (projection : ProjectionUniverse)
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (portal : Portal)
    (event : CausalVersionDag.EventPreimage) : Type where
  documentPre : Hyperdocument.Cell MDoc
  declaration : HyperdocumentOperations.Declaration
  accepted : HyperdocumentOperations.Accepted config projection authorityPre
    documentPre portal declaration
  eventExact : accepted.causalPreimage = event

namespace EventEvidence

def post
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : HyperdocumentOperations.Config}
    {projection : ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {portal : Portal}
    {event : CausalVersionDag.EventPreimage}
    (evidence : EventEvidence MDoc config projection authorityPre portal event) :
    Hyperdocument.Cell MDoc :=
  evidence.accepted.accepted.prepared.post

@[simp] theorem pre_root
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : HyperdocumentOperations.Config}
    {projection : ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {portal : Portal}
    {event : CausalVersionDag.EventPreimage}
    (evidence : EventEvidence MDoc config projection authorityPre portal event) :
    evidence.documentPre.root = event.preStateRoot := by
  exact evidence.accepted.causalPreimage_pre_root.trans
    (congrArg CausalVersionDag.EventPreimage.preStateRoot evidence.eventExact)

@[simp] theorem post_root
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : HyperdocumentOperations.Config}
    {projection : ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {portal : Portal}
    {event : CausalVersionDag.EventPreimage}
    (evidence : EventEvidence MDoc config projection authorityPre portal event) :
    evidence.post.root = event.postStateRoot := by
  exact evidence.accepted.causalPreimage_post_root.trans
    (congrArg CausalVersionDag.EventPreimage.postStateRoot evidence.eventExact)

end EventEvidence

/-- Ordinary content history is either genesis or a single-parent transition
whose canonical parent post-root is the child's pre-root. -/
inductive ParentCompatible :
    List CausalVersionDag.EventPreimage → CausalVersionDag.EventPreimage → Type
  | genesis (child : CausalVersionDag.EventPreimage)
      (serializedEmpty : child.parentFrontier = []) :
      ParentCompatible [] child
  | linear (parent child : CausalVersionDag.EventPreimage)
      (rootExact : parent.postStateRoot = child.preStateRoot) :
      ParentCompatible [parent] child

/-- Relational execution retains the exact accepted token and identifies both
states with its canonical input and output cells. -/
def Step
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    (config : HyperdocumentOperations.Config)
    (projection : ProjectionUniverse)
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (portal : Portal)
    (event : CausalVersionDag.EventPreimage)
    (before after : Hyperdocument.Cell MDoc) : Prop :=
  ∃ evidence : EventEvidence MDoc config projection authorityPre portal event,
    before = evidence.documentPre ∧ after = evidence.post

/-- The concrete causal family for ordinary accepted Hyperdocument effects. -/
def family
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    (config : HyperdocumentOperations.Config)
    (projection : ProjectionUniverse)
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (portal : Portal) :
    CausalVersionDag.SemanticFamily (Hyperdocument.Cell MDoc) where
  Evidence := EventEvidence MDoc config projection authorityPre portal
  ParentCompatible := ParentCompatible
  root := fun cell => cell.root
  Step := Step config projection authorityPre portal
  stepPreRoot := by
    intro event before after _ step
    rcases step with ⟨evidence, rfl, _⟩
    exact evidence.pre_root
  stepPostRoot := by
    intro event before after _ step
    rcases step with ⟨evidence, _, rfl⟩
    exact evidence.post_root

/-- The anchor is derived from the exact accepted event rather than supplied as
an unrelated pair of digests. -/
def anchorOf
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : HyperdocumentOperations.Config}
    {projection : ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {portal : Portal} {documentPre : Hyperdocument.Cell MDoc}
    {declaration : HyperdocumentOperations.Declaration}
    (accepted : HyperdocumentOperations.Accepted config projection authorityPre
      documentPre portal declaration) : CausalVersionDag.Anchor where
  historyDomain := accepted.causalPreimage.historyDomain
  streamId := accepted.causalPreimage.streamId

@[simp] theorem anchorOf_contains
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {config : HyperdocumentOperations.Config}
    {projection : ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {portal : Portal} {documentPre : Hyperdocument.Cell MDoc}
    {declaration : HyperdocumentOperations.Declaration}
    (accepted : HyperdocumentOperations.Accepted config projection authorityPre
      documentPre portal declaration) :
    (anchorOf accepted).Contains accepted.causalPreimage :=
  ⟨rfl, rfl⟩

/-! ## A concrete deployed-schema genesis -/

namespace Witness

open DeployedMaterializerWitness
open TypedAuthorizationWitness

deriving instance Countable for OperationIntent
deriving instance Countable for HyperdocumentOperations.CreatePayload
deriving instance Countable for HyperdocumentOperations.EditAtomPayload
deriving instance Countable for HyperdocumentOperations.LinkPayload
deriving instance Countable for HyperdocumentOperations.TranscludePayload
deriving instance Countable for HyperdocumentOperations.MarkPayload
deriving instance Countable for HyperdocumentOperations.AnnotatePayload
deriving instance Countable for HyperdocumentOperations.Action
deriving instance Countable for HyperdocumentOperations.RequestEnvelope
deriving instance Countable for HyperdocumentOperations.Declaration
deriving instance Countable for CausalVersionDag.EventPreimage
deriving instance Countable for Request

instance : Nonempty Digest := ⟨⟨0⟩⟩
instance {version domain} : Nonempty (Identifier version domain) := ⟨⟨⟨0⟩⟩⟩
instance : Nonempty PrincipalRef := ⟨⟨⟨0⟩, .object, ⟨0⟩⟩⟩
instance : Nonempty CausalVersionDag.SchemaRef := ⟨⟨⟨0⟩, 0⟩⟩
instance : Nonempty HyperdocumentOperations.CreatePayload :=
  ⟨⟨⟨⟨0⟩⟩, ⟨⟨0⟩⟩, ⟨0⟩, .container []⟩⟩
instance : Nonempty HyperdocumentOperations.Action :=
  ⟨.create (Classical.choice inferInstance)⟩
instance : Nonempty OperationIntent :=
  ⟨{ historyDomain := ⟨0⟩
     document := ⟨⟨0⟩⟩
     schema := ⟨⟨0⟩, 0⟩
     semanticVersion := 0
     parents := []
     author := ⟨⟨0⟩, .object, ⟨0⟩⟩
     expectedContentRoot := ⟨0⟩
     nonce := 0
     actionBytes := [] }⟩
instance : Nonempty HyperdocumentOperations.RequestEnvelope :=
  ⟨⟨⟨0⟩, 0, 0, ⟨0⟩, 0, 0⟩⟩
instance : Nonempty HyperdocumentOperations.Declaration :=
  ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance,
    Classical.choice inferInstance⟩⟩
instance : Nonempty CausalVersionDag.EventPreimage :=
  ⟨{ historyDomain := ⟨0⟩
     streamId := ⟨0⟩
     schema := ⟨⟨0⟩, 0⟩
     semanticVersion := 0
     semanticObjectRoot := ⟨0⟩
     preStateRoot := ⟨0⟩
     postStateRoot := ⟨0⟩
     parentFrontier := []
     authorId := ⟨0⟩
     principalId := ⟨0⟩
     requestId := ⟨0⟩
     effectId := ⟨0⟩ }⟩
instance : Nonempty (Request .object) :=
  ⟨{ domain := ⟨0⟩
     semantics := ⟨0⟩
     federation := ⟨0⟩
     subject := ⟨0⟩
     subjectKeyEpoch := 0
     target := ⟨0⟩
     verb := .observeObject
     argsDigest := ⟨0⟩
     effectsDigest := ⟨0⟩
     nonce := 0
     height := 0
     preStateRoot := ⟨0⟩
     policyId := ⟨0⟩
     policyEpoch := 0
     cost := 0 }⟩

def derivation : DigestDerivation where
  digestBytes := lengthRoot

noncomputable def actionCodec : LawfulCodec HyperdocumentOperations.Action :=
  codecOfCountable HyperdocumentOperations.Action

noncomputable def declarationCodec :
    LawfulCodec HyperdocumentOperations.Declaration :=
  codecOfCountable HyperdocumentOperations.Declaration

noncomputable def requestCodec : LawfulCodec (Request .object) :=
  codecOfCountable (Request .object)

noncomputable def intentCodec : LawfulCodec OperationIntent :=
  codecOfCountable OperationIntent

noncomputable def eventCodec : LawfulCodec CausalVersionDag.EventPreimage :=
  codecOfCountable CausalVersionDag.EventPreimage

noncomputable def config : HyperdocumentOperations.Config where
  actionCodec := actionCodec
  declarationCodec := declarationCodec
  requestCodec := requestCodec
  intentAddressing := { codec := intentCodec, derivation := derivation }
  effectDerivation := derivation
  requestDerivation := derivation
  requestDomain := ⟨700⟩
  semanticRelation := ⟨701⟩

def documentId : DocumentId := ⟨⟨10⟩⟩
def elementId : ElementId := ⟨⟨11⟩⟩
def author : PrincipalRef := ⟨⟨12⟩, .object, ⟨13⟩⟩

def action : HyperdocumentOperations.Action :=
  .create
    { documentId := documentId
      rootElementId := elementId
      schema := ⟨14⟩
      rootBody := .container [] }

def intent : OperationIntent where
  historyDomain := ⟨15⟩
  document := documentId
  schema := { schemaId := ⟨14⟩, version := 1 }
  semanticVersion := 0
  parents := []
  author := author
  expectedContentRoot := hyperdocumentCell.root
  nonce := 16
  actionBytes := actionCodec.encode action

def requestEnvelope : HyperdocumentOperations.RequestEnvelope where
  federation := ⟨17⟩
  subjectKeyEpoch := 0
  height := 20
  policyId := ⟨21⟩
  policyEpoch := 0
  cost := 1

def declaration : HyperdocumentOperations.Declaration where
  intent := intent
  request := requestEnvelope
  action := action

def capability : Capability .object where
  id := author.capabilityId
  root := author.capabilityId
  parent := none
  issuer := ⟨22⟩
  holder := .subject author.subject
  scope :=
    { targets := {(declaration.toRequest config).target}
      verbs := {.mutateObject}
      maxCost := 1 }
  notBefore := 0
  notAfter := 100
  issuerEpoch := 0
  policyId := requestEnvelope.policyId
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def storedCapability : StoredCapability .object := ⟨capability, []⟩

def projection : ProjectionUniverse where
  revocationKeys := {.capability capability.id}

noncomputable def authorityLogical :
    CellState.LogicalState CredentialAuthorityState.schema :=
  { fields :=
      (0 : CellState.FieldStore CredentialAuthorityState.schema).write
        (.capability .object capability.id) storedCapability
    resources := fun resource => nomatch resource }

noncomputable def authorityPre :
    CredentialAuthorityState.Cell authorityMaterializer :=
  CellState.materialize authorityMaterializer authorityLogical

theorem capability_opened :
    readCapability authorityPre .object capability.id = some storedCapability := by
  change authorityLogical.fields (.capability .object capability.id) =
    some storedCapability
  exact FieldStore.write_self _ _ _

def principal : AuthenticatedPrincipal projection authorityPre
    requestEnvelope.height author where
  stored := storedCapability
  opened := capability_opened
  idBound := rfl
  holderBound := rfl
  lineage := .root capability rfl rfl rfl
  validFrom := by decide
  validUntil := by decide
  issuerCurrent := rfl
  policyCurrent := rfl
  selfNotRevoked := by
    rw [CredentialAuthorityState.mem_authState_revoked_iff]
    intro member
    have notRevoked : CredentialAuthorityState.isRevoked authorityPre
        (.capability storedCapability.head.id) = false := by
      change
        (((0 : CellState.FieldStore CredentialAuthorityState.schema).write
          (.capability .object capability.id) storedCapability)
          (.revoked (.capability storedCapability.head.id))).getD false = false
      rw [FieldStore.write_other (different := by simp)]
      rfl
    exact Bool.false_ne_true (notRevoked.symm.trans member.2)
  ancestorsNotRevoked := by
    intro ancestor member
    simp [storedCapability, capability] at member
  channelsNotRevoked := by
    intro channel member
    simp [storedCapability, capability] at member

theorem namedCapabilityAdmissible :
    capability.Admissible
      (CredentialAuthorityState.authState projection authorityPre)
      (declaration.toRequest config) where
  holder := rfl
  scope :=
    { target := by simp [capability]
      verb := by simp [capability, declaration,
        HyperdocumentOperations.Declaration.toRequest]
      cost := by simp [capability, declaration, requestEnvelope,
        HyperdocumentOperations.Declaration.toRequest] }
  validFrom := by decide
  validUntil := by decide
  policyId := rfl
  policyEpoch := rfl
  policyCurrent := rfl
  issuerCurrent := rfl
  selfNotRevoked := principal.selfNotRevoked
  ancestorNotRevoked := principal.ancestorsNotRevoked
  channelNotRevoked := principal.channelsNotRevoked

def authorization : Authorized permissivePortal
    (CredentialAuthorityState.authState projection authorityPre)
    (declaration.toRequest config) where
  evidence := .proof () rfl
  policyWitness := ()
  policyEpochExact := rfl
  policyVerified := rfl

def semantic : HyperdocumentOperations.ValidOperation config
    hyperdocumentCell declaration where
  canonical :=
    { actionBytesExact := rfl
      documentExact := rfl
      objectCapability := rfl }
  preRootExact := rfl
  writesUnique := by
    simp [declaration, action,
      HyperdocumentOperations.Declaration.packedWrites,
      HyperdocumentOperations.Action.packedWrites,
      HyperdocumentOperations.createWrites,
      HyperdocumentOperations.PackedWrite.address]
  expectedExact := by
    intro write member
    simp [declaration, action,
      HyperdocumentOperations.Declaration.packedWrites,
      HyperdocumentOperations.Action.packedWrites,
      HyperdocumentOperations.createWrites] at member
    rcases member with rfl | rfl <;>
      rfl
  rangesValid := trivial

theorem validated_nonempty :
    Nonempty (CellState.ValidatedPatch hyperdocumentMaterializer
      hyperdocumentCell (declaration.patch config)) := by
  generalize exactOutcome : CellState.validate hyperdocumentMaterializer
    hyperdocumentCell (declaration.patch config) = outcome
  cases outcome with
  | accepted validated => exact ⟨validated⟩
  | rejected reason =>
      have rootExact : (declaration.patch config).expectedPreRoot =
          hyperdocumentCell.root := semantic.preRootExact
      have fieldsExact : (declaration.patch config).fieldFootprint =
          (declaration.patch config).namedFields :=
        (HyperdocumentOperations.Declaration.patch_namedFields
          config declaration).symm
      have resourcesExact : (declaration.patch config).resourceFootprint =
          (declaration.patch config).namedResources :=
        (HyperdocumentOperations.Declaration.patch_namedResources
          config declaration).symm
      unfold CellState.validate at exactOutcome
      rw [dif_pos rootExact, dif_pos fieldsExact, dif_pos resourcesExact]
        at exactOutcome
      cases exactOutcome

noncomputable def accepted : HyperdocumentOperations.Accepted config projection
    authorityPre hyperdocumentCell permissivePortal declaration :=
  HyperdocumentOperations.accept principal semantic namedCapabilityAdmissible
    authorization (Classical.choice validated_nonempty)

noncomputable def eventEvidence : EventEvidence hyperdocumentMaterializer config projection authorityPre permissivePortal
    accepted.causalPreimage where
  documentPre := hyperdocumentCell
  declaration := declaration
  accepted := accepted
  eventExact := rfl

noncomputable def semanticFamily :
    CausalVersionDag.SemanticFamily
      (Hyperdocument.Cell hyperdocumentMaterializer) :=
  family config projection authorityPre permissivePortal

noncomputable def addressing : CausalVersionDag.ContentAddressing :=
  causalVersionAddressing eventCodec derivation

theorem eventWellFormed : accepted.versionEventRecord.CausallyWellFormed := by
  constructor <;> simp [accepted, declaration, intent,
    HyperdocumentOperations.Accepted.versionEventRecord,
    VersionEventRecord.toCausalPreimage]

noncomputable def storedEvent : StoredVersionEvent addressing :=
  StoredVersionEvent.derive eventCodec derivation accepted.versionEventRecord
    eventWellFormed

noncomputable def verifiedEvent :
    CausalVersionDag.VerifiedEvent addressing semanticFamily :=
  storedEvent.toVerifiedEvent eventEvidence

noncomputable def anchor : CausalVersionDag.Anchor := anchorOf accepted

noncomputable def genesisValid :
    CausalVersionDag.ValidAppend anchor [] verifiedEvent where
  anchorExact := anchorOf_contains accepted
  genesisShape := Or.inl ⟨rfl, rfl, rfl⟩
  resolvedParents := []
  resolvedParentsExact := rfl
  resolvedParentsPresent := by simp
  parentAnchorExact := by simp
  parentSchemaExact := by simp
  schemaVersionMonotone := by simp
  semanticVersionIncreases := by simp
  entryFresh := by simp
  requestFresh := by simp
  effectFresh := by simp
  parentCompatibility := ParentCompatible.genesis accepted.causalPreimage rfl

noncomputable def history :
    CausalVersionDag.History (scheme := addressing)
  (family := semanticFamily) anchor :=
  (CausalVersionDag.History.empty anchor).append verifiedEvent genesisValid

@[simp] theorem history_has_one_event : history.events = [verifiedEvent] :=
  rfl

@[simp] theorem accepted_post_contains_document :
    Hyperdocument.lookup accepted.accepted.prepared.post.logical .documents
      documentId =
      some
        { rootElement := elementId
          schema := ⟨14⟩
          createdBy := author
          createdAt := declaration.operationId config } := by
  exact accepted.post_contains_fieldWrite
    (HyperdocumentOperations.PackedWrite.toFieldWrite
      ⟨.documents,
        { key := documentId
          expected := none
          replacement :=
            { rootElement := elementId
              schema := ⟨14⟩
              createdBy := author
              createdAt := declaration.operationId config } }⟩)
    (by simp [declaration, action,
      HyperdocumentOperations.Declaration.fieldWrites,
      HyperdocumentOperations.Declaration.packedWrites,
      HyperdocumentOperations.Action.packedWrites,
      HyperdocumentOperations.createWrites, intent, author])

/-- A cell with a different canonical root cannot be substituted into this
causal step.  Root collision resistance is deliberately not assumed, so exact
cell inequality alone would be too strong. -/
theorem no_step_from_wrong_pre_root
    (other : Hyperdocument.Cell hyperdocumentMaterializer)
    (wrong : other.root ≠ hyperdocumentCell.root) :
    ¬Step config projection authorityPre permissivePortal
      accepted.causalPreimage other accepted.accepted.prepared.post := by
  intro step
  rcases step with ⟨evidence, rfl, afterExact⟩
  exact wrong (evidence.pre_root.trans accepted.causalPreimage_pre_root.symm)

end Witness

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.HyperdocumentCausalFamily.EventEvidence.pre_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms EventEvidence.pre_root
/-- info: 'Minidregg.Theory.HyperdocumentCausalFamily.Witness.history_has_one_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.history_has_one_event
/-- info: 'Minidregg.Theory.HyperdocumentCausalFamily.Witness.accepted_post_contains_document' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.accepted_post_contains_document
/-- info: 'Minidregg.Theory.HyperdocumentCausalFamily.Witness.no_step_from_wrong_pre_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.no_step_from_wrong_pre_root

end

end Minidregg.Theory.HyperdocumentCausalFamily
