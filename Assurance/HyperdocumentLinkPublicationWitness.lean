/-
# Assurance.HyperdocumentLinkPublicationWitness -- a built linear link turn

This module constructs one concrete deployed-schema path from an accepted
genesis create to an accepted `.link` child.  The child is appended to the
ordinary `HyperdocumentCausalFamily`, its derived event is allocated after the
genesis event in the sparse event-log store, and content plus event-log posts
are retained by one logical `HyperdocumentPublication` commit.

The selected codecs are countability witnesses.  The digest functions below
are deliberately transparent semantic identifiers chosen to make freshness
computable in this witness; they are not collision-resistant hashes.  The
publication handler remains an abstract boundary, so this proves logical
atomicity and exact post containment, not durable installation or UI delivery.
-/
import Kernel.DeployedMaterializerWitness
import Kernel.HyperdocumentPublication
import Theory.HyperdocumentCausalFamily

namespace Minidregg.Assurance.HyperdocumentLinkPublicationWitness

open Minidregg.Kernel
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperationIntent
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

namespace Genesis

abbrev documentMaterializer :=
  Minidregg.Theory.DeployedMaterializerWitness.hyperdocumentMaterializer
abbrev authorityMaterializer :=
  Minidregg.Theory.DeployedMaterializerWitness.authorityMaterializer
abbrev documentPre :=
  Minidregg.Theory.DeployedMaterializerWitness.hyperdocumentCell
abbrev authorityPre :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.authorityPre
abbrev projection :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.projection
abbrev principal :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.principal
abbrev capability :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.capability
abbrev author :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.author
abbrev documentId :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.documentId
abbrev elementId :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.elementId
abbrev requestEnvelope :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.requestEnvelope
abbrev permissivePortal :=
  Minidregg.Theory.TypedAuthorizationWitness.permissivePortal

end Genesis

/-! ## Transparent witness addressing -/

abbrev actionCodec :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.actionCodec
abbrev declarationCodec :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.declarationCodec
abbrev requestCodec :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.requestCodec
abbrev intentCodec :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.intentCodec
abbrev eventCodec :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.eventCodec
abbrev intentDerivation :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.derivation

/-- Content-effect ids expose the declaration nonce in a disjoint witness
range.  This is a semantic test identifier, not a hash. -/
noncomputable def contentEffectDigest (bytes : List UInt8) : Digest :=
  match declarationCodec.decode bytes with
  | some declaration => ⟨1000 + declaration.intent.nonce⟩
  | none => ⟨0⟩

def contentEffectDerivation : DigestDerivation where
  digestBytes := contentEffectDigest

/-- Request ids likewise expose the exact request nonce. -/
noncomputable def requestDigest (bytes : List UInt8) : Digest :=
  match requestCodec.decode bytes with
  | some request => ⟨2000 + request.nonce⟩
  | none => ⟨0⟩

def requestDerivation : DigestDerivation where
  digestBytes := requestDigest

/-- Event addresses decode the domain-separated causal preimage and retain its
already-derived effect id. -/
noncomputable def eventDigest (bytes : List UInt8) : Digest :=
  match decodePreimage .v1 .versionEvent bytes with
  | some envelope =>
      match eventCodec.decode envelope.payload with
      | some event => event.effectId
      | none => ⟨0⟩
  | none => ⟨0⟩

def eventDerivation : DigestDerivation where
  digestBytes := eventDigest

def addressing : CausalVersionDag.ContentAddressing :=
  causalVersionAddressing eventCodec eventDerivation

@[simp] theorem address_exact (event : CausalVersionDag.EventPreimage) :
    addressing.address event = event.effectId := by
  simp [addressing, causalVersionAddressing, eventDerivation, eventDigest,
    CausalVersionDag.ContentAddressing.address]
  rw [eventCodec.decode_encode]

noncomputable def config : HyperdocumentOperations.Config where
  actionCodec := actionCodec
  declarationCodec := declarationCodec
  requestCodec := requestCodec
  intentAddressing := { codec := intentCodec, derivation := intentDerivation }
  effectDerivation := contentEffectDerivation
  requestDerivation := requestDerivation
  requestDomain := ⟨700⟩
  semanticRelation := ⟨701⟩

@[simp] theorem effectDigest_exact
    (declaration : HyperdocumentOperations.Declaration) :
    declaration.effectDigest config = ⟨1000 + declaration.intent.nonce⟩ := by
  change contentEffectDigest (declarationCodec.encode declaration) = _
  unfold contentEffectDigest
  rw [declarationCodec.decode_encode]

@[simp] theorem requestId_exact
    (declaration : HyperdocumentOperations.Declaration) :
    declaration.requestId config = ⟨2000 + declaration.intent.nonce⟩ := by
  change requestDigest
    (requestCodec.encode (declaration.toRequest config)) = _
  unfold requestDigest
  rw [requestCodec.decode_encode]
  rfl

/-! ## Accepted genesis create -/

def genesisAction : HyperdocumentOperations.Action :=
  .create
    { documentId := Genesis.documentId
      rootElementId := Genesis.elementId
      schema := ⟨14⟩
      rootBody := .container [] }

def genesisIntent : OperationIntent where
  historyDomain := ⟨15⟩
  document := Genesis.documentId
  schema := { schemaId := ⟨14⟩, version := 1 }
  semanticVersion := 0
  parents := []
  author := Genesis.author
  expectedContentRoot := Genesis.documentPre.root
  nonce := 16
  actionBytes := actionCodec.encode genesisAction

def genesisDeclaration : HyperdocumentOperations.Declaration where
  intent := genesisIntent
  request := Genesis.requestEnvelope
  action := genesisAction

def genesisCapabilityAdmissible :
    Genesis.capability.Admissible
      (CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre)
      (genesisDeclaration.toRequest config) where
  holder := rfl
  scope :=
    { target := by
        simpa [genesisDeclaration, genesisIntent, config,
          HyperdocumentOperations.Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.target
      verb := by
        simpa [genesisDeclaration, genesisIntent, config,
          HyperdocumentOperations.Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.verb
      cost := by
        simpa [genesisDeclaration, genesisIntent, config,
          HyperdocumentOperations.Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.cost }
  validFrom := by decide
  validUntil := by decide
  policyId := rfl
  policyEpoch := rfl
  policyCurrent := rfl
  issuerCurrent := rfl
  selfNotRevoked := Genesis.principal.selfNotRevoked
  ancestorNotRevoked := Genesis.principal.ancestorsNotRevoked
  channelNotRevoked := Genesis.principal.channelsNotRevoked

def genesisAuthorization : Authorized Genesis.permissivePortal
    (CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre)
    (genesisDeclaration.toRequest config) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def genesisSemantic : HyperdocumentOperations.ValidOperation config
    Genesis.documentPre genesisDeclaration where
  canonical :=
    { actionBytesExact := rfl
      documentExact := rfl
      objectCapability := rfl }
  preRootExact := rfl
  writesUnique := by
    simp [genesisDeclaration, genesisAction,
      HyperdocumentOperations.Declaration.packedWrites,
      HyperdocumentOperations.Action.packedWrites,
      HyperdocumentOperations.createWrites,
      HyperdocumentOperations.PackedWrite.address]
  expectedExact := by
    intro write member
    simp [genesisDeclaration, genesisAction,
      HyperdocumentOperations.Declaration.packedWrites,
      HyperdocumentOperations.Action.packedWrites,
      HyperdocumentOperations.createWrites] at member
    rcases member with rfl | rfl <;> rfl
  rangesValid := trivial

theorem validatedNonempty
    {pre : Hyperdocument.Cell Genesis.documentMaterializer}
    {declaration : HyperdocumentOperations.Declaration}
    (semantic : HyperdocumentOperations.ValidOperation config pre declaration) :
    Nonempty (ValidatedPatch Genesis.documentMaterializer pre
      (declaration.patch config)) := by
  generalize exactOutcome : validate Genesis.documentMaterializer pre
    (declaration.patch config) = outcome
  cases outcome with
  | accepted validated => exact ⟨validated⟩
  | rejected reason =>
      have rootExact : (declaration.patch config).expectedPreRoot = pre.root :=
        semantic.preRootExact
      unfold validate at exactOutcome
      rw [dif_pos rootExact,
        dif_pos (HyperdocumentOperations.Declaration.patch_namedFields _ _).symm,
        dif_pos (HyperdocumentOperations.Declaration.patch_namedResources _ _).symm]
        at exactOutcome
      cases exactOutcome

noncomputable def genesisAccepted : HyperdocumentOperations.Accepted config
    Genesis.projection Genesis.authorityPre Genesis.documentPre
    Genesis.permissivePortal genesisDeclaration :=
  HyperdocumentOperations.accept Genesis.principal genesisSemantic
    genesisCapabilityAdmissible genesisAuthorization
    (Classical.choice (validatedNonempty genesisSemantic))

abbrev genesisPost := genesisAccepted.accepted.prepared.post

@[simp] theorem genesis_link_absent (id : LinkId) :
    lookup genesisPost.logical .links id = none := by
  have framed := genesisAccepted.accepted.field_frame
    (⟨.links, id⟩ : Hyperdocument.Address) (by
      simp [genesisDeclaration, genesisAction,
        HyperdocumentOperations.family,
        HyperdocumentOperations.Declaration.patch,
        HyperdocumentOperations.Declaration.fieldWrites,
        HyperdocumentOperations.Declaration.packedWrites,
        HyperdocumentOperations.Action.packedWrites,
        HyperdocumentOperations.createWrites,
        HyperdocumentOperations.PackedWrite.toFieldWrite,
        HyperdocumentOperations.PackedWrite.address]
      constructor <;> intro equal <;> cases equal)
  simpa [Hyperdocument.lookup] using framed

/-! ## Accepted `.link` child -/

def linkId : LinkId := ⟨⟨25⟩⟩

def linkPayload : HyperdocumentOperations.LinkPayload where
  id := linkId
  sourceDocument := Genesis.documentId
  source := none
  target := .external [0x68, 0x74, 0x74, 0x70, 0x73] [0x65, 0x78]
    [0x2f, 0x6c, 0x6f, 0x6f, 0x6d]
  relation := ⟨24⟩

def linkAction : HyperdocumentOperations.Action := .link linkPayload

/-! The parent key is defined below from the accepted genesis event. -/

def semanticFamily : CausalVersionDag.SemanticFamily
    (Hyperdocument.Cell Genesis.documentMaterializer) :=
  HyperdocumentCausalFamily.family config Genesis.projection
    Genesis.authorityPre Genesis.permissivePortal

noncomputable def genesisEvidence :
    HyperdocumentCausalFamily.EventEvidence Genesis.documentMaterializer config
      Genesis.projection Genesis.authorityPre Genesis.permissivePortal
      genesisAccepted.causalPreimage where
  documentPre := Genesis.documentPre
  declaration := genesisDeclaration
  accepted := genesisAccepted
  eventExact := rfl

theorem genesisWellFormed : genesisAccepted.versionEventRecord.CausallyWellFormed := by
  constructor <;> simp [genesisAccepted, genesisDeclaration, genesisIntent,
    HyperdocumentOperations.Accepted.versionEventRecord,
    VersionEventRecord.toCausalPreimage]

noncomputable def genesisStored : StoredVersionEvent addressing :=
  StoredVersionEvent.derive eventCodec eventDerivation
    genesisAccepted.versionEventRecord genesisWellFormed

noncomputable def genesisNode :
    CausalVersionDag.VerifiedEvent addressing semanticFamily :=
  genesisStored.toVerifiedEvent genesisEvidence

def linkIntent : OperationIntent where
  historyDomain := genesisIntent.historyDomain
  document := Genesis.documentId
  schema := genesisIntent.schema
  semanticVersion := 1
  parents := [genesisStored.key]
  author := Genesis.author
  expectedContentRoot := genesisPost.root
  nonce := 26
  actionBytes := actionCodec.encode linkAction

def linkDeclaration : HyperdocumentOperations.Declaration where
  intent := linkIntent
  request := Genesis.requestEnvelope
  action := linkAction

def linkCapabilityAdmissible :
    Genesis.capability.Admissible
      (CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre)
      (linkDeclaration.toRequest config) where
  holder := rfl
  scope :=
    { target := by
        simpa [linkDeclaration, linkIntent, config,
          HyperdocumentOperations.Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.target
      verb := by
        simpa [linkDeclaration, linkIntent, config,
          HyperdocumentOperations.Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.verb
      cost := by
        simpa [linkDeclaration, linkIntent, config,
          HyperdocumentOperations.Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.cost }
  validFrom := by decide
  validUntil := by decide
  policyId := rfl
  policyEpoch := rfl
  policyCurrent := rfl
  issuerCurrent := rfl
  selfNotRevoked := Genesis.principal.selfNotRevoked
  ancestorNotRevoked := Genesis.principal.ancestorsNotRevoked
  channelNotRevoked := Genesis.principal.channelsNotRevoked

def linkAuthorization : Authorized Genesis.permissivePortal
    (CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre)
    (linkDeclaration.toRequest config) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def linkSemantic : HyperdocumentOperations.ValidOperation config genesisPost
    linkDeclaration where
  canonical :=
    { actionBytesExact := rfl
      documentExact := rfl
      objectCapability := rfl }
  preRootExact := rfl
  writesUnique := by
    simp [linkDeclaration, linkAction, linkPayload,
      HyperdocumentOperations.Declaration.packedWrites,
      HyperdocumentOperations.Action.packedWrites,
      HyperdocumentOperations.linkWrites,
      HyperdocumentOperations.PackedWrite.address]
  expectedExact := by
    intro write member
    simp [linkDeclaration, linkAction, linkPayload,
      HyperdocumentOperations.Declaration.packedWrites,
      HyperdocumentOperations.Action.packedWrites,
      HyperdocumentOperations.linkWrites] at member
    subst write
    exact genesis_link_absent linkId
  rangesValid := by
    intro range impossible
    cases impossible

noncomputable def linkAccepted : HyperdocumentOperations.Accepted config
    Genesis.projection Genesis.authorityPre genesisPost Genesis.permissivePortal
    linkDeclaration :=
  HyperdocumentOperations.accept Genesis.principal linkSemantic
    linkCapabilityAdmissible linkAuthorization
    (Classical.choice (validatedNonempty linkSemantic))

@[simp] theorem link_post_contains_forward :
    lookup linkAccepted.accepted.prepared.post.logical .links linkId =
      some (linkRecord (linkDeclaration.operationId config)
        Genesis.author linkPayload) :=
  linkAccepted.post_contains_link linkPayload rfl

/-! ## Exact causal append -/

noncomputable def linkEvidence :
    HyperdocumentCausalFamily.EventEvidence Genesis.documentMaterializer config
      Genesis.projection Genesis.authorityPre Genesis.permissivePortal
      linkAccepted.causalPreimage where
  documentPre := genesisPost
  declaration := linkDeclaration
  accepted := linkAccepted
  eventExact := rfl

theorem linkWellFormed : linkAccepted.versionEventRecord.CausallyWellFormed := by
  constructor <;> simp [linkAccepted, linkDeclaration, linkIntent,
    HyperdocumentOperations.Accepted.versionEventRecord,
    VersionEventRecord.toCausalPreimage]

noncomputable def linkStored : StoredVersionEvent addressing :=
  StoredVersionEvent.derive eventCodec eventDerivation
    linkAccepted.versionEventRecord linkWellFormed

noncomputable def linkNode :
    CausalVersionDag.VerifiedEvent addressing semanticFamily :=
  linkStored.toVerifiedEvent linkEvidence

noncomputable def anchor : CausalVersionDag.Anchor :=
  HyperdocumentCausalFamily.anchorOf genesisAccepted

noncomputable def genesisValid :
    CausalVersionDag.ValidAppend anchor [] genesisNode where
  anchorExact := HyperdocumentCausalFamily.anchorOf_contains genesisAccepted
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
  parentCompatibility :=
    HyperdocumentCausalFamily.ParentCompatible.genesis
      genesisAccepted.causalPreimage rfl

noncomputable def genesisHistory : CausalVersionDag.History
    (scheme := addressing) (family := semanticFamily) anchor :=
  (CausalVersionDag.History.empty anchor).append genesisNode genesisValid

@[simp] theorem genesis_effect_id : genesisNode.effectId = ⟨1016⟩ := by
  change genesisDeclaration.effectDigest config = ⟨1016⟩
  simp [genesisDeclaration, genesisIntent]

@[simp] theorem link_effect_id : linkNode.effectId = ⟨1026⟩ := by
  change linkDeclaration.effectDigest config = ⟨1026⟩
  simp [linkDeclaration, linkIntent]

@[simp] theorem genesis_request_id : genesisNode.requestId = ⟨2016⟩ := by
  change genesisDeclaration.requestId config = ⟨2016⟩
  simp [genesisDeclaration, genesisIntent]

@[simp] theorem link_request_id : linkNode.requestId = ⟨2026⟩ := by
  change linkDeclaration.requestId config = ⟨2026⟩
  simp [linkDeclaration, linkIntent]

@[simp] theorem genesis_entry_id : genesisNode.entryId = ⟨1016⟩ := by
  calc
    genesisNode.entryId = addressing.address genesisNode.preimage :=
      genesisNode.addressed.entryIdExact
    _ = genesisNode.effectId := address_exact _
    _ = ⟨1016⟩ := genesis_effect_id

@[simp] theorem link_entry_id : linkNode.entryId = ⟨1026⟩ := by
  calc
    linkNode.entryId = addressing.address linkNode.preimage :=
      linkNode.addressed.entryIdExact
    _ = linkNode.effectId := address_exact _
    _ = ⟨1026⟩ := link_effect_id

@[simp] theorem genesis_preimage_exact :
    genesisNode.preimage = genesisAccepted.causalPreimage :=
  rfl

@[simp] theorem link_preimage_exact :
    linkNode.preimage = linkAccepted.causalPreimage :=
  rfl

@[simp] theorem link_parent_frontier_exact :
    linkNode.preimage.parentFrontier = [genesisNode.entryId] := by
  change [genesisStored.key.digest] = [genesisStored.key.digest]
  rfl

noncomputable def linkValid :
    CausalVersionDag.ValidAppend anchor genesisHistory.events linkNode where
  anchorExact := ⟨rfl, rfl⟩
  genesisShape := Or.inr ⟨by simp [genesisHistory], by
    rw [link_parent_frontier_exact]
    simp⟩
  resolvedParents := [genesisNode]
  resolvedParentsExact := by simpa using link_parent_frontier_exact.symm
  resolvedParentsPresent := by simp [genesisHistory]
  parentAnchorExact := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    exact HyperdocumentCausalFamily.anchorOf_contains genesisAccepted
  parentSchemaExact := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    rfl
  schemaVersionMonotone := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    exact Nat.le_refl _
  semanticVersionIncreases := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    change 0 < 1
    decide
  entryFresh := by
    intro old present
    change old ∈ [genesisNode] at present
    have oldExact : old = genesisNode := by
      simpa using present
    subst old
    simp
  requestFresh := by
    intro old present
    change old ∈ [genesisNode] at present
    have oldExact : old = genesisNode := by
      simpa using present
    subst old
    simp
  effectFresh := by
    intro old present
    change old ∈ [genesisNode] at present
    have oldExact : old = genesisNode := by
      simpa using present
    subst old
    simp
  parentCompatibility :=
    HyperdocumentCausalFamily.ParentCompatible.linear
      genesisAccepted.causalPreimage linkAccepted.causalPreimage rfl

noncomputable def history : CausalVersionDag.History
    (scheme := addressing) (family := semanticFamily) anchor :=
  genesisHistory.append linkNode linkValid

@[simp] theorem history_exact : history.events = [genesisNode, linkNode] :=
  rfl

/-! ## Sparse event-log effect after a retained genesis event -/

deriving instance Countable for HyperdocumentVersionEffects.Declaration
deriving instance Nonempty for VersionEventRecord
deriving instance Nonempty for HyperdocumentVersionEffects.Declaration

noncomputable def eventDeclarationCodec :
    LawfulCodec HyperdocumentVersionEffects.Declaration :=
  Minidregg.Theory.DeployedMaterializerWitness.codecOfCountable
    HyperdocumentVersionEffects.Declaration

noncomputable def eventConfig : HyperdocumentVersionEffects.Config where
  declarationCodec := eventDeclarationCodec
  requestCodec := requestCodec
  effectDerivation := intentDerivation
  requestDerivation := requestDerivation
  eventCodec := eventCodec
  eventDerivation := eventDerivation
  requestDomain := config.requestDomain
  semanticRelation := ⟨703⟩

noncomputable def eventRepresentation :
    HyperdocumentEventLog.Representation Digest :=
  Minidregg.Kernel.DeployedMaterializerWitness.eventLogRepresentation

def eventStore : HyperdocumentEventLog.Sparse.Store :=
  HyperdocumentEventLog.Sparse.empty.set .events genesisStored.key
    (some genesisAccepted.versionEventRecord)

@[simp] theorem eventStore_contains_genesis :
    eventStore .events genesisStored.key =
      some genesisAccepted.versionEventRecord := by
  exact Minidregg.Kernel.SparseAuthenticatedState.Store.set_eq
    _ _ _ _

noncomputable def eventLogPre :
    CellState.Materialized eventRepresentation.cellMaterializer :=
  HyperdocumentVersionEffects.cellPre eventRepresentation eventStore

def eventDeclaration : HyperdocumentVersionEffects.Declaration where
  expectedLogRoot := eventLogPre.{0, 0}.root
  request := linkDeclaration.request
  record := linkAccepted.versionEventRecord

@[simp] theorem event_key_exact :
    eventDeclaration.key eventConfig = linkStored.key :=
  rfl

theorem eventFresh :
    eventStore .events (eventDeclaration.key eventConfig) = none := by
  apply Minidregg.Kernel.SparseAuthenticatedState.Store.set_ne
  intro equal
  have keyEqual : eventDeclaration.key eventConfig = genesisStored.key := by
    injection equal
  have digestEqual := congrArg Identifier.digest keyEqual
  change linkNode.entryId = genesisNode.entryId at digestEqual
  simp at digestEqual

def eventSource : HyperdocumentVersionEffects.SourceExact linkAccepted
    eventDeclaration where
  recordExact := rfl
  requestExact := rfl

def eventCapabilityAdmissible :
    Genesis.capability.Admissible
      (CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre)
      (eventDeclaration.toRequest eventConfig) where
  holder := rfl
  scope :=
    { target := by
        simpa [eventDeclaration,
          HyperdocumentVersionEffects.Declaration.toRequest, linkDeclaration,
          linkIntent] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.target
      verb := by
        simpa [eventDeclaration,
          HyperdocumentVersionEffects.Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.verb
      cost := by
        simpa [eventDeclaration, linkDeclaration,
          HyperdocumentVersionEffects.Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.cost }
  validFrom := by decide
  validUntil := by decide
  policyId := rfl
  policyEpoch := rfl
  policyCurrent := rfl
  issuerCurrent := rfl
  selfNotRevoked := Genesis.principal.selfNotRevoked
  ancestorNotRevoked := Genesis.principal.ancestorsNotRevoked
  channelNotRevoked := Genesis.principal.channelsNotRevoked

def eventAuthorization : Authorized Genesis.permissivePortal
    (CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre)
    (eventDeclaration.toRequest eventConfig) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

theorem eventValidatedNonempty : Nonempty
    (ValidatedPatch eventRepresentation.cellMaterializer
      eventLogPre.{0, 0}
      (eventDeclaration.patch eventConfig)) := by
  generalize exactOutcome : validate eventRepresentation.cellMaterializer
    eventLogPre.{0, 0}
    (eventDeclaration.patch eventConfig) = outcome
  cases outcome with
  | accepted validated => exact ⟨validated⟩
  | rejected reason =>
      have rootExact :
          (eventDeclaration.patch eventConfig).expectedPreRoot =
            eventLogPre.{0, 0}.root := rfl
      unfold validate at exactOutcome
      rw [dif_pos rootExact,
        dif_pos (HyperdocumentVersionEffects.Declaration.patch_namedFields _ _).symm,
        dif_pos (HyperdocumentVersionEffects.Declaration.patch_namedResources _ _).symm]
        at exactOutcome
      cases exactOutcome

noncomputable def eventAccepted : HyperdocumentVersionEffects.Accepted
    linkAccepted eventRepresentation eventStore eventConfig
    Genesis.permissivePortal eventDeclaration :=
  HyperdocumentVersionEffects.accept eventSource Genesis.principal
    eventCapabilityAdmissible linkWellFormed eventFresh eventAuthorization
    (Classical.choice eventValidatedNonempty)

@[simp] theorem event_post_contains_link_event :
    eventAccepted.accepted.prepared.post.logical.fields
      ⟨HyperdocumentEventLog.Sparse.Namespace.events,
        eventDeclaration.key eventConfig⟩ = some eventDeclaration.record :=
  eventAccepted.post_contains

theorem event_replay_rejected :
    ¬ (HyperdocumentEventLog.Sparse.appendOp
      (eventDeclaration.stored eventConfig eventAccepted.sourceWellFormed)).Enabled
      eventAccepted.sparse.post.logical :=
  eventAccepted.duplicate_rejected

/-! ## One logical atomic content + event publication -/

def header : HyperdocumentPublication.Header := ⟨⟨900⟩, ⟨901⟩⟩
def contentCellId : Digest := ⟨902⟩
def eventCellId : Digest := ⟨903⟩

def boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
    (HyperdocumentPublication.declaration linkAccepted eventAccepted header
      contentCellId eventCellId) where
  Evidence := fun _ _ => Unit

def jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput :=
  ⟨header.apex, ⟨904⟩⟩

noncomputable def commit :=
  HyperdocumentPublication.commit linkAccepted eventAccepted header
    contentCellId eventCellId rfl (by decide) boundary jointInput rfl ()

@[simp] theorem atomic_forward_link :
    lookup (commit.post .content).logical .links linkId =
      some (linkRecord (linkDeclaration.operationId config)
        Genesis.author linkPayload) := by
  change lookup linkAccepted.accepted.prepared.post.logical .links linkId = _
  exact link_post_contains_forward

@[simp] theorem atomic_event_append :
    (commit.post .eventLog).logical.fields
      ⟨HyperdocumentEventLog.Sparse.Namespace.events,
        eventDeclaration.key eventConfig⟩ = some eventDeclaration.record :=
  HyperdocumentPublication.commit_event_post_contains

/-! ## Concrete rejection teeth -/

/-- A child naming the accepted parent but changing its semantic pre-root
cannot inhabit the ordinary linear compatibility relation. -/
def staleChild : CausalVersionDag.EventPreimage :=
  { linkNode.preimage with
    preStateRoot := ⟨genesisNode.preimage.postStateRoot.value + 1⟩ }

theorem stale_parent_rejected :
    IsEmpty (HyperdocumentCausalFamily.ParentCompatible
      [genesisNode.preimage] staleChild) := by
  constructor
  intro compatible
  cases compatible with
  | linear _ _ rootExact =>
      have impossible : genesisNode.preimage.postStateRoot.value =
          genesisNode.preimage.postStateRoot.value + 1 :=
        congrArg Digest.value rootExact
      omega

/-- A nonempty optional source must resolve both stored endpoints.  The chosen
run is absent even after genesis, so no semantic acceptance token exists. -/
def absentRun : RunId := ⟨⟨300⟩⟩
def absentAtom : AtomId := ⟨⟨301⟩⟩

def badPoint : StablePoint :=
  { run := absentRun
    neighbor := some absentAtom
    bias := .before
    death := .invalidate }

def badRange : StableRange := ⟨badPoint, badPoint⟩

def badLinkPayload : HyperdocumentOperations.LinkPayload :=
  { linkPayload with id := ⟨⟨302⟩⟩, source := some badRange }

def badLinkIntent : OperationIntent :=
  { linkIntent with
    nonce := 303
    actionBytes := actionCodec.encode (.link badLinkPayload) }

def badLinkDeclaration : HyperdocumentOperations.Declaration :=
  { intent := badLinkIntent
    request := Genesis.requestEnvelope
    action := .link badLinkPayload }

theorem optional_source_out_of_range_rejected :
    ¬ HyperdocumentOperations.ValidOperation config genesisPost
      badLinkDeclaration := by
  intro semantic
  have stored := semantic.rangesValid badRange rfl
  rcases stored.start with ⟨run, opened, _, _⟩
  have framed := genesisAccepted.accepted.field_frame
    (⟨.runs, badPoint.run⟩ : Hyperdocument.Address) (by
      simp [genesisDeclaration, genesisAction,
        HyperdocumentOperations.family,
        HyperdocumentOperations.Declaration.patch,
        HyperdocumentOperations.Declaration.fieldWrites,
        HyperdocumentOperations.Declaration.packedWrites,
        HyperdocumentOperations.Action.packedWrites,
        HyperdocumentOperations.createWrites,
        HyperdocumentOperations.PackedWrite.toFieldWrite,
        HyperdocumentOperations.PackedWrite.address]
      constructor <;> intro equal <;> cases equal)
  have absent : lookup genesisPost.logical .runs badPoint.run = none := by
    simpa [Hyperdocument.lookup] using framed
  change lookup genesisPost.logical .runs badPoint.run = some run at opened
  rw [absent] at opened
  contradiction

def outsideTarget : ResourceId .object := ⟨999⟩

theorem outside_scope_rejected :
    ¬ Genesis.capability.Admissible
      (CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre)
      ((linkDeclaration.toRequest config).retarget outsideTarget) :=
  target_substitution_rejected Genesis.capability
    (CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre)
    (linkDeclaration.toRequest config) outsideTarget (by
      simp only [Genesis.capability,
        Minidregg.Theory.HyperdocumentCausalFamily.Witness.capability,
        Finset.mem_singleton]
      intro equal
      have valueEqual := congrArg ResourceId.value equal
      norm_num [outsideTarget,
        Minidregg.Theory.HyperdocumentCausalFamily.Witness.declaration,
        Minidregg.Theory.HyperdocumentCausalFamily.Witness.intent,
        Minidregg.Theory.HyperdocumentCausalFamily.Witness.documentId,
        Minidregg.Theory.HyperdocumentCausalFamily.Witness.config,
        HyperdocumentOperations.Declaration.toRequest] at valueEqual)

def revokedState : AuthState :=
  { CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre with
    revoked := {RevocationKey.capability Genesis.capability.id} }

theorem revoked_capability_rejected :
    ¬ Genesis.capability.Admissible revokedState
      (linkDeclaration.toRequest config) := by
  intro admitted
  exact admitted.selfNotRevoked (by simp [revokedState])

theorem causal_entry_replay_tooth :
    genesisNode.entryId ≠ linkNode.entryId :=
  linkValid.no_entry_replay (old := genesisNode) (by simp [genesisHistory])

theorem causal_request_replay_tooth :
    genesisNode.requestId ≠ linkNode.requestId :=
  linkValid.no_request_replay (old := genesisNode) (by simp [genesisHistory])

theorem causal_effect_replay_tooth :
    genesisNode.effectId ≠ linkNode.effectId :=
  linkValid.no_effect_replay (old := genesisNode) (by simp [genesisHistory])

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentLinkPublicationWitness.link_post_contains_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms link_post_contains_forward
/-- info: 'Minidregg.Assurance.HyperdocumentLinkPublicationWitness.history_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms history_exact
/-- info: 'Minidregg.Assurance.HyperdocumentLinkPublicationWitness.atomic_forward_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms atomic_forward_link
/-- info: 'Minidregg.Assurance.HyperdocumentLinkPublicationWitness.event_replay_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms event_replay_rejected
/-- info: 'Minidregg.Assurance.HyperdocumentLinkPublicationWitness.optional_source_out_of_range_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms optional_source_out_of_range_rejected

end

end Minidregg.Assurance.HyperdocumentLinkPublicationWitness
