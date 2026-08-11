/-
# Assurance.HyperdocumentTransclusionReferenceDeployment -- exact typed references

This module supplies the missing concrete `ReferenceEncoding` for the bounded
Hyperdocument path.  The encoding is deliberately not a hash: a lawful,
prefix-decodable structural codec serializes every typed reference and the
Lean byte-list encoder embeds those bytes injectively in the characteristic
zero semantic field.  Consequently the field-cell list is globally injective
without assuming collision resistance.

One accepted `.link` operation stores a complete `StoredTransclusionRef` in
the ordinary Hyperdocument cell, and the ordinary link response codec plus
`ContentQuery` reopen that exact record.  An exact realization recovers the
same typed reference, including its bounded opening and disclosure ceiling.

The reverse index at the end is complete only for its explicitly supplied,
finite list of authenticated events.  It is not a crawler, a global search
index, or a finality/availability theorem.  PCS opening soundness, commitment
collision resistance, Fiat--Shamir/ROM, external finality, physical storage,
search-index coverage, and response availability remain named premises.
-/

import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Assurance.HyperdocumentLinkEndpointController
import Compiler.HyperdocumentContentPageMaterializer

namespace Minidregg.Assurance.HyperdocumentTransclusionReferenceDeployment

open Minidregg.Assurance.HyperdocumentHistoryAdmission
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.TransclusionBacklinkHistory
open Minidregg.Compiler
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.HyperdocumentContentPageMaterializer
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Loom
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentInterface
open Minidregg.Theory.HyperdocumentOperationIntent
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ## A lossless bounded-field reference codec -/

/-- This characteristic-zero field is the semantic reference-codec carrier.
It is not advertised as the production proof system's finite security field. -/
abbrev Fld := ℚ

@[reducible] def uint8Encodable : Encodable UInt8 where
  encode byte := byte.toNat
  decode value :=
    if inRange : value < 2 ^ 8 then some (UInt8.ofNat value) else none
  encodek := by
    intro byte
    simp [byte.toNat_lt, UInt8.ofNat_toNat]

local instance : Encodable UInt8 := uint8Encodable

local instance uint8LinearOrder : LinearOrder UInt8 :=
  LinearOrder.lift' UInt8.toNat (by
    intro left right equal
    exact UInt8.toNat_inj.mp equal)

/-- Disclosure sets are placed on wire in lexicographic
`(namespace digest, payload bytes)` order.  This avoids the noncomputable
`Finset.toList` choice used by the schema-neutral codec. -/
local instance disclosureAtomLinearOrder : LinearOrder DisclosureAtom :=
  LinearOrder.lift'
    (fun atom => toLex (atom.namespaceId.value, atom.payload)) (by
      intro left right equal
      have fields := congrArg ofLex equal
      cases left with
      | mk leftNamespace leftPayload =>
          cases right with
          | mk rightNamespace rightPayload =>
              cases leftNamespace with
              | mk leftValue =>
                  cases rightNamespace with
                  | mk rightValue =>
                      change (leftValue, leftPayload) =
                        (rightValue, rightPayload) at fields
                      cases fields
                      rfl)

def finStream (size : Nat) : StreamCodec (Fin size) where
  encode value := StreamCodec.nat.encode value.val
  decodePrefix bytes := do
    let (value, suffix) <- StreamCodec.nat.decodePrefix bytes
    if inBounds : value < size then
      some (⟨value, inBounds⟩, suffix)
    else
      none
  decodePrefix_encode := by
    intro value suffix
    simp [StreamCodec.nat.decodePrefix_encode, value.isLt]

noncomputable def fldStream : StreamCodec Fld where
  encode value := StreamCodec.nat.encode (Encodable.encode value)
  decodePrefix bytes := do
    let (code, suffix) <- StreamCodec.nat.decodePrefix bytes
    let value <- Encodable.decode code
    some (value, suffix)
  decodePrefix_encode := by
    intro value suffix
    simp [StreamCodec.nat.decodePrefix_encode, Encodable.encodek]

def boundReceiptIxStream (n : Nat) : StreamCodec (BoundReceiptIx n) :=
  StreamCodec.xmap (finStream (16 + n * 3))
    (boundReceiptIxEquivRuntime n)
    (boundReceiptIxEquivRuntime n).symm
    (boundReceiptIxEquivRuntime n).symm_apply_apply

def openingShapeTag : OpeningShape -> Nat
  | .value => 0
  | .range => 1

def openingShapeOfTag : Nat -> OpeningShape
  | 0 => .value
  | _ => .range

def openingShapeStream : StreamCodec OpeningShape :=
  StreamCodec.xmap StreamCodec.nat openingShapeTag openingShapeOfTag
    (by intro shape; cases shape <;> rfl)

def referenceModeTag : Mode -> Nat
  | .snapshot => 0
  | .live => 1

def referenceModeOfTag : Nat -> Mode
  | 0 => .snapshot
  | _ => .live

def referenceModeStream : StreamCodec Mode :=
  StreamCodec.xmap StreamCodec.nat referenceModeTag referenceModeOfTag
    (by intro mode; cases mode <;> rfl)

def sourceIdentityStream : StreamCodec SourceIdentity :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream digestStream)))
    (fun source => (source.domain, source.object, source.historyEntryRoot,
      source.semanticRoot))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro source; cases source; rfl)

def openingStream (n : Nat) : StreamCodec (RangeOrValueOpening n Fld) :=
  StreamCodec.xmap
    (StreamCodec.product openingShapeStream
      (StreamCodec.product (StreamCodec.list (boundReceiptIxStream n))
        (StreamCodec.list fldStream)))
    (fun opening => (opening.shape, opening.coordinates, opening.cells))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro opening; cases opening; rfl)

def disclosureSetStream : StreamCodec (Finset DisclosureAtom) :=
  StreamCodec.xmap (StreamCodec.list disclosureAtomStream)
    (fun atoms => atoms.sort (fun left right => left <= right))
    List.toFinset
    (by
      intro atoms
      ext atom
      simp)

/-- A structural codec assembled from the same canonical digest, disclosure,
finite-coordinate, and typed-field leaves used by the bounded Hyperdocument
compiler path.  This is the exact typed representation named by the stored
opening descriptor below. -/
noncomputable def referenceStream (n : Nat) :
    StreamCodec (TransclusionRef n Fld DisclosureAtom) :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product sourceIdentityStream
          (StreamCodec.product (openingStream n)
          (StreamCodec.product referenceModeStream
            (StreamCodec.product disclosureSetStream disclosureSetStream)))))
    (fun reference =>
      (reference.referenceRoot, reference.source, reference.opening,
        reference.mode, reference.disclosure, reference.capabilityCeiling))
    (fun wire =>
      ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
        wire.2.2.2.2.1, wire.2.2.2.2.2⟩)
    (by intro reference; cases reference; rfl)

noncomputable def referenceCodec (n : Nat) :
    LawfulCodec (TransclusionRef n Fld DisclosureAtom) :=
  (referenceStream n).toLawful

noncomputable def byteCode (bytes : List UInt8) : Fld :=
  (Encodable.encode bytes : Nat)

theorem byteCode_injective : Function.Injective byteCode := by
  intro left right equal
  apply Encodable.encode_injective
  exact Nat.cast_injective equal

/-- The concrete missing carrier.  It is injective because both the lawful
typed codec and byte-list-to-characteristic-zero-field embedding are
injective. -/
noncomputable def encoding (n : Nat) :
    ReferenceEncoding n Fld DisclosureAtom where
  cells reference := [byteCode ((referenceCodec n).encode reference)]
  injective := by
    intro left right equal
    apply HyperdocumentContentPageMaterializer.lawfulCodec_encode_injective
      (referenceCodec n)
    apply byteCode_injective
    simpa using equal

theorem encoding_cells_nonempty {n : Nat}
    (reference : TransclusionRef n Fld DisclosureAtom) :
    (encoding n).cells reference ≠ [] := by
  simp [encoding]

/-! ## One exact realized reference -/

def sourceOpening : RangeOrValueOpening 1 Fld where
  shape := .value
  coordinates := [.inr (0, .post)]
  cells := [42]

def openingCodecId : Digest := ⟨93001⟩
def openingRelationId : Digest := ⟨93002⟩
def linkRelationId : Digest := ⟨93003⟩
def referenceRoot : Digest := ⟨93004⟩

/-- The descriptor commitment is a transparent application identifier in this
logical deployment.  Collision resistance is not asserted for it. -/
def descriptorCommitment (bytes : List UInt8) : Digest :=
  ⟨93005 + bytes.length⟩

def openingRepresentation : StoredReference.OpeningRepresentation 1 Fld where
  codecId := openingCodecId
  relationId := openingRelationId
  codec := (openingStream 1).toLawful
  commitDescriptor := descriptorCommitment

def storedSource : StoredSourceIdentity where
  historyDomain := ⟨15⟩
  objectRoot :=
    Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.documentId.digest
  historyEntryRoot := ⟨93006⟩
  semanticRoot := ⟨93007⟩

def storedReference : StoredTransclusionRef where
  referenceRoot := referenceRoot
  source := storedSource
  opening :=
    { shape := .value
      openingCodecId := openingCodecId
      openingRelationId := openingRelationId
      canonicalDescriptor := openingRepresentation.codec.encode sourceOpening
      openingCommitment := descriptorCommitment
        (openingRepresentation.codec.encode sourceOpening) }
  mode := .snapshot
  disclosureScope := ∅
  capabilityCeiling := ∅

def realizedReference : StoredReference.RealizedReference 1 Fld storedReference where
  representation := openingRepresentation
  realization :=
    { opening := sourceOpening
      shapeExact := rfl
      codecIdExact := rfl
      relationIdExact := rfl
      descriptorExact := rfl
      commitmentExact := rfl
      disclosureWithinCeiling := by simp [storedReference] }

def targetReference : TransclusionRef 1 Fld DisclosureAtom :=
  realizedReference.toRef

@[simp] theorem target_reference_root :
    targetReference.referenceRoot = referenceRoot := rfl

@[simp] theorem target_reference_opening :
    targetReference.opening = sourceOpening := rfl

theorem target_reference_descriptor_exact :
    openingRepresentation.codec.encode targetReference.opening =
      storedReference.opening.canonicalDescriptor :=
  realizedReference.toRef_descriptorExact

theorem target_reference_within_ceiling :
    targetReference.disclosure ⊆ targetReference.capabilityCeiling :=
  realizedReference.toRef_disclosureWithinCeiling

/-! ## Accepted publication and exact canonical reopening -/

namespace Prior

open Minidregg.Assurance.HyperdocumentLinkPublicationWitness

abbrev config :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.config
abbrev documentPre :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.genesisPost
abbrev principal :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.principal
abbrev projection :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.projection
abbrev authorityPre :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.authorityPre
abbrev portal :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.permissivePortal
abbrev author :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.author
abbrev documentId :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.documentId
abbrev requestEnvelope :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.requestEnvelope
abbrev actionCodec :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.actionCodec
abbrev capability :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.capability

end Prior

def transclusionId : TransclusionId := ⟨⟨93008⟩⟩
def forwardLinkId : LinkId := ⟨⟨93009⟩⟩

def forwardPayload : LinkPayload where
  id := forwardLinkId
  sourceDocument := Prior.documentId
  source := none
  target := .transclusion transclusionId storedReference
  relation := linkRelationId

def forwardAction : Action := .link forwardPayload

def forwardIntent : OperationIntent where
  historyDomain := ⟨15⟩
  document := Prior.documentId
  schema := { schemaId := ⟨14⟩, version := 1 }
  semanticVersion := 2
  parents := []
  author := Prior.author
  expectedContentRoot := Prior.documentPre.root
  nonce := 93010
  actionBytes := Prior.actionCodec.encode forwardAction

def forwardDeclaration : Declaration where
  intent := forwardIntent
  request := Prior.requestEnvelope
  action := forwardAction

def capabilityAdmissible :
    Prior.capability.Admissible
      (CredentialAuthorityState.authState Prior.projection Prior.authorityPre)
      (forwardDeclaration.toRequest Prior.config) where
  holder := rfl
  scope :=
    { target := by
        simpa [forwardDeclaration, forwardIntent, Prior.config,
          Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.target
      verb := by
        simpa [forwardDeclaration, forwardIntent, Prior.config,
          Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.verb
      cost := by
        simpa [forwardDeclaration, forwardIntent, Prior.config,
          Declaration.toRequest] using
          Minidregg.Theory.HyperdocumentCausalFamily.Witness.namedCapabilityAdmissible.scope.cost }
  validFrom := by decide
  validUntil := by decide
  policyId := rfl
  policyEpoch := rfl
  policyCurrent := rfl
  issuerCurrent := rfl
  selfNotRevoked := Prior.principal.selfNotRevoked
  ancestorNotRevoked := Prior.principal.ancestorsNotRevoked
  channelNotRevoked := Prior.principal.channelsNotRevoked

def authorization : Authorized Prior.portal
    (CredentialAuthorityState.authState Prior.projection Prior.authorityPre)
    (forwardDeclaration.toRequest Prior.config) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def forwardAddress : Hyperdocument.Address := ⟨.links, forwardLinkId⟩

theorem forward_absent :
    Hyperdocument.lookup Prior.documentPre.logical .links forwardLinkId = none := by
  exact
    Minidregg.Assurance.HyperdocumentLinkPublicationWitness.genesis_link_absent
      forwardLinkId

def semantic : ValidOperation Prior.config Prior.documentPre
    forwardDeclaration where
  canonical :=
    { actionBytesExact := rfl
      documentExact := rfl
      objectCapability := rfl }
  preRootExact := by simp [forwardDeclaration, forwardIntent]
  writesUnique := by
    simp [forwardDeclaration, forwardAction, forwardPayload,
      Declaration.packedWrites, Action.packedWrites,
      HyperdocumentOperations.linkWrites, PackedWrite.address]
  expectedExact := by
    intro write member
    simp [forwardDeclaration, forwardAction, forwardPayload,
      Declaration.packedWrites, Action.packedWrites,
      HyperdocumentOperations.linkWrites] at member
    subst write
    exact forward_absent
  rangesValid := by
    intro range impossible
    cases impossible

noncomputable def accepted : Accepted Prior.config Prior.projection
    Prior.authorityPre Prior.documentPre Prior.portal forwardDeclaration :=
  HyperdocumentOperations.accept Prior.principal semantic capabilityAdmissible
    authorization
    (Classical.choice
      (Minidregg.Assurance.HyperdocumentLinkPublicationWitness.validatedNonempty
        semantic))

def forwardRecord : LinkRecord :=
  linkRecord (forwardDeclaration.operationId Prior.config) Prior.author
    forwardPayload

@[simp] theorem accepted_post_contains_forward :
    Hyperdocument.lookup accepted.accepted.prepared.post.logical .links
      forwardLinkId = some forwardRecord := by
  simpa [forwardRecord, forwardDeclaration, forwardIntent] using
    accepted.post_contains_link forwardPayload rfl

def forwardQuery : ContentQuery := .link forwardLinkId

@[simp] theorem query_reopens_exact_forward :
    ContentQuery.project forwardQuery accepted.accepted.prepared.post.logical =
      some forwardRecord := by
  simpa [forwardQuery, ContentQuery.project] using accepted_post_contains_forward

noncomputable def responseBytes : List UInt8 :=
  HyperdocumentLinkEndpointController.linkRecordCodec.encode forwardRecord

@[simp] theorem response_decodes_exact_forward :
    HyperdocumentLinkEndpointController.linkRecordCodec.decode responseBytes =
      some forwardRecord :=
  HyperdocumentLinkEndpointController.linkRecordCodec.decode_encode forwardRecord

def forwardRealization :
    StoredReference.ForwardLinkRealization 1 Fld forwardRecord where
  transclusionId := transclusionId
  stored := storedReference
  targetExact := rfl
  realized := realizedReference

@[simp] theorem reopened_typed_reference_exact :
    forwardRealization.targetRef = targetReference := rfl

theorem exact_forward_reopen :
    ContentQuery.project forwardQuery accepted.accepted.prepared.post.logical =
        some forwardRecord ∧
      HyperdocumentLinkEndpointController.linkRecordCodec.decode responseBytes =
        some forwardRecord ∧
      forwardRecord.target = .transclusion transclusionId storedReference ∧
      forwardRealization.targetRef = targetReference :=
  ⟨query_reopens_exact_forward, response_decodes_exact_forward, rfl, rfl⟩

/-! ## One authenticated encoding event -/

abbrev eventCells : List Fld := (encoding 1).cells targetReference
abbrev eventWidth : Nat := 1

noncomputable def eventPost (_index : Fin eventWidth) : Fld :=
  byteCode ((referenceCodec 1).encode targetReference)

def eventDelta : ReceiptDelta (fun _ : Fin eventWidth => 0) eventPost where
  touched := Finset.univ
  frame := by simp

def eventClaim : BoundSemanticReceiptClaim eventWidth Fld where
  witness :=
    { binding := fun _ => 0
      core := ReceiptWitness.ofDelta eventDelta }
  valid := ReceiptWitness.ofDelta_satisfies eventDelta

def eventManifest : Manifest where
  manifestVersion := 1
  abiId := ⟨93011⟩
  semanticProgramId := ⟨93012⟩
  semanticRelationId := linkRelationId
  receiptCodecId := ⟨93013⟩
  codecs := []
  carriers := []
  bridges := []
  dialectClauses := []
  transcriptControllerDigest := ⟨93014⟩
  dimensions := []
  bounds := []

def eventRegistry : ControllerRegistry.{0, 0, 0, 0} := ⟨[]⟩

def eventClauseEvidence : ClauseEvidenceFamily eventManifest eventRegistry where
  Evidence := fun _ _ _ => PEmpty.{1}

def eventContext : HistoryAdmissionContext where
  manifestAddress := eventManifest.contentAddress
  historyDomain := forwardIntent.historyDomain
  sequence := 0
  previousReceiptRoot := none
  semanticObjectRoot := Prior.documentId.digest
  semanticRelationId := linkRelationId
  outcome := .committed
  preStateRoot := Prior.documentPre.root
  postStateRoot := accepted.accepted.prepared.post.root
  effectRoot := forwardDeclaration.effectDigest Prior.config
  authorizationRoot := Prior.authorityPre.root
  disclosureRoot := ⟨0⟩
  dialectClauseRoots := []

theorem eventContext_wellFormed : eventContext.WellFormed eventManifest where
  manifestExact := rfl
  semanticRelationExact := rfl
  historyLink := .inl ⟨rfl, rfl⟩
  rejectedAtomic := trivial
  dialectClauseIdsUnique := List.nodup_nil
  dialectClausesClosed := fun _ absent => absurd absent List.not_mem_nil

/-- The only semantic evidence retains the exact accepted publication. -/
inductive EventEvidence : HistoryAdmissionContext ->
    BoundSemanticReceiptClaim eventWidth Fld -> Type
  | published : EventEvidence eventContext eventClaim

def eventFamily : EntrySemanticsFamily eventWidth Fld where
  Evidence := EventEvidence
  rejectedCoreAtomic := by
    intro context claim evidence denial rejected
    cases evidence
    cases rejected

def eventHeader : HistoryAdmissionContext -> BindingIx -> Fld := fun _ _ => 0
def eventCode : Submodule Fld (BoundReceiptIx eventWidth -> Fld) := ⊤

def eventEntry : VerifiedEntry
    (manifest := eventManifest) (registry := eventRegistry)
    (clauseEvidence := eventClauseEvidence) (family := eventFamily)
    (headerCells := eventHeader) (C := eventCode) where
  context := eventContext
  claim := eventClaim
  semantics := .published
  contextWellFormed := eventContext_wellFormed
  dialectEvidence := ⟨fun index => index.elim0, fun index => index.elim0⟩
  bindingExact := rfl
  codeword := Submodule.mem_top

def eventOpening : RangeOrValueOpening eventWidth Fld where
  shape := .range
  coordinates := [.inr (0, .post)]
  cells := eventCells

@[simp] theorem eventEntry_word_post (index : Fin eventWidth) :
    eventEntry.word (.inr (index, .post)) = eventPost index := rfl

theorem eventOpening_exact : eventOpening.Exact eventEntry.word where
  cellsExact := by
    rfl
  valueShape := by intro impossible; cases impossible
  rangeShape := by
    intro _
    constructor
    · simp [eventOpening]
    · simp [eventOpening]

/-! ## Finite-domain backlinks with explicit security premises -/

section SecurityCeiling

variable
    (FinalityEvidence : HistoryAdmissionContext -> Prop)
    (PCSOpeningSound : BoundSemanticReceiptClaim eventWidth Fld ->
      RangeOrValueOpening eventWidth Fld -> Prop)
    (CommitmentBindingCR : BoundSemanticReceiptClaim eventWidth Fld -> Prop)
    (RandomOracleModel : BoundSemanticReceiptClaim eventWidth Fld -> Prop)

/-- These premises are not constructed here.  In particular, the transparent
descriptor identifier and the logical accepted cell do not imply them. -/
structure SecurityEvidence : Prop where
  externallyFinal : FinalityEvidence eventContext
  pcsOpeningSound : PCSOpeningSound eventClaim eventOpening
  commitmentBinding : CommitmentBindingCR eventClaim
  fiatShamirROM : RandomOracleModel eventClaim

variable (evidence : SecurityEvidence FinalityEvidence PCSOpeningSound
  CommitmentBindingCR RandomOracleModel)

include evidence

def authenticatedForward : LinkEvent
    (manifest := eventManifest) (registry := eventRegistry)
    (clauseEvidence := eventClauseEvidence) (family := eventFamily)
    (headerCells := eventHeader) (C := eventCode)
    FinalityEvidence PCSOpeningSound CommitmentBindingCR RandomOracleModel
    (encoding 1) linkRelationId :=
  TransclusionBacklinkHistory.forwardLink FinalityEvidence PCSOpeningSound
    CommitmentBindingCR RandomOracleModel (encoding 1) linkRelationId
    eventEntry targetReference eventOpening rfl rfl eventOpening_exact rfl
    target_reference_within_ceiling evidence.externallyFinal
    evidence.pcsOpeningSound evidence.commitmentBinding evidence.fiatShamirROM

/-- The declared domain is exactly this finite authenticated list.  It makes
no claim that some wider history, server, network, or web has been exhausted. -/
structure FiniteDomain where
  historyDomain : Digest
  firstSequence : Nat
  pastSequence : Nat
  events : List (LinkEvent
    (manifest := eventManifest) (registry := eventRegistry)
    (clauseEvidence := eventClauseEvidence) (family := eventFamily)
    (headerCells := eventHeader) (C := eventCode)
    FinalityEvidence PCSOpeningSound CommitmentBindingCR RandomOracleModel
    (encoding 1) linkRelationId)
  sourceInSlice : forall event, event ∈ events ->
    event.entry.context.historyDomain = historyDomain /\
      firstSequence <= event.entry.context.sequence /\
      event.entry.context.sequence < pastSequence

def singletonDomain : FiniteDomain FinalityEvidence PCSOpeningSound
    CommitmentBindingCR RandomOracleModel where
  historyDomain := eventContext.historyDomain
  firstSequence := 0
  pastSequence := 1
  events := [authenticatedForward FinalityEvidence PCSOpeningSound
    CommitmentBindingCR RandomOracleModel evidence]
  sourceInSlice := by
    intro event member
    simp only [List.mem_singleton] at member
    subst event
    change eventContext.historyDomain = eventContext.historyDomain /\
      0 <= eventContext.sequence /\ eventContext.sequence < 1
    simp [eventContext]

def finiteBacklinks
    (domain : FiniteDomain FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel)
    (target : SourceIdentity) :=
  domain.events.filter fun event => event.target.source = target

omit evidence in
theorem finiteBacklinks_sound
    (domain : FiniteDomain FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel)
    (target : SourceIdentity) (event)
    (member : event ∈ finiteBacklinks FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel domain target) :
    event ∈ domain.events /\ event.target.source = target := by
  simpa [finiteBacklinks] using member

omit evidence in
theorem finiteBacklinks_complete_in_declared_domain
    (domain : FiniteDomain FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel)
    (target : SourceIdentity) (event)
    (declared : event ∈ domain.events)
    (targetExact : event.target.source = target) :
    event ∈ finiteBacklinks FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel domain target := by
  simp [finiteBacklinks, declared, targetExact]

theorem singleton_backlink_recovered :
    authenticatedForward FinalityEvidence PCSOpeningSound
        CommitmentBindingCR RandomOracleModel evidence ∈
      finiteBacklinks FinalityEvidence PCSOpeningSound CommitmentBindingCR
        RandomOracleModel
        (singletonDomain FinalityEvidence PCSOpeningSound CommitmentBindingCR
          RandomOracleModel evidence)
        targetReference.source := by
  have targetExact :
      (authenticatedForward FinalityEvidence PCSOpeningSound
        CommitmentBindingCR RandomOracleModel evidence).target.source =
        targetReference.source := by
    rfl
  simp [finiteBacklinks, singletonDomain, targetExact]

end SecurityCeiling

/-! ## External deployment and service ceilings -/

/-- Required before the finite logical result may be advertised as a durable,
globally searchable, externally final, available backlink service.  This
module deliberately provides no inhabitant. -/
structure ExternalCompletion
    (PhysicalStorageRefined SearchIndexCoversRequestedDomain
      ExternallyFinal ResponseAvailable : Prop) : Prop where
  physicalStorageRefined : PhysicalStorageRefined
  searchIndexCoversRequestedDomain : SearchIndexCoversRequestedDomain
  externallyFinal : ExternallyFinal
  responseAvailable : ResponseAvailable

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentTransclusionReferenceDeployment.encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encoding
/-- info: 'Minidregg.Assurance.HyperdocumentTransclusionReferenceDeployment.exact_forward_reopen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_forward_reopen
/-- info: 'Minidregg.Assurance.HyperdocumentTransclusionReferenceDeployment.eventOpening_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eventOpening_exact
/-- info: 'Minidregg.Assurance.HyperdocumentTransclusionReferenceDeployment.singleton_backlink_recovered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms singleton_backlink_recovered

end

end Minidregg.Assurance.HyperdocumentTransclusionReferenceDeployment
