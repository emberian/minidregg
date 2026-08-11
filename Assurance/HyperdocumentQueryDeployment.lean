/-
# Assurance.HyperdocumentQueryDeployment -- authorized bounded-page reads

`Theory.HyperdocumentInterface` deliberately leaves `QueryConfig` abstract and
does not construct a `QuerySuccess`.  This module closes that carrier with a
stable v1 query-argument frame, lawful codecs for every query constructor, and
Lean cSHAKE256 addressing of the exact framed argument bytes.

The positive content pole reads the exact link reopened by
`HyperdocumentLinkReopenWitness` from a valid four-slot content page.  The
positive history pole reads one content-addressed, causally well-formed version
event from a valid four-slot event page.  Both retain one current
request-indexed authorization and the same semantically admissible capability.

The history page proves local representation validity and causal identity.  It
does not prove that the page is a member of an authoritative history, that the
selected event is externally final, that cSHAKE is collision resistant, or
that an OS can physically reopen either page.  Those ceilings remain explicit
at the end of the module.
-/
import Assurance.HyperdocumentLinkReopenWitness
import Compiler.HyperdocumentContentPageMaterializer
import Compiler.HyperdocumentEventPageMaterializer
import Compiler.Sp800185Cshake256

namespace Minidregg.Assurance.HyperdocumentQueryDeployment

open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentInterface
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

namespace ContentPage

abbrev Page :=
  Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page
abbrev Entry :=
  Minidregg.Compiler.HyperdocumentContentPageMaterializer.Entry
abbrev ForwardLink :=
  Minidregg.Compiler.HyperdocumentContentPageMaterializer.ForwardLink
abbrev ForwardTarget :=
  Minidregg.Compiler.HyperdocumentContentPageMaterializer.ForwardTarget
abbrev schema :=
  Minidregg.Compiler.HyperdocumentContentPageMaterializer.schema
abbrev materializer :=
  Minidregg.Compiler.HyperdocumentContentPageMaterializer.materializer
abbrev stateOfOption :=
  Minidregg.Compiler.HyperdocumentContentPageMaterializer.stateOfOption
abbrev PairBindingPremise :=
  Minidregg.Compiler.HyperdocumentContentPageMaterializer.PairBindingPremise

end ContentPage

namespace EventPage

abbrev Page :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.Page
abbrev Entry :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.Entry
abbrev schema :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.schema
abbrev materializer :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.materializer
abbrev stateOfOption :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.stateOfOption
abbrev eventScheme :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.eventScheme
abbrev PairBindingPremise :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.PairBindingPremise

end EventPage

set_option autoImplicit false

noncomputable section

namespace Publication

abbrev linkId :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.linkId
noncomputable abbrev linkDeclaration :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.linkDeclaration
noncomputable abbrev operationConfig :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.config
abbrev documentMaterializer :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.documentMaterializer
abbrev documentId :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.documentId
abbrev author :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.author

end Publication

namespace Reopen

noncomputable abbrev record :=
  Minidregg.Assurance.HyperdocumentLinkReopenWitness.record
abbrev query :=
  Minidregg.Assurance.HyperdocumentLinkReopenWitness.query

end Reopen

/-! ## Stable lawful query codec -/

def interfaceSchemaStream : StreamCodec InterfaceSchema where
  encode
    | .contentRead => [0]
    | .contentMutation => [1]
    | .historyRead => [2]
  decodePrefix
    | 0 :: suffix => some (.contentRead, suffix)
    | 1 :: suffix => some (.contentMutation, suffix)
    | 2 :: suffix => some (.historyRead, suffix)
    | _ => none
  decodePrefix_encode := by
    intro schema suffix
    cases schema <;> rfl

def interfaceVersionStream : StreamCodec InterfaceVersion where
  encode
    | .v1 => [1]
    | .reservedV2 => [2]
  decodePrefix
    | 1 :: suffix => some (.v1, suffix)
    | 2 :: suffix => some (.reservedV2, suffix)
    | _ => none
  decodePrefix_encode := by
    intro version suffix
    cases version <;> rfl

def interfaceIdStream : StreamCodec InterfaceId :=
  StreamCodec.xmap
    (StreamCodec.product interfaceSchemaStream interfaceVersionStream)
    (fun interfaceId => (interfaceId.schema, interfaceId.version))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro interfaceId; cases interfaceId; rfl)

def contentQueryStream : StreamCodec ContentQuery where
  encode
    | .link identifier =>
        0 :: (identifierStream .v1 .link).encode identifier
    | .annotation identifier =>
        1 :: (identifierStream .v1 .annotation).encode identifier
  decodePrefix
    | 0 :: bytes => do
        let (identifier, suffix) ←
          (identifierStream .v1 .link).decodePrefix bytes
        some (.link identifier, suffix)
    | 1 :: bytes => do
        let (identifier, suffix) ←
          (identifierStream .v1 .annotation).decodePrefix bytes
        some (.annotation identifier, suffix)
    | _ => none
  decodePrefix_encode := by
    intro query suffix
    cases query with
    | link identifier =>
        simp [(identifierStream .v1 .link).decodePrefix_encode]
    | annotation identifier =>
        simp [(identifierStream .v1 .annotation).decodePrefix_encode]

def historySliceStream : StreamCodec HistorySlice :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))
    (fun slice =>
      (slice.historyDomain, slice.firstSequence, slice.pastSequence))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro slice; cases slice; rfl)

def historyQueryStream : StreamCodec HistoryQuery where
  encode
    | .backlinks slice target =>
        0 :: historySliceStream.encode slice ++
          storedSourceIdentityStream.encode target
    | .version identifier =>
        1 :: (identifierStream .v1 .versionEvent).encode identifier
  decodePrefix
    | 0 :: bytes => do
        let (slice, afterSlice) ← historySliceStream.decodePrefix bytes
        let (target, suffix) ←
          storedSourceIdentityStream.decodePrefix afterSlice
        some (.backlinks slice target, suffix)
    | 1 :: bytes => do
        let (identifier, suffix) ←
          (identifierStream .v1 .versionEvent).decodePrefix bytes
        some (.version identifier, suffix)
    | _ => none
  decodePrefix_encode := by
    intro query suffix
    cases query with
    | backlinks slice target =>
        simp [List.append_assoc, historySliceStream.decodePrefix_encode,
          storedSourceIdentityStream.decodePrefix_encode]
    | version identifier =>
        simp [(identifierStream .v1 .versionEvent).decodePrefix_encode]

def queryStream : StreamCodec Query where
  encode
    | .content query => 0 :: contentQueryStream.encode query
    | .history query => 1 :: historyQueryStream.encode query
  decodePrefix
    | 0 :: bytes => do
        let (query, suffix) ← contentQueryStream.decodePrefix bytes
        some (.content query, suffix)
    | 1 :: bytes => do
        let (query, suffix) ← historyQueryStream.decodePrefix bytes
        some (.history query, suffix)
    | _ => none
  decodePrefix_encode := by
    intro query suffix
    cases query with
    | content query => simp [contentQueryStream.decodePrefix_encode]
    | history query => simp [historyQueryStream.decodePrefix_encode]

abbrev QueryArgumentTuple := InterfaceId × DocumentId × Query

def queryArgumentStream : StreamCodec QueryArgument :=
  StreamCodec.xmap
    (StreamCodec.product interfaceIdStream
      (StreamCodec.product (identifierStream .v1 .document) queryStream))
    (fun argument =>
      (argument.interfaceId, argument.document, argument.query))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro argument; cases argument; rfl)

/-- Stable marker: `LOOM/HDOC/QUERYARG`, query wire version 1. -/
def queryWireFrame : List UInt8 :=
  [76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 81, 85, 69, 82, 89, 65, 82, 71,
    1]

def decodeQueryArgument : List UInt8 → Option QueryArgument
  | 76 :: 79 :: 79 :: 77 :: 47 :: 72 :: 68 :: 79 :: 67 :: 47 :: 81 :: 85 ::
      69 :: 82 :: 89 :: 65 :: 82 :: 71 :: 1 :: payload =>
      queryArgumentStream.toLawful.decode payload
  | _ => none

def queryArgumentCodec : LawfulCodec QueryArgument where
  encode argument := queryWireFrame ++ queryArgumentStream.encode argument
  decode := decodeQueryArgument
  decode_encode := by
    intro argument
    change queryArgumentStream.toLawful.decode
      (queryArgumentStream.encode argument) = some argument
    exact queryArgumentStream.toLawful.decode_encode argument

@[simp] theorem reject_query_wire_version_two (payload : List UInt8) :
    decodeQueryArgument
      ([76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 81, 85, 69, 82, 89, 65,
        82, 71, 2] ++ payload) = none := by
  simp [decodeQueryArgument]

def queryDigestCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 72, 68, 79, 67, 46, 81, 85, 69, 82, 89, 46, 65, 82,
    71, 85, 77, 69, 78, 84, 47, 118, 49]

def queryDigest (bytes : List UInt8) : Digest :=
  (Minidregg.Compiler.Sp800185Cshake256.hash
    queryDigestCustomization bytes).digest

def queryConfig : QueryConfig where
  argumentCodec := queryArgumentCodec
  digestBytes := queryDigest
  requestDomain := ⟨90001⟩
  semanticRelation := ⟨90002⟩
  noEffectDigest := ⟨90003⟩

@[simp] theorem query_argument_roundtrip (argument : QueryArgument) :
    queryConfig.argumentCodec.decode
      (queryConfig.argumentCodec.encode argument) = some argument :=
  queryConfig.decode_encode_argument argument

@[simp] theorem argument_digest_exact (argument : QueryArgument) :
    queryConfig.argumentDigest argument =
      (Minidregg.Compiler.Sp800185Cshake256.hash queryDigestCustomization
        (queryWireFrame ++ queryArgumentStream.encode argument)).digest :=
  rfl

/-! ## Current authorization shared by both positive reads -/

abbrev portal :=
  Minidregg.Theory.TypedAuthorizationWitness.permissivePortal

def authState : AuthState where
  capabilityRoot := ⟨91001⟩
  revocationRoot := ⟨91002⟩
  policyRoot := ⟨91003⟩
  policyAddress := fun _ _ => ⟨0⟩
  revoked := ∅
  issuerEpoch := fun _ => 0
  policyEpoch := fun _ => 0
  subjectKeyEpoch := fun _ => 0

def issuer : IssuerId := ⟨91004⟩
def subject : SubjectId := ⟨91005⟩
def federation : FederationId := ⟨91006⟩
def policyId : PolicyId := ⟨91007⟩

/-! ## Exact bounded content-page link read -/

namespace Content

def boundedLink : ContentPage.ForwardLink where
  sourceDocument := Publication.documentId
  source := none
  target := .external [0x68, 0x74, 0x74, 0x70, 0x73] [0x65, 0x78]
    [0x2f, 0x6c, 0x6f, 0x6f, 0x6d]
  relation := ⟨24⟩
  author := Publication.author
  operation := Publication.linkDeclaration.operationId
    Publication.operationConfig
  tombstonedAt := none

@[simp] theorem boundedLink_canonical_exact :
    boundedLink.toCanonical = Reopen.record :=
  rfl

def page : ContentPage.Page where
  contentDomain := ⟨92001⟩
  document := Publication.documentId
  pageNumber := 0
  slot0 := some (.link Publication.linkId boundedLink)
  slot1 := none
  slot2 := none
  slot3 := none

theorem page_valid : page.Valid := by
  constructor
  · simp [page,
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page.addresses,
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page.entries,
      _root_.id,
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.Entry.address]
  · simp [page,
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page.entries,
      _root_.id,
      Minidregg.Compiler.HyperdocumentContentPageMaterializer.Entry.LocalTo,
      boundedLink]

def pageCell : Materialized ContentPage.materializer :=
  CellState.materialize ContentPage.materializer
    (ContentPage.stateOfOption (some page))

def pre : Hyperdocument.Cell Publication.documentMaterializer :=
  CellState.materialize Publication.documentMaterializer
    page.toCanonicalState

@[simp] theorem bounded_query_exact :
    ContentQuery.project Reopen.query pre.logical = some Reopen.record := by
  simp [pre, Reopen.query, ContentQuery.project, Hyperdocument.lookup,
    page,
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page.toCanonicalState,
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page.entries,
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.Entry.install,
    boundedLink, _root_.id]
  rfl

def argument : QueryArgument where
  interfaceId := contentReadV1
  document := Publication.documentId
  query := .content Reopen.query

def envelope : QueryEnvelope where
  federation := federation
  subject := subject
  subjectKeyEpoch := 0
  nonce := 892010
  height := 10
  expectedPreRoot := pre.root
  policyId := policyId
  policyEpoch := 0
  cost := 1

def declaration : QueryDeclaration := ⟨argument, envelope⟩

def request : Request .object := declaration.toRequest queryConfig

def capability : Capability .object where
  id := ⟨92011⟩
  root := ⟨92011⟩
  parent := none
  issuer := issuer
  holder := .subject subject
  scope :=
    { targets := {request.target}
      verbs := {.observeObject}
      maxCost := 1 }
  notBefore := 0
  notAfter := 100
  issuerEpoch := 0
  policyId := policyId
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

theorem capability_admissible : capability.Admissible authState request where
  holder := rfl
  scope :=
    { target := by simp [capability]
      verb := by simp [capability, request, declaration,
        QueryDeclaration.toRequest]
      cost := by simp [capability, request, declaration,
        QueryDeclaration.toRequest, envelope] }
  validFrom := by decide
  validUntil := by decide
  policyId := rfl
  policyEpoch := rfl
  policyCurrent := rfl
  issuerCurrent := rfl
  selfNotRevoked := by simp [authState]
  ancestorNotRevoked := by
    intro ancestor member
    simp [capability] at member
  channelNotRevoked := by
    intro channel member
    simp [capability] at member

def evidence : Evidence portal authState request :=
  .capability capability ⟨92012⟩ () () () () capability_admissible
    rfl rfl rfl rfl
    (by intro ancestor member; simp [capability] at member)
    (by intro channel member; simp [capability] at member)

def authorization : Authorized portal authState request where
  evidence := evidence
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def success : QuerySuccess queryConfig portal authState pre declaration request
    capability where
  requestExact := rfl
  interfaceExact := rfl
  queryWellFormed := trivial
  authorization := authorization
  capabilityAdmissible := capability_admissible
  preRootExact := rfl
  contentOwned := by
    change ∀ record,
      Hyperdocument.lookup pre.logical .links Publication.linkId = some record →
        record.sourceDocument = Publication.documentId
    intro record opened
    rw [show Hyperdocument.lookup pre.logical .links Publication.linkId =
        some Reopen.record by simpa [Reopen.query, ContentQuery.project] using
          bounded_query_exact] at opened
    have recordExact : Reopen.record = record := Option.some.inj opened
    subst record
    rfl

inductive Failure where
  | malformedArgument
  | argumentMismatch
  deriving DecidableEq, Repr

/-- The proof-carrying content controller decodes exact bytes and then reads
the deployed bounded page, rather than a host-provided result. -/
def execute (bytes : List UInt8)
    (_authorized : QuerySuccess queryConfig portal authState pre declaration
      request capability) : Except Failure (Option LinkRecord) :=
  match queryConfig.argumentCodec.decode bytes with
  | none => .error .malformedArgument
  | some decoded =>
      if decoded = declaration.argument then
        .ok (ContentQuery.project Reopen.query page.toCanonicalState)
      else
        .error .argumentMismatch

@[simp] theorem execute_honest :
    execute (queryConfig.argumentCodec.encode declaration.argument) success =
      .ok (some Reopen.record) := by
  unfold execute
  rw [query_argument_roundtrip]
  change
    (if declaration.argument = declaration.argument then
      Except.ok (ContentQuery.project Reopen.query page.toCanonicalState)
    else Except.error Failure.argumentMismatch) =
      Except.ok (some Reopen.record)
  rw [if_pos rfl]
  apply congrArg Except.ok
  simpa [pre] using bounded_query_exact

end Content

/-! ## Exact bounded event-page version read -/

namespace History

namespace Deployed

abbrev page :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.examplePage
abbrev entry :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.exampleEntry
abbrev record :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.exampleRecord
abbrev page_valid :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.examplePage_valid
abbrev eventPreimageCodec :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.eventPreimageCodec
abbrev eventDerivation :=
  Minidregg.Compiler.HyperdocumentEventPageMaterializer.eventDerivation

end Deployed

def anchorPage : ContentPage.Page where
  contentDomain := ⟨93001⟩
  document := Deployed.record.document
  pageNumber := 0
  slot0 := none
  slot1 := none
  slot2 := none
  slot3 := none

theorem anchorPage_valid : anchorPage.Valid := by
  constructor <;> simp [anchorPage,
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page.addresses,
    Minidregg.Compiler.HyperdocumentContentPageMaterializer.Page.entries]

def pre : Hyperdocument.Cell Publication.documentMaterializer :=
  CellState.materialize Publication.documentMaterializer
    anchorPage.toCanonicalState

def argument : QueryArgument where
  interfaceId := historyReadV1
  document := Deployed.record.document
  query := .history (.version Deployed.entry.key)

def envelope : QueryEnvelope where
  federation := federation
  subject := subject
  subjectKeyEpoch := 0
  nonce := 893010
  height := 10
  expectedPreRoot := pre.root
  policyId := policyId
  policyEpoch := 0
  cost := 1

def declaration : QueryDeclaration := ⟨argument, envelope⟩
def request : Request .object := declaration.toRequest queryConfig

def capability : Capability .object where
  id := ⟨93011⟩
  root := ⟨93011⟩
  parent := none
  issuer := issuer
  holder := .subject subject
  scope :=
    { targets := {request.target}
      verbs := {.observeObject}
      maxCost := 1 }
  notBefore := 0
  notAfter := 100
  issuerEpoch := 0
  policyId := policyId
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

theorem capability_admissible : capability.Admissible authState request where
  holder := rfl
  scope :=
    { target := by simp [capability]
      verb := by simp [capability, request, declaration,
        QueryDeclaration.toRequest]
      cost := by simp [capability, request, declaration,
        QueryDeclaration.toRequest, envelope] }
  validFrom := by decide
  validUntil := by decide
  policyId := rfl
  policyEpoch := rfl
  policyCurrent := rfl
  issuerCurrent := rfl
  selfNotRevoked := by simp [authState]
  ancestorNotRevoked := by
    intro ancestor member
    simp [capability] at member
  channelNotRevoked := by
    intro channel member
    simp [capability] at member

def evidence : Evidence portal authState request :=
  .capability capability ⟨93012⟩ () () () () capability_admissible
    rfl rfl rfl rfl
    (by intro ancestor member; simp [capability] at member)
    (by intro channel member; simp [capability] at member)

def authorization : Authorized portal authState request where
  evidence := evidence
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def success : QuerySuccess queryConfig portal authState pre declaration request
    capability where
  requestExact := rfl
  interfaceExact := rfl
  queryWellFormed := trivial
  authorization := authorization
  capabilityAdmissible := capability_admissible
  preRootExact := rfl
  contentOwned := trivial

def lookupVersion (id : VersionEventId) : List EventPage.Entry →
    Option VersionEventRecord
  | [] => none
  | entry :: rest =>
      if entry.key = id then some entry.record else lookupVersion id rest

def readPage (page : EventPage.Page) (id : VersionEventId) :
    Option VersionEventRecord :=
  lookupVersion id page.entries

@[simp] theorem deployed_read_exact :
    readPage Deployed.page Deployed.entry.key = some Deployed.record := by
  simp [readPage, lookupVersion, Deployed.page, Deployed.entry,
    Deployed.record,
    Minidregg.Compiler.HyperdocumentEventPageMaterializer.examplePage,
    Minidregg.Compiler.HyperdocumentEventPageMaterializer.exampleEntry,
    Minidregg.Compiler.HyperdocumentEventPageMaterializer.Page.entries,
    _root_.id]

theorem deployed_record_wellFormed : Deployed.record.CausallyWellFormed := by
  have valid := Deployed.page_valid.entriesValid Deployed.entry (by
    simp [Deployed.entry,
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.examplePage,
      Minidregg.Compiler.HyperdocumentEventPageMaterializer.Page.entries])
  exact valid.2.2.1

def stored : StoredVersionEvent EventPage.eventScheme :=
  StoredVersionEvent.derive Deployed.eventPreimageCodec
    Deployed.eventDerivation Deployed.record deployed_record_wellFormed

def projection : VersionProjection EventPage.eventScheme
    Deployed.record.document Deployed.entry.key where
  stored := stored
  keyExact := rfl
  documentExact := rfl

inductive Failure where
  | malformedArgument
  | argumentMismatch
  deriving DecidableEq, Repr

/-- The authorized history controller returns the value found in the exact
bounded event page.  The retained `VersionProjection` proves causal addressing,
not authoritative-history membership or external finality. -/
def execute (bytes : List UInt8)
    (_authorized : QuerySuccess queryConfig portal authState pre declaration
      request capability) : Except Failure (Option VersionEventRecord) :=
  match queryConfig.argumentCodec.decode bytes with
  | none => .error .malformedArgument
  | some decoded =>
      if decoded = declaration.argument then
        .ok (readPage Deployed.page Deployed.entry.key)
      else
        .error .argumentMismatch

@[simp] theorem execute_honest :
    execute (queryConfig.argumentCodec.encode declaration.argument) success =
      .ok (some Deployed.record) := by
  unfold execute
  rw [query_argument_roundtrip]
  change
    (if declaration.argument = declaration.argument then
      Except.ok (readPage Deployed.page Deployed.entry.key)
    else Except.error Failure.argumentMismatch) =
      Except.ok (some Deployed.record)
  rw [if_pos rfl]
  exact congrArg Except.ok deployed_read_exact

end History

/-! ## Concrete rejection teeth -/

namespace Teeth

def wrongInterfaceDeclaration : QueryDeclaration :=
  { Content.declaration with
    argument := { Content.argument with interfaceId := contentMutationV1 } }

def wrongInterfaceRequest : Request .object :=
  wrongInterfaceDeclaration.toRequest queryConfig

theorem wrong_interface_rejected :
    IsEmpty (QuerySuccess queryConfig portal authState Content.pre
      wrongInterfaceDeclaration wrongInterfaceRequest Content.capability) := by
  apply no_query_success_wrong_interface
  decide

def reservedVersionDeclaration : QueryDeclaration :=
  { Content.declaration with
    argument :=
      { Content.argument with
        interfaceId := ⟨.contentRead, .reservedV2⟩ } }

def reservedVersionRequest : Request .object :=
  reservedVersionDeclaration.toRequest queryConfig

theorem reserved_version_rejected :
    IsEmpty (QuerySuccess queryConfig portal authState Content.pre
      reservedVersionDeclaration reservedVersionRequest Content.capability) := by
  apply no_query_success_reserved_version
  rfl

def offScopeCapability : Capability .object :=
  { Content.capability with
    scope := { Content.capability.scope with targets := ∅ } }

theorem outside_scope_rejected :
    IsEmpty (QuerySuccess queryConfig portal authState Content.pre
      Content.declaration Content.request offScopeCapability) := by
  apply no_query_success_outside_scope
  simp [offScopeCapability]

def wrongTarget : ResourceId .object :=
  ⟨Content.request.target.value + 1⟩

def wrongTargetRequest : Request .object :=
  { Content.request with target := wrongTarget }

theorem wrong_target_ne : wrongTarget ≠ Content.request.target := by
  intro equal
  have values := congrArg (fun target : ResourceId .object => target.value) equal
  simp [wrongTarget] at values

theorem wrong_target_rejected :
    IsEmpty (QuerySuccess queryConfig portal authState Content.pre
      Content.declaration wrongTargetRequest Content.capability) := by
  apply no_query_success_wrong_target
  simpa [wrongTargetRequest] using wrong_target_ne

def staleRoot : Digest := ⟨Content.pre.root.value + 1⟩

def staleRootRequest : Request .object :=
  { Content.request with preStateRoot := staleRoot }

theorem stale_root_ne : staleRoot ≠ Content.pre.root := by
  intro equal
  have values := congrArg Digest.value equal
  simp [staleRoot] at values

theorem no_query_success_stale_root
    {M : Hyperdocument.Materializer Digest}
    {config : QueryConfig} {selectedPortal : Portal}
    {selectedAuthState : AuthState} {pre : Hyperdocument.Cell M}
    {declaration : QueryDeclaration} {request : Request .object}
    {capability : Capability .object}
    (stale : request.preStateRoot ≠ pre.root) :
    IsEmpty (QuerySuccess config selectedPortal selectedAuthState pre
      declaration request capability) :=
  ⟨fun success => stale success.preRootExact⟩

theorem stale_root_rejected :
    IsEmpty (QuerySuccess queryConfig portal authState Content.pre
      Content.declaration staleRootRequest Content.capability) := by
  apply no_query_success_stale_root
  simpa [staleRootRequest] using stale_root_ne

end Teeth

/-! ## Explicit deployment ceilings -/

/-- Additional evidence required before these pure, proof-carrying page reads
may be described as cryptographically authenticated, authoritative, final, and
physically available.  No constructor is supplied here.

The pair-scoped binding fields avoid the impossible claim that a finite digest
is globally injective.  `historyMember` and `externallyFinal` are independent:
a locally valid, content-addressed event page establishes neither. -/
structure DeploymentEvidence
    (reopenedContent : LogicalState ContentPage.schema)
    (reopenedHistory : LogicalState EventPage.schema)
    (AuthoritativeHistoryMember : VersionEventId → VersionEventRecord → Prop)
    (ExternallyFinal : VersionEventId → Prop)
    (PhysicallyAvailable : Digest → Prop)
    (AuthorizationVerifierSound : Prop) : Prop where
  contentRootObserved :
    ContentPage.materializer.rootBytes
        (ContentPage.materializer.codec.encode Content.pageCell.logical) =
      ContentPage.materializer.rootBytes
        (ContentPage.materializer.codec.encode reopenedContent)
  contentPairBinding :
    ContentPage.PairBindingPremise Content.pageCell.logical reopenedContent
  historyRootObserved :
    EventPage.materializer.rootBytes
        (EventPage.materializer.codec.encode
          (EventPage.stateOfOption (some History.Deployed.page))) =
      EventPage.materializer.rootBytes
        (EventPage.materializer.codec.encode reopenedHistory)
  historyPairBinding :
    EventPage.PairBindingPremise
      (EventPage.stateOfOption (some History.Deployed.page)) reopenedHistory
  historyMember :
    AuthoritativeHistoryMember History.Deployed.entry.key
      History.Deployed.record
  externallyFinal : ExternallyFinal History.Deployed.entry.key
  contentPhysicallyAvailable : PhysicallyAvailable Content.pageCell.root
  historyPhysicallyAvailable :
    PhysicallyAvailable
      (CellState.materialize EventPage.materializer
        (EventPage.stateOfOption (some History.Deployed.page))).root
  authorizationVerifierSound : AuthorizationVerifierSound

/-! ## Axiom pins -/

/-- info: 'Minidregg.Assurance.HyperdocumentQueryDeployment.queryArgumentCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms queryArgumentCodec
/-- info: 'Minidregg.Assurance.HyperdocumentQueryDeployment.Content.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Content.success
/-- info: 'Minidregg.Assurance.HyperdocumentQueryDeployment.History.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms History.success
/-- info: 'Minidregg.Assurance.HyperdocumentQueryDeployment.Teeth.stale_root_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.stale_root_rejected

end

end Minidregg.Assurance.HyperdocumentQueryDeployment
