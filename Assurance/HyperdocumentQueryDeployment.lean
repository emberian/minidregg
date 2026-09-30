/-
# Assurance.HyperdocumentQueryDeployment -- authorized reads of the deployed cells

`Theory.HyperdocumentInterface` deliberately leaves `QueryConfig` abstract and
does not construct a `QuerySuccess`.  This module closes that carrier with a
stable v1 query-argument frame, lawful codecs for every query constructor, and
Lean cSHAKE256 addressing of the exact framed argument bytes.

The positive content pole reads the exact link reopened by
`HyperdocumentLinkReopenWitness` from a deployed content store cell
(`HyperdocumentCell.contentMaterializer`).  The positive history pole reads the
accepted link's causally well-formed version event, keyed by the deployed cSHAKE
event scheme, from a deployed event-log cell.  Both retain one current
request-indexed authorization and the same semantically admissible capability.

The history cell proves causal identity of the event it holds.  It does not
prove that the cell is an authoritative history, that the selected event is
externally final, that cSHAKE is collision resistant, or that an OS can
physically reopen either cell.  Those ceilings remain explicit at the end of the
module.
-/
import Assurance.HyperdocumentLinkReopenWitness
import Compiler.HyperdocumentCell
import Compiler.Sp800185Cshake256

namespace Minidregg.Assurance.HyperdocumentQueryDeployment

open Minidregg.Compiler
open Minidregg.Kernel
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

/-- The root-collision premise for one pair of stores under one materializer. -/
def PairBindingPremise {L : Store.Layout.{0, 0, 0}} (M : CellState.Materializer L Digest)
    (left right : Store.Store L) : Prop :=
  M.rootOf left = M.rootOf right → left = right

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
  -- Both positive reads select the initial revision of this closed authority fixture.
  policyRevision := fun _ => 0
  subjectKeyEpoch := fun _ => 0
  parent := fun _ => none

def issuer : IssuerId := ⟨91004⟩
def subject : SubjectId := ⟨91005⟩
def federation : FederationId := ⟨91006⟩
def policyId : PolicyId := ⟨91007⟩

/-! ## Exact content-cell link read -/

namespace Content

abbrev ContentStore := Store.Store Hyperdocument.layout

/-- The deployed content cell holding exactly the reopened link. -/
def store : ContentStore :=
  (0 : ContentStore).set ⟨.links, Publication.linkId⟩ (some Reopen.record)

def cell : Materialized HyperdocumentCell.contentMaterializer :=
  CellState.materialize HyperdocumentCell.contentMaterializer store

def pre : Hyperdocument.Cell Publication.documentMaterializer :=
  CellState.materialize Publication.documentMaterializer store

@[simp] theorem store_query_exact :
    ContentQuery.project Reopen.query store = some Reopen.record := by
  simp only [Minidregg.Assurance.HyperdocumentLinkReopenWitness.query,
    ContentQuery.project, Hyperdocument.lookup, store, Store.Store.set_eq]
  rfl

@[simp] theorem bounded_query_exact :
    ContentQuery.project Reopen.query pre.logical = some Reopen.record :=
  store_query_exact

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
  policyRevision := authState.policyRevision policyId
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
    { targets := .explicit {request.target}
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
    { target := by simp [capability, TargetSet.Covers]
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
  .capability capability ⟨92012⟩ () () () () () capability_admissible
    rfl rfl rfl rfl rfl
    (by intro ancestor member; simp [capability] at member)
    (by intro channel member; simp [capability] at member)

def authorization : Authorized portal authState request where
  evidence := evidence
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyRevisionExact := rfl
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
the deployed content cell, rather than a host-provided result. -/
def execute (bytes : List UInt8)
    (_authorized : QuerySuccess queryConfig portal authState pre declaration
      request capability) : Except Failure (Option LinkRecord) :=
  match queryConfig.argumentCodec.decode bytes with
  | none => .error .malformedArgument
  | some decoded =>
      if decoded = declaration.argument then
        .ok (ContentQuery.project Reopen.query cell.logical)
      else
        .error .argumentMismatch

@[simp] theorem execute_honest :
    execute (queryConfig.argumentCodec.encode declaration.argument) success =
      .ok (some Reopen.record) := by
  unfold execute
  rw [query_argument_roundtrip]
  change
    (if declaration.argument = declaration.argument then
      Except.ok (ContentQuery.project Reopen.query cell.logical)
    else Except.error Failure.argumentMismatch) =
      Except.ok (some Reopen.record)
  rw [if_pos rfl]
  exact congrArg Except.ok store_query_exact

end Content

/-! ## Exact event-log cell version read -/

namespace History

namespace Deployed

/-- The accepted link's version event. -/
noncomputable abbrev record : VersionEventRecord :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.linkAccepted.versionEventRecord

theorem record_wellFormed : record.CausallyWellFormed :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.linkWellFormed

/-- Its deployed cSHAKE key. -/
noncomputable def key : VersionEventId :=
  deriveVersionEventId HyperdocumentCell.eventPreimageStream.toLawful
    HyperdocumentCell.eventDerivation record

/-- The deployed event-log cell holding exactly that event. -/
noncomputable def store : HyperdocumentEventLog.Sparse.Store :=
  (0 : HyperdocumentEventLog.Sparse.Store).set
    (HyperdocumentEventLog.Sparse.eventAddress key) (some record)

noncomputable def cell : Materialized HyperdocumentCell.eventMaterializer :=
  CellState.materialize HyperdocumentCell.eventMaterializer store

end Deployed

def pre : Hyperdocument.Cell Publication.documentMaterializer :=
  CellState.materialize Publication.documentMaterializer 0

def argument : QueryArgument where
  interfaceId := historyReadV1
  document := Deployed.record.document
  query := .history (.version Deployed.key)

def envelope : QueryEnvelope where
  federation := federation
  subject := subject
  subjectKeyEpoch := 0
  nonce := 893010
  height := 10
  expectedPreRoot := pre.root
  policyId := policyId
  policyEpoch := 0
  policyRevision := authState.policyRevision policyId
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
    { targets := .explicit {request.target}
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
    { target := by simp [capability, TargetSet.Covers]
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
  .capability capability ⟨93012⟩ () () () () () capability_admissible
    rfl rfl rfl rfl rfl
    (by intro ancestor member; simp [capability] at member)
    (by intro channel member; simp [capability] at member)

def authorization : Authorized portal authState request where
  evidence := evidence
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyRevisionExact := rfl
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

def readCell (store : HyperdocumentEventLog.Sparse.Store) (id : VersionEventId) :
    Option VersionEventRecord :=
  store (HyperdocumentEventLog.Sparse.eventAddress id)

@[simp] theorem deployed_read_exact :
    readCell Deployed.cell.logical Deployed.key = some Deployed.record :=
  Store.Store.set_eq _ _ _

noncomputable def stored : StoredVersionEvent HyperdocumentCell.eventScheme :=
  StoredVersionEvent.derive HyperdocumentCell.eventPreimageStream.toLawful
    HyperdocumentCell.eventDerivation Deployed.record Deployed.record_wellFormed

noncomputable def projection : VersionProjection HyperdocumentCell.eventScheme
    Deployed.record.document Deployed.key where
  stored := stored
  keyExact := rfl
  documentExact := rfl

inductive Failure where
  | malformedArgument
  | argumentMismatch
  deriving DecidableEq, Repr

/-- The authorized history controller returns the value found in the exact
deployed event-log cell.  The retained `VersionProjection` proves causal
addressing, not authoritative-history membership or external finality. -/
def execute (bytes : List UInt8)
    (_authorized : QuerySuccess queryConfig portal authState pre declaration
      request capability) : Except Failure (Option VersionEventRecord) :=
  match queryConfig.argumentCodec.decode bytes with
  | none => .error .malformedArgument
  | some decoded =>
      if decoded = declaration.argument then
        .ok (readCell Deployed.cell.logical Deployed.key)
      else
        .error .argumentMismatch

@[simp] theorem execute_honest :
    execute (queryConfig.argumentCodec.encode declaration.argument) success =
      .ok (some Deployed.record) := by
  unfold execute
  rw [query_argument_roundtrip]
  change
    (if declaration.argument = declaration.argument then
      Except.ok (readCell Deployed.cell.logical Deployed.key)
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
    scope := { Content.capability.scope with targets := .explicit ∅ } }

theorem outside_scope_rejected :
    IsEmpty (QuerySuccess queryConfig portal authState Content.pre
      Content.declaration Content.request offScopeCapability) := by
  apply no_query_success_outside_scope
  simp [offScopeCapability, TargetSet.Covers]

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

/-- Additional evidence required before these pure, proof-carrying cell reads
may be described as cryptographically authenticated, authoritative, final, and
physically available.  No constructor is supplied here.

The pair-scoped binding fields avoid the impossible claim that a finite digest
is globally injective.  `historyMember` and `externallyFinal` are independent:
a content-addressed event cell establishes neither. -/
structure DeploymentEvidence
    (reopenedContent : Store.Store Hyperdocument.layout)
    (reopenedHistory : HyperdocumentEventLog.Sparse.Store)
    (AuthoritativeHistoryMember : VersionEventId → VersionEventRecord → Prop)
    (ExternallyFinal : VersionEventId → Prop)
    (PhysicallyAvailable : Digest → Prop)
    (AuthorizationVerifierSound : Prop) : Prop where
  contentRootObserved :
    HyperdocumentCell.contentMaterializer.rootOf Content.cell.logical =
      HyperdocumentCell.contentMaterializer.rootOf reopenedContent
  contentPairBinding :
    PairBindingPremise HyperdocumentCell.contentMaterializer Content.cell.logical
      reopenedContent
  historyRootObserved :
    HyperdocumentCell.eventMaterializer.rootOf Minidregg.Assurance.HyperdocumentQueryDeployment.History.Deployed.cell.logical =
      HyperdocumentCell.eventMaterializer.rootOf reopenedHistory
  historyPairBinding :
    PairBindingPremise HyperdocumentCell.eventMaterializer
      Minidregg.Assurance.HyperdocumentQueryDeployment.History.Deployed.cell.logical reopenedHistory
  historyMember :
    AuthoritativeHistoryMember Minidregg.Assurance.HyperdocumentQueryDeployment.History.Deployed.key Minidregg.Assurance.HyperdocumentQueryDeployment.History.Deployed.record
  externallyFinal : ExternallyFinal Minidregg.Assurance.HyperdocumentQueryDeployment.History.Deployed.key
  contentPhysicallyAvailable : PhysicallyAvailable Content.cell.root
  historyPhysicallyAvailable : PhysicallyAvailable Minidregg.Assurance.HyperdocumentQueryDeployment.History.Deployed.cell.root
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
