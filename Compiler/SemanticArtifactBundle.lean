/-
# Compiler.SemanticArtifactBundle -- generated proof-native control artifact

This module packages the Lean-owned semantic manifest together with first-order
projections of the authorization, effect, reactive, and disclosure declarations.
The emitted object contains identifiers, codec pins, declaration data, and a phase
plan only.  It contains no native callback, verifier predicate, executor, challenge,
or acceptance bit.

Authorization is projected from `AuthorizationDeclaration.declaration`.  Semantic
effect data is projected from `Theory.EffectDeclaration.Declaration.toWire/words`.
Reactive declarations export only their closed guard syntax and shape; their keys,
values, and root values
remain bound by the declaration identifier.  A disclosure declaration exports codec
identifiers and its two mandatory check phases, never its executable verifier or
projection functions.

`ArtifactBundle.canonicalEncoding` is a closed first-order value whose decoder is a
left inverse.  The JSON writer consumes that value, following the existing emit/write
pattern.  The injective Goedel address is a mathematical content address, not a
cryptographic hash claim.
-/
import Compiler.SemanticManifest
import Compiler.TranscriptController
import Compiler.DeclaredEffectArtifact
import Theory.DisclosureDeclaration
import Theory.ReactiveController

namespace Minidregg.Compiler.SemanticArtifactBundle

open Lean (Json toJson)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Declaration and phase surfaces -/

inductive DeclarationKind where
  | effect
  | reactive
  | disclosure
deriving DecidableEq, Repr, Encodable

/-- Static declaration phases only.  These are labels for the Lean-owned control
schedule; none is an instruction to trust a native verdict. -/
inductive DeclarationPhase where
  | effectDescriptor
  | reactiveGuard
  | reactiveEffect
  | disclosureSameOpening
  | disclosurePermission
deriving DecidableEq, Repr, Encodable

/-- End-to-end semantic controller plan.  Detailed proof-round ordering remains pinned
by `Manifest.transcriptControllerDigest`; this plan owns the outer semantic order. -/
inductive ControllerPhase where
  | bindManifest
  | decodeAdmission
  | authorization
  | effects
  | reactive
  | disclosure
  | absorbPublic
  | absorbCommitments
  | proofRounds
  | absorbTerminal
  | deriveQueries
  | verifyOpenings
  | verifyDialectClauses
  | bindReceipt
  | commit
deriving DecidableEq, Repr, Encodable

def canonicalControllerPlan : List ControllerPhase :=
  [.bindManifest, .decodeAdmission, .authorization, .effects, .reactive,
   .disclosure, .absorbPublic, .absorbCommitments, .proofRounds,
   .absorbTerminal, .deriveQueries, .verifyOpenings, .verifyDialectClauses,
   .bindReceipt, .commit]

/-- First-order projection of one declaration.  `declarationWords` is declaration data,
not a native program: for effects it is the derived opcode descriptor; for reactive
control it is the closed guard/shape word; for disclosure it is empty because the
declaration's executable functions must not cross this boundary. -/
structure DeclarationArtifact where
  kind : DeclarationKind
  declarationId : Digest
  declarationCodecId : Digest
  schemaVersion : Nat
  inputCodecIds : List Digest
  outputCodecIds : List Digest
  parameterIds : List Digest
  declarationWords : List (List Nat)
  phasePlan : List DeclarationPhase
deriving DecidableEq, Repr

/-- One authorization mode and its exact existing check order. -/
structure AuthorizationModeArtifact where
  modeTag : Nat
  checkTags : List Nat
deriving DecidableEq, Repr, Encodable

/-- First-order projection of the existing authorization declaration. -/
structure AuthorizationArtifact where
  declarationId : Digest
  declarationCodecId : Digest
  requestCodecId : Digest
  schemaVersion : Nat
  requestFieldTags : List Nat
  modes : List AuthorizationModeArtifact
deriving DecidableEq, Repr

def requestFieldTag : Minidregg.Theory.AuthorizationDeclaration.RequestField -> Nat
  | .domain => 1
  | .semantics => 2
  | .federation => 3
  | .resourceKind => 4
  | .subject => 5
  | .subjectKeyEpoch => 6
  | .target => 7
  | .verb => 8
  | .argsDigest => 9
  | .effectsDigest => 10
  | .nonce => 11
  | .height => 12
  | .preStateRoot => 13
  | .policyId => 14
  | .policyEpoch => 15
  | .cost => 16

def authorizationModeTag : Minidregg.Theory.AuthorizationDeclaration.Mode -> Nat
  | .signature => 1
  | .proof => 2
  | .capability => 3

def authorizationCheckTag : Minidregg.Theory.AuthorizationDeclaration.Check -> Nat
  | .subjectKeyEpoch => 1
  | .signature => 2
  | .proof => 3
  | .capabilitySemantic => 4
  | .capabilityCommitment => 5
  | .capabilityMembership => 6
  | .issuer => 7
  | .selfNonRevocation => 8
  | .ancestorNonRevocations => 9
  | .channelNonRevocations => 10
  | .policyEpoch => 11
  | .policy => 12

def authorizationModeArtifact
    (plan : Minidregg.Theory.AuthorizationDeclaration.ModePlan) :
    AuthorizationModeArtifact :=
  ⟨authorizationModeTag plan.mode, plan.checks.map authorizationCheckTag⟩

/-- The authorization artifact is a projection of the one existing declaration. -/
def authorizationArtifact
    (declarationId declarationCodecId requestCodecId : Digest) :
    AuthorizationArtifact :=
  let declaration := Minidregg.Theory.AuthorizationDeclaration.declaration
  { declarationId := declarationId
    declarationCodecId := declarationCodecId
    requestCodecId := requestCodecId
    schemaVersion := declaration.schemaVersion
    requestFieldTags := declaration.requestFields.map requestFieldTag
    modes := declaration.modes.map authorizationModeArtifact }

/-! ## Projections from the existing effect/reactive/disclosure declarations -/

/-- Embed the first-order projection of an authoritative typed effect declaration.
The projection's schema and declaration word are derived from
`Theory.EffectDeclaration.Declaration.toWire/words`; only registry pins remain caller
arguments. -/
def DeclarationArtifact.ofDeclaredEffect
    (effect : DeclaredEffectArtifact.Artifact)
    (declarationId declarationCodecId operationCodecId stateCodecId : Digest)
    (parameterIds : List Digest) : DeclarationArtifact where
  kind := .effect
  declarationId := declarationId
  declarationCodecId := declarationCodecId
  schemaVersion := effect.schemaVersion
  inputCodecIds := [operationCodecId, stateCodecId]
  outputCodecIds := [stateCodecId]
  parameterIds := parameterIds
  declarationWords := [effect.words]
  phasePlan := [.effectDescriptor]

/-- Prefix-free encoding of the closed reactive guard AST. -/
def encodeGuardTerm : Minidregg.Theory.ReactiveController.GuardTerm -> List Nat
  | .allow => [1]
  | .deny => [2]
  | .bytesEq expected =>
      3 :: expected.length :: expected.map UInt8.toNat
  | .lengthLE bound => [4, bound]
  | .and left right =>
      let leftWord := encodeGuardTerm left
      let rightWord := encodeGuardTerm right
      5 :: leftWord.length :: leftWord ++ rightWord
  | .or left right =>
      let leftWord := encodeGuardTerm left
      let rightWord := encodeGuardTerm right
      6 :: leftWord.length :: leftWord ++ rightWord

/-- Project a reactive declaration without exporting its generic key/value/root values.
Those values remain pinned by `declarationId`; the artifact exposes the closed guard and
the finite effect/dependency shape only. -/
def DeclarationArtifact.ofReactive
    {U : Minidregg.Theory.IndexedProgram.FirstOrderUniverse}
    {T : Minidregg.Theory.ReactiveController.Types}
    (declaration : Minidregg.Theory.ReactiveController.Declaration U T)
    (declarationId declarationCodecId requestCodecId proofCodecId receiptCodecId : Digest)
    (schemaVersion : Nat) (parameterIds : List Digest) : DeclarationArtifact where
  kind := .reactive
  declarationId := declarationId
  declarationCodecId := declarationCodecId
  schemaVersion := schemaVersion
  inputCodecIds := [requestCodecId, proofCodecId]
  outputCodecIds := [receiptCodecId]
  parameterIds := parameterIds
  declarationWords :=
    [encodeGuardTerm declaration.guard,
     [declaration.effect.writes.length,
      match declaration.wakeAfter with | none => 0 | some _ => 1]]
  phasePlan := [.reactiveGuard, .reactiveEffect]

/-- Disclosure functions stay inside Lean.  The declaration argument pins this
projection to an actual `DisclosureDeclaration`, while only its declared codec IDs and
mandatory phase order cross the artifact boundary. -/
def DeclarationArtifact.ofDisclosure
    {Observer Policy Recipient Purpose CommitmentArtifact OutputArtifact PrivateOutput
      SourceWitness TargetWitness AuthorizationWitness Release : Type*}
    (declaration : Minidregg.Theory.DisclosureDeclaration Observer Policy Recipient Purpose
      CommitmentArtifact OutputArtifact PrivateOutput SourceWitness TargetWitness
      AuthorizationWitness Release)
    (declarationId declarationCodecId requestCodecId commitmentCodecId
      representationCodecId releaseCodecId proofCodecId : Digest)
    (schemaVersion : Nat) (parameterIds : List Digest) : DeclarationArtifact :=
  let _declarationMarker := declaration
  { kind := .disclosure
    declarationId := declarationId
    declarationCodecId := declarationCodecId
    schemaVersion := schemaVersion
    inputCodecIds :=
      [requestCodecId, commitmentCodecId, representationCodecId, proofCodecId]
    outputCodecIds := [releaseCodecId]
    parameterIds := parameterIds
    declarationWords := []
    phasePlan := [.disclosureSameOpening, .disclosurePermission] }

/-! ## Native ABI catalog carried by the semantic artifact -/

/-- Closed native kernel vocabulary.  A tag selects fallible opaque compute only;
it is neither a semantic relation nor an acceptance predicate. -/
inductive KernelTag where
  | tower256DotProduct
deriving DecidableEq, Repr, Encodable

/-- Closed byte-layout vocabulary used by generated transport glue. -/
inductive ByteCodecShape where
  | tower256PairVectorsU32LE
  | tower256CoordinateLE
deriving DecidableEq, Repr, Encodable

/-- Codec identifiers live in one of two explicit registries.  Manifest codecs
name semantic representations.  Native-ABI codecs name transport-only aggregate
layouts and cannot silently masquerade as manifest codecs. -/
inductive ByteCodecRegistry where
  | semanticManifest
  | nativeAbi
deriving DecidableEq, Repr, Encodable

/-- Exact first-order byte-codec data authenticated by the artifact. -/
structure ByteCodecProfile where
  registry : ByteCodecRegistry
  codecId : Nat
  valueTypeId : Nat
  version : Nat
  shape : ByteCodecShape
deriving DecidableEq, Repr, Encodable

/-- Exact first-order native work data authenticated by the artifact.  The
kernel tag only selects an opaque byte implementation generated outside the
semantic acceptance path. -/
structure WorkProfile where
  workId : Nat
  carrierProfileId : Nat
  requestCodec : ByteCodecProfile
  responseCodec : ByteCodecProfile
  kernel : KernelTag
deriving DecidableEq, Repr, Encodable

/-- Lookup in the artifact-local, transport-only ABI registry. -/
def lookupNativeAbiCodec (registry : List ByteCodecProfile) (codecId : Nat) :
    Option ByteCodecProfile :=
  registry.find? fun codec => decide (codec.codecId = codecId)

/-- One work codec is closed either by an exact manifest codec pin or by an
exact entry in the separate native-ABI registry. -/
def WorkCodecClosed (manifest : SemanticManifest.Manifest)
    (nativeAbiCodecs : List ByteCodecProfile) (codec : ByteCodecProfile) : Prop :=
  match codec.registry with
  | .semanticManifest =>
      manifest.lookupCodec ⟨codec.codecId⟩ = some
        ⟨⟨codec.codecId⟩, ⟨codec.valueTypeId⟩, codec.version⟩
  | .nativeAbi => lookupNativeAbiCodec nativeAbiCodecs codec.codecId = some codec

/-- Structural closure for the native portion of an artifact.  Work identifiers
and native-ABI codec identifiers are unique; native codec IDs are disjoint from
semantic manifest codec IDs; every work carrier and both codec uses resolve
inside this same artifact. -/
structure NativeCatalogWellFormed (manifest : SemanticManifest.Manifest)
    (nativeAbiCodecs : List ByteCodecProfile) (catalog : List WorkProfile) : Prop where
  workIdsUnique : (catalog.map WorkProfile.workId).Nodup
  nativeAbiCodecIdsUnique : (nativeAbiCodecs.map ByteCodecProfile.codecId).Nodup
  nativeAbiEntriesScoped : forall codec, codec ∈ nativeAbiCodecs →
    codec.registry = .nativeAbi
  nativeAbiDisjointManifest : forall codec, codec ∈ nativeAbiCodecs →
    manifest.lookupCodec ⟨codec.codecId⟩ = none
  carriersClosed : forall work, work ∈ catalog →
    ∃ carrier, manifest.lookupCarrier ⟨work.carrierProfileId⟩ = some carrier
  requestCodecsClosed : forall work, work ∈ catalog →
    WorkCodecClosed manifest nativeAbiCodecs work.requestCodec
  responseCodecsClosed : forall work, work ∈ catalog →
    WorkCodecClosed manifest nativeAbiCodecs work.responseCodec

/-! ## Bundle and canonical encoding -/

structure ArtifactBundle where
  manifest : SemanticManifest.Manifest
  nativeAbiCodecs : List ByteCodecProfile
  nativeWorkCatalog : List WorkProfile
  authorization : AuthorizationArtifact
  effects : List DeclarationArtifact
  reactive : DeclarationArtifact
  disclosure : DeclarationArtifact
  phasePlan : List ControllerPhase
deriving DecidableEq, Repr

/-- Constructor which fixes the outer phase order and the actual existing authorization
declaration projection. -/
def ArtifactBundle.ofDeclarations
    (manifest : SemanticManifest.Manifest)
    (nativeAbiCodecs : List ByteCodecProfile)
    (nativeWorkCatalog : List WorkProfile)
    (authorizationDeclarationId authorizationDeclarationCodecId
      authorizationRequestCodecId : Digest)
    (effects : List DeclarationArtifact)
    (reactive disclosure : DeclarationArtifact) : ArtifactBundle where
  manifest := manifest
  nativeAbiCodecs := nativeAbiCodecs
  nativeWorkCatalog := nativeWorkCatalog
  authorization := authorizationArtifact authorizationDeclarationId
    authorizationDeclarationCodecId authorizationRequestCodecId
  effects := effects
  reactive := reactive
  disclosure := disclosure
  phasePlan := canonicalControllerPlan

structure AuthorizationArtifactEncoding where
  declarationId : Nat
  declarationCodecId : Nat
  requestCodecId : Nat
  schemaVersion : Nat
  requestFieldTags : List Nat
  modes : List AuthorizationModeArtifact
deriving DecidableEq, Repr, Encodable

def AuthorizationArtifact.canonicalEncoding
    (artifact : AuthorizationArtifact) : AuthorizationArtifactEncoding :=
  ⟨artifact.declarationId.value, artifact.declarationCodecId.value,
    artifact.requestCodecId.value, artifact.schemaVersion,
    artifact.requestFieldTags, artifact.modes⟩

def AuthorizationArtifactEncoding.decode
    (wire : AuthorizationArtifactEncoding) : AuthorizationArtifact :=
  ⟨⟨wire.declarationId⟩, ⟨wire.declarationCodecId⟩, ⟨wire.requestCodecId⟩,
    wire.schemaVersion, wire.requestFieldTags, wire.modes⟩

@[simp] theorem AuthorizationArtifactEncoding.decode_canonicalEncoding
    (artifact : AuthorizationArtifact) : artifact.canonicalEncoding.decode = artifact := by
  cases artifact <;> rfl

structure DeclarationArtifactEncoding where
  kind : DeclarationKind
  declarationId : Nat
  declarationCodecId : Nat
  schemaVersion : Nat
  inputCodecIds : List Nat
  outputCodecIds : List Nat
  parameterIds : List Nat
  declarationWords : List (List Nat)
  phasePlan : List DeclarationPhase
deriving DecidableEq, Repr, Encodable

def DeclarationArtifact.canonicalEncoding
    (artifact : DeclarationArtifact) : DeclarationArtifactEncoding :=
  ⟨artifact.kind, artifact.declarationId.value, artifact.declarationCodecId.value,
    artifact.schemaVersion, artifact.inputCodecIds.map Digest.value,
    artifact.outputCodecIds.map Digest.value, artifact.parameterIds.map Digest.value,
    artifact.declarationWords, artifact.phasePlan⟩

def DeclarationArtifactEncoding.decode
    (wire : DeclarationArtifactEncoding) : DeclarationArtifact :=
  ⟨wire.kind, ⟨wire.declarationId⟩, ⟨wire.declarationCodecId⟩,
    wire.schemaVersion, wire.inputCodecIds.map Digest.mk,
    wire.outputCodecIds.map Digest.mk, wire.parameterIds.map Digest.mk,
    wire.declarationWords, wire.phasePlan⟩

@[simp] theorem DeclarationArtifactEncoding.decode_canonicalEncoding
    (artifact : DeclarationArtifact) : artifact.canonicalEncoding.decode = artifact := by
  cases artifact
  simp [DeclarationArtifact.canonicalEncoding, DeclarationArtifactEncoding.decode,
    Function.comp_def]

structure ArtifactBundleEncoding where
  manifest : SemanticManifest.ManifestEncoding
  nativeAbiCodecs : List ByteCodecProfile
  nativeWorkCatalog : List WorkProfile
  authorization : AuthorizationArtifactEncoding
  effects : List DeclarationArtifactEncoding
  reactive : DeclarationArtifactEncoding
  disclosure : DeclarationArtifactEncoding
  phasePlan : List ControllerPhase
deriving DecidableEq, Repr, Encodable

def ArtifactBundle.canonicalEncoding (bundle : ArtifactBundle) : ArtifactBundleEncoding where
  manifest := bundle.manifest.canonicalEncoding
  nativeAbiCodecs := bundle.nativeAbiCodecs
  nativeWorkCatalog := bundle.nativeWorkCatalog
  authorization := bundle.authorization.canonicalEncoding
  effects := bundle.effects.map DeclarationArtifact.canonicalEncoding
  reactive := bundle.reactive.canonicalEncoding
  disclosure := bundle.disclosure.canonicalEncoding
  phasePlan := bundle.phasePlan

def ArtifactBundleEncoding.decode (wire : ArtifactBundleEncoding) : ArtifactBundle where
  manifest := wire.manifest.decode
  nativeAbiCodecs := wire.nativeAbiCodecs
  nativeWorkCatalog := wire.nativeWorkCatalog
  authorization := wire.authorization.decode
  effects := wire.effects.map DeclarationArtifactEncoding.decode
  reactive := wire.reactive.decode
  disclosure := wire.disclosure.decode
  phasePlan := wire.phasePlan

@[simp] theorem ArtifactBundleEncoding.decode_canonicalEncoding
    (bundle : ArtifactBundle) : bundle.canonicalEncoding.decode = bundle := by
  cases bundle
  simp [ArtifactBundle.canonicalEncoding, ArtifactBundleEncoding.decode,
    Function.comp_def]

theorem ArtifactBundle.canonicalEncoding_injective :
    Function.Injective ArtifactBundle.canonicalEncoding := by
  intro left right h
  have := congrArg ArtifactBundleEncoding.decode h
  simpa using this

def ArtifactBundle.contentAddress (bundle : ArtifactBundle) : Digest :=
  ⟨Encodable.encode bundle.canonicalEncoding⟩

theorem ArtifactBundle.contentAddress_injective :
    Function.Injective ArtifactBundle.contentAddress := by
  intro left right h
  apply ArtifactBundle.canonicalEncoding_injective
  apply Encodable.encode_injective
  exact congrArg Digest.value h

/-! ## JSON/text projection -/

def natArray (values : List Nat) : Json :=
  Json.arr (values.map toJson).toArray

def natRows (rows : List (List Nat)) : Json :=
  Json.arr (rows.map natArray).toArray

def codecPinToJson (codec : SemanticManifest.CodecPinEncoding) : Json :=
  Json.mkObj
    [("codecId", toJson codec.codecId),
     ("valueTypeId", toJson codec.valueTypeId),
     ("version", toJson codec.version)]

def carrierToJson : SemanticManifest.CarrierProfileEncoding -> Json
  | .gf2Tower profile tower basis representation degree =>
      Json.mkObj
        [("kind", Json.str "gf2_tower"), ("profileId", toJson profile),
         ("towerId", toJson tower), ("basisId", toJson basis),
         ("representationId", toJson representation), ("degree", toJson degree)]
  | .ext6 profile modulus polynomial representation =>
      Json.mkObj
        [("kind", Json.str "ext6"), ("profileId", toJson profile),
         ("baseModulus", toJson modulus), ("definingPolynomialId", toJson polynomial),
         ("representationId", toJson representation)]
  | .residueRing profile degree plaintext moduli coefficientRep nttRep =>
      Json.mkObj
        [("kind", Json.str "residue_ring"), ("profileId", toJson profile),
         ("degree", toJson degree), ("plaintextModulus", toJson plaintext),
         ("orderedModuli", natArray moduli),
         ("coefficientRepresentationId", toJson coefficientRep),
         ("nttRepresentationId", toJson nttRep)]
  | .mpcShared profile base protocol federation parties threshold authentication =>
      Json.mkObj
        [("kind", Json.str "mpc_shared"), ("profileId", toJson profile),
         ("baseCarrierProfileId", toJson base), ("protocolId", toJson protocol),
         ("federationId", toJson federation), ("partyCount", toJson parties),
         ("threshold", toJson threshold),
         ("transcriptAuthenticationId", toJson authentication)]

def bridgeToJson (bridge : SemanticManifest.NamedBridgeEncoding) : Json :=
  Json.mkObj
    [("bridgeId", toJson bridge.bridgeId), ("relationId", toJson bridge.relationId),
     ("sourceCarrierId", toJson bridge.sourceCarrierId),
     ("targetCarrierId", toJson bridge.targetCarrierId),
     ("sourceCodecId", toJson bridge.sourceCodecId),
     ("targetCodecId", toJson bridge.targetCodecId)]

def dialectClauseToJson (clause : SemanticManifest.DialectClauseEncoding) : Json :=
  Json.mkObj
    [("clauseId", toJson clause.clauseId), ("relationId", toJson clause.relationId),
     ("carrierProfileId", toJson clause.carrierProfileId),
     ("statementCodecId", toJson clause.statementCodecId),
     ("proofCodecId", toJson clause.proofCodecId),
     ("proofSuiteId", toJson clause.proofSuiteId),
     ("verifierControllerDigest", toJson clause.verifierControllerDigest),
     ("requiredBridgeIds", natArray clause.requiredBridgeIds)]

def namedValueToJson (name : String) (id value : Nat) : Json :=
  Json.mkObj [(name, toJson id), ("value", toJson value)]

def manifestToJson (manifest : SemanticManifest.ManifestEncoding) : Json :=
  Json.mkObj
    [("manifestVersion", toJson manifest.manifestVersion),
     ("abiId", toJson manifest.abiId),
     ("semanticProgramId", toJson manifest.semanticProgramId),
     ("semanticRelationId", toJson manifest.semanticRelationId),
     ("receiptCodecId", toJson manifest.receiptCodecId),
     ("codecs", Json.arr (manifest.codecs.map codecPinToJson).toArray),
     ("carriers", Json.arr (manifest.carriers.map carrierToJson).toArray),
     ("bridges", Json.arr (manifest.bridges.map bridgeToJson).toArray),
     ("dialectClauses", Json.arr (manifest.dialectClauses.map dialectClauseToJson).toArray),
     ("transcriptControllerDigest", toJson manifest.transcriptControllerDigest),
     ("dimensions", Json.arr (manifest.dimensions.map fun pin =>
        namedValueToJson "dimensionId" pin.dimensionId pin.value).toArray),
     ("bounds", Json.arr (manifest.bounds.map fun pin =>
        namedValueToJson "boundId" pin.boundId pin.maximum).toArray)]

def authorizationModeToJson (mode : AuthorizationModeArtifact) : Json :=
  Json.mkObj [("modeTag", toJson mode.modeTag), ("checkTags", natArray mode.checkTags)]

def authorizationToJson (artifact : AuthorizationArtifactEncoding) : Json :=
  Json.mkObj
    [("declarationId", toJson artifact.declarationId),
     ("declarationCodecId", toJson artifact.declarationCodecId),
     ("requestCodecId", toJson artifact.requestCodecId),
     ("schemaVersion", toJson artifact.schemaVersion),
     ("requestFieldTags", natArray artifact.requestFieldTags),
     ("modes", Json.arr (artifact.modes.map authorizationModeToJson).toArray)]

def DeclarationKind.name : DeclarationKind -> String
  | .effect => "effect"
  | .reactive => "reactive"
  | .disclosure => "disclosure"

def DeclarationPhase.name : DeclarationPhase -> String
  | .effectDescriptor => "effect_descriptor"
  | .reactiveGuard => "reactive_guard"
  | .reactiveEffect => "reactive_effect"
  | .disclosureSameOpening => "disclosure_same_opening"
  | .disclosurePermission => "disclosure_permission"

def ControllerPhase.name : ControllerPhase -> String
  | .bindManifest => "bind_manifest"
  | .decodeAdmission => "decode_admission"
  | .authorization => "authorization"
  | .effects => "effects"
  | .reactive => "reactive"
  | .disclosure => "disclosure"
  | .absorbPublic => "absorb_public"
  | .absorbCommitments => "absorb_commitments"
  | .proofRounds => "proof_rounds"
  | .absorbTerminal => "absorb_terminal"
  | .deriveQueries => "derive_queries"
  | .verifyOpenings => "verify_openings"
  | .verifyDialectClauses => "verify_dialect_clauses"
  | .bindReceipt => "bind_receipt"
  | .commit => "commit"

def KernelTag.name : KernelTag -> String
  | .tower256DotProduct => "tower256_dot_product"

def ByteCodecShape.name : ByteCodecShape -> String
  | .tower256PairVectorsU32LE => "tower256_pair_vectors_u32_le"
  | .tower256CoordinateLE => "tower256_coordinate_le"

def ByteCodecRegistry.name : ByteCodecRegistry -> String
  | .semanticManifest => "semantic_manifest"
  | .nativeAbi => "native_abi"

def byteCodecProfileToJson (codec : ByteCodecProfile) : Json :=
  Json.mkObj
    [("registry", Json.str codec.registry.name),
     ("codecId", toJson codec.codecId),
     ("valueTypeId", toJson codec.valueTypeId),
     ("version", toJson codec.version),
     ("shape", Json.str codec.shape.name)]

def workProfileToJson (work : WorkProfile) : Json :=
  Json.mkObj
    [("workId", toJson work.workId),
     ("carrierProfileId", toJson work.carrierProfileId),
     ("requestCodec", byteCodecProfileToJson work.requestCodec),
     ("responseCodec", byteCodecProfileToJson work.responseCodec),
     ("kernelTag", Json.str work.kernel.name)]

def declarationToJson (artifact : DeclarationArtifactEncoding) : Json :=
  Json.mkObj
    [("kind", Json.str artifact.kind.name),
     ("declarationId", toJson artifact.declarationId),
     ("declarationCodecId", toJson artifact.declarationCodecId),
     ("schemaVersion", toJson artifact.schemaVersion),
     ("inputCodecIds", natArray artifact.inputCodecIds),
     ("outputCodecIds", natArray artifact.outputCodecIds),
     ("parameterIds", natArray artifact.parameterIds),
     ("declarationWords", natRows artifact.declarationWords),
     ("phasePlan", Json.arr
       (artifact.phasePlan.map fun phase => Json.str phase.name).toArray)]

/-- Complete bounded JSON projection of the exact canonical encoding.  Both the
standalone JSON writer and generated Rust consume this definition, preventing a
generator-local native catalog from escaping the artifact identity. -/
def canonicalPayloadToJson (wire : ArtifactBundleEncoding) : Json :=
  Json.mkObj
    [("schema", Json.str "minidregg/semantic-artifact-bundle/v1"),
     ("canonicalEncoding", Json.str "minidregg/encodable/v1"),
     ("manifest", manifestToJson wire.manifest),
     ("nativeAbiCodecs", Json.arr
       (wire.nativeAbiCodecs.map byteCodecProfileToJson).toArray),
     ("nativeWorkCatalog", Json.arr
       (wire.nativeWorkCatalog.map workProfileToJson).toArray),
     ("authorization", authorizationToJson wire.authorization),
     ("effects", Json.arr (wire.effects.map declarationToJson).toArray),
     ("reactive", declarationToJson wire.reactive),
     ("disclosure", declarationToJson wire.disclosure),
     ("phasePlan", Json.arr
       (wire.phasePlan.map fun phase => Json.str phase.name).toArray)]

theorem canonicalPayloadToJson_deterministic {left right : ArtifactBundleEncoding}
    (same : left = right) : canonicalPayloadToJson left = canonicalPayloadToJson right := by
  exact congrArg canonicalPayloadToJson same

def artifactBundleToJson (bundle : ArtifactBundle) : Json :=
  let wire := bundle.canonicalEncoding
  Json.mkObj
    [("schema", Json.str "minidregg/semantic-artifact-bundle/v1"),
     ("contentAddress", toJson bundle.contentAddress.value),
     ("manifest", manifestToJson wire.manifest),
     ("nativeAbiCodecs", Json.arr
       (wire.nativeAbiCodecs.map byteCodecProfileToJson).toArray),
     ("nativeWorkCatalog", Json.arr
       (wire.nativeWorkCatalog.map workProfileToJson).toArray),
     ("authorization", authorizationToJson wire.authorization),
     ("effects", Json.arr (wire.effects.map declarationToJson).toArray),
     ("reactive", declarationToJson wire.reactive),
     ("disclosure", declarationToJson wire.disclosure),
     ("phasePlan", Json.arr
       (wire.phasePlan.map fun phase => Json.str phase.name).toArray)]

def artifactBundleText (bundle : ArtifactBundle) : String :=
  (artifactBundleToJson bundle).pretty ++ "\n"

/-- Lean-owned writer; the caller selects the deployment path and declaration bundle. -/
def writeArtifactBundleJson (path : System.FilePath) (bundle : ArtifactBundle) : IO Unit := do
  if let some directory := path.parent then IO.FS.createDirAll directory
  IO.FS.writeFile path (artifactBundleText bundle)

/-- Reusable build target in the same style as the existing emitted descriptor writers. -/
structure BuildTarget where
  path : System.FilePath
  bundle : ArtifactBundle

def BuildTarget.run (target : BuildTarget) : IO Unit :=
  writeArtifactBundleJson target.path target.bundle

end Minidregg.Compiler.SemanticArtifactBundle
