/-
# Compiler.SemanticManifest -- content-addressed proof-native ABI declaration

This module is the first-order control manifest shared by every receipt proof dialect.
It deliberately contains no executor, verifier callback, field coercion, or generic
cross-carrier cast.  A carrier profile only pins representation parameters.  Movement
between profiles is permitted only by naming a manifest-registered bridge relation.

`Manifest.canonicalEncoding` removes the remaining `Digest` wrappers and produces a
closed first-order value.  Its decoder is a left inverse, hence the encoding and the
mathematical content address are injective.  The content address is an injective Goedel
address of the canonical value, not a claim of cryptographic collision resistance; a
deployment hash suite may hash the same value while retaining the theorem below as its
pre-hash canonicality boundary.

`AdmissionContext` binds the complete request and every root needed before a semantic
turn can be admitted.  Its well-formedness predicate closes dialect clause roots against
the manifest registry and enforces the genesis/history and rejected-turn atomicity
conditions.  The request itself reuses `AuthorizationDeclaration`'s kind-restoring
codec, rather than defining a second request wire format.
-/
import Mathlib.Logic.Encodable.Basic
import Theory.AuthorizationDeclaration

namespace Minidregg.Compiler.SemanticManifest

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration

set_option autoImplicit false

/-! ## First-order manifest declarations -/

/-- A registered codec.  `valueTypeId` prevents one byte codec from being silently
reused as the codec of a different semantic type. -/
structure CodecPin where
  codecId : Digest
  valueTypeId : Digest
  version : Nat
deriving DecidableEq, Repr

/-- A named dimension is an exact shape parameter, not a runtime suggestion. -/
structure DimensionPin where
  dimensionId : Digest
  value : Nat
deriving DecidableEq, Repr

/-- A named resource or algebraic bound enforced by the selected verifier relation. -/
structure BoundPin where
  boundId : Digest
  maximum : Nat
deriving DecidableEq, Repr

/-- Native representation profiles.  MPC sharing wraps a registered base carrier; it
is not presented as a new algebra.  The four constructors are intentionally explicit. -/
inductive CarrierProfile where
  | gf2Tower
      (profileId towerId basisId representationId : Digest)
      (degree : Nat)
  | ext6
      (profileId : Digest)
      (baseModulus : Nat)
      (definingPolynomialId representationId : Digest)
  | residueRing
      (profileId : Digest)
      (degree plaintextModulus : Nat)
      (orderedModuli : List Nat)
      (coefficientRepresentationId nttRepresentationId : Digest)
  | mpcShared
      (profileId baseCarrierProfileId protocolId federationId : Digest)
      (partyCount threshold : Nat)
      (transcriptAuthenticationId : Digest)
deriving DecidableEq, Repr

def CarrierProfile.id : CarrierProfile -> Digest
  | .gf2Tower profileId _ _ _ _ => profileId
  | .ext6 profileId _ _ _ => profileId
  | .residueRing profileId _ _ _ _ _ => profileId
  | .mpcShared profileId _ _ _ _ _ _ => profileId

/-- A bridge requirement names one directional relation and both endpoint
representations.  Possessing this record proves no equality and constructs no cast. -/
structure NamedBridgeRequirement where
  bridgeId : Digest
  relationId : Digest
  sourceCarrierId : Digest
  targetCarrierId : Digest
  sourceCodecId : Digest
  targetCodecId : Digest
deriving DecidableEq, Repr

/-- One semantic receipt dialect relation.  Required bridges are references into the
manifest bridge registry, never caller-supplied conversion procedures or native
semantics. -/
structure DialectClauseDecl where
  clauseId : Digest
  relationId : Digest
  carrierProfileId : Digest
  statementCodecId : Digest
  proofCodecId : Digest
  proofSuiteId : Digest
  verifierControllerDigest : Digest
  requiredBridgeIds : List Digest
deriving DecidableEq, Repr

/-- Complete Lean-authored native ABI manifest.  Every field is first-order data. -/
structure Manifest where
  manifestVersion : Nat
  abiId : Digest
  semanticProgramId : Digest
  semanticRelationId : Digest
  receiptCodecId : Digest
  codecs : List CodecPin
  carriers : List CarrierProfile
  bridges : List NamedBridgeRequirement
  dialectClauses : List DialectClauseDecl
  transcriptControllerDigest : Digest
  dimensions : List DimensionPin
  bounds : List BoundPin
deriving DecidableEq, Repr

/-! ## Canonical first-order encoding and content address -/

structure CodecPinEncoding where
  codecId : Nat
  valueTypeId : Nat
  version : Nat
deriving DecidableEq, Repr, Encodable

def CodecPin.canonicalEncoding (pin : CodecPin) : CodecPinEncoding :=
  ⟨pin.codecId.value, pin.valueTypeId.value, pin.version⟩

def CodecPinEncoding.decode (wire : CodecPinEncoding) : CodecPin :=
  ⟨⟨wire.codecId⟩, ⟨wire.valueTypeId⟩, wire.version⟩

@[simp] theorem CodecPinEncoding.decode_canonicalEncoding (pin : CodecPin) :
    pin.canonicalEncoding.decode = pin := by
  cases pin <;> rfl

structure DimensionPinEncoding where
  dimensionId : Nat
  value : Nat
deriving DecidableEq, Repr, Encodable

def DimensionPin.canonicalEncoding (pin : DimensionPin) : DimensionPinEncoding :=
  ⟨pin.dimensionId.value, pin.value⟩

def DimensionPinEncoding.decode (wire : DimensionPinEncoding) : DimensionPin :=
  ⟨⟨wire.dimensionId⟩, wire.value⟩

@[simp] theorem DimensionPinEncoding.decode_canonicalEncoding (pin : DimensionPin) :
    pin.canonicalEncoding.decode = pin := by
  cases pin <;> rfl

structure BoundPinEncoding where
  boundId : Nat
  maximum : Nat
deriving DecidableEq, Repr, Encodable

def BoundPin.canonicalEncoding (pin : BoundPin) : BoundPinEncoding :=
  ⟨pin.boundId.value, pin.maximum⟩

def BoundPinEncoding.decode (wire : BoundPinEncoding) : BoundPin :=
  ⟨⟨wire.boundId⟩, wire.maximum⟩

@[simp] theorem BoundPinEncoding.decode_canonicalEncoding (pin : BoundPin) :
    pin.canonicalEncoding.decode = pin := by
  cases pin <;> rfl

inductive CarrierProfileEncoding where
  | gf2Tower
      (profileId towerId basisId representationId degree : Nat)
  | ext6
      (profileId baseModulus definingPolynomialId representationId : Nat)
  | residueRing
      (profileId degree plaintextModulus : Nat)
      (orderedModuli : List Nat)
      (coefficientRepresentationId nttRepresentationId : Nat)
  | mpcShared
      (profileId baseCarrierProfileId protocolId federationId : Nat)
      (partyCount threshold transcriptAuthenticationId : Nat)
deriving DecidableEq, Repr, Encodable

def CarrierProfile.canonicalEncoding : CarrierProfile -> CarrierProfileEncoding
  | .gf2Tower profileId towerId basisId representationId degree =>
      .gf2Tower profileId.value towerId.value basisId.value representationId.value degree
  | .ext6 profileId baseModulus definingPolynomialId representationId =>
      .ext6 profileId.value baseModulus definingPolynomialId.value representationId.value
  | .residueRing profileId degree plaintextModulus orderedModuli coefficientRep nttRep =>
      .residueRing profileId.value degree plaintextModulus orderedModuli
        coefficientRep.value nttRep.value
  | .mpcShared profileId baseCarrier protocolId federationId partyCount threshold authId =>
      .mpcShared profileId.value baseCarrier.value protocolId.value federationId.value
        partyCount threshold authId.value

def CarrierProfileEncoding.decode : CarrierProfileEncoding -> CarrierProfile
  | .gf2Tower profileId towerId basisId representationId degree =>
      .gf2Tower ⟨profileId⟩ ⟨towerId⟩ ⟨basisId⟩ ⟨representationId⟩ degree
  | .ext6 profileId baseModulus definingPolynomialId representationId =>
      .ext6 ⟨profileId⟩ baseModulus ⟨definingPolynomialId⟩ ⟨representationId⟩
  | .residueRing profileId degree plaintextModulus orderedModuli coefficientRep nttRep =>
      .residueRing ⟨profileId⟩ degree plaintextModulus orderedModuli
        ⟨coefficientRep⟩ ⟨nttRep⟩
  | .mpcShared profileId baseCarrier protocolId federationId partyCount threshold authId =>
      .mpcShared ⟨profileId⟩ ⟨baseCarrier⟩ ⟨protocolId⟩ ⟨federationId⟩
        partyCount threshold ⟨authId⟩

@[simp] theorem CarrierProfileEncoding.decode_canonicalEncoding
    (profile : CarrierProfile) : profile.canonicalEncoding.decode = profile := by
  cases profile <;> rfl

structure NamedBridgeEncoding where
  bridgeId : Nat
  relationId : Nat
  sourceCarrierId : Nat
  targetCarrierId : Nat
  sourceCodecId : Nat
  targetCodecId : Nat
deriving DecidableEq, Repr, Encodable

def NamedBridgeRequirement.canonicalEncoding
    (bridge : NamedBridgeRequirement) : NamedBridgeEncoding :=
  ⟨bridge.bridgeId.value, bridge.relationId.value,
    bridge.sourceCarrierId.value, bridge.targetCarrierId.value,
    bridge.sourceCodecId.value, bridge.targetCodecId.value⟩

def NamedBridgeEncoding.decode (wire : NamedBridgeEncoding) : NamedBridgeRequirement :=
  ⟨⟨wire.bridgeId⟩, ⟨wire.relationId⟩,
    ⟨wire.sourceCarrierId⟩, ⟨wire.targetCarrierId⟩,
    ⟨wire.sourceCodecId⟩, ⟨wire.targetCodecId⟩⟩

@[simp] theorem NamedBridgeEncoding.decode_canonicalEncoding
    (bridge : NamedBridgeRequirement) : bridge.canonicalEncoding.decode = bridge := by
  cases bridge <;> rfl

structure DialectClauseEncoding where
  clauseId : Nat
  relationId : Nat
  carrierProfileId : Nat
  statementCodecId : Nat
  proofCodecId : Nat
  proofSuiteId : Nat
  verifierControllerDigest : Nat
  requiredBridgeIds : List Nat
deriving DecidableEq, Repr, Encodable

def DialectClauseDecl.canonicalEncoding (clause : DialectClauseDecl) :
    DialectClauseEncoding :=
  ⟨clause.clauseId.value, clause.relationId.value, clause.carrierProfileId.value,
    clause.statementCodecId.value, clause.proofCodecId.value,
    clause.proofSuiteId.value, clause.verifierControllerDigest.value,
    clause.requiredBridgeIds.map Digest.value⟩

def DialectClauseEncoding.decode (wire : DialectClauseEncoding) : DialectClauseDecl :=
  ⟨⟨wire.clauseId⟩, ⟨wire.relationId⟩, ⟨wire.carrierProfileId⟩,
    ⟨wire.statementCodecId⟩, ⟨wire.proofCodecId⟩, ⟨wire.proofSuiteId⟩,
    ⟨wire.verifierControllerDigest⟩, wire.requiredBridgeIds.map Digest.mk⟩

@[simp] theorem DialectClauseEncoding.decode_canonicalEncoding
    (clause : DialectClauseDecl) : clause.canonicalEncoding.decode = clause := by
  cases clause
  simp [DialectClauseDecl.canonicalEncoding, DialectClauseEncoding.decode,
    Function.comp_def]

structure ManifestEncoding where
  manifestVersion : Nat
  abiId : Nat
  semanticProgramId : Nat
  semanticRelationId : Nat
  receiptCodecId : Nat
  codecs : List CodecPinEncoding
  carriers : List CarrierProfileEncoding
  bridges : List NamedBridgeEncoding
  dialectClauses : List DialectClauseEncoding
  transcriptControllerDigest : Nat
  dimensions : List DimensionPinEncoding
  bounds : List BoundPinEncoding
deriving DecidableEq, Repr, Encodable

def Manifest.canonicalEncoding (manifest : Manifest) : ManifestEncoding where
  manifestVersion := manifest.manifestVersion
  abiId := manifest.abiId.value
  semanticProgramId := manifest.semanticProgramId.value
  semanticRelationId := manifest.semanticRelationId.value
  receiptCodecId := manifest.receiptCodecId.value
  codecs := manifest.codecs.map CodecPin.canonicalEncoding
  carriers := manifest.carriers.map CarrierProfile.canonicalEncoding
  bridges := manifest.bridges.map NamedBridgeRequirement.canonicalEncoding
  dialectClauses := manifest.dialectClauses.map DialectClauseDecl.canonicalEncoding
  transcriptControllerDigest := manifest.transcriptControllerDigest.value
  dimensions := manifest.dimensions.map DimensionPin.canonicalEncoding
  bounds := manifest.bounds.map BoundPin.canonicalEncoding

def ManifestEncoding.decode (wire : ManifestEncoding) : Manifest where
  manifestVersion := wire.manifestVersion
  abiId := ⟨wire.abiId⟩
  semanticProgramId := ⟨wire.semanticProgramId⟩
  semanticRelationId := ⟨wire.semanticRelationId⟩
  receiptCodecId := ⟨wire.receiptCodecId⟩
  codecs := wire.codecs.map CodecPinEncoding.decode
  carriers := wire.carriers.map CarrierProfileEncoding.decode
  bridges := wire.bridges.map NamedBridgeEncoding.decode
  dialectClauses := wire.dialectClauses.map DialectClauseEncoding.decode
  transcriptControllerDigest := ⟨wire.transcriptControllerDigest⟩
  dimensions := wire.dimensions.map DimensionPinEncoding.decode
  bounds := wire.bounds.map BoundPinEncoding.decode

@[simp] theorem ManifestEncoding.decode_canonicalEncoding (manifest : Manifest) :
    manifest.canonicalEncoding.decode = manifest := by
  cases manifest
  simp [Manifest.canonicalEncoding, ManifestEncoding.decode, Function.comp_def]

theorem Manifest.canonicalEncoding_injective :
    Function.Injective Manifest.canonicalEncoding := by
  intro left right h
  have := congrArg ManifestEncoding.decode h
  simpa using this

/-- Exact mathematical content address of the first-order manifest. -/
def Manifest.contentAddress (manifest : Manifest) : Digest :=
  ⟨Encodable.encode manifest.canonicalEncoding⟩

theorem Manifest.contentAddress_injective :
    Function.Injective Manifest.contentAddress := by
  intro left right h
  apply Manifest.canonicalEncoding_injective
  apply Encodable.encode_injective
  exact congrArg Digest.value h

/-! ## Closed registries and unique dialect clause lookup -/

def Manifest.lookupCodec (manifest : Manifest) (codecId : Digest) : Option CodecPin :=
  manifest.codecs.find? fun codec => decide (codec.codecId = codecId)

def Manifest.lookupCarrier (manifest : Manifest) (profileId : Digest) :
    Option CarrierProfile :=
  manifest.carriers.find? fun profile => decide (profile.id = profileId)

def Manifest.lookupBridge (manifest : Manifest) (bridgeId : Digest) :
    Option NamedBridgeRequirement :=
  manifest.bridges.find? fun bridge => decide (bridge.bridgeId = bridgeId)

def Manifest.lookupClause (manifest : Manifest) (clauseId : Digest) :
    Option DialectClauseDecl :=
  manifest.dialectClauses.find? fun clause => decide (clause.clauseId = clauseId)

def Manifest.CodecIdsUnique (manifest : Manifest) : Prop :=
  (manifest.codecs.map CodecPin.codecId).Nodup

def Manifest.CarrierIdsUnique (manifest : Manifest) : Prop :=
  (manifest.carriers.map CarrierProfile.id).Nodup

def Manifest.BridgeIdsUnique (manifest : Manifest) : Prop :=
  (manifest.bridges.map NamedBridgeRequirement.bridgeId).Nodup

def Manifest.ClauseIdsUnique (manifest : Manifest) : Prop :=
  (manifest.dialectClauses.map DialectClauseDecl.clauseId).Nodup

/-- Registry closure: every referenced carrier, codec, and named bridge is declared in
this same manifest. -/
structure Manifest.WellFormed (manifest : Manifest) : Prop where
  codecIdsUnique : manifest.CodecIdsUnique
  carrierIdsUnique : manifest.CarrierIdsUnique
  bridgeIdsUnique : manifest.BridgeIdsUnique
  dialectClauseIdsUnique : manifest.ClauseIdsUnique
  receiptCodecClosed : exists codec,
    manifest.lookupCodec manifest.receiptCodecId = some codec
  mpcBasesClosed : forall profile,
    profile ∈ manifest.carriers ->
    match profile with
    | .mpcShared _ baseCarrierId _ _ _ _ _ =>
        exists base, manifest.lookupCarrier baseCarrierId = some base
    | _ => True
  bridgeEndpointsClosed : forall bridge,
    bridge ∈ manifest.bridges ->
      (exists source, manifest.lookupCarrier bridge.sourceCarrierId = some source) /\
      (exists target, manifest.lookupCarrier bridge.targetCarrierId = some target) /\
      (exists sourceCodec, manifest.lookupCodec bridge.sourceCodecId = some sourceCodec) /\
      (exists targetCodec, manifest.lookupCodec bridge.targetCodecId = some targetCodec)
  dialectClausesClosed : forall clause,
    clause ∈ manifest.dialectClauses ->
      (exists carrier, manifest.lookupCarrier clause.carrierProfileId = some carrier) /\
      (exists statementCodec,
        manifest.lookupCodec clause.statementCodecId = some statementCodec) /\
      (exists proofCodec, manifest.lookupCodec clause.proofCodecId = some proofCodec) /\
      forall bridgeId, bridgeId ∈ clause.requiredBridgeIds ->
        exists bridge, manifest.lookupBridge bridgeId = some bridge

theorem Manifest.lookupClause_some_closed
    {manifest : Manifest} {clauseId : Digest} {clause : DialectClauseDecl}
    (found : manifest.lookupClause clauseId = some clause) :
    clause ∈ manifest.dialectClauses /\ clause.clauseId = clauseId := by
  have hfind := (List.find?_eq_some_iff_append).mp found
  refine ⟨?_, of_decide_eq_true hfind.1⟩
  rcases hfind.2 with ⟨before, after, hlist, _⟩
  rw [hlist]
  simp

private theorem clause_eq_of_unique_ids
    {clauses : List DialectClauseDecl} {left right : DialectClauseDecl}
    (unique : (clauses.map DialectClauseDecl.clauseId).Nodup)
    (leftMem : left ∈ clauses) (rightMem : right ∈ clauses)
    (sameId : left.clauseId = right.clauseId) : left = right := by
  induction clauses generalizing left right with
  | nil => simp at leftMem
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨headFresh, tailUnique⟩
      rcases List.mem_cons.mp leftMem with leftHead | leftTail
      · subst left
        rcases List.mem_cons.mp rightMem with rightHead | rightTail
        · subst right
          rfl
        · exfalso
          have rightIdMem : right.clauseId ∈
              tail.map DialectClauseDecl.clauseId :=
            List.mem_map.mpr ⟨right, rightTail, rfl⟩
          rw [← sameId] at rightIdMem
          exact headFresh rightIdMem
      · rcases List.mem_cons.mp rightMem with rightHead | rightTail
        · subst right
          exfalso
          have leftIdMem : left.clauseId ∈
              tail.map DialectClauseDecl.clauseId :=
            List.mem_map.mpr ⟨left, leftTail, rfl⟩
          rw [sameId] at leftIdMem
          exact headFresh leftIdMem
        · exact ih tailUnique leftTail rightTail sameId

/-- Under the manifest uniqueness condition, a clause identifier names at most one
registered declaration. -/
theorem Manifest.registeredClause_unique
    {manifest : Manifest} (unique : manifest.ClauseIdsUnique)
    {left right : DialectClauseDecl}
    (leftMem : left ∈ manifest.dialectClauses)
    (rightMem : right ∈ manifest.dialectClauses)
    (sameId : left.clauseId = right.clauseId) : left = right :=
  clause_eq_of_unique_ids unique leftMem rightMem sameId

theorem Manifest.lookupClause_unique
    {manifest : Manifest} (unique : manifest.ClauseIdsUnique)
    {clauseId : Digest} {left right : DialectClauseDecl}
    (leftFound : manifest.lookupClause clauseId = some left)
    (rightFound : manifest.lookupClause clauseId = some right) : left = right := by
  obtain ⟨leftMem, leftId⟩ := Manifest.lookupClause_some_closed leftFound
  obtain ⟨rightMem, rightId⟩ := Manifest.lookupClause_some_closed rightFound
  exact manifest.registeredClause_unique unique leftMem rightMem (leftId.trans rightId.symm)

/-! ## Complete admission context -/

/-- Semantic outcome tag.  Rejection carries its canonical error/denial identifier. -/
inductive AdmissionOutcome where
  | rejected (errorId : Digest)
  | committed
deriving DecidableEq, Repr

/-- Roots carried for one concrete dialect clause instance. -/
structure DialectClauseRoots where
  clauseId : Digest
  statementRoot : Digest
  proofRoot : Digest
deriving DecidableEq, Repr

/-- Everything fixed before admission.  No field is supplied by a native verifier as an
acceptance decision. -/
structure AdmissionContext where
  manifestAddress : Digest
  historyDomain : Digest
  sequence : Nat
  previousReceiptRoot : Option Digest
  turnId : Digest
  request : Minidregg.Theory.AuthorizationDeclaration.SomeRequest
  outcome : AdmissionOutcome
  preStateRoot : Digest
  postStateRoot : Digest
  effectRoot : Digest
  authorizationRoot : Digest
  disclosureRoot : Digest
  dialectClauseRoots : List DialectClauseRoots
deriving DecidableEq, Repr

structure RequestEncoding where
  domain : Nat
  semantics : Nat
  federation : Nat
  resourceKind : Nat
  subject : Nat
  subjectKeyEpoch : Nat
  target : Nat
  verb : Nat
  argsDigest : Nat
  effectsDigest : Nat
  nonce : Nat
  height : Nat
  preStateRoot : Nat
  policyId : Nat
  policyEpoch : Nat
  cost : Nat
deriving DecidableEq, Repr, Encodable

def RequestEncoding.ofWire
    (wire : Minidregg.Theory.AuthorizationDeclaration.RequestWire) : RequestEncoding :=
  ⟨wire.domain, wire.semantics, wire.federation, wire.resourceKind,
    wire.subject, wire.subjectKeyEpoch, wire.target, wire.verb,
    wire.argsDigest, wire.effectsDigest, wire.nonce, wire.height,
    wire.preStateRoot, wire.policyId, wire.policyEpoch, wire.cost⟩

def RequestEncoding.toWire (wire : RequestEncoding) :
    Minidregg.Theory.AuthorizationDeclaration.RequestWire :=
  ⟨wire.domain, wire.semantics, wire.federation, wire.resourceKind,
    wire.subject, wire.subjectKeyEpoch, wire.target, wire.verb,
    wire.argsDigest, wire.effectsDigest, wire.nonce, wire.height,
    wire.preStateRoot, wire.policyId, wire.policyEpoch, wire.cost⟩

@[simp] theorem RequestEncoding.toWire_ofWire
    (wire : Minidregg.Theory.AuthorizationDeclaration.RequestWire) :
    (RequestEncoding.ofWire wire).toWire = wire := by
  cases wire <;> rfl

inductive AdmissionOutcomeEncoding where
  | rejected (errorId : Nat)
  | committed
deriving DecidableEq, Repr, Encodable

def AdmissionOutcome.canonicalEncoding : AdmissionOutcome -> AdmissionOutcomeEncoding
  | .rejected errorId => .rejected errorId.value
  | .committed => .committed

def AdmissionOutcomeEncoding.decode : AdmissionOutcomeEncoding -> AdmissionOutcome
  | .rejected errorId => .rejected ⟨errorId⟩
  | .committed => .committed

@[simp] theorem AdmissionOutcomeEncoding.decode_canonicalEncoding
    (outcome : AdmissionOutcome) : outcome.canonicalEncoding.decode = outcome := by
  cases outcome <;> rfl

structure DialectClauseRootsEncoding where
  clauseId : Nat
  statementRoot : Nat
  proofRoot : Nat
deriving DecidableEq, Repr, Encodable

def DialectClauseRoots.canonicalEncoding (roots : DialectClauseRoots) :
    DialectClauseRootsEncoding :=
  ⟨roots.clauseId.value, roots.statementRoot.value, roots.proofRoot.value⟩

def DialectClauseRootsEncoding.decode (wire : DialectClauseRootsEncoding) :
    DialectClauseRoots :=
  ⟨⟨wire.clauseId⟩, ⟨wire.statementRoot⟩, ⟨wire.proofRoot⟩⟩

@[simp] theorem DialectClauseRootsEncoding.decode_canonicalEncoding
    (roots : DialectClauseRoots) : roots.canonicalEncoding.decode = roots := by
  cases roots <;> rfl

structure AdmissionContextEncoding where
  manifestAddress : Nat
  historyDomain : Nat
  sequence : Nat
  previousReceiptRoot : Option Nat
  turnId : Nat
  request : RequestEncoding
  outcome : AdmissionOutcomeEncoding
  preStateRoot : Nat
  postStateRoot : Nat
  effectRoot : Nat
  authorizationRoot : Nat
  disclosureRoot : Nat
  dialectClauseRoots : List DialectClauseRootsEncoding
deriving DecidableEq, Repr, Encodable

def AdmissionContext.canonicalEncoding (context : AdmissionContext) :
    AdmissionContextEncoding where
  manifestAddress := context.manifestAddress.value
  historyDomain := context.historyDomain.value
  sequence := context.sequence
  previousReceiptRoot := context.previousReceiptRoot.map Digest.value
  turnId := context.turnId.value
  request := RequestEncoding.ofWire
    (Minidregg.Theory.AuthorizationDeclaration.encodeRequest context.request)
  outcome := context.outcome.canonicalEncoding
  preStateRoot := context.preStateRoot.value
  postStateRoot := context.postStateRoot.value
  effectRoot := context.effectRoot.value
  authorizationRoot := context.authorizationRoot.value
  disclosureRoot := context.disclosureRoot.value
  dialectClauseRoots := context.dialectClauseRoots.map DialectClauseRoots.canonicalEncoding

def AdmissionContextEncoding.decode (wire : AdmissionContextEncoding) :
    Option AdmissionContext := do
  let request <- Minidregg.Theory.AuthorizationDeclaration.decodeRequest wire.request.toWire
  some
    { manifestAddress := ⟨wire.manifestAddress⟩
      historyDomain := ⟨wire.historyDomain⟩
      sequence := wire.sequence
      previousReceiptRoot := wire.previousReceiptRoot.map Digest.mk
      turnId := ⟨wire.turnId⟩
      request := request
      outcome := wire.outcome.decode
      preStateRoot := ⟨wire.preStateRoot⟩
      postStateRoot := ⟨wire.postStateRoot⟩
      effectRoot := ⟨wire.effectRoot⟩
      authorizationRoot := ⟨wire.authorizationRoot⟩
      disclosureRoot := ⟨wire.disclosureRoot⟩
      dialectClauseRoots := wire.dialectClauseRoots.map DialectClauseRootsEncoding.decode }

@[simp] theorem AdmissionContextEncoding.decode_canonicalEncoding
    (context : AdmissionContext) :
    context.canonicalEncoding.decode = some context := by
  cases context
  simp [AdmissionContext.canonicalEncoding, AdmissionContextEncoding.decode,
    Function.comp_def]

theorem AdmissionContext.canonicalEncoding_injective :
    Function.Injective AdmissionContext.canonicalEncoding := by
  intro left right h
  have := congrArg AdmissionContextEncoding.decode h
  simpa using this

/-- Admission closure and history/atomicity invariants. -/
structure AdmissionContext.WellFormed
    (manifest : Manifest) (context : AdmissionContext) : Prop where
  manifestExact : context.manifestAddress = manifest.contentAddress
  historyLink :
    (context.sequence = 0 /\ context.previousReceiptRoot = none) \/
    (0 < context.sequence /\ exists previous,
      context.previousReceiptRoot = some previous)
  requestSemantics : context.request.2.semantics = manifest.semanticRelationId
  requestPreState : context.request.2.preStateRoot = context.preStateRoot
  rejectedAtomic : match context.outcome with
    | .rejected _ => context.postStateRoot = context.preStateRoot
    | .committed => True
  dialectClauseIdsUnique :
    (context.dialectClauseRoots.map DialectClauseRoots.clauseId).Nodup
  dialectClausesClosed : forall roots,
    roots ∈ context.dialectClauseRoots ->
    exists clause, manifest.lookupClause roots.clauseId = some clause

theorem AdmissionContext.closedClause_unique
    {manifest : Manifest} (manifestUnique : manifest.ClauseIdsUnique)
    {context : AdmissionContext} (wellFormed : context.WellFormed manifest)
    {roots : DialectClauseRoots} (rootsMem : roots ∈ context.dialectClauseRoots) :
    ∃! clause,
      manifest.lookupClause roots.clauseId = some clause := by
  obtain ⟨clause, found⟩ := wellFormed.dialectClausesClosed roots rootsMem
  refine ⟨clause, found, ?_⟩
  intro other otherFound
  exact manifest.lookupClause_unique manifestUnique otherFound found

end Minidregg.Compiler.SemanticManifest
