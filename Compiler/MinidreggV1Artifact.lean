/-
# Compiler.MinidreggV1Artifact -- the concrete v1 semantic artifact

This module instantiates the generic semantic artifact boundary.  Every exported
declaration is projected from an existing Lean declaration: the repository's typed
authorization plan, a typed account-move declaration, a finite guarded reactive controller,
and a same-opening disclosure declaration.  Carrier, codec, and bridge vocabulary
is registered here, but no proof dialect is admitted without a concrete Lean
controller supplied by an extension manifest.
-/
import Compiler.SemanticArtifactBundle

namespace Minidregg.Compiler.MinidreggV1Artifact

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.SemanticArtifactBundle
open Minidregg.Compiler.DeclaredEffectArtifact

set_option autoImplicit false

/-! ## Stable identifiers -/

def id (value : Nat) : Digest := ⟨value⟩

def receiptCodec : CodecPin := ⟨id 1, id 1001, 1⟩
def authorizationDeclarationCodec : CodecPin := ⟨id 2, id 1002, 1⟩
def authorizationRequestCodec : CodecPin := ⟨id 3, id 1003, 1⟩
def effectDeclarationCodec : CodecPin := ⟨id 4, id 1004, 1⟩
def moveOperationCodec : CodecPin := ⟨id 5, id 1005, 1⟩
def kernelStateCodec : CodecPin := ⟨id 6, id 1006, 1⟩
def reactiveDeclarationCodec : CodecPin := ⟨id 7, id 1007, 1⟩
def reactiveRequestCodec : CodecPin := ⟨id 8, id 1008, 1⟩
def reactiveProofCodec : CodecPin := ⟨id 9, id 1009, 1⟩
def disclosureDeclarationCodec : CodecPin := ⟨id 10, id 1010, 1⟩
def disclosureRequestCodecPin : CodecPin := ⟨id 11, id 1011, 1⟩
def disclosureCommitmentCodec : CodecPin := ⟨id 12, id 1012, 1⟩
def disclosureRepresentationCodec : CodecPin := ⟨id 13, id 1013, 1⟩
def disclosureReleaseCodec : CodecPin := ⟨id 14, id 1014, 1⟩
def disclosureProofCodec : CodecPin := ⟨id 15, id 1015, 1⟩
def dialectStatementCodec : CodecPin := ⟨id 16, id 1016, 1⟩
def dialectProofCodec : CodecPin := ⟨id 17, id 1017, 1⟩
def gf2ValueCodec : CodecPin := ⟨id 18, id 1018, 1⟩
def ext6ValueCodec : CodecPin := ⟨id 19, id 1019, 1⟩
def residueRingValueCodec : CodecPin := ⟨id 20, id 1020, 1⟩
/-- Semantic pin for the canonical 256-bit recursive-coordinate value encoding.
This registers an ABI identity and version only; it does not identify or validate any
Rust representation. -/
def tower256ValueCodec : CodecPin := ⟨id 21, id 1021, 1⟩

def codecRegistry : List CodecPin :=
  [receiptCodec, authorizationDeclarationCodec, authorizationRequestCodec,
   effectDeclarationCodec, moveOperationCodec, kernelStateCodec,
   reactiveDeclarationCodec, reactiveRequestCodec, reactiveProofCodec,
   disclosureDeclarationCodec, disclosureRequestCodecPin,
   disclosureCommitmentCodec, disclosureRepresentationCodec,
   disclosureReleaseCodec, disclosureProofCodec, dialectStatementCodec,
   dialectProofCodec, gf2ValueCodec, ext6ValueCodec, residueRingValueCodec,
   tower256ValueCodec]

/-- Identifiers for the declared recursive Fan--Paar tower family and its canonical
recursive coordinate basis.  These are semantic ABI pins, not correspondence claims
about a native implementation. -/
def fanPaarTowerId : Digest := id 211
def fanPaarRecursiveBasisId : Digest := id 212

def gf2Carrier : CarrierProfile :=
  .gf2Tower (id 201) fanPaarTowerId fanPaarRecursiveBasisId gf2ValueCodec.codecId 64

def ext6Carrier : CarrierProfile :=
  .ext6 (id 202) 2013265921 (id 213) ext6ValueCodec.codecId

def residueRingCarrier : CarrierProfile :=
  .residueRing (id 203) 4096 1032193
    [68719403009, 68719230977, 137438822401]
    residueRingValueCodec.codecId (id 220)

def mpcCarrier : CarrierProfile :=
  .mpcShared (id 204) gf2Carrier.id (id 230) (id 231) 3 2 (id 232)

/-- A distinct `GF(2^256)` semantic carrier profile.  Sharing the declared tower family
and basis with the 64-bit profile does not identify their representations: the profile,
degree, and codec pins are distinct.  No Rust correspondence theorem is claimed. -/
def gf2Tower256Carrier : CarrierProfile :=
  .gf2Tower (id 205) fanPaarTowerId fanPaarRecursiveBasisId
    tower256ValueCodec.codecId 256

def carrierRegistry : List CarrierProfile :=
  [gf2Carrier, ext6Carrier, residueRingCarrier, mpcCarrier, gf2Tower256Carrier]

/-- A named consistency requirement only.  This record does not claim an implemented
cross-characteristic homomorphism. -/
def gf2ToExt6Bridge : NamedBridgeRequirement where
  bridgeId := id 301
  relationId := id 311
  sourceCarrierId := gf2Carrier.id
  targetCarrierId := ext6Carrier.id
  sourceCodecId := gf2ValueCodec.codecId
  targetCodecId := ext6ValueCodec.codecId

def ext6ToResidueRingBridge : NamedBridgeRequirement where
  bridgeId := id 302
  relationId := id 312
  sourceCarrierId := ext6Carrier.id
  targetCarrierId := residueRingCarrier.id
  sourceCodecId := ext6ValueCodec.codecId
  targetCodecId := residueRingValueCodec.codecId

def bridgeRegistry : List NamedBridgeRequirement :=
  [gf2ToExt6Bridge, ext6ToResidueRingBridge]

/-- The base artifact deliberately admits no proof dialect.  Concrete proof dialects
must extend this manifest with both a declaration and a Lean-owned controller; carrier
or codec registration alone is not implementation evidence. -/
def clauseRegistry : List DialectClauseDecl := []

/-! ## Concrete manifest and registry proofs -/

def manifest : Manifest where
  manifestVersion := 1
  abiId := id 100
  semanticProgramId := id 101
  semanticRelationId := id 102
  receiptCodecId := receiptCodec.codecId
  codecs := codecRegistry
  carriers := carrierRegistry
  bridges := bridgeRegistry
  dialectClauses := clauseRegistry
  transcriptControllerDigest := id 500
  dimensions :=
    [⟨id 501, 64⟩, ⟨id 502, 6⟩, ⟨id 503, 4096⟩, ⟨id 504, 4⟩]
  bounds := [⟨id 511, 1048576⟩, ⟨id 512, 3⟩, ⟨id 513, 65536⟩]

theorem manifest_wellFormed : manifest.WellFormed where
  codecIdsUnique := by
    change ([id 1, id 2, id 3, id 4, id 5, id 6, id 7, id 8, id 9, id 10,
      id 11, id 12, id 13, id 14, id 15, id 16, id 17, id 18, id 19, id 20,
      id 21] :
      List Digest).Nodup
    decide
  carrierIdsUnique := by
    change ([id 201, id 202, id 203, id 204, id 205] : List Digest).Nodup
    decide
  bridgeIdsUnique := by
    change ([id 301, id 302] : List Digest).Nodup
    decide
  dialectClauseIdsUnique := by
    exact List.nodup_nil
  receiptCodecClosed := ⟨receiptCodec, by decide⟩
  mpcBasesClosed := by
    intro profile member
    simp only [manifest, carrierRegistry, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · trivial
    · exact ⟨gf2Carrier, by decide⟩
    · trivial
  bridgeEndpointsClosed := by
    intro bridge member
    simp only [manifest, bridgeRegistry, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact
        ⟨⟨gf2Carrier, by decide⟩,
         ⟨ext6Carrier, by decide⟩,
         ⟨gf2ValueCodec, by decide⟩,
         ⟨ext6ValueCodec, by decide⟩⟩
    · exact
        ⟨⟨ext6Carrier, by decide⟩,
         ⟨residueRingCarrier, by decide⟩,
         ⟨ext6ValueCodec, by decide⟩,
         ⟨residueRingValueCodec, by decide⟩⟩
  dialectClausesClosed := by
    intro clause member
    simp [manifest, clauseRegistry] at member

/-- The full declared registries are not merely nodup: every key can be resolved by
the manifest's public lookup operations to exactly its authored declaration. -/
theorem key_registry_resolves :
    codecRegistry.map (fun pin => manifest.lookupCodec pin.codecId) =
      codecRegistry.map some ∧
    carrierRegistry.map (fun profile => manifest.lookupCarrier profile.id) =
      carrierRegistry.map some ∧
    bridgeRegistry.map (fun bridge => manifest.lookupBridge bridge.bridgeId) =
      bridgeRegistry.map some ∧
    clauseRegistry.map (fun clause => manifest.lookupClause clause.clauseId) =
      clauseRegistry.map some := by
  decide

/-! ## Concrete reactive declaration -/

def unitCodec : LawfulCodec Unit where
  encode _ := []
  decode
    | [] => some ()
    | _ => none
  decode_encode _ := rfl

def reactiveUniverse : FirstOrderUniverse where
  Code := Unit
  El := fun _ => Unit
  codec := fun _ => unitCodec

abbrev reactiveTypes : Minidregg.Theory.ReactiveController.Types where
  Key := Nat
  Value := Nat
  HoleId := Nat
  TurnId := Nat
  Root := Nat
  AuthorityDemand := Nat
  Commitment := Nat
  Height := Nat
  Continuation := Nat
  NullifierDomain := Nat

def reactiveDeclaration :
    Minidregg.Theory.ReactiveController.Declaration reactiveUniverse reactiveTypes where
  hole :=
    { holeId := 1
      code := ()
      turnId := 1
      preRoot := 100
      authorityDemand := 200
      footprint := {0}
      guardCommitment := 300
      effectCommitment := 301
      deadline := 1000
      continuation := 400
      nullifierDomain := 500 }
  guard := .and (.lengthLE 0) .allow
  effect := { writes := [(0, 7)], expectedPostRoot := 101 }
  wakeAfter := none

theorem reactive_is_finite_guarded_write :
    reactiveDeclaration.effect.writes = [(0, 7)] ∧
    reactiveDeclaration.guard = .and (.lengthLE 0) .allow := by
  exact ⟨rfl, rfl⟩

/-! ## Concrete same-opening disclosure declaration -/

def boolCodec : LawfulCodec Bool where
  encode
    | false => [0]
    | true => [1]
  decode
    | [0] => some false
    | [1] => some true
    | _ => none
  decode_encode value := by cases value <;> rfl

def decodeBoolByte : UInt8 → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

def boolByte : Bool → UInt8
  | false => 0
  | true => 1

def concreteDisclosureRequestCodec :
    LawfulCodec (DisclosureRequest Bool Bool Bool Bool) where
  encode request :=
    [boolByte request.observer, boolByte request.policy,
     boolByte request.recipient, boolByte request.purpose]
  decode
    | [observerByte, policyByte, recipientByte, purposeByte] => do
        let observer ← decodeBoolByte observerByte
        let policy ← decodeBoolByte policyByte
        let recipient ← decodeBoolByte recipientByte
        let purpose ← decodeBoolByte purposeByte
        some ⟨observer, policy, recipient, purpose⟩
    | _ => none
  decode_encode request := by
    rcases request with ⟨observer, policy, recipient, purpose⟩
    cases observer <;> cases policy <;> cases recipient <;> cases purpose <;> rfl

/-- Booleans make this small but non-vacuous: both representations must equal the
private output, both opening witnesses must authorize use, and policy plus an
authorization witness must be true. -/
def disclosureDeclaration :
    DisclosureDeclaration Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool where
  requestCodec := concreteDisclosureRequestCodec
  commitmentCodec := boolCodec
  representationCodec := boolCodec
  releaseCodec := boolCodec
  verifySourceOpening := fun commitment witness output =>
    decide (commitment = output ∧ witness = true)
  verifyTargetOpening := fun representation witness output =>
    decide (representation = output ∧ witness = true)
  verifyPermission := fun request _output witness =>
    decide (request.policy = true ∧ witness = true)
  projectRelease := fun request output => request.policy && output

theorem disclosure_accepts_honest_opening :
    disclosureDeclaration.verifySourceOpening true true true = true ∧
    disclosureDeclaration.verifyTargetOpening true true true = true ∧
    disclosureDeclaration.verifyPermission ⟨false, true, false, true⟩ true true = true := by
  decide

/-! ## Projected declarations and the v1 bundle -/

def effectArtifact : DeclarationArtifact :=
  DeclarationArtifact.ofDeclaredEffect accountMoveArtifact (id 602)
    effectDeclarationCodec.codecId moveOperationCodec.codecId
    kernelStateCodec.codecId [id 701]

theorem effectArtifact_is_typed_account_move :
    effectArtifact.declarationWords = [accountMoveDeclaration.toWire.words] := by
  rfl

def reactiveArtifact : DeclarationArtifact :=
  DeclarationArtifact.ofReactive reactiveDeclaration (id 603)
    reactiveDeclarationCodec.codecId reactiveRequestCodec.codecId
    reactiveProofCodec.codecId receiptCodec.codecId 1 [id 702]

def disclosureArtifact : DeclarationArtifact :=
  DeclarationArtifact.ofDisclosure disclosureDeclaration (id 604)
    disclosureDeclarationCodec.codecId disclosureRequestCodecPin.codecId
    disclosureCommitmentCodec.codecId disclosureRepresentationCodec.codecId
    disclosureReleaseCodec.codecId disclosureProofCodec.codecId 1 [id 703]

def bundle : ArtifactBundle :=
  ArtifactBundle.ofDeclarations manifest (id 601)
    authorizationDeclarationCodec.codecId authorizationRequestCodec.codecId
    [effectArtifact] reactiveArtifact disclosureArtifact

/-- The four declarations in the artifact are exactly the expected projections and
carry distinct pinned declaration identities. -/
theorem bundle_identity_pins :
    bundle.authorization.declarationId = id 601 ∧
    bundle.effects = [effectArtifact] ∧
    bundle.reactive.declarationId = id 603 ∧
    bundle.disclosure.declarationId = id 604 ∧
    bundle.phasePlan = canonicalControllerPlan := by
  decide

theorem bundle_codec_pins_are_registered :
    manifest.lookupCodec bundle.authorization.declarationCodecId =
        some authorizationDeclarationCodec ∧
    manifest.lookupCodec bundle.authorization.requestCodecId =
        some authorizationRequestCodec ∧
    manifest.lookupCodec effectArtifact.declarationCodecId =
        some effectDeclarationCodec ∧
    manifest.lookupCodec reactiveArtifact.declarationCodecId =
        some reactiveDeclarationCodec ∧
    manifest.lookupCodec disclosureArtifact.declarationCodecId =
        some disclosureDeclarationCodec := by
  decide

theorem bundle_encoding_roundtrip :
    bundle.canonicalEncoding.decode = bundle := by
  exact ArtifactBundleEncoding.decode_canonicalEncoding bundle

def buildTarget : BuildTarget where
  path := "prover/testdata/semantic_artifact_v1.json"
  bundle := bundle

/-- The generic `contentAddress` is an injective mathematical Gödel address and is
intentionally retained at the theorem boundary.  Materializing that unbounded numeral
is not a deployment hashing strategy.  This concrete writer emits the exact canonical
payload, from the shared JSON projections, for a deployment hash suite to digest. -/
def artifactPayloadToJson (artifact : ArtifactBundle) : Lean.Json :=
  let wire := artifact.canonicalEncoding
  Lean.Json.mkObj
    [("schema", Lean.Json.str "minidregg/semantic-artifact-bundle/v1"),
     ("canonicalEncoding", Lean.Json.str "minidregg/encodable/v1"),
     ("manifest", manifestToJson wire.manifest),
     ("authorization", authorizationToJson wire.authorization),
     ("effects", Lean.Json.arr (wire.effects.map declarationToJson).toArray),
     ("reactive", declarationToJson wire.reactive),
     ("disclosure", declarationToJson wire.disclosure),
     ("phasePlan", Lean.Json.arr
       (wire.phasePlan.map fun phase => Lean.Json.str phase.name).toArray)]

def artifactPayloadText (artifact : ArtifactBundle) : String :=
  (artifactPayloadToJson artifact).pretty ++ "\n"

def writeBuildTarget (target : BuildTarget) : IO Unit := do
  if let some directory := target.path.parent then IO.FS.createDirAll directory
  IO.FS.writeFile target.path (artifactPayloadText target.bundle)

#eval writeBuildTarget buildTarget

end Minidregg.Compiler.MinidreggV1Artifact
