/-
# Compiler.ArithmeticNativeDeployment -- deployable byte-backed clause 406

This module closes the smallest honest controller/artifact/native-work loop.
The artifact authenticates one fixed BabyBear add-1 work item and its byte
layouts. Generated Rust may return only an error or 144 candidate bytes. Lean
decodes those bytes as 36 canonical little-endian BabyBear words, rebuilds
the exact bounded `KernelResponse`, and runs the existing descriptor checker.

No Rust proposition, semantic verdict, or refinement theorem exists here.
-/

import Compiler.ComposableDeploymentManifest
import Compiler.NativeGlueGen

namespace Minidregg.Compiler.ArithmeticNativeDeployment

open Minidregg.Compiler.BignumKernelABI
open Minidregg.Compiler.ComposableDeploymentManifest
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.MinidreggV1ArithmeticWork
open Minidregg.Compiler.NativeGlueGen
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SemanticArtifactBundle
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxRecDepth 4096

/-! ## Artifact-authenticated byte work -/

def requestCodec : ByteCodecProfile where
  registry := .nativeAbi
  codecId := 9003
  valueTypeId := 9004
  version := 1
  shape := .empty

def responseCodec : ByteCodecProfile where
  registry := .nativeAbi
  codecId := 9005
  valueTypeId := 9006
  version := 1
  shape := .babyBearAdd1DescriptorU32LE

def workProfile : WorkProfile where
  workId := 9102
  carrierProfileId := babyBearArithmeticCarrier.id.value
  requestCodec := requestCodec
  responseCodec := responseCodec
  kernel := .babyBearAdd1ZeroWitness

theorem work_profile_pins_exact :
    workProfile.workId = 9102 ∧
    workProfile.carrierProfileId = babyBearArithmeticCarrier.id.value ∧
    workProfile.requestCodec = requestCodec ∧
    workProfile.responseCodec = responseCodec ∧
    workProfile.kernel = .babyBearAdd1ZeroWitness := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem response_wire_count_exact :
    arithmeticInstruction.call.descriptor.nWires = 36 := by
  decide

/-! ## Canonical BabyBear byte decoder -/

def u32LE (a b c d : UInt8) : Nat :=
  a.toNat + 256 * b.toNat + 256 ^ 2 * c.toNat + 256 ^ 3 * d.toNat

def decodeWord (a b c d : UInt8) : Option BabyBear :=
  let value := u32LE a b c d
  if value < babyBearP then some value else none

def decodeWords : Nat -> List UInt8 -> Option (List BabyBear)
  | 0, [] => some []
  | 0, _ => none
  | count + 1, a :: b :: c :: d :: rest =>
      match decodeWord a b c d with
      | none => none
      | some head =>
          match decodeWords count rest with
          | none => none
          | some tail => some (head :: tail)
  | _ + 1, _ => none

def responseOfList (wires : List BabyBear)
    (lengthExact : wires.length =
      arithmeticInstruction.call.descriptor.nWires) :
    KernelResponse arithmeticInstruction where
  wires := fun index => wires.get
    ⟨index.val, by simpa [lengthExact] using index.isLt⟩

def decodeResponse (bytes : List UInt8) :
    Option (KernelResponse arithmeticInstruction) :=
  if bytes.length = 144 then
    match decodeWords 36 bytes with
    | none => none
    | some wires =>
        if lengthExact : wires.length =
            arithmeticInstruction.call.descriptor.nWires then
          some (responseOfList wires lengthExact)
        else none
  else none

/-! The candidate is the deterministic evaluation of the emitted gate list
from the all-zero source assignment.  This computes auxiliary wires; it does
not decide descriptor acceptance. -/

def executeGate (wires : Nat → BabyBear) (gate : DGate BabyBear) :
    Nat → BabyBear :=
  fun index =>
    if index = gate.out then
      gate.op.denote (gate.a.read wires) (gate.b.read wires)
    else wires index

def honestTotalWires : Nat → BabyBear :=
  arithmeticInstruction.call.descriptor.gates.foldl executeGate (fun _ => 0)

def honestWires : List BabyBear :=
  List.ofFn (fun index : Fin 36 => honestTotalWires index)

def encodeWord (word : BabyBear) : List UInt8 :=
  NativeWorkProfiles.encodeU32LE word.val

def honestBytes : List UInt8 := honestWires.flatMap encodeWord

theorem honest_bytes_width : honestBytes.length = 144 := by
  decide

theorem emitted_candidate_exact :
    NativeGlueGen.babyBearAdd1ZeroCandidateBytes = honestBytes := by
  decide

theorem honest_words_decode : decodeWords 36 honestBytes = some honestWires := by
  decide

def honestResponse : KernelResponse arithmeticInstruction :=
  responseOfList honestWires (by decide)

theorem honest_response_decode : decodeResponse honestBytes = some honestResponse := by
  have honestLength : honestWires.length =
      arithmeticInstruction.call.descriptor.nWires := by decide
  simp [decodeResponse, honest_bytes_width, honest_words_decode,
    honestResponse, honestLength]

theorem honestResponse_accepts :
    arithmeticInstruction.call.Accepts honestResponse.totalWires := by
  apply (kernelCallAcceptsCheck_eq_true_iff arithmeticInstruction
    honestResponse).mp
  decide

theorem honestResponse_prefix :
    PublicPrefixExact arithmeticInstruction honestResponse := by
  constructor
  · rfl
  · intro index
    exact Fin.elim0 index

/-! ## Byte-only dialect controller -/

inductive ByteControllerOutcome
  | malformedResponse (bytes : List UInt8)
  | rejected (bytes : List UInt8) (failure : NativeKernelPlan.Failure)
  | certified (bytes : List UInt8)
      (response : KernelResponse arithmeticInstruction)
      (certificate : CertifiedResponse manifest arithmeticInstruction response)

def byteController : DialectController.{0, 0, 0, 0} arithmeticClause where
  Input := Unit
  Query := fun _ => List UInt8
  Reply := fun _ _ => List UInt8
  Outcome := fun _ => ByteControllerOutcome
  issue := fun _ => []
  check := fun _ bytes =>
    match decodeResponse bytes with
    | none => .malformedResponse bytes
    | some response =>
        match checkInstruction manifest arithmeticInstruction response with
        | .inl failure => .rejected bytes failure
        | .inr certificate => .certified bytes response certificate

def byteControllerEntry : ControllerEntry.{0, 0, 0, 0} where
  declaration := arithmeticClause
  controller := byteController

def bytePack : ImplementedControllerPack.{0, 0, 0, 0} where
  carriers := [babyBearArithmeticCarrier]
  nativeAbiCodecs := [requestCodec, responseCodec]
  nativeWorkCatalog := [workProfile]
  entries := [byteControllerEntry]

def artifact : ArtifactBundle :=
  bytePack.extendArtifact MinidreggV1Artifact.bundle

@[simp] theorem artifact_manifest : artifact.manifest = manifest := by
  rfl

theorem artifact_contains_exact_native_surface :
    requestCodec ∈ artifact.nativeAbiCodecs ∧
    responseCodec ∈ artifact.nativeAbiCodecs ∧
    workProfile ∈ artifact.nativeWorkCatalog := by
  simp [artifact, bytePack, ImplementedControllerPack.extendArtifact,
    MinidreggV1Artifact.bundle, ArtifactBundle.ofDeclarations]

theorem artifact_nativeCatalogWellFormed :
    NativeCatalogWellFormed artifact.manifest artifact.nativeAbiCodecs
      artifact.nativeWorkCatalog := by
  constructor
  · decide
  · decide
  · intro codec member
    simp [artifact, bytePack, ImplementedControllerPack.extendArtifact,
      MinidreggV1Artifact.bundle, ArtifactBundle.ofDeclarations,
      MinidreggV1Artifact.nativeAbiCodecRegistry] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro codec member
    simp [artifact, bytePack, ImplementedControllerPack.extendArtifact,
      MinidreggV1Artifact.bundle, ArtifactBundle.ofDeclarations,
      MinidreggV1Artifact.nativeAbiCodecRegistry] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro work member
    simp [artifact, bytePack, ImplementedControllerPack.extendArtifact,
      MinidreggV1Artifact.bundle, ArtifactBundle.ofDeclarations,
      MinidreggV1Artifact.nativeWorkCatalog] at member
    rcases member with rfl | rfl
    · exact ⟨MinidreggV1Artifact.gf2Tower256Carrier, by decide⟩
    · exact ⟨babyBearArithmeticCarrier, by decide⟩
  · intro work member
    simp [artifact, bytePack, ImplementedControllerPack.extendArtifact,
      MinidreggV1Artifact.bundle, ArtifactBundle.ofDeclarations,
      MinidreggV1Artifact.nativeWorkCatalog] at member
    rcases member with rfl | rfl
    · change lookupNativeAbiCodec
        [MinidreggV1Artifact.tower256DotProductRequestCodec,
          requestCodec, responseCodec] 9001 =
        some MinidreggV1Artifact.tower256DotProductRequestCodec
      rfl
    · change lookupNativeAbiCodec
        [MinidreggV1Artifact.tower256DotProductRequestCodec,
          requestCodec, responseCodec] 9003 = some requestCodec
      rfl
  · intro work member
    simp [artifact, bytePack, ImplementedControllerPack.extendArtifact,
      MinidreggV1Artifact.bundle, ArtifactBundle.ofDeclarations,
      MinidreggV1Artifact.nativeWorkCatalog] at member
    rcases member with rfl | rfl
    · change manifest.lookupCodec MinidreggV1Artifact.tower256ValueCodec.codecId =
        some MinidreggV1Artifact.tower256ValueCodec
      decide
    · change lookupNativeAbiCodec
        [MinidreggV1Artifact.tower256DotProductRequestCodec,
          requestCodec, responseCodec] 9005 = some responseCodec
      rfl

def registry : ControllerRegistry.{0, 0, 0, 0} :=
  bytePack.controllerRegistry

theorem registry_wellFormed : registry.WellFormed manifest := by
  constructor
  · change ([clauseControllerKey arithmeticClause] : List ControllerKey).Nodup
    simp
  · intro entry member
    change entry ∈ [byteControllerEntry] at member
    rw [List.mem_singleton] at member
    subst entry
    exact arithmetic_clause_registered
  · intro clause member
    change clause ∈ [arithmeticClause] at member
    rw [List.mem_singleton] at member
    subst clause
    refine ⟨byteControllerEntry, ?_⟩
    simp [registry, bytePack, ImplementedControllerPack.controllerRegistry,
      ControllerRegistry.lookup, byteControllerEntry, ControllerEntry.key,
      clauseControllerKey]

def deployment : DeploymentJoin.{0, 0, 0, 0} where
  artifact := artifact
  registry := registry
  manifestWellFormed := manifest_wellFormed
  nativeCatalogWellFormed := artifact_nativeCatalogWellFormed
  controllerRegistryWellFormed := registry_wellFormed

noncomputable def resolved :
    ResolvedClause deployment.artifact.manifest deployment.registry
      arithmeticClause.clauseId :=
  resolveRegistered deployment.manifestWellFormed
    deployment.controllerRegistryWellFormed arithmetic_clause_registered

theorem resolved_controller_exact :
    resolved.controllerEntry.declaration = arithmeticClause :=
  resolved.controllerExact.trans
    (deployment.artifact.manifest.lookupClause_unique
      deployment.manifestWellFormed.dialectClauseIdsUnique
      resolved.clauseFound arithmetic_clause_registered)

theorem honest_bytes_certified :
    ∃ certificate,
      byteController.check () honestBytes =
        .certified honestBytes honestResponse certificate := by
  rcases response_checked honestResponse honestResponse_prefix
      honestResponse_accepts with ⟨certificate, checked⟩
  exact ⟨certificate, by
    simp [byteController, honest_response_decode, checked]⟩

theorem malformed_bytes_cannot_certify
    {bytes : List UInt8} (wrongWidth : bytes.length ≠ 144) :
    ¬ ∃ response certificate,
      byteController.check () bytes =
        .certified bytes response certificate := by
  intro certified
  rcases certified with ⟨response, certificate, exact⟩
  have decodedNone : decodeResponse bytes = none := by
    simp [decodeResponse, wrongWidth]
  simp [byteController, decodedNone] at exact

/-- Generic dispatch transport failure blocks before the byte checker runs. -/
theorem native_error_blocks
    (input : resolved.Input) (oracle : NativeOracle resolved input)
    (failure : NativeFailure)
    (failed : oracle (resolved.controllerEntry.controller.issue input) =
      .error failure) :
    DialectClauseDispatch.run resolved input oracle = .blocked failure := by
  exact run_nativeFailure resolved input oracle failure failed

def rustBuildTarget : NativeGlueGen.BuildTarget where
  path := "prover/src/semantic_artifact_arithmetic.rs"
  bundle := artifact
  nativeCatalogWellFormed := artifact_nativeCatalogWellFormed

#eval rustBuildTarget.run

/-- info: 'Minidregg.Compiler.ArithmeticNativeDeployment.honestResponse_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestResponse_accepts
/-- info: 'Minidregg.Compiler.ArithmeticNativeDeployment.emitted_candidate_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emitted_candidate_exact
/-- info: 'Minidregg.Compiler.ArithmeticNativeDeployment.artifact_contains_exact_native_surface' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms artifact_contains_exact_native_surface
/-- info: 'Minidregg.Compiler.ArithmeticNativeDeployment.artifact_nativeCatalogWellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms artifact_nativeCatalogWellFormed
/-- info: 'Minidregg.Compiler.ArithmeticNativeDeployment.registry_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms registry_wellFormed
/-- info: 'Minidregg.Compiler.ArithmeticNativeDeployment.resolved_controller_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_controller_exact
/-- info: 'Minidregg.Compiler.ArithmeticNativeDeployment.honest_bytes_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honest_bytes_certified
/-- info: 'Minidregg.Compiler.ArithmeticNativeDeployment.malformed_bytes_cannot_certify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformed_bytes_cannot_certify
/-- info: 'Minidregg.Compiler.ArithmeticNativeDeployment.native_error_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms native_error_blocks

end Minidregg.Compiler.ArithmeticNativeDeployment
