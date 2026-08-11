/-
# Compiler.FramedWalRecoveryDeployment -- authenticated recovery deployment join

`FramedWalRecoveryController` checks recovery bytes, but a controller value by
itself does not say which extension artifact or registry selected it.  This
module closes that deployment join without assigning the opaque reader any
storage or database semantics.

The extension artifact carries a separate, recovery-specific work declaration.
It pins the empty request, the framed reply shape, both semantic codec pins, and
the exact controller/domain/codec bytes.  This is intentionally not encoded as
`NativeKernelPlan.WorkProfile`: the closed native kernel vocabulary has no WAL
reader, and inventing one would be a false Rust or OS refinement claim.

The generic native catalog remains byte-for-byte the V1 catalog.  Reader or
transport failure blocks dispatch.  Successful bytes are still checked by Lean,
which alone constructs `VerifiedRecovery`.
-/
import Compiler.ComposableDeploymentManifest
import Compiler.FramedWalRecoveryController

namespace Minidregg.Compiler.FramedWalRecoveryDeployment

open Minidregg.Compiler.ComposableDeploymentManifest
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.FramedWalRecoveryController
open Minidregg.Compiler.SemanticArtifactBundle
open Minidregg.Compiler.SemanticManifest
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

namespace Recovery

def id (value : Nat) : Digest := ⟨value⟩

def requestCodec : CodecPin := ⟨id 9501, id 19501, 1⟩
def replyCodec : CodecPin := ⟨id 9502, id 19502, 1⟩

/-- A byte alphabet for the recovery relation.  This declares only the
first-order carrier used by the clause; it is not a field implementation or a
claim about how a filesystem stores the byte stream. -/
def byteCarrier : CarrierProfile :=
  .gf2Tower (id 9503) (id 19503) (id 19504) replyCodec.codecId 8

def clause : DialectClauseDecl where
  clauseId := id 9504
  relationId := id 19505
  carrierProfileId := byteCarrier.id
  statementCodecId := requestCodec.codecId
  proofCodecId := replyCodec.codecId
  proofSuiteId := id 19506
  verifierControllerDigest := id 19507
  requiredBridgeIds := []

/-! ## Recovery-specific extension artifact -/

inductive RequestShape where
  | empty
deriving DecidableEq, Repr

/-- Fixed-width wire facts consumed by the executable Lean decoder. -/
structure ReplyShape where
  outerHeaderBytes : Nat
  frameBytes : Nat
  frameMagicBytes : Nat
  frameVersionBytes : Nat
  payloadBytes : Nat
  checksumBytes : Nat
deriving DecidableEq, Repr

def requestShape : RequestShape := .empty

def replyShape : ReplyShape where
  outerHeaderBytes := 3
  frameBytes := ClosedInstance.controller.pins.frameWidth
  frameMagicBytes := 1
  frameVersionBytes := 1
  payloadBytes := 3
  checksumBytes := 1

/-- Recovery work is transport data, not a native kernel work profile.  All
routing bytes and both semantic codec identities are authenticated together. -/
structure WorkDeclaration where
  workId : Digest
  clauseId : Digest
  requestCodec : CodecPin
  replyCodec : CodecPin
  requestShape : RequestShape
  replyShape : ReplyShape
  controllerPins : Pins
deriving DecidableEq, Repr

def work : WorkDeclaration where
  workId := id 9508
  clauseId := clause.clauseId
  requestCodec := requestCodec
  replyCodec := replyCodec
  requestShape := requestShape
  replyShape := replyShape
  controllerPins := ClosedInstance.controller.pins

/-- Companion first-order data for the ordinary semantic artifact.  Keeping
this separate avoids pretending the closed native work enum contains a WAL
reader while still making the byte declaration part of the selected extension
package. -/
structure ExtensionArtifact where
  bundle : ArtifactBundle
  recoveryWork : List WorkDeclaration
deriving DecidableEq, Repr

def lookupWork (artifact : ExtensionArtifact) (workId : Digest) :
    Option WorkDeclaration :=
  artifact.recoveryWork.find? fun candidate => decide (candidate.workId = workId)

/-- Resolution authenticates the caller-selected work key and all routing and
shape pins before dispatch. -/
def resolveWork (artifact : ExtensionArtifact) (workId : Digest)
    (pins : Pins) (requestPin replyPin : CodecPin)
    (requestBytes : List UInt8) : Option WorkDeclaration := do
  let candidate ← lookupWork artifact workId
  if candidate.controllerPins = pins ∧
      candidate.requestCodec = requestPin ∧
      candidate.replyCodec = replyPin ∧
      candidate.requestShape = .empty ∧ requestBytes = [] then
    some candidate
  else
    none

/-! ## Executable Lean controller -/

inductive Outcome (checkpoint : DataSnapshot ClosedInstance.DataWitness.lengthRoot)
  | rejected (failure : Failure Unit)
  | verified (recovery : VerifiedRecovery ClosedInstance.controller checkpoint)

/-- The opaque boundary receives exactly the empty byte request and may return
only bytes.  The check phase reruns the complete Lean recovery controller. -/
def controller : DialectController.{0, 0, 0, 0} clause where
  Input := DataSnapshot ClosedInstance.DataWitness.lengthRoot
  Query := fun _ => List UInt8
  Reply := fun _ _ => List UInt8
  Outcome := Outcome
  issue := fun _ => []
  check := fun checkpoint bytes =>
    match FramedWalRecoveryController.run ClosedInstance.controller checkpoint
        (fun _ : Unit => .ok bytes) () with
    | .error failure => .rejected failure
    | .ok verified => .verified verified

def entry : ControllerEntry.{0, 0, 0, 0} where
  declaration := clause
  controller := controller

def pack : ImplementedControllerPack.{0, 0, 0, 0} where
  codecs := [requestCodec, replyCodec]
  carriers := [byteCarrier]
  entries := [entry]

def bundle : ArtifactBundle :=
  pack.extendArtifact MinidreggV1Artifact.bundle

def artifact : ExtensionArtifact :=
  ⟨bundle, [work]⟩

def registry : ControllerRegistry.{0, 0, 0, 0} :=
  pack.controllerRegistry

@[simp] theorem base_identity_unchanged :
    bundle.manifest.manifestVersion =
        MinidreggV1Artifact.bundle.manifest.manifestVersion ∧
      bundle.manifest.abiId = MinidreggV1Artifact.bundle.manifest.abiId ∧
      bundle.manifest.semanticProgramId =
        MinidreggV1Artifact.bundle.manifest.semanticProgramId ∧
      bundle.manifest.semanticRelationId =
        MinidreggV1Artifact.bundle.manifest.semanticRelationId := by
  decide

@[simp] theorem base_native_catalog_unchanged :
    bundle.nativeAbiCodecs = MinidreggV1Artifact.bundle.nativeAbiCodecs ∧
      bundle.nativeWorkCatalog =
        MinidreggV1Artifact.bundle.nativeWorkCatalog := by
  constructor <;> rfl

theorem manifest_wellFormed : bundle.manifest.WellFormed := by
  constructor
  · change (MinidreggV1Artifact.codecRegistry.map CodecPin.codecId ++
      [requestCodec.codecId, replyCodec.codecId]).Nodup
    decide
  · change (MinidreggV1Artifact.carrierRegistry.map CarrierProfile.id ++
      [byteCarrier.id]).Nodup
    decide
  · exact MinidreggV1Artifact.manifest_wellFormed.bridgeIdsUnique
  · change ([clause.clauseId] : List Digest).Nodup
    simp
  · exact MinidreggV1Artifact.manifest_wellFormed.receiptCodecClosed
  · intro profile member
    change profile ∈
      [MinidreggV1Artifact.gf2Carrier,
       MinidreggV1Artifact.ext6Carrier,
       MinidreggV1Artifact.residueRingCarrier,
       MinidreggV1Artifact.mpcCarrier,
       MinidreggV1Artifact.gf2Tower256Carrier,
       byteCarrier] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · trivial
    · exact ⟨MinidreggV1Artifact.gf2Carrier, by decide⟩
    · trivial
    · trivial
  · intro bridge member
    change bridge ∈
      [MinidreggV1Artifact.gf2ToExt6Bridge,
       MinidreggV1Artifact.ext6ToResidueRingBridge] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact
        ⟨⟨MinidreggV1Artifact.gf2Carrier, by decide⟩,
         ⟨MinidreggV1Artifact.ext6Carrier, by decide⟩,
         ⟨MinidreggV1Artifact.gf2ValueCodec, by decide⟩,
         ⟨MinidreggV1Artifact.ext6ValueCodec, by decide⟩⟩
    · exact
        ⟨⟨MinidreggV1Artifact.ext6Carrier, by decide⟩,
         ⟨MinidreggV1Artifact.residueRingCarrier, by decide⟩,
         ⟨MinidreggV1Artifact.ext6ValueCodec, by decide⟩,
         ⟨MinidreggV1Artifact.residueRingValueCodec, by decide⟩⟩
  · intro registered member
    change registered ∈ [clause] at member
    rw [List.mem_singleton] at member
    subst registered
    exact
      ⟨⟨byteCarrier, by decide⟩,
       ⟨requestCodec, by decide⟩,
       ⟨replyCodec, by decide⟩,
       by simp [clause]⟩

theorem registry_wellFormed : registry.WellFormed bundle.manifest := by
  constructor
  · change ([clauseControllerKey clause] : List ControllerKey).Nodup
    simp
  · intro registered member
    change registered ∈ [entry] at member
    rw [List.mem_singleton] at member
    subst registered
    decide
  · intro registered member
    change registered ∈ [clause] at member
    rw [List.mem_singleton] at member
    subst registered
    refine ⟨entry, ?_⟩
    rfl

theorem nativeCatalog_wellFormed :
    NativeCatalogWellFormed bundle.manifest bundle.nativeAbiCodecs
      bundle.nativeWorkCatalog := by
  constructor
  · exact MinidreggV1Artifact.bundle_native_catalog_wellFormed.workIdsUnique
  · exact MinidreggV1Artifact.bundle_native_catalog_wellFormed
      |>.nativeAbiCodecIdsUnique
  · exact MinidreggV1Artifact.bundle_native_catalog_wellFormed
      |>.nativeAbiEntriesScoped
  · intro codec member
    have exactCodec : codec = MinidreggV1Artifact.tower256DotProductRequestCodec := by
      simpa [bundle, pack, ImplementedControllerPack.extendArtifact,
        MinidreggV1Artifact.bundle, ArtifactBundle.ofDeclarations,
        MinidreggV1Artifact.nativeAbiCodecRegistry] using member
    subst codec
    decide
  · intro nativeWork member
    have exactWork : nativeWork = MinidreggV1Artifact.tower256DotProductWork := by
      simpa [bundle, pack, ImplementedControllerPack.extendArtifact,
        MinidreggV1Artifact.bundle, ArtifactBundle.ofDeclarations,
        MinidreggV1Artifact.nativeWorkCatalog] using member
    subst nativeWork
    exact ⟨MinidreggV1Artifact.gf2Tower256Carrier, by decide⟩
  · intro nativeWork member
    have exactWork : nativeWork = MinidreggV1Artifact.tower256DotProductWork := by
      simpa [bundle, pack, ImplementedControllerPack.extendArtifact,
        MinidreggV1Artifact.bundle, ArtifactBundle.ofDeclarations,
        MinidreggV1Artifact.nativeWorkCatalog] using member
    subst nativeWork
    change lookupNativeAbiCodec [MinidreggV1Artifact.tower256DotProductRequestCodec]
      9001 = some MinidreggV1Artifact.tower256DotProductRequestCodec
    rfl
  · intro nativeWork member
    have exactWork : nativeWork = MinidreggV1Artifact.tower256DotProductWork := by
      simpa [bundle, pack, ImplementedControllerPack.extendArtifact,
        MinidreggV1Artifact.bundle, ArtifactBundle.ofDeclarations,
        MinidreggV1Artifact.nativeWorkCatalog] using member
    subst nativeWork
    change bundle.manifest.lookupCodec MinidreggV1Artifact.tower256ValueCodec.codecId =
      some MinidreggV1Artifact.tower256ValueCodec
    decide

/-- Exact selected artifact/registry join. -/
def deployment : DeploymentJoin.{0, 0, 0, 0} where
  artifact := bundle
  registry := registry
  manifestWellFormed := manifest_wellFormed
  nativeCatalogWellFormed := nativeCatalog_wellFormed
  controllerRegistryWellFormed := registry_wellFormed

/-! ## Exact resolution and deployment teeth -/

theorem clause_registered :
    bundle.manifest.lookupClause clause.clauseId = some clause := by
  decide

/-- A fully constructive registered resolution keeps the concrete dependent
controller visible for executable teeth. -/
def resolved : ResolvedClause bundle.manifest registry clause.clauseId where
  clause := clause
  clauseFound := clause_registered
  carrier := byteCarrier
  carrierFound := by decide
  statementCodec := requestCodec
  statementCodecFound := by decide
  proofCodec := replyCodec
  proofCodecFound := by decide
  bridges := fun bridgeId member => by simp [clause] at member
  controllerEntry := entry
  controllerFound := rfl
  controllerExact := rfl

/-- The deployment join extended with the recovery-specific first-order work
catalog.  These fields are the load-bearing cross-registry equalities: the
selected semantic bundle, exact clause controller, semantic codec pins, wire
shapes, and controller routing bytes must all agree. -/
structure JoinedDeployment where
  extensionArtifact : ExtensionArtifact
  semantic : DeploymentJoin.{0, 0, 0, 0}
  selectedWork : WorkDeclaration
  bundleJoined : extensionArtifact.bundle = semantic.artifact
  workFound : lookupWork extensionArtifact selectedWork.workId = some selectedWork
  workClauseExact : selectedWork.clauseId = clause.clauseId
  requestCodecFound :
    semantic.artifact.manifest.lookupCodec selectedWork.requestCodec.codecId =
      some selectedWork.requestCodec
  replyCodecFound :
    semantic.artifact.manifest.lookupCodec selectedWork.replyCodec.codecId =
      some selectedWork.replyCodec
  controllerFound :
    semantic.registry.lookup (clauseControllerKey clause) = some entry
  controllerPinsExact :
    selectedWork.controllerPins = ClosedInstance.controller.pins
  requestShapeExact : selectedWork.requestShape = .empty
  replyShapeExact : selectedWork.replyShape = replyShape

def joined : JoinedDeployment where
  extensionArtifact := artifact
  semantic := deployment
  selectedWork := work
  bundleJoined := rfl
  workFound := rfl
  workClauseExact := rfl
  requestCodecFound := by decide
  replyCodecFound := by decide
  controllerFound := rfl
  controllerPinsExact := rfl
  requestShapeExact := rfl
  replyShapeExact := rfl

@[simp] theorem joined_byte_shapes_exact :
    joined.selectedWork.requestShape = .empty ∧
      joined.selectedWork.replyShape.outerHeaderBytes = 3 ∧
      joined.selectedWork.replyShape.frameBytes = 6 ∧
      joined.selectedWork.replyShape.payloadBytes = 3 ∧
      joined.selectedWork.replyShape.checksumBytes = 1 := by
  decide

@[simp] theorem joined_routing_pins_exact :
    joined.selectedWork.controllerPins.controllerId = 161 ∧
      joined.selectedWork.controllerPins.domainId = 73 ∧
      joined.selectedWork.controllerPins.codecId = 29 := by
  decide

@[simp] theorem exact_work_resolves :
    resolveWork artifact work.workId ClosedInstance.controller.pins
      requestCodec replyCodec [] = some work := by
  rfl

@[simp] theorem wrong_work_rejected :
    resolveWork artifact (id 9999) ClosedInstance.controller.pins
      requestCodec replyCodec [] = none := by
  rfl

@[simp] theorem wrong_pin_rejected :
    resolveWork artifact work.workId
      { ClosedInstance.controller.pins with controllerId := 0 }
      requestCodec replyCodec [] = none := by
  rfl

@[simp] theorem wrong_request_shape_rejected :
    resolveWork artifact work.workId ClosedInstance.controller.pins
      requestCodec replyCodec [1] = none := by
  rfl

@[simp] theorem wrong_reply_codec_rejected :
    resolveWork artifact work.workId ClosedInstance.controller.pins
      requestCodec { replyCodec with version := 2 } [] = none := by
  rfl

@[simp] theorem registered_wrong_controller_bytes_rejected :
    resolved.controllerEntry.controller.check ClosedInstance.DataWitness.before
        ClosedInstance.wrongControllerBytes =
      .rejected (.wire .wrongController) := by
  rfl

@[simp] theorem registered_wrong_domain_bytes_rejected :
    resolved.controllerEntry.controller.check ClosedInstance.DataWitness.before
        ClosedInstance.wrongDomainBytes =
      .rejected (.wire .wrongDomain) := by
  rfl

@[simp] theorem registered_wrong_codec_bytes_rejected :
    resolved.controllerEntry.controller.check ClosedInstance.DataWitness.before
        ClosedInstance.wrongCodecBytes =
      .rejected (.wire .wrongCodec) := by
  rfl

@[simp] theorem registered_truncated_reply_rejected :
    resolved.controllerEntry.controller.check ClosedInstance.DataWitness.before
        ClosedInstance.truncatedBytes =
      .rejected (.wire .truncatedFrame) := by
  rfl

@[simp] theorem registered_corrupt_reply_rejected :
    resolved.controllerEntry.controller.check ClosedInstance.DataWitness.before
        ClosedInstance.corruptChecksumBytes =
      .rejected (.wire .invalidFrame) := by
  rfl

@[simp] theorem registered_stale_recovery_rejected :
    resolved.controllerEntry.controller.check
        ClosedInstance.DataWitness.afterConcurrentReadMove
        ClosedInstance.honestBytes =
      .rejected (.recovery (.rejected .staleReadGuard)) := by
  rfl

@[simp] theorem reader_failure_blocks :
    DialectClauseDispatch.run resolved ClosedInstance.DataWitness.before
        (fun _ => .error .unavailable) =
      .blocked .unavailable := by
  rfl

/-- **Positive registered path:** exact resolved work, exact registry entry,
opaque returned bytes, Lean decoding, and guarded replay yield the installed
durable snapshot. -/
theorem registered_honest_recovery :
    ∃ verified : VerifiedRecovery ClosedInstance.controller
        ClosedInstance.DataWitness.before,
      DialectClauseDispatch.run resolved ClosedInstance.DataWitness.before
          (fun _ => .ok ClosedInstance.honestBytes) =
        .completed (.verified verified) ∧
      verified.snapshot = DataSnapshot.install ClosedInstance.DataWitness.before
        ClosedInstance.DataWitness.intent := by
  refine ⟨⟨ClosedInstance.honestBytes, [ClosedInstance.DataWitness.intent],
    DataSnapshot.install ClosedInstance.DataWitness.before
      ClosedInstance.DataWitness.intent,
    ClosedInstance.honest_decode, ClosedInstance.honest_replay⟩, rfl, rfl⟩

/-- Reader failure at the lower boundary is likewise never an accepted
recovery, independent of registry resolution. -/
theorem opaque_reader_error_blocks :
    FramedWalRecoveryController.run ClosedInstance.controller
        ClosedInstance.DataWitness.before ClosedInstance.failingReader () =
      .error (.native 404) :=
  ClosedInstance.native_error_blocks

end Recovery

/-! ## Pinned axiom audit -/

/-- info: 'Minidregg.Compiler.FramedWalRecoveryDeployment.Recovery.manifest_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Recovery.manifest_wellFormed
/-- info: 'Minidregg.Compiler.FramedWalRecoveryDeployment.Recovery.registry_wellFormed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Recovery.registry_wellFormed
/-- info: 'Minidregg.Compiler.FramedWalRecoveryDeployment.Recovery.registered_honest_recovery' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Recovery.registered_honest_recovery
/-- info: 'Minidregg.Compiler.FramedWalRecoveryDeployment.Recovery.reader_failure_blocks' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Recovery.reader_failure_blocks

end Minidregg.Compiler.FramedWalRecoveryDeployment
