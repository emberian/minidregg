/-
# Compiler.ComposableDeploymentManifest -- honest manifest/artifact/controller joins

`Manifest.WellFormed` proves only that first-order registry references close.  It
does not produce executable control, prove a proof system, or supply the
root-indexed evidence consumed by semantic history.  This module keeps those
boundaries separate and gives deployments one constructive rule:

* admitted clauses are projected from actual `ControllerEntry` values;
* packs compose by appending their vocabulary and controller entries;
* a `DeploymentJoin` must separately prove manifest closure and controller
  registry closure, so duplicate resource, clause, or controller identifiers
  prevent construction;
* security-gated and reserved candidates live in a catalog which is never
  projected into the deployed manifest.

The concrete instance closes the local arithmetic clause `406`: an opaque,
fallible native response is only data, and the controller outcome retains the
existing Lean `CertifiedResponse`.  Tower256 LogUp clause `404` remains outside
base V1 and outside this deployed pack.  Its exact remaining controller and
security gates are recorded below; neither its well-formed local manifest nor
its semantic theorem is treated as deployment evidence.
-/

import Compiler.MinidreggV1ArithmeticWork
import Compiler.DialectClauseDispatch
import Compiler.Logup256ReceiptClause
import Compiler.BfvReceiptClause
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Compiler.ComposableDeploymentManifest

open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SemanticArtifactBundle
open Minidregg.Compiler.SemanticManifest
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uInput uQuery uReply uOutcome

/-! ## Implemented controller packs -/

/-- Vocabulary plus executable Lean controller entries contributed by one
deployment component.  There is deliberately no independent clause list:
every admitted clause is projected from an actual controller entry. -/
structure ImplementedControllerPack where
  codecs : List CodecPin := []
  carriers : List CarrierProfile := []
  bridges : List NamedBridgeRequirement := []
  nativeAbiCodecs : List ByteCodecProfile := []
  nativeWorkCatalog : List WorkProfile := []
  entries : List (ControllerEntry.{uInput, uQuery, uReply, uOutcome}) := []

namespace ImplementedControllerPack

/-- The clauses a pack proposes to admit are exactly the declarations carried
by its executable controller entries. -/
def clauses
    (pack : ImplementedControllerPack.{uInput, uQuery, uReply, uOutcome}) :
    List DialectClauseDecl :=
  pack.entries.map ControllerEntry.declaration

/-- Component composition is plain ordered concatenation.  Collision freedom
is not assumed here: constructing the resulting `DeploymentJoin` below must
prove all manifest and controller key uniqueness obligations. -/
def append
    (left right : ImplementedControllerPack.{uInput, uQuery, uReply, uOutcome}) :
    ImplementedControllerPack.{uInput, uQuery, uReply, uOutcome} where
  codecs := left.codecs ++ right.codecs
  carriers := left.carriers ++ right.carriers
  bridges := left.bridges ++ right.bridges
  nativeAbiCodecs := left.nativeAbiCodecs ++ right.nativeAbiCodecs
  nativeWorkCatalog := left.nativeWorkCatalog ++ right.nativeWorkCatalog
  entries := left.entries ++ right.entries

@[simp] theorem append_clauses
    (left right : ImplementedControllerPack.{uInput, uQuery, uReply, uOutcome}) :
    (left.append right).clauses = left.clauses ++ right.clauses := by
  simp [append, clauses]

/-- Extend only the registries owned by a controller pack.  Global manifest
identity/version/program pins remain those of the selected base artifact. -/
def extendManifest
    (pack : ImplementedControllerPack.{uInput, uQuery, uReply, uOutcome})
    (base : Manifest) : Manifest :=
  { base with
    codecs := base.codecs ++ pack.codecs
    carriers := base.carriers ++ pack.carriers
    bridges := base.bridges ++ pack.bridges
    dialectClauses := base.dialectClauses ++ pack.clauses }

def controllerRegistry
    (pack : ImplementedControllerPack.{uInput, uQuery, uReply, uOutcome}) :
    ControllerRegistry.{uInput, uQuery, uReply, uOutcome} :=
  ⟨pack.entries⟩

/-- The artifact carries the exact combined manifest; declarations and phase
order remain projected from the selected base artifact. -/
def extendArtifact
    (pack : ImplementedControllerPack.{uInput, uQuery, uReply, uOutcome})
    (base : ArtifactBundle) : ArtifactBundle :=
  { base with
    manifest := pack.extendManifest base.manifest
    nativeAbiCodecs := base.nativeAbiCodecs ++ pack.nativeAbiCodecs
    nativeWorkCatalog := base.nativeWorkCatalog ++ pack.nativeWorkCatalog }

end ImplementedControllerPack

/-! ## The constructive deployment join -/

/-- A deployment is not merely a well-formed manifest.  It joins one exact
artifact to one executable registry and requires both forms of closure.

Because `ControllerRegistry.WellFormed` covers every manifest clause, callers
cannot use this structure to smuggle a gated or reserved declaration into the
artifact without also supplying a controller entry at its exact two-part key. -/
structure DeploymentJoin where
  artifact : ArtifactBundle
  registry : ControllerRegistry.{uInput, uQuery, uReply, uOutcome}
  manifestWellFormed : artifact.manifest.WellFormed
  nativeCatalogWellFormed : NativeCatalogWellFormed artifact.manifest
    artifact.nativeAbiCodecs artifact.nativeWorkCatalog
  controllerRegistryWellFormed : registry.WellFormed artifact.manifest

namespace DeploymentJoin

/-- Every deployed clause resolves to an actual controller entry.  This is the
implementation evidence which `Manifest.WellFormed` alone cannot provide. -/
theorem controller_for_clause
    (deployment : DeploymentJoin.{uInput, uQuery, uReply, uOutcome})
    (clause : DialectClauseDecl)
    (member : clause ∈ deployment.artifact.manifest.dialectClauses) :
    ∃ entry, deployment.registry.lookup (clauseControllerKey clause) = some entry :=
  deployment.controllerRegistryWellFormed.manifestControllersClosed clause member

theorem clause_ids_unique
    (deployment : DeploymentJoin.{uInput, uQuery, uReply, uOutcome}) :
    deployment.artifact.manifest.ClauseIdsUnique :=
  deployment.manifestWellFormed.dialectClauseIdsUnique

theorem controller_keys_unique
    (deployment : DeploymentJoin.{uInput, uQuery, uReply, uOutcome}) :
    deployment.registry.KeysUnique :=
  deployment.controllerRegistryWellFormed.keysUnique

theorem native_work_ids_unique
    (deployment : DeploymentJoin.{uInput, uQuery, uReply, uOutcome}) :
    (deployment.artifact.nativeWorkCatalog.map WorkProfile.workId).Nodup :=
  deployment.nativeCatalogWellFormed.workIdsUnique

theorem native_abi_codec_ids_unique
    (deployment : DeploymentJoin.{uInput, uQuery, uReply, uOutcome}) :
    (deployment.artifact.nativeAbiCodecs.map ByteCodecProfile.codecId).Nodup :=
  deployment.nativeCatalogWellFormed.nativeAbiCodecIdsUnique

/-- Resolve one deployed clause together with its carrier, codecs, bridges,
and exact executable controller. -/
noncomputable def resolve
    (deployment : DeploymentJoin.{uInput, uQuery, uReply, uOutcome})
    (clauseId : Digest) : Option
      (ResolvedClause deployment.artifact.manifest deployment.registry clauseId) :=
  DialectClauseDispatch.resolve deployment.artifact.manifest
    deployment.manifestWellFormed deployment.registry
    deployment.controllerRegistryWellFormed clauseId

end DeploymentJoin

/-! ## Candidate maturity is not deployment admission -/

/-- Security/control conditions which must be supplied by an exact deployment,
not inferred from deterministic Lean execution. -/
inductive SecurityGate
  | exactDispatchController
  | exactControllerInputAndReplyCodec
  | towerProfileAndValueCodec
  | nativeBytesDecodedAndRechecked
  | tablePositionBinding
  | checkpointPositionBinding
  | pcsOpeningAndSampledDecider
  | commitmentBinding
  | cshakeAlgorithmAndDomainPins
  | cshakeRandomOracleTransport
  | commonGameFailureBudget
  | semanticHistoryClauseEvidence
deriving DecidableEq, Repr

/-- Deterministic Lean-owned foundations already available to a gated clause.
They are kept separate from cryptographic/security gates. -/
inductive DeterministicFoundation
  | recursiveFanPaarTower256Codec
  | stableTower256BackendPins
  | concreteSp800185Cshake256
  | exactMerkleAndTranscriptDomains
  | exactMerkleCollisionReduction
  | nativeByteDecodeAndRecheck
  | exactLogupControllerSchedule
  | verifiedRunSemanticReduction
  | commonGameAdmissionInterface
deriving DecidableEq, Repr

/-- Reasons why a declaration is only a reservation. -/
inductive ReservationBlocker
  | carrierNotClosed
  | statementCodecUnassigned
  | proofCodecUnassigned
  | proofSuiteUnassigned
  | controllerUnassigned
  | semanticRelationNotConnected
  | historyEvidenceAdapterMissing
deriving DecidableEq, Repr

/-- Honest three-way maturity classification.  Only the `implemented` branch
carries a controller entry; the other branches are catalog data and cannot be
converted into an `ImplementedControllerPack`. -/
inductive ClauseCandidate
  | implemented
      (entry : ControllerEntry.{uInput, uQuery, uReply, uOutcome})
  | securityPremiseGated
      (declaration : DialectClauseDecl)
      (foundations : List DeterministicFoundation)
      (gates : List SecurityGate)
  | reserved
      (declaration : DialectClauseDecl) (blockers : List ReservationBlocker)

def ClauseCandidate.declaration :
    ClauseCandidate.{uInput, uQuery, uReply, uOutcome} → DialectClauseDecl
  | .implemented entry => entry.declaration
  | .securityPremiseGated declaration _ _ => declaration
  | .reserved declaration _ => declaration

/-- Only actual implemented entries project into a controller pack. -/
def implementedEntries :
    List (ClauseCandidate.{uInput, uQuery, uReply, uOutcome}) →
      List (ControllerEntry.{uInput, uQuery, uReply, uOutcome})
  | [] => []
  | .implemented entry :: rest => entry :: implementedEntries rest
  | .securityPremiseGated _ _ _ :: rest => implementedEntries rest
  | .reserved _ _ :: rest => implementedEntries rest

/-! ## Concrete clause 406 dispatch controller -/

open Minidregg.Compiler.MinidreggV1ArithmeticWork

/-- Controller result for the exact generated `0 + 0 = 0` work item.  The
successful constructor retains the response and the proof produced by Lean's
existing descriptor checker. -/
inductive ArithmeticControllerOutcome
  | rejected (failure : NativeKernelPlan.Failure)
  | certified
      (response : KernelResponse arithmeticInstruction)
      (certificate : CertifiedResponse manifest arithmeticInstruction response)

/-- A real `DialectClauseDispatch` controller for clause 406.  The issued
query is fixed to one unit token; the dependent reply type is the exact bounded
response for the Lean-selected instruction. -/
def arithmeticController : DialectController.{0, 0, 0, 0} arithmeticClause where
  Input := Unit
  Query := fun _ => Unit
  Reply := fun _ _ => KernelResponse arithmeticInstruction
  Outcome := fun _ => ArithmeticControllerOutcome
  issue := fun _ => ()
  check := fun _ response =>
    match checkInstruction manifest arithmeticInstruction response with
    | .inl failure => .rejected failure
    | .inr certificate => .certified response certificate

def arithmeticControllerEntry : ControllerEntry.{0, 0, 0, 0} where
  declaration := arithmeticClause
  controller := arithmeticController

/-- The first actual implemented pack.  Its clause list is derived from the
controller entry and its only vocabulary addition is the exact BabyBear
carrier used by the checked descriptor. -/
def arithmeticPack : ImplementedControllerPack.{0, 0, 0, 0} where
  carriers := [babyBearArithmeticCarrier]
  entries := [arithmeticControllerEntry]

@[simp] theorem arithmeticPack_manifest_exact :
    arithmeticPack.extendManifest MinidreggV1Artifact.manifest = manifest := by
  rfl

/-- Concrete artifact selected by this deployment.  The manifest is the exact
clause-406 extension; base declarations and the authenticated native catalog
are retained unchanged. -/
def arithmeticDeploymentArtifact : ArtifactBundle :=
  { MinidreggV1Artifact.bundle with manifest := manifest }

@[simp] theorem arithmeticDeploymentArtifact_manifest :
    arithmeticDeploymentArtifact.manifest = manifest := rfl

@[simp] theorem arithmeticDeploymentArtifact_nativeAbiCodecs :
    arithmeticDeploymentArtifact.nativeAbiCodecs =
      MinidreggV1Artifact.bundle.nativeAbiCodecs := rfl

@[simp] theorem arithmeticDeploymentArtifact_nativeWorkCatalog :
    arithmeticDeploymentArtifact.nativeWorkCatalog =
      MinidreggV1Artifact.bundle.nativeWorkCatalog := rfl

theorem arithmeticDeploymentArtifact_nativeWorkCatalog_raw :
    arithmeticDeploymentArtifact.nativeWorkCatalog =
      MinidreggV1Artifact.nativeWorkCatalog := rfl

theorem arithmeticDeploymentArtifact_lookupCodec (codecId : Digest) :
    arithmeticDeploymentArtifact.manifest.lookupCodec codecId =
      MinidreggV1Artifact.bundle.manifest.lookupCodec codecId := by
  rfl

theorem arithmeticDeploymentArtifact_workCodecClosed_iff
    (codec : ByteCodecProfile) :
    WorkCodecClosed arithmeticDeploymentArtifact.manifest
        arithmeticDeploymentArtifact.nativeAbiCodecs codec ↔
      WorkCodecClosed MinidreggV1Artifact.bundle.manifest
        MinidreggV1Artifact.bundle.nativeAbiCodecs codec := by
  cases codec.registry <;> rfl

def arithmeticRegistry : ControllerRegistry.{0, 0, 0, 0} :=
  arithmeticPack.controllerRegistry

theorem arithmeticRegistry_wellFormed : arithmeticRegistry.WellFormed manifest := by
  constructor
  · change ([clauseControllerKey arithmeticClause] : List ControllerKey).Nodup
    simp
  · intro entry member
    change entry ∈ [arithmeticControllerEntry] at member
    rw [List.mem_singleton] at member
    subst entry
    exact arithmetic_clause_registered
  · intro clause member
    change clause ∈ [arithmeticClause] at member
    rw [List.mem_singleton] at member
    subst clause
    refine ⟨arithmeticControllerEntry, ?_⟩
    simp [arithmeticRegistry, arithmeticPack,
      ImplementedControllerPack.controllerRegistry, ControllerRegistry.lookup,
      arithmeticControllerEntry, ControllerEntry.key, clauseControllerKey]

/-- Extending base V1 with clause 406 and its BabyBear carrier preserves the
artifact-authenticated native catalog.  That catalog currently contains only
the independent Tower256 dot-product work profile; it does not fabricate a
byte transport profile for the typed arithmetic controller. -/
theorem arithmeticNativeCatalog_wellFormed :
    NativeCatalogWellFormed arithmeticDeploymentArtifact.manifest
      arithmeticDeploymentArtifact.nativeAbiCodecs
      arithmeticDeploymentArtifact.nativeWorkCatalog := by
  constructor
  · exact MinidreggV1Artifact.bundle_native_catalog_wellFormed.workIdsUnique
  · exact MinidreggV1Artifact.bundle_native_catalog_wellFormed.nativeAbiCodecIdsUnique
  · exact MinidreggV1Artifact.bundle_native_catalog_wellFormed.nativeAbiEntriesScoped
  · intro codec member
    rw [arithmeticDeploymentArtifact_lookupCodec]
    exact MinidreggV1Artifact.bundle_native_catalog_wellFormed
      |>.nativeAbiDisjointManifest codec member
  · intro work member
    rw [arithmeticDeploymentArtifact_nativeWorkCatalog_raw] at member
    have exactWork : work = MinidreggV1Artifact.tower256DotProductWork := by
      simpa [MinidreggV1Artifact.nativeWorkCatalog] using member
    subst work
    exact ⟨MinidreggV1Artifact.gf2Tower256Carrier, by decide⟩
  · intro work member
    apply (arithmeticDeploymentArtifact_workCodecClosed_iff work.requestCodec).mpr
    exact MinidreggV1Artifact.bundle_native_catalog_wellFormed
      |>.requestCodecsClosed work member
  · intro work member
    apply (arithmeticDeploymentArtifact_workCodecClosed_iff work.responseCodec).mpr
    exact MinidreggV1Artifact.bundle_native_catalog_wellFormed
      |>.responseCodecsClosed work member

/-- The concrete combined V1-derived artifact/manifest/controller join. -/
def arithmeticDeployment : DeploymentJoin.{0, 0, 0, 0} where
  artifact := arithmeticDeploymentArtifact
  registry := arithmeticRegistry
  manifestWellFormed := manifest_wellFormed
  nativeCatalogWellFormed := arithmeticNativeCatalog_wellFormed
  controllerRegistryWellFormed := arithmeticRegistry_wellFormed

/-- Constructive dependency resolution for the implemented clause; no
evaluation of the noncomputable option-valued convenience wrapper is needed. -/
noncomputable def arithmeticResolved :
    ResolvedClause arithmeticDeployment.artifact.manifest
      arithmeticDeployment.registry arithmeticClause.clauseId :=
  resolveRegistered arithmeticDeployment.manifestWellFormed
    arithmeticDeployment.controllerRegistryWellFormed
    arithmetic_clause_registered

theorem arithmetic_controller_exact :
    arithmeticResolved.controllerEntry.declaration = arithmeticClause :=
  arithmeticResolved.controllerExact.trans
    (arithmeticDeployment.artifact.manifest.lookupClause_unique
      arithmeticDeployment.manifestWellFormed.dialectClauseIdsUnique
      arithmeticResolved.clauseFound arithmetic_clause_registered)

/-- A certified dispatch outcome carries the exact descriptor theorem; native
bytes never become semantic acceptance without this Lean object. -/
theorem arithmetic_certified_accepts
    {response : KernelResponse arithmeticInstruction}
    {certificate : CertifiedResponse manifest arithmeticInstruction response} :
    arithmeticInstruction.call.Accepts response.totalWires :=
  certificate.descriptorAcceptance

/-! ## Gated and reserved catalog entries -/

/-- Clause 404 has substantial deterministic Lean machinery, including the
proved Tower256 codec, concrete cSHAKE computation, exact controller schedule,
verified-run reduction, and common-game admission theorem.  It is nevertheless
gated on these exact deployment conditions and therefore remains outside the
implemented pack. -/
def tower256LogupCandidate : ClauseCandidate.{0, 0, 0, 0} :=
  .securityPremiseGated Logup256ReceiptClause.clausePin
    [.recursiveFanPaarTower256Codec,
     .stableTower256BackendPins,
     .concreteSp800185Cshake256,
     .exactMerkleAndTranscriptDomains,
     .exactMerkleCollisionReduction,
     .nativeByteDecodeAndRecheck,
     .exactLogupControllerSchedule,
     .verifiedRunSemanticReduction,
     .commonGameAdmissionInterface]
    [.exactDispatchController,
     .exactControllerInputAndReplyCodec,
     .nativeBytesDecodedAndRechecked,
     .tablePositionBinding,
     .checkpointPositionBinding,
     .pcsOpeningAndSampledDecider,
     .commitmentBinding,
     .cshakeRandomOracleTransport,
     .commonGameFailureBudget,
     .semanticHistoryClauseEvidence]

/-- The gated catalog points at the one shared backend owned by
`Tower256ConcreteBackend`; no deployment-local constants are copied. -/
theorem tower256_backend_pins_exact :
    Tower256ConcreteBackend.backend.cshake.algorithmId =
        Tower256ConcreteBackend.cshakeAlgorithmId ∧
    Tower256ConcreteBackend.backend.cshake.digestCodecPin =
        Tower256ConcreteBackend.digestCodecPin ∧
    Tower256ConcreteBackend.backend.merkle.suiteId =
        Tower256ConcreteBackend.merkleSuiteId :=
  ⟨Tower256ConcreteBackend.cshakeAlgorithmExact,
   Tower256ConcreteBackend.digestCodecPinExact,
   Tower256ConcreteBackend.merkleSuiteExact⟩

/-- The BFV buffer admission controller is real Lean computation, but its
clause still carries zero proof-codec/proof-suite sentinels and is not a closed
proof-system deployment declaration. -/
def bfvCandidate : ClauseCandidate.{0, 0, 0, 0} :=
  .reserved BfvReceiptClause.bfvClauseDecl
    [.carrierNotClosed, .proofCodecUnassigned, .proofSuiteUnassigned,
     .controllerUnassigned,
     .semanticRelationNotConnected, .historyEvidenceAdapterMissing]

def candidateCatalog : List (ClauseCandidate.{0, 0, 0, 0}) :=
  [.implemented arithmeticControllerEntry, tower256LogupCandidate, bfvCandidate]

theorem candidate_ids_unique :
    (candidateCatalog.map ClauseCandidate.declaration |>.map
      DialectClauseDecl.clauseId).Nodup := by
  decide

theorem candidate_projection_exact :
    implementedEntries candidateCatalog = [arithmeticControllerEntry] := by
  rfl

/-- Extension-only LogUp clause 404 is absent from base V1. -/
theorem tower256Logup_absent_from_base :
    MinidreggV1Artifact.manifest.lookupClause
      Logup256ReceiptClause.clausePin.clauseId = none := by
  decide

/-- It is also absent from the concrete combined deployment.  Cataloguing a
gated clause cannot admit it. -/
theorem tower256Logup_absent_from_deployment :
    arithmeticDeployment.artifact.manifest.lookupClause
      Logup256ReceiptClause.clausePin.clauseId = none := by
  decide

/-- By contrast, the implemented arithmetic clause is present and resolves
through the joined controller registry. -/
theorem arithmetic_present_in_deployment :
    arithmeticDeployment.artifact.manifest.lookupClause arithmeticClause.clauseId =
      some arithmeticClause := by
  decide

/-! ## Exact residual boundary for history and hash deployment

`Sp800185Cshake256.controller` is executable Lean and proves exact 32-byte
reply checking, but `Manifest` has no hash-service registry which binds an
algorithm identifier, customization domains, and digest codec to a deployed
controller.  Consequently cSHAKE is evidence used by a future gated clause,
not an independently admitted dialect here.

Likewise, `SemanticHistoryAccumulator.ClauseEvidenceFamily` is indexed by the
resolved controller and the exact statement/proof roots.  A deployment join
does not fabricate such a family: each implemented clause must still provide
its own history adapter before its roots can occur in `VerifiedEntry`.
-/

#print axioms arithmeticRegistry_wellFormed
#print axioms arithmeticNativeCatalog_wellFormed
#print axioms arithmetic_controller_exact
#print axioms arithmetic_certified_accepts
#print axioms tower256_backend_pins_exact
#print axioms tower256Logup_absent_from_deployment

end Minidregg.Compiler.ComposableDeploymentManifest
