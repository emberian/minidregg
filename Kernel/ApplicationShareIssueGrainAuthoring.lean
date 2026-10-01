/-
Operator-private current-image authoring for a grain-backed share ticket.
The request selects two already existing grain tasks and their capabilities;
Mini derives their present states/roots, the full ticket birth, the joint
factory/Book/grain command and every signing header. A detached plan is not
admission; the event-22 receiver rechecks all branches on a fresh image.
-/
import Kernel.ApplicationShareIssueGrainAdmission
import Kernel.NativeHost
import Compiler.GrainResourceBirthHostCodec

namespace Minidregg.Kernel.ApplicationShareIssueGrainAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationShareIssueSource
open Minidregg.Kernel.NativeHost

set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local irreducible] NativeHost.Config.profile
  CanonicalRuntimeProfile.Profile.compilerProfile

structure GrainSelector where
  task : Nat
  capability : CapabilityId
  observeCapability : CapabilityId
  deriving DecidableEq, Repr

def selectorStream : StreamCodec GrainSelector :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
        CredentialAuthorityEntryCodec.capabilityIdStream))
    (fun selector => (selector.task, selector.capability, selector.observeCapability))
    (fun (task, capability, observeCapability) =>
      ⟨task, capability, observeCapability⟩)
    (by intro selector; cases selector; rfl)

structure Request where
  spec : Spec
  payer : Nat
  funding : List InitialFunding
  sourceCapabilities : List CapabilityId
  tool : GrainSelector
  parent : GrainSelector
  deriving DecidableEq, Repr

private def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product specStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.list fundingStream)
          (StreamCodec.product
            (StreamCodec.list CredentialAuthorityEntryCodec.capabilityIdStream)
            (StreamCodec.product selectorStream selectorStream)))))
    (fun request => (request.spec, request.payer, request.funding,
      request.sourceCapabilities, request.tool, request.parent))
    (fun (spec, payer, funding, sourceCapabilities, tool, parent) =>
      ⟨spec, payer, funding, sourceCapabilities, tool, parent⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request := NativeHostCodec.framed
  "DREGG/APPLICATION/GRAIN-SHARE-ISSUE-REQUEST/v1".toUTF8.toList requestStream

structure Plan where
  request : Request
  birth : SigningPlan
  appSlot : SigningSlot

private def planStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product requestStream
    (StreamCodec.product signingPlanStream signingSlotStream))
    (fun plan => (plan.request, plan.birth, plan.appSlot))
    (fun (request, birth, appSlot) => ⟨request, birth, appSlot⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan := NativeHostCodec.framed
  "DREGG/APPLICATION/GRAIN-SHARE-ISSUE-PLAN/v1".toUTF8.toList planStream

private def currentAgent (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (task : Nat) :
    Except String (Digest × AgentGrain.State) := do
  let .present cell := opened.directory.directory.slots task
    | throw "grain-backed issue task unavailable"
  match cell with
  | ⟨.declaredObject, payload⟩ =>
      let page := payload.logical
      let some state := AgentGrain.readState task page
        | throw "grain-backed issue task state unavailable"
      return (payload.root, state)
  | _ => throw "grain-backed issue task has wrong resource kind"

private def slot (snapshot : CredentialAuthorityDomain.Snapshot)
    (marker role index : Nat) (wanted : PackedEffectRequest) :
    Except String SigningSlot := do
  let .ok header := CredentialSignatureAdmission.signingHeader snapshot marker wanted
    | throw "grain-backed share signing key selection refused"
  return ⟨role, index, CredentialSignedEnvelopeController.headerCodec.encode header⟩

def prepareLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (request : Request) : Except String Plan := do
  let profile := config.profile
  let height := NativeHost.logicalHeight config opened.durable
  let .ok ready := ApplicationShareIssueSource.prepare profile config request.spec
    | throw "grain-backed share source refused"
  unless opened.pins.tariff == config.tariff do
    throw "grain-backed share factory tariff differs from loaded host"
  let tariff ← config.grainBirthTariffValue
  let birthDraft := ready.expectedDescriptor profile config
    opened.authority.snapshot.authState height request.payer request.funding
  let (toolRoot, toolBefore) ← currentAgent config opened request.tool.task
  let (parentRoot, parentBefore) ← currentAgent config opened request.parent.task
  let source : GrainResourceBirthController.Source :=
    { birth := birthDraft
      toolTask := request.tool.task
      toolCapability := request.tool.capability
      toolObserveCapability := request.tool.observeCapability
      toolRoot := toolRoot
      toolBefore := toolBefore
      parentTask := request.parent.task
      parentCapability := request.parent.capability
      parentObserveCapability := request.parent.observeCapability
      parentRoot := parentRoot
      parentBefore := parentBefore }
  let specialPins := ready.effectivePins opened.pins
  let marker := GrainResourceBirthAdmission.useMarker profile config.deployment tariff source
  let .ok draft := ResourceBirthController.Concrete.prepareGrainDraft
      profile.compilerProfile profile.disabledEvaluators config.deployment specialPins opened.durable birthDraft marker
    | throw "grain-backed share birth preparation refused"
  let source := source.withAuxiliaryCreates draft.descriptor.auxiliaryCreates
  let expected := { birthDraft with auxiliaryCreates := draft.descriptor.auxiliaryCreates }
  unless CanonicalCellRegistry.sourceEncoding.codec.encode source.birth ==
      CanonicalCellRegistry.sourceEncoding.codec.encode expected do
    throw "grain-backed share finalized birth differs from source"
  let .ok birth := GrainResourceBirthController.prepareSourceBirth
      profile.compilerProfile profile.disabledEvaluators config.deployment specialPins opened.durable
      profile.semantics tariff source
    | throw "grain-backed share birth preparation refused"
  let ambient : DeclaredResourceController.Ambient := ⟨config.federation, height⟩
  let .ok grain := GrainResourceBirthTransaction.prepareTargets profile
      config.deployment specialPins opened.durable ambient tariff source birth
    | throw "grain-backed share target preparation refused"
  let .ok _pending := GrainResourceBirthAdmission.preparePending profile
      config.deployment specialPins opened.durable ambient tariff source birth grain
    | throw "grain-backed share tuple preparation refused"
  unless request.sourceCapabilities.length == source.birth.resourceBatch.operations.length do
    throw "grain-backed share source capability count mismatch"
  let marker := GrainResourceBirthAdmission.useMarker profile config.deployment tariff source
  let branches ← (GrainResourceBirthAdmission.branches tariff source).mapM fun branch =>
    let label := NativeHostGrainBirth.branchLabel branch
    slot birth.prepared.pre.authority.snapshot marker label.1 label.2
      (GrainResourceBirthAdmission.branchRequest birth grain height branch)
  let observations ← (List.finRange (source.grainCommand tariff).targets.length).mapM
    fun index => slot birth.prepared.pre.authority.snapshot marker 8 index.val
      ⟨(source.grainCommand tariff).targets[index].kind,
        GrainResourceBirthAdmission.readRequest birth grain index⟩
  let finalized := GrainResourceBirthHostCodec.finalizedCodec.encode
    ⟨GrainResourceBirthHostCodec.sourceCodec.encode source,
      DeclaredResourceController.commandCodec.encode (source.grainCommand tariff)⟩
  let signedBirth : SigningPlan :=
    ⟨config.deployment.domain, profile.semantics,
      opened.durable.worldRoot, height,
      .birth finalized request.sourceCapabilities, branches ++ observations⟩
  let context : ApplicationShareIssueDelegation.Context config.deployment opened.durable :=
    ⟨birth.prepared.pre.directory, birth.prepared.pre.authority⟩
  let .ok app := ApplicationShareIssueDelegation.prepare context profile
      config.federation height request.spec source.birth
    | throw "grain-backed share app preparation refused"
  let .ok header := CredentialSignatureAdmission.signingHeader
      birth.prepared.pre.authority.snapshot
      (ApplicationShareIssueSource.issueMarker request.spec source.birth)
      ⟨.object, app.wanted⟩
    | throw "grain-backed share app signing key selection refused"
  return ⟨request, signedBirth,
    ⟨5, 0, CredentialSignedEnvelopeController.headerCodec.encode header⟩⟩

def prepareRequestLoaded (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (bytes : List UInt8) : Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical grain-backed share request"
  prepareLoaded config opened request

/-- Assembly only binds detached signatures to source-generated headers.
Neither this plan nor its caller's signer assertions can authorize event 22. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  unless signatures.length == plan.birth.slots.length + 1 do
    throw "grain-backed share signature count mismatch"
  let .ok signed := NativeHost.assemble plan.birth
      (signatures.take plan.birth.slots.length)
    | throw "grain-backed share birth assembly refused"
  let .birth grainIngress := signed
    | throw "grain-backed share plan is not a birth"
  let some signature := signatures[plan.birth.slots.length]?
    | throw "missing app delegation signature"
  unless signature.length == 64 do
    throw "app delegation signature must be 64 bytes"
  let some header := CredentialSignedEnvelopeController.headerCodec.decode plan.appSlot.header
    | throw "noncanonical app signing header"
  let appEnvelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨header, signature⟩
  return ApplicationShareIssueGrainSource.codec.encode
    ⟨plan.request.spec, grainIngress, appEnvelope⟩

end Minidregg.Kernel.ApplicationShareIssueGrainAuthoring
