/-
Detached source authoring for an app agent lifetime grant. The operator selects the
ticket, payer and funding, but every birth allocation and signing header is
derived from the currently verified Mini image. Assembly only inserts detached
signatures; native receiving rechecks both branches and the exact final source.
-/
import Kernel.ApplicationAgentLifetimeGrantReceiver

namespace Minidregg.Kernel.ApplicationAgentLifetimeGrantAuthoring
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationAgentLifetimeGrantSource
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel
set_option autoImplicit false

structure Request where
  spec : Spec
  payer : Nat
  funding : List InitialFunding
  sourceCapabilities : List CapabilityId

private def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product specStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.list fundingStream)
          (StreamCodec.list CredentialAuthorityEntryCodec.capabilityIdStream))))
    (fun request =>
      (request.spec, request.payer, request.funding, request.sourceCapabilities))
    (fun (spec, payer, funding, sourceCapabilities) =>
      ⟨spec, payer, funding, sourceCapabilities⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request :=
  NativeHostCodec.framed "DREGG/APPLICATION/AGENT-LIFETIME-ISSUE-REQUEST/v1".toUTF8.toList
    requestStream

structure Plan where
  request : Request
  birth : SigningPlan
  appSlot : SigningSlot

private def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product requestStream
      (StreamCodec.product signingPlanStream signingSlotStream))
    (fun plan => (plan.request, plan.birth, plan.appSlot))
    (fun (request, birth, appSlot) => ⟨request, birth, appSlot⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan :=
  NativeHostCodec.framed "DREGG/APPLICATION/AGENT-LIFETIME-ISSUE-PLAN/v2".toUTF8.toList
    planStream

/-- Derive the ordinary birth draft, its source-generated authority shards,
and the independent app `.delegateObject` signing header from one verified
loaded image. A plan is not an accepted issue or a permission to dispatch. -/
def prepareLoaded {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target)
    (spec : Spec) (payer : Nat) (funding : List InitialFunding)
    (sourceCapabilities : List CapabilityId) :
    Except String Plan := do
  let opened := verified.opened
  let some prior := verified.issues.find? (fun issue =>
      spec.grant.matchesIssued issue.evidence.spec issue.index issue.receipt)
    | throw "agent lifetime grant original event22 issue absent"
  if prior.evidence.record.event.codecVersion != 22 then
    throw "agent lifetime grant source is not an event22 ticket"
  let some original := opened.durable.image.accepted[prior.index]?
    | throw "agent lifetime grant original ticket record absent"
  if DurableReceiverCodec.intentStream.encode original !=
      DurableReceiverCodec.intentStream.encode prior.evidence.record then
    throw "agent lifetime grant original ticket record differs"
  let profile := config.profile
  let height := NativeHost.logicalHeight config opened.durable
  let .ok ready := ApplicationAgentLifetimeGrantSource.prepare profile config spec
    | throw "agent lifetime grant source refused"
  if opened.pins.tariff != config.tariff then
    throw "agent lifetime grant factory tariff differs from loaded host"
  let draft := ready.expectedDescriptor profile config
    opened.authority.snapshot.authState height payer funding
  let .ok prepared := ResourceBirthController.Concrete.prepareDraft
    profile.compilerProfile profile.disabledEvaluators config.deployment opened.pins
      opened.durable draft height ready.sourced
    | throw "agent lifetime grant birth preparation refused"
  let expected := { draft with auxiliaryCreates := prepared.prepared.grants.auxiliaryCreates }
  if CanonicalCellRegistry.sourceEncoding.codec.encode prepared.descriptor !=
      CanonicalCellRegistry.sourceEncoding.codec.encode expected then
    throw "agent lifetime grant finalized birth differs from source"
  let .ok _pending := ResourceBirthPolicyController.Concrete.preparePending
    prepared.prepared height | throw "agent lifetime grant birth pending refused"
  if sourceCapabilities.length != prepared.descriptor.resourceBatch.operations.length then
    throw "agent lifetime grant birth source capability count mismatch"
  let birthSlot := fun (role index : Nat)
      (branch : ResourceBirthPolicyController.Concrete.Branch prepared.descriptor) => do
    let wanted := ResourceBirthPolicyController.Concrete.branchRequest (profile := profile)
      prepared.prepared height branch
    let .ok header := CredentialSignatureAdmission.signingHeader
        prepared.prepared.authority.snapshot prepared.descriptor.authorityNullifier wanted
      | throw "agent lifetime grant birth signing key selection refused"
    pure (⟨role, index, CredentialSignedEnvelopeController.headerCodec.encode header⟩ : SigningSlot)
  let factory ← birthSlot 0 0 .factory
  let authority ← birthSlot 1 0 .authority
  let allocations ← (List.finRange prepared.descriptor.createRequests.length).mapM
    (fun index => birthSlot 2 index.val (.allocation index))
  let sources ← (List.finRange prepared.descriptor.resourceBatch.operations.length).mapM
    (fun index => birthSlot 3 index.val (.source index))
  let birth : SigningPlan :=
    ⟨config.deployment.domain, profile.semantics,
      opened.durable.worldRoot, height,
      .birth (CanonicalCellRegistry.sourceEncoding.codec.encode prepared.descriptor)
        sourceCapabilities,
      factory :: authority :: allocations ++ sources⟩
  let context : ApplicationAgentLifetimeGrantDelegation.Context config.deployment :=
    (Minidregg.Compiler.ServedBasis.Ground.full _ prepared.prepared.directory prepared.prepared.authority)
  let .ok app := ApplicationAgentLifetimeGrantDelegation.prepare context profile
    config.federation height spec prepared.descriptor
    | throw "agent lifetime grant app preparation refused"
  let wanted : PackedEffectRequest := ⟨.object, app.wanted⟩
  let .ok header := CredentialSignatureAdmission.signingHeader
      prepared.prepared.authority.snapshot
      (ApplicationAgentLifetimeGrantSource.issueMarker spec prepared.descriptor) wanted
    | throw "agent lifetime grant app signing key selection refused"
  pure ⟨⟨spec, payer, funding, sourceCapabilities⟩, birth,
    ⟨5, 0, CredentialSignedEnvelopeController.headerCodec.encode header⟩⟩

def prepareRequestLoaded {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical agent lifetime grant authoring request"
  if requestCodec.encode request != bytes then
    throw "noncanonical agent lifetime grant authoring request"
  prepareLoaded verified request.spec request.payer request.funding
    request.sourceCapabilities

/-- Signature order is exactly the returned birth slots followed by the app
slot. Neither detached signatures nor a caller-supplied plan establish native
admission; `ApplicationAgentLifetimeGrantReceiver` re-verifies at the current image. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) : Except String (List UInt8) := do
  if signatures.length != plan.birth.slots.length + 1 then
    throw "agent lifetime grant signature count mismatch"
  let .ok signed := NativeHost.assemble plan.birth
      (signatures.take plan.birth.slots.length)
    | throw "agent lifetime grant birth assembly refused"
  let birthIngress ← match signed with
    | .birth bytes => pure bytes
    | _ => throw "agent lifetime grant plan is not a birth"
  let some signature := signatures[plan.birth.slots.length]?
    | throw "missing app delegation signature"
  if signature.length != 64 then
    throw "app delegation signature must be 64 bytes"
  let some header := CredentialSignedEnvelopeController.headerCodec.decode plan.appSlot.header
    | throw "noncanonical app signing header"
  let appEnvelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨header, signature⟩
  pure (ApplicationAgentLifetimeGrantSource.ingressCodec.encode
    ⟨plan.request.spec, birthIngress, appEnvelope⟩)

/-- A retained plan cannot silently authorize after the image or current app
law changes. The native receiver still checks every signature and the CAS. -/
def assembleCurrent {config : NativeHost.Config} {target : NativeHost.Durable}
    (verified : NativeHostReplay.Verified config target) (plan : Plan)
    (signatures : List (List UInt8)) : Except String (List UInt8) := do
  let fresh ← prepareLoaded verified plan.request.spec plan.request.payer
    plan.request.funding plan.request.sourceCapabilities
  if planCodec.encode fresh != planCodec.encode plan then
    throw "agent lifetime grant plan no longer current"
  assemble fresh signatures

end Minidregg.Kernel.ApplicationAgentLifetimeGrantAuthoring
