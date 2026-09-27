/-
Detached source authoring for an app share issue. The operator selects the
ticket, payer and funding, but every birth allocation and signing header is
derived from the currently verified Mini image. Assembly only inserts detached
signatures; native receiving rechecks both branches and the exact final source.
-/
import Kernel.ApplicationShareIssueAdmission
import Kernel.NativeHost

namespace Minidregg.Kernel.ApplicationShareIssueAuthoring
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
  NativeHostCodec.framed "DREGG/APPLICATION/SHARE-ISSUE-REQUEST/v1".toUTF8.toList
    requestStream

structure Plan where
  spec : Spec
  birth : SigningPlan
  appSlot : SigningSlot

private def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product specStream
      (StreamCodec.product signingPlanStream signingSlotStream))
    (fun plan => (plan.spec, plan.birth, plan.appSlot))
    (fun (spec, birth, appSlot) => ⟨spec, birth, appSlot⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan :=
  NativeHostCodec.framed "DREGG/APPLICATION/SHARE-ISSUE-PLAN/v1".toUTF8.toList
    planStream

/-- Derive the ordinary birth draft, its source-generated authority shards,
and the independent app `.delegateObject` signing header from one verified
loaded image. A plan is not an accepted issue or a permission to dispatch. -/
def prepareLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (spec : Spec) (payer : Nat) (funding : List InitialFunding)
    (sourceCapabilities : List CapabilityId) :
    Except String Plan := do
  let profile := config.profile
  let height := NativeHost.logicalHeight config opened.durable
  let .ok ready := ApplicationShareIssueSource.prepare profile config spec
    | throw "share ticket source refused"
  let draft := ready.expectedDescriptor profile config
    opened.authority.snapshot.authState height payer funding
  let .ok prepared := ResourceBirthController.Concrete.prepareDraft
    profile.compilerProfile config.deployment opened.pins opened.durable draft
    | throw "share ticket birth preparation refused"
  let expected := { draft with auxiliaryCreates := prepared.prepared.grants.auxiliaryCreates }
  if CanonicalCellRegistry.sourceEncoding.codec.encode prepared.descriptor !=
      CanonicalCellRegistry.sourceEncoding.codec.encode expected then
    throw "share ticket finalized birth differs from source"
  let .ok _pending := ResourceBirthPolicyController.Concrete.preparePending
    prepared.prepared height | throw "share ticket birth pending refused"
  let birth ← (NativeHost.prepareLoaded config opened
    (.birth (CanonicalCellRegistry.sourceEncoding.codec.encode draft) sourceCapabilities)).mapError
      (fun _ => "share ticket birth signing plan refused")
  match birth.finalizedDraft with
  | .birth finalized capabilities =>
      unless finalized == CanonicalCellRegistry.sourceEncoding.codec.encode
          prepared.descriptor && capabilities == sourceCapabilities do
        throw "share ticket birth plan differs from current source"
  | _ => throw "share ticket plan is not a birth"
  let context : ApplicationShareIssueDelegation.Context config.deployment opened.durable :=
    ⟨prepared.prepared.directory, prepared.prepared.authority⟩
  let .ok app := ApplicationShareIssueDelegation.prepare context profile
    config.federation height spec prepared.descriptor
    | throw "share ticket app preparation refused"
  let wanted : PackedEffectRequest := ⟨.object, app.wanted⟩
  let .ok header := CredentialSignatureAdmission.signingHeader
      prepared.prepared.authority.snapshot
      (ApplicationShareIssueSource.issueMarker spec prepared.descriptor) wanted
    | throw "share ticket app signing key selection refused"
  pure ⟨spec, birth,
    ⟨5, 0, CredentialSignedEnvelopeController.headerCodec.encode header⟩⟩

def prepareRequestLoaded (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (bytes : List UInt8) : Except String Plan := do
  let some request := requestCodec.decode bytes
    | throw "noncanonical share issue authoring request"
  prepareLoaded config opened request.spec request.payer request.funding
    request.sourceCapabilities

/-- Signature order is exactly the returned birth slots followed by the app
slot. Neither detached signatures nor a caller-supplied plan establish native
admission; `ApplicationShareIssueReceiver` re-verifies at the current image. -/
def assemble (plan : Plan) (signatures : List (List UInt8)) : Except String (List UInt8) := do
  if signatures.length != plan.birth.slots.length + 1 then
    throw "share issue signature count mismatch"
  let .ok signed := NativeHost.assemble plan.birth
      (signatures.take plan.birth.slots.length)
    | throw "share ticket birth assembly refused"
  let birthIngress ← match signed with
    | .birth bytes => pure bytes
    | _ => throw "share ticket plan is not a birth"
  let some signature := signatures[plan.birth.slots.length]?
    | throw "missing app delegation signature"
  if signature.length != 64 then
    throw "app delegation signature must be 64 bytes"
  let some header := CredentialSignedEnvelopeController.headerCodec.decode plan.appSlot.header
    | throw "noncanonical app signing header"
  let appEnvelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨header, signature⟩
  pure (ApplicationShareIssueSource.ingressCodec.encode
    ⟨plan.spec, birthIngress, appEnvelope⟩)

end Minidregg.Kernel.ApplicationShareIssueAuthoring
