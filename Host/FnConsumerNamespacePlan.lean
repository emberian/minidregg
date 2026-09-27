/- Conditional event20 authoring from a locally interrogated fn consumer.
The caller must be the restricted native Host route that runs the pinned fn
binary, checks its exact scope/control identity, and supplies its fenced
position/status. These numbers are not portable evidence or remote proof. -/
import Kernel.FnConsumerNamespaceAdmissionAt
import Lean.Data.Json

namespace Minidregg.Host.FnConsumerNamespacePlan

open Lean
open Minidregg.Kernel
open Minidregg.Kernel.FnConsumerNamespaceRegistration
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

def freshSpec (config : NativeHost.Config) (pin : NativeHost.FnGatewayPin)
    (scope : FnConsumerScope.Scope) (controlBinding : List UInt8)
    (observedPosition committedAck : Nat) : Except String Spec := do
  unless config.fnGateway == some pin && observedPosition == 0 &&
      committedAck == 0 do
    throw "fn consumer registration requires the configured gateway at ACK zero"
  let spec : Spec :=
    { domain := config.deployment.domain
      semantics := config.profile.semantics
      consumerNamespace := ⟨pin.application, scope, controlBinding⟩
      gatewaySubject := pin.subject
      gatewayTarget := pin.target
      gatewayCapability := pin.capability
      initialPosition := 0
      legacyAnchor := none }
  unless spec.valid do
    throw "fn consumer namespace registration exceeds strict profile"
  pure spec

/-- The retained source-owned signing plan. Main obtains all fields from one
verified Mini prefix and one fenced native fn position/status query. -/
structure Plan where
  spec : Spec
  expectedAuthorityRoot : Digest
  expectedTargetRoot : Digest
  signingHeader : List UInt8
  deriving DecidableEq, Repr

def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product specStream
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream bytesStream)))
    (fun plan => (plan.spec, plan.expectedAuthorityRoot,
      plan.expectedTargetRoot, plan.signingHeader))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/FN/CONSUMER-NAMESPACE-PLAN/v1".toUTF8.toList
      planStream)

theorem plan_decode_encode (plan : Plan) :
    planCodec.decode (planCodec.encode plan) = some plan :=
  planCodec.decode_encode plan

def unsignedIngress (spec : Spec) (expectedAuthorityRoot expectedTargetRoot :
    Digest) : Ingress :=
  ⟨spec, [], expectedAuthorityRoot, expectedTargetRoot⟩

/-- Context bytes committed by the source-owned gateway request. These are
not themselves the credential signature preimage. -/
def contextBytes (spec : Spec) (expectedAuthorityRoot expectedTargetRoot :
    Digest) : List UInt8 :=
  FnConsumerFrontierGateway.signingBytes
    (FnConsumerNamespaceAdmissionAt.proposal
      (unsignedIngress spec expectedAuthorityRoot expectedTargetRoot))

/-- Select the actual current authority key/header for the gateway request.
The caller must already have fenced the native fn status and position; this
function independently checks the current Mini gateway law and target root. -/
def prepareSigningHeader (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (spec : Spec)
    (expectedAuthorityRoot expectedTargetRoot : Digest) : Except String (List UInt8) := do
  unless spec.valid && spec.legacyAnchor.isNone && spec.initialPosition == 0 do
    throw "fn consumer fresh registration spec refused"
  let ingress := unsignedIngress spec expectedAuthorityRoot expectedTargetRoot
  let proposal := FnConsumerNamespaceAdmissionAt.proposal ingress
  let some pin := config.fnGateway
    | throw "fn consumer gateway is not configured"
  let .ok () := FnGatewayPolicy.checkCurrent config opened pin
    | throw "fn consumer gateway current law refused"
  let .ok prepared := FnConsumerFrontierGateway.prepare
      (FnConsumerFrontierGateway.contextOf opened) config.profile config.federation
      (NativeHost.logicalHeight config opened.durable) pin proposal
    | throw "fn consumer registration target or pin refused"
  let wanted : PackedEffectRequest :=
    ⟨.object, prepared.wanted⟩
  let .ok header := CredentialSignatureAdmission.signingHeader
      opened.authority.snapshot (FnConsumerFrontierGateway.marker proposal) wanted
    | throw "fn consumer gateway signing key unavailable"
  pure (CredentialSignedEnvelopeController.headerCodec.encode header)

/-- The authority guard is the durable outer root; the gateway request's
target pre-state root is the selected content cell's logical root. The lower
gateway preparation separately proves that cell's outer root is current. -/
def currentRoots (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (pin : NativeHost.FnGatewayPin) : Except String (Digest × Digest) := do
  let authorityRoot := opened.durable.snapshot.model.roots
    config.deployment.authorityAnchor.catalogueCellId
  let probe : DeclaredResourceController.Target :=
    ⟨.object, pin.target, pin.capability, 1, ⟨0⟩, .content ⟨[]⟩, none⟩
  let .present cell := opened.directory.directory.slots pin.target
    | throw "fn consumer namespace target is absent"
  let some pre := DeclaredResourceController.selectTarget config.deployment probe cell
    | throw "fn consumer namespace target is not valid content"
  pure (authorityRoot, pre.root)

def prepare (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (pin : NativeHost.FnGatewayPin) (scope : FnConsumerScope.Scope)
    (controlBinding : List UInt8) (observedPosition committedAck : Nat) :
    Except String Plan := do
  let spec ← freshSpec config pin scope controlBinding observedPosition committedAck
  let (expectedAuthorityRoot, expectedTargetRoot) ← currentRoots config opened pin
  let header ← prepareSigningHeader config opened spec
    expectedAuthorityRoot expectedTargetRoot
  let plan : Plan := ⟨spec, expectedAuthorityRoot, expectedTargetRoot, header⟩
  unless !header.isEmpty && header.length ≤ 4096 &&
      (planCodec.encode plan).length ≤ 8192 do
    throw "fn consumer namespace signing plan exceeds strict profile"
  pure plan

def checkCurrent (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (plan : Plan) : Except String Unit := do
  let some pin := config.fnGateway
    | throw "fn consumer gateway is not configured"
  let expected ← freshSpec config pin plan.spec.consumerNamespace.scope
    plan.spec.consumerNamespace.controlBinding 0 0
  unless expected == plan.spec do
    throw "fn consumer namespace signing plan gateway changed"
  let roots ← currentRoots config opened pin
  unless roots == (plan.expectedAuthorityRoot, plan.expectedTargetRoot) do
    throw "fn consumer namespace signing plan roots changed"
  let header ← prepareSigningHeader config opened plan.spec
    plan.expectedAuthorityRoot plan.expectedTargetRoot
  unless header == plan.signingHeader do
    throw "fn consumer namespace signing plan no longer current"

def assemble (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (plan : Plan) (gatewayEnvelope : List UInt8) : Except String Ingress := do
  checkCurrent config opened plan
  let ingress : Ingress :=
    ⟨plan.spec, gatewayEnvelope, plan.expectedAuthorityRoot, plan.expectedTargetRoot⟩
  unless plan.spec.valid && plan.spec.legacyAnchor.isNone &&
      plan.spec.initialPosition == 0 &&
      !plan.signingHeader.isEmpty && plan.signingHeader.length ≤ 4096 &&
      (planCodec.encode plan).length ≤ 8192 &&
      !gatewayEnvelope.isEmpty &&
      gatewayEnvelope.length ≤ 4096 &&
      (ingressCodec.encode ingress).length ≤ 8192 do
    throw "fn consumer registration envelope exceeds strict profile"
  pure ingress

/-- Custody returns only a detached Ed25519 signature. The Host alone authors
the credential envelope wire from the retained exact signing header. -/
def assembleSignature (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (plan : Plan)
    (signature : List UInt8) : Except String Ingress := do
  unless signature.length == 64 do
    throw "fn consumer gateway signature must contain exactly 64 bytes"
  let some header := CredentialSignedEnvelopeController.headerCodec.decode
      plan.signingHeader
    | throw "fn consumer namespace signing header is not canonical"
  unless CredentialSignedEnvelopeController.headerCodec.encode header ==
      plan.signingHeader do
    throw "fn consumer namespace signing header is not canonical"
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨header, signature⟩
  assemble config opened plan envelope

private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then '0'.toNat + n else 'a'.toNat + n - 10)

private def encodeHex (bytes : List UInt8) : String :=
  Id.run do
    let mut output := ByteArray.empty
    for byte in bytes do
      output := output.push (UInt8.ofNat ((hexDigit (byte.toNat / 16)).toNat))
      output := output.push (UInt8.ofNat ((hexDigit (byte.toNat % 16)).toNat))
    return String.fromUTF8! output

/-- Operator display of a canonical retained plan. Decoding this does not
authenticate fn state or authorize admission; only prepare/checkCurrent do. -/
def inspectPlanBytes (bytes : List UInt8) : Except String Lean.Json := do
  unless !bytes.isEmpty && bytes.length ≤ 8192 do
    throw "fn consumer namespace plan exceeds strict frame"
  let some plan := planCodec.decode bytes
    | throw "fn consumer namespace plan is not canonical"
  unless planCodec.encode plan == bytes && plan.spec.valid &&
      plan.spec.initialPosition == 0 && plan.spec.legacyAnchor.isNone &&
      !plan.signingHeader.isEmpty && plan.signingHeader.length ≤ 4096 do
    throw "fn consumer namespace plan is not fresh or canonical"
  let some header := CredentialSignedEnvelopeController.headerCodec.decode
      plan.signingHeader
    | throw "fn consumer namespace signing header is not canonical"
  unless CredentialSignedEnvelopeController.headerCodec.encode header ==
      plan.signingHeader do
    throw "fn consumer namespace signing header is not canonical"
  let scope := plan.spec.consumerNamespace.scope
  let identity := (Sp800185Cshake256.hash
    "DREGG/FN/CONSUMER-NAMESPACE-PLAN-IDENTITY/v1".toUTF8.toList bytes).digest
  pure <| Lean.Json.mkObj
    [("type", toJson "fn-consumer-namespace-plan-v1")
    ,("canonicalPlanHex", toJson (encodeHex bytes))
    ,("planIdentity", toJson (Nat.repr identity.value))
    ,("domain", toJson (Nat.repr plan.spec.domain.value))
    ,("semantics", toJson (Nat.repr plan.spec.semantics.value))
    ,("applicationHex", toJson (encodeHex plan.spec.consumerNamespace.application))
    ,("historyHex", toJson (encodeHex scope.history))
    ,("incarnationHex", toJson (encodeHex scope.incarnation))
    ,("consumerHex", toJson (encodeHex scope.consumer))
    ,("principalHex", toJson (encodeHex scope.principal))
    ,("queryHex", toJson (encodeHex scope.query))
    ,("queryVersion", toJson (Nat.repr scope.queryVersion))
    ,("viewVersion", toJson (Nat.repr scope.viewVersion))
    ,("registrationEpoch", toJson (Nat.repr scope.registrationEpoch))
    ,("controlBindingHex", toJson (encodeHex plan.spec.consumerNamespace.controlBinding))
    ,("gatewaySubject", toJson (Nat.repr plan.spec.gatewaySubject.value))
    ,("gatewayTarget", toJson (Nat.repr plan.spec.gatewayTarget))
    ,("gatewayCapability", toJson (Nat.repr plan.spec.gatewayCapability.value))
    ,("expectedAuthorityRoot", toJson (Nat.repr plan.expectedAuthorityRoot.value))
    ,("expectedTargetRoot", toJson (Nat.repr plan.expectedTargetRoot.value))
    ,("signingKeyId", toJson (Nat.repr header.keyId))
    ,("signingKeyEpoch", toJson (Nat.repr header.keyEpoch))
    ,("signingAlgorithm", toJson (Nat.repr header.algorithm))
    ,("signingAuthorityRoot", toJson (Nat.repr header.authorityRoot.value))
    ,("signingHeaderHex", toJson (encodeHex plan.signingHeader))]

end Minidregg.Host.FnConsumerNamespacePlan
