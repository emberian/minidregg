/- Lower registration admission. Replay supplies any named v1 original from its
same-walk accepted record/receipt; a public caller's `Legacy` is not history
authority. Live Host must use a Verified wrapper before constructing an intent. -/
module

public import Kernel.FnConsumerNamespaceRegistration
public import Kernel.FnConsumerFrontierGateway
public import Kernel.FnConsumerProgressHistory

@[expose] public section

namespace Minidregg.Kernel.FnConsumerNamespaceAdmissionAt

open Minidregg.Kernel
open Minidregg.Kernel.FnConsumerNamespaceRegistration
open Minidregg.Theory
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Legacy where
  record : DurableReceiver.IntentRecord
  receipt : NativeHostCodec.Receipt

def anchorMatches (spec : Spec) (legacy : Option Legacy) : Bool :=
  match legacy with
  | none => spec.legacyAnchor.isNone && spec.initialPosition == 0
  | some prior =>
      match FnConsumerProgress.originalSkipAnyGatewayWithIdentity
          spec.domain spec.semantics prior.record with
      | none => false
      | some original =>
          spec.legacyAnchor == some prior.receipt &&
          prior.record.transactionId == prior.receipt.transactionId &&
          prior.record.event.eventId == prior.receipt.eventId &&
          original.evidence.application == spec.consumerNamespace.application &&
          original.evidence.scope == spec.consumerNamespace.scope &&
          original.evidence.controlBinding == spec.consumerNamespace.controlBinding &&
          original.subject == spec.gatewaySubject &&
          original.target == spec.gatewayTarget &&
          original.capability == spec.gatewayCapability &&
          original.evidence.toPosition == spec.initialPosition

def proposal (ingress : Ingress) : FnConsumerFrontierGateway.Proposal :=
  { domain := ingress.spec.domain
    semantics := ingress.spec.semantics
    application := ingress.spec.consumerNamespace.application
    subject := ingress.spec.gatewaySubject
    target := ingress.spec.gatewayTarget
    capability := ingress.spec.gatewayCapability
    canonicalSpec := specCodec.encode ingress.spec
    expectedAuthorityRoot := ingress.expectedAuthorityRoot
    expectedTargetRoot := ingress.expectedTargetRoot }

structure ConditionalGround (config : NativeHost.Config) (ground : ServedBasis.Ground config.deployment)
    (legacy : Option Legacy) (ingress : Ingress) where
  private mk ::
  anchorExact : anchorMatches ingress.spec legacy = true
  gateway : FnConsumerFrontierGateway.CheckedGround config ground
    (proposal ingress) ingress.gatewayEnvelope

abbrev Conditional (config : NativeHost.Config) (opened : NativeHost.Opened config) :=
  ConditionalGround config (FnConsumerFrontierGateway.contextOf opened)

theorem Conditional.sound {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {legacy : Option Legacy} {ingress : Ingress}
    (conditional : Conditional config opened legacy ingress) :
    anchorMatches ingress.spec legacy = true ∧
    conditional.gateway.signature.signature.envelopeBytes = ingress.gatewayEnvelope ∧
    FnConsumerFrontierGateway.authorize conditional.gateway.prepared
      conditional.gateway.signature.signature = some conditional.gateway.signature.authorization :=
  ⟨conditional.anchorExact, conditional.gateway.signature.envelopeExact,
    conditional.gateway.signature.authorized⟩

def prepareConditionalGround (config : NativeHost.Config) (ground : ServedBasis.Ground config.deployment)
    (legacy : Option Legacy) (ingress : Ingress) :
    IO (Except String (ConditionalGround config ground legacy ingress)) := do
  unless ingress.spec.valid &&
      (ingressCodec.encode ingress).length ≤ 8192 do
    return .error "fn consumer namespace registration refused"
  if anchorExact : anchorMatches ingress.spec legacy = true then
    match ← FnConsumerFrontierGateway.checkGround config ground
        (proposal ingress) ingress.gatewayEnvelope with
    | .error _ => return .error "fn consumer namespace registration refused"
    | .ok gateway => return .ok ⟨anchorExact, gateway⟩
  else return .error "fn consumer namespace registration refused"

def prepareConditional (config : NativeHost.Config) (opened : NativeHost.Opened config) :=
  prepareConditionalGround config (FnConsumerFrontierGateway.contextOf opened)

/-- The turn's charge: it writes nothing, so its storage lane is the World's
storage of its guards and its retained event (`DeployedCharge.storageCharge`). -/
def charge (snap : DataSnapshot ResourceBirthCodec.rootBytes) (guards : List ReadGuard)
    (ingress : Ingress) : ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => (ingressCodec.encode ingress).length
  | .memoryTouches => 1
  | .storageBytes => DeployedCharge.storageCharge snap [] (event ingress)
  | .witnessBytes => (ingressCodec.encode ingress).length
  | .proofWork => 1
  | .sideEffectCount => 1
  | .feeDebit | .networkBytes | .leaseByteBlocks => 0

def ConditionalGround.intent (config : NativeHost.Config) (ground : ServedBasis.Ground config.deployment)
    (legacy : Option Legacy) (ingress : Ingress)
    (accepted : ConditionalGround config ground legacy ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  let guards := FnConsumerFrontierGateway.readGuards accepted.gateway.prepared ++
    ground.authorityReadGuards
  { transactionId := transactionId ingress.spec
    writes := []
    readGuards := guards
    nullifiers := [claimNullifier ingress.spec]
    exactCharge := (Minidregg.Theory.ResourceCost.Charge.materialize
      (charge ground.view guards ingress)).toCharge
    event := event ingress
    subject := some ingress.spec.gatewaySubject
    postRootsBound := by intro write present; cases present
    guardsReadOnly := by intro guard _; simp }

def Conditional.intent (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (legacy : Option Legacy) (ingress : Ingress)
    (accepted : Conditional config opened legacy ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  ConditionalGround.intent config (FnConsumerFrontierGateway.contextOf opened) legacy ingress accepted

end Minidregg.Kernel.FnConsumerNamespaceAdmissionAt
