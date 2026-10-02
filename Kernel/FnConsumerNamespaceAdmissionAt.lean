/- Lower registration admission. Replay supplies any named v1 original from its
same-walk accepted record/receipt; a public caller's `Legacy` is not history
authority. Live Host must use a Verified wrapper before constructing an intent. -/
import Kernel.FnConsumerNamespaceRegistration
import Kernel.FnConsumerFrontierGateway
import Kernel.FnConsumerProgressHistory

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

structure Conditional (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (legacy : Option Legacy) (ingress : Ingress) where
  private mk ::
  anchorExact : anchorMatches ingress.spec legacy = true
  gateway : FnConsumerFrontierGateway.CheckedOpened config opened
    (proposal ingress) ingress.gatewayEnvelope

def prepareConditional (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (legacy : Option Legacy) (ingress : Ingress) :
    IO (Except String (Conditional config opened legacy ingress)) := do
  unless ingress.spec.valid &&
      (ingressCodec.encode ingress).length ≤ 8192 do
    return .error "fn consumer namespace registration refused"
  if anchorExact : anchorMatches ingress.spec legacy = true then
    match ← FnConsumerFrontierGateway.checkOpened config opened
        (proposal ingress) ingress.gatewayEnvelope with
    | .error _ => return .error "fn consumer namespace registration refused"
    | .ok gateway => return .ok ⟨anchorExact, gateway⟩
  else return .error "fn consumer namespace registration refused"

def charge (ingress : Ingress) : ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => (ingressCodec.encode ingress).length
  | .memoryTouches => 1
  | .storageBytes => (ingressCodec.encode ingress).length
  | .witnessBytes => (ingressCodec.encode ingress).length
  | .proofWork => 1
  | .sideEffectCount => 1
  | .feeDebit | .networkBytes | .leaseByteBlocks => 0

def Conditional.intent (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (legacy : Option Legacy) (ingress : Ingress)
    (accepted : Conditional config opened legacy ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  { transactionId := transactionId ingress.spec
    writes := []
    readGuards := FnConsumerFrontierGateway.readGuards accepted.gateway.prepared ++
      opened.authority.readGuards
    nullifiers := [claimNullifier ingress.spec]
    exactCharge := charge ingress
    event := event ingress
    subject := some ingress.spec.gatewaySubject
    postRootsBound := by intro write present; cases present
    guardsReadOnly := by intro guard _; simp }

end Minidregg.Kernel.FnConsumerNamespaceAdmissionAt
