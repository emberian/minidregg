/-
Lower event19 component admission at a source-owned frontier cursor. Only a
private replay walk or a live Verified wrapper may supply that predecessor;
this function alone does not certify history or an fn poll's completeness.
-/
module

public import Kernel.FnConsumerFrontierProposal
public import Kernel.FnConsumerNamespaceHistory

@[expose] public section

namespace Minidregg.Kernel.FnEmptyPollAdmissionAtV2

open Minidregg.Kernel
open Minidregg.Kernel.FnEmptyPollProgressV2
open Minidregg.Theory
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure AcceptedGround (config : NativeHost.Config) (ground : ServedBasis.Ground config.deployment)
    (cursor : FnConsumerFrontierCore.Cursor)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress) where
  private mk ::
  frontierExact : FnConsumerFrontierCore.checkAfter cursor
    (candidate ingress.spec) = .ok ()
  keyGatewayExact : ingress.spec.keyMatchesGateway = true
  registrationExact : registration.receipt = ingress.spec.registrationReceipt
  registrationKeyExact : registration.ingress.spec.key = ingress.spec.evidence.key
  gateway : FnConsumerFrontierGateway.CheckedGround config ground
    (FnConsumerFrontierProposal.empty ingress) ingress.gatewayEnvelope

abbrev Accepted (config : NativeHost.Config) (opened : NativeHost.Opened config) :=
  AcceptedGround config (FnConsumerFrontierGateway.contextOf opened)

theorem Accepted.sound {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {cursor : FnConsumerFrontierCore.Cursor} {registration : FnConsumerNamespaceHistory.Original}
    {ingress : Ingress} (accepted : Accepted config opened cursor registration ingress) :
    FnConsumerFrontierCore.checkAfter cursor (candidate ingress.spec) = .ok () ∧
    registration.receipt = ingress.spec.registrationReceipt ∧
    registration.ingress.spec.key = ingress.spec.evidence.key ∧
    accepted.gateway.signature.signature.envelopeBytes = ingress.gatewayEnvelope ∧
    FnConsumerFrontierGateway.authorize accepted.gateway.prepared
      accepted.gateway.signature.signature = some accepted.gateway.signature.authorization :=
  ⟨accepted.frontierExact, accepted.registrationExact, accepted.registrationKeyExact,
    accepted.gateway.signature.envelopeExact, accepted.gateway.signature.authorized⟩

def admitAtGround (config : NativeHost.Config) (ground : ServedBasis.Ground config.deployment)
    (cursor : FnConsumerFrontierCore.Cursor)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress) :
    IO (Except String (AcceptedGround config ground cursor registration ingress)) := do
  unless ingress.spec.evidence.valid &&
      (ingressCodec.encode ingress).length ≤ 12288 do
    return .error "ordered empty fn page refused"
  if registrationExact : registration.receipt = ingress.spec.registrationReceipt then
    if registrationKeyExact : registration.ingress.spec.key = ingress.spec.evidence.key then
      if keyGatewayExact : ingress.spec.keyMatchesGateway = true then
        if frontierExact : FnConsumerFrontierCore.checkAfter cursor
            (candidate ingress.spec) = .ok () then
          match ← FnConsumerFrontierGateway.checkGround config ground
              (FnConsumerFrontierProposal.empty ingress) ingress.gatewayEnvelope with
          | .error _ => return .error "ordered empty fn page refused"
          | .ok gateway => return .ok ⟨frontierExact, keyGatewayExact, registrationExact,
              registrationKeyExact, gateway⟩
        else return .error "ordered empty fn page refused"
      else return .error "ordered empty fn page refused"
    else return .error "ordered empty fn page refused"
  else return .error "ordered empty fn page refused"

def admitAt (config : NativeHost.Config) (opened : NativeHost.Opened config) :=
  admitAtGround config (FnConsumerFrontierGateway.contextOf opened)

/-- The turn's charge: it writes nothing, so its storage lane is the World's
storage of its retained event (`DeployedCharge.storageCharge`; a guard is a pin and writes
nothing). -/
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

def AcceptedGround.intent (config : NativeHost.Config) (ground : ServedBasis.Ground config.deployment)
    (cursor : FnConsumerFrontierCore.Cursor)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress)
    (accepted : AcceptedGround config ground cursor registration ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  let guards := FnConsumerFrontierGateway.readGuards accepted.gateway.prepared ++
    ground.authorityReadGuards
  { transactionId := transactionId ingress.spec
    writes := []
    readGuards := guards
    nullifiers := [frontierNullifier ingress.spec]
    exactCharge := (Minidregg.Theory.ResourceCost.Charge.materialize
      (charge ground.view guards ingress)).toCharge
    event := event ingress
    subject := some ingress.spec.gatewaySubject
    postRootsBound := by intro write present; cases present
    guardsReadOnly := by intro guard _; simp }

def Accepted.intent (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (cursor : FnConsumerFrontierCore.Cursor)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress)
    (accepted : Accepted config opened cursor registration ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  AcceptedGround.intent config (FnConsumerFrontierGateway.contextOf opened) cursor registration ingress accepted

end Minidregg.Kernel.FnEmptyPollAdmissionAtV2
