/-
Lower event17 component admission at a source-owned frontier cursor. The caller
must obtain the cursor and prior event13 record/receipt from its *private*
native-verified replay walk. Passing an arbitrary Cursor or Original to this
function is not a receiving-authority claim; live Host uses a Verified wrapper.
-/
module

public import Kernel.FnConsumerFrontierProposal
public import Kernel.FnSelectedPollReleaseShape
public import Kernel.FnConsumerNamespaceHistory

@[expose] public section

namespace Minidregg.Kernel.FnSelectedPollAdmissionAt

open Minidregg.Kernel
open Minidregg.Kernel.FnSelectedPollCoverage
open Minidregg.Theory
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure AcceptedGround (config : NativeHost.Config) (ground : ServedBasis.Ground config.deployment)
    (cursor : FnConsumerFrontierCore.Cursor)
    (original : FnSelectedPollReleaseShape.Original)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress) where
  private mk ::
  frontierExact : FnConsumerFrontierCore.checkAfter cursor
    (candidate ingress.spec) = .ok ()
  keyGatewayExact : ingress.spec.keyMatchesGateway = true
  registrationExact : registration.receipt = ingress.spec.registrationReceipt
  registrationKeyExact : registration.ingress.spec.key = ingress.spec.evidence.key
  gateway : FnConsumerFrontierGateway.CheckedGround config ground
    (FnConsumerFrontierProposal.selected ingress) ingress.gatewayEnvelope
  receiptExact : original.receipt = ingress.spec.evidence.releaseReceipt
  keyExact : FnSelectiveReleaseIngress.transactionId original.ingress =
    ingress.spec.evidence.releaseKey
  messageExact : original.ingress.packet.release.destination.messageId =
    ingress.spec.evidence.messageId
  groupExact : original.ingress.packet.release.destination.group =
    ingress.spec.evidence.key.scope.query

abbrev Accepted (config : NativeHost.Config) (opened : NativeHost.Opened config) :=
  AcceptedGround config (FnConsumerFrontierGateway.contextOf opened)

theorem Accepted.sound {config : NativeHost.Config} {opened : NativeHost.Opened config}
    {cursor : FnConsumerFrontierCore.Cursor} {original : FnSelectedPollReleaseShape.Original}
    {registration : FnConsumerNamespaceHistory.Original} {ingress : Ingress}
    (accepted : Accepted config opened cursor original registration ingress) :
    FnConsumerFrontierCore.checkAfter cursor (candidate ingress.spec) = .ok () ∧
    registration.receipt = ingress.spec.registrationReceipt ∧
    original.receipt = ingress.spec.evidence.releaseReceipt ∧
    FnSelectiveReleaseIngress.transactionId original.ingress = ingress.spec.evidence.releaseKey ∧
    original.ingress.packet.release.destination.messageId = ingress.spec.evidence.messageId ∧
    original.ingress.packet.release.destination.group = ingress.spec.evidence.key.scope.query ∧
    FnConsumerFrontierGateway.authorize accepted.gateway.prepared
      accepted.gateway.signature.signature = some accepted.gateway.signature.authorization :=
  ⟨accepted.frontierExact, accepted.registrationExact, accepted.receiptExact, accepted.keyExact,
    accepted.messageExact, accepted.groupExact, accepted.gateway.signature.authorized⟩

def admitAtGround (config : NativeHost.Config) (ground : ServedBasis.Ground config.deployment)
    (cursor : FnConsumerFrontierCore.Cursor)
    (original : FnSelectedPollReleaseShape.Original)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress) :
    IO (Except String (AcceptedGround config ground cursor original registration ingress)) := do
  unless ingress.spec.evidence.valid &&
      (ingressCodec.encode ingress).length ≤ 16384 do
    return .error "selected fn poll testimony refused"
  if registrationExact : registration.receipt = ingress.spec.registrationReceipt then
    if registrationKeyExact : registration.ingress.spec.key = ingress.spec.evidence.key then
      if keyGatewayExact : ingress.spec.keyMatchesGateway = true then
        if frontierExact : FnConsumerFrontierCore.checkAfter cursor
            (candidate ingress.spec) = .ok () then
          match ← FnConsumerFrontierGateway.checkGround config ground
              (FnConsumerFrontierProposal.selected ingress) ingress.gatewayEnvelope with
          | .error _ => return .error "selected fn poll testimony refused"
          | .ok gateway =>
              if receiptExact : original.receipt = ingress.spec.evidence.releaseReceipt then
                if keyExact : FnSelectiveReleaseIngress.transactionId original.ingress =
                    ingress.spec.evidence.releaseKey then
                  if messageExact : original.ingress.packet.release.destination.messageId =
                      ingress.spec.evidence.messageId then
                    if groupExact : original.ingress.packet.release.destination.group =
                        ingress.spec.evidence.key.scope.query then
                      return .ok ⟨frontierExact, keyGatewayExact, registrationExact,
                        registrationKeyExact, gateway, receiptExact, keyExact,
                        messageExact, groupExact⟩
                    else return .error "selected fn poll testimony refused"
                  else return .error "selected fn poll testimony refused"
                else return .error "selected fn poll testimony refused"
              else return .error "selected fn poll testimony refused"
        else return .error "selected fn poll testimony refused"
      else return .error "selected fn poll testimony refused"
    else return .error "selected fn poll testimony refused"
  else return .error "selected fn poll testimony refused"

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
    (original : FnSelectedPollReleaseShape.Original)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress)
    (accepted : AcceptedGround config ground cursor original registration ingress) :
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
    (original : FnSelectedPollReleaseShape.Original)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress)
    (accepted : Accepted config opened cursor original registration ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  AcceptedGround.intent config (FnConsumerFrontierGateway.contextOf opened) cursor original registration ingress accepted

end Minidregg.Kernel.FnSelectedPollAdmissionAt
