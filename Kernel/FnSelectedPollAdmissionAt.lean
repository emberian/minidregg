/-
Lower event17 component admission at a source-owned frontier cursor. The caller
must obtain the cursor and prior event13 record/receipt from its *private*
native-verified replay walk. Passing an arbitrary Cursor or Original to this
function is not a receiving-authority claim; live Host uses a Verified wrapper.
-/
import Kernel.FnConsumerFrontierProposal
import Kernel.FnSelectedPollReleaseShape
import Kernel.FnConsumerNamespaceHistory

namespace Minidregg.Kernel.FnSelectedPollAdmissionAt

open Minidregg.Kernel
open Minidregg.Kernel.FnSelectedPollCoverage
open Minidregg.Theory
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Accepted (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (cursor : FnConsumerFrontierCore.Cursor)
    (original : FnSelectedPollReleaseShape.Original)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress) where
  private mk ::
  frontierExact : FnConsumerFrontierCore.checkAfter cursor
    (candidate ingress.spec) = .ok ()
  keyGatewayExact : ingress.spec.keyMatchesGateway = true
  registrationExact : registration.receipt = ingress.spec.registrationReceipt
  registrationKeyExact : registration.ingress.spec.key = ingress.spec.evidence.key
  gateway : FnConsumerFrontierGateway.CheckedOpened config opened
    (FnConsumerFrontierProposal.selected ingress) ingress.gatewayEnvelope
  receiptExact : original.receipt = ingress.spec.evidence.releaseReceipt
  keyExact : FnSelectiveReleaseIngress.transactionId original.ingress =
    ingress.spec.evidence.releaseKey
  messageExact : original.ingress.packet.release.destination.messageId =
    ingress.spec.evidence.messageId
  groupExact : original.ingress.packet.release.destination.group =
    ingress.spec.evidence.key.scope.query

def admitAt (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (cursor : FnConsumerFrontierCore.Cursor)
    (original : FnSelectedPollReleaseShape.Original)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress) :
    IO (Except String (Accepted config opened cursor original registration ingress)) := do
  unless ingress.spec.evidence.valid &&
      (ingressCodec.encode ingress).length ≤ 16384 do
    return .error "selected fn poll testimony refused"
  if registrationExact : registration.receipt = ingress.spec.registrationReceipt then
    if registrationKeyExact : registration.ingress.spec.key = ingress.spec.evidence.key then
      if keyGatewayExact : ingress.spec.keyMatchesGateway = true then
        if frontierExact : FnConsumerFrontierCore.checkAfter cursor
            (candidate ingress.spec) = .ok () then
          match ← FnConsumerFrontierGateway.checkOpened config opened
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

def charge (ingress : Ingress) : ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => (ingressCodec.encode ingress).length
  | .memoryTouches => 1
  | .storageBytes => (ingressCodec.encode ingress).length
  | .witnessBytes => (ingressCodec.encode ingress).length
  | .proofWork => 1
  | .sideEffectCount => 1
  | .feeDebit | .networkBytes | .leaseByteBlocks => 0

def Accepted.intent (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (cursor : FnConsumerFrontierCore.Cursor)
    (original : FnSelectedPollReleaseShape.Original)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress)
    (accepted : Accepted config opened cursor original registration ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  { transactionId := transactionId ingress.spec
    writes := []
    readGuards := [FnConsumerFrontierGateway.readGuard accepted.gateway.prepared] ++
      opened.authority.readGuards
    nullifiers := [frontierNullifier ingress.spec]
    exactCharge := charge ingress
    event := event ingress
    postRootsBound := by intro write present; cases present
    guardsReadOnly := by intro guard _; simp }

end Minidregg.Kernel.FnSelectedPollAdmissionAt
