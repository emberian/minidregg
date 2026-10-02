/-
Lower event19 component admission at a source-owned frontier cursor. Only a
private replay walk or a live Verified wrapper may supply that predecessor;
this function alone does not certify history or an fn poll's completeness.
-/
import Kernel.FnConsumerFrontierProposal
import Kernel.FnConsumerNamespaceHistory

namespace Minidregg.Kernel.FnEmptyPollAdmissionAtV2

open Minidregg.Kernel
open Minidregg.Kernel.FnEmptyPollProgressV2
open Minidregg.Theory
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

structure Accepted (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (cursor : FnConsumerFrontierCore.Cursor)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress) where
  private mk ::
  frontierExact : FnConsumerFrontierCore.checkAfter cursor
    (candidate ingress.spec) = .ok ()
  keyGatewayExact : ingress.spec.keyMatchesGateway = true
  registrationExact : registration.receipt = ingress.spec.registrationReceipt
  registrationKeyExact : registration.ingress.spec.key = ingress.spec.evidence.key
  gateway : FnConsumerFrontierGateway.CheckedOpened config opened
    (FnConsumerFrontierProposal.empty ingress) ingress.gatewayEnvelope

def admitAt (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (cursor : FnConsumerFrontierCore.Cursor)
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress) :
    IO (Except String (Accepted config opened cursor registration ingress)) := do
  unless ingress.spec.evidence.valid &&
      (ingressCodec.encode ingress).length ≤ 12288 do
    return .error "ordered empty fn page refused"
  if registrationExact : registration.receipt = ingress.spec.registrationReceipt then
    if registrationKeyExact : registration.ingress.spec.key = ingress.spec.evidence.key then
      if keyGatewayExact : ingress.spec.keyMatchesGateway = true then
        if frontierExact : FnConsumerFrontierCore.checkAfter cursor
            (candidate ingress.spec) = .ok () then
          match ← FnConsumerFrontierGateway.checkOpened config opened
              (FnConsumerFrontierProposal.empty ingress) ingress.gatewayEnvelope with
          | .error _ => return .error "ordered empty fn page refused"
          | .ok gateway => return .ok ⟨frontierExact, keyGatewayExact, registrationExact,
              registrationKeyExact, gateway⟩
        else return .error "ordered empty fn page refused"
      else return .error "ordered empty fn page refused"
    else return .error "ordered empty fn page refused"
  else return .error "ordered empty fn page refused"

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
    (registration : FnConsumerNamespaceHistory.Original) (ingress : Ingress)
    (accepted : Accepted config opened cursor registration ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  { transactionId := transactionId ingress.spec
    writes := []
    readGuards := FnConsumerFrontierGateway.readGuards accepted.gateway.prepared ++
      opened.authority.readGuards
    nullifiers := [frontierNullifier ingress.spec]
    exactCharge := charge ingress
    event := event ingress
    subject := some ingress.spec.gatewaySubject
    postRootsBound := by intro write present; cases present
    guardsReadOnly := by intro guard _; simp }

end Minidregg.Kernel.FnEmptyPollAdmissionAtV2
