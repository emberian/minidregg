/-
Operator-private signing plan for one locally observed selected or empty fn poll.
Main alone runs the pinned fn binary and supplies the projected evidence. This
module binds that evidence to the current gateway credential signing header;
the detached signature is not an admission or an fn ACK.
-/
module

public import Host.FnConsumerNamespacePlan
public import Compiler.FnEvidenceCodec
public import Kernel.FnConsumerFrontierProposal
public import Host.Json
public import Kernel.FnSelectedPollCoverage
public import Kernel.FnEmptyPollProgressV2

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Host.FnConsumerFrontierPlan

open Lean
open Minidregg.Kernel
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

structure Plan where
  selected : Option FnSelectedPollCoverage.Spec
  empty : Option FnEmptyPollProgressV2.Spec
  cursorBytes : List UInt8
  reportBytes : List UInt8
  sourceBytes : List UInt8
  expectedAuthorityRoot : Digest
  expectedTargetRoot : Digest
  signingHeader : List UInt8
  deriving DecidableEq, Repr

def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.option FnSelectedPollCoverage.specStream)
      (StreamCodec.product (StreamCodec.option FnEmptyPollProgressV2.specStream)
        (StreamCodec.product bytesStream
          (StreamCodec.product bytesStream
            (StreamCodec.product bytesStream
              (StreamCodec.product digestStream
                (StreamCodec.product digestStream bytesStream)))))))
    (fun plan => (plan.selected, plan.empty, plan.cursorBytes, plan.reportBytes,
      plan.sourceBytes, plan.expectedAuthorityRoot, plan.expectedTargetRoot,
      plan.signingHeader))
    (fun (selected, empty, cursor, report, source, authorityRoot, targetRoot,
      header) =>
      ⟨selected, empty, cursor, report, source, authorityRoot, targetRoot, header⟩)
    (by intro plan; cases plan; rfl)

def planCodec : LawfulCodec Plan :=
  NativeHostCodec.framed "DREGG/FN/CONSUMER-FRONTIER-PLAN/v2".toUTF8.toList planStream

theorem plan_decode_encode (plan : Plan) :
    planCodec.decode (planCodec.encode plan) = some plan :=
  planCodec.decode_encode plan

def Plan.proposal (plan : Plan) : Except String FnConsumerFrontierGateway.Proposal := do
  unless !plan.cursorBytes.isEmpty && plan.cursorBytes.length ≤ 346 &&
      plan.reportBytes.length ≤ FnEvidenceCodec.maxStorePollEventBytes &&
      plan.sourceBytes.length ≤ FnEvidenceCodec.maxSourceBytes do
    throw "fn frontier retained poll artifacts exceed strict profile"
  match plan.selected, plan.empty with
  | some spec, none =>
      unless spec.evidence.valid && spec.keyMatchesGateway &&
          spec.evidence.cursor == plan.cursorBytes &&
          spec.evidence.reportDigest ==
            FnConsumerFrontierCore.reportDigest plan.reportBytes &&
          spec.evidence.sourceDigest ==
            FnConsumerFrontierCore.sourceDigest plan.sourceBytes &&
          !plan.reportBytes.isEmpty && !plan.sourceBytes.isEmpty do
        throw "selected fn frontier spec refused"
      pure (FnConsumerFrontierProposal.selected
        ⟨spec, [], plan.expectedAuthorityRoot, plan.expectedTargetRoot⟩)
  | none, some spec =>
      unless spec.evidence.valid && spec.keyMatchesGateway &&
          spec.evidence.cursor == plan.cursorBytes &&
          spec.evidence.reportDigest ==
            FnConsumerFrontierCore.reportDigest plan.reportBytes &&
          plan.reportBytes.isEmpty && plan.sourceBytes.isEmpty do
        throw "empty fn frontier spec refused"
      pure (FnConsumerFrontierProposal.empty
        ⟨spec, [], plan.expectedAuthorityRoot, plan.expectedTargetRoot⟩)
  | _, _ => throw "fn frontier plan must contain exactly one poll kind"

def prepareSigningHeaderAt (config : NativeHost.Config)
    (ground : ServedBasis.Ground config.deployment)
    (proposal : FnConsumerFrontierGateway.Proposal) : Except String (List UInt8) := do
  let some pin := config.fnGateway
    | throw "fn consumer gateway is not configured"
  let .ok () := FnGatewayPolicy.checkGround config ground pin
    | throw "fn consumer gateway current law refused"
  let .ok prepared := FnConsumerFrontierGateway.prepare
      ground config.profile config.federation
      (config.genesisHeight + ground.height) pin proposal
    | throw "fn frontier target or pin refused"
  let wanted : PackedEffectRequest := ⟨.object, prepared.wanted⟩
  let .ok header := CredentialSignatureAdmission.signingHeader
      ground.authority (FnConsumerFrontierGateway.marker proposal) wanted
    | throw "fn frontier gateway signing key unavailable"
  pure (CredentialSignedEnvelopeController.headerCodec.encode header)

def prepareSigningHeader (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (proposal : FnConsumerFrontierGateway.Proposal) : Except String (List UInt8) :=
  prepareSigningHeaderAt config (FnConsumerFrontierGateway.contextOf opened) proposal

def prepareAt (config : NativeHost.Config) (ground : ServedBasis.Ground config.deployment)
    (selected : Option FnSelectedPollCoverage.Spec)
    (empty : Option FnEmptyPollProgressV2.Spec) (cursorBytes reportBytes
      sourceBytes : List UInt8) : Except String Plan := do
  let some pin := config.fnGateway
    | throw "fn consumer gateway is not configured"
  let (authorityRoot, targetRoot) ← FnConsumerNamespacePlan.currentRootsAt
    config ground pin
  let candidate : Plan := ⟨selected, empty, cursorBytes, reportBytes, sourceBytes,
    authorityRoot, targetRoot, []⟩
  let proposal ← candidate.proposal
  let header ← prepareSigningHeaderAt config ground proposal
  let plan := { candidate with signingHeader := header }
  unless !header.isEmpty && header.length ≤ 4096 &&
      (planCodec.encode plan).length + 4 + 64 ≤
        FnEvidenceCodec.maxHostFrameBytes do
    throw "fn frontier signing plan exceeds strict profile"
  pure plan

def prepare (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (selected : Option FnSelectedPollCoverage.Spec) (empty : Option FnEmptyPollProgressV2.Spec)
    (cursorBytes reportBytes sourceBytes : List UInt8) : Except String Plan :=
  prepareAt config (FnConsumerFrontierGateway.contextOf opened) selected empty cursorBytes reportBytes sourceBytes

def checkCurrent (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (plan : Plan) : Except String Unit := do
  let some pin := config.fnGateway
    | throw "fn consumer gateway is not configured"
  let roots ← FnConsumerNamespacePlan.currentRoots config opened pin
  unless roots == (plan.expectedAuthorityRoot, plan.expectedTargetRoot) do
    throw "fn frontier signing plan roots changed"
  let proposal ← plan.proposal
  let header ← prepareSigningHeaderAt config (FnConsumerFrontierGateway.contextOf opened) proposal
  unless header == plan.signingHeader do
    throw "fn frontier signing plan no longer current"

def assembleSignature (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (plan : Plan)
    (signature : List UInt8) : Except String (List UInt8) := do
  unless signature.length == 64 &&
      (planCodec.encode plan).length + 4 + 64 ≤
        FnEvidenceCodec.maxHostFrameBytes do
    throw "fn frontier gateway signature or plan exceeds strict profile"
  checkCurrent config opened plan
  let some header := CredentialSignedEnvelopeController.headerCodec.decode
      plan.signingHeader
    | throw "fn frontier signing header is not canonical"
  unless CredentialSignedEnvelopeController.headerCodec.encode header ==
      plan.signingHeader do
    throw "fn frontier signing header is not canonical"
  let envelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨header, signature⟩
  match plan.selected, plan.empty with
  | some spec, none =>
      let ingress : FnSelectedPollCoverage.Ingress :=
        ⟨spec, envelope, plan.expectedAuthorityRoot, plan.expectedTargetRoot⟩
      unless (FnSelectedPollCoverage.ingressCodec.encode ingress).length ≤ 16384 do
        throw "selected fn frontier ingress exceeds strict profile"
      pure (FnSelectedPollCoverage.ingressCodec.encode ingress)
  | none, some spec =>
      let ingress : FnEmptyPollProgressV2.Ingress :=
        ⟨spec, envelope, plan.expectedAuthorityRoot, plan.expectedTargetRoot⟩
      unless (FnEmptyPollProgressV2.ingressCodec.encode ingress).length ≤ 12288 do
        throw "empty fn frontier ingress exceeds strict profile"
      pure (FnEmptyPollProgressV2.ingressCodec.encode ingress)
  | _, _ => throw "fn frontier plan must contain exactly one poll kind"

private def receiptJson (receipt : NativeHostCodec.Receipt) : Lean.Json :=
  Lean.Json.mkObj
    [("transactionId", toJson (Nat.repr receipt.transactionId.value)),
     ("eventId", toJson (Nat.repr receipt.eventId.value)),
     ("acceptedCount", toJson (Nat.repr receipt.acceptedCount)),
     ("worldRoot", toJson (Nat.repr receipt.worldRoot.value))]

/-- Display only. Custody still has to compare the complete approved scope,
gateway, selected release, and exact signing header before signing. -/
def inspectPlanBytes (bytes : List UInt8) : Except String Lean.Json := do
  unless !bytes.isEmpty && bytes.length ≤ FnEvidenceCodec.maxHostFrameBytes do
    throw "fn frontier plan exceeds strict frame"
  let some plan := planCodec.decode bytes
    | throw "fn frontier plan is not canonical"
  let _ ← plan.proposal
  let some header := CredentialSignedEnvelopeController.headerCodec.decode
      plan.signingHeader
    | throw "fn frontier signing header is not canonical"
  unless CredentialSignedEnvelopeController.headerCodec.encode header ==
      plan.signingHeader do
    throw "fn frontier signing header is not canonical"
  let (kind, key, fromPosition, toPosition, predecessor, registrationReceipt,
       selectedSequence, releaseReceipt, releaseKey) ←
    match plan.selected, plan.empty with
    | some spec, none => pure ("selected", spec.evidence.key, spec.evidence.fromPosition,
          spec.evidence.toPosition, spec.evidence.predecessor,
          spec.registrationReceipt, some spec.evidence.selectedSequence,
          some spec.evidence.releaseReceipt, some spec.evidence.releaseKey)
    | none, some spec => pure ("empty", spec.evidence.key, spec.evidence.fromPosition,
          spec.evidence.toPosition, spec.evidence.predecessor,
          spec.registrationReceipt, none, none, none)
    | _, _ => throw "fn frontier plan has invalid kind"
  let scope := key.scope
  let canonicalSpec := match plan.selected, plan.empty with
    | some spec, none => FnSelectedPollCoverage.specCodec.encode spec
    | none, some spec => FnEmptyPollProgressV2.specCodec.encode spec
    | _, _ => []
  pure <| Lean.Json.mkObj
    [("type", toJson "fn-consumer-frontier-plan-v2"),
     ("kind", toJson kind),
     ("canonicalPlanHex", toJson (Minidregg.Host.Json.encodeHex bytes)),
     ("canonicalSpecHex", toJson (Minidregg.Host.Json.encodeHex canonicalSpec)),
     ("cursorHex", toJson (Minidregg.Host.Json.encodeHex plan.cursorBytes)),
     ("reportBytes", toJson (Nat.repr plan.reportBytes.length)),
     ("sourceBytes", toJson (Nat.repr plan.sourceBytes.length)),
     ("reportDigest", toJson (Nat.repr
        (FnConsumerFrontierCore.reportDigest plan.reportBytes).value)),
     ("sourceDigest", toJson (Nat.repr
        (FnConsumerFrontierCore.sourceDigest plan.sourceBytes).value)),
     ("applicationHex", toJson (Minidregg.Host.Json.encodeHex key.application)),
     ("historyHex", toJson (Minidregg.Host.Json.encodeHex scope.history)),
     ("incarnationHex", toJson (Minidregg.Host.Json.encodeHex scope.incarnation)),
     ("consumerHex", toJson (Minidregg.Host.Json.encodeHex scope.consumer)),
     ("principalHex", toJson (Minidregg.Host.Json.encodeHex scope.principal)),
     ("queryHex", toJson (Minidregg.Host.Json.encodeHex scope.query)),
     ("queryVersion", toJson (Nat.repr scope.queryVersion)),
     ("viewVersion", toJson (Nat.repr scope.viewVersion)),
     ("registrationEpoch", toJson (Nat.repr scope.registrationEpoch)),
     ("controlBindingHex", toJson (Minidregg.Host.Json.encodeHex key.controlBinding)),
     ("gatewaySubject", toJson (Nat.repr key.gatewaySubject.value)),
     ("gatewayTarget", toJson (Nat.repr key.gatewayTarget)),
     ("gatewayCapability", toJson (Nat.repr key.gatewayCapability.value)),
     ("fromPosition", toJson (Nat.repr fromPosition)),
     ("toPosition", toJson (Nat.repr toPosition)),
     ("selectedSequence", toJson (selectedSequence.map Nat.repr)),
     ("predecessor", predecessor.map receiptJson |>.getD Lean.Json.null),
     ("registrationReceipt", receiptJson registrationReceipt),
     ("releaseReceipt", releaseReceipt.map receiptJson |>.getD Lean.Json.null),
     ("releaseKey", toJson (releaseKey.map (fun key => Nat.repr key.value))),
     ("expectedAuthorityRoot", toJson (Nat.repr plan.expectedAuthorityRoot.value)),
     ("expectedTargetRoot", toJson (Nat.repr plan.expectedTargetRoot.value)),
     ("signingKeyId", toJson (Nat.repr header.keyId)),
     ("signingKeyEpoch", toJson (Nat.repr header.keyEpoch)),
     ("signingAlgorithm", toJson (Nat.repr header.algorithm)),
     ("signingValidUntil", toJson (Nat.repr header.validUntil)),
     ("signingHeaderHex", toJson (Minidregg.Host.Json.encodeHex plan.signingHeader))]

end Minidregg.Host.FnConsumerFrontierPlan
