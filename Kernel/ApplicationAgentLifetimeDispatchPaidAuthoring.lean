/-
Source-owned v3 lifetime dispatch signing plans. The fixed custodian supplies
only selectors, one HTTP request, and a new operation ID. Mini derives the
current parent/purse, the certified event27 grant, exact reserve context and
signing headers from one verifier-opened image. A plan is not a permit.
-/
import Kernel.ApplicationDispatchAgentPaidAuthoring
import Kernel.ApplicationAgentLifetimeDispatchReceiver

namespace Minidregg.Kernel.ApplicationAgentLifetimeDispatchPaidAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Request where
  fixed : ApplicationDispatchAgentPaidAuthoring.Request
  grantIssueIndex : Nat
  grantResource : Nat
  grantObserveCapability : CapabilityId
  deriving DecidableEq

structure FixedSelectors where
  legacy : ApplicationDispatchAgentPaidAuthoring.FixedSelectors
  grantIssueIndex : Nat
  grantResource : Nat
  grantObserveCapability : CapabilityId
  deriving DecidableEq

def Request.fixedSelectors (request : Request) : FixedSelectors :=
  ⟨request.fixed.fixedSelectors, request.grantIssueIndex,
    request.grantResource, request.grantObserveCapability⟩

def Request.matchesFixed (request : Request) (pin : FixedSelectors) : Bool :=
  decide (request.fixedSelectors = pin)

def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationDispatchAgentPaidAuthoring.requestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          CredentialAuthorityEntryCodec.capabilityIdStream)))
    (fun request => (request.fixed, request.grantIssueIndex,
      request.grantResource, request.grantObserveCapability))
    (fun (fixed, grantIssueIndex, grantResource, grantObserveCapability) =>
      ⟨fixed, grantIssueIndex, grantResource, grantObserveCapability⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-AUTHOR-REQUEST/v3".toUTF8.toList
    requestStream

/-- Immutable historical receipts and full current physical roots projected
by source authoring, retained in both v3 plans for crash-phase custody. The
runtime cannot elevate these bytes to authority without later native checks. -/
structure SourceBindings where
  originalIssueReceipt : NativeHostCodec.Receipt
  grantIssueReceipt : NativeHostCodec.Receipt
  grantInitializedRoot : Digest
  grantPhysicalRoot : Digest
  parentPhysicalRoot : Digest
  pursePhysicalRoot : Digest

def sourceBindingsStream : StreamCodec SourceBindings :=
  StreamCodec.xmap
    (StreamCodec.product NativeHostCodec.receiptStream
      (StreamCodec.product NativeHostCodec.receiptStream
        (StreamCodec.product digestStream
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream digestStream)))))
    (fun value => (value.originalIssueReceipt, value.grantIssueReceipt,
      value.grantInitializedRoot, value.grantPhysicalRoot,
      value.parentPhysicalRoot, value.pursePhysicalRoot))
    (fun (originalIssueReceipt, grantIssueReceipt, grantInitializedRoot,
          grantPhysicalRoot, parentPhysicalRoot, pursePhysicalRoot) =>
      ⟨originalIssueReceipt, grantIssueReceipt, grantInitializedRoot,
        grantPhysicalRoot, parentPhysicalRoot, pursePhysicalRoot⟩)
    (by intro value; cases value; rfl)

structure ReservePlan where
  request : Request
  context : ApplicationAgentLifetimeDispatchReserveContext.Context
  bindings : SourceBindings
  invocation : NativeHostCodec.SigningPlan

def reservePlanStream : StreamCodec ReservePlan :=
  StreamCodec.xmap
    (StreamCodec.product requestStream
      (StreamCodec.product ApplicationAgentLifetimeDispatchReserveContext.contextStream
        (StreamCodec.product sourceBindingsStream NativeHostCodec.signingPlanStream)))
    (fun plan => (plan.request, plan.context, plan.bindings, plan.invocation))
    (fun (request, context, bindings, invocation) =>
      ⟨request, context, bindings, invocation⟩)
    (by intro plan; cases plan; rfl)

def reservePlanCodec : LawfulCodec ReservePlan :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-RESERVE-PLAN/v3".toUTF8.toList
    reservePlanStream

private def certifiedGrant (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target)
    (request : Request) : Except String (NativeHostReplay.PriorLifetimeGrant config) := do
  let some grant := verified.grants.find? (fun prior =>
      prior.index == request.grantIssueIndex)
    | throw "lifetime grant absent from admitted history"
  let source := grant.ingress.spec.grant
  if source.source.resource != request.grantResource ||
      source.participant.grantObserveCapability != request.grantObserveCapability ||
      grant.ticket.index != request.fixed.base.base.issueIndex ||
      grant.ticket.evidence.spec.ticket.resource != request.fixed.base.base.ticketResource ||
      !source.matchesIssued grant.ticket.evidence.spec grant.ticket.index grant.ticket.receipt then
    throw "lifetime grant differs from fixed custodian/original ticket"
  pure grant

private def currentGrantCell (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target)
    (grant : NativeHostReplay.PriorLifetimeGrant config) :
    Except String (PackedCell CanonicalCellRegistry.registry) := do
  let resource := grant.ingress.spec.grant.source.resource
  let cell ← match verified.opened.directory.directory.slots resource with
    | .present cell => pure cell
    | _ => throw "current lifetime grant cell unavailable"
  if ResourceBirthCodec.physicalRoot (.live cell) != grant.finalRoot ||
      ApplicationAgentLifetimeDispatchCurrent.grantAt config.deployment.domain resource cell !=
        some grant.ingress.spec.grant then
    throw "current lifetime grant differs from certified installation"
  pure cell

/-- Before the ordinary reserve, all current coordinates and the complete
grant binding are derived from this verified image. Signatures are detached;
the final event26 receiver still proves the reserve's original admission. -/
def prepareReserveVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (request : Request) :
    Except String ReservePlan := do
  let grant ← certifiedGrant config verified request
  let grantCell ← currentGrantCell config verified grant
  let base := request.fixed
  if base.purseTask == base.base.task || base.purseTask == request.grantResource ||
      base.reserveAmount < 0 || base.maximumCharge < 0 ||
      base.maximumCharge > base.reserveAmount then
    throw "lifetime reserve fixed amount/task bounds refused"
  let app ← ApplicationDispatchAuthoring.prepareWithLifetimeGrant config verified
    base.base.base request.grantIssueIndex base.base.task
    base.base.parentCapability base.base.parentObserveCapability
  let some unsigned := ApplicationDispatchAdmissionIngress.codec.decode app.unsignedIngress
    | throw "lifetime reserve app plan is noncanonical"
  let some parent := unsigned.parent
    | throw "lifetime reserve parent missing from source plan"
  let parentCell ← match verified.opened.directory.directory.slots parent.task with
    | .present cell => pure cell
    | _ => throw "current lifetime parent unavailable"
  if parentCell.payload.root != parent.root then
    throw "current lifetime parent differs from source plan"
  let purseCell ← match verified.opened.directory.directory.slots base.purseTask with
    | .present cell => pure cell
    | _ => throw "current lifetime purse unavailable"
  let some purseState := ApplicationDispatchAgentPayer.stateAt base.purseTask purseCell
    | throw "current lifetime purse state unavailable"
  if !(purseState.status == 1 || purseState.status == 2) ||
      purseState.reserved != 0 || base.reserveAmount > purseState.remaining then
    throw "lifetime purse cannot reserve requested allowance"
  let old : ApplicationDispatchAgentReserveContext.Context :=
    { domain := config.deployment.domain
      semantics := config.profile.semantics
      app := unsigned.dispatch.dispatch.app
      session := unsigned.dispatch.dispatch.session
      ticketResource := grant.ticket.evidence.spec.ticket.resource
      ticketRoot := unsigned.ticketRoot
      parentTask := parent.task
      parentGeneration := parent.state.generation
      purseTask := base.purseTask
      purseGeneration := purseState.generation
      payerSubject := base.payerSubject
      reserveAmount := base.reserveAmount
      maximumCharge := base.maximumCharge
      reserveOperationId := base.reserveOperationId
      httpOperationId := base.base.base.http.operationId
      requestDigest := ApplicationDispatchCodec.requestDigest base.base.base.http }
  let context : ApplicationAgentLifetimeDispatchReserveContext.Context :=
    ⟨old, request.grantResource, grant.index,
      ApplicationAgentLifetimeDispatchReserveContext.grantDigest
        grant.ingress.spec.grant⟩
  let command : DeclaredResourceController.Command :=
    { subject := base.payerSubject
      expectedAuthorityRoot := verified.opened.authority.snapshot.cell.root
      nonce := ApplicationAgentLifetimeDispatchReserveContext.reserveNonce context
      targets := [AgentGrain.Operation.target (.reserve base.reserveAmount)
        base.purseTask base.purseCapability purseCell.payload.root purseState
        (some base.purseObserve)] }
  let invocation ← NativeHost.prepareLoaded config verified.opened
    (.invoke (DeclaredResourceController.commandCodec.encode command))
  let bindings : SourceBindings :=
    { originalIssueReceipt := grant.ticket.receipt
      grantIssueReceipt := grant.receipt
      grantInitializedRoot := grant.finalRoot
      grantPhysicalRoot := ResourceBirthCodec.physicalRoot (.live grantCell)
      parentPhysicalRoot := ResourceBirthCodec.physicalRoot (.live parentCell)
      pursePhysicalRoot := ResourceBirthCodec.physicalRoot (.live purseCell) }
  pure ⟨request, context, bindings, invocation⟩

def assembleReserve (plan : ReservePlan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let signed ← NativeHost.assemble plan.invocation signatures
  let .invoke command := signed
    | throw "lifetime reserve plan is not an invocation"
  pure (DeclaredResourceController.signedBytes
    plan.invocation.domain plan.invocation.semantics command)

structure PaidRequest where
  fixed : Request
  context : ApplicationAgentLifetimeDispatchReserveContext.Context
  reserveIndex : Nat
  deriving DecidableEq

def paidRequestStream : StreamCodec PaidRequest :=
  StreamCodec.xmap
    (StreamCodec.product requestStream
      (StreamCodec.product ApplicationAgentLifetimeDispatchReserveContext.contextStream
        StreamCodec.nat))
    (fun request => (request.fixed, request.context, request.reserveIndex))
    (fun (fixed, context, reserveIndex) => ⟨fixed, context, reserveIndex⟩)
    (by intro request; cases request; rfl)

def paidRequestCodec : LawfulCodec PaidRequest :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-PAID-AUTHOR-REQUEST/v3".toUTF8.toList
    paidRequestStream

structure PaidPlan where
  /-- The fixed request is compact here: full HTTP bytes occur once in
  `app.unsignedIngress`. -/
  request : PaidRequest
  app : ApplicationDispatchAuthoring.Plan
  grant : ApplicationAgentLifetimeGrant.Grant
  grantRoot : Digest
  grantObservationSlot : NativeHostCodec.SigningSlot
  bindings : SourceBindings
  reserveReceipt : NativeHostCodec.Receipt
  payer : NativeHostCodec.SigningPlan

def paidPlanStream : StreamCodec PaidPlan :=
  StreamCodec.xmap
    (StreamCodec.product paidRequestStream
      (StreamCodec.product ApplicationDispatchAuthoring.planStream
        (StreamCodec.product ApplicationAgentLifetimeGrant.grantStream
          (StreamCodec.product digestStream
            (StreamCodec.product NativeHostCodec.signingSlotStream
              (StreamCodec.product sourceBindingsStream
                (StreamCodec.product NativeHostCodec.receiptStream
                  NativeHostCodec.signingPlanStream)))))))
    (fun plan => (plan.request, plan.app, plan.grant, plan.grantRoot,
      plan.grantObservationSlot, plan.bindings, plan.reserveReceipt, plan.payer))
    (fun (request, app, grant, grantRoot, grantObservationSlot, bindings,
          reserveReceipt, payer) =>
      ⟨request, app, grant, grantRoot, grantObservationSlot, bindings,
        reserveReceipt, payer⟩)
    (by intro plan; cases plan; rfl)

def paidPlanCodec : LawfulCodec PaidPlan :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-PAID-AUTHOR-PLAN/v3".toUTF8.toList
    paidPlanStream

private def compactHttp (operationId : Nat) : ApplicationDispatchCodec.Request :=
  { operationId := operationId, method := [], path := [], query := [],
    headers := [], body := [] }

/-- After the v3 ordinary reserve commits, re-open the current image. The
historical grant and reserve are selected from this exact verified walk; the
signed app, payer and grant observation plans still require fresh native
event26 admission before any physical HTTP effect. -/
def preparePaidVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target)
    (request : PaidRequest) : Except String PaidPlan := do
  let fixed := request.fixed
  let base := request.context.base
  if fixed.fixed.purseTask != base.purseTask ||
      fixed.fixed.payerSubject != base.payerSubject ||
      fixed.fixed.reserveAmount != base.reserveAmount ||
      fixed.fixed.maximumCharge != base.maximumCharge ||
      fixed.fixed.reserveOperationId != base.reserveOperationId ||
      fixed.grantResource != request.context.grantResource ||
      fixed.grantIssueIndex != request.context.grantIssueIndex then
    throw "lifetime paid fixed custodian differs from reserve context"
  let grant ← certifiedGrant config verified fixed
  let grantCell ← currentGrantCell config verified grant
  let app ← ApplicationDispatchAuthoring.prepareWithLifetimeGrant config verified
    fixed.fixed.base.base fixed.grantIssueIndex fixed.fixed.base.task
    fixed.fixed.base.parentCapability fixed.fixed.base.parentObserveCapability
  let some unsigned := ApplicationDispatchAdmissionIngress.codec.decode app.unsignedIngress
    | throw "lifetime paid app plan is noncanonical"
  let probe : ApplicationAgentLifetimeDispatchIngress.Ingress :=
    { dispatch := unsigned, reserveContext := request.context
      reserveIndex := request.reserveIndex
      payerCapability := fixed.fixed.purseCapability
      payerObserve := fixed.fixed.purseObserve
      payerSigned := ⟨[], [], [], []⟩
      grantRoot := grantCell.payload.root
      grantObserveCapability := fixed.grantObserveCapability
      grantObservationEnvelope := [] }
  if !ApplicationAgentLifetimeDispatchIngress.matchesRoute probe
      grant.ingress.spec.grant grant.ticket.evidence.spec.ticket.resource grant.index then
    throw "lifetime paid context differs from current source app/grant plan"
  let some reserve := verified.reserves.find? (fun prior =>
      prior.index == request.reserveIndex)
    | throw "lifetime reserve absent from admitted history"
  if grant.index >= reserve.index then
    throw "lifetime grant must precede the reserve"
  let .ok bound := ApplicationAgentLifetimeDispatchReserveCore.bindContext
      reserve.raw request.context
    | throw "lifetime original reserve differs from grant-bound context"
  if verified.opened.durable.image.accepted[reserve.index]?.map
      DurableReceiverCodec.intentStream.encode !=
      some (DurableReceiverCodec.intentStream.encode reserve.raw.record) ||
      !decide (NativeHostReplay.dispatchPurseUntouched
        (verified.opened.durable.image.accepted.drop (reserve.index + 1))
        base.purseTask) then
    throw "lifetime reserve changed after original admission"
  let purseCell ← match verified.opened.directory.directory.slots base.purseTask with
    | .present cell => pure cell
    | _ => throw "current lifetime paid purse unavailable"
  let some purseState := ApplicationDispatchAgentPayer.stateAt base.purseTask purseCell
    | throw "current lifetime paid purse state unavailable"
  let some parent := unsigned.parent
    | throw "lifetime paid parent missing from source plan"
  let parentCell ← match verified.opened.directory.directory.slots parent.task with
    | .present cell => pure cell
    | _ => throw "current lifetime paid parent unavailable"
  if parentCell.payload.root != parent.root then
    throw "current lifetime paid parent differs from source plan"
  if purseState != AgentGrain.reserve bound.beforeState base.reserveAmount then
    throw "current lifetime paid hold differs from admitted reserve"
  let command : DeclaredResourceController.Command :=
    { subject := base.payerSubject
      expectedAuthorityRoot := verified.opened.authority.snapshot.cell.root
      nonce := ApplicationAgentLifetimeDispatchReserveContext.payerNonce request.context
      targets := [AgentGrain.Operation.target .input base.purseTask
        fixed.fixed.purseCapability purseCell.payload.root purseState
        (some fixed.fixed.purseObserve)] }
  let payer ← NativeHost.prepareLoaded config verified.opened
    (.invoke (DeclaredResourceController.commandCodec.encode command))
  let some selection := ApplicationDispatchAdmission.selectCommand unsigned
    | throw "lifetime paid app selector missing"
  let appCommand := ApplicationDispatchCommand.command unsigned.dispatch selection
    unsigned.parent
  let .ok prepared := DeclaredResourceController.prepare config.deployment config.profile
    ⟨config.federation, NativeHost.logicalHeight config verified.opened.durable⟩
    verified.opened.durable appCommand
    | throw "lifetime paid app command preparation refused"
  let grantObservationSlot ← ApplicationDispatchAuthoring.prepareObservationSlot
    config verified.opened unsigned selection prepared 4 fixed.grantResource
    fixed.grantObserveCapability grantCell.payload.root
  let compactBase : ApplicationDispatchAuthoring.Request :=
    { fixed.fixed.base.base with http := compactHttp base.httpOperationId }
  let compactFixed : Request :=
    { fixed with fixed := { fixed.fixed with
        base := { fixed.fixed.base with base := compactBase } } }
  let compactRequest : PaidRequest := { request with fixed := compactFixed }
  let compactApp : ApplicationDispatchAuthoring.Plan :=
    { app with request := compactBase }
  let bindings : SourceBindings :=
    { originalIssueReceipt := grant.ticket.receipt
      grantIssueReceipt := grant.receipt
      grantInitializedRoot := grant.finalRoot
      grantPhysicalRoot := ResourceBirthCodec.physicalRoot (.live grantCell)
      parentPhysicalRoot := ResourceBirthCodec.physicalRoot (.live parentCell)
      pursePhysicalRoot := ResourceBirthCodec.physicalRoot (.live purseCell) }
  pure ⟨compactRequest, compactApp, grant.ingress.spec.grant,
    grantCell.payload.root, grantObservationSlot, bindings,
    reserve.raw.receipt, payer⟩

/-- Assembly inserts detached app, grant-observation and payer signatures.
The complete event26 receiver rechecks every current and historical fact. -/
def assemblePaid (plan : PaidPlan)
    (appSignatures : List (List UInt8)) (grantSignature : List UInt8)
    (payerSignatures : List (List UInt8)) : Except String (List UInt8) := do
  let base := plan.request.context.base
  if plan.request.fixed.fixed.base.base.http != compactHttp base.httpOperationId ||
      plan.app.request.http != compactHttp base.httpOperationId ||
      grantSignature.length != 64 then
    throw "lifetime paid plan duplicates HTTP or has malformed grant signature"
  let appBytes ← ApplicationDispatchAuthoring.assemble plan.app appSignatures
  let some dispatch := ApplicationDispatchAdmissionIngress.codec.decode appBytes
    | throw "assembled lifetime app dispatch noncanonical"
  let some grantHeader := CredentialSignedEnvelopeController.headerCodec.decode
      plan.grantObservationSlot.header
    | throw "lifetime grant observation header noncanonical"
  let grantEnvelope := CredentialSignedEnvelopeController.envelopeCodec.encode
    ⟨grantHeader, grantSignature⟩
  let signed ← NativeHost.assemble plan.payer payerSignatures
  let .invoke payerSigned := signed
    | throw "lifetime payer plan is not an invocation"
  let ingress : ApplicationAgentLifetimeDispatchIngress.Ingress :=
    { dispatch := dispatch
      reserveContext := plan.request.context
      reserveIndex := plan.request.reserveIndex
      payerCapability := plan.request.fixed.fixed.purseCapability
      payerObserve := plan.request.fixed.fixed.purseObserve
      payerSigned := payerSigned
      grantRoot := plan.grantRoot
      grantObserveCapability := plan.request.fixed.grantObserveCapability
      grantObservationEnvelope := grantEnvelope }
  if !ApplicationAgentLifetimeDispatchIngress.matchesRoute ingress plan.grant
      base.ticketResource plan.request.context.grantIssueIndex then
    throw "assembled lifetime dispatch differs from signed reserve/grant"
  pure (ApplicationAgentLifetimeDispatchIngress.codec.encode ingress)

end Minidregg.Kernel.ApplicationAgentLifetimeDispatchPaidAuthoring
