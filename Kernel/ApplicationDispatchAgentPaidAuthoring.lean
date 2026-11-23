/-
Source-owned v2 paid dispatch authoring. A fixed agent custodian supplies only
its configured selectors and exact HTTP request; Mini derives the reserve
context, current roots and signing headers from one verifier-opened image.
Detached signatures are never authority until event21 is admitted anew.
-/
module

public import Kernel.ApplicationDispatchAgentAuthoring
public import Kernel.ApplicationDispatchAgentReceiver

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

namespace Minidregg.Kernel.ApplicationDispatchAgentPaidAuthoring

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- The runtime allocates `reserveOperationId` before asking for the signed
reserve. The signer/caps/task selectors are fixed by operator custody, not
selected by HTTP. `base.http` is the sole body-bearing request. -/
structure Request where
  base : ApplicationDispatchAgentAuthoring.Request
  purseTask : Nat
  purseCapability : CapabilityId
  purseObserve : CapabilityId
  payerSubject : SubjectId
  reserveAmount : Int
  maximumCharge : Int
  reserveOperationId : Nat
  deriving DecidableEq

/-- Operator custody pins every selector and allowance. Only canonical HTTP
bytes and the one new reserve operation ID vary per call. A private Host route
must compare this value with its startup pin before exposing signing headers. -/
structure FixedSelectors where
  issueIndex : Nat
  ticketResource : Nat
  packageManifest : Nat
  snapshotManifest : Nat
  sessionObserve : CapabilityId
  manifestObserve : CapabilityId
  enrollmentObserve : CapabilityId
  parentTask : Nat
  parentCapability : CapabilityId
  parentObserve : CapabilityId
  purseTask : Nat
  purseCapability : CapabilityId
  purseObserve : CapabilityId
  payerSubject : SubjectId
  reserveAmount : Int
  maximumCharge : Int
  deriving DecidableEq

def Request.fixedSelectors (request : Request) : FixedSelectors :=
  { issueIndex := request.base.base.issueIndex
    ticketResource := request.base.base.ticketResource
    packageManifest := request.base.base.packageManifest
    snapshotManifest := request.base.base.snapshotManifest
    sessionObserve := request.base.base.sessionObserveCapability
    manifestObserve := request.base.base.manifestObserveCapability
    enrollmentObserve := request.base.base.enrollmentObserveCapability
    parentTask := request.base.task
    parentCapability := request.base.parentCapability
    parentObserve := request.base.parentObserveCapability
    purseTask := request.purseTask
    purseCapability := request.purseCapability
    purseObserve := request.purseObserve
    payerSubject := request.payerSubject
    reserveAmount := request.reserveAmount
    maximumCharge := request.maximumCharge }

def Request.matchesPin (request pin : Request) : Bool :=
  decide (request.fixedSelectors = pin.fixedSelectors)

def Request.matchesFixed (request : Request) (pin : FixedSelectors) : Bool :=
  decide (request.fixedSelectors = pin)

def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationDispatchAgentAuthoring.requestStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
          (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
            (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
              (StreamCodec.product IntStream.intStream
                (StreamCodec.product IntStream.intStream
                  StreamCodec.nat)))))))
    (fun request => (request.base, request.purseTask, request.purseCapability,
      request.purseObserve, request.payerSubject, request.reserveAmount,
      request.maximumCharge, request.reserveOperationId))
    (fun (base, purseTask, purseCapability, purseObserve, payerSubject,
          reserveAmount, maximumCharge, reserveOperationId) =>
      ⟨base, purseTask, purseCapability, purseObserve, payerSubject,
        reserveAmount, maximumCharge, reserveOperationId⟩)
    (by intro request; cases request; rfl)

def requestCodec : LawfulCodec Request :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-DISPATCH-AUTHOR-REQUEST/v2".toUTF8.toList
    requestStream

structure ReservePlan where
  request : Request
  context : ApplicationDispatchAgentReserveContext.Context
  invocation : NativeHostCodec.SigningPlan

def reservePlanStream : StreamCodec ReservePlan :=
  StreamCodec.xmap
    (StreamCodec.product requestStream
      (StreamCodec.product ApplicationDispatchAgentReserveContext.contextStream
        NativeHostCodec.signingPlanStream))
    (fun plan => (plan.request, plan.context, plan.invocation))
    (fun (request, context, invocation) => ⟨request, context, invocation⟩)
    (by intro plan; cases plan; rfl)

def reservePlanCodec : LawfulCodec ReservePlan :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-DISPATCH-RESERVE-PLAN/v2".toUTF8.toList
    reservePlanStream

/-- This must run before the ordinary reserve. A caller cannot assert a
ticket root, app/session identity, parent generation or purse generation. -/
private def reserveCommand (config : Config) (ground : ServedBasis.Ground config.deployment)
    (preparedBase : ApplicationDispatchAgentAuthoring.Plan)
    (issue : ApplicationDispatchHistoricalCore.IssuedEvidence config) (request : Request) :
    Except String (ApplicationDispatchAgentReserveContext.Context × DeclaredResourceController.Command) := do
  let parent := preparedBase.parent
  let some unsigned := ApplicationDispatchAdmissionIngress.codec.decode
      preparedBase.signing.unsignedIngress
    | throw "source dispatch plan is noncanonical"
  if request.purseTask == request.base.task then
    throw "dispatch purse overlaps agent parent"
  if request.reserveAmount < 0 || request.maximumCharge < 0 ||
      request.maximumCharge > request.reserveAmount then
    throw "dispatch reserve/charge bounds refused"
  let ticket := issue.spec.ticket
  let ticketCell ← match ground.directory.slots ticket.resource with
    | .present cell => pure cell
    | _ => throw "current ticket unavailable for reserve plan"
  if ticketCell.payload.root != unsigned.ticketRoot then
    throw "reserve plan ticket root differs from current dispatch"
  let purseCell ← match ground.directory.slots request.purseTask with
    | .present cell => pure cell
    | _ => throw "current dispatch purse unavailable"
  let some purseState := ApplicationDispatchAgentPayer.stateAt
      request.purseTask purseCell
    | throw "current dispatch purse state unavailable"
  if !(purseState.status == 1 || purseState.status == 2) ||
      purseState.reserved != 0 || request.reserveAmount > purseState.remaining then
    throw "dispatch purse cannot reserve requested allowance"
  let context : ApplicationDispatchAgentReserveContext.Context :=
    { domain := config.deployment.domain
      semantics := config.profile.semantics
      app := unsigned.dispatch.dispatch.app
      session := unsigned.dispatch.dispatch.session
      ticketResource := ticket.resource
      ticketRoot := unsigned.ticketRoot
      parentTask := parent.parent.task
      parentGeneration := parent.parent.state.generation
      purseTask := request.purseTask
      purseGeneration := purseState.generation
      payerSubject := request.payerSubject
      reserveAmount := request.reserveAmount
      maximumCharge := request.maximumCharge
      reserveOperationId := request.reserveOperationId
      httpOperationId := request.base.base.http.operationId
      requestDigest := ApplicationDispatchCodec.requestDigest request.base.base.http }
  let command : DeclaredResourceController.Command :=
    { subject := request.payerSubject
      nonce := ApplicationDispatchAgentReserveContext.nonce context
      targets := [AgentGrain.Operation.target (.reserve request.reserveAmount)
        request.purseTask request.purseCapability purseCell.payload.root
        purseState (some request.purseObserve)] }
  return (context, command)

def prepareReserveVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target) (request : Request) :
    Except String ReservePlan := do
  let preparedBase ← ApplicationDispatchAgentAuthoring.prepareVerified config
    verified request.base
  let some issue := verified.issues.find? (fun issue => issue.index == request.base.base.issueIndex)
    | throw "admitted share issue absent from reserve plan"
  let (context, command) ← reserveCommand config verified.opened.ground preparedBase issue.evidence request
  let invocation ← NativeHost.prepareInvokeOn config verified.opened.ground (logicalHeight config verified.opened.durable)
    (DeclaredResourceController.commandCodec.encode command)
  return ⟨request, context, invocation⟩

def planCommand (config : Config) (light : NativeHostLight.Light config)
    (command : DeclaredResourceController.Command) : ExceptT String IO NativeHostCodec.SigningPlan := do
  let keys := DeclaredResourceController.invocationKeys config.deployment.domain config.profile.semantics command
  let basis ← ExceptT.mk (light.basis keys)
  NativeHost.prepareInvokeOn config (.ofBasis basis) (config.genesisHeight + basis.height)
    (DeclaredResourceController.commandCodec.encode command)

def prepareReserveLight (config : Config) (light : NativeHostLight.Light config)
    (request : Request) : ExceptT String IO ReservePlan := do
  let (plan, issue) ← ApplicationDispatchAgentAuthoring.prepareLight config light request.base
  let basis ← ExceptT.mk (light.basis ⟨[], []⟩)
  let (context, command) ← reserveCommand config (.ofBasis basis) plan issue request
  return ⟨request, context, ← planCommand config light command⟩

/-- Detached reserve signatures produce the ordinary signed invocation.
Event21 later proves that this exact native reserve entered admitted history. -/
def assembleReserve (plan : ReservePlan) (signatures : List (List UInt8)) :
    Except String (List UInt8) := do
  let signed ← NativeHost.assemble plan.invocation signatures
  let .invoke command := signed
    | throw "dispatch reserve plan is not an invocation"
  pure (DeclaredResourceController.signedBytes
    plan.invocation.domain plan.invocation.semantics command)

structure PaidRequest where
  fixed : Request
  context : ApplicationDispatchAgentReserveContext.Context
  reserveIndex : Nat
  deriving DecidableEq

def paidRequestStream : StreamCodec PaidRequest :=
  StreamCodec.xmap
    (StreamCodec.product requestStream
      (StreamCodec.product ApplicationDispatchAgentReserveContext.contextStream
        StreamCodec.nat))
    (fun request => (request.fixed, request.context, request.reserveIndex))
    (fun (fixed, context, reserveIndex) => ⟨fixed, context, reserveIndex⟩)
    (by intro request; cases request; rfl)

def paidRequestCodec : LawfulCodec PaidRequest :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-DISPATCH-PAID-AUTHOR-REQUEST/v2".toUTF8.toList
    paidRequestStream

structure PaidPlan where
  /-- Fixed-selector carrier. Its HTTP fields are deliberately empty; the
  single full request is in `app.unsignedIngress`. -/
  request : PaidRequest
  app : ApplicationDispatchAuthoring.Plan
  payer : NativeHostCodec.SigningPlan

private def compactHttp (operationId : Nat) : ApplicationDispatchCodec.Request :=
  { operationId := operationId, method := [], path := [], query := [],
    headers := [], body := [] }

def paidPlanStream : StreamCodec PaidPlan :=
  StreamCodec.xmap
    (StreamCodec.product paidRequestStream
      (StreamCodec.product ApplicationDispatchAuthoring.planStream
        NativeHostCodec.signingPlanStream))
    (fun plan => (plan.request, plan.app, plan.payer))
    (fun (request, app, payer) => ⟨request, app, payer⟩)
    (by intro plan; cases plan; rfl)

def paidPlanCodec : LawfulCodec PaidPlan :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-DISPATCH-PAID-AUTHOR-PLAN/v2".toUTF8.toList
    paidPlanStream

/-- After the ordinary reserve has committed, prepare two independent
signatures at the same verified tip: the agent's app request and the payer's
current no-op witness. The final event21 receiver rechecks all of this. -/
private def paidCommand (config : Config) (ground : ServedBasis.Ground config.deployment)
    (request : PaidRequest) (app : ApplicationDispatchAgentAuthoring.Plan)
    (issue : ApplicationDispatchHistoricalCore.IssuedEvidence config)
    (reserve : ApplicationDispatchAgentReserveCore.RawEvidence config) :
    Except String DeclaredResourceController.Command := do
  if request.fixed.purseTask != request.context.purseTask ||
      request.fixed.payerSubject != request.context.payerSubject ||
      request.fixed.reserveAmount != request.context.reserveAmount ||
      request.fixed.maximumCharge != request.context.maximumCharge ||
      request.fixed.reserveOperationId != request.context.reserveOperationId then
    throw "paid dispatch fixed custodian differs from signed reserve context"
  let some unsigned := ApplicationDispatchAdmissionIngress.codec.decode
      app.signing.unsignedIngress
    | throw "noncanonical source app plan"
  if !ApplicationDispatchAgentReserveContext.matchesIngress request.context
      unsigned issue.spec.ticket.resource then
    throw "paid dispatch context differs from current source app plan"
  let .ok bound := reserve.bindContext request.context
    | throw "agent reserve differs from source context"
  let purseCell ← match ground.directory.slots
      request.context.purseTask with
    | .present cell => pure cell
    | _ => throw "current paid dispatch purse unavailable"
  let some purseState := ApplicationDispatchAgentPayer.stateAt
      request.context.purseTask purseCell
    | throw "current paid dispatch purse state unavailable"
  if purseState != AgentGrain.reserve bound.beforeState request.context.reserveAmount then
    throw "current paid dispatch hold differs from admitted reserve"
  let command : DeclaredResourceController.Command :=
    { subject := request.context.payerSubject
      nonce := ApplicationDispatchAgentPayer.payerNonce request.context
      targets := [AgentGrain.Operation.target .input request.context.purseTask
        request.fixed.purseCapability purseCell.payload.root purseState
        (some request.fixed.purseObserve)] }
  return command

private def compactPlan (request : PaidRequest) (app : ApplicationDispatchAgentAuthoring.Plan)
    (payer : NativeHostCodec.SigningPlan) : PaidPlan :=
  let compactBase : ApplicationDispatchAuthoring.Request :=
    { request.fixed.base.base with
      http := compactHttp request.context.httpOperationId }
  let compactFixed : Request :=
    { request.fixed with base := { request.fixed.base with base := compactBase } }
  let compactRequest : PaidRequest := { request with fixed := compactFixed }
  let compactApp : ApplicationDispatchAuthoring.Plan :=
    { app.signing with request := compactBase }
  ⟨compactRequest, compactApp, payer⟩


def preparePaidVerified (config : Config) {target : Durable}
    (verified : NativeHostReplay.Verified config target)
    (request : PaidRequest) : Except String PaidPlan := do
  let app ← ApplicationDispatchAgentAuthoring.prepareVerified config verified
    request.fixed.base
  let some issue := verified.issues.find? (fun issue =>
      issue.index == request.fixed.base.base.issueIndex)
    | throw "agent ticket issue absent from verified history"
  let some reserve := verified.reserves.find? (fun reserve =>
      reserve.index == request.reserveIndex)
    | throw "agent reserve absent from verified history"
  if verified.opened.durable.image.accepted[reserve.index]?.map
      DurableReceiverCodec.intentStream.encode !=
      some (DurableReceiverCodec.intentStream.encode reserve.raw.record) ||
      !decide (NativeHostReplay.dispatchPurseUntouched
        (verified.opened.durable.image.accepted.drop (reserve.index + 1))
        request.context.purseTask) then
    throw "agent reserve changed after original admission"
  let command ← paidCommand config verified.opened.ground request app issue.evidence reserve.raw
  let payer ← NativeHost.prepareInvokeOn config verified.opened.ground (logicalHeight config verified.opened.durable)
    (DeclaredResourceController.commandCodec.encode command)
  return compactPlan request app payer

def preparePaidLight (config : Config) (light : NativeHostLight.Light config)
    (request : PaidRequest) : ExceptT String IO PaidPlan := do
  let (app, issue) ← ApplicationDispatchAgentAuthoring.prepareLight config light request.fixed.base
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let reserve ← ExceptT.mk ((·.mapError (·.message)) <$> (NativeHostReplay.selectReserve config reader request.reserveIndex).run)
  let last ← ExceptT.mk ((·.mapError (·.message)) <$> reader.lastWrite ⟨request.context.purseTask⟩)
  if last.value.getD 0 > request.reserveIndex + 1 then throw "agent reserve changed after original admission"
  let basis ← ExceptT.mk (light.basis ⟨[], []⟩)
  let command ← paidCommand config (.ofBasis basis) request app issue reserve
  return compactPlan request app (← planCommand config light command)

/-- Assembly inserts detached app and payer signatures only. It is never a
substitute for event21 same-image native admission and exact CAS readback. -/
def assemblePaid (plan : PaidPlan) (appSignatures payerSignatures : List (List UInt8)) :
    Except String (List UInt8) := do
  if plan.request.fixed.base.base.http !=
      compactHttp plan.request.context.httpOperationId ||
      plan.app.request.http != compactHttp plan.request.context.httpOperationId then
    throw "paid plan duplicates or changes canonical HTTP request"
  let appBytes ← ApplicationDispatchAuthoring.assemble plan.app appSignatures
  let some dispatch := ApplicationDispatchAdmissionIngress.codec.decode appBytes
    | throw "assembled app dispatch noncanonical"
  if !ApplicationDispatchAgentReserveContext.matchesIngress plan.request.context
      dispatch plan.request.context.ticketResource then
    throw "assembled paid dispatch differs from reserve context"
  let signed ← NativeHost.assemble plan.payer payerSignatures
  let .invoke payerSigned := signed
    | throw "paid dispatch payer plan is not an invocation"
  pure (ApplicationDispatchAgentIngress.codec.encode
    ⟨dispatch, plan.request.context, plan.request.reserveIndex,
      plan.request.fixed.purseCapability, plan.request.fixed.purseObserve,
      payerSigned⟩)

end Minidregg.Kernel.ApplicationDispatchAgentPaidAuthoring
