/-
Member app preparation and read-only current dispatch admission. Preparation
requires a current member signature over the exact domain/semantics/request and
five full current signed resource reads before returning the private planner's
headers. Readiness reuses the ordinary receiver's exact verified admission,
including chronological ticket evidence. Neither path receives a physical
permit, calls a receiver, appends, checkpoints, or invokes the app.
-/
module

public import Kernel.ApplicationDispatchAuthoring
public import Kernel.ApplicationDispatchReceiver
public import Kernel.CarriedApplicationDispatchReceiver
public import Lean.Data.Json

@[expose] public section

namespace Minidregg.Host.ApplicationDispatchReady

open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.NativeHost
open Minidregg.Theory.TypedAuthorization
open Lean

set_option autoImplicit false

/-- Distinct signature domain; decimal coordinates have explicit separators and
are followed by the existing canonical framed request. This signature is never
an invocation signature or permission to dispatch a physical request. -/
def authenticationBytes (config : Config) (request : List UInt8) : List UInt8 :=
  ("MINI/APPLICATION/AUTHENTICATED-PLAN/v1\n" ++
    toString config.deployment.domain.value ++ "\n" ++
    toString config.profile.semantics.value ++ "\n").toUTF8.toList ++ request

/-- The requester is told `undisclosed` and nothing else (the readiness probe discloses no
state-dependent reason); the operator's own log, this process's stderr, names the clause that
refused (`Compiler.RefusalReason.undisclosed`, `Kernel.NativeHost.logOperatorRefusal`). -/
private def logClause (clause : String) : IO Unit :=
  IO.eprintln s!"host: application readiness refused (operator log): {clause}"

private def stopped {α : Type} (clause : String) : IO (Except String α) := do
  logClause clause
  pure (.error "undisclosed")

private def authorizePlan (config : Config) (opened : Opened config)
    (requestBytes signature : List UInt8) (observations : List (List UInt8))
    (plan : ApplicationDispatchAuthoring.Plan) :
    IO (Except String ApplicationDispatchAuthoring.Plan) := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode plan.unsignedIngress
    | stopped "plan ingress does not decode"
  let dispatch := ingress.dispatch.dispatch
  if dispatch.session.origin != .human then return (← stopped "session origin is not human")
  if signature.length != 64 then return (← stopped "signature is not 64 bytes")
  let context := observationContext config opened
  let key := NativeObservationController.intentKey context dispatch.session.subject
  let verdict ← match key with
    | .error _ => pure (.ok false)
    | .ok publicKey => CredentialSignatureIO.verify config.signature publicKey (authenticationBytes config requestBytes) signature
  match NativeObservationController.authenticated key verdict with
  | .error reason => return (← stopped s!"member authentication: {repr reason}")
  | .ok _ => pure ()
  let targets : List (Nat × CapabilityId) :=
    [(dispatch.app.resource, ingress.dispatch.appObserveCapability),
     (dispatch.app.packageManifest, ingress.dispatch.manifestObserveCapability),
     (dispatch.session.resource, plan.request.sessionObserveCapability),
     (ingress.dispatch.enrollmentResource, ingress.dispatch.enrollmentObserveCapability),
     (plan.request.ticketResource, ingress.ticketObserveCapability)]
  if observations.length != targets.length then
    return (← stopped s!"{observations.length} observations for {targets.length} targets")
  for ((target, capability), bytes) in targets.zip observations do
    let some signed := NativeObservationCodec.signedCodec.decode bytes
      | do let r ← stopped s!"observation of resource {target} does not decode"
           return r
    let intent := signed.challenge.intent
    if intent.subject != dispatch.session.subject then
      return (← stopped s!"observation of resource {target} is for another subject")
    if intent.purpose != .query ⟨.object, target, .resource⟩ then
      return (← stopped s!"observation of resource {target} is not a resource query")
    if intent.grants != [⟨.object, target, capability⟩] then
      return (← stopped s!"observation of resource {target} does not carry exactly the declared grant")
    -- Narrowed reads do not authorize disclosure of a complete app plan.
    if (grantFields config opened intent.grants target).isSome then
      return (← stopped s!"observation of resource {target} is narrowed to fields")
    match ← NativeObservationController.authorize config.signature context
        config.profile config.federation config.genesisHeight signed with
    | .error reason => return (← stopped s!"observation of resource {target}: {repr reason}")
    | .ok _ => pure ()
  return .ok plan

def authenticatedPlanVerified {config : Config} {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (request signature : List UInt8) (observations : List (List UInt8)) :
    IO (Except String ApplicationDispatchAuthoring.Plan) := do
  let .ok plan := ApplicationDispatchAuthoring.prepareRequestVerified config old request
    | stopped "plan preparation refused"
  authorizePlan config old.opened request signature observations plan

def authenticatedPlanSuffix {config : Config} {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target)
    (request signature : List UInt8) (observations : List (List UInt8)) :
    IO (Except String ApplicationDispatchAuthoring.Plan) := do
  let .ok plan ← (ApplicationDispatchAuthoring.prepareRequestSuffix config old request).run
    | stopped "plan preparation refused"
  authorizePlan config old.opened request signature observations plan

private def refusedJson : Json := .mkObj
  [("type", "mini-application-ready-v1"), ("status", "refused"),
   ("reason", "undisclosed")]

private def refused (clause : String) : IO Json := do
  logClause clause
  pure refusedJson

private def readyJson (config : Config) (opened : Opened config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (admitted : NativeHostReplay.DispatchAt config opened ingress) : Json :=
  let dispatch := ingress.dispatch.dispatch
  let decimal := fun (n : Nat) => Json.str (toString n)
  let signedDecimal := fun (n : Int) => Json.str (toString n)
  .mkObj [("type", "mini-application-ready-v1"), ("status", "admitted"),
    ("origin", "native-current-dispatch-admission"), ("currentness", "at-observed-head"),
    ("domain", decimal config.deployment.domain.value),
    ("semantics", decimal config.profile.semantics.value),
    ("height", decimal (logicalHeight config opened.durable)),
    ("worldRoot", decimal opened.durable.worldRoot.value),
    ("app", decimal dispatch.app.resource), ("generation", signedDecimal dispatch.app.generation),
    ("session", decimal dispatch.session.resource),
    ("sessionGeneration", signedDecimal dispatch.session.generation),
    ("subject", decimal dispatch.session.subject.value),
    ("ticket", decimal admitted.prior.evidence.spec.ticket.resource),
    ("enrollment", decimal ingress.dispatch.enrollmentResource),
    ("operation", decimal dispatch.request.operationId),
    ("physicalDispatch", .bool false)]

def readyVerified {config : Config} {target : Durable}
    (old : NativeHostReplay.Verified config target) (bytes : List UInt8) : IO Json := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | refused "dispatch ingress does not decode"
  if ApplicationStreamContinuity.reservedProbe ingress.dispatch.dispatch.request then
    return (← refused "the request is the reserved stream probe")
  if ingress.dispatch.dispatch.session.origin != .human then
    return (← refused "session origin is not human")
  match ApplicationDispatchLookup.lookupVerified old bytes with
  | .ok none => pure ()
  | .ok (some _) => return (← refused "this dispatch is already admitted")
  | .error reason => return (← refused s!"dispatch lookup: {repr reason}")
  if (ApplicationDispatchReceiver.refusalAtTip? old ingress).isNone then
    return (← refused "the receiver holds no refusal at the tip for this dispatch")
  let .ok admitted ← NativeHostReplay.admitDispatchVerified old ingress
    | refused "dispatch admission refused"
  return readyJson config old.opened ingress admitted

def readySuffix {config : Config} {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8) : IO Json := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | refused "dispatch ingress does not decode"
  if ApplicationStreamContinuity.reservedProbe ingress.dispatch.dispatch.request then
    return (← refused "the request is the reserved stream probe")
  if ingress.dispatch.dispatch.session.origin != .human then
    return (← refused "session origin is not human")
  match CarriedApplicationDispatchReceiver.lookupVerified old bytes with
  | .ok none => pure ()
  | .ok (some _) => return (← refused "this dispatch is already admitted")
  | .error reason => return (← refused s!"dispatch lookup: {repr reason}")
  if (CarriedApplicationDispatchReceiver.refusalAtTip? old bytes).isNone then
    return (← refused "the receiver holds no refusal at the tip for this dispatch")
  let .ok admitted ← NativeHostReplay.admitDispatchSuffixVerified old ingress
    | refused "dispatch admission refused"
  return readyJson config old.opened ingress admitted

/-- Public readiness assembles the member's exact detached signatures locally;
ordinary operator op37 remains private. Final admission always rechecks source. -/
def assembledReadyVerified {config : Config} {target : Durable}
    (old : NativeHostReplay.Verified config target) (planBytes : List UInt8)
    (signatures : List (List UInt8)) : IO Json := do
  let some plan := ApplicationDispatchAuthoring.planCodec.decode planBytes
    | refused "plan does not decode"
  let .ok ingress := ApplicationDispatchAuthoring.assemble plan signatures
    | refused "the signatures do not assemble into the plan's ingress"
  readyVerified old ingress

def assembledReadySuffix {config : Config} {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target) (planBytes : List UInt8)
    (signatures : List (List UInt8)) : IO Json := do
  let some plan := ApplicationDispatchAuthoring.planCodec.decode planBytes
    | refused "plan does not decode"
  let .ok ingress := ApplicationDispatchAuthoring.assemble plan signatures
    | refused "the signatures do not assemble into the plan's ingress"
  readySuffix old ingress

end Minidregg.Host.ApplicationDispatchReady
