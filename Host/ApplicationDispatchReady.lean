/-
Member app preparation and read-only current dispatch admission. Preparation
requires a current member signature over the exact domain/semantics/request and
five full current signed resource reads before returning the private planner's
headers. Readiness reuses the ordinary receiver's exact verified admission,
including chronological ticket evidence. Neither path receives a physical
permit, calls a receiver, appends, checkpoints, or invokes the app.
-/
import Kernel.ApplicationDispatchAuthoring
import Kernel.ApplicationDispatchReceiver
import Kernel.CarriedApplicationDispatchReceiver
import Lean.Data.Json

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

private def stopped {α : Type} : Except String α := .error "undisclosed"

private def authorizePlan (config : Config) (opened : Opened config)
    (requestBytes signature : List UInt8) (observations : List (List UInt8))
    (plan : ApplicationDispatchAuthoring.Plan) :
    IO (Except String ApplicationDispatchAuthoring.Plan) := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode plan.unsignedIngress
    | return stopped
  let dispatch := ingress.dispatch.dispatch
  if dispatch.session.origin != .human || signature.length != 64 then return stopped
  let context := observationContext config opened
  let key := NativeObservationController.intentKey context dispatch.session.subject
  let verdict ← match key with
    | .error _ => pure (.ok false)
    | .ok publicKey => CredentialSignatureIO.verify config.signature publicKey (authenticationBytes config requestBytes) signature
  match NativeObservationController.authenticated key verdict with
  | .error _ => return stopped
  | .ok _ => pure ()
  let targets : List (Nat × CapabilityId) :=
    [(dispatch.app.resource, ingress.dispatch.appObserveCapability),
     (dispatch.app.packageManifest, ingress.dispatch.manifestObserveCapability),
     (dispatch.session.resource, plan.request.sessionObserveCapability),
     (ingress.dispatch.enrollmentResource, ingress.dispatch.enrollmentObserveCapability),
     (plan.request.ticketResource, ingress.ticketObserveCapability)]
  if observations.length != targets.length then return stopped
  for ((target, capability), bytes) in targets.zip observations do
    let some signed := NativeObservationCodec.signedCodec.decode bytes | return stopped
    let intent := signed.challenge.intent
    if intent.subject != dispatch.session.subject then return stopped
    if intent.purpose != .query ⟨.object, target, .resource⟩ then return stopped
    if intent.grants != [⟨.object, target, capability⟩] then return stopped
    -- Narrowed reads do not authorize disclosure of a complete app plan.
    if (grantFields config opened intent.grants target).isSome then return stopped
    match ← NativeObservationController.authorize config.signature context
        config.profile config.federation config.genesisHeight signed with
    | .error _ => return stopped
    | .ok _ => pure ()
  return .ok plan

def authenticatedPlanVerified {config : Config} {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (request signature : List UInt8) (observations : List (List UInt8)) :
    IO (Except String ApplicationDispatchAuthoring.Plan) := do
  let .ok plan := ApplicationDispatchAuthoring.prepareRequestVerified config old request
    | return stopped
  authorizePlan config old.opened request signature observations plan

def authenticatedPlanSuffix {config : Config} {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target)
    (request signature : List UInt8) (observations : List (List UInt8)) :
    IO (Except String ApplicationDispatchAuthoring.Plan) := do
  let .ok plan := ApplicationDispatchAuthoring.prepareRequestSuffix config old request
    | return stopped
  authorizePlan config old.opened request signature observations plan

private def refused : Json := .mkObj
  [("type", "mini-application-ready-v1"), ("status", "refused"),
   ("reason", "undisclosed")]

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
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes | return refused
  if ApplicationStreamContinuity.reservedProbe ingress.dispatch.dispatch.request ||
      ingress.dispatch.dispatch.session.origin != .human then return refused
  match ApplicationDispatchLookup.lookupVerified old bytes with
  | .ok none => pure ()
  | _ => return refused
  if (ApplicationDispatchReceiver.refusalAtTip? old ingress).isNone then return refused
  let .ok admitted ← NativeHostReplay.admitDispatchVerified old ingress | return refused
  return readyJson config old.opened ingress admitted

def readySuffix {config : Config} {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8) : IO Json := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes | return refused
  if ApplicationStreamContinuity.reservedProbe ingress.dispatch.dispatch.request ||
      ingress.dispatch.dispatch.session.origin != .human then return refused
  match CarriedApplicationDispatchReceiver.lookupVerified old bytes with
  | .ok none => pure ()
  | _ => return refused
  if (CarriedApplicationDispatchReceiver.refusalAtTip? old bytes).isNone then return refused
  let .ok admitted ← NativeHostReplay.admitDispatchSuffixVerified old ingress | return refused
  return readyJson config old.opened ingress admitted

/-- Public readiness assembles the member's exact detached signatures locally;
ordinary operator op37 remains private. Final admission always rechecks source. -/
def assembledReadyVerified {config : Config} {target : Durable}
    (old : NativeHostReplay.Verified config target) (planBytes : List UInt8)
    (signatures : List (List UInt8)) : IO Json := do
  let some plan := ApplicationDispatchAuthoring.planCodec.decode planBytes | return refused
  let .ok ingress := ApplicationDispatchAuthoring.assemble plan signatures | return refused
  readyVerified old ingress

def assembledReadySuffix {config : Config} {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target) (planBytes : List UInt8)
    (signatures : List (List UInt8)) : IO Json := do
  let some plan := ApplicationDispatchAuthoring.planCodec.decode planBytes | return refused
  let .ok ingress := ApplicationDispatchAuthoring.assemble plan signatures | return refused
  readySuffix old ingress

end Minidregg.Host.ApplicationDispatchReady
