/- Objective invocation quotation: locally retained request → final command.

The producer never accepts a remote final command, claimed output or
`expectedInput`. On ONE locally opened image it:
1. builds the command-free `Environment` (subject, nonce, the actual fee-first
   compute preparation from the request's funding);
2. authenticates the request's signed source/input queries through the SAME
   oracle the receiver installs, and derives `expectedInput` from those reads;
3. runs the SAME `ObjectiveBendNativeAdmission.prepareCore` on the derived claim;
4. evaluates the applied source ONCE with no command
   (`ObjectiveInvocationLayout.*Source`, equal to every admission token's
   outcome by `*Source_exact`) and places each source effect on its selected
   role, in plan order, funding last (`effectsOf_layout`);
5. re-runs the full receiving gate (`prepareFrom`, `select`, `admit`) on the
   final command, unsigned: target signatures are the signer's to add.
The returned plan is "Core4 executeWith output" (evaluator
`ObjectiveBendNativeAdmission.evaluatorId`), not a source-semantics theorem.
Quotation reserves no authority and spends nothing. -/
import Kernel.NativeHost
import Kernel.ObjectiveBendAuthenticatedInputs
import Compiler.ObjectiveBendQuoteRequest
import Compiler.ObjectiveInvocationLayout
import Lean.Data.Json
namespace Minidregg.Host.ObjectiveInvocationQuote
open Minidregg.Compiler Minidregg.Kernel Minidregg.Theory
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.ObjectiveBendTypes Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandData
open Lean (Json)
set_option autoImplicit false

abbrev Request := ObjectiveBendQuoteRequest.Request
abbrev Admission := Minidregg.Kernel.ObjectiveBendNativeAdmission

/-- The claim this request would sign, for a given input commitment. -/
def claimOf (request : Request) (expectedInput : Digest) : ObjectiveInvocationClaim.Claim :=
  ⟨request.source.ref,request.source.envelope,request.source.atom,request.inputCodec,
    request.outputCodec,request.arguments,request.inputRefs,request.inputEnvelopes,expectedInput,
    request.capacity⟩

/-- The command-free admission environment on this opened image. The funding
index is a position in a command that does not exist yet; budget and Book
preparation do not read it (`Prepared.relocate_budget_exact`). -/
def environmentOf (config : Config) (opened : Opened config) (request : Request) :
    Except String (Admission.Environment config.deployment opened.durable) := do
  let some clock := ClockCellDomain.load config.deployment opened.durable.snapshot
    | throw "clock unavailable"
  let compute ← (RunComputeBudgetDomain.prepare config.deployment opened.durable.snapshot clock.clock
      request.subject request.capacity.proofWork (request.funding.map fun funding => funding.input 0)).mapError
    fun _ => "compute funding refused"
  pure ⟨observationContext config opened,config.federation,config.genesisHeight,request.subject,
    request.nonce,some compute⟩

/-- One source effect before it has a command position. -/
structure Placed where
  resource : Nat
  root : Digest
  payload : Payload

def roleFor (request : Request) (resource : Nat) : Option ObjectiveBendQuoteRequest.Role :=
  request.roles.find? fun role => role.resource == resource

/-- Every role as a read placeholder: only the result role's POSITION is read
from it (`ObjectiveBendGenericResult.augment` reads target id and root). -/
def skeleton (request : Request) : Command :=
  { subject := request.subject, nonce := request.nonce,
    targets := request.roles.map fun role => role.target .read }

def resultIndex (request : Request) : Except String Nat :=
  match request.roles.findIdx? (fun role => role.resource == request.resultResource) with
  | some index => .ok index
  | none => .error "result resource has no selected role"

/-- Command-free evaluation of the applied source and placement of its effects,
in source plan order, by the registered output codec. -/
def placed {F : Type} [Field F] [DecidableEq F] {deployment : CanonicalCellRegistry.Deployment}
    {durable : Admission.Durable} {environment : Admission.Environment deployment durable}
    {profile : CanonicalRuntimeProfile.Profile F} {claim : ObjectiveInvocationClaim.Claim}
    (request : Request) (core : Admission.Core environment profile claim) : Except String (List Placed) := do
  let capacity := Admission.scalarProfile claim.capacity
  let limits := Admission.limits claim.capacity
  let budget := Admission.budget claim.capacity
  let term := core.applied.term
  let profileAt (index : Nat) :=
    Admission.profileAt core.policy core.source.loaded.artifact request.subject request.nonce index
  let resultEffect (type : Ty) (value : Data) : Except String Placed := do
    let some bytes := ObjectiveBendResultAdapter.encodeData budget.nodes value
      | throw "result value exceeds its output bound"
    let index ← resultIndex request
    let profile := profileAt index
    let slot := ObjectiveBendResultAdapter.returnSlot profile type bytes
    let some role := roleFor request request.resultResource | throw "result resource has no selected role"
    pure ⟨request.resultResource,role.root,(ObjectiveBendResultAdapter.returnEffect profile slot).payload⟩
  let scalarEffects (native : ObjectiveNativeScalarBinding.NativePlan) : List Placed :=
    native.effects.map fun scalar =>
      ⟨scalar.ref.resourceID,scalar.ref.root,(ObjectiveNativeScalarBinding.effect 0 scalar).payload⟩
  if claim.outputCodec = ObjectiveBendPlanAdapter.codecId then
    let some native := ObjectiveInvocationLayout.scalarSource capacity limits budget term
      | throw "source did not produce a scalar plan"
    pure (scalarEffects native)
  else if claim.outputCodec = ObjectiveBendResultAdapter.codecId then
    let some value := ObjectiveInvocationLayout.resultSource capacity limits budget term
      | throw "source did not finish"
    pure [← resultEffect core.typed.type value]
  else if claim.outputCodec = Admission.combinedCodec then
    let some (native,resultData) := ObjectiveInvocationLayout.combinedSource capacity limits budget term
      | throw "source did not produce a plan/result envelope"
    let .field "plan" _ (.field "result" resultType .emptyRow) := core.typed.type
      | throw "source type is not a plan/result envelope"
    pure (scalarEffects native ++ [← resultEffect resultType resultData])
  else if claim.outputCodec = ObjectiveBendGenericResult.codecId then
    let some (native,resultData) := ObjectiveInvocationLayout.genericSource capacity limits budget term
      | throw "source did not produce a plan/result envelope"
    let .field "plan" _ (.field "result" resultType .emptyRow) := core.typed.type
      | throw "source type is not a plan/result envelope"
    let some bytes := ObjectiveBendResultAdapter.encodeData budget.nodes resultData
      | throw "result value exceeds its output bound"
    let index ← resultIndex request
    let slot := ObjectiveBendResultAdapter.returnSlot (profileAt index) resultType bytes
    let some augmented := ObjectiveBendGenericResult.augment (profileAt index) (skeleton request) slot native.effects
      | throw "result target cannot carry the return atom"
    pure (augmented.map fun effect => ⟨effect.ref.resourceID,effect.ref.root,effect.payload⟩)
  else throw "unregistered output codec"

/-- Effect targets in plan order on their selected roles, then the funding leg
last. Roles the source did not write are not targets. -/
def layout (request : Request) (effects : List Placed) : Except String (List Target) := do
  let targets ← effects.mapM fun effect => do
    let some role := roleFor request effect.resource
      | throw s!"source wrote resource {effect.resource}, which the request did not select"
    if role.root != effect.root then throw s!"source effect root differs from role {effect.resource}"
    pure (role.target effect.payload)
  let funding ← match request.funding with
    | none => pure []
    | some funding => do
      let some role := roleFor request funding.payer | throw "funding payer has no selected role"
      if targets.any (fun target => target.target == funding.payer) then
        throw "the payer account is also an effect target"
      pure [role.target (.computeFunding ⟨funding.asset,funding.credits,funding.expectedPayerBalance,
        funding.expectedBookRoot⟩)]
  pure (ObjectiveInvocationLayout.layout targets funding)

structure Derived where
  claim : ObjectiveInvocationClaim.Claim
  command : Command
  plan : BendWorldPlan.Plan

def planBytes (plan : BendWorldPlan.Plan) : List UInt8 :=
  (plan.effects.map BendWorldPlan.effectStream.encode).flatten ++
    (plan.returns.map BendWorldPlan.encodeReturn).flatten

/-- The producer. Every refusal names its stage; nothing is retried with a
new nonce. -/
def derive (config : Config) (opened : Opened config) (request : Request) :
    IO (Except String Derived) := do
  if !ObjectiveBendQuoteRequest.wellFormed request then return .error "malformed request"
  let environment ← match environmentOf config opened request with
    | .error reason => return .error reason
    | .ok environment => pure environment
  let draft := claimOf request (ObjectiveInvocationClaim.inputCommitment [])
  let authenticated ← match ← ObjectiveBendAuthenticatedInputs.authorize config.signature environment
      config.profile draft with
    | .error reason => return .error s!"source/input queries refused: {repr reason}"
    | .ok authenticated => pure authenticated
  let input := Admission.inputOf authenticated
  let claim := claimOf request (ObjectiveInvocationClaim.inputCommitment (ObjectiveBendNativeInput.encode input))
  let core ← match ← Admission.prepareCore config.signature ObjectiveBendAuthenticatedInputs.oracle
      environment config.profile claim with
    | .error reason => return .error s!"source/input gate refused: {repr reason}"
    | .ok core => pure core
  -- Import/invoke source correspondence: the stored artifact (with its typed
  -- core) and package must equal this client's own pinned-frontend replay.
  if core.source.loaded.record.payload != request.source.expectedArtifact ||
      core.source.package.record.payload != request.source.expectedPackage then
    return .error "stored source differs from the locally replayed artifact/package"
  let effects ← match placed request core with
    | .error reason => return .error reason
    | .ok effects => pure effects
  let targets ← match layout request effects with
    | .error reason => return .error reason
    | .ok targets => pure targets
  let command : Command := { subject := request.subject, nonce := request.nonce, targets := targets,
    family := some (ObjectiveInvocationClaim.family claim) }
  let ambient : Ambient := ⟨config.federation,logicalHeight config opened.durable⟩
  match prepareFrom config.deployment config.profile ambient opened.durable (some opened.directory) command with
  | .error reason => return .error s!"final command preparation refused: {repr reason}"
  | .ok prepared =>
    match ← Admission.select config.signature ObjectiveBendAuthenticatedInputs.oracle prepared with
    | .error reason => return .error s!"final source/input gate refused: {repr reason}"
    | .ok selection =>
      let guards := readGuards prepared ++ selection.core.guards.filter fun guard =>
        decide (guard.cellId ∉ (writes prepared).map DataWrite.cellId)
      match Admission.admit selection (commandCodec.encode command) (writes prepared) guards with
      | .error reason => return .error s!"final output gate refused: {repr reason}"
      | .ok admitted => return .ok ⟨claim,command,admitted.output.plan⟩

def toJson (derived : Derived) : Json :=
  Json.mkObj [
    ("schema","dregg.objective-bend.quote.v1"),
    ("evidence","Core4 executeWith output"),
    ("evaluator",ObjectiveBendNativeInput.hex (digestStream.encode Admission.evaluatorId)),
    ("claim",ObjectiveBendNativeInput.hex (ObjectiveInvocationClaim.encode derived.claim)),
    ("expectedInput",ObjectiveBendNativeInput.hex (digestStream.encode derived.claim.expectedInput)),
    ("command",ObjectiveBendNativeInput.hex (commandCodec.encode derived.command)),
    ("plan",ObjectiveBendNativeInput.hex (planBytes derived.plan))]

/-- Host operation: decode a retained request, derive on a freshly walked
image, write the quote. -/
def quoteBytes (config : Config) (opened : Opened config) (bytes : List UInt8) : IO (Except String Json) := do
  let some request := ObjectiveBendQuoteRequest.decode bytes | return .error "noncanonical Objective request"
  match ← derive config opened request with
  | .error reason => return .error reason
  | .ok derived => return .ok (toJson derived)

end Minidregg.Host.ObjectiveInvocationQuote
