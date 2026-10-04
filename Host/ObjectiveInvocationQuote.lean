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
import Compiler.ObjectiveBendDataWire
import Lean.Data.Json
namespace Minidregg.Host.ObjectiveInvocationQuote
open Minidregg.Compiler Minidregg.Kernel Minidregg.Theory
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.ObjectiveBendTypes Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Lean (Json)
set_option autoImplicit false

abbrev Request := ObjectiveBendQuoteRequest.Request

/-- The claim this request would sign, for a given input commitment. -/
def claimOf (request : Request) (expectedInput : Digest) : ObjectiveInvocationClaim.Claim :=
  ⟨request.source.ref,request.source.envelope,request.source.atom,request.inputCodec,
    request.outputCodec,request.arguments,request.inputRefs,request.inputEnvelopes,expectedInput,
    request.capacity⟩

/-- The command-free admission environment on this opened image. The funding
index is a position in a command that does not exist yet; budget and Book
preparation do not read it (`Prepared.relocate_budget_exact`). -/
def environmentOf (config : Config) (opened : Opened config) (request : Request) :
    Except String (ObjectiveBendNativeAdmission.Environment config.deployment opened.durable) := do
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
    {durable : DeclaredResourceController.Durable} {environment : ObjectiveBendNativeAdmission.Environment deployment durable}
    {profile : CanonicalRuntimeProfile.Profile F} {claim : ObjectiveInvocationClaim.Claim}
    (request : Request) (core : ObjectiveBendNativeAdmission.Core environment profile claim) : Except String (List Placed) := do
  let capacity := ObjectiveBendNativeAdmission.scalarProfile claim.capacity
  let limits := ObjectiveBendNativeAdmission.limits claim.capacity
  let budget := ObjectiveBendNativeAdmission.budget claim.capacity
  let term := core.applied.term
  let profileAt (index : Nat) :=
    ObjectiveBendNativeAdmission.profileAt core.policy core.source.loaded.artifact request.subject request.nonce index
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
  else if claim.outputCodec = ObjectiveBendNativeAdmission.combinedCodec then
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
  artifact : ObjectiveBendSourceArtifact.Artifact

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
  if let some policyBytes := NativeInvocationProfile.binding config.profile.receiverParameters .objectiveMethod then
    if let some policy := ObjectiveBendNativeAdmission.decodePolicy policyBytes then
      let price := policy.tariff.workOf request.capacity
      if request.capacity.proofWork != price then
        return .error s!"proofWork {request.capacity.proofWork} is not the tariff price {price} of the declared envelope"
  let draft := claimOf request (ObjectiveInvocationClaim.inputCommitment [])
  let authenticated ← match ← ObjectiveBendAuthenticatedInputs.authorize config.signature environment
      config.profile draft with
    | .error reason => return .error s!"source/input queries refused: {repr reason}"
    | .ok authenticated => pure authenticated
  let input := ObjectiveBendNativeAdmission.inputOf authenticated
  let claim := claimOf request (ObjectiveInvocationClaim.inputCommitment (ObjectiveBendNativeInput.encode input))
  let core ← match ← ObjectiveBendNativeAdmission.prepareCore config.signature ObjectiveBendAuthenticatedInputs.oracle
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
  let command : Command :=
    { subject := request.subject, nonce := request.nonce, targets := targets,
      family := some (ObjectiveInvocationClaim.family claim) }
  let ambient : Ambient := ⟨config.federation,logicalHeight config opened.durable⟩
  match prepareFrom config.deployment config.profile ambient opened.durable (some opened.directory) command with
  | .error reason => return .error s!"final command preparation refused: {repr reason}"
  | .ok prepared =>
    match ← ObjectiveBendNativeAdmission.select config.signature ObjectiveBendAuthenticatedInputs.oracle prepared with
    | .error reason => return .error s!"final source/input gate refused: {repr reason}"
    | .ok selection =>
      -- The receiver's guard list less nothing it can compute without
      -- signatures: ordinary read guards, audience guards, then the route's
      -- consumed-read guards (`completeAdmissionGuards`). Ingress here is the
      -- unsigned command, so `turnBytes` must cover the signed envelope too.
      match ← checkAudiences prepared with
      | .error reason => return .error s!"final audience check refused: {repr reason}"
      | .ok audience =>
      let guards := admissionGuards prepared audience ++ selection.core.guards.filter fun guard =>
        decide (guard.cellId ∉ (writes prepared).map DataWrite.cellId)
      match ObjectiveBendNativeAdmission.admit selection (commandCodec.encode command) (writes prepared) guards with
      | .error reason => return .error s!"final output gate refused: {repr reason}"
      | .ok admitted => return .ok ⟨claim,command,admitted.output.plan,admitted.core.source.loaded.artifact⟩


/-! ## Request authoring from JSON (all numbers canonical decimal strings,
digests/bytes canonical lowercase hex) -/

private def field (json : Json) (name : String) : Except String Json :=
  (json.getObjVal? name).mapError fun _ => s!"missing {name}"

private def natOf (json : Json) (name : String) : Except String Nat := do
  let text ← ((← field json name).getStr?).mapError fun _ => s!"{name} must be a decimal string"
  let some value := text.toNat? | throw s!"{name} must be canonical decimal"
  if toString value != text then throw s!"{name} must be canonical decimal"
  pure value

private def intOf (json : Json) (name : String) : Except String Int := do
  let text ← ((← field json name).getStr?).mapError fun _ => s!"{name} must be a decimal string"
  let some value := text.toInt? | throw s!"{name} must be canonical decimal"
  if toString value != text then throw s!"{name} must be canonical decimal"
  pure value

private def bytesOf (json : Json) (name : String) : Except String (List UInt8) := do
  let text ← ((← field json name).getStr?).mapError fun _ => s!"{name} must be hex"
  let some bytes := ObjectiveBendPlanAdapter.unhex text.toList | throw s!"{name} must be lowercase hex"
  pure bytes

private def digestOf (json : Json) (name : String) : Except String Digest := do
  let some digest := ObjectiveNativeScalarBinding.rootCodec.decode (← bytesOf json name)
    | throw s!"{name} must be a canonical digest encoding"
  pure digest

private def kindOf (json : Json) : Except String TypedAuthorization.ResourceKind := do
  match ← ((← field json "kind").getStr?).mapError (fun _ => "kind must be a string") with
  | "object" => pure .object
  | "account" => pure .account
  | "program" => pure .program
  | _ => throw "kind must be object, account or program"

private def refOf (json : Json) : Except String ObjectiveInvocationClaim.InputRef := do
  pure ⟨← kindOf json,← natOf json "resource",← digestOf json "root",⟨← natOf json "capability"⟩⟩

private def arrayOf (json : Json) (name : String) : Except String (List Json) := do
  let array ← ((← field json name).getArr?).mapError fun _ => s!"{name} must be an array"
  pure array.toList

private def capacityOf (json : Json) : Except String ObjectiveInvocationClaim.Capacity := do
  pure ⟨← natOf json "typeFuel",← natOf json "sourceTicks",← natOf json "heap",← natOf json "stack",
    ← natOf json "outputNodes",← natOf json "outputBytes",← natOf json "inputBytes",← natOf json "scalarBits",
    ← natOf json "memoryTouches",← natOf json "proofWork",← natOf json "feeDebit",← natOf json "turnBytes",
    ← natOf json "witnessBytes",← natOf json "storageBytes",← natOf json "sideEffectCount",
    ← natOf json "networkBytes",← natOf json "leaseByteBlocks",← natOf json "incidences"⟩

private def roleOf (json : Json) : Except String ObjectiveBendQuoteRequest.Role := do
  let observe := (json.getObjVal? "observeCapability").toOption
  let observeCapability ← match observe with
    | none => pure none
    | some _ => pure (some ⟨← natOf json "observeCapability"⟩)
  pure
    { kind := ← kindOf json, resource := ← natOf json "resource", capability := ⟨← natOf json "capability"⟩,
      schemaVersion := ← natOf json "schemaVersion", root := ← digestOf json "root",
      observeCapability := observeCapability }

private def fundingOf (json : Json) : Except String ObjectiveBendQuoteRequest.Funding := do
  pure ⟨← natOf json "payer",⟨← natOf json "capability"⟩,← natOf json "asset",← natOf json "credits",
    ← intOf json "expectedPayerBalance",← digestOf json "expectedBookRoot"⟩

/-- The retained request, authored from JSON. `arguments` is the exact typed
argument packet text; its UTF-8 bytes are the claim's arguments. -/
def requestOfJson (json : Json) : Except String Request := do
  if (← field json "schema") != Json.str "dregg.objective-bend.request.v1" then
    throw "schema must be dregg.objective-bend.request.v1"
  let source ← field json "source"
  let arguments ← ((← field json "arguments").getStr?).mapError fun _ => "arguments must be the argument packet text"
  let funding := (json.getObjVal? "funding").toOption
  let request : Request := {
    subject := ⟨← natOf json "subject"⟩, nonce := ← natOf json "nonce",
    source := ⟨← refOf (← field source "ref"),← digestOf source "atom",← bytesOf source "expectedArtifact",
      ← bytesOf source "expectedPackage",← bytesOf source "envelope"⟩,
    arguments := arguments.toUTF8.toList,
    inputRefs := ← (← arrayOf json "inputRefs").mapM refOf,
    inputEnvelopes := ← (← arrayOf json "inputEnvelopes").mapM fun value => do
      let text ← (value.getStr?).mapError fun _ => "inputEnvelopes must be hex strings"
      let some bytes := ObjectiveBendPlanAdapter.unhex text.toList | throw "inputEnvelopes must be lowercase hex"
      pure bytes,
    capacity := ← capacityOf (← field json "capacity"),
    inputCodec := ← digestOf json "inputCodec", outputCodec := ← digestOf json "outputCodec",
    roles := ← (← arrayOf json "roles").mapM roleOf,
    resultResource := ← natOf json "resultResource",
    funding := ← match funding with
      | none => pure none
      | some value => some <$> fundingOf value }
  if !ObjectiveBendQuoteRequest.wellFormed request then throw "request is not well formed"
  pure request

/-- The signer's prepare intent for the derived command: one observe grant per
target that names an observe capability (the same grants an ordinary workspace
invocation carries). Its nonce is the intent's own, distinct from the command
nonce the source/input queries share. -/
def prepareIntent (derived : Derived) (intentNonce : Nat) : NativeObservationCodec.Intent :=
  ⟨derived.command.subject,intentNonce,
    .prepare (.invoke (commandCodec.encode derived.command)),
    derived.command.targets.filterMap fun target =>
      target.observeCapability.map fun capability => ⟨target.kind,target.target,capability⟩⟩

def toJson (derived : Derived) (intentNonce : Nat) : Json :=
  Json.mkObj [
    ("schema","dregg.objective-bend.quote.v2"),
    ("evidence","a deep source evaluation (not proved unique): Core4 executeWith output"),
    ("semanticId",ObjectiveBendNativeInput.hex (digestStream.encode
      (ObjectiveBendNativeAdmission.methodSemanticId derived.artifact))),
    ("artifactId",ObjectiveBendNativeInput.hex (digestStream.encode
      (ObjectiveBendNativeAdmission.methodArtifactId derived.artifact))),
    ("proofWork",toString derived.claim.capacity.proofWork),
    ("evaluator",ObjectiveBendNativeInput.hex (digestStream.encode ObjectiveBendNativeAdmission.evaluatorId)),
    ("claim",ObjectiveBendNativeInput.hex (ObjectiveInvocationClaim.encode derived.claim)),
    ("expectedInput",ObjectiveBendNativeInput.hex (digestStream.encode derived.claim.expectedInput)),
    ("command",ObjectiveBendNativeInput.hex (commandCodec.encode derived.command)),
    ("plan",ObjectiveBendNativeInput.hex (planBytes derived.plan)),
    ("intent",ObjectiveBendNativeInput.hex
      (NativeObservationCodec.intentCodec.encode (prepareIntent derived intentNonce))),
    -- The structured result as this signer's own evaluation produced it: the
    -- return atom the command stores (id and exact bytes) and its decoded value.
    ("returns",Json.arr (derived.plan.returns.map fun slot => Json.mkObj [
      ("atom",toString (BendWorldPlan.returnId slot).value),
      ("payload",ObjectiveBendNativeInput.hex (BendWorldPlan.encodeReturn slot)),
      ("value",match ObjectiveBendResultAdapter.decodeData
          (ObjectiveBendNativeAdmission.scalarProfile derived.claim.capacity)
          (ObjectiveBendNativeAdmission.budget derived.claim.capacity) slot.bytes with
        | some value => ObjectiveBendDataWire.dataJson value
        | none => Json.null)]).toArray)]

/-- Host operation: decode a retained request, derive on a freshly walked
image, write the quote. -/

private def hexDigest (digest : Digest) : Json :=
  .str (ObjectiveBendNativeInput.hex (digestStream.encode digest))

/-- Public constants an operator and a client need to author a policy and a
request: the edition, the evaluator, and every registered codec identity. -/
def constants : Json := Json.mkObj [
  ("schema","dregg.objective-bend.native-constants.v1"),
  ("semanticsId",hexDigest ObjectiveBendNativeAdmission.semanticsId),
  ("evaluatorId",hexDigest ObjectiveBendNativeAdmission.evaluatorId),
  ("inputCodec",hexDigest ObjectiveBendNativeInput.codecId),
  ("scalarCodec",hexDigest ObjectiveBendPlanAdapter.codecId),
  ("resultCodec",hexDigest ObjectiveBendResultAdapter.codecId),
  ("combinedCodec",hexDigest ObjectiveBendNativeAdmission.combinedCodec),
  ("genericCodec",hexDigest ObjectiveBendGenericResult.codecId),
  ("resultStorageSchema",hexDigest ObjectiveBendResultAdapter.storageSchema),
  ("frontEnd",Json.str ObjectiveBendFrontEndIdentity.identity)]

/-- Operator policy authoring: JSON → canonical policy hex for the
`objectiveInvocation` pin. The edition is always this build's semanticsId. -/
def authorPolicy (json : Json) : Except String String := do
  if (← field json "schema") != Json.str "dregg.objective-bend.policy.v1" then
    throw "schema must be dregg.objective-bend.policy.v1"
  let frontEnd ← ((← field json "frontEnd").getStr?).mapError fun _ => "frontEnd must be a string"
  if frontEnd != ObjectiveBendFrontEndIdentity.identity then
    throw s!"frontEnd must be this Host's front end {ObjectiveBendFrontEndIdentity.identity} (objective-constants)"
  let outputs ← (← arrayOf json "outputs").mapM fun value => do
    let hex ← (value.getStr?).mapError fun _ => "outputs must be hex digests"
    let some bytes := ObjectiveBendPlanAdapter.unhex hex.toList | throw "outputs must be lowercase hex"
    let some digest := ObjectiveNativeScalarBinding.rootCodec.decode bytes | throw "outputs must be digests"
    pure digest
  let tariff ← field json "tariff"
  let tariff : ObjectiveBendNativeAdmission.Tariff := ⟨← natOf tariff "version",← natOf tariff "base",
    ← natOf tariff "typeFuel",← natOf tariff "sourceTicks",← natOf tariff "heap",← natOf tariff "stack",
    ← natOf tariff "outputNodes",← natOf tariff "outputBytes",← natOf tariff "inputBytes"⟩
  if !tariff.valid then
    throw s!"tariff must be version {ObjectiveBendNativeAdmission.tariffVersion} with a positive base"
  let policy : ObjectiveBendNativeAdmission.Policy := ⟨ObjectiveBendNativeAdmission.semanticsId,← natOf json "sourceBytes",
    ← capacityOf (← field json "maximum"),outputs,← digestOf json "clearAudience",
    frontEnd,tariff⟩
  let encoded := ObjectiveBendNativeAdmission.encodePolicy policy
  if ObjectiveBendNativeAdmission.decodePolicy encoded != some policy then throw "policy does not round-trip"
  pure (ObjectiveBendNativeInput.hex encoded)

/-- Host operation `author objective-request`: JSON → canonical request bytes. -/
def authorRequest (json : Json) : Except String (List UInt8) :=
  (ObjectiveBendQuoteRequest.codec.encode ·) <$> requestOfJson json

def quoteBytes (config : Config) (opened : Opened config) (bytes : List UInt8) (intentNonce : Nat) :
    IO (Except String Json) := do
  let some request := ObjectiveBendQuoteRequest.decode bytes | return .error "noncanonical Objective request"
  if intentNonce == request.nonce then
    return .error "the prepare intent nonce must differ from the command nonce"
  match ← derive config opened request with
  | .error reason => return .error reason
  | .ok derived => return .ok (toJson derived intentNonce)

end Minidregg.Host.ObjectiveInvocationQuote
