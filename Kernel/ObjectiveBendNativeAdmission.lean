/- The Objective-only source/current-input/execution gate. This module creates
no current effect authority. The controller first verifies ALL original native
signatures/laws/audience checks, then supplies these exact current read tokens.
A closed registered policy selects source/input/output and resource envelopes;
actual full writes and guards are checked before an AcceptedInvocation exists. -/
import Kernel.ObjectiveBendNativeInput
import Kernel.ObjectiveBendPublishedPackage
import Kernel.ObjectiveBendPreparedOutput
import Compiler.ObjectiveBendCombinedResult
import Compiler.ObjectiveBendGenericResult
import Compiler.ObjectiveInvocationClaim
import Compiler.NativeInvocationProfile
import Theory.ResourceCost
namespace Minidregg.Kernel.ObjectiveBendNativeAdmission
open Minidregg.Compiler Minidregg.Theory
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandData
set_option autoImplicit false

/-- This is a new source-selected receiving edition. It does not relabel the
historical TT evaluator or assert source ticks are physical processor work. -/
def semanticsId : Digest := (Sp800185Cshake256.hash
  "DREGG.OBJECTIVE-BEND.NATIVE-SEMANTICS/v2".toUTF8.toList
  "objective-bend-1;Core4;typed-core.v2;lazy-demand-origin-thunks;global-root-and-field-capacity;current-native-authority;explicit-ordered-authenticated-input-footprint".toUTF8.toList).digest

def evaluatorId : Digest := (Sp800185Cshake256.hash
  "DREGG.OBJECTIVE-BEND.NATIVE-EVALUATOR/v1".toUTF8.toList
  "ObjectiveBendDemandData.executeWith(ObjectiveBendDemandCapacity.allows);Core4".toUTF8.toList).digest

def charge (c : ObjectiveInvocationClaim.Capacity) : ResourceCost.Charge
  | .incidences => c.incidences
  | .turnBytes => c.turnBytes
  | .memoryTouches => c.memoryTouches
  | .witnessBytes => c.witnessBytes
  | .proofWork => c.proofWork
  | .storageBytes => c.storageBytes
  | .networkBytes => c.networkBytes
  | .sideEffectCount => c.sideEffectCount
  | .feeDebit => c.feeDebit
  | .leaseByteBlocks => c.leaseByteBlocks

structure Tooling where
  parserSha256 : String
  frontendSha256 : String
  elaboratorSha256 : String
  deriving DecidableEq, Repr

def toolingStream : StreamCodec Tooling := StreamCodec.xmap
  (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream PolicyRecordCodec.stringStream))
  (fun t => (t.parserSha256,t.frontendSha256,t.elaboratorSha256))
  (fun t => ⟨t.1,t.2.1,t.2.2⟩) (by intro t; cases t; rfl)

structure Policy where
  edition : Digest
  sourceBytes : Nat
  maximum : ObjectiveInvocationClaim.Capacity
  outputs : List Digest
  /-- CLEAR disclosure audience; current native audience checks are additional. -/
  clearAudience : Digest
  /-- Explicit trusted elaborator boundary, included in the runtime profile. -/
  tooling : Tooling
  deriving DecidableEq, Repr

def policyStream : StreamCodec Policy := StreamCodec.xmap
  (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat (StreamCodec.product ObjectiveInvocationClaim.capacityStream
    (StreamCodec.product (StreamCodec.list digestStream) (StreamCodec.product digestStream toolingStream)))))
  (fun p => (p.edition,p.sourceBytes,p.maximum,p.outputs,p.clearAudience,p.tooling))
  (fun p => ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2⟩) (by intro p; cases p; rfl)

def policyFrame : List UInt8 := "DREGG/OBJECTIVE-BEND/NATIVE-POLICY".toUTF8.toList ++ [2]
def encodePolicy (p : Policy) : List UInt8 := policyFrame ++ policyStream.encode p
def decodePolicy (bytes : List UInt8) : Option Policy := do
  if bytes.take policyFrame.length != policyFrame then none else do
    let p ← policyStream.toLawful.decode (bytes.drop policyFrame.length)
    if encodePolicy p == bytes then some p else none

instance chargeLeDecidable (a b : ResourceCost.Charge) : Decidable (a ≤ b) :=
  decidable_of_iff (ResourceCost.Lane.allCheck (fun lane => decide (a lane ≤ b lane)) = true)
    (by simpa only [ResourceCost.Charge.le_iff,decide_eq_true_eq] using
      ResourceCost.Lane.allCheck_eq_true_iff (fun lane => decide (a lane ≤ b lane)))

def capacityWithin (a b : ObjectiveInvocationClaim.Capacity) : Bool :=
  decide (charge a ≤ charge b) && decide (a.typeFuel ≤ b.typeFuel) &&
  decide (a.sourceTicks ≤ b.sourceTicks) && decide (a.heap ≤ b.heap) &&
  decide (a.stack ≤ b.stack) && decide (a.outputNodes ≤ b.outputNodes) &&
  decide (a.outputBytes ≤ b.outputBytes) && decide (a.inputBytes ≤ b.inputBytes) &&
  decide (a.scalarBits ≤ b.scalarBits)

def readContext {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command) :
    ResourceObservationAdmission.Context deployment durable := ⟨prepared.directory,prepared.authority⟩

def readRequest {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command) (i : TargetIndex command) :
    Request command.targets[i].kind :=
  { requestFor prepared.authority.snapshot profile.semantics ambient command command.targets[i]
      (prepared.targets i).before.payload.root with
    verb := observeVerb command.targets[i].kind
    effectsDigest := (Sp800185Cshake256.hash "DREGG.RESOURCE.TRANSACTION.OBSERVE/v3".toUTF8.toList
      ((StreamCodec.product bytesStream StreamCodec.nat).encode
        (commandBytes prepared.authority.snapshot.domain profile.semantics command,command.targets[i].target))).digest }

structure Read {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (i : TargetIndex command) (envelope : List UInt8) where
  private mk ::
  selected : ResourceObservationAdmission.Prepared (readContext prepared) profile (readRequest prepared i)
    (operationMarker prepared.authority.snapshot.domain profile.semantics command)
    (command.targets[i].observeCapability.getD ⟨0⟩) (commandCodec.encode command)
  preparedExact : ResourceObservationAdmission.prepare (readContext prepared) profile (readRequest prepared i)
    (operationMarker prepared.authority.snapshot.domain profile.semantics command)
    (command.targets[i].observeCapability.getD ⟨0⟩) (commandCodec.encode command) = .ok selected
  checked : ResourceObservationAdmission.Checked selected envelope

def bindRead {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    {prepared : PreparedInvocation deployment profile ambient durable command} {i : TargetIndex command}
    {envelope : List UInt8}
    (selected : ResourceObservationAdmission.Prepared (readContext prepared) profile (readRequest prepared i)
      (operationMarker prepared.authority.snapshot.domain profile.semantics command)
      (command.targets[i].observeCapability.getD ⟨0⟩) (commandCodec.encode command))
    (exact : ResourceObservationAdmission.prepare (readContext prepared) profile (readRequest prepared i)
      (operationMarker prepared.authority.snapshot.domain profile.semantics command)
      (command.targets[i].observeCapability.getD ⟨0⟩) (commandCodec.encode command) = .ok selected)
    (checked : ResourceObservationAdmission.Checked selected envelope) : Read prepared i envelope :=
  ⟨selected,exact,checked⟩

abbrev Reads {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command) (envelopes : List (List UInt8)) :=
  (i : TargetIndex command) → Read prepared i (envelopes[i.val]?.getD [])

private def clearKeyEpoch : Digest := (Sp800185Cshake256.hash
  "DREGG.OBJECTIVE-BEND.CLEAR-NO-CRYPTOKEY/v1".toUTF8.toList []).digest
private def declarationId (name : String) : Digest := (Sp800185Cshake256.hash
  "DREGG.OBJECTIVE-BEND.SELECTED-DECLARATION/v1".toUTF8.toList
  (PolicyRecordCodec.stringStream.encode name)).digest

private def returnTargets (command : Command) : List Nat := (command.targets.zipIdx).filterMap fun (target,index) =>
  match target.payload with
  | .content content => if content.actions.any (fun action => match action with
      | .createAtom _ (.inlineObject schema) _ => schema == ObjectiveBendResultAdapter.storageSchema
      | _ => false) then some index else none
  | _ => none

def resultProfile (policy : Policy) (artifact : ObjectiveBendSourceArtifact.Artifact)
    (command : Command) : Option ObjectiveBendResultAdapter.Profile := do
  let [target] := returnTargets command | none
  pure ⟨ObjectiveBendSourceArtifact.identity artifact,declarationId artifact.declaration,
    artifact.declaration,"result",command.subject,clearKeyEpoch,policy.clearAudience,command.nonce,target⟩

def limits (c : ObjectiveInvocationClaim.Capacity) : Limits := ⟨c.heap,c.stack⟩
def budget (c : ObjectiveInvocationClaim.Capacity) : Budget := {ticks:=c.sourceTicks,nodes:=c.outputNodes,bytes:=c.outputBytes}
def scalarProfile (c : ObjectiveInvocationClaim.Capacity) : ObjectiveBendDemandCapacity.Profile := ⟨c.scalarBits⟩

def combinedCodec : Digest := (Sp800185Cshake256.hash
  "DREGG.OBJECTIVE-BEND.COMBINED-RESULT/v1".toUTF8.toList
  (digestStream.encode ObjectiveBendPlanAdapter.codecId ++ digestStream.encode ObjectiveBendResultAdapter.codecId)).digest

inductive Output {durable : Durable} (deployment : Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (result : ObjectiveBendResultAdapter.Profile) (command : Command) (source : AnnotatedTerm)
    (c : ObjectiveInvocationClaim.Capacity)
  | scalar (prepared : ObjectiveBendPreparedOutput.Prepared deployment loaded command source (limits c) (budget c) (scalarProfile c))
  | result (prepared : ObjectiveBendResultAdapter.PreparedResult result command source (limits c) (budget c) (scalarProfile c))
  | combined (prepared : ObjectiveBendCombinedResult.Prepared deployment loaded result command source (limits c) (budget c) (scalarProfile c))
  | generic (prepared : ObjectiveBendGenericResult.Prepared deployment loaded result command source (limits c) (budget c) (scalarProfile c))

def Output.plan {durable : Durable} {deployment : Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {result : ObjectiveBendResultAdapter.Profile} {command : Command} {source : AnnotatedTerm}
    {c : ObjectiveInvocationClaim.Capacity} : Output deployment loaded result command source c → BendWorldPlan.Plan
  | .scalar p => ObjectiveBendPreparedOutput.plan p
  | .result p => p.plan
  | .combined p => p.plan
  | .generic p => p.plan

def Output.execution {durable : Durable} {deployment : Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {result : ObjectiveBendResultAdapter.Profile} {command : Command} {source : AnnotatedTerm}
    {c : ObjectiveInvocationClaim.Capacity} : Output deployment loaded result command source c →
    ExecutionWith (ObjectiveBendDemandCapacity.allows (scalarProfile c)) (limits c) (budget c) source.term
  | .scalar p => p.execution
  | .result p => p.execution
  | .combined p => p.execution
  | .generic p => p.execution

theorem Output.exact {durable : Durable} {deployment : Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {result : ObjectiveBendResultAdapter.Profile} {command : Command} {source : AnnotatedTerm}
    {c : ObjectiveInvocationClaim.Capacity} (output : Output deployment loaded result command source c) :
    BendWorldPlan.matchesCommand output.plan command = true := by
  cases output with
  | scalar p => exact ObjectiveBendPreparedOutput.native_matches p
  | result p => exact p.nativeExact
  | combined p => exact p.nativeExact
  | generic p => exact p.nativeExact

/-- Complete native counters; proofWork remains a signed work envelope charged
by prepareCompute, while source and forcing ticks have their own exact cap. -/
def usage {durable : Durable} {deployment : Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {result : ObjectiveBendResultAdapter.Profile} {command : Command} {source : AnnotatedTerm}
    {c : ObjectiveInvocationClaim.Capacity} (output : Output deployment loaded result command source c)
    (inputBytes sourceBytes : List UInt8) (ingress : List UInt8)
    (writes : List DataWrite) (guards : List ReadGuard) : ResourceCost.Charge
  | .incidences => command.targets.length+1
  | .turnBytes => ingress.length
  | .memoryTouches => writes.length+guards.length+output.execution.extraction.result.state.heap.size
  | .witnessBytes => inputBytes.length+sourceBytes.length+
      ((output.plan.effects.map (fun e => BendWorldPlan.effectStream.encode e)).flatten.length +
       (output.plan.returns.map BendWorldPlan.encodeReturn).flatten.length)
  | .proofWork => c.proofWork
  | .storageBytes => (writes.map fun write => write.canonicalPostBytes.length).sum
  | .networkBytes => 0
  | .sideEffectCount => output.plan.effects.length
  | .feeDebit => c.feeDebit
  | .leaseByteBlocks => 0


structure SourceSelection {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (envelopes : List (List UInt8)) (reads : Reads prepared envelopes)
    (claim : ObjectiveInvocationClaim.Claim) (policy : Policy) where
  private mk ::
  index : TargetIndex command
  indexExact : index.val = claim.sourceIndex
  readonly : command.targets[index].payload = .read
  fullScope : ResourceObservationAdmission.readerFields (readContext prepared)
    command.targets[index].kind (command.targets[index].observeCapability.getD ⟨0⟩) = none
  payload : CellState.Materialized (CanonicalCellRegistry.materializer .content)
  observedExact : (reads index).selected.observed.before = ⟨.content,payload⟩
  loaded : ObjectiveBendArtifactSource.Loaded payload.logical ⟨claim.sourceAtom⟩ policy.sourceBytes
  package : ObjectiveBendPublishedPackage.Loaded payload.logical ⟨loaded.artifact.package⟩ policy.sourceBytes
  declarationExact : ObjectiveSourcePackage.selectedDeclaration package.package = some loaded.artifact.declaration
  parserExact : package.package.parserSha256 = policy.tooling.parserSha256
  frontendExact : package.package.frontendSha256 = policy.tooling.frontendSha256
  inputCodecExact : loaded.artifact.inputCodec = ObjectiveBendNativeInput.codecId
  claimInputExact : claim.inputCodec = loaded.artifact.inputCodec
  outputCodecExact : claim.outputCodec = loaded.artifact.outputCodec
  outputRegistered : loaded.artifact.outputCodec ∈ policy.outputs

private def selectSource {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (envelopes : List (List UInt8)) (reads : Reads prepared envelopes)
    (claim : ObjectiveInvocationClaim.Claim) (policy : Policy) :
    Option (SourceSelection prepared envelopes reads claim policy) := do
  if valid : claim.sourceIndex < command.targets.length then
    let index : TargetIndex command := ⟨claim.sourceIndex,valid⟩
    if readonly : command.targets[index].payload = .read then
      if full : ResourceObservationAdmission.readerFields (readContext prepared)
          command.targets[index].kind (command.targets[index].observeCapability.getD ⟨0⟩) = none then
        match observed : (reads index).selected.observed.before with
        | ⟨.content,payload⟩ =>
          let loaded ← ObjectiveBendArtifactSource.lookupWithin payload.logical ⟨claim.sourceAtom⟩
            policy.sourceBytes claim.capacity.typeFuel
          let package ← ObjectiveBendPublishedPackage.lookup payload.logical ⟨loaded.artifact.package⟩ policy.sourceBytes
          if declaration : ObjectiveSourcePackage.selectedDeclaration package.package = some loaded.artifact.declaration then
            if parser : package.package.parserSha256 = policy.tooling.parserSha256 then
              if frontend : package.package.frontendSha256 = policy.tooling.frontendSha256 then
                if input : loaded.artifact.inputCodec = ObjectiveBendNativeInput.codecId then
                  if claimInput : claim.inputCodec = loaded.artifact.inputCodec then
                    if output : claim.outputCodec = loaded.artifact.outputCodec then
                      if registered : loaded.artifact.outputCodec ∈ policy.outputs then
                        some ⟨index,rfl,readonly,full,payload,observed,loaded,package,declaration,parser,frontend,input,claimInput,output,registered⟩
                      else none
                    else none
                  else none
                else none
              else none
            else none
          else none
        | _ => none
      else none
    else none
  else none

def inputRefAt (command : Command) (i : TargetIndex command) : ObjectiveInvocationClaim.InputRef :=
  ⟨command.targets[i].kind,command.targets[i].target,command.targets[i].expectedTargetRoot,
    command.targets[i].observeCapability.getD ⟨0⟩⟩

/-- The signed input manifest selects exact current roles in its authored order.
Generated output targets do not enter the input unless explicitly selected. -/
structure SelectedInputs (command : Command) (claim : ObjectiveInvocationClaim.Claim) where
  private mk ::
  indices : List (TargetIndex command)
  exact : indices.map (inputRefAt command) = claim.inputRefs
  capabilities : ∀ i ∈ indices, command.targets[i].observeCapability.isSome = true

def selectInputs (command : Command) (claim : ObjectiveInvocationClaim.Claim) :
    Option (SelectedInputs command claim) := do
  let indices ← claim.inputRefs.mapM fun ref => ObjectiveNativeScalarBinding.indexOf command ref.resource
  if exact : indices.map (inputRefAt command) = claim.inputRefs then
    if capabilities : ∀ i ∈ indices, command.targets[i].observeCapability.isSome = true then
      some ⟨indices,exact,capabilities⟩
    else none
  else none

private def inputReads {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (envelopes : List (List UInt8)) (reads : Reads prepared envelopes)
    (indices : List (TargetIndex command)) :
    List (ObjectiveBendNativeInput.AdmittedRead (readContext prepared) profile command.subject) :=
  indices.map fun i => ObjectiveBendNativeInput.admitRead command.subject
    (reads i).selected (reads i).checked rfl prepared.compute

/-- Current admitted source and authenticated applied initial term, before any
source demand. It cannot authorize a completed effect or certify a checkpoint. -/
structure InputPrepared {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (envelopes : List (List UInt8)) where
  private mk ::
  claim : ObjectiveInvocationClaim.Claim
  selected : command.objectiveClaim = .ok (some claim)
  semantics : NativeInvocationProfile.registered profile.receiverParameters .objectiveMethod = true
  policy : Policy
  policyExact : NativeInvocationProfile.binding profile.receiverParameters .objectiveMethod = some (encodePolicy policy)
  policyEdition : policy.edition = semanticsId
  capacities : capacityWithin claim.capacity policy.maximum = true
  reads : Reads prepared envelopes
  source : SourceSelection prepared envelopes reads claim policy
  selectedInputs : SelectedInputs command claim
  input : ObjectiveBendNativeInput.Input
  inputExact : input = ⟨command.subject,command.nonce,claim.arguments,
    (inputReads prepared envelopes reads selectedInputs.indices).map ObjectiveBendNativeInput.AdmittedRead.value⟩
  inputCommitted : ObjectiveInvocationClaim.inputCommitment (ObjectiveBendNativeInput.encode input) = claim.expectedInput
  inputTerm : ObjectiveBendOpenRecursion.Term
  inputTermExact : ObjectiveBendNativeInput.sourceTerm input claim.capacity.inputBytes claim.capacity.scalarBits = .ok inputTerm
  typed : Checked (ObjectiveBendNativeInput.instantiate source.loaded.checked.packet.source inputTerm) []
  funding : ∃ funded, prepared.compute = some funded ∧
    funded.steps = claim.capacity.proofWork ∧ funded.credits = claim.capacity.feeDebit

def InputPrepared.applied {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    {prepared : PreparedInvocation deployment profile ambient durable command} {envelopes : List (List UInt8)}
    (input : InputPrepared prepared envelopes) : AnnotatedTerm :=
  ObjectiveBendNativeInput.instantiate input.source.loaded.checked.packet.source input.inputTerm

def InputPrepared.contextBytes {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    {prepared : PreparedInvocation deployment profile ambient durable command} {envelopes : List (List UInt8)}
    (input : InputPrepared prepared envelopes) : List UInt8 :=
  "DREGG/OBJECTIVE-BEND/ADMITTED-INPUT-CONTEXT".toUTF8.toList ++ [1] ++
  ObjectiveInvocationClaim.encode input.claim ++ ObjectiveBendNativeInput.encode input.input ++
  digestStream.encode (ObjectiveBendSourceArtifact.identity input.source.loaded.artifact)

/-- This evidence is indexed by the SAME prepared native command/image and
final full ingress/write/guard lists. It contains no signature/law permission. -/
structure Admitted {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (envelopes : List (List UInt8)) (ingress : List UInt8)
    (writes : List DataWrite) (guards : List ReadGuard) where
  private mk ::
  claim : ObjectiveInvocationClaim.Claim
  selected : command.objectiveClaim = .ok (some claim)
  semantics : NativeInvocationProfile.registered profile.receiverParameters .objectiveMethod = true
  policy : Policy
  policyExact : NativeInvocationProfile.binding profile.receiverParameters .objectiveMethod = some (encodePolicy policy)
  policyEdition : policy.edition = semanticsId
  capacities : capacityWithin claim.capacity policy.maximum = true
  reads : Reads prepared envelopes
  source : SourceSelection prepared envelopes reads claim policy
  selectedInputs : SelectedInputs command claim
  input : ObjectiveBendNativeInput.Input
  inputExact : input = ⟨command.subject,command.nonce,claim.arguments,
    (inputReads prepared envelopes reads selectedInputs.indices).map ObjectiveBendNativeInput.AdmittedRead.value⟩
  inputCommitted : ObjectiveInvocationClaim.inputCommitment (ObjectiveBendNativeInput.encode input) = claim.expectedInput
  inputTerm : ObjectiveBendOpenRecursion.Term
  inputTermExact : ObjectiveBendNativeInput.sourceTerm input claim.capacity.inputBytes claim.capacity.scalarBits = .ok inputTerm
  result : ObjectiveBendResultAdapter.Profile
  resultExact : result.sourceArtifact = ObjectiveBendSourceArtifact.identity source.loaded.artifact ∧
    result.selectedDeclaration = declarationId source.loaded.artifact.declaration ∧
    result.sourceEntry = source.loaded.artifact.declaration ∧ result.recipient = command.subject ∧
    result.audience = policy.clearAudience ∧ result.generation = command.nonce
  output : Output deployment prepared.directory result command
    (ObjectiveBendNativeInput.instantiate source.loaded.checked.packet.source inputTerm) claim.capacity
  codecExact : (claim.outputCodec = ObjectiveBendPlanAdapter.codecId ∧ ∃ p, output = .scalar p) ∨
    (claim.outputCodec = ObjectiveBendResultAdapter.codecId ∧ ∃ p, output = .result p) ∨
    (claim.outputCodec = combinedCodec ∧ ∃ p, output = .combined p) ∨
    (claim.outputCodec = ObjectiveBendGenericResult.codecId ∧ ∃ p, output = .generic p)
  funding : ∃ funded, prepared.compute = some funded ∧
    funded.steps = claim.capacity.proofWork ∧ funded.credits = claim.capacity.feeDebit
  readsCurrent : ∀ guard ∈ output.plan.reads, guard ∈ guards ∨
    ∃ write ∈ writes, guard.cellId = write.cellId ∧ guard.expectedRoot = write.expectedPre
  fits : usage output (ObjectiveBendNativeInput.encode input) (source.loaded.record.payload ++ source.package.record.payload) ingress writes guards ≤ charge claim.capacity

private def selectResult (policy : Policy) (artifact : ObjectiveBendSourceArtifact.Artifact)
    (command : Command) (codec : Digest) : Option ObjectiveBendResultAdapter.Profile :=
  if codec = ObjectiveBendPlanAdapter.codecId then
    some ⟨ObjectiveBendSourceArtifact.identity artifact,declarationId artifact.declaration,
      artifact.declaration,"result",command.subject,clearKeyEpoch,policy.clearAudience,command.nonce,0⟩
  else resultProfile policy artifact command

private def checkOutput {durable : Durable} (deployment : Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (result : ObjectiveBendResultAdapter.Profile) (command : Command) (source : AnnotatedTerm)
    (claim : ObjectiveInvocationClaim.Claim) (checked : Checked source []) : Except Reject
    ({output : Output deployment loaded result command source claim.capacity //
      (claim.outputCodec = ObjectiveBendPlanAdapter.codecId ∧ ∃ p, output = .scalar p) ∨
      (claim.outputCodec = ObjectiveBendResultAdapter.codecId ∧ ∃ p, output = .result p) ∨
      (claim.outputCodec = combinedCodec ∧ ∃ p, output = .combined p) ∨
    (claim.outputCodec = ObjectiveBendGenericResult.codecId ∧ ∃ p, output = .generic p)}) := do
  if codec : claim.outputCodec = ObjectiveBendPlanAdapter.codecId then
    let prepared ← (ObjectiveBendPreparedOutput.prepare deployment loaded command source claim.capacity.typeFuel
      (limits claim.capacity) (budget claim.capacity) (scalarProfile claim.capacity)).mapError (fun _ => Reject.bendExecution)
    pure ⟨.scalar prepared,Or.inl ⟨codec,prepared,rfl⟩⟩
  else if codec : claim.outputCodec = ObjectiveBendResultAdapter.codecId then
    let prepared ← (ObjectiveBendResultAdapter.prepare result command source claim.capacity.typeFuel
      (limits claim.capacity) (budget claim.capacity) (scalarProfile claim.capacity)).mapError (fun _ => Reject.bendExecution)
    pure ⟨.result prepared,Or.inr (Or.inl ⟨codec,prepared,rfl⟩)⟩
  else if codec : claim.outputCodec = combinedCodec then
    let prepared ← (ObjectiveBendCombinedResult.prepare deployment loaded result command source claim.capacity.typeFuel
      (limits claim.capacity) (budget claim.capacity) (scalarProfile claim.capacity)).mapError (fun _ => Reject.bendExecution)
    pure ⟨.combined prepared,Or.inr (Or.inr (Or.inl ⟨codec,prepared,rfl⟩))⟩
  else if codec : claim.outputCodec = ObjectiveBendGenericResult.codecId then
    let prepared ← (ObjectiveBendGenericResult.prepareChecked deployment loaded result command source checked
      (limits claim.capacity) (budget claim.capacity) (scalarProfile claim.capacity)).mapError (fun _ => Reject.bendExecution)
    pure ⟨.generic prepared,Or.inr (Or.inr (Or.inr ⟨codec,prepared,rfl⟩))⟩
  else throw .bendExecution

private def checkedFunding {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command) (claim : ObjectiveInvocationClaim.Claim) :
    Option {funded : RunComputeBudgetDomain.Prepared deployment durable.snapshot command.subject //
      prepared.compute = some funded ∧ funded.steps = claim.capacity.proofWork ∧ funded.credits = claim.capacity.feeDebit} :=
  match selected : prepared.compute with
  | none => none
  | some funded =>
    if steps : funded.steps = claim.capacity.proofWork then
      if credits : funded.credits = claim.capacity.feeDebit then some ⟨funded,rfl,steps,credits⟩ else none
    else none

/-- The controller supplies these reads only after current original authority
and law checks. This checks the exact applied source before any demand. -/
def prepareInput {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (envelopes : List (List UInt8)) (reads : Reads prepared envelopes) : Except Reject (InputPrepared prepared envelopes) := do
  match selected : command.objectiveClaim with
  | .error reason => throw reason
  | .ok none => throw .bendExecution
  | .ok (some claim) =>
    if semantics : NativeInvocationProfile.registered profile.receiverParameters .objectiveMethod = true then
      let some policyBytes := NativeInvocationProfile.binding profile.receiverParameters .objectiveMethod | throw .bendExecution
      let some policy := decodePolicy policyBytes | throw .bendExecution
      if policyExact : NativeInvocationProfile.binding profile.receiverParameters .objectiveMethod = some (encodePolicy policy) then
        if policyEdition : policy.edition = semanticsId then
          if capacities : capacityWithin claim.capacity policy.maximum = true then
            if evaluatorId ∈ profile.disabledEvaluators then throw .bendExecution
            if !ObjectiveSourcePackage.shaPin policy.tooling.elaboratorSha256 then throw .bendExecution
            let some funding := checkedFunding prepared claim | throw .computeFunding
            let some source := selectSource prepared envelopes reads claim policy | throw .bendExecution
            let some selectedInputs := selectInputs command claim | throw .bendExecution
            let input : ObjectiveBendNativeInput.Input := ⟨command.subject,command.nonce,claim.arguments,
              (inputReads prepared envelopes reads selectedInputs.indices).map ObjectiveBendNativeInput.AdmittedRead.value⟩
            if inputCommitted : ObjectiveInvocationClaim.inputCommitment (ObjectiveBendNativeInput.encode input) = claim.expectedInput then
             match inputTermExact : ObjectiveBendNativeInput.sourceTerm input claim.capacity.inputBytes claim.capacity.scalarBits with
             | .error _ => throw .bendExecution
             | .ok inputTerm =>
               let some typed := check (ObjectiveBendNativeInput.instantiate source.loaded.checked.packet.source inputTerm)
                 [] claim.capacity.typeFuel | throw .bendExecution
               pure ⟨claim,selected,semantics,policy,policyExact,policyEdition,capacities,reads,source,selectedInputs,input,rfl,inputCommitted,
                 inputTerm,inputTermExact,typed,⟨funding.1,funding.2⟩⟩
            else throw .bendExecution
          else throw .bendExecution
        else throw .bendExecution
      else throw .bendExecution
    else throw .bendExecution
/-- Called ONLY after current original native authority/read checks. Families
cannot fall through to ordinary admission; malformed source or output refuses. -/
def admit {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (envelopes : List (List UInt8)) (reads : Reads prepared envelopes) (ingress : List UInt8)
    (writes : List DataWrite) (guards : List ReadGuard) : Except Reject (Admitted prepared envelopes ingress writes guards) := do
  let initial ← prepareInput prepared envelopes reads
  let claim := initial.claim
  let policy := initial.policy
  let source := initial.source
  let input := initial.input
  let inputTerm := initial.inputTerm
  let some result := selectResult policy source.loaded.artifact command claim.outputCodec | throw .bendExecution
  if resultExact : result.sourceArtifact = ObjectiveBendSourceArtifact.identity source.loaded.artifact ∧
      result.selectedDeclaration = declarationId source.loaded.artifact.declaration ∧
      result.sourceEntry = source.loaded.artifact.declaration ∧ result.recipient = command.subject ∧
      result.audience = policy.clearAudience ∧ result.generation = command.nonce then
    let output ← checkOutput deployment prepared.directory result command initial.applied claim initial.typed
    if readsCurrent : ∀ guard ∈ output.1.plan.reads, guard ∈ guards ∨
        ∃ write ∈ writes, guard.cellId = write.cellId ∧ guard.expectedRoot = write.expectedPre then
      if fits : usage output.1 (ObjectiveBendNativeInput.encode input) (source.loaded.record.payload ++ source.package.record.payload) ingress writes guards ≤ charge claim.capacity then
        pure ⟨claim,initial.selected,initial.semantics,policy,initial.policyExact,initial.policyEdition,initial.capacities,
          initial.reads,source,initial.selectedInputs,input,initial.inputExact,initial.inputCommitted,inputTerm,initial.inputTermExact,result,resultExact,
          output.1,output.2,initial.funding,readsCurrent,fits⟩
      else throw .bendExecution
    else throw .bendExecution
  else throw .bendExecution

#assert_axioms Output.exact
end Minidregg.Kernel.ObjectiveBendNativeAdmission
