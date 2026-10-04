/- The Objective-only source/current-input/execution gate. This module creates
no current effect authority. The controller first verifies ALL original native
signatures/laws/audience checks. Source and program input enter ONLY as current
authorized reads (`AdmittedRead`, each carrying an unforgeable signature-checked
`ResourceObservationAdmission.Checked`) whose correspondence to the signed claim's
source and input refs is checked HERE (`Authenticated.sound`); no final-command
position or command-bound read token selects either. The reads are supplied by a
`ReadOracle` because the signed-query controller (NativeObservationController)
sits ABOVE DeclaredResourceController in the import order, through
NativeObservationCodec → NativeHostCodec (Intent's `prepare` Draft) and the
capability controllers. The default oracle refuses with the named
`Reject.noReadOracle`. The command-free `Core` is what quotation reuses.
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

def clearKeyEpoch : Digest := (Sp800185Cshake256.hash
  "DREGG.OBJECTIVE-BEND.CLEAR-NO-CRYPTOKEY/v1".toUTF8.toList []).digest
def declarationId (name : String) : Digest := (Sp800185Cshake256.hash
  "DREGG.OBJECTIVE-BEND.SELECTED-DECLARATION/v1".toUTF8.toList
  (PolicyRecordCodec.stringStream.encode name)).digest

private def returnTargets (command : Command) : List Nat := (command.targets.zipIdx).filterMap fun (target,index) =>
  match target.payload with
  | .content content => if content.actions.any (fun action => match action with
      | .createAtom _ (.inlineObject schema) _ => schema == ObjectiveBendResultAdapter.storageSchema
      | _ => false) then some index else none
  | _ => none

/-- The clear result profile of one invocation; only `target` is a command
position. Quotation and admission share this single constructor. -/
def profileAt (policy : Policy) (artifact : ObjectiveBendSourceArtifact.Artifact)
    (subject : TypedAuthorization.SubjectId) (nonce : Nat) (target : Nat) : ObjectiveBendResultAdapter.Profile :=
  ⟨ObjectiveBendSourceArtifact.identity artifact,declarationId artifact.declaration,
    artifact.declaration,"result",subject,clearKeyEpoch,policy.clearAudience,nonce,target⟩

def resultProfile (policy : Policy) (artifact : ObjectiveBendSourceArtifact.Artifact)
    (command : Command) : Option ObjectiveBendResultAdapter.Profile := do
  let [target] := returnTargets command | none
  pure (profileAt policy artifact command.subject command.nonce target)

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



/-- Command-free admission environment: one current image, subject and nonce,
and the actual fee-first compute preparation. Quotation and final admission
build the same value from the same image. -/
structure Environment (deployment : Deployment) (durable : Durable) where
  context : ResourceObservationAdmission.Context deployment durable
  federation : FederationId
  genesisHeight : Nat
  subject : TypedAuthorization.SubjectId
  nonce : Nat
  compute : Option (RunComputeBudgetDomain.Prepared deployment durable.snapshot subject)

/-- The environment of a final command's admission. -/
def environment {F : Type} [Field F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command) (genesisHeight : Nat) :
    Environment deployment durable :=
  ⟨readContext prepared,ambient.federation,genesisHeight,command.subject,command.nonce,prepared.compute⟩

/-- A current authorized read by the environment's subject. Its
`ResourceObservationAdmission.Checked` token is constructed only after the
signature verifies and the read is authorized on this context. -/
abbrev Read {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    (environment : Environment deployment durable) (profile : CanonicalRuntimeProfile.Profile F) :=
  ObjectiveBendNativeInput.AdmittedRead environment.context profile environment.subject

/-- A read is exactly the claimed selector, for this nonce and federation. -/
def refMatches {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    (read : Read environment profile) (ref : ObjectiveInvocationClaim.InputRef) : Bool :=
  decide (read.kind = ref.kind ∧ read.request.target.value = ref.resource ∧
    read.capability = ref.capability ∧ read.value.root = ref.root ∧
    read.request.nonce = environment.nonce ∧ read.request.federation = environment.federation)

/-- Everything a matching read binds: the authenticated Request's subject, nonce,
target, verb and federation, and the read's kind, capability and observed root,
each equal to the environment or the signed ref. No digest-only binding. -/
def Bound {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    (read : Read environment profile) (ref : ObjectiveInvocationClaim.InputRef) : Prop :=
  read.request.subject = environment.subject ∧ read.request.nonce = environment.nonce ∧
  read.request.target.value = ref.resource ∧ read.request.verb = observeVerb read.kind ∧
  read.kind = ref.kind ∧ read.capability = ref.capability ∧ read.value.root = ref.root ∧
  read.request.federation = environment.federation

theorem refMatches_sound {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {read : Read environment profile} {ref : ObjectiveInvocationClaim.InputRef}
    (matched : refMatches read ref = true) : Bound read ref := by
  simp only [refMatches, decide_eq_true_eq] at matched
  exact ⟨read.subjectExact, matched.2.2.2.2.1, matched.2.1, read.prepared.observeExact,
    matched.1, matched.2.2.1, matched.2.2.2.1, matched.2.2.2.2.2⟩

/-- Source and ordered inputs, each an unforgeable current read matching its
signed ref. The constructor is public: its fields are the evidence. -/
structure Authenticated {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    (environment : Environment deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (claim : ObjectiveInvocationClaim.Claim) where
  source : Read environment profile
  sourceExact : refMatches source claim.source = true
  inputs : List (Read environment profile)
  inputsLength : inputs.length = claim.inputRefs.length
  inputsExact : (inputs.zip claim.inputRefs).all (fun pair => refMatches pair.1 pair.2) = true

theorem forall₂_of_zip_all {α β : Type} (p : α → β → Bool) :
    ∀ (l : List α) (m : List β), l.length = m.length →
      (l.zip m).all (fun pair => p pair.1 pair.2) = true → List.Forall₂ (fun a b => p a b = true) l m
  | [],[],_,_ => .nil
  | a::l,b::m,length,all => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at all
    exact .cons all.1 (forall₂_of_zip_all p l m (by simpa using length) all.2)
  | [],_::_,length,_ => by simp at length
  | _::_,[],length,_ => by simp at length

/-- The claimed source and every ordered claimed input are bound fieldwise. -/
theorem Authenticated.sound {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {claim : ObjectiveInvocationClaim.Claim} (authenticated : Authenticated environment profile claim) :
    Bound authenticated.source claim.source ∧
      List.Forall₂ (fun read ref => Bound read ref) authenticated.inputs claim.inputRefs :=
  ⟨refMatches_sound authenticated.sourceExact,
    (forall₂_of_zip_all _ _ _ authenticated.inputsLength authenticated.inputsExact).imp
      (fun _ _ matched => refMatches_sound matched)⟩

def authenticate {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    (claim : ObjectiveInvocationClaim.Claim) (source : Read environment profile)
    (inputs : List (Read environment profile)) : Option (Authenticated environment profile claim) :=
  if sourceExact : refMatches source claim.source = true then
    if inputsLength : inputs.length = claim.inputRefs.length then
      if inputsExact : (inputs.zip claim.inputRefs).all (fun pair => refMatches pair.1 pair.2) = true then
        some ⟨source,sourceExact,inputs,inputsLength,inputsExact⟩
      else none
    else none
  else none

/-- Supplier of the claim's signed source/input queries as current reads. The
real one (`ObjectiveBendAuthenticatedInputs.oracle`) authenticates each claimed
envelope through NativeObservationController; it cannot construct a `Read`
without a verified, authorized signature on this context. -/
structure ReadOracle where
  authenticate : {F : Type} → [Field F] → [DecidableEq F] → {deployment : Deployment} →
    {durable : Durable} → CredentialSignatureIO.NativeConfig →
    (environment : Environment deployment durable) → (profile : CanonicalRuntimeProfile.Profile F) →
    (claim : ObjectiveInvocationClaim.Claim) → IO (Except Reject (Authenticated environment profile claim))

/-- A caller that did not install the signed-query oracle. Its refusal is
`noReadOracle`, distinct from every policy or authority refusal. -/
def ReadOracle.refuse : ReadOracle := ⟨fun _ _ _ _ => pure (.error .noReadOracle)⟩

theorem ReadOracle.refuse_refuses {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {durable : Durable} (native : CredentialSignatureIO.NativeConfig)
    (environment : Environment deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (claim : ObjectiveInvocationClaim.Claim) :
    ReadOracle.refuse.authenticate native environment profile claim = pure (.error .noReadOracle) := rfl

/-- CAS dependencies of one consumed read: the read resource at its current
physical root, the read's clock, and every governing law/kind cell. -/
def readGuardsOf {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    (read : Read environment profile) : Option (List ReadGuard) := do
  let laws ← ResourceObservationAdmission.lawReadGuards read.prepared
  pure ((⟨⟨read.request.target.value⟩,durable.snapshot.model.roots ⟨read.request.target.value⟩⟩ : ReadGuard) ::
    read.prepared.clock.readGuard :: laws.map (fun (cell,root) => (⟨⟨cell⟩,root⟩ : ReadGuard)))

/-- Full-scope source selection from the signed source query. -/
structure SourceSelection {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    (claim : ObjectiveInvocationClaim.Claim) (read : Read environment profile) (policy : Policy) where
  private mk ::
  fullScope : ResourceObservationAdmission.readerFields environment.context claim.source.kind claim.source.capability = none
  payload : CellState.Materialized (CanonicalCellRegistry.materializer .content)
  observedExact : read.prepared.observed.before = ⟨.content,payload⟩
  loaded : ObjectiveBendArtifactSource.Loaded payload.logical ⟨claim.sourceAtom⟩ policy.sourceBytes
  package : ObjectiveBendPublishedPackage.Loaded payload.logical ⟨loaded.artifact.package⟩ policy.sourceBytes
  declarationExact : ObjectiveSourcePackage.selectedDeclaration package.package = some loaded.artifact.declaration
  parserExact : package.package.parserSha256 = policy.tooling.parserSha256
  frontendExact : package.package.frontendSha256 = policy.tooling.frontendSha256
  inputCodecExact : loaded.artifact.inputCodec = ObjectiveBendNativeInput.codecId
  claimInputExact : claim.inputCodec = loaded.artifact.inputCodec
  outputCodecExact : claim.outputCodec = loaded.artifact.outputCodec
  outputRegistered : loaded.artifact.outputCodec ∈ policy.outputs

private def selectSource {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    (claim : ObjectiveInvocationClaim.Claim) (read : Read environment profile)
    (policy : Policy) : Option (SourceSelection claim read policy) := do
  if full : ResourceObservationAdmission.readerFields environment.context claim.source.kind claim.source.capability = none then
    match observed : read.prepared.observed.before with
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
                    some ⟨full,payload,observed,loaded,package,declaration,parser,frontend,input,claimInput,output,registered⟩
                  else none
                else none
              else none
            else none
          else none
        else none
      else none
    | _ => none
  else none

private def checkedFunding {deployment : Deployment} {durable : Durable} {subject : TypedAuthorization.SubjectId}
    (compute : Option (RunComputeBudgetDomain.Prepared deployment durable.snapshot subject))
    (claim : ObjectiveInvocationClaim.Claim) :
    Option {funded : RunComputeBudgetDomain.Prepared deployment durable.snapshot subject //
      compute = some funded ∧ funded.steps = claim.capacity.proofWork ∧ funded.credits = claim.capacity.feeDebit} :=
  match selected : compute with
  | none => none
  | some funded =>
    if steps : funded.steps = claim.capacity.proofWork then
      if credits : funded.credits = claim.capacity.feeDebit then some ⟨funded,rfl,steps,credits⟩ else none
    else none

/-- The applied input commitment a quotation must sign: computed from the same
authorized reads, so the producer never chooses `expectedInput`. -/
def inputOf {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {claim : ObjectiveInvocationClaim.Claim}
    (authenticated : Authenticated environment profile claim) : ObjectiveBendNativeInput.Input :=
  ⟨environment.subject,environment.nonce,claim.arguments,
    authenticated.inputs.map ObjectiveBendNativeInput.AdmittedRead.value⟩

/-- Command-free admitted source and authenticated applied input, before any
demand. Quotation and final admission build this SAME token from the same
environment fields; it cannot authorize an effect or certify a checkpoint. -/
structure Core {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    (environment : Environment deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (claim : ObjectiveInvocationClaim.Claim) where
  private mk ::
  semantics : NativeInvocationProfile.registered profile.receiverParameters .objectiveMethod = true
  policy : Policy
  policyExact : NativeInvocationProfile.binding profile.receiverParameters .objectiveMethod = some (encodePolicy policy)
  policyEdition : policy.edition = semanticsId
  capacities : capacityWithin claim.capacity policy.maximum = true
  funding : ∃ funded, environment.compute = some funded ∧
    funded.steps = claim.capacity.proofWork ∧ funded.credits = claim.capacity.feeDebit
  authenticated : Authenticated environment profile claim
  /-- CAS dependencies of every consumed read (`readGuardsOf`). -/
  guardLists : List (List ReadGuard)
  guardsExact : (authenticated.source :: authenticated.inputs).mapM readGuardsOf = some guardLists
  source : SourceSelection claim authenticated.source policy
  input : ObjectiveBendNativeInput.Input
  inputExact : input = inputOf authenticated
  inputCommitted : ObjectiveInvocationClaim.inputCommitment (ObjectiveBendNativeInput.encode input) = claim.expectedInput
  inputTerm : ObjectiveBendOpenRecursion.Term
  inputTermExact : ObjectiveBendNativeInput.sourceTerm input claim.capacity.inputBytes claim.capacity.scalarBits = .ok inputTerm
  typed : Checked (ObjectiveBendNativeInput.instantiate source.loaded.checked.packet.source inputTerm) []

def Core.guards {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {claim : ObjectiveInvocationClaim.Claim} (core : Core environment profile claim) : List ReadGuard :=
  core.guardLists.flatten

def Core.applied {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {claim : ObjectiveInvocationClaim.Claim} (core : Core environment profile claim) : AnnotatedTerm :=
  ObjectiveBendNativeInput.instantiate core.source.loaded.checked.packet.source core.inputTerm

def Core.contextBytes {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    {environment : Environment deployment durable} {profile : CanonicalRuntimeProfile.Profile F}
    {claim : ObjectiveInvocationClaim.Claim} (core : Core environment profile claim) : List UInt8 :=
  "DREGG/OBJECTIVE-BEND/ADMITTED-INPUT-CONTEXT".toUTF8.toList ++ [2] ++
  ObjectiveInvocationClaim.encode claim ++ ObjectiveBendNativeInput.encode core.input ++
  digestStream.encode (ObjectiveBendSourceArtifact.identity core.source.loaded.artifact)

/-- Shared by quotation and admission. Signature/policy work happens inside
`authorize`, after cheap policy, capacity and funding refusals. -/
def prepareCore {F : Type} [Field F] [DecidableEq F] {deployment : Deployment} {durable : Durable}
    (native : CredentialSignatureIO.NativeConfig) (oracle : ReadOracle)
    (environment : Environment deployment durable) (profile : CanonicalRuntimeProfile.Profile F)
    (claim : ObjectiveInvocationClaim.Claim) : IO (Except Reject (Core environment profile claim)) := do
  if semantics : NativeInvocationProfile.registered profile.receiverParameters .objectiveMethod = true then
    let some policyBytes := NativeInvocationProfile.binding profile.receiverParameters .objectiveMethod
      | return .error .bendExecution
    let some policy := decodePolicy policyBytes | return .error .bendExecution
    if policyExact : NativeInvocationProfile.binding profile.receiverParameters .objectiveMethod = some (encodePolicy policy) then
      if policyEdition : policy.edition = semanticsId then
        if capacities : capacityWithin claim.capacity policy.maximum = true then
          if evaluatorId ∈ profile.disabledEvaluators then return .error .bendExecution
          if !ObjectiveSourcePackage.shaPin policy.tooling.elaboratorSha256 then return .error .bendExecution
          let some funding := checkedFunding environment.compute claim | return .error .computeFunding
          match ← oracle.authenticate native environment profile claim with
          | .error reason => return .error reason
          | .ok authenticated =>
           match guardsExact : (authenticated.source :: authenticated.inputs).mapM readGuardsOf with
           | none => return .error .observationRejected
           | some guardLists =>
            let some source := selectSource claim authenticated.source policy | return .error .bendExecution
            let input := inputOf authenticated
            if inputCommitted : ObjectiveInvocationClaim.inputCommitment (ObjectiveBendNativeInput.encode input) = claim.expectedInput then
              match inputTermExact : ObjectiveBendNativeInput.sourceTerm input claim.capacity.inputBytes claim.capacity.scalarBits with
              | .error _ => return .error .bendExecution
              | .ok inputTerm =>
                let some typed := check (ObjectiveBendNativeInput.instantiate source.loaded.checked.packet.source inputTerm)
                  [] claim.capacity.typeFuel | return .error .bendExecution
                return .ok ⟨semantics,policy,policyExact,policyEdition,capacities,⟨funding.1,funding.2⟩,
                  authenticated,guardLists,guardsExact,source,input,rfl,inputCommitted,inputTerm,inputTermExact,typed⟩
            else return .error .bendExecution
        else return .error .bendExecution
      else return .error .bendExecution
    else return .error .bendExecution
  else return .error .bendExecution

/-- This evidence is indexed by the SAME prepared native command/image and
final full ingress/write/guard lists. It contains no signature/law permission. -/
structure Admitted {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (ingress : List UInt8) (writes : List DataWrite) (guards : List ReadGuard) where
  private mk ::
  claim : ObjectiveInvocationClaim.Claim
  selected : command.objectiveClaim = .ok (some claim)
  genesisHeight : Nat
  heightExact : genesisHeight + durable.image.accepted.length = ambient.height
  core : Core (environment prepared genesisHeight) profile claim
  /-- Every consumed read's CAS dependency is a final guard or the exact
  pre-state of a final write. -/
  inputsCurrent : ∀ guard ∈ core.guards, guard ∈ guards ∨
    ∃ write ∈ writes, guard.cellId = write.cellId ∧ guard.expectedRoot = write.expectedPre
  result : ObjectiveBendResultAdapter.Profile
  resultExact : result.sourceArtifact = ObjectiveBendSourceArtifact.identity core.source.loaded.artifact ∧
    result.selectedDeclaration = declarationId core.source.loaded.artifact.declaration ∧
    result.sourceEntry = core.source.loaded.artifact.declaration ∧ result.recipient = command.subject ∧
    result.audience = core.policy.clearAudience ∧ result.generation = command.nonce
  output : Output deployment prepared.directory result command core.applied claim.capacity
  codecExact : (claim.outputCodec = ObjectiveBendPlanAdapter.codecId ∧ ∃ p, output = .scalar p) ∨
    (claim.outputCodec = ObjectiveBendResultAdapter.codecId ∧ ∃ p, output = .result p) ∨
    (claim.outputCodec = combinedCodec ∧ ∃ p, output = .combined p) ∨
    (claim.outputCodec = ObjectiveBendGenericResult.codecId ∧ ∃ p, output = .generic p)
  readsCurrent : ∀ guard ∈ output.plan.reads, guard ∈ guards ∨
    ∃ write ∈ writes, guard.cellId = write.cellId ∧ guard.expectedRoot = write.expectedPre
  fits : usage output (ObjectiveBendNativeInput.encode core.input)
    (core.source.loaded.record.payload ++ core.source.package.record.payload) ingress writes guards ≤ charge claim.capacity

private def selectResult (policy : Policy) (artifact : ObjectiveBendSourceArtifact.Artifact)
    (command : Command) (codec : Digest) : Option ObjectiveBendResultAdapter.Profile :=
  if codec = ObjectiveBendPlanAdapter.codecId then
    some (profileAt policy artifact command.subject command.nonce 0)
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


/-- The command's signed claim and its command-free core on the admission image.
The query height is the admission height: `genesisHeight` is recovered from the
ambient height and refused when the accepted prefix exceeds it. -/
structure Selection {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command) where
  private mk ::
  claim : ObjectiveInvocationClaim.Claim
  selected : command.objectiveClaim = .ok (some claim)
  genesisHeight : Nat
  heightExact : genesisHeight + durable.image.accepted.length = ambient.height
  core : Core (environment prepared genesisHeight) profile claim

/-- Called ONLY after current original native authority checks. Signature,
policy and source typing work; no source demand runs here. -/
def select {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    (native : CredentialSignatureIO.NativeConfig) (oracle : ReadOracle)
    (prepared : PreparedInvocation deployment profile ambient durable command) :
    IO (Except Reject (Selection prepared)) := do
  match selected : command.objectiveClaim with
  | .error reason => return .error reason
  | .ok none => return .error .bendExecution
  | .ok (some claim) =>
    if bounded : durable.image.accepted.length ≤ ambient.height then
      let genesisHeight := ambient.height - durable.image.accepted.length
      let heightExact : genesisHeight + durable.image.accepted.length = ambient.height := Nat.sub_add_cancel bounded
      match ← prepareCore native oracle (environment prepared genesisHeight) profile claim with
      | .error reason => return .error reason
      | .ok core => return .ok ⟨claim,selected,genesisHeight,heightExact,core⟩
    else return .error .bendExecution

/-- Source demand and exact output binding against the FINAL full ingress,
writes and guards. Families cannot fall through to ordinary admission;
malformed source or output refuses. -/
def admit {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable} {command : Command}
    {prepared : PreparedInvocation deployment profile ambient durable command}
    (selection : Selection prepared) (ingress : List UInt8)
    (writes : List DataWrite) (guards : List ReadGuard) : Except Reject (Admitted prepared ingress writes guards) := do
  let core := selection.core
  let claim := selection.claim
  if inputsCurrent : ∀ guard ∈ core.guards, guard ∈ guards ∨
      ∃ write ∈ writes, guard.cellId = write.cellId ∧ guard.expectedRoot = write.expectedPre then
    let some result := selectResult core.policy core.source.loaded.artifact command claim.outputCodec
      | throw .bendExecution
    if resultExact : result.sourceArtifact = ObjectiveBendSourceArtifact.identity core.source.loaded.artifact ∧
        result.selectedDeclaration = declarationId core.source.loaded.artifact.declaration ∧
        result.sourceEntry = core.source.loaded.artifact.declaration ∧ result.recipient = command.subject ∧
        result.audience = core.policy.clearAudience ∧ result.generation = command.nonce then
      let output ← checkOutput deployment prepared.directory result command core.applied claim core.typed
      if readsCurrent : ∀ guard ∈ output.1.plan.reads, guard ∈ guards ∨
          ∃ write ∈ writes, guard.cellId = write.cellId ∧ guard.expectedRoot = write.expectedPre then
        if fits : usage output.1 (ObjectiveBendNativeInput.encode core.input)
            (core.source.loaded.record.payload ++ core.source.package.record.payload) ingress writes guards ≤ charge claim.capacity then
          pure ⟨claim,selection.selected,selection.genesisHeight,selection.heightExact,core,inputsCurrent,
            result,resultExact,output.1,output.2,readsCurrent,fits⟩
        else throw .bendExecution
      else throw .bendExecution
    else throw .bendExecution
  else throw .staleTarget

#assert_axioms Output.exact
#assert_axioms refMatches_sound
#assert_axioms Authenticated.sound
#assert_axioms ReadOracle.refuse_refuses
end Minidregg.Kernel.ObjectiveBendNativeAdmission
