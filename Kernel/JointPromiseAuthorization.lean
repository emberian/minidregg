/- Purpose-specific reservation permission over the existing native invocation.
The original selected effect is admitted normally. EVERY target must additionally
admit the exact install promise under independently scoped reserve authority.
No ordinary grant, old AcceptedInvocation, or client Boolean mints this token. -/
import Kernel.JointInvocationCandidate
namespace Minidregg.Kernel.JointPromiseAuthorization
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.Store
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.MultiCellHyperedge
set_option autoImplicit false
set_option maxHeartbeats 800000

/-- Version one means: the exact admitted projection may be installed after
commit, even if its ordinary grant later expires. Before YES no such promise
exists. Policy/authority/clock/audience dependencies remain locked throughout.
This is a distinct operation, not a reinterpretation of ordinary invocation. -/
structure Declaration where
  candidateBytes : List UInt8
  selectedSignedBytes : List UInt8
  sourceImageBytes : List UInt8
  epoch : Nat
  generation : Nat
  nonce : Nat
  capabilities : List CapabilityId
  maintenance : Charge
  repairEnvelopes : List (List UInt8)

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap
    (StreamCodec.product (bytesStream) (StreamCodec.product (bytesStream) (StreamCodec.product (bytesStream) (StreamCodec.product (StreamCodec.nat) (StreamCodec.product (StreamCodec.nat) (StreamCodec.product (StreamCodec.nat) (StreamCodec.product (StreamCodec.list CredentialAuthorityEntryCodec.capabilityIdStream) (StreamCodec.product (DurableReceiverCodec.chargeStream) (StreamCodec.list bytesStream)))))))))
    (fun d => (d.candidateBytes,d.selectedSignedBytes,d.sourceImageBytes,d.epoch,
      d.generation,d.nonce,d.capabilities,d.maintenance,d.repairEnvelopes))
    (fun (c,s,i,e,g,n,cs,m,r) => ⟨c,s,i,e,g,n,cs,m,r⟩) (by intro d; cases d; rfl)
def statement (domain semantics : Digest) (d : Declaration) : List UInt8 :=
  "DREGG/JOINT/INSTALL-PROMISE/v1".toUTF8.toList ++
    (StreamCodec.product digestStream (StreamCodec.product digestStream declarationStream)).encode
      (domain,semantics,d)
def commitment (domain semantics : Digest) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG/JOINT/INSTALL-PROMISE/REQUEST/v1".toUTF8.toList
    (statement domain semantics d)).digest

def wanted (domain semantics : Digest) (d : Declaration) (ordinary : PackedEffectRequest) :
    PackedEffectRequest :=
  ⟨ordinary.1,
    { ordinary.2 with
      verb := reserveVerb ordinary.1
      argsDigest := commitment domain semantics d
      effectsDigest := commitment domain semantics d
      nonce := d.nonce }⟩

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {ground : Ground deployment} {command : Command}

def rawLeg (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (source : Source command) (incidence : Incidence command) :
    CandidateLegData (DeclaredResourceController.layout prepared) incidence :=
  let original := DeclaredResourceController.rawLeg prepared source incidence
  { original with request := wanted deployment.domain profile.semantics d original.request }

def bindFamily (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (source : Source command) (portals : Incidence command → Portal)
    (incidence : Incidence command) : SemanticLegBinding (rawLeg prepared d source incidence) :=
  let original := DeclaredResourceController.bindFamily prepared source portals incidence
  { Nullifier := original.Nullifier
    family := { original.family with
      request := fun declaration => wanted deployment.domain profile.semantics d
        (original.family.request declaration)
      effectDigest := fun _ => commitment deployment.domain profile.semantics d }
    declaration := original.declaration
    outcome := original.outcome
    preExact := original.preExact
    requestExact := congrArg (wanted deployment.domain profile.semantics d) original.requestExact
    effectsExact := rfl
    patchExact := original.patchExact
    postconditionExact := original.postconditionExact }

def plan (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) : PreparationPlan (DeclaredResourceController.layout prepared) (Source command) where
  leg := rawLeg prepared d
  jointDigest := fun _ => commitment deployment.domain profile.semantics d
  legEffectsDigest := fun _ _ => commitment deployment.domain profile.semantics d
  bindFamily := bindFamily prepared d

def tuple (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (original : PreparedTuple (DeclaredResourceController.plan prepared)) :
    PreparedTuple (plan prepared d) where
  source := original.source
  primary := original.primary
  validated := original.validated
  postconditions := original.postconditions
  cellIdsDistinct := original.cellIdsDistinct
  requestEffects := fun _ => rfl

/-- All original participant projections remain, including negative clauses,
foreign-law dependencies, run/compute inputs and source clock. Request slots
are replaced by the purpose-specific request, not appended behind old slots. -/
def commonSlots (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (source : Source command) (incidence : Incidence command) : List (String × Int) :=
  let actual := (rawLeg prepared d source incidence).request
  [("target/storageKind", Int.ofNat (storageKind prepared incidence)),
    ("joint/install-promise/version",1), ("joint/install-promise/epoch",Int.ofNat d.epoch),
    ("joint/install-promise/generation",Int.ofNat d.generation)] ++
    Kernel.ClockCell.slots prepared.clock.clock ++
    CanonicalRuntimeProfile.requestSlots actual.2 ++
    bytesSlots "command/bytes" 0 (commandCodec.encode source.val) ++
    bytesSlots "joint/install-promise/statement" 0 (statement deployment.domain profile.semantics d) ++
    runSlots prepared.run ++ computeSlots prepared

def step (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (original : PreparedTuple (DeclaredResourceController.plan prepared))
    (incidence : Incidence command) : PolicyStepContext :=
  PolicyStepContext.ofPreparedTuple
    (fun source logical => projectWithCommon prepared incidence
      (commonSlots prepared d source incidence) logical)
    profile.semantics { tuple prepared d original with primary := incidence }

def config (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (original : PreparedTuple (DeclaredResourceController.plan prepared))
    (incidence : Incidence command) : ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile ground.authority
    ground.directory
    (sourceCapabilityPortal ground.authority (commitment deployment.domain profile.semantics d).value)
    (step prepared d original incidence) (incidenceTarget command incidence).target
    ((kindDependencies prepared incidence).map (·.additional) |>.getD [])

/-- Named portal boundary keeps dependent admission evidence from repeatedly
normalizing the full physical law configuration. It is exactly that current
source configuration, without a new authority constructor. -/
def portal (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (original : PreparedTuple (DeclaredResourceController.plan prepared))
    (incidence : Incidence command) : Portal :=
  (config prepared d original incidence).portal

def request (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (original : PreparedTuple (DeclaredResourceController.plan prepared))
    (incidence : Incidence command) := (tuple prepared d original).request incidence |>.2

/-- The authority read leg uses the first targets reserve capability, just as
its ordinary invocation uses that targets capability. Every target has its own
purpose-specific capability, and the complete list is signed in the statement. -/
def capability (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (incidence : Incidence command) : CapabilityId :=
  d.capabilities[(incidence.getD (firstIndex prepared)).val]?.getD ⟨0⟩

def authorize (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (original : PreparedTuple (DeclaredResourceController.plan prepared))
    (incidence : Incidence command)
    (signature : CredentialSignatureAdmission.CheckedSignature ground.authority) :
    Except Reject (Authorized (portal prepared d original incidence)
      ground.authority.authState (request prepared d original incidence)) := do
  let wanted := request prepared d original incidence
  let lawConfig := config prepared d original incidence
  let _ ← requireSome .policyUnavailable (kindDependencies prepared incidence)
  let evidence ← requireSome .capabilityRejected
    (lawConfig.capabilityEvidenceChecked wanted (capability prepared d incidence)
      () signature () (fun _ => ())).toOption
  let law ← requireSome .policyUnavailable lawConfig.resolve?
  let context := step prepared d original incidence
  if inputsInRange profile.compilerProfile.compiler law.predicate context.oldState context.newState != true then
    throw .policyInputRange
  if !decide (castInjOn F (intsOf law.predicate context.oldState context.newState)) then
    throw .policyCastAlias
  requireSome .policyRejected (law.admit wanted evidence law.witness
    (.policy wanted.policyId wanted.policyRevision)
    (source_request_epoch_current prepared original incidence)
    (source_request_revision_current prepared original incidence))

structure Signed where
  declaration : Declaration
  targetEnvelopes : List (List UInt8)
  authorityEnvelope : List UInt8

def Signed.envelope (signed : Signed) : Incidence command → List UInt8
  | none => signed.authorityEnvelope
  | some i => signed.targetEnvelopes[i.val]?.getD []

attribute [irreducible] portal

structure CheckedLeg (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (original : PreparedTuple (DeclaredResourceController.plan prepared))
    (incidence : Incidence command) (envelope : List UInt8) where
  receipt : CredentialSignatureAdmission.CheckedSignature ground.authority
  envelopeExact : receipt.envelopeBytes = envelope
  authority : Authorized (portal prepared d original incidence)
    ground.authority.authState (request prepared d original incidence)
  admitted : authorize prepared d original incidence receipt = .ok authority
  fields : fieldsCheck authority.evidence.capabilityValue (legFootprint prepared incidence) = .ok ()

def verifyLeg (native : CredentialSignatureIO.NativeConfig)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (d : Declaration) (original : PreparedTuple (DeclaredResourceController.plan prepared))
    (incidence : Incidence command) (envelope : List UInt8) :
    IO (Except Reject (CheckedLeg prepared d original incidence envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native ground.authority
      (commitment deployment.domain profile.semantics d).value
      (request prepared d original incidence) envelope with
  | .error reason => return .error (.legSignature reason)
  | .ok signature =>
      if wire : signature.envelopeBytes = envelope then
        match admitted : authorize prepared d original incidence signature with
        | .error reason => return .error reason
        | .ok authority =>
            match fields : fieldsCheck authority.evidence.capabilityValue (legFootprint prepared incidence) with
            | .error reason => return .error reason
            | .ok () => return .ok ⟨signature,wire,authority,admitted,fields⟩
      else return .error (.legSignature .sourceBinding)

/-- Private token minted only by CURRENT ordinary admission plus CURRENT
purpose-specific signatures, capabilities, full composed laws and field bounds.
It is not reconstructible from an untrusted certificate or journal event. -/
structure Accepted (prepared : PreparedInvocation deployment profile ambient ground command)
    (selected : SignedCommand) (signed : Signed) where
  private mk ::
  ordinary : AcceptedInvocation prepared selected
  shape : PhysicalShape prepared
  selectedExact : signed.declaration.selectedSignedBytes =
    signedBytes deployment.domain profile.semantics selected
  sourceExact : ground.sourceImage.map DurableReceiverCodec.imageStream.encode =
    some signed.declaration.sourceImageBytes
  targetCount : signed.declaration.capabilities.length = command.targets.length
  envelopeCount : signed.targetEnvelopes.length = command.targets.length
  /-- An observe-only read target carries no promise envelope: no promise leg
  runs for it; its only authorization is its `ReadLeg`. -/
  readEnvelopes : ∀ i : TargetIndex command, command.targets[i].observeOnly = true →
    signed.envelope (some i) = []
  checked : (incidence : Incidence command) → incidenceObserveOnly command incidence = false →
    CheckedLeg prepared signed.declaration ordinary.tuple incidence (signed.envelope incidence)

def admit (native : CredentialSignatureIO.NativeConfig)
    (prepared : PreparedInvocation deployment profile ambient ground command)
    (shape : PhysicalShape prepared) (selected : SignedCommand) (signed : Signed) :
    IO (Except Reject (Accepted prepared selected signed)) := do
  if selectedExact : signed.declaration.selectedSignedBytes = signedBytes deployment.domain profile.semantics selected then
    if sourceExact : ground.sourceImage.map DurableReceiverCodec.imageStream.encode =
    some signed.declaration.sourceImageBytes then
      if targetCount : signed.declaration.capabilities.length = command.targets.length then
        if envelopeCount : signed.targetEnvelopes.length = command.targets.length then
         if readEnvelopes : ∀ i : TargetIndex command, command.targets[i].observeOnly = true →
             signed.envelope (some i) = [] then
          match ← DeclaredResourceController.admit native prepared selected with
          | .error reason => return .error reason
          | .ok ordinary =>
              match ← collectLegs (fun incidence _ =>
                  verifyLeg native prepared signed.declaration ordinary.tuple incidence (signed.envelope incidence)) with
              | .error reason => return .error reason
              | .ok checked => return .ok ⟨ordinary,shape,selectedExact,sourceExact,targetCount,envelopeCount,
                  readEnvelopes,checked⟩
         else return .error .readTargetEnvelope
        else return .error .wrongEnvelopeCount
      else return .error .wrongEnvelopeCount
    else return .error .physicalPreparation
  else return .error .malformedCommand

end Minidregg.Kernel.JointPromiseAuthorization
namespace Minidregg.Kernel.JointPromiseAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
def signedStream : StreamCodec Signed :=
  StreamCodec.xmap (StreamCodec.product declarationStream
    (StreamCodec.product (StreamCodec.list bytesStream) bytesStream))
    (fun s => (s.declaration,s.targetEnvelopes,s.authorityEnvelope))
    (fun (d,t,a) => ⟨d,t,a⟩) (by intro s; cases s; rfl)
end Minidregg.Kernel.JointPromiseAuthorization
