/- Current management policy admission for a verified failed START custody report. Only the dedicated checked reconciliation slot changes the policy projection; current per-incidence signature, grant, revision and epoch admission remain decisive. -/
import Kernel.ApplicationFailedStartRecoveryReport
import Kernel.DeclaredResourceController

namespace Minidregg.Kernel.ApplicationFailedStartRecoveryPolicy

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomain
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.ApplicationFailedStartRecoveryReport

set_option autoImplicit false

open Minidregg.Compiler.ServedBasis (Ground)
set_option maxHeartbeats 800000

/-- The checked completion slot is visible to every incidence whose policy
view is the application's transition. That is the app mutation incidence and
the authority incidence: DRC asks the authority envelope for the policy of
`command.first` and projects the first target's local slots, and a completion
command always puts the app first (`Source.command_has_app_first`). Withholding
the slot there made the app law judge the authority leg's own completion edge
(8→2, 9→4, 10→2) without its gate, so every checked completion was refused
with `policyRejected` while BEGIN and claim (no gate) were admitted. The
package incidence keeps its ordinary DRC projection; the full joint command is
still visible to it through the joint slots. -/
def extraSlots {command : DeclaredResourceController.Command}
    (app : Nat) (incidence : DeclaredResourceController.Incidence command) :
    List (String × Int) :=
  match incidence with
  | none =>
      if command.first.target == app then
        [(ApplicationGrain.reconciliationSlot, 1)]
      else []
  | some index =>
      if command.targets[index].target == app then
        [(ApplicationGrain.reconciliationSlot, 1)]
      else []

theorem authority_completion_slot_iff_app_first
    {command : DeclaredResourceController.Command} (app : Nat) :
    extraSlots (command := command) app none =
      if command.first.target == app then [(ApplicationGrain.reconciliationSlot, 1)] else [] := rfl

theorem non_app_target_has_no_completion_slot
    {command : DeclaredResourceController.Command} (app : Nat)
    (index : DeclaredResourceController.TargetIndex command)
    (other : command.targets[index].target ≠ app) :
    extraSlots (command := command) app (some index) = [] := by
  simp only [extraSlots]
  exact if_neg (by simpa using other)

def step {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation
      deployment profile ambient ground command)
    (tuple : PreparedTuple
      (DeclaredResourceController.plan prepared))
    (incidence : DeclaredResourceController.Incidence command)
    {domain semantics : Digest} {publicKey : List UInt8}
    {begin : ApplicationLifecycleBeginV3Ingress.Ingress}
    (_checked : Checked domain semantics publicKey begin) : PolicyStepContext :=
  let common := DeclaredResourceController.projectCommonSlots prepared incidence tuple.source ++
    extraSlots begin.base.source.app incidence
  PolicyStepContext.ofPreparedTupleExact
    (fun _ logical => DeclaredResourceController.projectWithCommon
      prepared incidence common logical) profile.semantics
    { tuple with primary := incidence }
    (DeclaredResourceController.policyPreCell prepared)
    (DeclaredResourceController.policyPostState prepared)
    (DeclaredResourceController.policyPreCell_exact prepared tuple)
    (DeclaredResourceController.policyPostState_exact prepared tuple)

def policyConfig {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation
      deployment profile ambient ground command)
    (tuple : PreparedTuple (DeclaredResourceController.plan prepared))
    (incidence : DeclaredResourceController.Incidence command)
    {domain semantics : Digest} {publicKey : List UInt8}
    {begin : ApplicationLifecycleBeginV3Ingress.Ingress}
    (checked : Checked domain semantics publicKey begin) : ComposedPolicyAdmission.Config F :=
  DeclaredResourceController.policyConfigFromStep prepared incidence
    (step prepared tuple incidence checked)


def portals {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation
      deployment profile ambient ground command)
    (tuple : PreparedTuple (DeclaredResourceController.plan prepared))
    {domain semantics : Digest} {publicKey : List UInt8}
    {begin : ApplicationLifecycleBeginV3Ingress.Ingress}
    (checked : Checked domain semantics publicKey begin) :
    DeclaredResourceController.Incidence command → Portal :=
  fun incidence => (policyConfig prepared tuple incidence checked).portal

attribute [irreducible] portals

def authorizeLeg {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation
      deployment profile ambient ground command)
    (tuple : PreparedTuple (DeclaredResourceController.plan prepared))
    (incidence : DeclaredResourceController.Incidence command)
    {domain semantics : Digest} {publicKey : List UInt8}
    {begin : ApplicationLifecycleBeginV3Ingress.Ingress}
    (checked : Checked domain semantics publicKey begin)
    (signature : CredentialSignatureAdmission.CheckedSignature ground.authority) :
    Except DeclaredResourceController.Reject
      (Authorized (portals prepared tuple checked incidence)
        ground.authority.authState (tuple.request incidence).2) := do
  let wanted := (tuple.request incidence).2
  let context := step prepared tuple incidence checked
  let config := policyConfig prepared tuple incidence checked
  let capability := (DeclaredResourceController.incidenceTarget command incidence).capability
  let _ ← DeclaredResourceController.requireSome .policyUnavailable
    (DeclaredResourceController.kindDependencies prepared incidence)
  let evidence ← DeclaredResourceController.requireSome .capabilityRejected
    (config.capabilityEvidenceChecked wanted capability () signature () (fun _ => ())).toOption
  let law ← DeclaredResourceController.requireSome .policyUnavailable config.resolve?
  let witness := law.witness
  if inputsInRange profile.compilerProfile.compiler law.predicate
      context.oldState context.newState != true then
    throw .policyInputRange
  if !decide (castInjOn F (intsOf law.predicate
      context.oldState context.newState)) then
    throw .policyCastAlias
  let authorization ← DeclaredResourceController.requireSome .policyRejected
    (ComposedPolicyAdmission.admit config
      wanted evidence witness (.policy wanted.policyId wanted.policyRevision)
      (DeclaredResourceController.source_request_epoch_current prepared tuple incidence)
      (DeclaredResourceController.source_request_revision_current prepared tuple incidence))
  have portalExact : config.portal = portals prepared tuple checked incidence := by
    unfold portals policyConfig config
    rfl
  return portalExact ▸ authorization

structure CheckedLeg {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation
      deployment profile ambient ground command)
    (tuple : PreparedTuple (DeclaredResourceController.plan prepared))
    {domain semantics : Digest} {publicKey : List UInt8}
    {begin : ApplicationLifecycleBeginV3Ingress.Ingress}
    (physical : Checked domain semantics publicKey begin)
    (incidence : DeclaredResourceController.Incidence command)
    (envelope : List UInt8) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature ground.authority
  envelopeExact : receipt.envelopeBytes = envelope
  authorization : Authorized (portals prepared tuple physical incidence)
    ground.authority.authState (tuple.request incidence).2
  admitted : authorizeLeg prepared tuple incidence physical receipt = .ok authorization

def verifyLeg {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {command : DeclaredResourceController.Command}
    (native : CredentialSignatureIO.NativeConfig)
    (prepared : DeclaredResourceController.PreparedInvocation
      deployment profile ambient ground command)
    (tuple : PreparedTuple (DeclaredResourceController.plan prepared))
    {domain semantics : Digest} {publicKey : List UInt8}
    {begin : ApplicationLifecycleBeginV3Ingress.Ingress}
    (physical : Checked domain semantics publicKey begin)
    (incidence : DeclaredResourceController.Incidence command)
    (envelope : List UInt8) :
    IO (Except DeclaredResourceController.Reject
      (CheckedLeg prepared tuple physical incidence envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native ground.authority
      (DeclaredResourceController.operationMarker
        ground.authority.domain profile.semantics command)
      (tuple.request incidence).2 envelope with
  | .error reason => return .error (.legSignature reason)
  | .ok signature =>
      if exactWire : signature.envelopeBytes = envelope then
        match admitted : authorizeLeg prepared tuple incidence physical signature with
        | .error reason => return .error reason
        | .ok authorization => return .ok ⟨signature, exactWire, authorization, admitted⟩
      else return .error (.legSignature .sourceBinding)

/-- A complete special admission reuses the ordinary prepared command, tuple,
all target observations, native signatures, current capability snapshot and
installed policy compiler. The sole changed policy input is the app branch's
source-owned checked-completion slot. -/
structure Accepted {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {command : DeclaredResourceController.Command}
    (prepared : DeclaredResourceController.PreparedInvocation
      deployment profile ambient ground command)
    (signed : DeclaredResourceController.SignedCommand)
    {domain semantics : Digest} {publicKey : List UInt8}
    {begin : ApplicationLifecycleBeginV3Ingress.Ingress}
    (physical : Checked domain semantics publicKey begin) where
  private mk ::
  ingressExact : DeclaredResourceController.commandCodec.encode command = signed.commandBytes
  envelopeCount : signed.targetEnvelopes.length = command.targets.length
  observeCount : signed.observeEnvelopes.length =
    (if command.requiresObservation then command.targets.length else 0)
  observations : command.requiresObservation = true →
    (i : DeclaredResourceController.TargetIndex command) →
    DeclaredResourceController.ReadLeg prepared i
      (signed.observeEnvelopes[i.val]?.getD [])
  tuple : PreparedTuple (DeclaredResourceController.plan prepared)
  readEnvelopes : DeclaredResourceController.ReadEnvelopesEmpty command signed
  /-- The leg of every incidence but an observe-only read target, whose only
  authorization is its `ReadLeg` in `observations`. -/
  legs : (incidence : DeclaredResourceController.Incidence command) →
    DeclaredResourceController.incidenceObserveOnly command incidence = false →
    CheckedLeg prepared tuple physical incidence (signed.envelope command incidence)

def admit {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {command : DeclaredResourceController.Command}
    (native : CredentialSignatureIO.NativeConfig)
    (prepared : DeclaredResourceController.PreparedInvocation
      deployment profile ambient ground command)
    (signed : DeclaredResourceController.SignedCommand)
    {domain semantics : Digest} {publicKey : List UInt8}
    {begin : ApplicationLifecycleBeginV3Ingress.Ingress}
    (physical : Checked domain semantics publicKey begin) :
    IO (Except DeclaredResourceController.Reject
      (Accepted prepared signed physical)) := do
  if ingress : DeclaredResourceController.commandCodec.encode command = signed.commandBytes then
    if count : signed.targetEnvelopes.length = command.targets.length then
      if readCount : signed.observeEnvelopes.length =
          (if command.requiresObservation then command.targets.length else 0) then
       if readEnvelopes : DeclaredResourceController.ReadEnvelopesEmpty command signed then
        match ← DeclaredResourceController.verifyReads native prepared signed with
        | .error reason => return .error reason
        | .ok observations =>
          match DeclaredResourceController.prepareTuple prepared with
          | none => return .error .conflictingIncidences
          | some tuple =>
              match ← DeclaredResourceController.collectLegs (fun incidence _ =>
                  verifyLeg native prepared tuple physical incidence
                    (signed.envelope command incidence)) with
              | .error reason => return .error reason
              | .ok legs => return .ok ⟨ingress, count, readCount, observations, tuple, readEnvelopes, legs⟩
       else return .error .readTargetEnvelope
      else return .error .wrongEnvelopeCount
    else return .error .wrongEnvelopeCount
  else return .error .malformedCommand

end Minidregg.Kernel.ApplicationFailedStartRecoveryPolicy
