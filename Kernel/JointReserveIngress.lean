/- Current native admission for the retained event60 reservation ingress.
Raw bytes reconstruct a claim only. The receiver repeats the actual selected
ordinary call, every purpose-specific signature/law, and source control method
at precisely this source prefix. It never imports an old AcceptedInvocation.
-/
import Kernel.JointReceiverAdmission
import Kernel.NativeHostContext
import Compiler.PrivateSuccessorCustodyCodec
namespace Minidregg.Kernel.JointReserveIngress
open Minidregg.Theory
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.PrivateSuccessorCustodyCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.JointInvocationCandidate
open Minidregg.Kernel.JointReceiverAdmission
open Minidregg.Kernel.PrivateSuccessorCustody
set_option autoImplicit false
set_option maxHeartbeats 800000

def frame : List UInt8 := "DREGG/JOINT/SOURCE-RESERVE/v1".toUTF8.toList

def decodeSource (bytes : List UInt8) : Option ReserveSource := do
  if bytes.take frame.length != frame then none else
  let source ← reserveSourceStream.toLawful.decode (bytes.drop frame.length)
  if reserveSourceBytes source != bytes then none else some source

/-- Structural plan reconstruction checks exact byte syntax, distinct source
participants and the already required final signer/nullifier. It does not claim
that an arbitrary submitter invented a complete hidden evaluator footprint. -/
def decodePlan (bytes : List UInt8) : Option (Plan Descriptor) := do
  let candidate ← (candidateStream descriptorStream).toLawful.decode bytes
  if (candidateStream descriptorStream).encode candidate != bytes then none else
  if distinct : candidate.required.Nodup then
    let index ← candidate.participants.findIdx? (fun p => p.domain == candidate.lastSigner)
    if bound : index < candidate.participants.length then
      let last : Fin candidate.participants.length := ⟨index,bound⟩
      if same : (candidate.participants[last]).domain = candidate.lastSigner then
        if lineage : candidate.lineage ∈ (candidate.participants[last]).intent.nullifiers then
          some ⟨candidate,distinct,last,same,lineage⟩
        else none
      else none
    else none
  else none

/-- PENDING custody identity is retained exactly but not qualified by this
function. Physical readiness/privateRecovery is a subsequent native operation. -/
def descriptorMatches (candidate : Candidate Descriptor) (p : Projection Descriptor) : Bool :=
  decide (p.custody.key.commandBytes = candidate.commandBytes) &&
  decide (p.custody.key.invocation = p.intent.transactionId) &&
  decide (p.custody.key.attempt = candidate.attempt) &&
  decide (p.custody.key.generation = p.generation) &&
  decide (DurableReceiverCodec.intentStream.encode p.custody.exactSuccessor =
    DurableReceiverCodec.intentStream.encode p.intent)

/-- Only current native source admission can return the opaque reservation
capability. Fixed config supplies resource schema, epoch, runtime semantics,
current authority directory and native signature helper. The packet supplies
none of those verification policies. -/
def admit (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO (Except String (Reserved config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable)) := do
  let some source := decodeSource bytes | return .error "noncanonical joint reserve source"
  let some pin := config.jointControl | return .error "joint source control not enabled"
  let some consensus := config.jointConsensus | return .error "joint source consensus not enabled"
  let some plan := decodePlan source.candidateBytes | return .error "invalid exact candidate plan"
  if plan.candidate.semantics != config.profile.semantics then
    return .error "candidate runtime semantics mismatch"
  if source.promise.declaration.epoch != consensus.epoch then return .error "reservation epoch mismatch"
  if member : source.participant < plan.candidate.participants.length then
    let i : Fin plan.candidate.participants.length := ⟨source.participant,member⟩
    let p := plan.candidate.participants[i]
    if !(descriptorMatches plan.candidate p) then return .error "custody descriptor identity mismatch"
    let some (selectedDomain,selectedSemantics,selected) :=
      decodeSignedBytes source.promise.declaration.selectedSignedBytes
      | return .error "invalid selected signed invocation"
    if selectedDomain != config.deployment.domain || selectedSemantics != config.profile.semantics then
      return .error "selected source scope mismatch"
    if plan.candidate.commandBytes != selected.commandBytes then return .error "candidate command mismatch"
    let some command := commandCodec.decode selected.commandBytes
      | return .error "invalid selected command"
    let ambient := ⟨config.federation,logicalHeight config opened.durable⟩
    match prepareFrom config.deployment config.profile ambient opened.durable (some opened.directory) command with
    | .error reason => return .error s!"selected preparation refused: {repr reason}"
    | .ok prepared =>
      if shape : PhysicalShape prepared then
        match ← JointPromiseAuthorization.admit config.signature prepared shape selected source.promise with
        | .error reason => return .error s!"current install promise refused: {repr reason}"
        | .ok promised =>
          match config.sourceGate none opened.durable.snapshot (promised.ordinary.dataIntent promised.shape) with
          | .error _ => return .error "selected operation conflicts with a protected source facet"
          | .ok () => pure ()
          let some (controlDomain,controlSemantics,controlSigned) := decodeSignedBytes source.controlSignedBytes
            | return .error "invalid signed control operation"
          if controlDomain != config.deployment.domain || controlSemantics != config.profile.semantics then
            return .error "control source scope mismatch"
          let some controlCommand := commandCodec.decode controlSigned.commandBytes
            | return .error "invalid control command"
          match prepareFrom config.deployment config.profile ambient opened.durable (some opened.directory) controlCommand with
          | .error reason => return .error s!"control preparation refused: {repr reason}"
          | .ok controlPrepared =>
            if controlShape : PhysicalShape controlPrepared then
              match ← DeclaredResourceController.admit config.signature controlPrepared controlSigned with
              | .error reason => return .error s!"current control operation refused: {repr reason}"
              | .ok controlAccepted =>
                let some reserved := buildReserve descriptorStream pin consensus.epoch plan i promised controlShape controlAccepted
                  | return .error "exact reservation/funding/source transition refused"
                if reserved.intent.event.canonicalBytes != bytes then
                  return .error "reservation ingress differs from actual derived record"
                return .ok reserved
            else return .error "control physical shape refused"
      else return .error "selected physical shape refused"
  else return .error "participant outside exact candidate"
end Minidregg.Kernel.JointReserveIngress
