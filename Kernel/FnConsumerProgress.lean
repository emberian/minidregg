/-
Durable progress for an observed empty fn consumer page. This is a local
processing declaration, not an application operation or fn-issued evidence.
Only the pinned gateway may write the record. The host must have obtained the
cursor from an actual trusted local poll and checked its scope and positions
before calling evaluateVerified; a user-supplied Bool is not an attestation.
-/
import Kernel.FnConsumerProgressHistory
import Kernel.FnConsumerOperation

namespace Minidregg.Kernel.FnConsumerProgress

open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

/-- The lower historical selector retains the existing operation name rule,
exact signed-command bytes and transaction marker. The v1 wire is unchanged. -/
theorem validName_legacy_exact (value : List UInt8) :
    FnConsumerScope.validName value = FnConsumerOperation.validName value := by
  rfl

theorem exactSignedCommand_legacy_exact (signedBytes : List UInt8)
    (expected : DeclaredResourceController.Command) :
    exactSignedCommand signedBytes expected =
      FnConsumerOperation.exactSignedCommand signedBytes expected := by
  rfl

theorem marker_legacy_exact (domain semantics : Digest)
    (subject : SubjectId) (evidence : Evidence) :
    marker domain semantics subject evidence =
      FnConsumerOperation.marker domain semantics subject
        (progressNonce domain semantics evidence) := by
  rfl

def Report.matchesGateway (report : Report) (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) : Bool :=
  policy.matchesGateway pin &&
  report.evidence.application == policy.application &&
  report.subject == policy.subject && report.target == policy.target &&
  report.capability == policy.capability

def checkReport (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (report : Report) : Except String Unit :=
  if report.matchesGateway pin policy then
    if report.evidence.valid then .ok ()
    else .error "empty-page progress is unobserved, unscoped, or outside selected scan bound"
  else .error "empty-page progress differs from independently pinned gateway"

/-- An accepted report cannot select its own subject or resource. -/
theorem checkReport_pinned (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (report : Report)
    (accepted : checkReport pin policy report = .ok ()) :
    report.evidence.application = pin.application ∧
    report.subject = pin.subject ∧ report.target = pin.target ∧
    report.capability = pin.capability := by
  have pinned : report.matchesGateway pin policy = true := by
    cases hval : report.matchesGateway pin policy with
    | false => simp [checkReport, hval] at accepted
    | true => rfl
  simp [Report.matchesGateway, FnConsumerOperation.Policy.matchesGateway] at pinned
  aesop

inductive Decision where
  | fresh (command : DeclaredResourceController.Command)
  | repeated
  | refused (detail : String)
  deriving Repr

def decide (pin : FnGatewayPolicy.Pin) (scope : Scope)
    (domain semantics : Digest) (report : Report)
    (accepted : List DurableReceiver.IntentRecord) : Decision :=
  let transaction := marker domain semantics report.subject report.evidence
  match accepted.find? (fun entry => entry.transactionId == transaction) with
  | none => .fresh (progressCommand domain semantics report)
  | some original =>
      if originalSkip pin scope domain semantics original == some report.evidence then
        .repeated
      else .refused "empty-page progress marker occupied by another transaction"

def Decision.intent (report : Report) : Decision → Option NativeObservationCodec.Intent
  | .fresh command =>
      some ⟨report.subject, command.nonce + 1,
        .prepare (.invoke (DeclaredResourceController.commandCodec.encode command)),
        [⟨.object, report.target, report.capability⟩]⟩
  | _ => none

def evaluateVerified (consumer : NativeHost.Config) (pin : FnGatewayPolicy.Pin)
    (policy : FnConsumerOperation.Policy) (scope : Scope) (report : Report)
    (opened : NativeHost.Opened consumer) : Except String Decision := do
  checkReport pin policy report
  unless report.evidence.scope == scope do
    throw "empty-page progress scope differs from independently selected fn consumer"
  FnGatewayPolicy.checkCurrent consumer opened pin
  pure (decide pin scope consumer.deployment.domain consumer.profile.semantics
    report opened.durable.image.accepted)

end Minidregg.Kernel.FnConsumerProgress
