/-
Select an app share issuance from the actual native-admitted replay pass. The
checkpoint retains exactly one original prefix; no reconstructed caller image
or event-shaped bytes can stand in for verified admission.
-/
import Kernel.NativeHostReplay
import Kernel.ApplicationShareIssueReceiver
import Kernel.ApplicationDispatchHistoricalCore

namespace Minidregg.Kernel.ApplicationShareIssueHistorical
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.NativeHostReplay
open Minidregg.Kernel.ApplicationShareIssueSource
open Minidregg.Kernel.ApplicationShareIssueAdmission
set_option autoImplicit false

structure Issued (config : Config) (target : Durable) (index : Nat) where
  private mk ::
  selection : VerifiedSelection config target index
  ingress : ApplicationShareIssueSource.Ingress
  accepted : ApplicationShareIssueAdmission.Accepted config.profile config
    selection.selected.before.pins selection.selected.before.durable
    (logicalHeight config selection.selected.before.durable) ingress
  matched : recordMatches selection.selected.record
    (ApplicationShareIssueReceiver.intent accepted) = true
  receiptTransaction : selection.selected.receipt.transactionId =
    accepted.birth.descriptor.transactionId
  receiptEvent : selection.selected.receipt.eventId =
    (ApplicationShareIssueReceiver.event config.deployment.domain ingress).eventId

/-- Re-admit the complete original composite ingress against the exact
verifier-retained prefix and compare the entire durable record. The original
receipt comes from that same accepted walk, not a caller-supplied projection. -/
def select (config : Config) (target : Durable) (index : Nat) :
    IO (Except String (Issued config target index)) := do
  let .ok selection ← verifyLoadedSelected config target index
    | return .error "share issue selected native history refused"
  let before := selection.selected.before
  let .ok ⟨ingress, accepted⟩ ← ApplicationShareIssueAdmission.admitNative
      config.profile config before.pins config.signature before.durable
      (logicalHeight config before.durable)
      selection.selected.record.event.canonicalBytes
    | return .error "share issue original admission refused"
  let intent := ApplicationShareIssueReceiver.intent accepted
  if matched : recordMatches selection.selected.record intent = true then
    if receiptTransaction : selection.selected.receipt.transactionId =
        accepted.birth.descriptor.transactionId then
      if receiptEvent : selection.selected.receipt.eventId =
          (ApplicationShareIssueReceiver.event config.deployment.domain ingress).eventId then
        return .ok ⟨selection, ingress, accepted, matched,
          receiptTransaction, receiptEvent⟩
      else return .error "share issue original receipt event differs"
    else return .error "share issue original receipt transaction differs"
  else return .error "share issue original intent differs from durable record"

/-- This issue is precisely the full record at the chosen index of an exact
verified current image. -/
theorem Issued.record_exact {config : Config} {target : Durable} {index : Nat}
    (issued : Issued config target index) :
    target.image.accepted[index]? =
      some (DurableReceiver.IntentRecord.ofIntent
        (ApplicationShareIssueReceiver.intent issued.accepted)) := by
  rw [issued.selection.record_at]
  exact congrArg some ((recordMatches_iff _ _).mp issued.matched)

/-- The lower dispatch core receives only the compact admitted-issue fact;
`record_exact` separately binds it to the verifier's current chronological
history at this selected index. -/
def Issued.toEvidence {config : Config} {target : Durable} {index : Nat}
    (issued : Issued config target index) :
    ApplicationDispatchHistoricalCore.IssuedEvidence config :=
  ApplicationDispatchHistoricalCore.IssuedEvidence.fromAccepted config
    issued.selection.selected.before.pins
    issued.selection.selected.before.durable
    (logicalHeight config issued.selection.selected.before.durable)
    issued.ingress issued.accepted issued.selection.selected.record
    ((recordMatches_iff _ _).mp issued.matched)

end Minidregg.Kernel.ApplicationShareIssueHistorical
