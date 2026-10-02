/-
A retained old-profile ticket may authorize a new-profile session enrollment
only through current admission. This is separate from target-profile PriorIssue:
the old descriptor is neither coerced nor re-admitted with today's codec.
-/
import Compiler.CarriedApplicationProvenance
import Kernel.ApplicationGrainSessionEnrollmentIntent

namespace Minidregg.Kernel.CarriedSessionEnrollmentAdmission

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.CarriedApplicationProvenance
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource

set_option autoImplicit false

structure Admitted (config : Config) (opened : Opened config) (ingress : Ingress) where
  private mk ::
  issue : CarriedIssue config opened.durable
  issueIndex : issue.index = ingress.request.issueIndex
  issueReceipt : issue.receipt = ingress.issueReceipt
  ticketResource : issue.spec.ticket.resource = ingress.request.ticketResource
  checked : ApplicationGrainSessionEnrollmentAdmission.Checked config opened ingress
    issue.spec issue.receipt

/-- Reuses actual current interface/ticket/role checks, current signed DRC, and
three independent current signed resource reads. Old admission never bypasses
target policy, current revocation, or same-image physical guards. -/
def admitAt (config : Config) (opened : Opened config)
    (issue : CarriedIssue config opened.durable) (ingress : Ingress) :
    IO (Except String (Admitted config opened ingress)) := do
  if issueIndex : issue.index = ingress.request.issueIndex then
    if issueReceipt : issue.receipt = ingress.issueReceipt then
      if ticketResource : issue.spec.ticket.resource = ingress.request.ticketResource then
        match ← ApplicationGrainSessionEnrollmentAdmission.admitAt config opened ingress
            issue.spec issue.receipt with
        | .error detail => return .error detail
        | .ok checked => return .ok ⟨issue, issueIndex, issueReceipt, ticketResource, checked⟩
      else return .error "carried enrollment ticket resource differs"
    else return .error "carried enrollment original receipt differs"
  else return .error "carried enrollment original index differs"

def Admitted.intent {config : Config} {opened : Opened config} {ingress : Ingress}
    (admitted : Admitted config opened ingress) : DurableDataIntent.DataIntent rootBytes :=
  ApplicationGrainSessionEnrollmentIntent.intent admitted.checked

theorem Admitted.event28 {config : Config} {opened : Opened config} {ingress : Ingress}
    (admitted : Admitted config opened ingress) : admitted.intent.event.codecVersion = 28 := rfl

theorem Admitted.retains_ingress {config : Config} {opened : Opened config} {ingress : Ingress}
    (admitted : Admitted config opened ingress) :
    admitted.intent.event.canonicalBytes = ingress.canonicalBytes := rfl

theorem Admitted.original_record_present {config : Config} {opened : Opened config}
    {ingress : Ingress} (admitted : Admitted config opened ingress) :
    opened.durable.image.accepted[ingress.request.issueIndex]? = some admitted.issue.record := by
  rw [← admitted.issueIndex]
  exact admitted.issue.currentPresent

end Minidregg.Kernel.CarriedSessionEnrollmentAdmission
