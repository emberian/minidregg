/-
Current dispatch admission joined to an authenticated carried issue.
Old scope commitments retain exact descriptor bytes; current roots, epochs,
revocation, grants, policy linkage and all signed reads are checked anew.
-/
import Compiler.CarriedDispatchProvenance
import Kernel.ApplicationDispatchPending

namespace Minidregg.Kernel.CarriedDispatchAdmission

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.CarriedDispatchProvenance
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Admitted (config : Config) (opened : Opened config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) where
  private mk ::
  issue : CarriedDispatchIssue config opened.durable
  issueBytesExact : ingress.issueIngressBytes = issue.issue.ingress.canonicalBytes
  checked : ApplicationDispatchAdmission.CheckedCurrentForSourceBytes
    config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩ opened.durable ingress
    issue.issue.spec issue.originalSourceBytes

def admitAt (config : Config) (opened : Opened config)
    (issue : CarriedDispatchIssue config opened.durable)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    IO (Except String (Admitted config opened ingress)) := do
  if issueBytesExact : ingress.issueIngressBytes = issue.issue.ingress.canonicalBytes then
    match ← ApplicationDispatchAdmission.checkCurrentFromSourceBytes
        config.deployment config.profile
        ⟨config.federation, logicalHeight config opened.durable⟩ config.signature
        opened.durable ingress issue.issue.spec issue.originalSourceBytes with
    | .error detail => return .error detail
    | .ok checked => return .ok ⟨issue, issueBytesExact, checked⟩
  else return .error "carried dispatch source differs from admitted old issue"

def Admitted.intent {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : Admitted config opened ingress) : DurableDataIntent.DataIntent rootBytes :=
  ApplicationDispatchPending.candidateIntent admitted.checked

theorem Admitted.event11 {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : Admitted config opened ingress) : admitted.intent.event.codecVersion = 11 := rfl

theorem Admitted.retains_ingress {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : Admitted config opened ingress) :
    admitted.intent.event.canonicalBytes = ingress.canonicalBytes := rfl

theorem Admitted.original_record_present {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : Admitted config opened ingress) :
    opened.durable.image.accepted[admitted.issue.issue.index]? =
      some admitted.issue.issue.record := admitted.issue.issue.currentPresent

end Minidregg.Kernel.CarriedDispatchAdmission
