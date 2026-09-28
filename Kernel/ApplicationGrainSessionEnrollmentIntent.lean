/-
One durable event28 intent from a natively admitted joint enrollment and
three independently signed, same-image observations. No receipt or HTTP
permission is constructed by this candidate intent.
-/
import Kernel.ApplicationGrainSessionEnrollmentAdmission

namespace Minidregg.Kernel.ApplicationGrainSessionEnrollmentIntent

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentAdmission

set_option autoImplicit false

private def appGuard {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config opened ingress spec receipt) : ReadGuard :=
  ⟨⟨spec.ticket.scope.app⟩,
    ResourceBirthCodec.physicalRoot (.live checked.appRead.selected.observed.before)⟩

private def manifestGuard {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config opened ingress spec receipt) : ReadGuard :=
  ⟨⟨ingress.request.packageManifest⟩,
    ResourceBirthCodec.physicalRoot (.live checked.manifestRead.selected.observed.before)⟩

private def ticketGuard {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config opened ingress spec receipt) : ReadGuard :=
  ⟨⟨spec.ticket.resource⟩,
    ResourceBirthCodec.physicalRoot (.live checked.ticketRead.selected.observed.before)⟩

def readGuards {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config opened ingress spec receipt) : List ReadGuard :=
  [appGuard checked, manifestGuard checked, ticketGuard checked]

theorem readGuards_current {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config opened ingress spec receipt)
    (guard : ReadGuard) (member : guard ∈ readGuards checked) :
    guard.expectedRoot = opened.durable.snapshot.model.roots guard.cellId := by
  simp [readGuards] at member
  rcases member with app | manifest | ticket
  · subst guard; exact checked.appRead.current
  · subst guard; exact checked.manifestRead.current
  · subst guard; exact checked.ticketRead.current

theorem readGuards_readonly {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config opened ingress spec receipt)
    (guard : ReadGuard) (member : guard ∈ readGuards checked) :
    guard.cellId ∉ (DeclaredResourceController.writes checked.prepared).map DataWrite.cellId := by
  simp [readGuards] at member
  rcases member with app | manifest | ticket
  · subst guard; exact checked.appRead.readonly
  · subst guard; exact checked.manifestRead.readonly
  · subst guard; exact checked.ticketRead.readonly

def charge {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config opened ingress spec receipt) : Charge :=
  let ordinary := checked.accepted.dataIntent checked.shape
  fun dimension => match dimension with
    | .incidences => ordinary.exactCharge .incidences + 3
    | .turnBytes => ingress.canonicalBytes.length
    | .witnessBytes => ingress.canonicalBytes.length
    | .proofWork => ordinary.exactCharge .proofWork + 3
    | .memoryTouches => ordinary.exactCharge .memoryTouches + 3
    | .storageBytes => ordinary.exactCharge .storageBytes + ingress.canonicalBytes.length
    | other => ordinary.exactCharge other

def intent {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config opened ingress spec receipt) :
    DataIntent rootBytes := by
  let ordinary := checked.accepted.dataIntent checked.shape
  have readonly : ∀ guard ∈ ordinary.readGuards ++ readGuards checked,
      guard.cellId ∉ ordinary.writes.map DataWrite.cellId := by
    intro guard member
    rcases List.mem_append.mp member with old | extra
    · exact ordinary.guardsReadOnly guard old
    · exact readGuards_readonly checked guard extra
  exact
    { transactionId := ordinary.transactionId
      writes := ordinary.writes
      readGuards := ordinary.readGuards ++ readGuards checked
      nullifiers := ordinary.nullifiers
      exactCharge := charge checked
      event := ApplicationGrainSessionEnrollmentSource.event config.deployment.domain ingress
      postRootsBound := ordinary.postRootsBound
      guardsReadOnly := readonly }

theorem intent_event_version {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config opened ingress spec receipt) :
    (intent checked).event.codecVersion = 28 := rfl

theorem intent_retains_full_ingress {config : Config} {opened : Opened config}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config opened ingress spec receipt) :
    (intent checked).event.canonicalBytes = ingress.canonicalBytes := rfl

end Minidregg.Kernel.ApplicationGrainSessionEnrollmentIntent
