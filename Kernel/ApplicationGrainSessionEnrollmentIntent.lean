/-
One durable event28 intent from a natively admitted joint enrollment and
three independently signed, same-image observations. No receipt or HTTP
permission is constructed by this candidate intent.
-/
module

public import Kernel.ApplicationGrainSessionEnrollmentAdmission

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

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

private def appGuard {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt) : ReadGuard :=
  ⟨⟨spec.ticket.scope.app⟩,
    ResourceBirthCodec.physicalRoot (.live checked.appRead.selected.observed.before)⟩

private def manifestGuard {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt) : ReadGuard :=
  ⟨⟨ingress.request.packageManifest⟩,
    ResourceBirthCodec.physicalRoot (.live checked.manifestRead.selected.observed.before)⟩

private def ticketGuard {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt) : ReadGuard :=
  ⟨⟨spec.ticket.resource⟩,
    ResourceBirthCodec.physicalRoot (.live checked.ticketRead.selected.observed.before)⟩

def readGuards {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt) : List ReadGuard :=
  [appGuard checked, manifestGuard checked, ticketGuard checked]

theorem readGuards_current {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt)
    (guard : ReadGuard) (member : guard ∈ readGuards checked) :
    guard.expectedRoot = ground.cells.model.roots guard.cellId := by
  simp [readGuards] at member
  rcases member with app | manifest | ticket
  · subst guard; exact checked.appRead.current
  · subst guard; exact checked.manifestRead.current
  · subst guard; exact checked.ticketRead.current

theorem readGuards_readonly {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt)
    (guard : ReadGuard) (member : guard ∈ readGuards checked) :
    guard.cellId ∉ (DeclaredResourceController.writes checked.prepared).map DataWrite.cellId := by
  simp [readGuards] at member
  rcases member with app | manifest | ticket
  · subst guard; exact checked.appRead.readonly
  · subst guard; exact checked.manifestRead.readonly
  · subst guard; exact checked.ticketRead.readonly

/-- The enrollment tariff over an already-derived ordinary intent. Keeping `ordinary` as a
parameter prevents the lane closure from re-deriving its writes and guards for every lane. -/
def chargeOf {config : Config} {ground : ServedBasis.Ground config.deployment} {ingress : Ingress}
    (ordinary : DataIntent rootBytes) : Charge :=
  fun dimension => match dimension with
    | .incidences => ordinary.exactCharge .incidences + 3
    | .turnBytes => ingress.canonicalBytes.length
    | .witnessBytes => ingress.canonicalBytes.length
    | .proofWork => ordinary.exactCharge .proofWork + 3
    | .memoryTouches => ordinary.exactCharge .memoryTouches + 3
    | .storageBytes => DeployedCharge.storageCharge ground.view ordinary.writes
        (ApplicationGrainSessionEnrollmentSource.event config.deployment.domain ingress)
    | other => ordinary.exactCharge other

def charge {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt) : Charge :=
  chargeOf (config := config) (ground := ground) (ingress := ingress)
    (checked.accepted.dataIntent checked.shape)

def intent {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt) :
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
      exactCharge := (Minidregg.Theory.ResourceCost.Charge.materialize
        (chargeOf (config := config) (ground := ground) (ingress := ingress) ordinary)).toCharge
      event := ApplicationGrainSessionEnrollmentSource.event config.deployment.domain ingress
      subject := ordinary.subject
      postRootsBound := ordinary.postRootsBound
      guardsReadOnly := readonly }

theorem intent_exactCharge {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt) :
    (intent checked).exactCharge = charge checked := by
  exact Minidregg.Theory.ResourceCost.Charge.materialize_eq _

theorem intent_event_version {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt) :
    (intent checked).event.codecVersion = 28 := rfl

theorem intent_retains_full_ingress {config : Config} {ground : ServedBasis.Ground config.deployment}
    {ingress : Ingress} {spec : ApplicationShareIssueSource.Spec}
    {receipt : NativeHostCodec.Receipt}
    (checked : Checked config ground ingress spec receipt) :
    (intent checked).event.canonicalBytes = ingress.canonicalBytes := rfl

end Minidregg.Kernel.ApplicationGrainSessionEnrollmentIntent
