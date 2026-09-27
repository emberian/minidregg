/-
Source-derived pending dispatch payload from the native current-image checks.
This module deliberately exposes no CAS receiver or physical delivery permit:
`CheckedCurrent` alone cannot prove that the installed ticket came from an
accepted historical share issue. An upper verifier must supply that provenance
and bind it to the complete issue ingress before committing this candidate.
-/
import Kernel.ApplicationDispatchAdmission

namespace Minidregg.Kernel.ApplicationDispatchPending

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationDispatchAdmission

set_option autoImplicit false

variable {F : Type} [Field F] [DecidableEq F]
variable {deployment : CanonicalCellRegistry.Deployment}
variable {profile : CanonicalRuntimeProfile.Profile F}
variable {ambient : DeclaredResourceController.Ambient}
variable {durable : DeclaredResourceController.Durable}
variable {ingress : ApplicationDispatchAdmissionIngress.Ingress}
variable {spec : ApplicationShareIssueSource.Spec}
variable {descriptor : ResourceBirth.Descriptor CanonicalCellRegistry.registry}

private def appGuard (_checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    ReadGuard := observationGuard ingress.dispatch.dispatch.app.resource ingress.dispatch.appRoot

private def manifestGuard (_checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    ReadGuard := observationGuard ingress.dispatch.dispatch.app.packageManifest
      ingress.dispatch.dispatch.app.manifestRoot

private def enrollmentGuard (_checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    ReadGuard := observationGuard ingress.dispatch.enrollmentResource ingress.dispatch.enrollmentRoot

private def ticketGuard (_checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    ReadGuard := observationGuard spec.ticket.resource ingress.ticketRoot

/-- Four independently signed and checked current reads are bound to the
same physical CAS as the session/agent witness. -/
def readGuards (checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    List ReadGuard :=
  [appGuard checked, manifestGuard checked, enrollmentGuard checked, ticketGuard checked]

theorem readGuards_current
    (checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor)
    (guard : ReadGuard) (member : guard ∈ readGuards checked) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId := by
  simp [readGuards] at member
  rcases member with app | manifest | enrollment | ticket
  · subst guard; exact checked.appRead.current
  · subst guard; exact checked.manifestRead.current
  · subst guard; exact checked.enrollmentRead.current
  · subst guard; exact checked.ticketRead.current

theorem readGuards_readonly
    (checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor)
    (guard : ReadGuard) (member : guard ∈ readGuards checked) :
    guard.cellId ∉ (DeclaredResourceController.writes checked.prepared).map DataWrite.cellId := by
  simp [readGuards] at member
  rcases member with app | manifest | enrollment | ticket
  · subst guard; exact checked.appRead.readonly
  · subst guard; exact checked.manifestRead.readonly
  · subst guard; exact checked.enrollmentRead.readonly
  · subst guard; exact checked.ticketRead.readonly

/-- The pending source tariff includes four additional native observations,
the complete wrapper ingress, and its stable one-use operation key. It charges
no external HTTP effect, which has not happened. -/
def charge (checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    Charge :=
  let ordinary := checked.invocation.dataIntent checked.shape
  fun dimension => match dimension with
    | .incidences => ordinary.exactCharge .incidences + 4
    | .turnBytes => ingress.canonicalBytes.length
    | .witnessBytes => ingress.canonicalBytes.length
    | .proofWork => ordinary.exactCharge .proofWork + 4
    | .memoryTouches => ordinary.exactCharge .memoryTouches + 4
    | .storageBytes => ordinary.exactCharge .storageBytes +
        ingress.canonicalBytes.length +
        (ApplicationDispatchAdmissionIngress.nullifier ingress).canonicalBytes.length
    | other => ordinary.exactCharge other

/-- A special pending event, not the ordinary DRC mutation receipt. This is a
candidate data intent; only a receiver joined with verifier-authenticated
share-issue provenance may submit it. -/
def candidateIntent
    (checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    DataIntent rootBytes := by
  let ordinary := checked.invocation.dataIntent checked.shape
  have guarded : ∀ guard ∈ ordinary.readGuards ++ readGuards checked,
      guard.cellId ∉ ordinary.writes.map DataWrite.cellId := by
    intro guard member
    rcases List.mem_append.mp member with old | extra
    · exact ordinary.guardsReadOnly guard old
    · exact readGuards_readonly checked guard extra
  exact
    { transactionId := ordinary.transactionId
      writes := ordinary.writes
      readGuards := ordinary.readGuards ++ readGuards checked
      nullifiers := ordinary.nullifiers ++
        [ApplicationDispatchAdmissionIngress.nullifier ingress]
      exactCharge := charge checked
      event := ApplicationDispatchAdmissionIngress.event ingress
      postRootsBound := ordinary.postRootsBound
      guardsReadOnly := guarded }

theorem candidateIntent_retains_full_ingress
    (checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    (candidateIntent checked).event.canonicalBytes = ingress.canonicalBytes := rfl

theorem candidateIntent_event_version
    (checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    (candidateIntent checked).event.codecVersion = 11 := rfl

theorem candidateIntent_reuses_ordinary_transaction
    (checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    (candidateIntent checked).transactionId =
      (checked.invocation.dataIntent checked.shape).transactionId := rfl

/-- Even when the ordinary command/transaction marker is identical, changing
any outer HTTP, ticket or issue coordinate changes the exact special event.
The durable same-id path must therefore treat it as a conflict, never replay
the old receipt as authorization for the new outer request. -/
theorem special_event_eq_iff_ingress_eq
    (left right : ApplicationDispatchAdmissionIngress.Ingress) :
    ApplicationDispatchAdmissionIngress.event left =
      ApplicationDispatchAdmissionIngress.event right ↔ left = right := by
  constructor
  · intro equal
    exact (lawful_encode_injective ApplicationDispatchAdmissionIngress.codec)
      (congrArg StableEvent.canonicalBytes equal)
  · intro equal
    rw [equal]

theorem candidateIntent_ne_ordinary_event
    (checked : CheckedCurrent deployment profile ambient durable ingress spec descriptor) :
    (candidateIntent checked).event ≠
      DeclaredResourceController.invocationEvent deployment.domain profile.semantics
        (ApplicationDispatchCommand.command ingress.dispatch checked.selection ingress.parent)
        ingress.dispatch.signed := by
  intro equal
  have versions := congrArg StableEvent.codecVersion equal
  norm_num [candidateIntent, ApplicationDispatchAdmissionIngress.event,
    DeclaredResourceController.invocationEvent] at versions

end Minidregg.Kernel.ApplicationDispatchPending
