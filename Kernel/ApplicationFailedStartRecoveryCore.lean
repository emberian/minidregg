/- Exact durable recovery intent with current package guard, original-claim stable nullifier and complete event66 evidence. The receiver must bind historical admission and confirm the complete post-CAS image. -/
import Kernel.ApplicationFailedStartRecoveryAdmission

namespace Minidregg.Kernel.ApplicationFailedStartRecoveryCore

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

open Minidregg.Compiler.ServedBasis (Ground)
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (Reader)

def packageGuard {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress) :
    ReadGuard :=
  ApplicationLifecycleClaimCurrent.observationGuard
    ingress.source.originalBegin.base.source.packageManifest accepted.packageCell

def extraGuards {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress) :
    List ReadGuard :=
  if ingress.source.needsPackageWrite then [] else [packageGuard accepted]

theorem extraGuards_readonly {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress)
    (guard : ReadGuard) (member : guard ∈ extraGuards accepted) :
    guard.cellId ∉ (DeclaredResourceController.writes accepted.prepared).map DataWrite.cellId := by
  unfold extraGuards at member
  split at member
  · simp at member
  · simp only [List.mem_singleton] at member
    subst guard
    exact accepted.packageGuardReadOnly (by simp_all)

theorem extraGuards_current {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress)
    (guard : ReadGuard) (member : guard ∈ extraGuards accepted) :
    guard.expectedRoot = ground.view.model.roots guard.cellId := by
  unfold extraGuards at member
  split at member
  · simp at member
  · simp only [List.mem_singleton] at member
    subst guard
    exact accepted.packageRead.physicalCurrent

/-- Storage charge is the DRC's actual output write bytes plus the special
event ingress and new nullifier bytes. The ordinary event does not occupy a
second stored record. Extra work counts the package observation and physical
custodian verification, without charging an unperformed OS effect. -/
def charge {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress) :
    Charge :=
  let ws := DeclaredResourceController.writes accepted.prepared
  let guards := DeclaredResourceController.readGuards accepted.prepared ++ extraGuards accepted
  let base := DeclaredResourceController.sourceChargeFrom accepted.prepared ingress.signed ws guards
  fun dimension => match dimension with
    | .incidences => base .incidences + 1
    | .turnBytes => ingress.canonicalBytes.length
    | .witnessBytes => ingress.canonicalBytes.length
    | .proofWork => base .proofWork + 2
    | .memoryTouches => base .memoryTouches + 2
    | .storageBytes => base .storageBytes + ingress.canonicalBytes.length +
        (ApplicationFailedStartRecoveryIngress.stableNullifier ingress).canonicalBytes.length +
        (ingress.creationMarker.map (·.canonicalBytes.length)).getD 0
    | other => base other

def intent {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress) :
    DataIntent rootBytes := by
  let ws := DeclaredResourceController.writes accepted.prepared
  let guards := DeclaredResourceController.readGuards accepted.prepared ++ extraGuards accepted
  have guarded : ∀ guard ∈ guards, guard.cellId ∉ ws.map DataWrite.cellId := by
    intro guard member
    rcases List.mem_append.mp member with old | extra
    · exact DeclaredResourceController.readGuards_readonly accepted.prepared accepted.shape guard old
    · exact extraGuards_readonly accepted guard extra
  exact
    { transactionId := DeclaredResourceController.transactionId config.deployment.domain
        config.profile.semantics (ingress.source.command config.deployment.domain config.profile.semantics)
      writes := ws
      readGuards := guards
      nullifiers := [DeclaredResourceController.invocationNullifier config.deployment.domain
        (DeclaredResourceController.operationMarker config.deployment.domain
          config.profile.semantics (ingress.source.command config.deployment.domain config.profile.semantics)),
        ApplicationFailedStartRecoveryIngress.stableNullifier ingress] ++
        ingress.creationMarker.toList
      exactCharge := charge accepted
      event := ApplicationFailedStartRecoveryIngress.event ingress
      subject := some (ingress.source.command config.deployment.domain config.profile.semantics).subject
      postRootsBound := DeclaredResourceController.writes_roots_bound accepted.prepared
      guardsReadOnly := guarded }

theorem intent_event {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress) :
    (intent accepted).event = ApplicationFailedStartRecoveryIngress.event ingress := rfl

theorem intent_event_version {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress) :
    (intent accepted).event.codecVersion = 66 := rfl

theorem intent_has_report_nullifier {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress) :
    ApplicationFailedStartRecoveryIngress.stableNullifier ingress ∈
      (intent accepted).nullifiers := by
  simp [intent]

theorem intent_has_created_marker {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress)
    (marker : StableNullifier) (created : ingress.creationMarker = some marker) :
    marker ∈ (intent accepted).nullifiers := by
  simp [intent, created]

theorem intent_writes {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress) :
    (intent accepted).writes = DeclaredResourceController.writes accepted.prepared := rfl

theorem intent_package_guard_current {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationFailedStartRecoveryIngress.Ingress}
    (accepted : ApplicationFailedStartRecoveryAdmission.Candidate config head ground ingress)
    (readOnly : ingress.source.needsPackageWrite = false) :
    packageGuard accepted ∈ (intent accepted).readGuards ∧
      (packageGuard accepted).expectedRoot =
        ground.view.model.roots (packageGuard accepted).cellId := by
  constructor
  · change packageGuard accepted ∈
      DeclaredResourceController.readGuards accepted.prepared ++ extraGuards accepted
    apply List.mem_append_right
    simp [extraGuards, readOnly]
  · exact accepted.packageRead.physicalCurrent

end Minidregg.Kernel.ApplicationFailedStartRecoveryCore
