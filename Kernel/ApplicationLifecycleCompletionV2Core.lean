/-
The checked completion's source-owned durable intent. Admission above this
module binds the physical custodian, exact historical claim, current law,
signed package observation, and all incidences on one old image. This module
does not submit a CAS or authorize a physical launch.
-/
import Kernel.ApplicationLifecycleCompletionV2Admission

namespace Minidregg.Kernel.ApplicationLifecycleCompletionV2Core

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
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress) :
    ReadGuard :=
  ApplicationLifecycleClaimCurrent.observationGuard
    ingress.source.originalBegin.base.source.packageManifest accepted.packageCell

def extraGuards {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress) :
    List ReadGuard :=
  if ingress.source.needsPackageWrite then [] else [packageGuard accepted]

theorem extraGuards_readonly {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress)
    (guard : ReadGuard) (member : guard ∈ extraGuards accepted) :
    guard.cellId ∉ (DeclaredResourceController.writes accepted.prepared).map DataWrite.cellId := by
  unfold extraGuards at member
  split at member
  · simp at member
  · simp only [List.mem_singleton] at member
    subst guard
    exact accepted.packageGuardReadOnly (by simp_all)

theorem extraGuards_current {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress)
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
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress) :
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
        (ApplicationLifecycleCompletionV2Ingress.stableNullifier ingress).canonicalBytes.length +
        (ingress.creationMarker.map (·.canonicalBytes.length)).getD 0
    | other => base other

def intent {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress) :
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
        ApplicationLifecycleCompletionV2Ingress.stableNullifier ingress] ++
        ingress.creationMarker.toList
      exactCharge := charge accepted
      event := ApplicationLifecycleCompletionV2Ingress.event ingress
      subject := some (ingress.source.command config.deployment.domain config.profile.semantics).subject
      postRootsBound := DeclaredResourceController.writes_roots_bound accepted.prepared
      guardsReadOnly := guarded }

theorem intent_event {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress) :
    (intent accepted).event = ApplicationLifecycleCompletionV2Ingress.event ingress := rfl

theorem intent_event_version {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress) :
    (intent accepted).event.codecVersion = 25 := rfl

theorem intent_has_report_nullifier {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress) :
    ApplicationLifecycleCompletionV2Ingress.stableNullifier ingress ∈
      (intent accepted).nullifiers := by
  simp [intent]

theorem intent_has_created_marker {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress)
    (marker : StableNullifier) (created : ingress.creationMarker = some marker) :
    marker ∈ (intent accepted).nullifiers := by
  simp [intent, created]

theorem intent_writes {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress) :
    (intent accepted).writes = DeclaredResourceController.writes accepted.prepared := rfl

theorem intent_package_guard_current {config : Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : ApplicationLifecycleCompletionV2Ingress.Ingress}
    (accepted : ApplicationLifecycleCompletionV2Admission.Candidate config head ground ingress)
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

end Minidregg.Kernel.ApplicationLifecycleCompletionV2Core
