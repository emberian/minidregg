/-
The checked completion's source-owned durable intent. Admission above this
module binds the physical custodian, exact historical claim, current law,
signed package observation, and all incidences on one old image. This module
does not submit a CAS or authorize a physical launch.
-/
import Kernel.ApplicationLifecycleCompletionAdmission

namespace Minidregg.Kernel.ApplicationLifecycleCompletionCore

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

def packageGuard {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress) :
    ReadGuard :=
  ApplicationLifecycleClaimCurrent.observationGuard
    ingress.source.originalBegin.base.source.packageManifest accepted.packageCell

def extraGuards {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress) :
    List ReadGuard :=
  if ingress.source.needsPackageWrite then [] else [packageGuard accepted]

theorem extraGuards_readonly {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress)
    (guard : ReadGuard) (member : guard ∈ extraGuards accepted) :
    guard.cellId ∉ (DeclaredResourceController.writes accepted.prepared).map DataWrite.cellId := by
  unfold extraGuards at member
  split at member
  · simp at member
  · simp only [List.mem_singleton] at member
    subst guard
    exact accepted.packageGuardReadOnly (by simp_all)

theorem extraGuards_current {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress)
    (guard : ReadGuard) (member : guard ∈ extraGuards accepted) :
    guard.expectedRoot = opened.durable.snapshot.model.roots guard.cellId := by
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
def charge {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress) :
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
        (ApplicationLifecycleCompletionIngress.stableNullifier ingress).canonicalBytes.length
    | other => base other

def intent {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress) :
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
        ApplicationLifecycleCompletionIngress.stableNullifier ingress]
      exactCharge := charge accepted
      event := ApplicationLifecycleCompletionIngress.event ingress
      postRootsBound := DeclaredResourceController.writes_roots_bound accepted.prepared
      guardsReadOnly := guarded }

theorem intent_event {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress) :
    (intent accepted).event = ApplicationLifecycleCompletionIngress.event ingress := rfl

theorem intent_event_version {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress) :
    (intent accepted).event.codecVersion = 18 := rfl

theorem intent_has_report_nullifier {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress) :
    ApplicationLifecycleCompletionIngress.stableNullifier ingress ∈
      (intent accepted).nullifiers := by
  simp [intent]

theorem intent_writes {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress) :
    (intent accepted).writes = DeclaredResourceController.writes accepted.prepared := rfl

theorem intent_package_guard_current {config : Config} {opened : Opened config}
    {ingress : ApplicationLifecycleCompletionIngress.Ingress}
    (accepted : ApplicationLifecycleCompletionAdmission.Candidate config opened ingress)
    (readOnly : ingress.source.needsPackageWrite = false) :
    packageGuard accepted ∈ (intent accepted).readGuards ∧
      (packageGuard accepted).expectedRoot =
        opened.durable.snapshot.model.roots (packageGuard accepted).cellId := by
  constructor
  · change packageGuard accepted ∈
      DeclaredResourceController.readGuards accepted.prepared ++ extraGuards accepted
    apply List.mem_append_right
    simp [extraGuards, readOnly]
  · exact accepted.packageRead.physicalCurrent

end Minidregg.Kernel.ApplicationLifecycleCompletionCore
