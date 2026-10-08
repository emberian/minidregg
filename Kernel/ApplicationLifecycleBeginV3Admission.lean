/-
Current native admission for a launch-bound signed-SPK lifecycle BEGIN. The
existing v1 receiver supplies the full current DRC/signature/policy/package
observation checks; this layer binds the reusable v2 command descriptor and
the grain-specific volume/action choice. Verified history must additionally
check the create/continue selection before treating the intent as accepted.
-/
import Kernel.ApplicationLifecycleBeginV3Ingress
import Kernel.ApplicationLifecycleClaimV3Ingress
import Kernel.ApplicationLifecycleBeginReceiver

namespace Minidregg.Kernel.ApplicationLifecycleBeginV3Admission

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.CanonicalCellRegistry
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationLifecycleBeginV3Ingress

set_option autoImplicit false

open Minidregg.Compiler.ServedBasis (Ground)
set_option maxHeartbeats 1000000

def installedExact (deployment : CanonicalCellRegistry.Deployment)
    (ingress : Ingress) (cell : PackedCell CanonicalCellRegistry.registry) : Bool :=
  let source := ingress.base.source
  if source.kind == .start || source.kind == .stop then
    match cell with
    | ⟨.content, payload⟩ =>
        let page := payload.logical
            match ApplicationDispatchManifest.decodeInstalled deployment.domain
                source.packageManifest source.app source.before.packageVersion page with
            | none => false
            | some manifest =>
                decide (manifest = prospectiveManifest ingress) &&
                  ingress.descriptor.matchesManifest manifest
    | _ => false
  else true

/-- The nullifiers a launch binding's markers read from the spent map: the
first-attempt and created markers. A light basis must declare them. -/
def markerNullifiersOf (domain : Digest) (start : Option ApplicationLifecycleLaunchBinding.Binding) :
    List StableNullifier :=
  match start with
  | none => []
  | some binding =>
      [ApplicationLifecycleClaimV3Ingress.firstAttemptNullifier domain binding,
        ApplicationLifecycleClaimV3Ingress.createdNullifier domain binding]

def markerNullifiers (ingress : Ingress) : List StableNullifier :=
  markerNullifiersOf ingress.base.domain ingress.start

/-- Every key a v3 BEGIN reads: the base BEGIN's (transaction id and operation
marker) and its launch markers. -/
def keys (ingress : Ingress) : DurableView.Keys :=
  let base := ApplicationLifecycleBeginReceiver.keys ingress.base
  ⟨base.transactions, base.nullifiers ++ markerNullifiers ingress⟩

/-- The ground answers every marker the binding reads (an undeclared marker is
never read as unconsumed). -/
def markersDeclaredOf {deployment : CanonicalCellRegistry.Deployment} (ground : Ground deployment)
    (domain : Digest) (start : Option ApplicationLifecycleLaunchBinding.Binding) : Bool :=
  (markerNullifiersOf domain start).all ground.declaresNullifier

def markersDeclared {deployment : CanonicalCellRegistry.Deployment} (ground : Ground deployment)
    (ingress : Ingress) : Bool :=
  markersDeclaredOf ground ingress.base.domain ingress.start

/-- The current nullifier image prevents rearming a first create and excludes
continue before a completed create. Verified additionally selects the exact
successful completion certificate; marker presence is never that certificate.
A marker the ground did not declare refuses (`markersDeclaredOf`). -/
def markersCurrentOf {deployment : CanonicalCellRegistry.Deployment} (ground : Ground deployment)
    (domain : Digest) (start : Option ApplicationLifecycleLaunchBinding.Binding) : Bool :=
  markersDeclaredOf ground domain start &&
  match start with
  | none => true
  | some binding =>
      let first := ApplicationLifecycleClaimV3Ingress.firstAttemptNullifier domain binding
      let created := ApplicationLifecycleClaimV3Ingress.createdNullifier domain binding
      match binding.choice with
      | .create _ => !ground.view.model.consumed first &&
          !ground.view.model.consumed created
      | .continue => ground.view.model.consumed created

def markersCurrent {deployment : CanonicalCellRegistry.Deployment} (ground : Ground deployment)
    (ingress : Ingress) : Bool :=
  markersCurrentOf ground ingress.base.domain ingress.start

theorem consumed_first_attempt_refuses_create
    {deployment : CanonicalCellRegistry.Deployment} (ground : Ground deployment) (ingress : Ingress)
    (binding : ApplicationLifecycleLaunchBinding.Binding) (index : Nat)
    (selected : ingress.start = some binding)
    (choice : binding.choice = .create index)
    (consumed : ground.view.model.consumed
      (ApplicationLifecycleClaimV3Ingress.firstAttemptNullifier
        ingress.base.domain binding) = true) :
    markersCurrent ground ingress = false := by
  simp [markersCurrent, markersCurrentOf, selected, choice, consumed]

theorem missing_created_refuses_continue
    {deployment : CanonicalCellRegistry.Deployment} (ground : Ground deployment) (ingress : Ingress)
    (binding : ApplicationLifecycleLaunchBinding.Binding)
    (selected : ingress.start = some binding)
    (choice : binding.choice = .continue)
    (missing : ground.view.model.consumed
      (ApplicationLifecycleClaimV3Ingress.createdNullifier
        ingress.base.domain binding) = false) :
    markersCurrent ground ingress = false := by
  simp [markersCurrent, markersCurrentOf, selected, choice, missing]

/-- **An undeclared launch marker refuses** (the pole of a silent "unconsumed"). -/
theorem undeclared_marker_refuses
    {deployment : CanonicalCellRegistry.Deployment} (ground : Ground deployment) (ingress : Ingress)
    (marker : StableNullifier) (member : marker ∈ markerNullifiers ingress)
    (undeclared : ground.declaresNullifier marker = false) :
    markersCurrent ground ingress = false := by
  have : markersDeclared ground ingress = false := by
    unfold markersDeclared markersDeclaredOf
    exact List.all_eq_false.mpr ⟨marker, member, by simp [undeclared]⟩
  simp [markersCurrent, markersCurrentOf, markersDeclared] at this ⊢
  simp [this]

structure Accepted {F : Type} [Field F] [DecidableEq F]
    (deployment : CanonicalCellRegistry.Deployment)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : DeclaredResourceController.Ambient)
    (ground : Ground deployment)
    (ingress : Ingress) where
  private mk ::
  base : ApplicationLifecycleBeginReceiver.Accepted deployment profile ambient ground
    ingress.base
  descriptorBound : ingress.shape = true
  installed : installedExact deployment ingress base.selected.observed.before = true
  markers : markersCurrent ground ingress = true

/-- The admitted DRC invocation is indexed by the old command built from the
v3 source whose signed operation ID commits to the complete launch selection.
This is stronger than retaining that selection only in the special event. -/
theorem Accepted.signedInvocationBound {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {ingress : Ingress}
    (accepted : Accepted deployment profile ambient ground ingress) :
    ingress.base.source.operationId = ingress.authorizationOperationId ∧
      ∃ prepared : DeclaredResourceController.PreparedInvocation deployment profile
        ambient ground
        (ApplicationLifecycleBegin.command deployment.domain profile.semantics
          ingress.base.source),
        Nonempty (DeclaredResourceController.AcceptedInvocation prepared
          ingress.base.signed) := by
  exact ⟨shape_authorizationId ingress accepted.descriptorBound,
    accepted.base.prepared, ⟨accepted.base.invocation⟩⟩

def admitNative {F : Type} [Field F] [DecidableEq F]
    (deployment : CanonicalCellRegistry.Deployment)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : DeclaredResourceController.Ambient)
    (native : CredentialSignatureIO.NativeConfig)
    (ground : Ground deployment)
    (ingress : Ingress) : IO (Except String (Accepted deployment profile ambient ground ingress)) := do
  let .ok base ← ApplicationLifecycleBeginReceiver.admitLoaded
      deployment profile ambient native ground ingress.base
    | return .error "v3 lifecycle BEGIN base authority refused"
  if bound : ingress.shape = true then
    if installed : installedExact deployment ingress base.selected.observed.before = true then
      if _declared : markersDeclared ground ingress = true then
        if markers : markersCurrent ground ingress = true then
          return .ok ⟨base, bound, installed, markers⟩
        else return .error "v3 lifecycle BEGIN first-attempt/created marker state refused"
      else return .error "v3 lifecycle BEGIN launch marker undeclared"
    else return .error "v3 lifecycle BEGIN installed manifest differs from launch descriptor"
  else return .error "v3 lifecycle BEGIN descriptor, volume or action refused"

def Accepted.intent {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {ingress : Ingress}
    (accepted : Accepted deployment profile ambient ground ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  let legacy := accepted.base.intent
  let ordinary := accepted.base.invocation.dataIntent accepted.base.shape
  { legacy with
    exactCharge := fun dimension => match dimension with
      | .turnBytes => ingress.canonicalBytes.length
      | .witnessBytes => ingress.canonicalBytes.length
      | .storageBytes => ordinary.exactCharge .storageBytes +
          ingress.canonicalBytes.length +
          (ApplicationLifecycleBegin.stableNullifier deployment.domain
            profile.semantics ingress.base.source).canonicalBytes.length
      | other => legacy.exactCharge other
    event := event ingress }

theorem Accepted.intent_event {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {ingress : Ingress}
    (accepted : Accepted deployment profile ambient ground ingress) :
    accepted.intent.event = event ingress := rfl

theorem Accepted.intent_writes {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {ground : Ground deployment}
    {ingress : Ingress}
    (accepted : Accepted deployment profile ambient ground ingress) :
    accepted.intent.writes = accepted.base.intent.writes := rfl

end Minidregg.Kernel.ApplicationLifecycleBeginV3Admission
