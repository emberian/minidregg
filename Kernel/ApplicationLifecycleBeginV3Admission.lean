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

/-- The current nullifier image prevents rearming a first create and excludes
continue before a completed create. Verified additionally selects the exact
successful completion certificate; marker presence is never that certificate. -/
def markersCurrent (durable : DeclaredResourceController.Durable)
    (ingress : Ingress) : Bool :=
  match ingress.start with
  | none => true
  | some binding =>
      let first := ApplicationLifecycleClaimV3Ingress.firstAttemptNullifier
        ingress.base.domain binding
      let created := ApplicationLifecycleClaimV3Ingress.createdNullifier
        ingress.base.domain binding
      match binding.choice with
      | .create _ => !durable.snapshot.model.consumed first &&
          !durable.snapshot.model.consumed created
      | .continue => durable.snapshot.model.consumed created

theorem consumed_first_attempt_refuses_create
    (durable : DeclaredResourceController.Durable) (ingress : Ingress)
    (binding : ApplicationLifecycleLaunchBinding.Binding) (index : Nat)
    (selected : ingress.start = some binding)
    (choice : binding.choice = .create index)
    (consumed : durable.snapshot.model.consumed
      (ApplicationLifecycleClaimV3Ingress.firstAttemptNullifier
        ingress.base.domain binding) = true) :
    markersCurrent durable ingress = false := by
  simp [markersCurrent, selected, choice, consumed]

theorem missing_created_refuses_continue
    (durable : DeclaredResourceController.Durable) (ingress : Ingress)
    (binding : ApplicationLifecycleLaunchBinding.Binding)
    (selected : ingress.start = some binding)
    (choice : binding.choice = .continue)
    (missing : durable.snapshot.model.consumed
      (ApplicationLifecycleClaimV3Ingress.createdNullifier
        ingress.base.domain binding) = false) :
    markersCurrent durable ingress = false := by
  simp [markersCurrent, selected, choice, missing]

structure Accepted {F : Type} [Field F] [DecidableEq F]
    (deployment : CanonicalCellRegistry.Deployment)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : DeclaredResourceController.Ambient)
    (durable : DeclaredResourceController.Durable)
    (ingress : Ingress) where
  private mk ::
  base : ApplicationLifecycleBeginReceiver.Accepted deployment profile ambient durable
    ingress.base
  descriptorBound : ingress.shape = true
  installed : installedExact deployment ingress base.selected.observed.before = true
  markers : markersCurrent durable ingress = true

/-- The admitted DRC invocation is indexed by the old command built from the
v3 source whose signed operation ID commits to the complete launch selection.
This is stronger than retaining that selection only in the special event. -/
theorem Accepted.signedInvocationBound {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {durable : DeclaredResourceController.Durable}
    {ingress : Ingress}
    (accepted : Accepted deployment profile ambient durable ingress) :
    ingress.base.source.operationId = ingress.authorizationOperationId ∧
      ∃ prepared : DeclaredResourceController.PreparedInvocation deployment profile
        ambient durable
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
    (durable : DeclaredResourceController.Durable)
    (ingress : Ingress) : IO (Except String (Accepted deployment profile ambient durable ingress)) := do
  let .ok base ← ApplicationLifecycleBeginReceiver.admitLoaded
      deployment profile ambient native durable ingress.base
    | return .error "v3 lifecycle BEGIN base authority refused"
  if bound : ingress.shape = true then
    if installed : installedExact deployment ingress base.selected.observed.before = true then
      if markers : markersCurrent durable ingress = true then
        return .ok ⟨base, bound, installed, markers⟩
      else return .error "v3 lifecycle BEGIN first-attempt/created marker state refused"
    else return .error "v3 lifecycle BEGIN installed manifest differs from launch descriptor"
  else return .error "v3 lifecycle BEGIN descriptor, volume or action refused"

def Accepted.intent {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {durable : DeclaredResourceController.Durable}
    {ingress : Ingress}
    (accepted : Accepted deployment profile ambient durable ingress) :
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
    {durable : DeclaredResourceController.Durable}
    {ingress : Ingress}
    (accepted : Accepted deployment profile ambient durable ingress) :
    accepted.intent.event = event ingress := rfl

theorem Accepted.intent_writes {F : Type} [Field F] [DecidableEq F]
    {deployment : CanonicalCellRegistry.Deployment}
    {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : DeclaredResourceController.Ambient}
    {durable : DeclaredResourceController.Durable}
    {ingress : Ingress}
    (accepted : Accepted deployment profile ambient durable ingress) :
    accepted.intent.writes = accepted.base.intent.writes := rfl

end Minidregg.Kernel.ApplicationLifecycleBeginV3Admission
