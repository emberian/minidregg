/-
Fresh signed-SPK lifecycle BEGIN admission. The existing v1 receiver supplies
the current DRC, policy, package observation, and physical-guard checks on one
image; this layer additionally requires a full descriptor preimage and its
source-derived prospective Manifest. V1 remains a historical replay grammar.
-/
import Kernel.ApplicationLifecycleBeginV2Ingress
import Kernel.ApplicationLifecycleBeginReceiver

namespace Minidregg.Kernel.ApplicationLifecycleBeginV2Admission

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.CanonicalCellRegistry
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationLifecycleBeginV2Ingress

set_option autoImplicit false

open Minidregg.Compiler.ServedBasis (Ground)
set_option maxHeartbeats 1000000

/-- Start/stop must see the exact already installed manifest in the same
signed, read-guarded package cell. Install/upgrade bind a prospective manifest
for a later checked completion; they do not assert it is installed already. -/
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

/-- The keys a v2 BEGIN reads: its base BEGIN's. -/
def keys (ingress : Ingress) : DurableView.Keys :=
  ApplicationLifecycleBeginReceiver.keys ingress.base

structure Accepted {F : Type} [Field F] [DecidableEq F]
    (deployment : CanonicalCellRegistry.Deployment)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : DeclaredResourceController.Ambient)
    (ground : Ground deployment)
    (ingress : Ingress) where
  private mk ::
  base : ApplicationLifecycleBeginReceiver.Accepted deployment profile ambient ground
    ingress.base
  descriptorBound : ApplicationLifecycleBeginV2Ingress.descriptorBound ingress = true
  installed : installedExact deployment ingress base.selected.observed.before = true

def admitNative {F : Type} [Field F] [DecidableEq F]
    (deployment : CanonicalCellRegistry.Deployment)
    (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : DeclaredResourceController.Ambient)
    (native : CredentialSignatureIO.NativeConfig)
    (ground : Ground deployment)
    (ingress : Ingress) : IO (Except String (Accepted deployment profile ambient ground ingress)) := do
  let .ok base ← ApplicationLifecycleBeginReceiver.admitLoaded
      deployment profile ambient native ground ingress.base
    | return .error "v2 lifecycle BEGIN base authority refused"
  if bound : ApplicationLifecycleBeginV2Ingress.descriptorBound ingress = true then
    if installed : installedExact deployment ingress base.selected.observed.before = true then
      return .ok ⟨base, bound, installed⟩
    else return .error "v2 lifecycle BEGIN installed manifest differs from signed SPK descriptor"
  else return .error "v2 lifecycle BEGIN descriptor or prospective manifest refused"

/-- Preserve the admitted writes, guards and nullifiers. Only the new full
canonical event and the source-byte-dependent charge replace the v1 wrapper;
ordinary DRC post-write bytes and the stable BEGIN nullifier are unchanged. -/
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

end Minidregg.Kernel.ApplicationLifecycleBeginV2Admission
