/-
Conditional preparation of one current one-shot lifecycle claim. Historical
BEGIN admission is re-derived on the prior state read from the authenticated
history and compared to the full selected stored intent. Current app, package,
mutation and management authority are checked on the current ground. This module emits a DataIntent
but never commits it or grants a host launch; a verified-history adapter must
bind this conditional result to NativeHostReplay.Verified first.
-/
import Kernel.ApplicationLifecycleClaimCurrent

namespace Minidregg.Kernel.ApplicationLifecycleClaimCore

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ApplicationLifecycleClaim
open Minidregg.Kernel.ApplicationLifecycleClaimIngress

set_option autoImplicit false

open Minidregg.Compiler.ServedBasis (Ground Grounded)
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (Reader)

structure Conditional (config : NativeHost.Config) {store : StoreIdentity} (head : Head store)
    (ground : Ground config.deployment) (ingress : Ingress) where
  private mk ::
  original : ApplicationLifecycleClaimHistory.Conditional config head ingress.source
  current : ApplicationLifecycleClaimCurrent.Accepted config.deployment config.profile
    ⟨config.federation, config.genesisHeight + ground.height⟩
    ground ingress

/-- `current` is the ground the claim is checked on (the light basis or, for the
audit walk, the full shape); `reader` supplies the original BEGIN's record and
prefix state. -/
def prepare (config : NativeHost.Config) {store : StoreIdentity}
    (reader : Reader ResourceBirthCodec.rootBytes store)
    (grounded : Grounded config.deployment reader.head)
    (ingress : Ingress) : IO (Except String (Conditional config reader.head grounded.ground ingress)) := do
  let ground := grounded.ground
  let original ← match ← ApplicationLifecycleClaimHistory.admit config reader ground.height ingress.source with
    | .error detail => return .error detail
    | .ok original => pure original
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, config.genesisHeight + ground.height⟩
  match ← ApplicationLifecycleClaimCurrent.admitLoaded config.deployment config.profile
      ambient config.signature ground ingress with
  | .error detail => return .error detail
  | .ok current => return .ok ⟨original, current⟩

/-- Every key the current part of a claim reads. -/
def keys (ingress : Ingress) : DurableView.Keys :=
  ApplicationLifecycleClaimCurrent.keys ingress

def packageGuard (source : Source)
    (before : PackedCell CanonicalCellRegistry.registry) : ReadGuard :=
  ApplicationLifecycleClaimCurrent.observationGuard
    source.begin.source.packageManifest before

/-- The app's old root is already guarded by the DRC target write. Only the
independent package observation contributes a new read-only guard. Both native
observation signatures are separately checked by `current`. The event and
canonical byte count come from an admitted versioned outer ingress. -/
def intentFromCurrent {config : NativeHost.Config} {ground : Ground config.deployment}
    {ingress : Ingress}
    (current : ApplicationLifecycleClaimCurrent.Accepted config.deployment config.profile
      ⟨config.federation, config.genesisHeight + ground.height⟩
      ground ingress)
    (wireEvent : StableEvent) (wireBytes : Nat) :
    DataIntent rootBytes := by
  let ordinary := current.invocation.dataIntent current.shape
  have guarded : ∀ guard ∈ ordinary.readGuards ++
      [packageGuard ingress.source current.packageRead.selected.observed.before],
      guard.cellId ∉ ordinary.writes.map DataWrite.cellId := by
    intro guard member
    rcases List.mem_append.mp member with old | extra
    · exact ordinary.guardsReadOnly guard old
    · simp only [List.mem_singleton] at extra
      subst guard
      exact current.packageReadOnly
  exact
    { transactionId := ordinary.transactionId
      writes := ordinary.writes
      readGuards := ordinary.readGuards ++
        [packageGuard ingress.source current.packageRead.selected.observed.before]
      nullifiers := ordinary.nullifiers ++
        [stableNullifier config.deployment.domain config.profile.semantics ingress.source]
      exactCharge := fun dimension => match dimension with
        | .incidences => ordinary.exactCharge .incidences + 2
        | .turnBytes => wireBytes
        | .witnessBytes => wireBytes
        | .proofWork => ordinary.exactCharge .proofWork + 2
        | .memoryTouches => ordinary.exactCharge .memoryTouches + 2
        | .storageBytes => ordinary.exactCharge .storageBytes +
            wireBytes +
            (stableNullifier config.deployment.domain config.profile.semantics
              ingress.source).canonicalBytes.length
        | other => ordinary.exactCharge other
      event := wireEvent
      subject := ordinary.subject
      postRootsBound := ordinary.postRootsBound
      guardsReadOnly := guarded }

def Conditional.intent {config : NativeHost.Config} {store : StoreIdentity} {head : Head store}
    {ground : Ground config.deployment} {ingress : Ingress}
    (conditional : Conditional config head ground ingress) :
    DataIntent rootBytes :=
  intentFromCurrent conditional.current (event ingress) ingress.canonicalBytes.length

theorem Conditional.intent_event {config : NativeHost.Config} {store : StoreIdentity} {head : Head store} {ground : Ground config.deployment}
    {ingress : Ingress} (conditional : Conditional config head ground ingress) :
    conditional.intent.event = event ingress := rfl

theorem Conditional.intent_writes {config : NativeHost.Config} {store : StoreIdentity} {head : Head store}
    {ground : Ground config.deployment} {ingress : Ingress}
    (conditional : Conditional config head ground ingress) :
    conditional.intent.writes =
      (conditional.current.invocation.dataIntent conditional.current.shape).writes := rfl

theorem Conditional.intent_package_guard {config : NativeHost.Config} {store : StoreIdentity} {head : Head store}
    {ground : Ground config.deployment} {ingress : Ingress}
    (conditional : Conditional config head ground ingress) :
    packageGuard ingress.source conditional.current.packageRead.selected.observed.before ∈
      conditional.intent.readGuards ∧
      (packageGuard ingress.source conditional.current.packageRead.selected.observed.before).expectedRoot =
        ground.view.model.roots
          (packageGuard ingress.source conditional.current.packageRead.selected.observed.before).cellId := by
  constructor
  · change packageGuard ingress.source conditional.current.packageRead.selected.observed.before ∈
      (conditional.current.invocation.dataIntent conditional.current.shape).readGuards ++
        [packageGuard ingress.source conditional.current.packageRead.selected.observed.before]
    simp
  · exact conditional.current.packageRead.current

end Minidregg.Kernel.ApplicationLifecycleClaimCore
