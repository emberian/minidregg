/-
Conditional current claim for an exact launch-bound BEGIN. The original v3
BEGIN is re-admitted at its prefix and matched in full; current management,
app/package policy and signed observations are checked on the same tip. A
first-create claim atomically consumes the stable first-attempt marker. This
lower module does not certify the original BEGIN's membership in Verified or
the successful prior-create completion required for `continue`.
-/
import Kernel.ApplicationLifecycleClaimV3Ingress
import Kernel.ApplicationLifecycleBeginV3Admission
import Kernel.ApplicationLifecycleClaimCore

namespace Minidregg.Kernel.ApplicationLifecycleClaimV3Core

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationLifecycleClaimV3Ingress

set_option autoImplicit false

def markersCurrent {config : Config} (opened : Opened config) (ingress : Ingress) : Bool :=
  match ingress.originalBegin.start with
  | none => true
  | some binding =>
      let attempt := firstAttemptNullifier ingress.base.domain binding
      let created := ApplicationLifecycleClaimV3Ingress.createdNullifier
        ingress.base.domain binding
      match binding.choice with
      | .create _ =>
          !opened.durable.snapshot.model.consumed attempt &&
            !opened.durable.snapshot.model.consumed created
      | .continue => opened.durable.snapshot.model.consumed created

theorem consumed_first_attempt_refuses_create {config : Config}
    (opened : Opened config) (ingress : Ingress)
    (binding : ApplicationLifecycleLaunchBinding.Binding) (index : Nat)
    (selected : ingress.originalBegin.start = some binding)
    (choice : binding.choice = .create index)
    (consumed : opened.durable.snapshot.model.consumed
      (ApplicationLifecycleClaimV3Ingress.firstAttemptNullifier
        ingress.base.domain binding) = true) :
    markersCurrent opened ingress = false := by
  simp [markersCurrent, selected, choice, consumed]

structure Conditional (config : Config) (opened : Opened config)
    (ingress : Ingress) where
  private mk ::
  sourceExact : ingress.originalExact = true
  original : NativeHistorySelection.Candidate config opened
    ingress.base.source.originalIndex
  originalAccepted : ApplicationLifecycleBeginV3Admission.Accepted
    config.deployment config.profile
    ⟨config.federation, logicalHeight config original.prior.durable⟩
    original.prior.durable ingress.originalBegin
  originalMatch : NativeHistorySelection.Matched original originalAccepted.intent
  current : ApplicationLifecycleClaimCurrent.Accepted config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩
    opened.durable ingress.base
  currentInstalled : ApplicationLifecycleBeginV3Admission.installedExact
    config.deployment ingress.originalBegin
    current.packageRead.selected.observed.before = true
  markers : markersCurrent opened ingress = true

theorem Conditional.original_record_exact {config : Config} {opened : Opened config}
    {ingress : Ingress} (conditional : Conditional config opened ingress) :
    conditional.original.record =
      DurableReceiver.IntentRecord.ofIntent conditional.originalAccepted.intent := by
  exact conditional.originalMatch.selected.symm.trans conditional.originalMatch.exact

def prepare (config : Config) (opened : Opened config) (ingress : Ingress) :
    IO (Except String (Conditional config opened ingress)) := do
  if sourceExact : ingress.originalExact = true then
    let original ← match NativeHistorySelection.select config opened
        ingress.base.source.originalIndex with
      | .error detail => return .error detail
      | .ok original => pure original
    let originalAmbient : DeclaredResourceController.Ambient :=
      ⟨config.federation, logicalHeight config original.prior.durable⟩
    let originalAccepted ← match ← ApplicationLifecycleBeginV3Admission.admitNative
        config.deployment config.profile originalAmbient config.signature
        original.prior.durable ingress.originalBegin with
      | .error detail => return .error s!"original v3 lifecycle begin refused: {detail}"
      | .ok accepted => pure accepted
    let originalMatch ← match NativeHistorySelection.matchIntent original
        originalAccepted.intent with
      | .error detail => return .error detail
      | .ok matched => pure matched
    let ambient : DeclaredResourceController.Ambient :=
      ⟨config.federation, logicalHeight config opened.durable⟩
    let current ← match ← ApplicationLifecycleClaimCurrent.admitLoaded
        config.deployment config.profile ambient config.signature opened.durable
        ingress.base with
      | .error detail => return .error detail
      | .ok current => pure current
    if installed : ApplicationLifecycleBeginV3Admission.installedExact
        config.deployment ingress.originalBegin
        current.packageRead.selected.observed.before = true then
      if markerReady : markersCurrent opened ingress = true then
        return .ok ⟨sourceExact, original, originalAccepted,
          originalMatch, current, installed, markerReady⟩
      else return .error "v3 claim first-attempt/created marker state refused"
    else return .error "current package differs from original signed launch descriptor"
  else return .error "v3 claim original BEGIN projection differs"

def Conditional.intent {config : Config} {opened : Opened config}
    {ingress : Ingress} (conditional : Conditional config opened ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  let ordinary := ApplicationLifecycleClaimCore.intentFromCurrent conditional.current
    (event ingress) ingress.canonicalBytes.length
  match ingress.createAttempt with
  | none => ordinary
  | some marker =>
      { ordinary with
        nullifiers := ordinary.nullifiers ++ [marker]
        exactCharge := fun dimension => match dimension with
          | .storageBytes => ordinary.exactCharge .storageBytes +
              marker.canonicalBytes.length
          | other => ordinary.exactCharge other }

theorem Conditional.intent_event {config : Config} {opened : Opened config}
    {ingress : Ingress} (conditional : Conditional config opened ingress) :
    conditional.intent.event = event ingress := by
  unfold Conditional.intent
  split <;> rfl

theorem Conditional.create_intent_has_attempt {config : Config} {opened : Opened config}
    {ingress : Ingress} (conditional : Conditional config opened ingress)
    (marker : StableNullifier) (selected : ingress.createAttempt = some marker) :
    marker ∈ conditional.intent.nullifiers := by
  simp [Conditional.intent, selected]

end Minidregg.Kernel.ApplicationLifecycleClaimV3Core
