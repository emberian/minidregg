/-
Conditional v2 lifecycle claim admission. The original descriptor-bearing
BEGIN is re-admitted at its exact stored prefix and compared to the complete
record. Today's management, mutation, package and app observations are checked
on one current image. This module emits no CAS or physical launch permit;
Replay must additionally prove the original step belonged to admitted history.
-/
import Kernel.ApplicationLifecycleClaimV2Ingress
import Kernel.ApplicationLifecycleBeginV2Admission
import Kernel.ApplicationLifecycleClaimCore

namespace Minidregg.Kernel.ApplicationLifecycleClaimV2Core

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationLifecycleClaimV2Ingress

set_option autoImplicit false

structure Conditional (config : Config) (opened : Opened config)
    (ingress : Ingress) where
  private mk ::
  sourceExact : ingress.originalExact = true
  original : NativeHistorySelection.Candidate config opened
    ingress.base.source.originalIndex
  originalAccepted : ApplicationLifecycleBeginV2Admission.Accepted
    config.deployment config.profile
    ⟨config.federation, logicalHeight config original.prior.durable⟩
    original.prior.durable ingress.originalBegin
  originalMatch : NativeHistorySelection.Matched original originalAccepted.intent
  current : ApplicationLifecycleClaimCurrent.Accepted config.deployment config.profile
    ⟨config.federation, logicalHeight config opened.durable⟩
    opened.durable ingress.base
  currentInstalled : ApplicationLifecycleBeginV2Admission.installedExact
    config.deployment ingress.originalBegin
    current.packageRead.selected.observed.before = true

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
    let originalAccepted ← match ← ApplicationLifecycleBeginV2Admission.admitNative
        config.deployment config.profile originalAmbient config.signature
        original.prior.durable ingress.originalBegin with
      | .error detail => return .error s!"original v2 lifecycle begin refused: {detail}"
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
    if installed : ApplicationLifecycleBeginV2Admission.installedExact
        config.deployment ingress.originalBegin
        current.packageRead.selected.observed.before = true then
      return .ok ⟨sourceExact, original, originalAccepted,
        originalMatch, current, installed⟩
    else return .error "current package differs from original signed SPK descriptor"
  else return .error "v2 claim original BEGIN projection differs"

def Conditional.intent {config : Config} {opened : Opened config}
    {ingress : Ingress} (conditional : Conditional config opened ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  ApplicationLifecycleClaimCore.intentFromCurrent conditional.current
    (event ingress) ingress.canonicalBytes.length

theorem Conditional.intent_event {config : Config} {opened : Opened config}
    {ingress : Ingress} (conditional : Conditional config opened ingress) :
    conditional.intent.event = event ingress := rfl

end Minidregg.Kernel.ApplicationLifecycleClaimV2Core
