/-
Conditional failed-create retry evidence. This is not a launch permit: native
replay must additionally bind the original claim to its admitted chronological
walk, and the new BEGIN/CLAIM must check current management authority. The
retained report certifies a dead incarnation, never absence of past effects.
-/
import Kernel.ApplicationFailedStartRecoveryCore

namespace Minidregg.Kernel.ApplicationFailedCreateRetryEvidence

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Selector where
  recoveryIndex : Nat
  recovery : ApplicationFailedStartRecoveryIngress.Ingress
  deriving DecidableEq

def selectorStream : StreamCodec Selector :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      ApplicationFailedStartRecoveryIngress.ingressStream)
    (fun selector => (selector.recoveryIndex, selector.recovery))
    (fun (index, recovery) => ⟨index, recovery⟩)
    (by intro selector; cases selector; rfl)

def selectorCodec : LawfulCodec Selector := NativeHostCodec.framed
  "DREGG/APPLICATION/FAILED-CREATE-RETRY-SELECTOR/v1".toUTF8.toList
  selectorStream

def Selector.canonicalBytes (selector : Selector) : List UInt8 :=
  selectorCodec.encode selector

/-- The exact accepted recovery identifies one retry token. A different
manager signature cannot rearm that same recovery. This token is consumed
only by the new CLAIM, and never replaces the original first-attempt marker.
The codecVersion is the existing recovery-nullifier family; its new frame and
digest customization distinguish it from reconciliation's own marker. -/
def retryToken (selector : Selector) : StableNullifier where
  codecVersion := 66
  domain := selector.recovery.domain
  nullifierId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/FAILED-CREATE-RETRY-TOKEN-ID/v1".toUTF8.toList
    selector.canonicalBytes).digest
  canonicalBytes :=
    "DREGG/APPLICATION/FAILED-CREATE-RETRY-TOKEN-BYTES/v1".toUTF8.toList ++
      selector.canonicalBytes

def bindingMatches (selector : Selector)
    (begin : ApplicationLifecycleBeginV3Ingress.Ingress) : Bool :=
  let original := selector.recovery.source.originalBegin
  let recovered := selector.recovery.source.operation.after
    selector.recovery.source.claimedState
  decide (begin.base.domain = selector.recovery.domain ∧
    begin.base.semantics = selector.recovery.semantics ∧
    begin.base.source.kind = .start ∧
    begin.base.source.app = original.base.source.app ∧
    begin.base.source.before = recovered ∧
    begin.base.source.packageManifest = original.base.source.packageManifest ∧
    begin.base.source.snapshotManifest = original.base.source.snapshotManifest ∧
    begin.descriptor = original.descriptor ∧ begin.volume = original.volume) &&
  match original.start, begin.start with
  | some old, some next =>
      match old.choice, next.choice with
      | .create oldIndex, .create nextIndex =>
          decide (old.app = next.app ∧ old.volume = next.volume ∧
            old.packageRoot = next.packageRoot ∧ oldIndex = nextIndex ∧
            old.commandDigest = next.commandDigest ∧ next.priorCreate = none)
      | _, _ => false
  | _, _ => false

def markersCurrent (config : Config) (opened : Opened config)
    (selector : Selector) : Bool :=
  match selector.recovery.source.originalBegin.start with
  | none => false
  | some binding =>
      opened.durable.snapshot.model.consumed
          (ApplicationLifecycleClaimV3Ingress.firstAttemptNullifier
            config.deployment.domain binding) &&
        !opened.durable.snapshot.model.consumed
          (ApplicationLifecycleClaimV3Ingress.createdNullifier
            config.deployment.domain binding) &&
        opened.durable.snapshot.model.consumed
          (ApplicationFailedStartRecoveryIngress.stableNullifier selector.recovery) &&
        !opened.durable.snapshot.model.consumed (retryToken selector)

/-- A protected, fully re-admitted recovery intent at its selected physical
prefix. This lower value retains no permission to commit a retry. The upper
chronological gate must match its original claim to the same Verified walk.
Current BEGIN admission independently checks the exact stopped state and
package bound by bindingMatches against signed current resource reads. -/
structure Conditional (config : Config) (opened : Opened config)
    (selector : Selector) (begin : ApplicationLifecycleBeginV3Ingress.Ingress) where
  private mk ::
  selected : NativeHistorySelection.Candidate config opened selector.recoveryIndex
  recovered : ApplicationFailedStartRecoveryAdmission.Candidate config
    selected.prior selector.recovery
  matched : NativeHistorySelection.Matched selected
    (ApplicationFailedStartRecoveryCore.intent recovered)
  bindingExact : bindingMatches selector begin = true
  markersExact : markersCurrent config opened selector = true

def prepare (config : Config) (opened : Opened config) (selector : Selector)
    (begin : ApplicationLifecycleBeginV3Ingress.Ingress) :
    IO (Except String (Conditional config opened selector begin)) := do
  let selected ← match NativeHistorySelection.select config opened selector.recoveryIndex with
    | .error detail => return .error detail
    | .ok selected => pure selected
  let recovered ← match ← ApplicationFailedStartRecoveryAdmission.prepareConditional
      config selected.prior selector.recovery with
    | .error detail => return .error s!"failed-create retry recovery refused: {detail}"
    | .ok admitted => pure admitted
  let matched ← match NativeHistorySelection.matchIntent selected
      (ApplicationFailedStartRecoveryCore.intent recovered) with
    | .error detail => return .error detail
    | .ok matched => pure matched
  if bound : bindingMatches selector begin = true then
    if markers : markersCurrent config opened selector = true then
      return .ok ⟨selected, recovered, matched, bound, markers⟩
    else return .error "failed-create retry original/recovery/created/token markers refuse"
  else return .error "failed-create retry differs from recovered state/app/volume/create/package"

theorem selector_decode_encode (selector : Selector) :
    selectorCodec.decode selector.canonicalBytes = some selector :=
  selectorCodec.decode_encode selector

theorem consumed_retry_refuses (config : Config) (opened : Opened config)
    (selector : Selector)
    (consumed : opened.durable.snapshot.model.consumed (retryToken selector) = true) :
    markersCurrent config opened selector = false := by
  unfold markersCurrent
  split
  · rfl
  · simp [consumed]

theorem bindingMatches_before (selector : Selector)
    (begin : ApplicationLifecycleBeginV3Ingress.Ingress)
    (matched : bindingMatches selector begin = true) :
    begin.base.source.before = selector.recovery.source.operation.after
      selector.recovery.source.claimedState := by
  simp only [bindingMatches, Bool.and_eq_true, decide_eq_true_eq] at matched
  exact matched.1.2.2.2.2.1

theorem bindingMatches_descriptor (selector : Selector)
    (begin : ApplicationLifecycleBeginV3Ingress.Ingress)
    (matched : bindingMatches selector begin = true) :
    begin.descriptor = selector.recovery.source.originalBegin.descriptor := by
  simp only [bindingMatches, Bool.and_eq_true, decide_eq_true_eq] at matched
  exact matched.1.2.2.2.2.2.2.2.1

theorem bindingMatches_stopped_generation (selector : Selector)
    (begin : ApplicationLifecycleBeginV3Ingress.Ingress)
    (matched : bindingMatches selector begin = true) :
    begin.base.source.before.phase = 2 ∧
      begin.base.source.before.generation = selector.recovery.source.claimedState.generation + 1 := by
  rw [bindingMatches_before selector begin matched]
  exact ⟨rfl, rfl⟩

theorem Conditional.recovery_record_exact {config : Config} {opened : Opened config}
    {selector : Selector} {begin : ApplicationLifecycleBeginV3Ingress.Ingress}
    (accepted : Conditional config opened selector begin) :
    accepted.selected.record = DurableReceiver.IntentRecord.ofIntent
      (ApplicationFailedStartRecoveryCore.intent accepted.recovered) :=
  accepted.matched.selected.symm.trans accepted.matched.exact

end Minidregg.Kernel.ApplicationFailedCreateRetryEvidence
