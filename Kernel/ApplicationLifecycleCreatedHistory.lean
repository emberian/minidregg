/-
Conditional selection of one successful first-create completion at its exact
original prefix. This source-level reconstruction alone is not a launch
permit: Replay must match the full record to its own chronological admitted
certificate before a later continue BEGIN or claim can consume it.
-/
import Kernel.ApplicationLifecycleCompletionV2Core
import Kernel.NativeHistorySelection

namespace Minidregg.Kernel.ApplicationLifecycleCreatedHistory

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

structure Candidate (config : Config) (opened : Opened config)
    (binding : ApplicationLifecycleLaunchBinding.Binding) where
  private mk ::
  receipt : NativeHostCodec.Receipt
  custody : ApplicationLifecycleLaunchBinding.Custody
  priorExact : binding.priorCreate = some (receipt, custody)
  index : Nat
  indexExact : index + 1 = receipt.acceptedCount
  selected : NativeHistorySelection.Candidate config opened index
  after : Opened config
  afterImage : after.durable.image = NativeHistorySelection.prefixImage opened (index + 1)
  ingress : ApplicationLifecycleCompletionV2Ingress.Ingress
  ingressExact : selected.record.event.canonicalBytes = ingress.canonicalBytes
  accepted : ApplicationLifecycleCompletionV2Admission.Candidate config selected.prior ingress
  recordExact : selected.record =
    DurableReceiver.IntentRecord.ofIntent (ApplicationLifecycleCompletionV2Core.intent accepted)
  created : ingress.creationMarker.isSome = true
  sourceChoice :
    (match ingress.source.originalBegin.start.map (·.choice) with
     | some (.create _) => true
     | _ => false) = true
  appExact : ingress.source.app = binding.app
  volumeExact : ingress.source.originalBegin.volume = binding.volume
  custodyExact : ingress.source.physical.report.volumeCustody = some custody
  receiptTransaction : selected.record.transactionId = receipt.transactionId
  receiptEvent : selected.record.event.eventId = receipt.eventId
  receiptBoundary : after.durable.worldRoot = receipt.worldRoot

/-- Creation may have used an older package version. The reusable certificate
joins app identity, the permanent volume ID, exact signed custody and original
receipt; a later BEGIN independently authorizes its current package root. -/
theorem Candidate.same_volume_lineage {config : Config} {opened : Opened config}
    {binding : ApplicationLifecycleLaunchBinding.Binding}
    (candidate : Candidate config opened binding) :
    candidate.ingress.source.app = binding.app ∧
    candidate.ingress.source.originalBegin.volume = binding.volume ∧
    candidate.ingress.source.physical.report.volumeCustody = some candidate.custody :=
  ⟨candidate.appExact, candidate.volumeExact, candidate.custodyExact⟩

theorem Candidate.record_contains_created_marker
    {config : Config} {opened : Opened config}
    {binding : ApplicationLifecycleLaunchBinding.Binding}
    (candidate : Candidate config opened binding) :
    ∃ marker : StableNullifier,
      candidate.ingress.creationMarker = some marker ∧
      marker ∈ candidate.selected.record.nullifiers := by
  have created := candidate.created
  cases selected : candidate.ingress.creationMarker with
  | none => simp [selected] at created
  | some marker =>
      refine ⟨marker, rfl, ?_⟩
      rw [candidate.recordExact]
      exact ApplicationLifecycleCompletionV2Core.intent_has_created_marker
        candidate.accepted marker (by simp [selected])

private def decodeSelected (bytes : List UInt8) : Except String
    { ingress : ApplicationLifecycleCompletionV2Ingress.Ingress //
      ApplicationLifecycleCompletionV2Ingress.codec.decode bytes = some ingress } :=
  match _decoded : ApplicationLifecycleCompletionV2Ingress.codec.decode bytes with
  | none => .error "selected creation completion is noncanonical"
  | some ingress => .ok ⟨ingress, rfl⟩

/-- The lower reader does not infer a created volume from a nullifier alone. It
rechecks the original source, custodian signature, full intent and the exact
claimed receipt against the selected prefix. A Verified join is still needed. -/
def select (config : Config) (opened : Opened config)
    (binding : ApplicationLifecycleLaunchBinding.Binding) :
    IO (Except String (Candidate config opened binding)) := do
  match priorExact : binding.priorCreate with
  | none => return .error "continue has no original completed-create receipt"
  | some (receipt, custody) =>
    if count : 0 < receipt.acceptedCount then
      let index := receipt.acceptedCount - 1
      have indexExact : index + 1 = receipt.acceptedCount := by omega
      let selected ← match ← NativeHistorySelection.selectIO config opened index with
        | .error detail => return .error detail
        | .ok selected => pure selected
      let prefixAfter := NativeHistorySelection.prefixImage opened (index + 1)
      let loaded ← match ← NativeHistorySelection.loadPrefix opened.durable.logStart prefixAfter with
        | .error _ => return .error "selected completed-create post-prefix unavailable"
        | .ok loaded => pure loaded.val
      let after ← match validateLoaded config loaded with
        | .error _ => return .error "selected completed-create post-prefix invalid"
        | .ok after => pure after
      if afterImage : after.durable.image = prefixAfter then
        let ingressSelected ← match decodeSelected selected.record.event.canonicalBytes with
          | .error detail => return .error detail
          | .ok selected => pure selected
        let ingress := ingressSelected.val
        have ingressExact : selected.record.event.canonicalBytes = ingress.canonicalBytes :=
          (ApplicationLifecycleCompletionV2Ingress.decoded_canonical
            ingressSelected.property).symm
        let accepted ← match ← ApplicationLifecycleCompletionV2Admission.prepareConditional
            config selected.prior ingress with
          | .error detail => return .error s!"original create completion refused: {detail}"
          | .ok accepted => pure accepted
        if matched : NativeHistorySelection.recordMatches selected.record
            (ApplicationLifecycleCompletionV2Core.intent accepted) = true then
          have recordExact : selected.record = DurableReceiver.IntentRecord.ofIntent
              (ApplicationLifecycleCompletionV2Core.intent accepted) :=
            (NativeHistorySelection.recordMatches_iff _ _).mp matched
          if created : ingress.creationMarker.isSome = true then
            if choice : (match ingress.source.originalBegin.start.map (·.choice) with
                | some (.create _) => true
                | _ => false) = true then
              if appExact : ingress.source.app = binding.app then
                if volumeExact : ingress.source.originalBegin.volume = binding.volume then
                  if custodyExact : ingress.source.physical.report.volumeCustody = some custody then
                    if transaction : selected.record.transactionId = receipt.transactionId then
                      if event : selected.record.event.eventId = receipt.eventId then
                        if boundary : after.durable.worldRoot =
                            receipt.worldRoot then
                          return .ok ⟨receipt, custody, priorExact, index, indexExact,
                            selected, after, afterImage, ingress, ingressExact,
                            accepted, recordExact, created, choice, appExact,
                            volumeExact, custodyExact, transaction, event, boundary⟩
                        else return .error "completed-create post-image boundary differs"
                      else return .error "completed-create event differs from receipt"
                    else return .error "completed-create transaction differs from receipt"
                  else return .error "completed-create custody differs"
                else return .error "completed-create volume differs"
              else return .error "completed-create app differs"
            else return .error "selected completion was not a create action"
          else return .error "selected completion did not create a volume"
        else return .error "selected completion full intent differs"
      else return .error "selected completed-create post-prefix image changed"
    else return .error "completed-create receipt has zero accepted count"

end Minidregg.Kernel.ApplicationLifecycleCreatedHistory
