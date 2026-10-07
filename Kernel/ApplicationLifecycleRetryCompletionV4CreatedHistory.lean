/-
Conditional selection of one successful retried repeat-create completion (event72)
at its exact original prefix; the v4 twin of ApplicationLifecycleCreatedHistory. This source-level reconstruction alone is not a launch
permit: Replay must match the full record to its own chronological admitted
certificate before a later continue BEGIN or claim can consume it.
-/
import Kernel.ApplicationLifecycleRetryCompletionV4Core
import Kernel.NativeHistorySelection

namespace Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4CreatedHistory

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (Reader)

structure Candidate (config : Config) {store : StoreIdentity} (head : Head store)
    (binding : ApplicationLifecycleLaunchBinding.Binding) where
  private mk ::
  receipt : NativeHostCodec.Receipt
  custody : ApplicationLifecycleLaunchBinding.Custody
  priorExact : binding.priorCreate = some (receipt, custody)
  index : Nat
  indexExact : index + 1 = receipt.acceptedCount
  selected : NativeHistorySelection.Candidate config head index
  after : NativeHistorySelection.After config head index
  ingress : ApplicationLifecycleRetryCompletionV4Ingress.Ingress
  ingressExact : selected.record.event.canonicalBytes = ingress.canonicalBytes
  accepted : ApplicationLifecycleRetryCompletionV4Admission.Candidate config head selected.ground ingress
  recordExact : selected.record =
    DurableReceiver.IntentRecord.ofIntent (ApplicationLifecycleRetryCompletionV4Core.intent accepted)
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
  receiptBoundary : after.opened.served.worldRoot = receipt.worldRoot

/-- Creation may have used an older package version. The reusable certificate
joins app identity, the permanent volume ID, exact signed custody and original
receipt; a later BEGIN independently authorizes its current package root. -/
theorem Candidate.same_volume_lineage {config : Config} {store : StoreIdentity} {head : Head store}
    {binding : ApplicationLifecycleLaunchBinding.Binding}
    (candidate : Candidate config head binding) :
    candidate.ingress.source.app = binding.app ∧
    candidate.ingress.source.originalBegin.volume = binding.volume ∧
    candidate.ingress.source.physical.report.volumeCustody = some candidate.custody :=
  ⟨candidate.appExact, candidate.volumeExact, candidate.custodyExact⟩

theorem Candidate.record_contains_created_marker
    {config : Config} {store : StoreIdentity} {head : Head store}
    {binding : ApplicationLifecycleLaunchBinding.Binding}
    (candidate : Candidate config head binding) :
    ∃ marker : StableNullifier,
      candidate.ingress.creationMarker = some marker ∧
      marker ∈ candidate.selected.record.nullifiers := by
  have created := candidate.created
  cases selected : candidate.ingress.creationMarker with
  | none => simp [selected] at created
  | some marker =>
      refine ⟨marker, rfl, ?_⟩
      rw [candidate.recordExact]
      exact ApplicationLifecycleRetryCompletionV4Core.intent_has_created_marker
        candidate.accepted marker (by simp [selected])

private def decodeSelected (bytes : List UInt8) : Except String
    { ingress : ApplicationLifecycleRetryCompletionV4Ingress.Ingress //
      ApplicationLifecycleRetryCompletionV4Ingress.codec.decode bytes = some ingress } :=
  match _decoded : ApplicationLifecycleRetryCompletionV4Ingress.codec.decode bytes with
  | none => .error "selected creation completion is noncanonical"
  | some ingress => .ok ⟨ingress, rfl⟩

/-- The lower reader does not infer a created volume from a nullifier alone. It
rechecks the original source, custodian signature, full intent and the exact
claimed receipt against the selected prefix. A Verified join is still needed. -/
def select (config : Config) {store : StoreIdentity}
    (reader : Reader ResourceBirthCodec.rootBytes store) (bound : Nat)
    (binding : ApplicationLifecycleLaunchBinding.Binding) :
    IO (Except String (Candidate config reader.head binding)) := do
  match priorExact : binding.priorCreate with
  | none => return .error "continue has no original completed-create receipt"
  | some (receipt, custody) =>
    if count : 0 < receipt.acceptedCount then
      let index := receipt.acceptedCount - 1
      have indexExact : index + 1 = receipt.acceptedCount := by omega
      -- The completion's keys depend on the record's event: read it (verified) first.
      let probe ← match ← reader.atHeight (index + 1) with
        | .error refusal => return .error refusal.message
        | .ok read => pure read.record
      let probeKeys : DurableView.Keys :=
        match decodeSelected probe.event.canonicalBytes with
        | .error _ => ⟨[], []⟩
        | .ok decoded => ApplicationLifecycleRetryCompletionV4Admission.keys config decoded.val
      let selected ← match ← NativeHistorySelection.select config reader bound index probeKeys with
        | .error detail => return .error detail
        | .ok selected => pure selected
      let after ← match ← NativeHistorySelection.selectAfter config reader index with
        | .error _ => return .error "selected completed-create post-prefix unavailable or invalid"
        | .ok after => pure after
      let ingressSelected ← match decodeSelected selected.record.event.canonicalBytes with
        | .error detail => return .error detail
        | .ok selected => pure selected
      let ingress := ingressSelected.val
      have ingressExact : selected.record.event.canonicalBytes = ingress.canonicalBytes :=
        (ApplicationLifecycleRetryCompletionV4Ingress.decoded_canonical
          ingressSelected.property).symm
      let accepted ← match ← ApplicationLifecycleRetryCompletionV4Admission.prepareConditional
          config reader selected.grounded ingress with
        | .error detail => return .error s!"original create completion refused: {detail}"
        | .ok accepted => pure accepted
      if matched : NativeHistorySelection.recordMatches selected.record
          (ApplicationLifecycleRetryCompletionV4Core.intent accepted) = true then
        have recordExact : selected.record = DurableReceiver.IntentRecord.ofIntent
            (ApplicationLifecycleRetryCompletionV4Core.intent accepted) :=
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
                      if boundary : after.opened.served.worldRoot =
                          receipt.worldRoot then
                        return .ok ⟨receipt, custody, priorExact, index, indexExact,
                          selected, after, ingress, ingressExact,
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
    else return .error "completed-create receipt has zero accepted count"

end Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4CreatedHistory
