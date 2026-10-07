/-
Conditional source check of one original launch-bound claim at its exact
prefix. Replay must compare this to its chronological retry claim gate; the live
receiver must obtain that comparison from Verified. A structural prefix is
not, by itself, a completion permit.
-/
import Kernel.ApplicationLifecycleRetryCompletionV4Source
import Kernel.NativeHistorySelection
import Kernel.ApplicationLifecycleRetryClaimV4Core

namespace Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4History

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (Reader)

def projection {config : Config} {store : StoreIdentity} {head : Head store} {index : Nat}
    (candidate : NativeHistorySelection.Candidate config head index)
    (after : NativeHistorySelection.After config head index)
    (source : ApplicationLifecycleRetryCompletionV4Source.Source)
    (accepted : ApplicationLifecycleRetryClaimV4Core.Conditional
      config head candidate.ground source.originalClaim) :
    ApplicationLifecycleRetryClaimV4Projection.Committed :=
  let post := after.opened.served
  let begin := source.originalBegin.base.source
  let receipt : NativeHostCodec.Receipt :=
    ⟨accepted.intent.transactionId, accepted.intent.event.eventId,
      index + 1, post.worldRoot⟩
  { core :=
      { source := source.originalClaim.base.source
        originalTransaction := accepted.original.record.transactionId
        originalEvent := accepted.original.record.event.eventId
        originalNullifier :=
          (ApplicationLifecycleBegin.stableNullifier config.deployment.domain
            config.profile.semantics begin).nullifierId
        claimReceipt := receipt
        claimNullifier :=
          (ApplicationLifecycleClaim.stableNullifier config.deployment.domain
            config.profile.semantics source.originalClaim.base.source).nullifierId
        appPhysicalRoot := post.roots ⟨begin.app⟩
        packagePhysicalRoot := post.roots ⟨begin.packageManifest⟩
        authorityPhysicalRoot :=
          post.roots ⟨config.deployment.authorityCellId⟩
        postWorldRoot := receipt.worldRoot }
    originalClaim := source.originalClaim }

structure Candidate (config : Config) {store : StoreIdentity} (head : Head store)
    (source : ApplicationLifecycleRetryCompletionV4Source.Source) where
  private mk ::
  index : Nat
  selected : NativeHistorySelection.Candidate config head index
  claimBytes : selected.record.event.canonicalBytes =
    source.originalClaim.canonicalBytes
  accepted : ApplicationLifecycleRetryClaimV4Core.Conditional
    config head selected.ground source.originalClaim
  recordExact : selected.record =
    DurableReceiver.IntentRecord.ofIntent accepted.intent
  after : NativeHistorySelection.After config head index
  projectionExact : source.physical.report.claim =
    projection selected after source accepted

def select (config : Config) {store : StoreIdentity}
    (reader : Reader ResourceBirthCodec.rootBytes store) (bound : Nat)
    (source : ApplicationLifecycleRetryCompletionV4Source.Source) :
    IO (Except String (Candidate config reader.head source)) := do
  let count := source.physical.report.claim.core.claimReceipt.acceptedCount
  if 0 < count then
    let index := count - 1
    let selected ← match ← NativeHistorySelection.select config reader bound index
        (ApplicationLifecycleRetryClaimV4Core.keys source.originalClaim) with
      | .error detail => return .error detail
      | .ok selected => pure selected
    if claimBytes : selected.record.event.canonicalBytes =
        source.originalClaim.canonicalBytes then
      let accepted ← match ← ApplicationLifecycleRetryClaimV4Core.prepare config reader
          selected.grounded source.originalClaim with
        | .error _ => return .error "selected claim source refused at its original prefix"
        | .ok accepted => pure accepted
      if matched : NativeHistorySelection.recordMatches selected.record accepted.intent = true then
        have recordExact : selected.record =
            DurableReceiver.IntentRecord.ofIntent accepted.intent :=
          (NativeHistorySelection.recordMatches_iff _ _).mp matched
        let after ← match ← NativeHistorySelection.selectAfter config reader index with
          | .error _ => return .error "selected claim post-prefix unavailable or invalid"
          | .ok after => pure after
        if projectionExact : source.physical.report.claim =
            projection selected after source accepted then
          return .ok ⟨index, selected, claimBytes, accepted,
            recordExact, after, projectionExact⟩
        else return .error "physical report differs from original claim projection"
      else return .error "selected claim full intent differs"
    else return .error "selected claim ingress differs"
  else return .error "physical report has no claim receipt"

end Minidregg.Kernel.ApplicationLifecycleRetryCompletionV4History
