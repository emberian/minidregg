/-
Conditional source check of one original launch-bound claim at its exact
prefix. Replay must compare this to its chronological PriorClaimV3; the live
receiver must obtain that comparison from Verified. A structural prefix is
not, by itself, a completion permit.
-/
import Kernel.ApplicationLifecycleCompletionV2Source
import Kernel.NativeHistorySelection
import Kernel.ApplicationLifecycleClaimV3Core

namespace Minidregg.Kernel.ApplicationLifecycleCompletionV2History

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

def projection {config : Config} {opened : Opened config} {index : Nat}
    (candidate : NativeHistorySelection.Candidate config opened index)
    (after : Opened config)
    (source : ApplicationLifecycleCompletionV2Source.Source)
    (accepted : ApplicationLifecycleClaimV3Core.Conditional
      config candidate.prior source.originalClaim) :
    ApplicationLifecycleClaimV3Projection.Committed :=
  let post := after.durable
  let begin := source.originalBegin.base.source
  let receipt : NativeHostCodec.Receipt :=
    ⟨accepted.intent.transactionId, accepted.intent.event.eventId,
      index + 1, worldRoot config post.image⟩
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
        appPhysicalRoot := post.snapshot.model.roots ⟨begin.app⟩
        packagePhysicalRoot := post.snapshot.model.roots ⟨begin.packageManifest⟩
        authorityPhysicalRoot :=
          post.snapshot.model.roots ⟨config.deployment.authorityCellId⟩
        postWorldRoot := receipt.worldRoot }
    originalClaim := source.originalClaim }

structure Candidate (config : Config) (opened : Opened config)
    (source : ApplicationLifecycleCompletionV2Source.Source) where
  private mk ::
  index : Nat
  selected : NativeHistorySelection.Candidate config opened index
  claimBytes : selected.record.event.canonicalBytes =
    source.originalClaim.canonicalBytes
  accepted : ApplicationLifecycleClaimV3Core.Conditional
    config selected.prior source.originalClaim
  recordExact : selected.record =
    DurableReceiver.IntentRecord.ofIntent accepted.intent
  after : Opened config
  afterBytes : after.durable.bytes =
    DurableReceiverCodec.encode (NativeHistorySelection.prefixImage opened (index + 1))
  projectionExact : source.physical.report.claim =
    projection selected after source accepted

def select (config : Config) (opened : Opened config)
    (source : ApplicationLifecycleCompletionV2Source.Source) :
    IO (Except String (Candidate config opened source)) := do
  let count := source.physical.report.claim.core.claimReceipt.acceptedCount
  if 0 < count then
    let index := count - 1
    let selected ← match NativeHistorySelection.select config opened index with
      | .error detail => return .error detail
      | .ok selected => pure selected
    if claimBytes : selected.record.event.canonicalBytes =
        source.originalClaim.canonicalBytes then
      let accepted ← match ← ApplicationLifecycleClaimV3Core.prepare config
          selected.prior source.originalClaim with
        | .error _ => return .error "selected claim source refused at its original prefix"
        | .ok accepted => pure accepted
      if matched : NativeHistorySelection.recordMatches selected.record accepted.intent = true then
        have recordExact : selected.record =
            DurableReceiver.IntentRecord.ofIntent accepted.intent :=
          (NativeHistorySelection.recordMatches_iff _ _).mp matched
        let bytes := DurableReceiverCodec.encode
          (NativeHistorySelection.prefixImage opened (index + 1))
        let loaded ← match DurableReceiverIO.loadBytes rootBytes bytes with
          | .error _ => return .error "selected claim post-prefix unavailable"
          | .ok loaded => pure loaded
        let after ← match validateLoaded config loaded with
          | .error _ => return .error "selected claim post-prefix invalid"
          | .ok after => pure after
        if afterBytes : after.durable.bytes = bytes then
          if projectionExact : source.physical.report.claim =
              projection selected after source accepted then
            return .ok ⟨index, selected, claimBytes, accepted,
              recordExact, after, afterBytes, projectionExact⟩
          else return .error "physical report differs from original claim projection"
        else return .error "selected claim post-prefix bytes changed"
      else return .error "selected claim full intent differs"
    else return .error "selected claim ingress differs"
  else return .error "physical report has no claim receipt"

end Minidregg.Kernel.ApplicationLifecycleCompletionV2History
