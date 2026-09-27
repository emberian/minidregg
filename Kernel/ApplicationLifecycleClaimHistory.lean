/-
Conditional original-BEGIN admission for a later lifecycle claim. The caller
supplies a physically loaded image; `NativeHistorySelection` reconstructs its
exact prefix and record, and the original BEGIN is freshly re-admitted at that
prefix. This is not a trusted history witness or a launch permit. The upper
adapter must also select the same step from `NativeHostReplay.Verified`.
-/
import Kernel.ApplicationLifecycleClaimIngress
import Kernel.ApplicationLifecycleBeginReceiver
import Kernel.NativeHistorySelection

namespace Minidregg.Kernel.ApplicationLifecycleClaimHistory

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.NativeHistorySelection
open Minidregg.Kernel.ApplicationLifecycleClaim

set_option autoImplicit false

structure Conditional (config : Config) (opened : Opened config)
    (source : Source) where
  private mk ::
  selected : Candidate config opened source.originalIndex
  admitted : ApplicationLifecycleBeginReceiver.Accepted config.deployment config.profile
    ⟨config.federation, logicalHeight config selected.prior.durable⟩
    selected.prior.durable source.begin
  exact : Matched selected admitted.intent

/-- The original record is equal to the full source-admitted BEGIN intent,
including its event, reads, writes, charges and nullifier. -/
theorem Conditional.original_record_exact {config : Config} {opened : Opened config}
    {source : Source} (conditional : Conditional config opened source) :
    conditional.selected.record =
      DurableReceiver.IntentRecord.ofIntent conditional.admitted.intent := by
  exact conditional.exact.selected.symm.trans conditional.exact.exact

def admit (config : Config) (opened : Opened config) (source : Source) :
    IO (Except String (Conditional config opened source)) := do
  let selected ← match NativeHistorySelection.select config opened source.originalIndex with
    | .error detail => return .error detail
    | .ok selected => pure selected
  let ambient : DeclaredResourceController.Ambient :=
    ⟨config.federation, logicalHeight config selected.prior.durable⟩
  let admitted ← match ← ApplicationLifecycleBeginReceiver.admitLoaded
      config.deployment config.profile ambient config.signature selected.prior.durable
      source.begin with
    | .error detail => return .error s!"original lifecycle begin refused: {detail}"
    | .ok admitted => pure admitted
  match NativeHistorySelection.matchIntent selected admitted.intent with
  | .error detail => return .error detail
  | .ok exact => return .ok ⟨selected, admitted, exact⟩

end Minidregg.Kernel.ApplicationLifecycleClaimHistory
