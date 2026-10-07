/-
An original lifecycle BEGIN is selected from the native-admitted replay walk,
then the same complete BEGIN intent and current claim are checked against one
exact old image. This is an admission candidate, not a durable claim receipt or
a physical launch permit.
-/
import Kernel.NativeHostReplay
import Kernel.ApplicationLifecycleClaimCore
import Kernel.NativeHistorySelection

namespace Minidregg.Kernel.ApplicationLifecycleClaimVerified

open Minidregg.Compiler
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.NativeHostReplay
open Minidregg.Kernel.ApplicationLifecycleClaimIngress

set_option autoImplicit false

structure Admitted (config : Config) (target : Durable) (ingress : Ingress) where
  private mk ::
  selection : VerifiedSelection config target ingress.source.originalIndex
  claim : ClaimAt config selection.verified.opened ingress
  /-- The walk's admitted prefix before the original BEGIN is the Store's own verified log:
  every one of those records is the record the claim's history `reader` gives, verified against
  its anchored head, at that height (read in windows, none held; the hash floor is the one
  every verified read carries, `DurableHistory.verifyAt_sound`: an honest leaf or a node
  collision). Replaces the equality of the claim's prior image with the walk's. -/
  originalPrefixExact : NativeHistorySelection.PrefixRead claim.reader.head
    selection.selected.priorRecords ingress.source.originalIndex
  /-- The claim's original-prefix state is the walk's: same height and same chain. -/
  originalPriorHeight : claim.conditional.original.selected.prior.height =
    selection.selected.before.durable.height
  originalPriorChain : claim.conditional.original.selected.prior.served.chain =
    selection.selected.before.durable.chain
  originalRecordExact : recordMatches selection.selected.record
    claim.conditional.original.admitted.intent = true
  originalReceiptTransaction : selection.selected.receipt.transactionId =
    claim.conditional.original.admitted.intent.transactionId
  originalReceiptEvent : selection.selected.receipt.eventId =
    claim.conditional.original.admitted.intent.event.eventId

def Admitted.intent {config : Config} {target : Durable} {ingress : Ingress}
    (admitted : Admitted config target ingress) :
    DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes :=
  admitted.claim.intent

def Admitted.toDerived {config : Config} {target : Durable} {ingress : Ingress}
    (admitted : Admitted config target ingress) :
    Derived config admitted.selection.verified.opened :=
  admitted.claim.toDerived

theorem Admitted.toDerived_intent {config : Config} {target : Durable}
    {ingress : Ingress} (admitted : Admitted config target ingress) :
    admitted.toDerived.intent = admitted.intent := rfl

/-- Replaying today's physical image is not enough: the original BEGIN prefix
must be the one that the verifier actually admitted, and the full original
record and receipt identities must match the source-recomputed BEGIN. -/
def admit (config : Config) {store : DurableHistory.StoreIdentity}
    (reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store)
    (target : Durable) (ingress : Ingress) :
    IO (Except String (Admitted config target ingress)) := do
  let .ok selection ← verifyLoadedSelected config reader target ingress.source.originalIndex
    | return .error "lifecycle claim selected native history refused"
  let .ok claim ← admitClaimVerified selection.verified ingress
    | return .error "lifecycle claim current or original admission refused"
  let ⟨originalPrefixExact⟩ ← match ← NativeHistorySelection.readPrefix claim.reader
      selection.selected.priorRecords ingress.source.originalIndex with
    | .error detail => return .error s!"lifecycle claim original prefix refused: {detail}"
    | .ok exact => pure exact
  if originalPriorHeight : claim.conditional.original.selected.prior.height =
      selection.selected.before.durable.height then
   if originalPriorChain : claim.conditional.original.selected.prior.served.chain =
      selection.selected.before.durable.chain then
    if originalRecordExact : recordMatches selection.selected.record
        claim.conditional.original.admitted.intent = true then
      if originalReceiptTransaction : selection.selected.receipt.transactionId =
          claim.conditional.original.admitted.intent.transactionId then
        if originalReceiptEvent : selection.selected.receipt.eventId =
            claim.conditional.original.admitted.intent.event.eventId then
          return .ok ⟨selection, claim, originalPrefixExact, originalPriorHeight,
            originalPriorChain, originalRecordExact, originalReceiptTransaction,
            originalReceiptEvent⟩
        else return .error "lifecycle claim original event receipt differs"
      else return .error "lifecycle claim original transaction receipt differs"
    else return .error "lifecycle claim original complete intent differs"
   else return .error "lifecycle claim original prefix chain differs from the admitted walk's"
  else return .error "lifecycle claim original prefix height differs from the admitted walk's"

theorem Admitted.original_record_at {config : Config} {target : Durable}
    {ingress : Ingress} (admitted : Admitted config target ingress) :
    target.image.accepted[ingress.source.originalIndex]? =
      some (DurableReceiver.IntentRecord.ofIntent admitted.claim.conditional.original.admitted.intent) := by
  rw [admitted.selection.record_at]
  exact congrArg some ((recordMatches_iff _ _).mp admitted.originalRecordExact)

theorem Admitted.event_exact {config : Config} {target : Durable}
    {ingress : Ingress} (admitted : Admitted config target ingress) :
    admitted.intent.event = ApplicationLifecycleClaimIngress.event ingress :=
  admitted.claim.conditional.intent_event

end Minidregg.Kernel.ApplicationLifecycleClaimVerified
