/- Shape selector for a same-walk, already native-admitted event20 record and
its exact receipt. The caller, not this pure selector, must mint that history
pair through native replay or verified exact readback. -/
import Kernel.FnConsumerNamespaceRegistration
import Kernel.DurableReceiver

namespace Minidregg.Kernel.FnConsumerNamespaceHistory

open Minidregg.Kernel.FnConsumerNamespaceRegistration
open Minidregg.Kernel
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

structure Original where
  private mk ::
  ingress : Ingress
  receipt : Receipt
  transactionExact : transactionId ingress.spec = receipt.transactionId
  eventExact : (event ingress).eventId = receipt.eventId

/-- Both the complete gateway-bound key and the exact native registration
receipt must match a selected/empty successor. Callers obtain `Original`
only from a verified same-walk record/receipt selection. -/
def Original.matches (original : Original) (key : FnConsumerFrontierCore.Key)
    (receipt : Receipt) : Bool :=
  original.ingress.spec.key == key && original.receipt == receipt

theorem Original.matches_iff (original : Original)
    (key : FnConsumerFrontierCore.Key) (receipt : Receipt) :
    original.matches key receipt = true ↔
      original.ingress.spec.key = key ∧ original.receipt = receipt := by
  simp [Original.matches]

def selectAt (domain semantics : Digest)
    (record : DurableReceiver.IntentRecord) (receipt : Receipt) :
    Option Original := do
  let ingress ← ingressCodec.decode record.event.canonicalBytes
  if ingress.spec.domain != domain || ingress.spec.semantics != semantics ||
      record.event != event ingress ||
      record.transactionId != transactionId ingress.spec then none
  else
    if transactionExact : transactionId ingress.spec = receipt.transactionId then
      if eventExact : (event ingress).eventId = receipt.eventId then
        some ⟨ingress, receipt, transactionExact, eventExact⟩
      else none
    else none

end Minidregg.Kernel.FnConsumerNamespaceHistory
