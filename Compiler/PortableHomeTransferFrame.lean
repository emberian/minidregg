/- Full source ResourceCell control envelope. Transfer payload never replaces
lifecycle/kind/policy metadata and never installs client-supplied raw posts. -/
import Compiler.PortableHomeTransferCodec
import Compiler.CanonicalCellRegistry
import Kernel.ContentResource
namespace Minidregg.Compiler.PortableHomeTransferFrame
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Kernel.PortableHomeTransfer
set_option autoImplicit false
structure Pin where
  cell : Minidregg.Kernel.DurableDataIntent.CellId
  atom : AtomId
  schema : Digest
  deriving DecidableEq

def atom (pin : Pin) (bytes : List UInt8) : Option AtomRecord := do
  let .live packed ← ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry |>.decode bytes
    | none
  match packed with
  | ⟨.content,content⟩ => do
      let actual ← Hyperdocument.lookup content.logical .atoms pin.atom
      if actual.document != Kernel.ContentResource.documentOf pin.cell.value ||
          actual.kind != .inlineObject pin.schema || actual.tombstonedAt.isSome then none else some actual
  | _ => none

def readState (pin : Pin) (bytes : List UInt8) : Option State := do
  let actual ← atom pin bytes
  PortableHomeTransferCodec.decode actual.payload

def edit (pin : Pin) (bytes : List UInt8) (next : State) : Option Kernel.ContentResource.Command := do
  let before ← atom pin bytes
  return ⟨[.editAtom ⟨pin.atom,before,.inlineObject pin.schema,
    PortableHomeTransferCodec.encode next,false⟩]⟩

/-- Registered in BOTH live and chronological replay by the owning kernel
facet. Every ordinary control write refuses; source-authorized typed receiving
retains joint/activity facet gates and checks its ONE exact derived control post. -/
def ordinaryGate {rootBytes : List UInt8 → Digest} (pin : Pin)
    (snapshot : Kernel.DurableDataIntent.DataSnapshot rootBytes)
    (intent : Kernel.DurableDataIntent.DataIntent rootBytes) :
    Except Kernel.DurableDataIntent.RejectReason Unit := do
  let some state := readState pin (snapshot.canonicalBytes pin.cell)
    | throw (.durable .transactionConflict)
  if !Minidregg.Theory.ResourceCost.Charge.fundedCheck
      (state.maintenanceReserve + intent.exactCharge) snapshot.model.available then
    throw (.durable .transactionConflict)
  if intent.writes.any (fun write => write.cellId == pin.cell) then
    throw (.durable .transactionConflict)
  else
    let touchesHome := intent.writes.any (fun write => write.cellId.value ∈ state.governedCells)
    let reconciled := decide (AllSettled state.liabilities)
    let serving := state.phase == .serving ||
      ((state.phase == .destinationActive || state.phase == .released) && reconciled)
    if touchesHome && !serving then throw (.durable .transactionConflict) else pure ()

/- Capturing bytes is not enough: ordinary writes to source-selected home
cells stop as soon as preparation is durable. Maintenance/reconciliation may
advance only through exact source-derived portable intent receiving, retaining
all other facet laws. Activity dispatch also needs its current worker admission
join; this write gate alone is not an external process fence. -/
end Minidregg.Compiler.PortableHomeTransferFrame
