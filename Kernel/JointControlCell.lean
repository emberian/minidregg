/- Source-owned control-cell representation for the atomic integration join.
No alternate Store transaction is needed: this cell is changed in the same
DataIntent record as reservation/install/decision state. Integration must install
ordinaryGate in BOTH live admission and replay; merely importing is insufficient.
-/
import Kernel.JointReservation
namespace Minidregg.Kernel.JointControlCell
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.JointReservation
set_option autoImplicit false
structure Control where
  reservations : Table
  /-- Agreed terminal source decisions, indexed by exact scoped instance.
  These are common source transition records, NOT replica-local engine inputs. -/
  decisions : List (List UInt8 × List UInt8)
  /-- Durable source-authorized private continuation envelopes. -/
  repairOutbox : List (List UInt8)
  /-- Source-owned funds unavailable to ordinary application spending.
  Authorized maintenance debits/refills this alongside actual source charges. -/
  maintenanceReserve : Charge
def reservationStream : StreamCodec Reservation :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product bytesStream
      (StreamCodec.product DurableReceiverCodec.nullifierStream
        (StreamCodec.product DurableReceiverCodec.intentStream
          (StreamCodec.product bytesStream StreamCodec.nat)))))
    (fun r => (r.domain,r.candidateBytes,r.lineage,r.intent,r.sourceImageBytes,r.generation))
    (fun (d,c,l,i,s,g) => ⟨d,c,l,i,s,g⟩) (by intro r; cases r; rfl)
def controlStream : StreamCodec Control :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list reservationStream)
      (StreamCodec.product (StreamCodec.list (StreamCodec.product bytesStream bytesStream))
        (StreamCodec.product (StreamCodec.list bytesStream) DurableReceiverCodec.chargeStream)))
    (fun c => (c.reservations,c.decisions,c.repairOutbox,c.maintenanceReserve))
    (fun (r,e,o,m) => ⟨r,e,o,m⟩) (by intro c; cases c; rfl)
def decode (bytes : List UInt8) : Option Control := do
  let c ← controlStream.toLawful.decode bytes
  if controlStream.encode c == bytes then some c else none
/-- The control cell cannot itself become an application lock: otherwise
the engine could reserve the very cell needed to finish/abort its decision. -/
def Control.wellFormed (c : Control) (domain : Digest) (controlCell : CellId) : Bool :=
  c.reservations.all (fun r => r.domain == domain && !r.footprint.contains controlCell) &&
    (c.decisions.map Prod.fst).eraseDups.length == c.decisions.length
def Control.funded (c : Control) (domain : Digest) (available : Charge) : Bool :=
  Charge.fundedCheck (heldCharge domain c.reservations + c.maintenanceReserve) available
inductive Reject where
  | malformedControl | protectedControlWrite | reservationConflict | maintenanceStarvation
  deriving DecidableEq, Repr
/-- Pure predicate over the ACTUAL loaded source snapshot and proposed intent.
readControl is the source-owned full ResourceCell frame/payload decoder;
controlStream alone is NOT a native physical cell codec.
All writes of the control cell are reserved to a typed joint controller, whose
own admission must establish source law and certificate obligations. -/
def ordinaryGate {rootBytes : List UInt8 → Digest}
    (readControl : List UInt8 → Option Control) (domain : Digest) (controlCell : CellId)
    (snapshot : DataSnapshot rootBytes) (intent : DataIntent rootBytes) : Except Reject Unit := do
  let some c := readControl (snapshot.canonicalBytes controlCell) | .error .malformedControl
  if !c.wellFormed domain controlCell then .error .malformedControl
  else if intent.writes.any (fun w => w.cellId == controlCell) then .error .protectedControlWrite
  else if allowed domain c.reservations (IntentRecord.ofIntent intent) snapshot.model.available
    then
      if Charge.fundedCheck (heldCharge domain c.reservations + intent.exactCharge + c.maintenanceReserve) snapshot.model.available then .ok ()
      else .error .maintenanceStarvation
    else .error .reservationConflict
/-- Successful ordinary admission protects every exact held read/write cell;
the existing DataSnapshot.install is the actual source installer. -/
theorem admitted_preserves_bytes {rootBytes : List UInt8 → Digest}
    (readControl : List UInt8 → Option Control)
    (domain : Digest) (controlCell : CellId) (snapshot : DataSnapshot rootBytes)
    (intent : DataIntent rootBytes) (c : Control)
    (decoded : readControl (snapshot.canonicalBytes controlCell) = some c)
    (accepted : ordinaryGate readControl domain controlCell snapshot intent = .ok ())
    (held : Reservation) (member : held ∈ c.reservations) (same : held.domain = domain)
    (cell : CellId) (heldCell : cell ∈ held.footprint) :
    (DataSnapshot.install snapshot intent).canonicalBytes cell = snapshot.canonicalBytes cell := by
  simp only [ordinaryGate, decoded, Option.some.injEq] at accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  split at accepted
  next allowed =>
    exact compatible_install_preserves_bytes held intent
      (allowed_compatible domain c.reservations (IntentRecord.ofIntent intent)
        snapshot.model.available allowed held member same) snapshot cell heldCell
  · cases accepted
end Minidregg.Kernel.JointControlCell
