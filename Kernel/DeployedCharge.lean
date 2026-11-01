/-
# Kernel.DeployedCharge -- the Host debits the derived turn's charge (the FD-1 charge switch)

ROOT 10-08 / 10-14: the Host's storage lane is the World's: `storageOf` of the
derived turn's creates, legs and event (`DeployedHistory.legBytes`: the new
values an allocation or a write carries, `imageBytes` of a born cell,
`eventBytes`: the canonical bytes of the event the turn retains -- the archived
ingress), never the whole post image.  The per-kind framing the post image
carried is gone, and so is every receiver-local ingress, nullifier or marker
term: the event term is the one charge for what the log retains.

* `storageCharge snap writes event`: that number, read against the cells the
  snapshot holds -- what every receiver's `.storageBytes` lane is.  Read guards
  are not in it: a guard is a pin (`Turn.pins`), which writes nothing.
* `charge_eq`: for a represented snapshot, a derived turn's charge IS the
  intent's exact charge, on every lane, when the intent's storage lane is
  `storageCharge` (`charged`).  The append path refuses any other
  (`WorldTrack.advance`, naming the first `mismatch` lane), so on every
  accepted turn Host charge = World charge.
-/
module

public import Kernel.SnapRepresents
public import Kernel.DeployedRepresentsCheck
public import Kernel.DeployedHistory
public import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.DeployedCharge

open Minidregg.Theory.Store
open Minidregg.Kernel.World
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Kernel.HostRefinesWorld (SnapRepresents cellsOf cellsOf_eq allLanes mem_allLanes)
open Minidregg.Theory.ResourceCost (Lane Charge)
open Minidregg.Kernel.DurableDataIntent
  (DataIntent DataSnapshot DataWrite ReadGuard StableEvent TransactionId)
open Minidregg.Kernel.DeployedBridge (deployedR bridge)
open Minidregg.Kernel.DeployedHistory (history)

set_option autoImplicit false

variable {rootBytes : List UInt8 → Theory.TypedAuthorization.Digest}

/-- The storage lane of the turn a write list and its event are, against held
cells: `storageOf` of its derived creates and legs and its event. -/
def storageAt (cells : CellId → Option (Cell deployedR)) (writes : List DataWrite)
    (event : StableEvent) : Nat :=
  let ds := deltas bridge.codec cells writes
  storageOf history (ds.filterMap fun d => d.2.create? d.1)
    (ds.filterMap fun d => d.2.leg? bridge.codec d.1) event

/-- The storage lane against the cells a snapshot holds. -/
def storageCharge (snap : DataSnapshot rootBytes) (writes : List DataWrite)
    (event : StableEvent) : Nat :=
  storageAt (cellsOf bridge snap) writes event

theorem storageCharge_eq (snap : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    storageCharge snap intent.writes intent.event =
      storageOf history (createsOf bridge.codec (cellsOf bridge snap) intent)
        (legsOf bridge.codec (cellsOf bridge snap) intent) intent.event := rfl

/-- **Host charge = World charge.** -/
theorem charge_eq {snap : DataSnapshot rootBytes} {height : Nat}
    {w : World deployedR TransactionId Theory.TypedAuthorization.Digest}
    (rep : SnapRepresents bridge snap height w) {intent : DataIntent rootBytes}
    {t : DTurn deployedR Theory.TypedAuthorization.Digest}
    (derived : Turn.ofIntent bridge history w intent = .ok t)
    (charged : intent.exactCharge .storageBytes =
      storageCharge snap intent.writes intent.event) :
    t.charge = intent.exactCharge := by
  have d := (ofCells_ok derived).eq
  have cells : (fun c => w.cells c) = cellsOf bridge snap := funext fun c => cellsOf_eq rep c
  rw [d]
  funext l
  show chargeOf history (createsOf bridge.codec (fun c => w.cells c) intent)
    (legsOf bridge.codec (fun c => w.cells c) intent) intent.event intent.exactCharge l = _
  rw [cells]
  unfold chargeOf
  split
  · rename_i e
    subst e
    rw [charged, storageCharge_eq]
  · rfl

#assert_axioms charge_eq

/-- The first lane on which two charges differ, if any: what the append path
names when an intent's charge is not its derived turn's. -/
def mismatch (charge exact : Charge) : Option Lane :=
  allLanes.find? fun l => decide (charge l ≠ exact l)

theorem mismatch_none {charge exact : Charge} (h : mismatch charge exact = none) : charge = exact :=
  funext fun l => by simpa using List.find?_eq_none.mp h l (mem_allLanes l)

theorem mismatch_self (charge : Charge) : mismatch charge charge = none :=
  List.find?_eq_none.mpr fun _ _ => by simp

#assert_axioms mismatch_none
#assert_axioms mismatch_self

end Minidregg.Kernel.DeployedCharge
