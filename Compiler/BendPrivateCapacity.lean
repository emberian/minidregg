/- Versioned fixed-capacity private execution charging. This is a reservation
semantics, not an invented padded source step count. Activating it requires the
new receiver's funded reservation/custody join; historical Nock remains exact.
-/
import Theory.ResourceCost
import Compiler.NockProgramCodec

namespace Minidregg.Compiler.BendPrivateCapacity
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

def contract : List UInt8 :=
  "DREGG.BEND.PRIVATE-CAPACITY/v1:public-fixed-reservation;private-canonical-IR-usage;full-padding-control-repair;no-public-exact-use-refund;physical-backend-cost-separate;current-funded-resource-authority;historical-nock-unchanged".toUTF8.toList

structure Capacity where
  incidences : Nat
  turnBytes : Nat
  memoryTouches : Nat
  witnessBytes : Nat
  proofWork : Nat
  storageBytes : Nat
  networkBytes : Nat
  sideEffectCount : Nat
  feeDebit : Nat
  leaseByteBlocks : Nat
  deriving DecidableEq, Repr

def charge (capacity : Capacity) : ResourceCost.Charge
  | .incidences => capacity.incidences
  | .turnBytes => capacity.turnBytes
  | .memoryTouches => capacity.memoryTouches
  | .witnessBytes => capacity.witnessBytes
  | .proofWork => capacity.proofWork
  | .storageBytes => capacity.storageBytes
  | .networkBytes => capacity.networkBytes
  | .sideEffectCount => capacity.sideEffectCount
  | .feeDebit => capacity.feeDebit
  | .leaseByteBlocks => capacity.leaseByteBlocks

def quote (capacity : Capacity) : ResourceCost.Quote :=
  ⟨charge capacity, charge capacity, fun _ => Nat.le_refl _⟩

/-- Actual canonical IR usage is private and must fit the reservation. It is
never substituted for the public charge, and it is not native opcode cost. -/
structure Fits (capacity : Capacity) where
  canonicalIrUsage : ResourceCost.Charge
  bounded : canonicalIrUsage ≤ charge capacity

def publicCharge (capacity : Capacity) (_usage : Fits capacity) : ResourceCost.Charge :=
  charge capacity

theorem branch_charge_independent (capacity : Capacity) (left right : Fits capacity) :
    publicCharge capacity left = publicCharge capacity right := rfl

theorem exact_reserved (capacity : Capacity) :
    (quote capacity).exact = (quote capacity).upper := rfl

/-- Reservation affordability checks the entire fixed vector, including padding
and repair, rather than the observed secret branch's usage. -/
def funded (capacity : Capacity) (available : ResourceCost.Charge) : Bool :=
  ResourceCost.Charge.fundedCheck (charge capacity) available

theorem funded_iff (capacity : Capacity) (available : ResourceCost.Charge) :
    funded capacity available = true ↔ charge capacity ≤ available :=
  ResourceCost.Charge.fundedCheck_eq_true_iff _ _

end Minidregg.Compiler.BendPrivateCapacity
