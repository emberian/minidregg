/-
# Kernel.SeatCell — the registry kind of seats, invitations and contract instances

Every cell the seat kernel (`Kernel.Seat`, `Kernel.SeatReceiver`) writes, other
than the Book, is one registry cell of this kind
(`CanonicalCellRegistry.Kind.seat`), built by the one protected-cell construction
(`Kernel.ProtectedCell`) at its coordinate `2^256 + cSHAKE(domain, role, key)`:

| role         | key                         | body                                        |
|--------------|-----------------------------|---------------------------------------------|
| `instance`   | the instance object's id    | the instance: package pin, clause, seats    |
| `invitation` | the invitation id           | the invitation: instance, role, terms, holder, spent |
| `seat`       | `H(offer transaction)`      | the seat: instance, offerer, payee, proposal, open |
| `holdings`   | the activity record cell id | the seat coordinates the activity holds     |
| `package`    | the package pin             | the contract artifact bytes                 |

**A seat's Book account IS its seat cell's coordinate.** No user may install a
cell of this kind (`UserShape` is false), no birth may choose an id at or above
`2^256` (`CanonicalCellRegistry.userInitial_not_seat_coordinate`), and the seat
kernel refuses a funding or payee account in that space, so no one can own,
squat or pre-fund a seat account: the offerer never names it.
-/
import Kernel.ProtectedCell

namespace Minidregg.Kernel.SeatCell

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- Registry tag 20 (after 19 objectiveActivity); schema 91019. -/
def registryTag : UInt8 := 20
def schemaId : Nat := 91019
def wireVersion : Nat := 1

inductive Role where
  | inst
  | invitation
  | seat
  | holdings
  | package
  deriving DecidableEq, Repr

def Role.tag : Role → Nat
  | .inst => 0 | .invitation => 1 | .seat => 2 | .holdings => 3 | .package => 4

def Role.ofTag : Nat → Role
  | 0 => .inst | 1 => .invitation | 2 => .seat | 3 => .holdings | _ => .package

def roleStream : StreamCodec Role :=
  StreamCodec.xmap StreamCodec.nat Role.tag Role.ofTag (by intro role; cases role <;> rfl)

/-- The seat family: `DREGG.SEAT.CELL.ID/v1`, `DREGG.SEAT.CELL.STATE/v1`,
frame `DREGG/SEAT-CELL`. -/
def spec : ProtectedCell.Spec where
  Role := Role
  roleStream := roleStream
  idCustomization := "DREGG.SEAT.CELL.ID/v1".toUTF8.toList
  rootCustomization := "DREGG.SEAT.CELL.STATE/v1".toUTF8.toList
  wireFrame := "DREGG/SEAT-CELL".toUTF8.toList
  wireVersion := wireVersion

abbrev Payload := ProtectedCell.Payload spec
abbrev payloadStream : StreamCodec Payload := ProtectedCell.payloadStream spec
abbrev reservedBase : Nat := ProtectedCell.reservedBase
abbrev coordinate (domain : Digest) (role : Role) (key : List UInt8) : Nat :=
  ProtectedCell.coordinate spec domain role key
theorem coordinate_reserved (domain : Digest) (role : Role) (key : List UInt8) :
    reservedBase ≤ coordinate domain role key := ProtectedCell.coordinate_reserved spec domain role key
abbrev layout : Store.Layout.{0, 0, 0} := ProtectedCell.layout spec
abbrev payloadAt (state : Store layout) : Option Payload := ProtectedCell.payloadAt spec state
abbrev materializer : Materializer layout Digest := ProtectedCell.materializer spec
abbrev CellValid (domain : Digest) (cellId : Nat) (payload : Payload) : Prop :=
  ProtectedCell.CellValid spec domain cellId payload
abbrev cellOf (payload : Payload) : Materialized materializer := ProtectedCell.cellOf spec payload

#assert_axioms coordinate_reserved
end Minidregg.Kernel.SeatCell
