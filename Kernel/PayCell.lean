/-
# Kernel.PayCell — the pay cell: tariff, deposit address book, assignment

One store cell per deployment, at an identifier derived from the deployment
domain (`physicalId`), with three namespaces on `Theory.Store`:

| namespace    | key          | value                     | discipline  |
|--------------|--------------|---------------------------|-------------|
| `tariff`     | `Unit`       | `PayTariff.Tariff`        | RAM         |
| `book`       | index `Nat`  | 32-byte deposit address   | append-only |
| `assignment` | index `Nat`  | Book `AccountId`          | append-only |

`book` is written by the operator's control capability (`PayBookReceiver`);
`assignment` binds book index `i` to the account a subject owns
(`PayAssignmentReceiver`); `tariff` is the operator's versioned rate. Time is
not here: the deployment's one clock is the clock cell (`Kernel.ClockCell`,
written by `ClockTickReceiver`), and a payment's "paid at" is that clock's `now`.

Both indexed namespaces are append-only, so an index is written once
(`Store.Op.allocate_enabled_fresh`).  The index an observation names resolves
to both its address (`bookAt`) and its account (`assignmentAt`); a payment
nullifier covering signature ‖ address (PAY §10 erratum 1) reads the address
from `bookAt`.

Wire: the store codec with layout name `DREGG/PAY/CELL/v2` (its frame commits
to the name and every namespace's codec identifier); the tariff value is
`DREGG/PAY/TARIFF/v1`.
-/
import Compiler.StoreCodec
import Kernel.PayTariff

namespace Minidregg.Kernel.PayCell

open Minidregg.Compiler
open Minidregg.Compiler.StoreCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Store
open Minidregg.Theory.CellState (Materializer Materialized materialize)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.PayTariff

set_option autoImplicit false

inductive Namespace
  | tariff
  | book
  | assignment
  deriving DecidableEq, Repr

def Namespace.Key : Namespace → Type
  | .tariff => Unit
  | .book => Nat
  | .assignment => Nat

def Namespace.Value : Namespace → Type
  | .tariff => Tariff
  | .book => Address32
  | .assignment => Nat

instance Namespace.keyDecEq : (space : Namespace) → DecidableEq (Namespace.Key space)
  | .tariff => inferInstanceAs (DecidableEq Unit)
  | .book => inferInstanceAs (DecidableEq Nat)
  | .assignment => inferInstanceAs (DecidableEq Nat)

instance Namespace.valueDecEq : (space : Namespace) → DecidableEq (Namespace.Value space)
  | .tariff => inferInstanceAs (DecidableEq Tariff)
  | .book => inferInstanceAs (DecidableEq (List UInt8))
  | .assignment => inferInstanceAs (DecidableEq Nat)

def Namespace.discipline : Namespace → Discipline
  | .tariff => .ram
  | .book => .appendOnly
  | .assignment => .appendOnly

abbrev layout : Layout.{0, 0, 0} where
  Namespace := Namespace
  Key := Namespace.Key
  Value := Namespace.Value
  discipline := Namespace.discipline

abbrev PayStore := Store layout

/-! ## Addresses and typed reads -/

def tariffAddress : Address layout := ⟨.tariff, ()⟩
def bookAddress (index : Nat) : Address layout := ⟨.book, index⟩
def assignmentAddress (index : Nat) : Address layout := ⟨.assignment, index⟩

def tariffOf (store : PayStore) : Option Tariff := store tariffAddress
/-- The deposit address at book index `index`. -/
def bookAt (store : PayStore) (index : Nat) : Option Address32 := store (bookAddress index)
/-- The account book index `index` is assigned to. -/
def assignmentAt (store : PayStore) (index : Nat) : Option Nat := store (assignmentAddress index)

/-- Present rows of one namespace. -/
def countIn (store : PayStore) (space : Namespace) : Nat :=
  (store.support.filter fun address => address.1 = space).card

/-- The next unassigned index: the number of assignments made.  History
independent — the assignment namespace grows with payers, not turns. -/
def nextFree (store : PayStore) : Nat := countIn store .assignment

/-- The next free book index: the number of installed deposit addresses. -/
def bookSize (store : PayStore) : Nat := countIn store .book

/-- Whether some index is already bound to `account`: a scan of the support. -/
def accountAssigned (store : PayStore) (account : Nat) : Bool :=
  decide (∃ address ∈ store.support, assignedTo store account address = true)
where
  assignedTo (store : PayStore) (account : Nat) : Address layout → Bool
    | ⟨.assignment, index⟩ => decide (assignmentAt store index = some account)
    | _ => false

/-! ## The cell law -/

/-- Every book entry is a 32-byte key; a scan of the support. -/
def rowShaped (store : PayStore) : Address layout → Bool
  | ⟨.book, index⟩ =>
      match bookAt store index with
      | some address => address.length == 32
      | none => true
  | _ => true

/-- A pay cell always holds a tariff, and every deposit address
is 32 bytes.  The identity half of the law is the registry's
(`CanonicalCellRegistry.LogicalLaw`). -/
def Law (store : PayStore) : Prop :=
  (tariffOf store).isSome = true ∧
    ∀ address ∈ store.support, rowShaped store address = true

instance (store : PayStore) : Decidable (Law store) := by
  unfold Law
  infer_instance

/-! ## Wire `DREGG/PAY/CELL/v2` -/

def namespaceStream : StreamCodec Namespace where
  encode
    | .tariff => [0]
    | .book => [1]
    | .assignment => [2]
  decodePrefix
    | 0 :: suffix => some (.tariff, suffix)
    | 1 :: suffix => some (.book, suffix)
    | 2 :: suffix => some (.assignment, suffix)
    | _ => none
  decodePrefix_encode := by intro space suffix; cases space <;> rfl

def keyStream : (space : Namespace) → StreamCodec (Namespace.Key space)
  | .tariff => unitStream
  | .book => StreamCodec.nat
  | .assignment => StreamCodec.nat

def valueStream : (space : Namespace) → StreamCodec (Namespace.Value space)
  | .tariff => tariffStream
  | .book => bytesStream
  | .assignment => StreamCodec.nat

def wireName : String := "DREGG/PAY/CELL/v2"

def wire : Wire layout where
  name := wireName
  namespaces := [.tariff, .book, .assignment]
  namespaces_complete := by intro space; cases space <;> simp
  namespaceStream := namespaceStream
  keyStream := keyStream
  valueStream := valueStream
  keyCodecId
    | .tariff => "unit"
    | .book => "book-index/nat"
    | .assignment => "book-index/nat"
  valueCodecId
    | .tariff => "DREGG/PAY/TARIFF/v1"
    | .book => "address32/bytes"
    | .assignment => "account-id/nat"

def materializer : Materializer layout Digest := StoreCodec.materializer wire

abbrev Cell := Materialized materializer

theorem cell_roundtrip (store : PayStore) :
    StoreCodec.decode wire (StoreCodec.encode wire store) = some store :=
  StoreCodec.decode_encode wire store

theorem cell_canonical {bytes : List UInt8} {store : PayStore}
    (accepted : StoreCodec.decode wire bytes = some store) : StoreCodec.encode wire store = bytes :=
  StoreCodec.decode_reencodes wire accepted

/-! ## Identity and genesis -/

def idCustomization : List UInt8 := "DREGG.PAY.CELL.ID/v1".toUTF8.toList

/-- The pay cell's physical identifier in deployment `domain`. -/
def physicalId (domain : Digest) : Nat :=
  (Sp800185Cshake256.hash idCustomization (digestStream.encode domain)).digest.value

/-- The genesis pay cell: the placeholder tariff, an empty book and no
assignment. -/
def genesisStore : PayStore :=
  (0 : PayStore).set tariffAddress (some genesisDefault)

theorem genesis_law : Law genesisStore := by decide +kernel

theorem genesis_tariff : tariffOf genesisStore = some genesisDefault := by decide +kernel

theorem genesis_nextFree : nextFree genesisStore = 0 := by decide +kernel

/-- Refuting pole of the law: a pay cell without a tariff is not lawful. -/
theorem tariffless_unlawful : ¬ Law (0 : PayStore) := by
  decide +kernel

/-- Refuting pole of the row shape: a 31-byte deposit address is not lawful. -/
theorem short_address_unlawful :
    ¬ Law (genesisStore.set (bookAddress 0) (some (List.replicate 31 1))) := by
  decide +kernel

#assert_axioms cell_roundtrip
#assert_axioms cell_canonical
#assert_axioms genesis_law
#assert_axioms genesis_tariff
#assert_axioms genesis_nextFree
#assert_axioms tariffless_unlawful
#assert_axioms short_address_unlawful

end Minidregg.Kernel.PayCell
