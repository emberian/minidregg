/-
# Kernel.PayCell — the pay cell: tariff, deposit address book, assignment, enrolment

One store cell per deployment, at an identifier derived from the deployment
domain (`physicalId`), with six namespaces on `Theory.Store`:

| namespace    | key              | value                     | discipline  |
|--------------|------------------|---------------------------|-------------|
| `tariff`     | `Unit`           | `PayTariff.Tariff`        | RAM         |
| `book`       | index `Nat`      | 32-byte deposit address   | append-only |
| `assignment` | index `Nat`      | Book `AccountId`          | append-only |
| `enrolment`  | Mini key (32 B)  | `EnrolRecord`             | RAM         |
| `sshIndex`   | ssh blob (51 B)  | Mini key                  | append-only |
| `journal`    | nullifier bytes  | `Unattributed`            | append-only |

The last three are PAY §11's self-enrollment state (layout v2).  An
`enrolment` row is written once by an enrollment and rewritten only by a
renewal of the same key (its lease grows, `PayEnrolDecision`); `sshIndex`
makes an ssh key belong to at most one Mini key, and the law ties the two
namespaces together in both directions; `journal` holds every
enrollment-index payment that was not accepted, with its named reason.

`book` is written by the operator's control capability (`PayBookReceiver`);
`assignment` binds book index `i` to the account a subject owns
(`PayAssignmentReceiver`); `tariff` is the operator's versioned rate. Time is
the deployment's one clock cell (`Kernel.ClockCell`): the pay observer advances
its `slot` (and its `now` to the observed block time when that is later) in the
same intent as the credits it reports; the pay cell keeps no clock.

Both indexed namespaces are append-only, so an index is written once
(`Store.Op.allocate_enabled_fresh`).  The index an observation names resolves
to both its address (`bookAt`) and its account (`assignmentAt`); a payment
nullifier covering signature ‖ address (PAY §10 erratum 1) reads the address
from `bookAt`.

Wire: the store codec with layout name `DREGG/PAY/CELL/v4` (its frame commits
to the name and every namespace's codec identifier); the tariff value is
`DREGG/PAY/TARIFF/v3`.  v3 = P3b-1's enrolment namespaces without P2's in-cell
clock: namespace tag 3 (the clock) is retired and decodes to nothing.  v4 = v3
with the tariff at `DREGG/PAY/TARIFF/v3` (C3's `slashCallerPermille`).  A v1,
v2 or v3 cell refuses to decode.
-/
import Compiler.StoreCodec
import Kernel.PayTariff
import Kernel.PayEnrolMemo

namespace Minidregg.Kernel.PayCell

open Minidregg.Compiler
open Minidregg.Compiler.StoreCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Store
open Minidregg.Theory.CellState (Materializer Materialized materialize)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayEnrolMemo (JournalReason MemoField isEd25519Blob)

set_option autoImplicit false

inductive Namespace
  | tariff
  | book
  | assignment
  | enrolment
  | sshIndex
  | journal
  deriving DecidableEq, Repr

/-- The finalized chain tip a pay observer reports at: the slot and its block
time (unix s). It is the observer's claim about the chain, carried in its
command; it is not stored here (the deployment clock cell holds `now`/`slot`). -/
structure ChainTip where
  slot : Nat
  blockTime : Nat
  deriving DecidableEq, Repr

/-- The chain hour of a tip: the unit of enrollment leases. -/
def ChainTip.hour (tip : ChainTip) : Nat := tip.blockTime / 3600

/-- The hour of a unix time: the public enrollment view's `clock.hour` (read
from the clock cell's `now`). -/
def hourOf (now : Nat) : Nat := now / 3600

def chainTipStream : StreamCodec ChainTip :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat StreamCodec.nat)
    (fun tip => (tip.slot, tip.blockTime))
    (fun (slot, blockTime) => ⟨slot, blockTime⟩)
    (by intro tip; cases tip; rfl)

/-- A self-enrolled Mini key's record (PAY §11.4), keyed by the 32-byte Mini
key.  `leaseUntil` is a chain hour (`blockTime / 3600`): the node membership
the key has paid for runs while `clock hour < leaseUntil`. -/
structure EnrolRecord where
  /-- The 51-byte `ssh-ed25519` wire blob the enrollment bought a login for. -/
  sshBlob : List UInt8
  /-- The Book account born for the key. -/
  account : Nat
  /-- The book index assigned to that account, if one was free. -/
  index : Option Nat
  leaseUntil : Nat
  /-- The chain slot of the enrolling payment. -/
  enrolledSlot : Nat
  deriving DecidableEq, Repr

/-- An enrollment-index payment that was not accepted: consumed (its
nullifier is spent), credited nowhere, and kept here with its reason. -/
structure Unattributed where
  index : Nat
  amount : Nat
  slot : Nat
  reason : JournalReason
  memo : MemoField
  deriving DecidableEq, Repr

def Namespace.Key : Namespace → Type
  | .tariff => Unit
  | .book => Nat
  | .assignment => Nat
  | .enrolment => List UInt8
  | .sshIndex => List UInt8
  | .journal => List UInt8

def Namespace.Value : Namespace → Type
  | .tariff => Tariff
  | .book => Address32
  | .assignment => Nat
  | .enrolment => EnrolRecord
  | .sshIndex => List UInt8
  | .journal => Unattributed

instance Namespace.keyDecEq : (space : Namespace) → DecidableEq (Namespace.Key space)
  | .tariff => inferInstanceAs (DecidableEq Unit)
  | .book => inferInstanceAs (DecidableEq Nat)
  | .assignment => inferInstanceAs (DecidableEq Nat)
  | .enrolment => inferInstanceAs (DecidableEq (List UInt8))
  | .sshIndex => inferInstanceAs (DecidableEq (List UInt8))
  | .journal => inferInstanceAs (DecidableEq (List UInt8))

instance Namespace.valueDecEq : (space : Namespace) → DecidableEq (Namespace.Value space)
  | .tariff => inferInstanceAs (DecidableEq Tariff)
  | .book => inferInstanceAs (DecidableEq (List UInt8))
  | .assignment => inferInstanceAs (DecidableEq Nat)
  | .enrolment => inferInstanceAs (DecidableEq EnrolRecord)
  | .sshIndex => inferInstanceAs (DecidableEq (List UInt8))
  | .journal => inferInstanceAs (DecidableEq Unattributed)

def Namespace.discipline : Namespace → Discipline
  | .tariff => .ram
  | .book => .appendOnly
  | .assignment => .appendOnly
  | .enrolment => .ram
  | .sshIndex => .appendOnly
  | .journal => .appendOnly

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
def enrolmentAddress (miniKey : List UInt8) : Address layout := ⟨.enrolment, miniKey⟩
def sshIndexAddress (sshBlob : List UInt8) : Address layout := ⟨.sshIndex, sshBlob⟩
def journalAddress (nullifier : List UInt8) : Address layout := ⟨.journal, nullifier⟩

def tariffOf (store : PayStore) : Option Tariff := store tariffAddress
/-- The deposit address at book index `index`. -/
def bookAt (store : PayStore) (index : Nat) : Option Address32 := store (bookAddress index)
/-- The account book index `index` is assigned to. -/
def assignmentAt (store : PayStore) (index : Nat) : Option Nat := store (assignmentAddress index)
/-- The self-enrollment record of a Mini key. -/
def enrolmentAt (store : PayStore) (miniKey : List UInt8) : Option EnrolRecord :=
  store (enrolmentAddress miniKey)
/-- The Mini key an ssh blob is enrolled under. -/
def sshIndexAt (store : PayStore) (sshBlob : List UInt8) : Option (List UInt8) :=
  store (sshIndexAddress sshBlob)
def journalAt (store : PayStore) (nullifier : List UInt8) : Option Unattributed :=
  store (journalAddress nullifier)

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

/-- Every book entry is a 32-byte key; every enrolment row is a 32-byte Mini
key holding one ssh-ed25519 blob that the ssh index maps back to it; every
ssh index row points at an enrolment row holding that blob.  A scan of the
support. -/
def rowShaped (store : PayStore) : Address layout → Bool
  | ⟨.book, index⟩ =>
      match bookAt store index with
      | some address => address.length == 32
      | none => true
  | ⟨.enrolment, miniKey⟩ =>
      match enrolmentAt store miniKey with
      | some record => miniKey.length == 32 && isEd25519Blob record.sshBlob &&
          decide (sshIndexAt store record.sshBlob = some miniKey)
      | none => true
  | ⟨.sshIndex, blob⟩ =>
      match sshIndexAt store blob with
      | some miniKey =>
          match enrolmentAt store miniKey with
          | some record => decide (record.sshBlob = blob)
          | none => false
      | none => true
  | _ => true

/-- A pay cell always holds a tariff, every deposit address is
32 bytes, and the enrolment and ssh index rows agree.  The identity half of the law is the registry's
(`CanonicalCellRegistry.LogicalLaw`). -/
def Law (store : PayStore) : Prop :=
  (tariffOf store).isSome = true ∧
    ∀ address ∈ store.support, rowShaped store address = true

instance (store : PayStore) : Decidable (Law store) := by
  unfold Law
  infer_instance

/-! ## Wire `DREGG/PAY/CELL/v4` -/

def namespaceStream : StreamCodec Namespace where
  encode
    | .tariff => [0]
    | .book => [1]
    | .assignment => [2]
    | .enrolment => [4]
    | .sshIndex => [5]
    | .journal => [6]
  decodePrefix
    | 0 :: suffix => some (.tariff, suffix)
    | 1 :: suffix => some (.book, suffix)
    | 2 :: suffix => some (.assignment, suffix)
    | 4 :: suffix => some (.enrolment, suffix)
    | 5 :: suffix => some (.sshIndex, suffix)
    | 6 :: suffix => some (.journal, suffix)
    | _ => none
  decodePrefix_encode := by intro space suffix; cases space <;> rfl

def enrolRecordStream : StreamCodec EnrolRecord :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.option StreamCodec.nat)
          (StreamCodec.product StreamCodec.nat StreamCodec.nat))))
    (fun record => (record.sshBlob, record.account, record.index, record.leaseUntil,
      record.enrolledSlot))
    (fun (blob, account, index, lease, slot) => ⟨blob, account, index, lease, slot⟩)
    (by intro record; cases record; rfl)

def unattributedStream : StreamCodec Unattributed :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product PayEnrolMemo.journalReasonStream PayEnrolMemo.memoFieldStream))))
    (fun row => (row.index, row.amount, row.slot, row.reason, row.memo))
    (fun (index, amount, slot, reason, memo) => ⟨index, amount, slot, reason, memo⟩)
    (by intro row; cases row; rfl)

def keyStream : (space : Namespace) → StreamCodec (Namespace.Key space)
  | .tariff => unitStream
  | .book => StreamCodec.nat
  | .assignment => StreamCodec.nat
  | .enrolment => bytesStream
  | .sshIndex => bytesStream
  | .journal => bytesStream

def valueStream : (space : Namespace) → StreamCodec (Namespace.Value space)
  | .tariff => tariffStream
  | .book => bytesStream
  | .assignment => StreamCodec.nat
  | .enrolment => enrolRecordStream
  | .sshIndex => bytesStream
  | .journal => unattributedStream

def wireName : String := "DREGG/PAY/CELL/v4"

def wire : Wire layout where
  name := wireName
  namespaces := [.tariff, .book, .assignment, .enrolment, .sshIndex, .journal]
  namespaces_complete := by intro space; cases space <;> simp
  namespaceStream := namespaceStream
  keyStream := keyStream
  valueStream := valueStream
  keyCodecId
    | .tariff => "unit"
    | .book => "book-index/nat"
    | .assignment => "book-index/nat"
    | .enrolment => "mini-key32/bytes"
    | .sshIndex => "ssh-ed25519-blob/bytes"
    | .journal => "soltx-nullifier/bytes"
  valueCodecId
    | .tariff => "DREGG/PAY/TARIFF/v3"
    | .book => "address32/bytes"
    | .assignment => "account-id/nat"
    | .enrolment => "DREGG/PAY/ENROLMENT/v1"
    | .sshIndex => "mini-key32/bytes"
    | .journal => "DREGG/PAY/UNATTRIBUTED/v1"

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

/-- A lawful enrolled key: its record and its ssh index row. -/
def enrolledFixture : PayStore :=
  (genesisStore.set (enrolmentAddress PayEnrolMemo.fixtureMemo.miniKey)
    (some ⟨PayEnrolMemo.fixtureMemo.sshBlob, 108, some 1, 500168, 900⟩)).set
    (sshIndexAddress PayEnrolMemo.fixtureMemo.sshBlob) (some PayEnrolMemo.fixtureMemo.miniKey)

/-- Satisfiable pole of the enrolment shape. -/
theorem enrolled_fixture_law : Law enrolledFixture := by decide +kernel

/-- Refuting pole: an enrolment row whose ssh key is not indexed is not lawful. -/
theorem unindexed_enrolment_unlawful :
    ¬ Law (genesisStore.set (enrolmentAddress PayEnrolMemo.fixtureMemo.miniKey)
      (some ⟨PayEnrolMemo.fixtureMemo.sshBlob, 108, some 1, 500168, 900⟩)) := by decide +kernel

/-- Refuting pole: an ssh index row naming a key with no enrolment is not lawful. -/
theorem dangling_ssh_index_unlawful :
    ¬ Law (genesisStore.set (sshIndexAddress PayEnrolMemo.fixtureMemo.sshBlob)
      (some PayEnrolMemo.fixtureMemo.miniKey)) := by decide +kernel

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
#assert_axioms enrolled_fixture_law
#assert_axioms unindexed_enrolment_unlawful
#assert_axioms dangling_ssh_index_unlawful

end Minidregg.Kernel.PayCell
