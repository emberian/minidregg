/-
# Compiler.CanonicalResourcePageMaterializer

The existing finite Book is the wire carrier. Accounts and the three
sparse-map supports (balances, leases, floors) are sorted; all nonzero coordinates are encoded, including balances
outside the registered account set. There is no bounded-book twin or caller
post-state. Absent book fields remain distinct from a present empty book.

Version 2 replaced the countability/unary representation and length roots.
Version 3 adds the Book's floors section and the `setFloor`/`sweep`
operations; version-2 frames are refused, not reinterpreted.
The codec is mechanically composed from compact first-order stream codecs;
decoding additionally requires exact re-encoding. State roots use the actual
Lean cSHAKE256 implementation. Hash collision resistance is an explicit
compared-pair premise, never universal injectivity into a finite digest.
-/
module

public import Compiler.FiniteDependentMapCodec
public import Compiler.IntStream
public import Compiler.Sp800185Cshake256
public import Theory.CanonicalResourceKernel
public import Mathlib.Data.Finset.Sort

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

namespace Minidregg.Compiler.CanonicalResourcePageMaterializer
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Store
open Minidregg.Compiler.IntStream (intStream)
set_option autoImplicit false

variable {K V : Type} [DecidableEq K] [Zero V]

/-- Product view of the shared dependent sparse-map reconstruction. -/
def fromEntries (values : List (K × V)) : Π₀ _ : K, V :=
  FiniteDependentMapCodec.fromEntries
    (values.map fun entry => (⟨entry.1, entry.2⟩ : Sigma (fun _ : K => V)))

theorem fromEntries_map (keys : List K) (f : Π₀ _ : K, V) (key : K) :
    fromEntries (keys.map (fun k => (k, f k))) key =
      if key ∈ keys then f key else 0 := by
  have hsimpa :=
    FiniteDependentMapCodec.fromEntries_map keys f key
  simp [fromEntries, List.map_map] at hsimpa ⊢
  exact hsimpa

/-- The product view preserves the existing resource wire tuple exactly. -/
def entries [LinearOrder K] [DecidableEq V] (f : Π₀ _ : K, V) : List (K × V) :=
  (FiniteDependentMapCodec.entries f).map fun entry => (entry.1, entry.2)

@[simp] theorem entries_eq [LinearOrder K] [DecidableEq V] (f : Π₀ _ : K, V) :
    entries f = (f.support.sort (· ≤ ·)).map (fun key => (key, f key)) := by
  simp [entries, FiniteDependentMapCodec.entries, List.map_map]

theorem fromEntries_entries [LinearOrder K] [DecidableEq V] (f : Π₀ _ : K, V) :
    fromEntries (entries f) = f := by
  simpa [fromEntries, entries, List.map_map, Function.comp_def] using
    FiniteDependentMapCodec.fromEntries_entries f

/-- Pair order is pinned by the injective natural pairing, not insertion order. -/
local instance accountAssetOrder : LinearOrder (AccountId × AssetId) :=
  LinearOrder.lift' Nat.pairEquiv Nat.pairEquiv.injective

abbrev LeaseTuple := Nat × Nat × Nat × Nat × Nat × Nat

def leaseTupleStream : StreamCodec LeaseTuple :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))))

def leaseStream : StreamCodec LeaseRecord :=
  StreamCodec.xmap leaseTupleStream
    (fun lease => (lease.holder, lease.lessor, lease.asset, lease.prepaid,
      lease.startsAt, lease.expiresAt))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2⟩)
    (by intro lease; rfl)

abbrev BookTuple := List Nat × List ((Nat × Nat) × Int) × List (Nat × Option LeaseRecord) ×
  List ((Nat × Nat) × Nat)

def bookTuple (book : Book) : BookTuple :=
  (book.accounts.sort (· ≤ ·), entries book.balances, entries book.leaseRecords,
    entries book.floors)

def bookOfTuple (wire : BookTuple) : Book where
  accounts := wire.1.toFinset
  balances := fromEntries wire.2.1
  leaseRecords := fromEntries wire.2.2.1
  floors := fromEntries wire.2.2.2

@[simp] theorem bookOfTuple_bookTuple (book : Book) : bookOfTuple (bookTuple book) = book := by
  cases book
  simp only [bookTuple, bookOfTuple, Finset.sort_toFinset, fromEntries_entries]

def bookTupleStream : StreamCodec BookTuple :=
  StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.product
      (StreamCodec.list (StreamCodec.product
        (StreamCodec.product StreamCodec.nat StreamCodec.nat) intStream))
      (StreamCodec.product
        (StreamCodec.list (StreamCodec.product StreamCodec.nat
          (StreamCodec.option leaseStream)))
        (StreamCodec.list (StreamCodec.product
          (StreamCodec.product StreamCodec.nat StreamCodec.nat) StreamCodec.nat))))

/-- The lax tuple codec above spells every tuple, including unsorted,
duplicated and explicit-zero ones; `bookStream` spells only canonical books
and REFUSES the rest in the stream decoder (sorted strict account list, strictly
key-sorted non-zero map entries: balances, leases, floors). Its bytes are the tuple codec's bytes at the
canonical tuple (`bookStream_encode`). -/
def bookStream : StreamCodec Book :=
  StreamCodec.xmap
    (StreamCodec.product (FiniteDependentMapCodec.finsetStream StreamCodec.nat)
      (StreamCodec.product
        (FiniteDependentMapCodec.mapStream (StreamCodec.product StreamCodec.nat StreamCodec.nat)
          (fun _ => intStream))
        (StreamCodec.product
          (FiniteDependentMapCodec.mapStream StreamCodec.nat (fun _ => StreamCodec.option leaseStream))
          (FiniteDependentMapCodec.mapStream (StreamCodec.product StreamCodec.nat StreamCodec.nat)
            (fun _ => StreamCodec.nat)))))
    (fun book => (book.accounts, book.balances, book.leaseRecords, book.floors))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro book; rfl)

private theorem encodeMany_entryStream {K V : Type} (keyStream : StreamCodec K)
    (valueStream : StreamCodec V) (items : List (Sigma (fun _ : K => V))) :
    StreamCodec.encodeMany (FiniteDependentMapCodec.entryStream keyStream (fun _ => valueStream)) items =
      StreamCodec.encodeMany (StreamCodec.product keyStream valueStream)
        (items.map fun entry => (entry.1, entry.2)) := by
  induction items with
  | nil => rfl
  | cons entry rest ih =>
      simp only [StreamCodec.encodeMany, List.map_cons, ih]
      rfl

private theorem list_entryStream_encode {K V : Type} (keyStream : StreamCodec K)
    (valueStream : StreamCodec V) (items : List (Sigma (fun _ : K => V))) :
    (StreamCodec.list (FiniteDependentMapCodec.entryStream keyStream (fun _ => valueStream))).encode items =
      (StreamCodec.list (StreamCodec.product keyStream valueStream)).encode
        (items.map fun entry => (entry.1, entry.2)) := by
  simp only [StreamCodec.list, List.length_map, encodeMany_entryStream]

/-- The canonical book codec writes exactly the tuple codec's bytes at the
canonical tuple: the encoding did not change, only the decoder's refusals. -/
theorem bookStream_encode (book : Book) :
    bookStream.encode book = bookTupleStream.encode (bookTuple book) := by
  simp only [bookStream, bookTupleStream, StreamCodec.xmap, StreamCodec.product,
    FiniteDependentMapCodec.finsetStream_encode, FiniteDependentMapCodec.mapStream_encode,
    list_entryStream_encode, bookTuple, entries]

def stateOfOption : Option Book → Store CanonicalResourceKernel.layout
  | none => 0
  | some book => (0 : Store CanonicalResourceKernel.layout).set bookAddress (some book)

def bookAt (state : Store CanonicalResourceKernel.layout) : Option Book :=
  state bookAddress

@[simp] theorem bookAt_some (book : Book) :
    bookAt (stateOfOption (some book)) = some book := by
  simp [bookAt, stateOfOption]

theorem state_ext (state : Store CanonicalResourceKernel.layout) :
    state = stateOfOption (bookAt state) := by
  apply DFinsupp.ext
  rintro ⟨field, key⟩
  cases field
  cases key
  cases present : state bookAddress with
  | none => simp [bookAt, stateOfOption, present]
  | some book => simp [bookAt, stateOfOption, present]

def stateStream : StreamCodec (Store CanonicalResourceKernel.layout) :=
  StreamCodec.xmap (StreamCodec.option bookStream) bookAt stateOfOption
    (by intro state; exact (state_ext state).symm)
    (by intro wire; cases wire <;> simp [bookAt, stateOfOption])

def wireVersion : Nat := 3

def wireFrame : List UInt8 := [68,82,69,71,71,47,82,69,83,79,85,82,67,69,47,3]

/-- The resource frame and the codec's kind byte, CHECKED, then one value.
Every stream below is canonical, so the decoder accepts exactly the encodings
(`framedCodec_decode_iff`): alternative integer encodings, duplicate map
entries, zero entries, reordered supports and trailing bytes are refused by the
streams themselves, with no re-encode. -/
def framedCodec {α : Type} (kind : UInt8) (stream : StreamCodec α) : LawfulCodec α :=
  (StreamCodec.framed (wireFrame ++ [kind]) stream).toLawful

theorem framedCodec_encode {α : Type} (kind : UInt8) (stream : StreamCodec α) (value : α) :
    (framedCodec kind stream).encode value = wireFrame ++ kind :: stream.encode value := by
  simp [framedCodec, StreamCodec.toLawful, StreamCodec.framed_encode]

theorem framedCodec_canonical {α : Type} (kind : UInt8) (stream : StreamCodec α)
    {bytes : List UInt8} {value : α} (accepted : (framedCodec kind stream).decode bytes = some value) :
    (framedCodec kind stream).encode value = bytes :=
  StreamCodec.toLawful_canonical _ bytes value accepted

theorem framedCodec_decode_iff {α : Type} (kind : UInt8) (stream : StreamCodec α)
    (bytes : List UInt8) (value : α) :
    (framedCodec kind stream).decode bytes = some value ↔
      (framedCodec kind stream).encode value = bytes :=
  StreamCodec.toLawful_decode_iff _ bytes value

def stateCodec : LawfulCodec (Store CanonicalResourceKernel.layout) :=
  framedCodec 0 stateStream

def rootCustomization : List UInt8 := "DREGG.RESOURCE.STATE/v3".toUTF8.toList

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def materializer : Materializer CanonicalResourceKernel.layout Digest where
  codec := stateCodec
  rootBytes := rootBytes

abbrev OperationWire := Nat × List Nat

def operationWire : Operation → OperationWire
  | .transfer source destination asset amount => (0, [source, destination, asset, amount])
  | .mint asset destination amount => (1, [asset, destination, amount])
  | .burn source asset amount => (2, [source, asset, amount])
  | .fee payer collector asset amount => (3, [payer, collector, asset, amount])
  | .lease leaseId holder lessor asset rate epochs starts =>
      (4, [leaseId, holder, lessor, asset, rate, epochs, starts])
  | .setFloor asset account floor => (5, [asset, account, floor])
  | .sweep holder commons asset permille epochs amount =>
      (6, [holder, commons, asset, permille, epochs, amount])

def operationOfWire : OperationWire → Option Operation
  | (0, [source, destination, asset, amount]) => some (.transfer source destination asset amount)
  | (1, [asset, destination, amount]) => some (.mint asset destination amount)
  | (2, [source, asset, amount]) => some (.burn source asset amount)
  | (3, [payer, collector, asset, amount]) => some (.fee payer collector asset amount)
  | (4, [leaseId, holder, lessor, asset, rate, epochs, starts]) =>
      some (.lease leaseId holder lessor asset rate epochs starts)
  | (5, [asset, account, floor]) => some (.setFloor asset account floor)
  | (6, [holder, commons, asset, permille, epochs, amount]) =>
      some (.sweep holder commons asset permille epochs amount)
  | _ => none

@[simp] theorem operationOfWire_operationWire (operation : Operation) :
    operationOfWire (operationWire operation) = some operation := by cases operation <;> rfl

theorem operationWire_of_operationOfWire {wire : OperationWire} {operation : Operation}
    (decoded : operationOfWire wire = some operation) : operationWire operation = wire := by
  unfold operationOfWire at decoded
  split at decoded <;> first | (cases decoded; rfl) | cases decoded

def operationWireStream : StreamCodec OperationWire :=
  StreamCodec.product StreamCodec.nat (StreamCodec.list StreamCodec.nat)

def operationStream : StreamCodec Operation where
  encode operation := operationWireStream.encode (operationWire operation)
  decodePrefix bytes := do
    let (wire, suffix) ← operationWireStream.decodePrefix bytes
    let operation ← operationOfWire wire
    some (operation, suffix)
  decodePrefix_encode := by
    intro operation suffix
    simp [operationWireStream.decodePrefix_encode]
  encode_decodePrefix := by
    intro bytes operation suffix decoded
    cases wireOk : operationWireStream.decodePrefix bytes with
    | none => simp [wireOk] at decoded
    | some pair =>
      obtain ⟨wire, rest⟩ := pair
      cases operationOk : operationOfWire wire with
      | none => simp [wireOk, operationOk] at decoded
      | some decodedOperation =>
        simp only [wireOk, operationOk, bind, Option.bind, Option.some.injEq,
          Prod.mk.injEq] at decoded
        obtain ⟨rfl, rfl⟩ := decoded
        change operationWireStream.encode (operationWire decodedOperation) ++ rest = bytes
        rw [operationWire_of_operationOfWire operationOk]
        exact operationWireStream.encode_decodePrefix _ _ _ wireOk

def operationCodec : LawfulCodec Operation :=
  framedCodec 1 operationStream

abbrev PostingTuple := Nat × Nat × Nat × Nat

def postingStream : StreamCodec Posting :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun posting => (posting.source, posting.destination, posting.asset, posting.amount))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro posting; rfl)

def postingCodec : LawfulCodec Posting :=
  framedCodec 2 postingStream

/-- The effect preimage is itself a derived codec, so operation/posting
separation and complete consumption follow the common product law. -/
def effectSourceCodec : LawfulCodec (Operation × Posting) :=
  framedCodec 4 (StreamCodec.product operationStream postingStream)

/-- A batch on the wire: registrations, operations, then deregistrations. The
deregistration list is part of every batch's bytes (an empty list is still
encoded), so a two-list batch from before deregistration fails to decode. -/
def batchStream : StreamCodec Batch :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list StreamCodec.nat)
      (StreamCodec.product (StreamCodec.list operationStream) (StreamCodec.list StreamCodec.nat)))
    (fun batch => (batch.registrations, batch.operations, batch.deregistrations))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro batch; rfl)

def batchCodec : LawfulCodec Batch :=
  framedCodec 3 batchStream

theorem codec_encode_injective {α : Type} (codec : LawfulCodec α) :
    Function.Injective codec.encode := by
  intro left right same
  have decoded := congrArg codec.decode same
  simpa only [codec.decode_encode, Option.some.injEq] using decoded

theorem state_decode_encode (state : Store CanonicalResourceKernel.layout) :
    stateCodec.decode (stateCodec.encode state) = some state :=
  stateCodec.decode_encode state

theorem operation_decode_encode (operation : Operation) :
    operationCodec.decode (operationCodec.encode operation) = some operation :=
  operationCodec.decode_encode operation

theorem batch_decode_encode (batch : Batch) :
    batchCodec.decode (batchCodec.encode batch) = some batch :=
  batchCodec.decode_encode batch

theorem absent_distinct_from_empty_book :
    stateCodec.encode (stateOfOption none) ≠
      stateCodec.encode (stateOfOption (some Book.empty)) := by decide

/-- The migration is a real wire break: old frame version 1 is refused. -/
theorem reject_version_one (payload : List UInt8) :
    stateCodec.decode
      ([68,82,69,71,71,47,82,69,83,79,85,82,67,69,47,1] ++ payload) = none := rfl

/-- So is version 2, the Book without floors: an old state is refused, never
read as a Book whose floors are all zero. -/
theorem reject_version_two (payload : List UInt8) :
    stateCodec.decode
      ([68,82,69,71,71,47,82,69,83,79,85,82,67,69,47,2] ++ payload) = none := rfl

/-- The superseded countability materializer emitted only zero-byte unary
strings; they are all refused, including the empty string. -/
theorem reject_legacy_unary (count : Nat) :
    stateCodec.decode (List.replicate count 0) = none := by
  cases count <;> rfl

/-- Same-size operations remain distinct source bytes. Hashes below consume
those bytes, never merely their lengths. -/
theorem same_size_distinct_operations :
    (operationCodec.encode (.fee 1 2 0 1)).length =
      (operationCodec.encode (.fee 1 2 0 2)).length ∧
    operationCodec.encode (.fee 1 2 0 1) ≠ operationCodec.encode (.fee 1 2 0 2) := by decide

theorem operation_wire_is_compact :
    (operationCodec.encode (.transfer 1000000 2000000 3000000 4000000)).length < 64 := by decide

theorem bookTupleStream_encode_injective : Function.Injective bookTupleStream.encode :=
  codec_encode_injective bookTupleStream.toLawful

/-- Exact rejection law for every raw finite book tuple, not a finite test
corpus. Account order and exact nonzero map support are forced on input. -/
theorem decode_tuple_eq_none_iff (wire : BookTuple) :
    stateCodec.decode (wireFrame ++ [0, 1] ++ bookTupleStream.encode wire) = none ↔
      bookTuple (bookOfTuple wire) ≠ wire := by
  constructor
  · intro refused canonical
    have encoded : stateCodec.encode (stateOfOption (some (bookOfTuple wire))) =
        wireFrame ++ [0, 1] ++ bookTupleStream.encode wire := by
      change wireFrame ++ 0 :: (StreamCodec.option bookStream).encode
          (bookAt (stateOfOption (some (bookOfTuple wire)))) = _
      rw [bookAt_some]
      change wireFrame ++ 0 :: 1 :: bookStream.encode (bookOfTuple wire) = _
      rw [bookStream_encode, canonical]
      simp
    have accepted := (framedCodec_decode_iff 0 stateStream _ _).mpr encoded
    change stateCodec.decode _ = some _ at accepted
    rw [refused] at accepted
    cases accepted
  · intro different
    cases decoded : stateCodec.decode (wireFrame ++ [0, 1] ++ bookTupleStream.encode wire) with
    | none => rfl
    | some state =>
      exfalso
      have encoded := (framedCodec_decode_iff 0 stateStream _ _).mp decoded
      change wireFrame ++ 0 :: (StreamCodec.option bookStream).encode (bookAt state) = _ at encoded
      cases present : bookAt state with
      | none =>
          rw [present] at encoded
          simp [StreamCodec.option] at encoded
      | some book =>
          rw [present] at encoded
          change wireFrame ++ 0 :: 1 :: bookStream.encode book = _ at encoded
          rw [bookStream_encode] at encoded
          simp only [List.append_assoc, List.append_cancel_left_eq, List.cons_append,
            List.nil_append, List.cons.injEq, true_and] at encoded
          have same := bookTupleStream_encode_injective encoded
          apply different
          rw [← same, bookOfTuple_bookTuple]

private theorem entries_keys_nodup {K V : Type} [LinearOrder K] [Zero V] [DecidableEq V]
    (values : Π₀ _ : K, V) : ((entries values).map Prod.fst).Nodup := by
  simpa [entries_eq, List.map_map, Function.comp_def] using values.support.sort_nodup (· ≤ ·)

private theorem entries_nonzero {K V : Type} [LinearOrder K] [Zero V] [DecidableEq V]
    (values : Π₀ _ : K, V) (entry : K × V) (member : entry ∈ entries values) :
    entry.2 ≠ 0 := by
  rw [entries_eq] at member
  obtain ⟨key, present, same⟩ := List.mem_map.mp member
  rw [← same]
  exact (DFinsupp.mem_support_toFun _ _).mp ((Finset.mem_sort _).mp present)

/-- Concrete adversarial payloads exercise the strict decoder, rather than
merely proving that the canonical encoder never emits the bad shape. -/
theorem rejects_duplicate_accounts :
    stateCodec.decode (wireFrame ++ [0, 1] ++
      bookTupleStream.encode ([7, 7], [], [], [])) = none := by
  rw [decode_tuple_eq_none_iff]
  intro same
  have unique : (bookTuple (bookOfTuple ([7, 7], [], [], []))).1.Nodup :=
    (bookOfTuple ([7, 7], [], [], [])).accounts.sort_nodup (· ≤ ·)
  rw [same] at unique
  simp at unique

theorem rejects_duplicate_balance_coordinates :
    stateCodec.decode (wireFrame ++ [0, 1] ++
      bookTupleStream.encode ([1], [((1, 0), 5), ((1, 0), 5)], [], [])) = none := by
  rw [decode_tuple_eq_none_iff]
  intro same
  have unique := entries_keys_nodup
    (bookOfTuple ([1], [((1, 0), 5), ((1, 0), 5)], [], [])).balances
  change ((bookTuple (bookOfTuple ([1], [((1, 0), 5), ((1, 0), 5)], [], []))).2.1.map Prod.fst).Nodup at unique
  rw [same] at unique
  simp at unique

theorem rejects_zero_balance_support :
    stateCodec.decode (wireFrame ++ [0, 1] ++
      bookTupleStream.encode ([1], [((1, 0), 0)], [], [])) = none := by
  rw [decode_tuple_eq_none_iff]
  intro same
  have member : ((1, 0), (0 : Int)) ∈
      (bookTuple (bookOfTuple ([1], [((1, 0), 0)], [], []))).2.1 := by rw [same]; simp
  exact entries_nonzero _ _ member rfl

theorem rejects_unsorted_accounts :
    stateCodec.decode (wireFrame ++ [0, 1] ++
      bookTupleStream.encode ([2, 1], [], [], [])) = none := by
  rw [decode_tuple_eq_none_iff]
  intro same
  have ordered : (bookTuple (bookOfTuple ([2, 1], [], [], []))).1.Pairwise (· ≤ ·) :=
    (bookOfTuple ([2, 1], [], [], [])).accounts.pairwise_sort (· ≤ ·)
  rw [same] at ordered
  norm_num at ordered

theorem rejects_duplicate_floor_coordinates :
    stateCodec.decode (wireFrame ++ [0, 1] ++
      bookTupleStream.encode ([1], [], [], [((1, 0), 5), ((1, 0), 5)])) = none := by
  rw [decode_tuple_eq_none_iff]
  intro same
  have unique := entries_keys_nodup
    (bookOfTuple ([1], [], [], [((1, 0), 5), ((1, 0), 5)])).floors
  change ((bookTuple (bookOfTuple ([1], [], [], [((1, 0), 5), ((1, 0), 5)]))).2.2.2.map
    Prod.fst).Nodup at unique
  rw [same] at unique
  simp at unique

theorem rejects_zero_floor_support :
    stateCodec.decode (wireFrame ++ [0, 1] ++
      bookTupleStream.encode ([1], [], [], [((1, 0), 0)])) = none := by
  rw [decode_tuple_eq_none_iff]
  intro same
  have member : ((1, 0), (0 : Nat)) ∈
      (bookTuple (bookOfTuple ([1], [], [], [((1, 0), 0)]))).2.2.2 := by rw [same]; simp
  exact entries_nonzero _ _ member rfl

theorem rejects_unknown_operation :
    operationCodec.decode (wireFrame ++ [1] ++
      operationWireStream.encode (17, [])) = none := by decide

theorem preserves_hidden_balance_coordinate :
    stateCodec.decode (stateCodec.encode (stateOfOption (some witnessHiddenBook))) =
      some (stateOfOption (some witnessHiddenBook)) :=
  stateCodec.decode_encode _

end Minidregg.Compiler.CanonicalResourcePageMaterializer

/- Existing consumers retain their API name, now definitionally the concrete
materializer above. The countability-selected materializer has been deleted. -/
namespace Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.CellState

abbrev materializer := Minidregg.Compiler.CanonicalResourcePageMaterializer.materializer

def witnessCell : Materialized materializer := materialize materializer witnessLogical

@[simp] theorem witnessCell_logicalBook : logicalBook witnessCell.logical = witnessBook := by
  simp [witnessCell, witnessLogical, logicalBook, materialize]

theorem witnessMintAccepted : Accepted witnessCell (.mint 0 1 2) :=
  Accepted.ofAdmission (by simpa using witnessMintAdmission)

theorem witnessBirthAccepted : AcceptedBatch witnessCell witnessBirthBatch :=
  AcceptedBatch.ofAdmission (by simpa using witnessBirthBatch_admitted)

theorem witnessBirthAccepted_conserves (asset : AssetId) :
    (logicalBook witnessBirthAccepted.post.logical).totalAsset asset =
      (logicalBook witnessCell.logical).totalAsset asset :=
  witnessBirthAccepted.conserves asset

end Minidregg.Theory.CanonicalResourceKernel
