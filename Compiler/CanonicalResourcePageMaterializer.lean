/-
# Compiler.CanonicalResourcePageMaterializer

The existing finite Book is the wire carrier. Accounts and both sparse-map
supports are sorted; all nonzero coordinates are encoded, including balances
outside the registered account set. There is no bounded-book twin or caller
post-state. Absent book fields remain distinct from a present empty book.

Version 2 replaces the countability/unary representation and length roots.
The codec is mechanically composed from compact first-order stream codecs;
decoding additionally requires exact re-encoding. State roots use the actual
Lean cSHAKE256 implementation. Hash collision resistance is an explicit
compared-pair premise, never universal injectivity into a finite digest.
-/
import Compiler.FiniteDependentMapCodec
import Compiler.Sp800185Cshake256
import Theory.CanonicalResourceKernel
import Mathlib.Data.Finset.Sort

namespace Minidregg.Compiler.CanonicalResourcePageMaterializer
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false
local instance : DecidableEq CanonicalResourceKernel.schema.Field :=
  inferInstanceAs (DecidableEq CanonicalResourceKernel.Field)
local instance : DecidableEq CanonicalResourceKernel.schema.Resource :=
  inferInstanceAs (DecidableEq Empty)

/-- Re-encoding is part of decoding: alternative integer encodings, duplicate
map entries, zero entries, reordered supports, and trailing bytes are refused. -/
def canonicalCodec {α : Type} (codec : LawfulCodec α) : LawfulCodec α where
  encode := codec.encode
  decode bytes := do
    let value ← codec.decode bytes
    if codec.encode value = bytes then some value else none
  decode_encode := by intro value; simp [codec.decode_encode]

theorem canonicalCodec_accepted_bytes {α : Type} (codec : LawfulCodec α)
    {bytes : List UInt8} {value : α}
    (accepted : (canonicalCodec codec).decode bytes = some value) :
    codec.encode value = bytes := by
  simp only [canonicalCodec, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨decoded, _, accepted⟩ := accepted
  split_ifs at accepted with exactBytes
  · cases Option.some.inj accepted; exact exactBytes

variable {K V : Type} [DecidableEq K] [Zero V]

/-- Product view of the shared dependent sparse-map reconstruction. -/
def fromEntries (values : List (K × V)) : Π₀ _ : K, V :=
  FiniteDependentMapCodec.fromEntries
    (values.map fun entry => (⟨entry.1, entry.2⟩ : Sigma (fun _ : K => V)))

theorem fromEntries_map (keys : List K) (f : Π₀ _ : K, V) (key : K) :
    fromEntries (keys.map (fun k => (k, f k))) key =
      if key ∈ keys then f key else 0 := by
  simpa [fromEntries, List.map_map] using
    FiniteDependentMapCodec.fromEntries_map keys f key

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

def intWire : Int → Sum Nat Nat
  | .ofNat value => .inl value
  | .negSucc value => .inr value

def intOfWire : Sum Nat Nat → Int
  | .inl value => .ofNat value
  | .inr value => .negSucc value

def intStream : StreamCodec Int :=
  StreamCodec.xmap (StreamCodec.sum StreamCodec.nat StreamCodec.nat)
    intWire intOfWire (by intro value; cases value <;> rfl)

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

abbrev BookTuple := List Nat × List ((Nat × Nat) × Int) × List (Nat × Option LeaseRecord)

def bookTuple (book : Book) : BookTuple :=
  (book.accounts.sort (· ≤ ·), entries book.balances, entries book.leaseRecords)

def bookOfTuple (wire : BookTuple) : Book where
  accounts := wire.1.toFinset
  balances := fromEntries wire.2.1
  leaseRecords := fromEntries wire.2.2

@[simp] theorem bookOfTuple_bookTuple (book : Book) : bookOfTuple (bookTuple book) = book := by
  cases book
  simp only [bookTuple, bookOfTuple, Finset.sort_toFinset, fromEntries_entries]

def bookTupleStream : StreamCodec BookTuple :=
  StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.product
      (StreamCodec.list (StreamCodec.product
        (StreamCodec.product StreamCodec.nat StreamCodec.nat) intStream))
      (StreamCodec.list (StreamCodec.product StreamCodec.nat
        (StreamCodec.option leaseStream))))

def bookStream : StreamCodec Book :=
  StreamCodec.xmap bookTupleStream bookTuple bookOfTuple bookOfTuple_bookTuple

def stateOfOption : Option Book → LogicalState CanonicalResourceKernel.schema
  | none => { fields := 0, resources := fun resource => nomatch resource }
  | some book =>
    { fields := (0 : FieldStore CanonicalResourceKernel.schema).write .book book
      resources := fun resource => nomatch resource }

def bookAt (state : LogicalState CanonicalResourceKernel.schema) : Option Book :=
  state.fields .book

@[simp] theorem bookAt_some (book : Book) :
    bookAt (stateOfOption (some book)) = some book := by
  simp [bookAt, stateOfOption]
  rfl

theorem state_ext (state : LogicalState CanonicalResourceKernel.schema) :
    state = stateOfOption (bookAt state) := by
  cases state with
  | mk fields resources =>
    have resourcesExact : resources = fun resource => nomatch resource := by
      funext resource; exact Empty.elim resource
    cases present : fields .book with
    | none =>
      have fieldsExact : fields = (0 : FieldStore CanonicalResourceKernel.schema) := by
        apply DFinsupp.ext
        intro field; cases field; simpa using present
      rw [fieldsExact, resourcesExact]; rfl
    | some book =>
      have fieldsExact : fields = (0 : FieldStore CanonicalResourceKernel.schema).write .book book := by
        apply DFinsupp.ext
        intro field; cases field; simp [present]
      rw [fieldsExact, resourcesExact]; rfl

def stateStream : StreamCodec (LogicalState CanonicalResourceKernel.schema) :=
  StreamCodec.xmap (StreamCodec.option bookStream) bookAt stateOfOption
    (by intro state; exact (state_ext state).symm)

def wireVersion : Nat := 2

def wireFrame : List UInt8 := [68,82,69,71,71,47,82,69,83,79,85,82,67,69,47,2]

def framedCodec {α : Type} (kind : UInt8) (codec : LawfulCodec α) : LawfulCodec α where
  encode value := wireFrame ++ kind :: codec.encode value
  decode
    | 68 :: 82 :: 69 :: 71 :: 71 :: 47 :: 82 :: 69 :: 83 :: 79 :: 85 :: 82 :: 67 :: 69 :: 47 :: 2 :: found :: payload =>
      if found = kind then codec.decode payload else none
    | _ => none
  decode_encode := by intro value; simp [wireFrame, codec.decode_encode]

def stateCodec : LawfulCodec (LogicalState CanonicalResourceKernel.schema) :=
  canonicalCodec (framedCodec 0 stateStream.toLawful)

def rootCustomization : List UInt8 := "DREGG.RESOURCE.STATE/v2".toUTF8.toList

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def materializer : Materializer CanonicalResourceKernel.schema Digest where
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

def operationOfWire : OperationWire → Option Operation
  | (0, [source, destination, asset, amount]) => some (.transfer source destination asset amount)
  | (1, [asset, destination, amount]) => some (.mint asset destination amount)
  | (2, [source, asset, amount]) => some (.burn source asset amount)
  | (3, [payer, collector, asset, amount]) => some (.fee payer collector asset amount)
  | (4, [leaseId, holder, lessor, asset, rate, epochs, starts]) =>
      some (.lease leaseId holder lessor asset rate epochs starts)
  | _ => none

@[simp] theorem operationOfWire_operationWire (operation : Operation) :
    operationOfWire (operationWire operation) = some operation := by cases operation <;> rfl

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

def operationCodec : LawfulCodec Operation :=
  canonicalCodec (framedCodec 1 operationStream.toLawful)

abbrev PostingTuple := Nat × Nat × Nat × Nat

def postingStream : StreamCodec Posting :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun posting => (posting.source, posting.destination, posting.asset, posting.amount))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro posting; rfl)

def postingCodec : LawfulCodec Posting :=
  canonicalCodec (framedCodec 2 postingStream.toLawful)

/-- The effect preimage is itself a derived codec, so operation/posting
separation and complete consumption follow the common product law. -/
def effectSourceCodec : LawfulCodec (Operation × Posting) :=
  canonicalCodec (framedCodec 4 (StreamCodec.product operationStream postingStream).toLawful)

def batchStream : StreamCodec Batch :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list StreamCodec.nat)
      (StreamCodec.list operationStream))
    (fun batch => (batch.registrations, batch.operations))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro batch; rfl)

def batchCodec : LawfulCodec Batch :=
  canonicalCodec (framedCodec 3 batchStream.toLawful)

theorem codec_encode_injective {α : Type} (codec : LawfulCodec α) :
    Function.Injective codec.encode := by
  intro left right same
  have decoded := congrArg codec.decode same
  simpa only [codec.decode_encode, Option.some.injEq] using decoded

theorem state_decode_encode (state : LogicalState CanonicalResourceKernel.schema) :
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

private theorem decode_present_tuple (wire : BookTuple) :
    (framedCodec 0 stateStream.toLawful).decode
      (wireFrame ++ [0, 1] ++ bookTupleStream.encode wire) =
        some (stateOfOption (some (bookOfTuple wire))) := by
  have parsed := bookTupleStream.decodePrefix_encode wire []
  simp only [List.append_nil] at parsed
  simp [framedCodec, wireFrame, stateStream, StreamCodec.toLawful,
    StreamCodec.xmap, StreamCodec.option, bookStream, parsed]

/-- Exact rejection law for every raw finite book tuple, not a finite test
corpus. Account order and exact nonzero map support are forced on input. -/
theorem decode_tuple_eq_none_iff (wire : BookTuple) :
    stateCodec.decode (wireFrame ++ [0, 1] ++ bookTupleStream.encode wire) = none ↔
      bookTuple (bookOfTuple wire) ≠ wire := by
  simp only [stateCodec, canonicalCodec, decode_present_tuple]
  simp [framedCodec, stateStream, StreamCodec.toLawful, StreamCodec.xmap,
    StreamCodec.option, bookAt_some, bookStream]
  constructor
  · intro different equal
    exact different (congrArg bookTupleStream.encode equal)
  · intro different equal
    exact different (codec_encode_injective bookTupleStream.toLawful equal)

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
      bookTupleStream.encode ([7, 7], [], [])) = none := by
  rw [decode_tuple_eq_none_iff]
  intro same
  have unique : (bookTuple (bookOfTuple ([7, 7], [], []))).1.Nodup :=
    (bookOfTuple ([7, 7], [], [])).accounts.sort_nodup (· ≤ ·)
  rw [same] at unique
  simp at unique

theorem rejects_duplicate_balance_coordinates :
    stateCodec.decode (wireFrame ++ [0, 1] ++
      bookTupleStream.encode ([1], [((1, 0), 5), ((1, 0), 5)], [])) = none := by
  rw [decode_tuple_eq_none_iff]
  intro same
  have unique := entries_keys_nodup
    (bookOfTuple ([1], [((1, 0), 5), ((1, 0), 5)], [])).balances
  change ((bookTuple (bookOfTuple ([1], [((1, 0), 5), ((1, 0), 5)], []))).2.1.map Prod.fst).Nodup at unique
  rw [same] at unique
  simp at unique

theorem rejects_zero_balance_support :
    stateCodec.decode (wireFrame ++ [0, 1] ++
      bookTupleStream.encode ([1], [((1, 0), 0)], [])) = none := by
  rw [decode_tuple_eq_none_iff]
  intro same
  have member : ((1, 0), (0 : Int)) ∈
      (bookTuple (bookOfTuple ([1], [((1, 0), 0)], []))).2.1 := by rw [same]; simp
  exact entries_nonzero _ _ member rfl

theorem rejects_unsorted_accounts :
    stateCodec.decode (wireFrame ++ [0, 1] ++
      bookTupleStream.encode ([2, 1], [], [])) = none := by
  rw [decode_tuple_eq_none_iff]
  intro same
  have ordered : (bookTuple (bookOfTuple ([2, 1], [], []))).1.Pairwise (· ≤ ·) :=
    (bookOfTuple ([2, 1], [], [])).accounts.pairwise_sort (· ≤ ·)
  rw [same] at ordered
  norm_num at ordered

theorem rejects_unknown_operation :
    operationCodec.decode (wireFrame ++ [1] ++
      operationWireStream.encode (17, [])) = none := by decide

theorem preserves_hidden_balance_coordinate :
    stateCodec.decode (stateCodec.encode (stateOfOption (some witnessHiddenBook))) =
      some (stateOfOption (some witnessHiddenBook)) :=
  stateCodec.decode_encode _

structure Collision (left right : LogicalState CanonicalResourceKernel.schema) : Prop where
  statesDifferent : left ≠ right
  bytesDifferent : stateCodec.encode left ≠ stateCodec.encode right
  rootsEqual : rootBytes (stateCodec.encode left) = rootBytes (stateCodec.encode right)

theorem collision_of_root_eq_of_ne {left right : LogicalState CanonicalResourceKernel.schema}
    (different : left ≠ right)
    (same : rootBytes (stateCodec.encode left) = rootBytes (stateCodec.encode right)) :
    Collision left right :=
  ⟨different, fun bytes => different (codec_encode_injective stateCodec bytes), same⟩

def PairBindingPremise (left right : LogicalState CanonicalResourceKernel.schema) : Prop :=
  ¬ Collision left right

theorem state_eq_of_root_eq {left right : LogicalState CanonicalResourceKernel.schema}
    (binding : PairBindingPremise left right)
    (same : rootBytes (stateCodec.encode left) = rootBytes (stateCodec.encode right)) :
    left = right := by
  by_contra different
  exact binding (collision_of_root_eq_of_ne different same)

end Minidregg.Compiler.CanonicalResourcePageMaterializer

/- Existing consumers retain their API name, now definitionally the concrete
materializer above. The countability-selected materializer has been deleted. -/
namespace Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.CellState

abbrev materializer := Minidregg.Compiler.CanonicalResourcePageMaterializer.materializer

def witnessCell : Materialized materializer := materialize materializer witnessLogical

@[simp] theorem witnessCell_logicalBook : logicalBook witnessCell.logical = witnessBook := by
  simp [witnessCell, witnessLogical, logicalBook, materialize, FieldStore.read]

noncomputable def witnessMintAccepted : Accepted witnessCell (.mint 0 1 2) :=
  Accepted.ofAdmission (by simpa using witnessMintAdmission)

noncomputable def witnessBirthAccepted : AcceptedBatch witnessCell witnessBirthBatch :=
  AcceptedBatch.ofAdmission (by simpa using witnessBirthBatch_admitted)

theorem witnessBirthAccepted_conserves (asset : AssetId) :
    (logicalBook witnessBirthAccepted.post.logical).totalAsset asset =
      (logicalBook witnessCell.logical).totalAsset asset :=
  witnessBirthAccepted.conserves asset

end Minidregg.Theory.CanonicalResourceKernel
