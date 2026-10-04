/-
# Kernel.SessionIndex — the accepted log's lookups, kept at append (deos efficiency B)

Two functions of the accepted log that the host recomputed from the whole list
on every request (scout D §2 hotspot 3):

* `Image.cellIds` — `(seed ids ++ every write's id).eraseDups`, quadratic in the
  log's writes, evaluated by every validation, every root-entry list and every
  cell enumeration;
* the first accepted index of a transaction id — `List.findIdx?`, a linear
  scan, on every receipt lookup (`NativeHost.historicalReceipt`).

Each is cached on the loaded image beside the presence and link indexes
(`DurableReceiverIO.Loaded.ids`, `.txs`), built once on open, advanced by one
record per append, and carries an exactness field. The cache is not a second
source of truth: its observable projections ARE the List functions' results,
by the theorems here (`CellIds.toList_eq`, `CellIds.contains_iff`,
`TxIndex.lookup_eq`), so a consumer switched from the List function to the
cache changes no result, by theorem rather than by test.

What the caches do not change: the image, its codec, the log, the world root,
every receipt. Nothing here is persisted; a reopen rebuilds both in one pass
over the log (`CellIds.ofImage`, `TxIndex.ofRecords`: linear, not quadratic).
-/
import Kernel.DurableReceiver
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas
import Theory.AssertAxioms

namespace Minidregg.Kernel.SessionIndex

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver

set_option autoImplicit false

/-- Digests hash by their value. -/
instance : Hashable Digest := ⟨fun digest => hash digest.value⟩

instance : LawfulHashable Digest where
  hash_eq a b same := by
    cases eq_of_beq same
    rfl

/-! ## Cell ids -/

/-- Every cell id an image enumerates: the order `Image.cellIds` lists them in,
and the set of them. -/
structure CellIds where
  order : Array CellId
  seen : Std.HashSet CellId

def CellIds.empty : CellIds := ⟨#[], ∅⟩

def CellIds.add (ids : CellIds) (id : CellId) : CellIds :=
  if ids.seen.contains id then ids else ⟨ids.order.push id, ids.seen.insert id⟩

def CellIds.addAll (ids : CellIds) (more : List CellId) : CellIds :=
  more.foldl CellIds.add ids

/-- The ids an image seeds or writes, with repeats, in log order: the list
`Image.cellIds` deduplicates. -/
def rawIds (image : Image) : List CellId :=
  image.seed.cells.map Prod.fst ++
    image.accepted.flatMap (fun record => record.writes.map DataWrite.cellId)

theorem cellIds_eq_rawIds (image : Image) : image.cellIds = (rawIds image).eraseDups := rfl

/-- The cache's two projections are the List function's: its order is
`raw.eraseDups`, its membership is membership in `raw`. -/
structure CellIds.Exact (ids : CellIds) (raw : List CellId) : Prop where
  order : ids.order.toList = raw.eraseDups
  seen : ∀ id, ids.seen.contains id = true ↔ id ∈ raw

theorem CellIds.empty_exact : CellIds.empty.Exact [] :=
  ⟨rfl, fun id => by simp [CellIds.empty]⟩

theorem eraseDups_singleton (id : CellId) : [id].eraseDups = [id] := by
  rw [List.eraseDups_cons]
  simp

theorem eraseDups_snoc (raw : List CellId) (id : CellId) :
    (raw ++ [id]).eraseDups = raw.eraseDups ++ (if id ∈ raw then [] else [id]) := by
  rw [List.eraseDups_append]
  by_cases member : id ∈ raw
  · simp [List.removeAll, member]
  · simp [List.removeAll, member, eraseDups_singleton]

theorem CellIds.add_exact {ids : CellIds} {raw : List CellId} (exact : ids.Exact raw)
    (id : CellId) : (ids.add id).Exact (raw ++ [id]) := by
  unfold CellIds.add
  by_cases member : id ∈ raw
  · have seen : ids.seen.contains id = true := (exact.seen id).mpr member
    rw [if_pos seen]
    refine ⟨?_, fun other => ?_⟩
    · rw [eraseDups_snoc, if_pos member, List.append_nil]
      exact exact.order
    · rw [exact.seen other, List.mem_append, List.mem_singleton]
      constructor
      · exact Or.inl
      · rintro (inside | rfl)
        · exact inside
        · exact member
  · have unseen : ¬ ids.seen.contains id = true := fun seen => member ((exact.seen id).mp seen)
    rw [if_neg unseen]
    refine ⟨?_, fun other => ?_⟩
    · rw [Array.toList_push, eraseDups_snoc, if_neg member, exact.order]
    · rw [Std.HashSet.contains_insert, Bool.or_eq_true, exact.seen other, List.mem_append,
        List.mem_singleton, beq_iff_eq]
      constructor
      · rintro (rfl | inside)
        · exact Or.inr rfl
        · exact Or.inl inside
      · rintro (inside | rfl)
        · exact Or.inr inside
        · exact Or.inl rfl

theorem CellIds.addAll_exact {ids : CellIds} {raw : List CellId} (exact : ids.Exact raw)
    (more : List CellId) : (ids.addAll more).Exact (raw ++ more) := by
  induction more generalizing ids raw with
  | nil => simpa [CellIds.addAll] using exact
  | cons id rest ih =>
      have step := ih (CellIds.add_exact exact id)
      rw [List.append_assoc, List.singleton_append] at step
      exact step

/-- One pass over the image: linear in its writes. -/
def CellIds.ofImage (image : Image) : CellIds :=
  CellIds.empty.addAll (rawIds image)

theorem CellIds.ofImage_exact (image : Image) : (CellIds.ofImage image).Exact (rawIds image) := by
  simpa using CellIds.addAll_exact CellIds.empty_exact (rawIds image)

/-- One accepted record's writes, added at append. -/
def CellIds.admit (ids : CellIds) (record : IntentRecord) : CellIds :=
  ids.addAll (record.writes.map DataWrite.cellId)

theorem rawIds_snoc (image : Image) (record : IntentRecord) :
    rawIds { image with accepted := image.accepted ++ [record] } =
      rawIds image ++ record.writes.map DataWrite.cellId := by
  simp [rawIds, List.flatMap_append, List.append_assoc]

theorem CellIds.admit_exact {ids : CellIds} {image : Image} (exact : ids.Exact (rawIds image))
    (record : IntentRecord) :
    (ids.admit record).Exact (rawIds { image with accepted := image.accepted ++ [record] }) := by
  rw [rawIds_snoc]
  exact CellIds.addAll_exact exact _

/-- **Refinement (enumeration)**: the cache's list is `Image.cellIds`. -/
theorem CellIds.toList_eq {ids : CellIds} {image : Image} (exact : ids.Exact (rawIds image)) :
    ids.order.toList = image.cellIds := by
  rw [cellIds_eq_rawIds]
  exact exact.order

/-- **Refinement (membership)**: the cache's set is membership in `Image.cellIds`. -/
theorem CellIds.contains_iff {ids : CellIds} {image : Image} (exact : ids.Exact (rawIds image))
    (id : CellId) : ids.seen.contains id = true ↔ id ∈ image.cellIds := by
  rw [exact.seen id, cellIds_eq_rawIds, List.mem_eraseDups]

/-! ## Transaction ids -/

/-- A transaction id's first accepted index: `findIdx?` over the log, the
function `NativeHost.historicalReceipt` selects a receipt by. -/
def firstIndex (records : List IntentRecord) (transactionId : TransactionId) : Option Nat :=
  records.findIdx? (fun record => record.transactionId == transactionId)

abbrev TxIndex := Std.HashMap TransactionId Nat

/-- Every lookup is the log's first index. -/
def TxIndex.Exact (txs : TxIndex) (records : List IntentRecord) : Prop :=
  ∀ transactionId, txs[transactionId]? = firstIndex records transactionId

theorem TxIndex.empty_exact : (∅ : TxIndex).Exact [] := by
  intro transactionId
  simp [firstIndex]

/-- The record at index `height` (0-based: the log held `height` records
before it). A transaction id already indexed keeps its first index. -/
def TxIndex.admitAt (txs : TxIndex) (height : Nat) (record : IntentRecord) : TxIndex :=
  txs.insertIfNew record.transactionId height

theorem firstIndex_snoc (records : List IntentRecord) (record : IntentRecord)
    (transactionId : TransactionId) :
    firstIndex (records ++ [record]) transactionId =
      (firstIndex records transactionId).or
        (if record.transactionId == transactionId then some records.length else none) := by
  unfold firstIndex
  rw [List.findIdx?_append]
  by_cases same : (record.transactionId == transactionId) = true
  · simp [List.findIdx?_cons, same]
  · simp [List.findIdx?_cons, same]

theorem TxIndex.admitAt_exact {txs : TxIndex} {records : List IntentRecord}
    (exact : txs.Exact records) (record : IntentRecord) :
    (txs.admitAt records.length record).Exact (records ++ [record]) := by
  intro transactionId
  unfold TxIndex.admitAt
  rw [Std.HashMap.getElem?_insertIfNew, firstIndex_snoc, exact transactionId]
  by_cases same : record.transactionId = transactionId
  · subst same
    have here := exact record.transactionId
    cases found : firstIndex records record.transactionId with
    | none =>
        have absent : ¬ record.transactionId ∈ txs := by
          rw [Std.HashMap.mem_iff_isSome_getElem?, here, found]
          simp
        simp [absent]
    | some index =>
        have present : record.transactionId ∈ txs := by
          rw [Std.HashMap.mem_iff_isSome_getElem?, here, found]
          simp
        simp [present]
  · have differs : (record.transactionId == transactionId) = false := by
      simpa using same
    simp [differs]

/-- Index a suffix whose predecessor log held `height` records. -/
def TxIndex.extendFrom (txs : TxIndex) (height : Nat) : List IntentRecord → TxIndex
  | [] => txs
  | record :: rest => TxIndex.extendFrom (txs.admitAt height record) (height + 1) rest

theorem TxIndex.extendFrom_exact {txs : TxIndex} {records : List IntentRecord}
    (exact : txs.Exact records) (more : List IntentRecord) :
    (txs.extendFrom records.length more).Exact (records ++ more) := by
  induction more generalizing txs records with
  | nil => simpa [TxIndex.extendFrom] using exact
  | cons record rest ih =>
      have step := ih (TxIndex.admitAt_exact exact record)
      rw [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append] at step
      exact step

/-- One pass over the log: linear, never `records ++ [record]`. -/
def TxIndex.ofRecords (records : List IntentRecord) : TxIndex :=
  (∅ : TxIndex).extendFrom 0 records

theorem TxIndex.ofRecords_exact (records : List IntentRecord) :
    (TxIndex.ofRecords records).Exact records := by
  simpa using TxIndex.extendFrom_exact TxIndex.empty_exact records

/-- **Refinement (receipt selection)**: a cached lookup is the `findIdx?` the
receipt lookup specifies. -/
theorem TxIndex.lookup_eq {txs : TxIndex} {records : List IntentRecord}
    (exact : txs.Exact records) (transactionId : TransactionId) :
    txs[transactionId]? =
      records.findIdx? (fun record => record.transactionId == transactionId) :=
  exact transactionId

/-! ## Poles

The exactness premises are inhabited by construction at every image
(`ofImage_exact`, `ofRecords_exact`) and refuted by a cache that missed one
append: the stale index of a one-record log answers `none` where the log's
`findIdx?` answers `some 0`. -/

theorem stale_index_refuted (record : IntentRecord) :
    ¬ (∅ : TxIndex).Exact [record] := by
  intro exact
  have := exact record.transactionId
  simp [firstIndex] at this

theorem stale_cellIds_refuted (id : CellId) : ¬ CellIds.empty.Exact [id] := by
  intro exact
  have := exact.order
  simp [CellIds.empty, eraseDups_singleton] at this

#assert_axioms CellIds.toList_eq
#assert_axioms CellIds.contains_iff
#assert_axioms CellIds.admit_exact
#assert_axioms CellIds.ofImage_exact
#assert_axioms TxIndex.admitAt_exact
#assert_axioms TxIndex.ofRecords_exact
#assert_axioms TxIndex.lookup_eq
#assert_axioms stale_index_refuted
#assert_axioms stale_cellIds_refuted

end Minidregg.Kernel.SessionIndex
