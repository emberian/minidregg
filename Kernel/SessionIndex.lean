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
module

public import Kernel.DurableReceiver
public import Std.Data.HashMap.Lemmas
public import Std.Data.HashSet.Lemmas
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
  have hsimpa := CellIds.addAll_exact CellIds.empty_exact (rawIds image)
  simp at hsimpa ⊢
  exact hsimpa

/-- `List.eraseDups` of a list of cell ids in one hashed pass (linear, not quadratic). -/
def dedup (raw : List CellId) : List CellId := (CellIds.empty.addAll raw).order.toList

theorem dedup_eq (raw : List CellId) : dedup raw = raw.eraseDups := by
  have := (CellIds.addAll_exact CellIds.empty_exact raw).order
  simpa [dedup] using this

/-- `Image.cellIds`, compiled as one hashed pass (every compiled caller that sees
this module runs it; the definition and every theorem about it are unchanged). -/
def cellIdsFast (image : Image) : List CellId := dedup (rawIds image)

@[csimp] theorem cellIds_eq_fast : @Image.cellIds = @cellIdsFast := by
  funext image
  rw [cellIdsFast, dedup_eq, cellIds_eq_rawIds]

#assert_axioms cellIds_eq_fast

/-- Whether a list of cell ids has no repeat, in one hashed pass (`List.Nodup`'s
decision is quadratic). -/
def nodupFrom : List CellId → Std.HashSet CellId → Bool
  | [], _ => true
  | id :: rest, seen => if seen.contains id then false else nodupFrom rest (seen.insert id)

def nodupFast (ids : List CellId) : Bool := nodupFrom ids ∅

theorem nodupFrom_iff : ∀ (ids : List CellId) (seen : Std.HashSet CellId),
    nodupFrom ids seen = true ↔ ids.Nodup ∧ ∀ id ∈ ids, seen.contains id = false
  | [], seen => by simp [nodupFrom]
  | id :: rest, seen => by
      unfold nodupFrom
      by_cases hit : seen.contains id = true
      · simp only [hit, if_true, Bool.false_eq_true, false_iff, not_and]
        intro _ fresh
        have := fresh id List.mem_cons_self
        simp [hit] at this
      · simp only [hit, if_false, Bool.false_eq_true]
        rw [nodupFrom_iff rest (seen.insert id), List.nodup_cons]
        simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff, beq_eq_false_iff_ne,
          List.mem_cons, forall_eq_or_imp]
        constructor
        · rintro ⟨nodup, fresh⟩
          refine ⟨⟨fun member => (fresh id member).1 rfl, nodup⟩, by simpa using hit,
            fun other member => (fresh other member).2⟩
        · rintro ⟨⟨missing, nodup⟩, _, fresh⟩
          refine ⟨nodup, fun other member => ⟨?_, fresh other member⟩⟩
          rintro rfl
          exact missing member

theorem nodupFast_iff (ids : List CellId) : nodupFast ids = true ↔ ids.Nodup := by
  rw [nodupFast, nodupFrom_iff]
  simp

#assert_axioms nodupFast_iff

/-- One accepted record's writes, added at append. -/
def CellIds.admit (ids : CellIds) (record : IntentRecord) : CellIds :=
  ids.addAll (record.writes.map DataWrite.cellId)

theorem rawIds_snoc (image : Image) (record : IntentRecord) :
    rawIds (image.snoc record) = rawIds image ++ record.writes.map DataWrite.cellId := by
  simp [rawIds, List.flatMap_append, List.append_assoc]

theorem CellIds.admit_exact {ids : CellIds} {image : Image} (exact : ids.Exact (rawIds image))
    (record : IntentRecord) :
    (ids.admit record).Exact (rawIds (image.snoc record)) := by
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
  have hsimpa := TxIndex.extendFrom_exact TxIndex.empty_exact records
  simp at hsimpa ⊢
  exact hsimpa

/-- **Refinement (receipt selection)**: a cached lookup is the `findIdx?` the
receipt lookup specifies. -/
theorem TxIndex.lookup_eq {txs : TxIndex} {records : List IntentRecord}
    (exact : txs.Exact records) (transactionId : TransactionId) :
    txs[transactionId]? =
      records.findIdx? (fun record => record.transactionId == transactionId) :=
  exact transactionId

/-! ## First index by key (nullifiers, written cell ids)

The same shape as `TxIndex` for a record that carries a LIST of keys: key ↦ the
first log index whose record carries it. A past read at height `k` asks "was
this key carried by one of the first `k` records?", which is the cached index
compared against `k` (`KeyIndex.below_eq`): no pass over the prefix. -/

/-- A record list's first index carrying `key`. -/
def firstKeyIndex {K : Type} [DecidableEq K] (keys : IntentRecord → List K)
    (records : List IntentRecord) (key : K) : Option Nat :=
  records.findIdx? (fun record => (keys record).contains key)

abbrev KeyIndex (K : Type) [BEq K] [Hashable K] := Std.HashMap K Nat

section KeyIndex

variable {K : Type} [DecidableEq K] [Hashable K] [LawfulHashable K]

/-- Every lookup is the log's first index. -/
def KeyIndex.Exact (index : KeyIndex K) (keys : IntentRecord → List K)
    (records : List IntentRecord) : Prop :=
  ∀ key, index[key]? = firstKeyIndex keys records key

theorem KeyIndex.empty_exact (keys : IntentRecord → List K) :
    (∅ : KeyIndex K).Exact keys [] := by
  intro key
  simp [firstKeyIndex]

/-- Each key of the record at index `height` joins, keeping an earlier index. -/
def KeyIndex.admitAt (index : KeyIndex K) (keys : IntentRecord → List K) (height : Nat)
    (record : IntentRecord) : KeyIndex K :=
  (keys record).foldl (fun index key => index.insertIfNew key height) index

theorem KeyIndex.getElem?_foldl (index : KeyIndex K) (height : Nat) (more : List K) (key : K) :
    (more.foldl (fun index key => index.insertIfNew key height) index)[key]? =
      index[key]?.or (if more.contains key then some height else none) := by
  induction more generalizing index with
  | nil => simp
  | cons head rest ih =>
      rw [List.foldl_cons, ih, Std.HashMap.getElem?_insertIfNew]
      by_cases same : head = key
      · subst same
        by_cases present : head ∈ index
        · have found : (index[head]?).isSome := Std.HashMap.mem_iff_isSome_getElem?.mp present
          obtain ⟨value, isValue⟩ := Option.isSome_iff_exists.mp found
          simp [present]
        · have missing : index[head]? = none := Std.HashMap.getElem?_eq_none present
          simp [present]
      · have differs : (head == key) = false := by simp [same]
        have differs' : key ≠ head := Ne.symm same
        simp [differs, differs']

theorem firstKeyIndex_snoc (keys : IntentRecord → List K) (records : List IntentRecord)
    (record : IntentRecord) (key : K) :
    firstKeyIndex keys (records ++ [record]) key =
      (firstKeyIndex keys records key).or
        (if (keys record).contains key then some records.length else none) := by
  unfold firstKeyIndex
  rw [List.findIdx?_append]
  simp [List.findIdx?_cons]

theorem KeyIndex.admitAt_exact {index : KeyIndex K} {keys : IntentRecord → List K}
    {records : List IntentRecord} (exact : index.Exact keys records) (record : IntentRecord) :
    (index.admitAt keys records.length record).Exact keys (records ++ [record]) := by
  intro key
  unfold KeyIndex.admitAt
  rw [KeyIndex.getElem?_foldl, firstKeyIndex_snoc, exact key]

/-- Index a suffix whose predecessor log held `height` records. -/
def KeyIndex.extendFrom (index : KeyIndex K) (keys : IntentRecord → List K) (height : Nat) :
    List IntentRecord → KeyIndex K
  | [] => index
  | record :: rest => KeyIndex.extendFrom (index.admitAt keys height record) keys (height + 1) rest

theorem KeyIndex.extendFrom_exact {index : KeyIndex K} {keys : IntentRecord → List K}
    {records : List IntentRecord} (exact : index.Exact keys records) (more : List IntentRecord) :
    (index.extendFrom keys records.length more).Exact keys (records ++ more) := by
  induction more generalizing index records with
  | nil => simpa [KeyIndex.extendFrom] using exact
  | cons record rest ih =>
      have step := ih (KeyIndex.admitAt_exact exact record)
      rw [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append] at step
      exact step

/-- One pass over the log. -/
def KeyIndex.ofRecords (keys : IntentRecord → List K) (records : List IntentRecord) : KeyIndex K :=
  (∅ : KeyIndex K).extendFrom keys 0 records

theorem KeyIndex.ofRecords_exact (keys : IntentRecord → List K) (records : List IntentRecord) :
    (KeyIndex.ofRecords keys records).Exact keys records := by
  have hsimpa := KeyIndex.extendFrom_exact (KeyIndex.empty_exact keys) records
  simp at hsimpa ⊢
  exact hsimpa

end KeyIndex

/-- A first index below `height` is a hit in the first `height` elements. -/
theorem findIdx?_any_lt {α : Type} (p : α → Bool) :
    ∀ (list : List α) (height : Nat),
      ((list.findIdx? p).any fun index => decide (index < height)) = (list.take height).any p
  | [], height => by simp
  | head :: rest, 0 => by
      simp only [List.findIdx?_cons, List.take_zero, List.any_nil]
      split <;> simp
  | head :: rest, height + 1 => by
      simp only [List.findIdx?_cons, List.take_succ_cons, List.any_cons]
      by_cases hit : p head = true
      · simp [hit]
      · simp only [hit, Bool.false_or]
        rw [← findIdx?_any_lt p rest height]
        cases rest.findIdx? p <;> simp

/-- **A past height's membership, off the index**: the key is carried by one of
the first `height` records exactly when its cached first index is below `height`. -/
theorem KeyIndex.below_eq {K : Type} [DecidableEq K] [Hashable K] [LawfulHashable K]
    {index : KeyIndex K} {keys : IntentRecord → List K} {records : List IntentRecord}
    (exact : index.Exact keys records) (height : Nat) (key : K) :
    ((index[key]?).any fun first => decide (first < height)) =
      decide (key ∈ (records.take height).flatMap keys) := by
  rw [exact key]
  unfold firstKeyIndex
  rw [findIdx?_any_lt]
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true, List.mem_flatMap]

/-- **A past height's transaction ids, off the receipt index.** -/
theorem TxIndex.below_eq {txs : TxIndex} {records : List IntentRecord}
    (exact : txs.Exact records) (height : Nat) (transactionId : TransactionId) :
    ((txs[transactionId]?).any fun first => decide (first < height)) =
      ((records.take height).map IntentRecord.transactionId).contains transactionId := by
  rw [exact transactionId]
  unfold firstIndex
  rw [findIdx?_any_lt]
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true, -List.map_take]

#assert_axioms KeyIndex.ofRecords_exact
#assert_axioms KeyIndex.admitAt_exact
#assert_axioms KeyIndex.below_eq
#assert_axioms TxIndex.below_eq

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
