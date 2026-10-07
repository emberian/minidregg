/-
# Compiler.DurableIndexModel — the model theorem of the index families

`IndexRows.changes_exact`: over the logical map, a map that REPRESENTS a log (each
key's value is `declared log k`, a search over the log defined without the trie
and without `IndexRows.changes`) is advanced by a record's rows (computed from
priors the map holds) to a map that represents the log with the record
appended. Families 4 and 5 hold under `KeysDistinct keyHash (hashInputs log)`;
the meaning theorems (`presence_meaning`, `links_meaning`, `backlinks_meaning`,
`payer_meaning`, `incoming_meaning`) say in domain terms what each declared
value is. See `Compiler.DurableIndexFamilies` for the families.
-/
import Compiler.DurableIndexFamilies

namespace Minidregg.Compiler.DurableIndex

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.LinkIndex (TargetKey LinkKey lastWrite liveLinks)
open IndexRows

set_option autoImplicit false

/-! ## Change lists over the logical map -/

/-- The last change a list makes at `k` (`none`: it does not touch `k`). -/
def lastFor : List (IndexKey × Option (List UInt8)) → IndexKey → Option (Option (List UInt8))
  | [], _ => none
  | change :: rest, k => (lastFor rest k).or (if change.1 = k then some change.2 else none)

theorem lastFor_append (a b : List (IndexKey × Option (List UInt8))) (k : IndexKey) :
    lastFor (a ++ b) k = (lastFor b k).or (lastFor a k) := by
  induction a with
  | nil => simp [lastFor]
  | cons change rest ih => simp only [List.cons_append, lastFor, ih, Option.or_assoc]

theorem mapLookup_append (a b : List (IndexKey × List UInt8)) (k : IndexKey) :
    mapLookup (a ++ b) k = (mapLookup a k).or (mapLookup b k) := by
  unfold mapLookup; rw [List.find?_append]; cases a.find? (·.1 = k) <;> simp

theorem mapLookup_cons (e : IndexKey × List UInt8) (rest : List (IndexKey × List UInt8)) (k : IndexKey) :
    mapLookup (e :: rest) k = if e.1 = k then some e.2 else mapLookup rest k := by
  unfold mapLookup; by_cases h : e.1 = k <;> simp [h]

theorem mapLookup_filter_ne (m : List (IndexKey × List UInt8)) (k' k : IndexKey) :
    mapLookup (m.filter (·.1 ≠ k')) k = if k = k' then none else mapLookup m k := by
  induction m with
  | nil => simp [mapLookup]
  | cons e rest ih =>
      rw [List.filter_cons, mapLookup_cons]
      by_cases drop : e.1 = k'
      · have : ¬ (decide (e.1 ≠ k') = true) := by simp [drop]
        rw [if_neg this, ih]
        by_cases same : k = k'
        · simp [same]
        · have : ¬ e.1 = k := fun h => same (h ▸ drop)
          simp [same, this]
      · have : decide (e.1 ≠ k') = true := by simp [drop]
        rw [if_pos this, mapLookup_cons, ih]
        by_cases same : k = k'
        · have : ¬ e.1 = k := fun h => drop (h ▸ same)
          simp [same, this, drop]
        · simp [same]

theorem mapLookup_modelSet (m : List (IndexKey × List UInt8)) (k' : IndexKey) (value : Option (List UInt8))
    (k : IndexKey) : mapLookup (modelSet m k' value) k = if k = k' then value else mapLookup m k := by
  unfold modelSet
  rw [mapLookup_append, mapLookup_filter_ne]
  by_cases same : k = k'
  · subst same; cases value <;> simp [mapLookup]
  · cases value with
    | none => simp [same, mapLookup]
    | some v => simp [same, mapLookup, Ne.symm same]

/-- **A change list over a map**: the value at `k` is the list's last change at
`k`, else the map's. -/
theorem mapLookup_modelApply (changes : List (IndexKey × Option (List UInt8))) :
    ∀ (m : List (IndexKey × List UInt8)) (k : IndexKey),
      mapLookup (modelApply m changes) k = (lastFor changes k).getD (mapLookup m k) := by
  induction changes with
  | nil => intro m k; rfl
  | cons change rest ih =>
      intro m k
      show mapLookup (modelApply (modelSet m change.1 change.2) rest) k = _
      rw [ih, mapLookup_modelSet]
      simp only [lastFor]
      cases lastFor rest k with
      | some v => rfl
      | none =>
          by_cases same : change.1 = k
          · simp [same]
          · simp [same, Ne.symm same]

theorem modelSet_nodup {m : List (IndexKey × List UInt8)} (unique : (m.map Prod.fst).Nodup)
    (k : IndexKey) (value : Option (List UInt8)) : ((modelSet m k value).map Prod.fst).Nodup := by
  have sub : ((m.filter (·.1 ≠ k)).map Prod.fst).Nodup := unique.sublist ((List.filter_sublist (p := fun e : IndexKey × List UInt8 => decide (e.1 ≠ k)) (l := m)).map _)
  cases value with
  | none => simpa [modelSet] using sub
  | some v =>
      simp only [modelSet, Option.map_some, Option.toList_some, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨sub, List.nodup_singleton _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      have := (List.mem_filter.mp he).2
      simpa using this

theorem modelApply_nodup (changes : List (IndexKey × Option (List UInt8))) :
    ∀ (m : List (IndexKey × List UInt8)), (m.map Prod.fst).Nodup → ((modelApply m changes).map Prod.fst).Nodup := by
  induction changes with
  | nil => intro m unique; exact unique
  | cons change rest ih =>
      intro m unique
      exact ih _ (modelSet_nodup unique change.1 change.2)

theorem lastFor_none_of_keys (changes : List (IndexKey × Option (List UInt8))) (k : IndexKey)
    (away : ∀ change ∈ changes, change.1 ≠ k) : lastFor changes k = none := by
  induction changes with
  | nil => rfl
  | cons change rest ih =>
      simp only [lastFor, ih (fun c member => away c (List.mem_cons_of_mem _ member)),
        if_neg (away change List.mem_cons_self), Option.or_none]

theorem lastFor_flatMap_none {α : Type} (cells : List α) (g : α → List (IndexKey × Option (List UInt8)))
    (k : IndexKey) (away : ∀ x ∈ cells, lastFor (g x) k = none) : lastFor (cells.flatMap g) k = none := by
  induction cells with
  | nil => rfl
  | cons x rest ih =>
      rw [List.flatMap_cons, lastFor_append, ih (fun y member => away y (List.mem_cons_of_mem _ member)),
        away x List.mem_cons_self]
      rfl

theorem lastFor_flatMap_one {α : Type} [DecidableEq α] (cells : List α) (unique : cells.Nodup)
    (g : α → List (IndexKey × Option (List UInt8))) (k : IndexKey) {cell : α} (member : cell ∈ cells)
    (away : ∀ x ∈ cells, x ≠ cell → lastFor (g x) k = none) :
    lastFor (cells.flatMap g) k = lastFor (g cell) k := by
  induction cells with
  | nil => cases member
  | cons x rest ih =>
      rw [List.flatMap_cons, lastFor_append]
      obtain ⟨notIn, restUnique⟩ := List.nodup_cons.mp unique
      by_cases here : x = cell
      · subst here
        rw [lastFor_flatMap_none rest g k (fun y inRest => away y (List.mem_cons_of_mem _ inRest)
          (fun same => notIn (same ▸ inRest)))]
        rfl
      · rw [away x List.mem_cons_self here]
        have inRest : cell ∈ rest := by
          rcases List.mem_cons.mp member with same | inRest
          · exact absurd same.symm here
          · exact inRest
        rw [ih restUnique inRest (fun y inRest' => away y (List.mem_cons_of_mem _ inRest'))]
        cases lastFor (g cell) k <;> rfl

/-! ## Key distinctness: the hypothesis family -/

/-- **The key hash is injective on `inputs`.** A premise (assumed, never proved
for the deployed hash): for `keyHash` it is the COLLISION resistance of
cSHAKE256 at a 256-bit output (about 2^128 work) restricted to the byte strings
a log feeds it (`hashInputs`); its failure exhibits a cSHAKE256 collision
(`keysDistinct_or_collision`). -/
def KeysDistinct (hash : List UInt8 → Digest256) (inputs : List (List UInt8)) : Prop :=
  ∀ a ∈ inputs, ∀ b ∈ inputs, hash a = hash b → a = b

/-- Every live link the log's writes hold: (cell, link id, record). -/
def logLinks (records : List IntentRecord) : List (CellId × LinkId × LinkRecord) :=
  records.flatMap fun record => record.writes.flatMap fun write =>
    (liveLinks write.canonicalPostBytes).map fun link => (write.cellId, link.1, link.2)

/-- Every cell the log writes. -/
def logCells (records : List IntentRecord) : List CellId :=
  records.flatMap fun record => record.writes.map DataWrite.cellId

/-- The inputs a link contributes: its secondary, its record digest, its
backlink secondary and the primary of every target it is filed under. -/
def linkInputs (cell : CellId) (link : LinkId) (record : LinkRecord) : List (List UInt8) :=
  [Family.links :: 0xFF :: linkBytes link, Family.links :: 0xFE :: linkRecordBytes link record,
    Family.backlinks :: 0xFF :: pairBytes cell link] ++
    (targetsOf record).map fun target => Family.backlinks :: targetBytes target

/-- The inputs a record contributes besides its links: its subject and cells
(presence), its cells' family-4 primaries, its payer and its transfer's destination. -/
def recordInputs (record : IntentRecord) : List (List UInt8) :=
  (record.writes.map fun write => Family.links :: cellBytes write.cellId) ++
  (match record.subject with
    | some subject => (Family.presence :: subjectBytes subject) ::
        record.writes.map fun write => Family.presence :: 0xFF :: cellBytes write.cellId
    | none => []) ++
  (match fleetOf record with
    | some (payer, destination) => (Family.payer :: accountBytes payer) ::
        (destination.map fun d => Family.incoming :: accountBytes d).toList
    | none => [])

/-- Every byte string a log feeds the key hash. -/
def hashInputs (records : List IntentRecord) : List (List UInt8) :=
  records.flatMap recordInputs ++ (logLinks records).flatMap fun entry => linkInputs entry.1 entry.2.1 entry.2.2

theorem keyHash_cons_injective {hash : List UInt8 → Digest256} {inputs : List (List UInt8)}
    (distinct : KeysDistinct hash inputs) {family : UInt8} {a b : List UInt8}
    (inA : family :: a ∈ inputs) (inB : family :: b ∈ inputs)
    (same : hash (family :: a) = hash (family :: b)) : a = b :=
  (List.cons.inj (distinct _ inA _ inB same)).2

/-! ### Injective encodings -/

theorem digest_bytes_injective {a b : Digest} (same : digestStream.encode a = digestStream.encode b) : a = b :=
  HyperdocumentCodec.streamCodec_encode_injective digestStream same

theorem cellBytes_injective {a b : CellId} (same : cellBytes a = cellBytes b) : a = b :=
  digest_bytes_injective same

theorem linkBytes_injective {a b : LinkId} (same : linkBytes a = linkBytes b) : a = b := by
  have := digest_bytes_injective same
  cases a; cases b; simp_all

theorem pairBytes_injective {c c' : CellId} {l l' : LinkId} (same : pairBytes c l = pairBytes c' l') :
    c = c' ∧ l = l' := by
  have pair := HyperdocumentCodec.streamCodec_encode_injective
    (StreamCodec.product digestStream digestStream) (a₁ := (c, l.digest)) (a₂ := (c', l'.digest)) same
  simp only [Prod.mk.injEq] at pair
  refine ⟨pair.1, ?_⟩
  cases l; cases l'; simp_all

theorem linkRecordBytes_injective {l l' : LinkId} {r r' : LinkRecord}
    (same : linkRecordBytes l r = linkRecordBytes l' r') : l = l' ∧ r = r' := by
  have pair := HyperdocumentCodec.streamCodec_encode_injective
    (StreamCodec.product digestStream HyperdocumentCell.linkRecordStream)
    (a₁ := (l.digest, r)) (a₂ := (l'.digest, r')) same
  simp only [Prod.mk.injEq] at pair
  refine ⟨?_, pair.2⟩
  cases l; cases l'; simp_all

theorem targetBytes_injective {a b : TargetKey} (same : targetBytes a = targetBytes b) : a = b :=
  HyperdocumentCodec.streamCodec_encode_injective targetKeyStream same

/-! ## What the log declares (defined by search over the log; no trie, no `changes`) -/

/-- Families 0/1: a key ↦ the height of the first record that carries it. -/
def declared01 (records : List IntentRecord) (k : IndexKey) : Option (List UInt8) :=
  ((records.zipIdx 1).find? fun entry => k ∈ keys01 entry.1).map fun entry => heightValue entry.2

/-- The presence row a record at `height` declares at `k` (its last written cell with that key). -/
def presenceAt (record : IntentRecord) (height : Nat) (k : IndexKey) : Option (List UInt8) :=
  match record.subject with
  | none => none
  | some subject =>
      ((writtenCells record).reverse.find? fun cell => presenceKey subject cell = k).map
        fun cell => presenceValue cell height

/-- Family 2: the latest record whose presence keys hold `k`. -/
def declared2 (records : List IntentRecord) (k : IndexKey) : Option (List UInt8) :=
  (records.zipIdx 1).reverse.findSome? fun entry => presenceAt entry.1 entry.2 k

/-- One record's effect on a cell's live links: the live links of its last write,
each keeping the live-since height of the identical link it had, else this height. -/
def linkStep (cell : CellId) (prior : List (LinkId × LinkRecord × Nat)) (entry : IntentRecord × Nat) :
    List (LinkId × LinkRecord × Nat) :=
  match lastWrite cell entry.1 with
  | some write => (liveLinks write.canonicalPostBytes).map fun link =>
      (link.1, link.2, ((prior.find? fun e => e.1 = link.1 ∧ e.2.1 = link.2).map (·.2.2)).getD entry.2)
  | none => prior

/-- **A cell's live links with their live-since heights** after a log: the live
links of its latest write, each live without a break since the height it holds. -/
def linkState (records : List IntentRecord) (cell : CellId) : List (LinkId × LinkRecord × Nat) :=
  (records.zipIdx 1).foldl (linkStep cell) []

/-- Family 4: the facts of the link of the cell whose primary is `k`'s. -/
def declared4 (records : List IntentRecord) (k : IndexKey) : Option (List UInt8) :=
  ((logCells records).find? fun cell => cellPrimary cell = k.primary).bind fun cell =>
    ((linkState records cell).find? fun e => linkKey cell e.1 = k).map fun e => factsValue cell e.1 e.2.1 e.2.2

/-- Family 5: the row of a live link filed under `k`'s target primary, at `k`'s pair secondary. -/
def declared5 (records : List IntentRecord) (k : IndexKey) : Option (List UInt8) :=
  (logCells records).findSome? fun cell => (linkState records cell).findSome? fun e =>
    if k.secondary = pairSecondary cell e.1 ∧ k.primary ∈ targetPrimaries e.2.1 then
      some (rowValue cell e.1 e.2.1 e.2.2)
    else none

/-- The records (with heights) whose payer key is `k`. -/
def paying (records : List IntentRecord) (k : IndexKey) : List (IntentRecord × Nat) :=
  (records.zipIdx 1).filter fun entry => (fleetOf entry.1).map (fun fleet => payerKey fleet.1) = some k

/-- Family 6: how many records paid under `k`, the last one's height and transaction id. -/
def declared6 (records : List IntentRecord) (k : IndexKey) : Option (List UInt8) :=
  (paying records k).getLast?.map fun entry => payerValue (paying records k).length entry.2 entry.1.transactionId

def incomingAt (record : IntentRecord) (height : Nat) (k : IndexKey) : Option (List UInt8) :=
  match fleetOf record with
  | some (_, some destination) =>
      if incomingKey destination height = k then some (transactionValue record.transactionId) else none
  | _ => none

/-- Family 7: the transaction id of the record at `k`'s height paying `k`'s destination. -/
def declared7 (records : List IntentRecord) (k : IndexKey) : Option (List UInt8) :=
  (records.zipIdx 1).reverse.findSome? fun entry => incomingAt entry.1 entry.2 k

/-- **The index a log declares**, family by family. -/
def declared (records : List IntentRecord) (k : IndexKey) : Option (List UInt8) :=
  if k.family = Family.spent ∨ k.family = Family.transaction then declared01 records k
  else if k.family = Family.presence then declared2 records k
  else if k.family = Family.links then declared4 records k
  else if k.family = Family.backlinks then declared5 records k
  else if k.family = Family.payer then declared6 records k
  else if k.family = Family.incoming then declared7 records k
  else none

/-- A logical map (unique keys) holds exactly what the log declares. -/
def Represents (m : List (IndexKey × List UInt8)) (records : List IntentRecord) : Prop :=
  (m.map Prod.fst).Nodup ∧ ∀ k, mapLookup m k = declared records k

/-- The priors are the map's: the payer key's value, and each written cell's
family-4 members exactly (what a verified reveal of its prefix answers,
`reveal_sound`). -/
def PriorsOf (m : List (IndexKey × List UInt8)) (record : IntentRecord) (priors : Priors) : Prop :=
  priors.payer = (fleetOf record).bind (fun fleet => mapLookup m (payerKey fleet.1)) ∧
    ∀ cell ∈ writtenCells record, ∀ k v,
      (k, v) ∈ priors.links cell ↔ (k, v) ∈ m ∧ (bitsOf k).take 264 = linkPrefix cell

/-! ### Basic facts -/

theorem zipIdx_snoc (records : List IntentRecord) (record : IntentRecord) :
    (records ++ [record]).zipIdx 1 = records.zipIdx 1 ++ [(record, records.length + 1)] := by
  rw [List.zipIdx_append]; simp [Nat.add_comm]

theorem linkState_snoc (records : List IntentRecord) (record : IntentRecord) (cell : CellId) :
    linkState (records ++ [record]) cell = linkStep cell (linkState records cell) (record, records.length + 1) := by
  unfold linkState; rw [zipIdx_snoc, List.foldl_append]; rfl

theorem logCells_snoc (records : List IntentRecord) (record : IntentRecord) :
    logCells (records ++ [record]) = logCells records ++ record.writes.map DataWrite.cellId := by
  simp [logCells]

theorem logLinks_snoc (records : List IntentRecord) (record : IntentRecord) :
    logLinks (records ++ [record]) = logLinks records ++ logLinks [record] := by
  simp [logLinks]

theorem mem_writtenCells {record : IntentRecord} {cell : CellId} :
    cell ∈ writtenCells record ↔ cell ∈ record.writes.map DataWrite.cellId := by
  simp [writtenCells, List.mem_dedup]

theorem writtenCells_nodup (record : IntentRecord) : (writtenCells record).Nodup := List.nodup_dedup _

theorem lastWrite_none {record : IntentRecord} {cell : CellId} (away : cell ∉ writtenCells record) :
    lastWrite cell record = none := by
  unfold lastWrite
  rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff]
  intro write member same
  exact away (mem_writtenCells.mpr (List.mem_map.mpr ⟨write, member, by simpa using same⟩))

theorem lastWrite_some {record : IntentRecord} {cell : CellId} {write : DataWrite}
    (found : lastWrite cell record = some write) : write ∈ record.writes ∧ write.cellId = cell := by
  unfold lastWrite at found
  have member := List.mem_of_getLast? found
  have := List.mem_filter.mp member
  exact ⟨this.1, by simpa using this.2⟩

theorem linkState_unwritten (records : List IntentRecord) (record : IntentRecord) {cell : CellId}
    (away : cell ∉ writtenCells record) :
    linkState (records ++ [record]) cell = linkState records cell := by
  rw [linkState_snoc]; unfold linkStep; rw [lastWrite_none away]

/-- The links of a written cell after the record: its last write's, as `lastLinks`. -/
theorem linkState_written (records : List IntentRecord) (record : IntentRecord) {cell : CellId}
    (member : cell ∈ writtenCells record) :
    linkState (records ++ [record]) cell = (lastLinks cell record).map fun link =>
      (link.1, link.2, (((linkState records cell).find? fun e => e.1 = link.1 ∧ e.2.1 = link.2).map
        (·.2.2)).getD (records.length + 1)) := by
  rw [linkState_snoc]; unfold linkStep lastLinks
  cases found : lastWrite cell record with
  | some write => rfl
  | none =>
      exfalso
      obtain ⟨write, inWrites, same⟩ := List.mem_map.mp (mem_writtenCells.mp member)
      unfold lastWrite at found
      rw [List.getLast?_eq_none_iff, List.filter_eq_nil_iff] at found
      exact found write inWrites (by simpa using same)

theorem linkState_never (records : List IntentRecord) {cell : CellId} (never : cell ∉ logCells records) :
    linkState records cell = [] := by
  induction records using List.reverseRecOn with
  | nil => rfl
  | append_singleton rest record ih =>
      rw [logCells_snoc, List.mem_append, not_or] at never
      have away : cell ∉ writtenCells record := fun h => never.2 (mem_writtenCells.mp h)
      rw [linkState_unwritten rest record away, ih never.1]

theorem linkState_ids_nodup (records : List IntentRecord) (cell : CellId) :
    ((linkState records cell).map (·.1)).Nodup := by
  induction records using List.reverseRecOn with
  | nil => exact List.nodup_nil
  | append_singleton rest record ih =>
      by_cases member : cell ∈ writtenCells record
      · rw [linkState_written rest record member, List.map_map]
        have := Kernel.LinkIndex.liveLinks_ids_nodup
        unfold lastLinks
        cases lastWrite cell record with
        | none => exact List.nodup_nil
        | some write => simpa [Function.comp_def] using this write.canonicalPostBytes
      · rw [linkState_unwritten rest record member]; exact ih

theorem mem_lastLinks {record : IntentRecord} {cell : CellId} {link : LinkKey}
    (member : link ∈ lastLinks cell record) : (cell, link.1, link.2) ∈ logLinks [record] := by
  unfold lastLinks at member
  cases found : lastWrite cell record with
  | none => rw [found] at member; cases member
  | some write =>
      rw [found] at member
      obtain ⟨inWrites, same⟩ := lastWrite_some found
      simp only [logLinks, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_flatMap, List.mem_map]
      exact ⟨write, inWrites, link, member, by rw [same]⟩

theorem mem_linkState {records : List IntentRecord} {cell : CellId} {e : LinkId × LinkRecord × Nat}
    (member : e ∈ linkState records cell) : (cell, e.1, e.2.1) ∈ logLinks records := by
  induction records using List.reverseRecOn with
  | nil => cases member
  | append_singleton rest record ih =>
      rw [logLinks_snoc]
      by_cases written : cell ∈ writtenCells record
      · rw [linkState_written rest record written] at member
        obtain ⟨link, inLinks, rfl⟩ := List.mem_map.mp member
        exact List.mem_append_right _ (mem_lastLinks inLinks)
      · rw [linkState_unwritten rest record written] at member
        exact List.mem_append_left _ (ih member)

theorem mem_logCells_of_linkState {records : List IntentRecord} {cell : CellId} {e : LinkId × LinkRecord × Nat}
    (member : e ∈ linkState records cell) : cell ∈ logCells records := by
  by_contra never
  rw [linkState_never records never] at member
  cases member

/-! ### List helpers -/

theorem find?_of_unique {α : Type} (list : List α) (p : α → Bool) {a : α} (member : a ∈ list) (holds : p a = true)
    (unique : ∀ x ∈ list, p x = true → x = a) : list.find? p = some a := by
  induction list with
  | nil => cases member
  | cons x rest ih =>
      rw [List.find?_cons]
      by_cases here : p x = true
      · simp only [here]; exact congrArg some (unique x List.mem_cons_self here)
      · simp only [Bool.not_eq_true] at here; simp only [here]
        rcases List.mem_cons.mp member with same | inRest
        · subst same; rw [here] at holds; cases holds
        · exact ih inRest (fun y inY => unique y (List.mem_cons_of_mem _ inY))

theorem eq_of_mem_of_fst_eq {α β : Type} {list : List (α × β)} (unique : (list.map (·.1)).Nodup)
    {a b : α × β} (memA : a ∈ list) (memB : b ∈ list) (same : a.1 = b.1) : a = b :=
  List.inj_on_of_nodup_map unique memA memB same

theorem mapLookup_map {α : Type} (list : List α) (key : α → IndexKey) (value : α → List UInt8) (k : IndexKey) :
    mapLookup (list.map fun x => (key x, value x)) k = (list.find? fun x => key x = k).map value := by
  induction list with
  | nil => rfl
  | cons x rest ih =>
      rw [List.map_cons, mapLookup_cons, ih, List.find?_cons]
      by_cases here : key x = k <;> simp [here]

theorem mapLookup_none_of_keys (list : List (IndexKey × List UInt8)) (k : IndexKey)
    (away : ∀ e ∈ list, e.1 ≠ k) : mapLookup list k = none := by
  unfold mapLookup
  rw [List.find?_eq_none.mpr (fun e member => by simpa using away e member)]
  rfl

theorem mem_of_mapLookup {list : List (IndexKey × List UInt8)} {k : IndexKey} {v : List UInt8}
    (found : mapLookup list k = some v) : (k, v) ∈ list := by
  unfold mapLookup at found
  cases hfind : list.find? (·.1 = k) with
  | none => rw [hfind] at found; cases found
  | some e =>
      rw [hfind] at found
      have member := List.mem_of_find?_eq_some hfind
      have key := List.find?_some hfind
      simp only [Option.map_some, Option.some.injEq] at found
      simp only [decide_eq_true_eq] at key
      rw [← key, ← found]; exact member

theorem mapLookup_of_mem {list : List (IndexKey × List UInt8)} (unique : (list.map Prod.fst).Nodup)
    {k : IndexKey} {v : List UInt8} (member : (k, v) ∈ list) : mapLookup list k = some v := by
  unfold mapLookup
  rw [find?_of_unique list _ member (by simp)]
  · rfl
  · intro x inX same
    simp only [decide_eq_true_eq] at same
    exact eq_of_mem_of_fst_eq (list := list) (by simpa using unique) inX member same

/-- Two lists that hold the same entries, the second functional at `k`, look `k` up alike. -/
theorem mapLookup_congr {a b : List (IndexKey × List UInt8)} {k : IndexKey}
    (same : ∀ v, (k, v) ∈ a ↔ (k, v) ∈ b) (functional : ∀ v v', (k, v) ∈ b → (k, v') ∈ b → v = v') :
    mapLookup a k = mapLookup b k := by
  cases hb : mapLookup b k with
  | none =>
      apply mapLookup_none_of_keys
      intro e member same'
      have : (k, e.2) ∈ b := (same e.2).mp (by rw [← same']; exact member)
      have := mapLookup_none_of_keys
      unfold mapLookup at hb
      rw [Option.map_eq_none_iff, List.find?_eq_none] at hb
      exact hb (k, e.2) ‹(k, e.2) ∈ b› (by simp)
  | some v =>
      cases ha : mapLookup a k with
      | none =>
          have inB := mem_of_mapLookup hb
          have inA := (same v).mpr inB
          unfold mapLookup at ha
          rw [Option.map_eq_none_iff, List.find?_eq_none] at ha
          exact absurd (by simp) (ha (k, v) inA)
      | some w =>
          have inA := mem_of_mapLookup ha
          exact congrArg some (functional w v ((same w).mp inA) (mem_of_mapLookup hb))

/-! ### The cell prefix -/

theorem take_bytesBits (octets : List UInt8) (n : Nat) :
    (Kernel.WorldRoot.bytesBits octets).take (8 * n) = Kernel.WorldRoot.bytesBits (octets.take n) := by
  induction octets generalizing n with
  | nil => simp [Kernel.WorldRoot.bytesBits]
  | cons byte rest ih =>
      cases n with
      | zero => simp [Kernel.WorldRoot.bytesBits]
      | succ n =>
          simp only [Kernel.WorldRoot.bytesBits, List.flatMap_cons, List.take_succ_cons]
          rw [List.take_append, Kernel.WorldRoot.byteBits_length, List.take_of_length_le (by simp)]
          rw [show 8 * (n + 1) - 8 = 8 * n by omega]
          exact congrArg _ (ih n)

theorem prefix264 (k : IndexKey) :
    (bitsOf k).take 264 = Kernel.WorldRoot.bytesBits (k.family :: (fixedStream 32).encode k.primary) := by
  unfold bitsOf IndexKey.bytes
  rw [show (264 : Nat) = 8 * 33 by rfl, take_bytesBits]
  congr 1

theorem linkPrefix_iff (k : IndexKey) (cell : CellId) :
    (bitsOf k).take 264 = linkPrefix cell ↔ k.family = Family.links ∧ k.primary = cellPrimary cell := by
  unfold linkPrefix
  rw [prefix264, prefix264]
  constructor
  · intro same
    have bytes := Kernel.WorldRoot.bytesBits_injective same
    simp only [List.cons.injEq] at bytes
    exact ⟨bytes.1, HyperdocumentCodec.streamCodec_encode_injective (fixedStream 32) bytes.2⟩
  · rintro ⟨family, primary⟩
    simp [family, primary]

/-! ### What `KeysDistinct` gives over a log -/

theorem mem_hashInputs_cell {log : List IntentRecord} {cell : CellId} (member : cell ∈ logCells log) :
    Family.links :: cellBytes cell ∈ hashInputs log := by
  unfold logCells at member
  obtain ⟨record, inLog, inCells⟩ := List.mem_flatMap.mp member
  obtain ⟨write, inWrites, rfl⟩ := List.mem_map.mp inCells
  refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨record, inLog, ?_⟩)
  unfold recordInputs
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨write, inWrites, rfl⟩))

theorem mem_hashInputs_link {log : List IntentRecord} {cell : CellId} {link : LinkId} {record : LinkRecord}
    (member : (cell, link, record) ∈ logLinks log) {x : List UInt8} (input : x ∈ linkInputs cell link record) :
    x ∈ hashInputs log :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨(cell, link, record), member, input⟩)

section Distinct

variable {log : List IntentRecord} (distinct : KeysDistinct keyHash (hashInputs log))
include distinct

theorem cellPrimary_injective {a b : CellId} (inA : a ∈ logCells log) (inB : b ∈ logCells log)
    (same : cellPrimary a = cellPrimary b) : a = b :=
  cellBytes_injective (keyHash_cons_injective distinct (mem_hashInputs_cell inA)
    (mem_hashInputs_cell inB) same)

theorem linkSecondary_injective {c c' : CellId} {l l' : LinkId} {r r' : LinkRecord}
    (inA : (c, l, r) ∈ logLinks log) (inB : (c', l', r') ∈ logLinks log)
    (same : linkSecondary l = linkSecondary l') : l = l' := by
  have := keyHash_cons_injective distinct (mem_hashInputs_link inA (by simp [linkInputs]))
    (mem_hashInputs_link inB (by simp [linkInputs])) same
  exact linkBytes_injective (List.cons.inj this).2

theorem recordDigest_injective {c c' : CellId} {l l' : LinkId} {r r' : LinkRecord}
    (inA : (c, l, r) ∈ logLinks log) (inB : (c', l', r') ∈ logLinks log)
    (same : recordDigest l r = recordDigest l' r') : l = l' ∧ r = r' := by
  have := keyHash_cons_injective distinct (mem_hashInputs_link inA (by simp [linkInputs]))
    (mem_hashInputs_link inB (by simp [linkInputs])) same
  exact linkRecordBytes_injective (List.cons.inj this).2

theorem pairSecondary_injective {c c' : CellId} {l l' : LinkId} {r r' : LinkRecord}
    (inA : (c, l, r) ∈ logLinks log) (inB : (c', l', r') ∈ logLinks log)
    (same : pairSecondary c l = pairSecondary c' l') : c = c' ∧ l = l' := by
  have := keyHash_cons_injective distinct (mem_hashInputs_link inA (by simp [linkInputs]))
    (mem_hashInputs_link inB (by simp [linkInputs])) same
  exact pairBytes_injective (List.cons.inj this).2

theorem targetPrimary_injective {c c' : CellId} {l l' : LinkId} {r r' : LinkRecord} {t t' : TargetKey}
    (inA : (c, l, r) ∈ logLinks log) (inB : (c', l', r') ∈ logLinks log)
    (targetA : t ∈ targetsOf r) (targetB : t' ∈ targetsOf r')
    (same : targetPrimary t = targetPrimary t') : t = t' :=
  targetBytes_injective (keyHash_cons_injective distinct
    (mem_hashInputs_link inA (List.mem_append_right _ (List.mem_map.mpr ⟨t, targetA, rfl⟩)))
    (mem_hashInputs_link inB (List.mem_append_right _ (List.mem_map.mpr ⟨t', targetB, rfl⟩))) same)

end Distinct

/-! ### The key-driven diff -/

theorem lastFor_filterMap_self (keys : List IndexKey) (same : IndexKey → Prop) [DecidablePred same]
    (after : IndexKey → Option (List UInt8)) (k : IndexKey) :
    lastFor (keys.filterMap fun k' => if same k' then none else some (k', after k')) k =
      if k ∈ keys ∧ ¬ same k then some (after k) else none := by
  induction keys with
  | nil => simp [lastFor]
  | cons x rest ih =>
      rw [List.filterMap_cons]
      by_cases hx : same x
      · simp only [hx, if_true]
        rw [ih]
        by_cases here : x = k
        · subst here; simp [hx]
        · have : ¬ k = x := fun h => here h.symm
          simp [this]
      · simp only [hx, if_false, lastFor, ih]
        by_cases here : x = k
        · subst here; by_cases inRest : x ∈ rest <;> simp [hx, inRest]
        · have : ¬ k = x := fun h => here h.symm
          simp [here, this]

/-- **What a diff does at a key**: the new value where the two lists differ, else
whatever was there. -/
theorem diff_getD (before after : List (IndexKey × List UInt8)) (k : IndexKey) (x : Option (List UInt8)) :
    (lastFor (diff before after) k).getD x =
      if mapLookup after k = mapLookup before k then x else mapLookup after k := by
  unfold diff
  rw [lastFor_filterMap_self]
  by_cases eq : mapLookup after k = mapLookup before k
  · simp [eq]
  · have member : k ∈ ((before.map (·.1)) ++ (after.map (·.1))).dedup := by
      rw [List.mem_dedup, List.mem_append]
      by_contra neither
      rw [not_or] at neither
      apply eq
      rw [mapLookup_none_of_keys after k (fun e inA same => neither.2 (List.mem_map.mpr ⟨e, inA, same⟩)),
        mapLookup_none_of_keys before k (fun e inB same => neither.1 (List.mem_map.mpr ⟨e, inB, same⟩))]
    simp [eq, member]

theorem lastFor_diff_away (before after : List (IndexKey × List UInt8)) (k : IndexKey)
    (awayB : ∀ e ∈ before, e.1 ≠ k) (awayA : ∀ e ∈ after, e.1 ≠ k) : lastFor (diff before after) k = none := by
  unfold diff
  rw [lastFor_filterMap_self]
  have : k ∉ ((before.map (·.1)) ++ (after.map (·.1))).dedup := by
    rw [List.mem_dedup, List.mem_append, not_or]
    exact ⟨fun h => by obtain ⟨e, m, s⟩ := List.mem_map.mp h; exact awayB e m s,
      fun h => by obtain ⟨e, m, s⟩ := List.mem_map.mp h; exact awayA e m s⟩
  simp [this]

/-! ### Keys of the link families -/

theorem linkKey_eq_iff {k : IndexKey} (family : k.family = Family.links) (cell : CellId) (link : LinkId) :
    linkKey cell link = k ↔ cellPrimary cell = k.primary ∧ linkSecondary link = k.secondary := by
  obtain ⟨f, p, q⟩ := k
  simp only at family
  subst family
  simp [linkKey]

theorem backlinkKey_eq_iff {k : IndexKey} (family : k.family = Family.backlinks) (target : Digest256)
    (cell : CellId) (link : LinkId) :
    backlinkKey target cell link = k ↔ target = k.primary ∧ pairSecondary cell link = k.secondary := by
  obtain ⟨f, p, q⟩ := k
  simp only at family
  subst family
  simp [backlinkKey]

/-- The family-5 rows a cell's live links stand for. -/
def rowsOf (cell : CellId) (links : List (LinkId × LinkRecord × Nat)) : List (IndexKey × List UInt8) :=
  links.flatMap fun e => (targetPrimaries e.2.1).map fun target =>
    (backlinkKey target cell e.1, rowValue cell e.1 e.2.1 e.2.2)

/-- One cell's part of `declared5`. -/
def cell5 (records : List IntentRecord) (cell : CellId) (k : IndexKey) : Option (List UInt8) :=
  (linkState records cell).findSome? fun e =>
    if k.secondary = pairSecondary cell e.1 ∧ k.primary ∈ targetPrimaries e.2.1 then
      some (rowValue cell e.1 e.2.1 e.2.2)
    else none

theorem declared5_eq (records : List IntentRecord) (k : IndexKey) :
    declared5 records k = (logCells records).findSome? fun cell => cell5 records cell k := rfl

/-- A cell's family-5 rows are searched in its links' order: the first live link
filed under `k`'s target at `k`'s pair secondary. -/
theorem mapLookup_rowsOf {k : IndexKey} (family : k.family = Family.backlinks) (cell : CellId) :
    ∀ links : List (LinkId × LinkRecord × Nat),
      mapLookup (rowsOf cell links) k = links.findSome? fun e =>
        if k.secondary = pairSecondary cell e.1 ∧ k.primary ∈ targetPrimaries e.2.1 then
          some (rowValue cell e.1 e.2.1 e.2.2)
        else none
  | [] => rfl
  | e :: rest => by
      unfold rowsOf
      rw [List.flatMap_cons, mapLookup_append, mapLookup_map]
      have tail := mapLookup_rowsOf family cell rest
      unfold rowsOf at tail
      rw [tail, List.findSome?_cons]
      by_cases hit : k.secondary = pairSecondary cell e.1 ∧ k.primary ∈ targetPrimaries e.2.1
      · have found : ((targetPrimaries e.2.1).find? fun target => backlinkKey target cell e.1 = k) =
            some k.primary := by
          apply find?_of_unique _ _ hit.2
          · simp [backlinkKey_eq_iff family, hit.1]
          · intro x _ holds
            simp only [decide_eq_true_eq, backlinkKey_eq_iff family] at holds
            exact holds.1
        simp [found, hit]
      · have none : ((targetPrimaries e.2.1).find? fun target => backlinkKey target cell e.1 = k) = none := by
          rw [List.find?_eq_none]
          intro x member holds
          simp only [decide_eq_true_eq, backlinkKey_eq_iff family] at holds
          exact hit ⟨holds.2.symm, holds.1 ▸ member⟩
        simp [none, hit]

theorem findSome?_none_of {α β : Type} (list : List α) (f : α → Option β) (none : ∀ x ∈ list, f x = Option.none) :
    list.findSome? f = Option.none := by
  induction list with
  | nil => rfl
  | cons x rest ih =>
      rw [List.findSome?_cons, none x List.mem_cons_self]
      exact ih (fun y inY => none y (List.mem_cons_of_mem _ inY))

theorem findSome?_single {α β : Type} (list : List α) (f : α → Option β) {a : α}
    (others : ∀ x ∈ list, x ≠ a → f x = none) (member : a ∈ list) : list.findSome? f = f a := by
  induction list with
  | nil => cases member
  | cons x rest ih =>
      rw [List.findSome?_cons]
      by_cases here : x = a
      · subst here
        cases hfx : f x with
        | some b => rfl
        | none =>
            simp only []
            rw [findSome?_none_of rest f (fun y inY => by
              by_cases same : y = x
              · rw [same, hfx]
              · exact others y (List.mem_cons_of_mem _ inY) same)]
      · rw [others x List.mem_cons_self here]
        exact ih (fun y inY => others y (List.mem_cons_of_mem _ inY))
          ((List.mem_cons.mp member).resolve_left (Ne.symm here))


/-! ### Families 4 and 5 at a cell -/

section Cells

/-- Over a log `small` whose cells and links are among `log`'s, under
`KeysDistinct` on `log`: a family-4 key with a cell's primary declares that
cell's link. -/
theorem declared4_cell {log small : List IntentRecord} (distinct : KeysDistinct keyHash (hashInputs log))
    (cells : ∀ c ∈ logCells small, c ∈ logCells log) {cell : CellId} (inLog : cell ∈ logCells log)
    {k : IndexKey} (primary : k.primary = cellPrimary cell) :
    declared4 small k = ((linkState small cell).find? fun e => linkKey cell e.1 = k).map
      fun e => factsValue cell e.1 e.2.1 e.2.2 := by
  unfold declared4
  cases found : (logCells small).find? (fun c => cellPrimary c = k.primary) with
  | some other =>
      have member := List.mem_of_find?_eq_some found
      have same := List.find?_some found
      simp only [decide_eq_true_eq] at same
      rw [cellPrimary_injective distinct (cells other member) inLog (same.trans primary)]
      rfl
  | none =>
      have away : cell ∉ logCells small := by
        intro member
        rw [List.find?_eq_none] at found
        exact found cell member (by simp [primary])
      rw [linkState_never small away]
      rfl

/-- Over `small` (links among `log`'s), a family-5 key whose pair secondary is
that of a link of `log` declares only that cell's rows. -/
theorem declared5_owner {log small : List IntentRecord} (distinct : KeysDistinct keyHash (hashInputs log))
    (links : ∀ x ∈ logLinks small, x ∈ logLinks log) {cell : CellId} {link : LinkId} {record : LinkRecord}
    (owner : (cell, link, record) ∈ logLinks log) {k : IndexKey} (secondary : k.secondary = pairSecondary cell link) :
    declared5 small k = cell5 small cell k := by
  rw [declared5_eq]
  have others : ∀ c ∈ logCells small, c ≠ cell → cell5 small c k = none := by
    intro c _ differ
    unfold cell5
    apply findSome?_none_of
    intro e member
    rw [if_neg]
    rintro ⟨hit, _⟩
    have := pairSecondary_injective distinct (links _ (mem_linkState member)) owner (hit.symm.trans secondary)
    exact differ this.1
  by_cases member : cell ∈ logCells small
  · exact findSome?_single _ _ others member
  · rw [findSome?_none_of _ _ (fun c inC => others c inC (fun same => member (same ▸ inC)))]
    unfold cell5; rw [linkState_never small member]; rfl

end Cells

/-! ### One record against a represented map -/

section Step

variable {records : List IntentRecord} {record : IntentRecord} {m : List (IndexKey × List UInt8)}
  {priors : Priors}

theorem cells_sub : ∀ c ∈ logCells records, c ∈ logCells (records ++ [record]) := by
  intro c member; rw [logCells_snoc]; exact List.mem_append_left _ member

theorem links_sub : ∀ x ∈ logLinks records, x ∈ logLinks (records ++ [record]) := by
  intro x member; rw [logLinks_snoc]; exact List.mem_append_left _ member

theorem written_in_log {cell : CellId} (written : cell ∈ writtenCells record) :
    cell ∈ logCells (records ++ [record]) := by
  rw [logCells_snoc]; exact List.mem_append_right _ (mem_writtenCells.mp written)

theorem lastLinks_in_log {cell : CellId} {link : LinkKey} (member : link ∈ lastLinks cell record) :
    (cell, link.1, link.2) ∈ logLinks (records ++ [record]) := by
  rw [logLinks_snoc]; exact List.mem_append_right _ (mem_lastLinks member)

theorem declared_family {k : IndexKey} (log : List IntentRecord) :
    (k.family = Family.presence → declared log k = declared2 log k) ∧
    (k.family = Family.links → declared log k = declared4 log k) ∧
    (k.family = Family.backlinks → declared log k = declared5 log k) ∧
    (k.family = Family.payer → declared log k = declared6 log k) ∧
    (k.family = Family.incoming → declared log k = declared7 log k) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    simp [declared, h, Family.spent, Family.transaction, Family.presence, Family.links, Family.backlinks,
      Family.payer, Family.incoming]

theorem mem_iff_lookup (before : Represents m records) (k : IndexKey) (v : List UInt8) :
    (k, v) ∈ m ↔ declared records k = some v := by
  rw [← before.2 k]
  exact ⟨mapLookup_of_mem before.1, mem_of_mapLookup⟩

theorem prior_mem (before : Represents m records) (read : PriorsOf m record priors) {cell : CellId}
    (written : cell ∈ writtenCells record) (k : IndexKey) (v : List UInt8) :
    (k, v) ∈ priors.links cell ↔
      (k.family = Family.links ∧ k.primary = cellPrimary cell) ∧ declared4 records k = some v := by
  rw [read.2 cell written k v, linkPrefix_iff, mem_iff_lookup before]
  constructor
  · rintro ⟨declares, family⟩
    exact ⟨family, by rw [← (declared_family records).2.1 family.1]; exact declares⟩
  · rintro ⟨family, declares⟩
    exact ⟨by rw [(declared_family records).2.1 family.1]; exact declares, family⟩

theorem decode_facts (facts : LinkFacts) : linkFactsStream.toLawful.decode (linkFactsStream.encode facts) = some facts :=
  linkFactsStream.toLawful.decode_encode facts

theorem linkState_find_key (distinct : KeysDistinct keyHash (hashInputs (records ++ [record]))) {log : List IntentRecord}
    (links : ∀ x ∈ logLinks log, x ∈ logLinks (records ++ [record])) {cell : CellId}
    {e : LinkId × LinkRecord × Nat} (member : e ∈ linkState log cell) :
    (linkState log cell).find? (fun e' => linkKey cell e'.1 = linkKey cell e.1) = some e := by
  apply find?_of_unique _ _ member (by simp)
  intro e' inE' same
  simp only [decide_eq_true_eq, linkKey, IndexKey.mk.injEq, true_and] at same
  have ids := linkSecondary_injective distinct (links _ (mem_linkState inE')) (links _ (mem_linkState member)) same
  exact eq_of_mem_of_fst_eq (linkState_ids_nodup log cell) inE' member ids

theorem priorFacts_mem (distinct : KeysDistinct keyHash (hashInputs (records ++ [record])))
    (before : Represents m records) (read : PriorsOf m record priors) {cell : CellId}
    (written : cell ∈ writtenCells record) (x : LinkId × LinkFacts) :
    x ∈ priorFacts (priors.links cell) ↔
      ∃ e ∈ linkState records cell, x = (e.1, factsOf cell e.1 e.2.1 e.2.2) := by
  unfold priorFacts
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨k, v⟩, inPrior, decoded⟩
    obtain ⟨⟨family, primary⟩, declares⟩ := (prior_mem before read written k v).mp inPrior
    rw [declared4_cell distinct cells_sub (written_in_log written) primary] at declares
    obtain ⟨e, found, value⟩ := Option.map_eq_some_iff.mp declares
    refine ⟨e, List.mem_of_find?_eq_some found, ?_⟩
    simp only at decoded
    rw [← value] at decoded
    unfold factsValue at decoded
    rw [decode_facts] at decoded
    simp only [Option.map_some, Option.some.injEq] at decoded
    rw [← decoded]
    rfl
  · rintro ⟨e, member, rfl⟩
    refine ⟨(linkKey cell e.1, factsValue cell e.1 e.2.1 e.2.2), ?_, ?_⟩
    · have family : (linkKey cell e.1).family = Family.links := rfl
      have primary : (linkKey cell e.1).primary = cellPrimary cell := rfl
      refine (prior_mem before read written (linkKey cell e.1) (factsValue cell e.1 e.2.1 e.2.2)).mpr
        ⟨⟨family, primary⟩, ?_⟩
      rw [declared4_cell distinct cells_sub (written_in_log written) primary,
        linkState_find_key distinct links_sub member]
      rfl
    · simp only [factsValue, decode_facts, Option.map_some]
      rfl

/-- **The new links keep exactly the live-since heights the log assigns**: the
facts a record's rows write for a written cell are the facts of its links after
the record. -/
theorem newFacts_eq (distinct : KeysDistinct keyHash (hashInputs (records ++ [record])))
    (before : Represents m records) (read : PriorsOf m record priors) {cell : CellId}
    (written : cell ∈ writtenCells record) :
    newFacts (records.length + 1) cell record (priors.links cell) =
      (linkState (records ++ [record]) cell).map fun e => (e.1, factsOf cell e.1 e.2.1 e.2.2) := by
  rw [linkState_written records record written]
  unfold newFacts
  rw [List.map_map]
  apply List.map_congr_left
  intro link inLinks
  simp only [Function.comp_apply]
  congr 3
  by_cases present : ∃ e ∈ linkState records cell, e.1 = link.1 ∧ e.2.1 = link.2
  · obtain ⟨e, member, sameId, sameRecord⟩ := present
    have unique : ∀ e' ∈ linkState records cell, e'.1 = link.1 → e' = e := fun e' inE' same =>
      eq_of_mem_of_fst_eq (linkState_ids_nodup records cell) inE' member (same.trans sameId.symm)
    have stateFound : (linkState records cell).find? (fun e' => e'.1 = link.1 ∧ e'.2.1 = link.2) = some e := by
      apply find?_of_unique _ _ member
      · simp [sameId, sameRecord]
      · intro e' inE' holds
        have both : e'.1 = link.1 ∧ e'.2.1 = link.2 := by simpa using holds
        exact unique e' inE' both.1
    rw [stateFound]
    have priorFound : (priorFacts (priors.links cell)).find?
        (fun y => y.1 = link.1 ∧ y.2.recordDigest = recordDigest link.1 link.2) =
          some (e.1, factsOf cell e.1 e.2.1 e.2.2) := by
      apply find?_of_unique _ _ ((priorFacts_mem distinct before read written _).mpr ⟨e, member, rfl⟩)
      · simp [factsOf, sameId, sameRecord]
      intro y inY holds
      obtain ⟨e', inE', rfl⟩ := (priorFacts_mem distinct before read written y).mp inY
      simp only [decide_eq_true_eq] at holds
      rw [unique e' inE' holds.1]
    rw [priorFound]
    rfl
  · rw [List.find?_eq_none.mpr (fun e member holds => present ⟨e, member, by simpa using holds⟩)]
    rw [List.find?_eq_none.mpr]
    · rfl
    · intro y inY holds
      obtain ⟨e', inE', rfl⟩ := (priorFacts_mem distinct before read written y).mp inY
      simp only [decide_eq_true_eq, factsOf] at holds
      have := recordDigest_injective distinct (links_sub _ (mem_linkState inE')) (lastLinks_in_log inLinks)
        holds.2
      exact present ⟨e', inE', this.1, this.2⟩

theorem before_keys (before : Represents m records) (read : PriorsOf m record priors)
    (distinct : KeysDistinct keyHash (hashInputs (records ++ [record]))) {cell : CellId}
    (written : cell ∈ writtenCells record) {e : IndexKey × List UInt8}
    (member : e ∈ priorRows cell (priors.links cell)) :
    (e.1.family = Family.links ∧ e.1.primary = cellPrimary cell) ∨
      ∃ e' ∈ linkState records cell, ∃ target, e.1 = backlinkKey target cell e'.1 := by
  unfold priorRows at member
  rcases List.mem_append.mp member with inPrior | inDerived
  · exact Or.inl ((prior_mem before read written e.1 e.2).mp inPrior).1
  · obtain ⟨x, inFacts, inTargets⟩ := List.mem_flatMap.mp inDerived
    obtain ⟨target, _, rfl⟩ := List.mem_map.mp inTargets
    obtain ⟨e', inE', rfl⟩ := (priorFacts_mem distinct before read written x).mp inFacts
    exact Or.inr ⟨e', inE', target, rfl⟩

theorem after_keys (before : Represents m records) (read : PriorsOf m record priors)
    (distinct : KeysDistinct keyHash (hashInputs (records ++ [record]))) {cell : CellId}
    (written : cell ∈ writtenCells record) {e : IndexKey × List UInt8}
    (member : e ∈ linkRows cell (newFacts (records.length + 1) cell record (priors.links cell))) :
    (e.1.family = Family.links ∧ e.1.primary = cellPrimary cell) ∨
      ∃ e' ∈ linkState (records ++ [record]) cell, ∃ target, e.1 = backlinkKey target cell e'.1 := by
  rw [newFacts_eq distinct before read written] at member
  unfold linkRows at member
  rcases List.mem_append.mp member with inLinks | inBacklinks
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp inLinks
    exact Or.inl ⟨rfl, rfl⟩
  · obtain ⟨x, inFacts, inTargets⟩ := List.mem_flatMap.mp inBacklinks
    obtain ⟨target, _, rfl⟩ := List.mem_map.mp inTargets
    obtain ⟨e', inE', rfl⟩ := List.mem_map.mp inFacts
    exact Or.inr ⟨e', inE', target, rfl⟩

theorem lastFor_map_some {α : Type} (xs : List α) (key : α → IndexKey) (value : α → List UInt8) (k : IndexKey) :
    lastFor (xs.map fun x => (key x, some (value x))) k = ((xs.reverse.find? fun x => key x = k).map value).map some := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      rw [List.map_cons, lastFor, ih, List.reverse_cons, List.find?_append]
      cases (rest.reverse.find? fun x => key x = k) with
      | some y => rfl
      | none => by_cases here : key x = k <;> simp [here]

theorem findSome?_congr {α β : Type} (list : List α) (f g : α → Option β) (same : ∀ x ∈ list, f x = g x) :
    list.findSome? f = list.findSome? g := by
  induction list with
  | nil => rfl
  | cons x rest ih =>
      rw [List.findSome?_cons, List.findSome?_cons, same x List.mem_cons_self,
        ih (fun y inY => same y (List.mem_cons_of_mem _ inY))]

/-! ### Each family across one record -/

theorem step01 (fresh : ∀ k ∈ keys01 record, declared records k = none) (k : IndexKey)
    (family : k.family = Family.spent ∨ k.family = Family.transaction) :
    (lastFor (changes01 (records.length + 1) record) k).getD (declared01 records k) =
      declared01 (records ++ [record]) k := by
  unfold changes01
  rw [lastFor_map_some]
  unfold declared01
  rw [zipIdx_snoc, List.find?_append]
  by_cases mem : k ∈ keys01 record
  · have none : declared01 records k = none := by
      have := fresh k mem
      simpa [declared, family] using this
    unfold declared01 at none
    rw [Option.map_eq_none_iff] at none
    have found : ((keys01 record).reverse.find? fun x => x = k) = some k :=
      find?_of_unique _ _ (List.mem_reverse.mpr mem) (by simp) (fun x _ h => by simpa using h)
    simp [found, none, mem]
  · have notFound : ((keys01 record).reverse.find? fun x => x = k) = none := by
      rw [List.find?_eq_none]; intro x member same; simp only [decide_eq_true_eq] at same
      exact mem (same ▸ List.mem_reverse.mp member)
    rw [notFound]
    cases (records.zipIdx 1).find? (fun entry => k ∈ keys01 entry.1) <;> simp [mem]

theorem step2 (k : IndexKey) :
    (lastFor (changes2 (records.length + 1) record) k).getD (declared2 records k) =
      declared2 (records ++ [record]) k := by
  unfold declared2
  rw [zipIdx_snoc, List.reverse_append, List.reverse_singleton, List.singleton_append, List.findSome?_cons]
  unfold changes2 presenceAt
  cases record.subject with
  | none => rfl
  | some subject =>
      simp only
      rw [lastFor_map_some]
      cases ((writtenCells record).reverse.find? fun cell => presenceKey subject cell = k) <;> rfl

theorem payerCount_value (count height : Nat) (transactionId : TransactionId) :
    payerCount (some (payerValue count height transactionId)) = count := by
  have decoded : payerStream.toLawful.decode (payerStream.encode (count, height, transactionId)) =
      some (count, height, transactionId) := payerStream.toLawful.decode_encode _
  simp [payerCount, payerValue, decoded]

theorem step6 (before : Represents m records) (read : PriorsOf m record priors) (k : IndexKey)
    (family : k.family = Family.payer) :
    (lastFor (changes6 (records.length + 1) record priors.payer) k).getD (declared6 records k) =
      declared6 (records ++ [record]) k := by
  have snoc : paying (records ++ [record]) k = paying records k ++
      (if (fleetOf record).map (fun fleet => payerKey fleet.1) = some k then [(record, records.length + 1)] else []) := by
    unfold paying; rw [zipIdx_snoc, List.filter_append]
    by_cases hit : (fleetOf record).map (fun fleet => payerKey fleet.1) = some k <;> simp [hit]
  unfold declared6
  rw [snoc]
  unfold changes6
  cases hfleet : fleetOf record with
  | none => simp [lastFor]
  | some fleet =>
      by_cases hit : payerKey fleet.1 = k
      · have prior : priors.payer = declared6 records k := by
          rw [read.1, hfleet]
          simp only [Option.bind_some]
          rw [before.2, hit, (declared_family records).2.2.2.1 family]
        have count : payerCount priors.payer = (paying records k).length := by
          rw [prior]; unfold declared6
          cases hlast : (paying records k).getLast? with
          | none => rw [List.getLast?_eq_none_iff.mp hlast]; rfl
          | some last => simp [payerCount_value]
        simp [lastFor, hit, count]
      · simp [lastFor, hit]

theorem step7 (k : IndexKey) :
    (lastFor (changes7 (records.length + 1) record) k).getD (declared7 records k) =
      declared7 (records ++ [record]) k := by
  unfold declared7
  rw [zipIdx_snoc, List.reverse_append, List.reverse_singleton, List.singleton_append, List.findSome?_cons]
  unfold changes7 incomingAt
  rcases fleetOf record with _ | ⟨payer, _ | destination⟩
  · rfl
  · rfl
  · by_cases hit : incomingKey destination (records.length + 1) = k <;> simp [lastFor, hit]

theorem prior_lookup (before : Represents m records) (read : PriorsOf m record priors) {cell : CellId}
    (written : cell ∈ writtenCells record) {k : IndexKey} (family : k.family = Family.links)
    (primary : k.primary = cellPrimary cell) :
    mapLookup (priorRows cell (priors.links cell)) k = mapLookup m k := by
  unfold priorRows
  rw [mapLookup_append]
  have none : mapLookup ((priorFacts (priors.links cell)).flatMap fun entry =>
      entry.2.targets.map fun target => (backlinkKey target cell entry.1, linkRowStream.encode entry.2.row)) k = none := by
    apply mapLookup_none_of_keys
    intro e member same
    obtain ⟨x, _, inTargets⟩ := List.mem_flatMap.mp member
    obtain ⟨target, _, rfl⟩ := List.mem_map.mp inTargets
    have := congrArg IndexKey.family same
    simp [backlinkKey, family, Family.backlinks, Family.links] at this
  rw [none, Option.or_none]
  apply mapLookup_congr
  · intro v
    rw [prior_mem before read written k v, mem_iff_lookup before, (declared_family records).2.1 family]
    simp [family, primary]
  · intro v v' inV inV'
    have := (mapLookup_of_mem before.1 inV).symm.trans (mapLookup_of_mem before.1 inV')
    exact Option.some.inj this

/-- **Family 4 across one record.** -/
theorem step4 (distinct : KeysDistinct keyHash (hashInputs (records ++ [record])))
    (before : Represents m records) (read : PriorsOf m record priors) (k : IndexKey)
    (family : k.family = Family.links) :
    (lastFor (changesLinks (records.length + 1) record priors) k).getD (mapLookup m k) =
      declared4 (records ++ [record]) k := by
  unfold changesLinks
  by_cases owned : ∃ cell ∈ writtenCells record, cellPrimary cell = k.primary
  · obtain ⟨cell, written, primary⟩ := owned
    rw [lastFor_flatMap_one _ (writtenCells_nodup record) _ k written]
    · have afterLookup : mapLookup (linkRows cell (newFacts (records.length + 1) cell record (priors.links cell))) k =
          declared4 (records ++ [record]) k := by
        rw [newFacts_eq distinct before read written]
        unfold linkRows
        rw [mapLookup_append]
        have none : mapLookup ((((linkState (records ++ [record]) cell).map fun e =>
            (e.1, factsOf cell e.1 e.2.1 e.2.2))).flatMap fun entry =>
              entry.2.targets.map fun target => (backlinkKey target cell entry.1,
                linkRowStream.encode entry.2.row)) k = none := by
          apply mapLookup_none_of_keys
          intro e member same
          obtain ⟨x, _, inTargets⟩ := List.mem_flatMap.mp member
          obtain ⟨target, _, rfl⟩ := List.mem_map.mp inTargets
          have := congrArg IndexKey.family same
          simp [backlinkKey, family, Family.backlinks, Family.links] at this
        rw [none, Option.or_none, List.map_map, mapLookup_map,
          declared4_cell distinct (fun c h => h) (written_in_log written) primary.symm]
        rfl
      rw [diff_getD, prior_lookup before read written family primary.symm, afterLookup]
      split
      · rename_i same; exact same.symm
      · rfl
    · intro other inOther differ
      apply lastFor_diff_away
      · intro e member same
        rcases before_keys before read distinct inOther member with ⟨_, otherPrimary⟩ | ⟨e', _, target, key⟩
        · apply differ
          exact cellPrimary_injective distinct (written_in_log inOther) (written_in_log written)
            (otherPrimary.symm.trans ((congrArg IndexKey.primary same).trans primary.symm))
        · have := congrArg IndexKey.family (key.symm.trans same)
          simp [backlinkKey, family, Family.backlinks, Family.links] at this
      · intro e member same
        rcases after_keys before read distinct inOther member with ⟨_, otherPrimary⟩ | ⟨e', _, target, key⟩
        · apply differ
          exact cellPrimary_injective distinct (written_in_log inOther) (written_in_log written)
            (otherPrimary.symm.trans ((congrArg IndexKey.primary same).trans primary.symm))
        · have := congrArg IndexKey.family (key.symm.trans same)
          simp [backlinkKey, family, Family.backlinks, Family.links] at this
  · rw [lastFor_flatMap_none]
    · rw [Option.getD_none, before.2, (declared_family records).2.1 family]
      unfold declared4
      rw [logCells_snoc, List.find?_append]
      have fresh : ((record.writes.map DataWrite.cellId).find? fun c => cellPrimary c = k.primary) = none := by
        rw [List.find?_eq_none]
        intro c member same
        exact owned ⟨c, mem_writtenCells.mpr member, by simpa using same⟩
      rw [fresh, Option.or_none]
      cases found : (logCells records).find? (fun c => cellPrimary c = k.primary) with
      | none => rfl
      | some c =>
          have away : c ∉ writtenCells record := fun written =>
            owned ⟨c, written, by simpa using List.find?_some found⟩
          simp only [Option.bind_some]
          rw [linkState_unwritten records record away]
    · intro cell written
      apply lastFor_diff_away
      · intro e member same
        rcases before_keys before read distinct written member with ⟨_, cellP⟩ | ⟨e', _, target, key⟩
        · exact owned ⟨cell, written, cellP.symm.trans (congrArg IndexKey.primary same)⟩
        · have := congrArg IndexKey.family (key.symm.trans same)
          simp [backlinkKey, family, Family.backlinks, Family.links] at this
      · intro e member same
        rcases after_keys before read distinct written member with ⟨_, cellP⟩ | ⟨e', _, target, key⟩
        · exact owned ⟨cell, written, cellP.symm.trans (congrArg IndexKey.primary same)⟩
        · have := congrArg IndexKey.family (key.symm.trans same)
          simp [backlinkKey, family, Family.backlinks, Family.links] at this

theorem cell5_none_of {log : List IntentRecord} {cell : CellId} {k : IndexKey}
    (miss : ∀ e ∈ linkState log cell, k.secondary ≠ pairSecondary cell e.1) : cell5 log cell k = none := by
  unfold cell5
  apply findSome?_none_of
  intro e member
  rw [if_neg]
  rintro ⟨hit, _⟩
  exact miss e member hit

/-- **Family 5 across one record.** -/
theorem step5 (distinct : KeysDistinct keyHash (hashInputs (records ++ [record])))
    (before : Represents m records) (read : PriorsOf m record priors) (k : IndexKey)
    (family : k.family = Family.backlinks) :
    (lastFor (changesLinks (records.length + 1) record priors) k).getD (mapLookup m k) =
      declared5 (records ++ [record]) k := by
  have notLinks : ∀ (e : IndexKey × List UInt8), e.1.family = Family.links → e.1 ≠ k := by
    intro e eFamily same
    rw [same, family] at eFamily
    simp [Family.backlinks, Family.links] at eFamily
  have backlinkSecondary : ∀ {target : Digest256} {cell : CellId} {link : LinkId},
      backlinkKey target cell link = k → k.secondary = pairSecondary cell link := by
    intro target cell link same
    rw [← same]; rfl
  unfold changesLinks
  by_cases owned : ∃ cell ∈ writtenCells record, ∃ e : LinkId × LinkRecord × Nat,
      (e ∈ linkState records cell ∨ e ∈ linkState (records ++ [record]) cell) ∧
        k.secondary = pairSecondary cell e.1
  · obtain ⟨cell, written, e, inEither, secondary⟩ := owned
    have owner : (cell, e.1, e.2.1) ∈ logLinks (records ++ [record]) := by
      rcases inEither with inS | inS'
      · exact links_sub _ (mem_linkState inS)
      · exact mem_linkState inS'
    rw [lastFor_flatMap_one _ (writtenCells_nodup record) _ k written]
    · -- What the record's rows write at `k`: the rows of the cell's links after the record.
      have afterLookup : mapLookup (linkRows cell (newFacts (records.length + 1) cell record (priors.links cell))) k =
          declared5 (records ++ [record]) k := by
        rw [newFacts_eq distinct before read written]
        unfold linkRows
        rw [mapLookup_append, mapLookup_none_of_keys _ k (fun x member => by
          obtain ⟨y, _, rfl⟩ := List.mem_map.mp member
          exact notLinks _ rfl), Option.none_or]
        rw [declared5_owner distinct (fun x h => h) owner secondary]
        unfold cell5
        rw [← mapLookup_rowsOf family]
        rw [List.flatMap_map]
        rfl
      -- What the prior rows held at `k`: the map's value.
      have priorLookup : mapLookup (priorRows cell (priors.links cell)) k = mapLookup m k := by
        unfold priorRows
        rw [mapLookup_append, mapLookup_none_of_keys _ k (fun x member =>
          notLinks x ((prior_mem before read written x.1 x.2).mp member).1.1), Option.none_or]
        rw [before.2, (declared_family records).2.2.1 family,
          declared5_owner distinct links_sub owner secondary]
        unfold cell5
        rw [← mapLookup_rowsOf family]
        apply mapLookup_congr
        · intro v
          constructor
          · intro member
            obtain ⟨x, inFacts, inTargets⟩ := List.mem_flatMap.mp member
            obtain ⟨target, inT, same⟩ := List.mem_map.mp inTargets
            obtain ⟨e', inE', rfl⟩ := (priorFacts_mem distinct before read written x).mp inFacts
            exact List.mem_flatMap.mpr ⟨e', inE', List.mem_map.mpr ⟨target, inT, same⟩⟩
          · intro member
            obtain ⟨e', inE', inTargets⟩ := List.mem_flatMap.mp member
            obtain ⟨target, inT, same⟩ := List.mem_map.mp inTargets
            exact List.mem_flatMap.mpr ⟨(e'.1, factsOf cell e'.1 e'.2.1 e'.2.2),
              (priorFacts_mem distinct before read written _).mpr ⟨e', inE', rfl⟩,
              List.mem_map.mpr ⟨target, inT, same⟩⟩
        · intro v v' inV inV'
          obtain ⟨e₁, in₁, inT₁⟩ := List.mem_flatMap.mp inV
          obtain ⟨t₁, _, same₁⟩ := List.mem_map.mp inT₁
          obtain ⟨e₂, in₂, inT₂⟩ := List.mem_flatMap.mp inV'
          obtain ⟨t₂, _, same₂⟩ := List.mem_map.mp inT₂
          have s₁ := backlinkSecondary (congrArg Prod.fst same₁)
          have s₂ := backlinkSecondary (congrArg Prod.fst same₂)
          have pair := pairSecondary_injective distinct (links_sub _ (mem_linkState in₁))
            (links_sub _ (mem_linkState in₂)) (s₁.symm.trans s₂)
          have := eq_of_mem_of_fst_eq (linkState_ids_nodup records cell) in₁ in₂ pair.2
          subst this
          exact (congrArg Prod.snd same₁).symm.trans (congrArg Prod.snd same₂)
      rw [diff_getD, priorLookup, afterLookup]
      split
      · rename_i same; exact same.symm
      · rfl
    · intro other inOther differ
      apply lastFor_diff_away
      · intro x member same
        rcases before_keys before read distinct inOther member with ⟨xFamily, _⟩ | ⟨e', inE', target, key⟩
        · exact notLinks x xFamily same
        · have hit := backlinkSecondary (key.symm.trans same)
          exact differ (pairSecondary_injective distinct (links_sub _ (mem_linkState inE')) owner
            (hit.symm.trans secondary)).1
      · intro x member same
        rcases after_keys before read distinct inOther member with ⟨xFamily, _⟩ | ⟨e', inE', target, key⟩
        · exact notLinks x xFamily same
        · have hit := backlinkSecondary (key.symm.trans same)
          exact differ (pairSecondary_injective distinct (mem_linkState inE') owner
            (hit.symm.trans secondary)).1
  · have missBefore : ∀ cell ∈ writtenCells record, ∀ e ∈ linkState records cell,
        k.secondary ≠ pairSecondary cell e.1 := fun cell written e member hit =>
      owned ⟨cell, written, e, Or.inl member, hit⟩
    have missAfter : ∀ cell ∈ writtenCells record, ∀ e ∈ linkState (records ++ [record]) cell,
        k.secondary ≠ pairSecondary cell e.1 := fun cell written e member hit =>
      owned ⟨cell, written, e, Or.inr member, hit⟩
    rw [lastFor_flatMap_none]
    · rw [Option.getD_none, before.2, (declared_family records).2.2.1 family, declared5_eq, declared5_eq,
        logCells_snoc, List.findSome?_append]
      rw [findSome?_none_of (record.writes.map DataWrite.cellId) _ (fun c member =>
        cell5_none_of (missAfter c (mem_writtenCells.mpr member))), Option.or_none]
      apply findSome?_congr
      intro c _
      by_cases written : c ∈ writtenCells record
      · rw [cell5_none_of (missAfter c written), cell5_none_of (missBefore c written)]
      · unfold cell5; rw [linkState_unwritten records record written]
    · intro cell written
      apply lastFor_diff_away
      · intro x member same
        rcases before_keys before read distinct written member with ⟨xFamily, _⟩ | ⟨e', inE', target, key⟩
        · exact notLinks x xFamily same
        · exact missBefore cell written e' inE' (backlinkSecondary (key.symm.trans same))
      · intro x member same
        rcases after_keys before read distinct written member with ⟨xFamily, _⟩ | ⟨e', inE', target, key⟩
        · exact notLinks x xFamily same
        · exact missAfter cell written e' inE' (backlinkSecondary (key.symm.trans same))

theorem lastFor_family_none (changes : List (IndexKey × Option (List UInt8))) (k : IndexKey)
    (families : ∀ change ∈ changes, change.1.family ≠ k.family) : lastFor changes k = none :=
  lastFor_none_of_keys changes k fun change member same => families change member (congrArg IndexKey.family same)

theorem mem_diff_keys {before after : List (IndexKey × List UInt8)} {change : IndexKey × Option (List UInt8)}
    (member : change ∈ diff before after) :
    (∃ e ∈ before, e.1 = change.1) ∨ ∃ e ∈ after, e.1 = change.1 := by
  unfold diff at member
  obtain ⟨k, inKeys, made⟩ := List.mem_filterMap.mp member
  split at made
  · cases made
  · cases made
    rw [List.mem_dedup, List.mem_append] at inKeys
    rcases inKeys with inB | inA
    · obtain ⟨e, inE, same⟩ := List.mem_map.mp inB; exact Or.inl ⟨e, inE, same⟩
    · obtain ⟨e, inE, same⟩ := List.mem_map.mp inA; exact Or.inr ⟨e, inE, same⟩

theorem changesLinks_family (distinct : KeysDistinct keyHash (hashInputs (records ++ [record])))
    (before : Represents m records) (read : PriorsOf m record priors) :
    ∀ change ∈ changesLinks (records.length + 1) record priors,
      change.1.family = Family.links ∨ change.1.family = Family.backlinks := by
  intro change member
  unfold changesLinks at member
  obtain ⟨cell, written, inDiff⟩ := List.mem_flatMap.mp member
  rcases mem_diff_keys inDiff with ⟨e, inE, same⟩ | ⟨e, inE, same⟩
  · rw [← same]
    rcases before_keys before read distinct written inE with ⟨family, _⟩ | ⟨_, _, _, key⟩
    · exact Or.inl family
    · rw [key]; exact Or.inr rfl
  · rw [← same]
    rcases after_keys before read distinct written inE with ⟨family, _⟩ | ⟨_, _, _, key⟩
    · exact Or.inl family
    · rw [key]; exact Or.inr rfl

/-- **The model theorem.** A logical map that represents a log (`Represents`:
unique keys, each key's value what the log declares), advanced by a record's
rows computed from the map's own priors (`PriorsOf`: what verified openings and
reveals answer, `lookup_sound`/`reveal_sound`), represents the log with the
record appended — every family at once: the spent and transaction keys (fresh,
as `apply` checks), presence, the links of the record's FINAL write of each cell
with their live-since heights, their backlinks, the payer's count and latest
turn, and the incoming payment at this height. Families 4 and 5 need the key
hash injective on the log's inputs (`KeysDistinct`). -/
theorem IndexRows.changes_exact (records : List IntentRecord) (record : IntentRecord)
    (m : List (IndexKey × List UInt8)) (priors : Priors)
    (distinct : KeysDistinct keyHash (hashInputs (records ++ [record])))
    (before : Represents m records) (read : PriorsOf m record priors)
    (fresh : ∀ k ∈ keys01 record, declared records k = none) :
    Represents (modelApply m (changes (records.length + 1) record priors)) (records ++ [record]) := by
  refine ⟨modelApply_nodup _ _ before.1, fun k => ?_⟩
  rw [mapLookup_modelApply]
  unfold changes
  simp only [lastFor_append]
  have c01 : ∀ change ∈ changes01 (records.length + 1) record,
      change.1.family = Family.spent ∨ change.1.family = Family.transaction := by
    intro change member
    unfold changes01 keys01 at member
    simp only [List.map_cons, List.map_map, List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨n, _, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl rfl
  have c2 : ∀ change ∈ changes2 (records.length + 1) record, change.1.family = Family.presence := by
    intro change member
    unfold changes2 at member
    cases hs : record.subject with
    | none => rw [hs] at member; cases member
    | some subject =>
        rw [hs] at member
        obtain ⟨cell, _, rfl⟩ := List.mem_map.mp member
        rfl
  have cL := changesLinks_family distinct before read
  have c6 : ∀ change ∈ changes6 (records.length + 1) record priors.payer, change.1.family = Family.payer := by
    intro change member
    unfold changes6 at member
    cases hf : fleetOf record with
    | none => rw [hf] at member; cases member
    | some fleet => rw [hf] at member; simp at member; rw [member]; rfl
  have c7 : ∀ change ∈ changes7 (records.length + 1) record, change.1.family = Family.incoming := by
    intro change member
    unfold changes7 at member
    rcases hf : fleetOf record with _ | ⟨payer, _ | destination⟩ <;> rw [hf] at member
    · cases member
    · cases member
    · simp at member; rw [member]; rfl
  have away : ∀ (changes : List (IndexKey × Option (List UInt8))) (P : UInt8 → Prop),
      (∀ change ∈ changes, P change.1.family) → ¬ P k.family → lastFor changes k = none :=
    fun changes P holds notP => lastFor_family_none changes k fun change member same =>
      notP (same ▸ holds change member)
  have family := (declared_family (k := k) records)
  have family' := (declared_family (k := k) (records ++ [record]))
  by_cases f01 : k.family = Family.spent ∨ k.family = Family.transaction
  · rw [away _ (· = Family.presence) c2 (by rcases f01 with h | h <;> rw [h] <;> decide),
      away _ (fun f => f = Family.links ∨ f = Family.backlinks) cL (by rcases f01 with h | h <;> rw [h] <;> decide),
      away _ (· = Family.payer) c6 (by rcases f01 with h | h <;> rw [h] <;> decide),
      away _ (· = Family.incoming) c7 (by rcases f01 with h | h <;> rw [h] <;> decide)]
    simp only [Option.none_or]
    rw [before.2, show declared records k = declared01 records k by simp [declared, f01],
      show declared (records ++ [record]) k = declared01 (records ++ [record]) k by simp [declared, f01]]
    exact step01 fresh k f01
  have not01 := away _ (fun f => f = Family.spent ∨ f = Family.transaction) c01 f01
  rw [not01]
  by_cases f2 : k.family = Family.presence
  · rw [away _ (fun f => f = Family.links ∨ f = Family.backlinks) cL (by rw [f2]; decide),
      away _ (· = Family.payer) c6 (by rw [f2]; decide), away _ (· = Family.incoming) c7 (by rw [f2]; decide)]
    simp only [Option.none_or, Option.or_none]
    rw [before.2, family.1 f2, family'.1 f2]
    exact step2 k
  rw [away _ (· = Family.presence) c2 f2]
  by_cases f4 : k.family = Family.links
  · rw [away _ (· = Family.payer) c6 (by rw [f4]; decide), away _ (· = Family.incoming) c7 (by rw [f4]; decide)]
    simp only [Option.none_or, Option.or_none]
    rw [family'.2.1 f4]
    exact step4 distinct before read k f4
  by_cases f5 : k.family = Family.backlinks
  · rw [away _ (· = Family.payer) c6 (by rw [f5]; decide), away _ (· = Family.incoming) c7 (by rw [f5]; decide)]
    simp only [Option.none_or, Option.or_none]
    rw [family'.2.2.1 f5]
    exact step5 distinct before read k f5
  rw [away _ (fun f => f = Family.links ∨ f = Family.backlinks) cL (by rintro (h | h) <;> contradiction)]
  by_cases f6 : k.family = Family.payer
  · rw [away _ (· = Family.incoming) c7 (by rw [f6]; decide)]
    simp only [Option.none_or, Option.or_none]
    rw [before.2, family.2.2.2.1 f6, family'.2.2.2.1 f6]
    exact step6 before read k f6
  rw [away _ (· = Family.payer) c6 f6]
  by_cases f7 : k.family = Family.incoming
  · simp only [Option.none_or, Option.or_none]
    rw [before.2, family.2.2.2.2 f7, family'.2.2.2.2 f7]
    exact step7 k
  rw [away _ (· = Family.incoming) c7 f7]
  simp only [Option.none_or, Option.getD_none]
  rw [before.2]
  simp [declared, f01, f2, f4, f5, f6, f7]

end Step

/-! ## The key-distinctness floor: what it costs, and its teeth -/

theorem keyHash_value (input : List UInt8) :
    (keyHash input).val = (Sp800185Cshake256.hash keyCustomization input).digest.value := by
  unfold keyHash
  apply Nat.mod_eq_of_lt
  have bound := fixedValue_lt (Sp800185Cshake256.hash keyCustomization input).bytes
  rw [(Sp800185Cshake256.hash keyCustomization input).length_exact] at bound
  exact bound

/-- **A failure of `KeysDistinct` at the deployed hash is a cSHAKE256 collision**:
two different inputs under the key customization with one 32-byte output. The
floor is cSHAKE256's COLLISION resistance at 256 bits (about 2^128 work). -/
theorem keysDistinct_or_collision (inputs : List (List UInt8)) :
    KeysDistinct keyHash inputs ∨
      ∃ x y : List UInt8, x ≠ y ∧
        Sp800185Cshake256.hash keyCustomization x = Sp800185Cshake256.hash keyCustomization y := by
  by_cases holds : KeysDistinct keyHash inputs
  · exact Or.inl holds
  · right
    unfold KeysDistinct at holds
    push Not at holds
    obtain ⟨a, _, b, _, same, differ⟩ := holds
    refine ⟨a, b, differ, ?_⟩
    have values := congrArg Fin.val same
    rw [keyHash_value, keyHash_value] at values
    have digests : (Sp800185Cshake256.hash keyCustomization a).digest =
        (Sp800185Cshake256.hash keyCustomization b).digest := by
      cases hA : (Sp800185Cshake256.hash keyCustomization a).digest
      cases hB : (Sp800185Cshake256.hash keyCustomization b).digest
      rw [hA, hB] at values; simp only at values; rw [values]
    have bytes := congrArg Sp800185Cshake256.digestBytesLE digests
    rw [Sp800185Cshake256.digestBytesLE_hash, Sp800185Cshake256.digestBytesLE_hash] at bytes
    cases hA : Sp800185Cshake256.hash keyCustomization a
    cases hB : Sp800185Cshake256.hash keyCustomization b
    rw [hA, hB] at bytes
    simp only at bytes
    subst bytes
    rfl

theorem KeysDistinct.mono {hash : List UInt8 → Digest256} {small large : List (List UInt8)}
    (distinct : KeysDistinct hash large) (sub : ∀ x ∈ small, x ∈ large) : KeysDistinct hash small :=
  fun a inA b inB same => distinct a (sub a inA) b (sub b inB) same

namespace Teeth

/-- **Satisfiable at the deployed hash**: three distinct key inputs (two cells'
family-4 primaries and a link's secondary) hash apart. Checked by the compiled
evaluator (cSHAKE256 does not reduce in the kernel). -/
theorem keysDistinct_deployed :
    KeysDistinct keyHash [Family.links :: cellBytes ⟨1⟩, Family.links :: cellBytes ⟨2⟩,
      Family.links :: 0xFF :: linkBytes ⟨⟨1⟩⟩] := by
  unfold KeysDistinct
  native_decide

/-- **Refutable**: a hash that collides (here a constant one) on two different
inputs violates it, so the premise is not a tautology of the key shape. -/
theorem keysDistinct_refuted : ¬ KeysDistinct (fun _ => 0) [[0], [1]] := by
  intro distinct
  have := distinct [0] (by simp) [1] (by simp) rfl
  simp at this

end Teeth

/-! ## What each family's declared value means -/

section Meaning

theorem subjectBytes_injective {a b : SubjectId} (same : subjectBytes a = subjectBytes b) : a = b := by
  have := HyperdocumentCodec.streamCodec_encode_injective StreamCodec.nat same
  cases a; cases b; simp_all

theorem accountBytes_injective {a b : Nat} (same : accountBytes a = accountBytes b) : a = b :=
  HyperdocumentCodec.streamCodec_encode_injective StreamCodec.nat same

theorem hashInputs_snoc_sub (log : List IntentRecord) (record : IntentRecord) :
    ∀ x ∈ hashInputs log, x ∈ hashInputs (log ++ [record]) := by
  intro x member
  unfold hashInputs at member ⊢
  rw [List.flatMap_append, logLinks_snoc, List.flatMap_append]
  rcases List.mem_append.mp member with h | h
  · exact List.mem_append_left _ (List.mem_append_left _ h)
  · exact List.mem_append_right _ (List.mem_append_left _ h)

theorem find?_congr {α : Type} (list : List α) (p q : α → Bool) (same : ∀ x ∈ list, p x = q x) :
    list.find? p = list.find? q := by
  induction list with
  | nil => rfl
  | cons x rest ih =>
      rw [List.find?_cons, List.find?_cons, same x List.mem_cons_self,
        ih (fun y inY => same y (List.mem_cons_of_mem _ inY))]

/-- The greatest height whose record is signed by `subject` and writes `cell`. -/
def lastSeen (log : List IntentRecord) (subject : SubjectId) (cell : CellId) : Option Nat :=
  ((log.zipIdx 1).filter fun entry => entry.1.subject = some subject ∧ cell ∈ writtenCells entry.1).getLast?.map (·.2)

theorem lastSeen_snoc (log : List IntentRecord) (record : IntentRecord) (subject : SubjectId) (cell : CellId) :
    lastSeen (log ++ [record]) subject cell =
      if record.subject = some subject ∧ cell ∈ writtenCells record then some (log.length + 1)
      else lastSeen log subject cell := by
  unfold lastSeen
  rw [zipIdx_snoc, List.filter_append]
  by_cases hit : record.subject = some subject ∧ cell ∈ writtenCells record
  · simp [hit]
  · have : ¬ (record.subject = some subject ∧ cell ∈ writtenCells record) := hit
    simp [this]

/-- What one record declares at a presence key, when the key hash separates its inputs. -/
theorem presenceAt_key (record : IntentRecord) (height : Nat) (subject : SubjectId) (cell : CellId)
    {inputs : List (List UInt8)} (distinct : KeysDistinct keyHash inputs)
    (mine : (Family.presence :: subjectBytes subject) ∈ inputs ∧ (Family.presence :: 0xFF :: cellBytes cell) ∈ inputs)
    (theirs : ∀ x ∈ recordInputs record, x ∈ inputs) :
    presenceAt record height (presenceKey subject cell) =
      if record.subject = some subject ∧ cell ∈ writtenCells record then some (presenceValue cell height) else none := by
  unfold presenceAt
  cases hs : record.subject with
  | none => simp
  | some signer =>
      have memSubject : (Family.presence :: subjectBytes signer) ∈ recordInputs record := by
        unfold recordInputs; rw [hs]; exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
      have memCell : ∀ write ∈ record.writes,
          (Family.presence :: 0xFF :: cellBytes write.cellId) ∈ recordInputs record := by
        intro write inWrites
        unfold recordInputs; rw [hs]
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨write, inWrites, rfl⟩)))
      have sameCell : ∀ c ∈ (writtenCells record).reverse, presenceKey signer c = presenceKey subject cell →
          signer = subject ∧ c = cell := by
        intro c member same
        simp only [presenceKey, IndexKey.mk.injEq, true_and] at same
        obtain ⟨write, inWrites, rfl⟩ := List.mem_map.mp (mem_writtenCells.mp (List.mem_reverse.mp member))
        have signerSame := keyHash_cons_injective distinct (theirs _ memSubject) mine.1 same.1
        have cellSame := keyHash_cons_injective distinct (theirs _ (memCell write inWrites)) mine.2 same.2
        exact ⟨subjectBytes_injective signerSame, cellBytes_injective (List.cons.inj cellSame).2⟩
      by_cases hit : signer = subject ∧ cell ∈ writtenCells record
      · obtain ⟨rfl, written⟩ := hit
        have found : ((writtenCells record).reverse.find? fun c => presenceKey signer c = presenceKey signer cell) =
            some cell :=
          find?_of_unique _ _ (List.mem_reverse.mpr written) (by simp)
            (fun c member same => (sameCell c member (by simpa using same)).2)
        simp [found, written]
      · have notFound : ((writtenCells record).reverse.find? fun c => presenceKey signer c = presenceKey subject cell) =
            none := by
          rw [List.find?_eq_none]
          intro c member same
          obtain ⟨signerSame, cellSame⟩ := sameCell c member (by simpa using same)
          exact hit ⟨signerSame, cellSame ▸ List.mem_reverse.mp member⟩
        dsimp only
        rw [notFound]
        simp only [Option.map_none, Option.some.injEq]
        rw [if_neg hit]

/-- **Presence means the greatest height the subject wrote the cell.** -/
theorem presence_meaning (log : List IntentRecord) (subject : SubjectId) (cell : CellId)
    (distinct : KeysDistinct keyHash
      ((Family.presence :: subjectBytes subject) :: (Family.presence :: 0xFF :: cellBytes cell) :: hashInputs log)) :
    declared log (presenceKey subject cell) = (lastSeen log subject cell).map (presenceValue cell) := by
  rw [(declared_family log).1 rfl]
  induction log using List.reverseRecOn with
  | nil => rfl
  | append_singleton rest record ih =>
      have small := distinct.mono (fun x member => by
        rcases List.mem_cons.mp member with h | h
        · exact h ▸ List.mem_cons_self
        rcases List.mem_cons.mp h with h | h
        · exact h ▸ List.mem_cons_of_mem _ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hashInputs_snoc_sub rest record x h)))
      unfold declared2 at *
      rw [zipIdx_snoc, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.findSome?_cons, ih small, lastSeen_snoc]
      rw [presenceAt_key record _ subject cell distinct ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
        (fun x member => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_flatMap.mpr ⟨record, List.mem_append_right _ List.mem_cons_self, member⟩))))]
      by_cases hit : record.subject = some subject ∧ cell ∈ writtenCells record
      · simp [hit]
      · have : ¬ (record.subject = some subject ∧ cell ∈ writtenCells record) := hit
        simp [this]

theorem record_inputs_in {log : List IntentRecord} {record : IntentRecord} (member : record ∈ log) :
    ∀ x ∈ recordInputs record, x ∈ hashInputs log := fun x inX =>
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨record, member, inX⟩)

/-- **The links family holds a cell's latest live links** (the old link index's
forward map, `LinkIndex.latestLinks`), each with its live-since height. -/
theorem linkState_keys (log : List IntentRecord) (cell : CellId) :
    (linkState log cell).map (fun e => (e.1, e.2.1)) = Kernel.LinkIndex.latestLinks cell log := by
  induction log using List.reverseRecOn with
  | nil => rfl
  | append_singleton rest record ih =>
      rw [linkState_snoc, Kernel.LinkIndex.latestLinks_snoc]
      unfold linkStep
      cases lastWrite cell record with
      | none => exact ih
      | some write => simp [List.map_map, Function.comp_def]

/-- **Links mean the cell's live links with their live-since heights**: the
family-4 value at `(cell, link)` is the facts of `link` in `linkState`. -/
theorem links_meaning (log : List IntentRecord) (cell : CellId) (link : LinkId)
    (distinct : KeysDistinct keyHash
      ((Family.links :: cellBytes cell) :: (Family.links :: 0xFF :: linkBytes link) :: hashInputs log)) :
    declared log (linkKey cell link) =
      ((linkState log cell).find? fun e => e.1 = link).map fun e => factsValue cell link e.2.1 e.2.2 := by
  rw [(declared_family log).2.1 rfl]
  unfold declared4
  cases found : (logCells log).find? (fun c => cellPrimary c = (linkKey cell link).primary) with
  | none =>
      have away : cell ∉ logCells log := by
        intro member; rw [List.find?_eq_none] at found; exact found cell member (by simp [linkKey])
      rw [linkState_never log away]; rfl
  | some other =>
      have inLog := List.mem_of_find?_eq_some found
      have same := List.find?_some found
      simp only [decide_eq_true_eq, linkKey] at same
      have := keyHash_cons_injective distinct (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (mem_hashInputs_cell inLog))) List.mem_cons_self same
      rw [cellBytes_injective this]
      simp only [Option.bind_some]
      rw [find?_congr (linkState log cell) _ (fun e => decide (e.1 = link)) (fun e member => by
        simp only [linkKey, IndexKey.mk.injEq, true_and, decide_eq_decide]
        constructor
        · intro hit
          have := keyHash_cons_injective distinct
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_hashInputs_link (mem_linkState member)
              (by simp [linkInputs]))))
            (List.mem_cons_of_mem _ List.mem_cons_self) hit
          exact linkBytes_injective (List.cons.inj this).2
        · intro hit; rw [hit])]
      cases hfind : (linkState log cell).find? (fun e => decide (e.1 = link)) with
      | none => rw [Option.map_none, Option.map_none]
      | some e =>
          have := List.find?_some hfind
          simp only [decide_eq_true_eq] at this
          simp [this, factsValue]

/-- **Backlinks are the inversion over `targetsOf`**: the family-5 row of
`(cell, link)` under target `t` is present exactly when `link` is a live link of
`cell` filed under `t` (its target, or the document its transclusion reads), and
it is that link's row. -/
theorem backlinks_meaning (log : List IntentRecord) (target : TargetKey) (cell : CellId) (link : LinkId)
    (v : List UInt8)
    (distinct : KeysDistinct keyHash
      ((Family.backlinks :: 0xFF :: pairBytes cell link) :: (Family.backlinks :: targetBytes target) :: hashInputs log)) :
    declared log (backlinkKey (targetPrimary target) cell link) = some v ↔
      ∃ e ∈ linkState log cell, e.1 = link ∧ target ∈ targetsOf e.2.1 ∧ v = rowValue cell link e.2.1 e.2.2 := by
  rw [(declared_family log).2.2.1 rfl, declared5_eq]
  have pairIn : ∀ {c : CellId} {e : LinkId × LinkRecord × Nat}, e ∈ linkState log c →
      pairSecondary cell link = pairSecondary c e.1 → c = cell ∧ e.1 = link := by
    intro c e member same
    have := keyHash_cons_injective distinct
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_hashInputs_link (mem_linkState member)
        (by simp [linkInputs])))) List.mem_cons_self same.symm
    have := pairBytes_injective (List.cons.inj this).2
    exact ⟨this.1, this.2⟩
  have targetIn : ∀ {c : CellId} {e : LinkId × LinkRecord × Nat}, e ∈ linkState log c →
      (targetPrimary target ∈ targetPrimaries e.2.1 ↔ target ∈ targetsOf e.2.1) := by
    intro c e member
    unfold targetPrimaries
    constructor
    · intro inP
      obtain ⟨t, inT, same⟩ := List.mem_map.mp inP
      have := keyHash_cons_injective distinct
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_hashInputs_link (mem_linkState member)
          (List.mem_append_right _ (List.mem_map.mpr ⟨t, inT, rfl⟩)))))
        (List.mem_cons_of_mem _ List.mem_cons_self) same
      rw [← targetBytes_injective this]; exact inT
    · intro inT; exact List.mem_map.mpr ⟨target, inT, rfl⟩
  have others : ∀ c ∈ logCells log, c ≠ cell → cell5 log c (backlinkKey (targetPrimary target) cell link) = none :=
    fun c _ differ => cell5_none_of fun e member hit => differ (pairIn member hit).1
  have collapse : (logCells log).findSome? (fun c => cell5 log c (backlinkKey (targetPrimary target) cell link)) =
      cell5 log cell (backlinkKey (targetPrimary target) cell link) := by
    by_cases member : cell ∈ logCells log
    · exact findSome?_single _ _ others member
    · rw [findSome?_none_of _ _ (fun c inC => others c inC (fun same => member (same ▸ inC)))]
      unfold cell5; rw [linkState_never log member]; rfl
  rw [collapse]
  unfold cell5
  constructor
  · intro found
    obtain ⟨e, member, hit⟩ := List.exists_of_findSome?_eq_some found
    split at hit
    · rename_i cond
      obtain ⟨_, idSame⟩ := pairIn member cond.1
      refine ⟨e, member, idSame, (targetIn member).mp cond.2, ?_⟩
      cases hit; rw [idSame]
    · cases hit
  · rintro ⟨e, member, idSame, filed, rfl⟩
    rw [findSome?_single _ _ (a := e) (fun e' inE' differ => by
      rw [if_neg]
      rintro ⟨hit, _⟩
      exact differ (eq_of_mem_of_fst_eq (linkState_ids_nodup log cell) inE' member
        ((pairIn inE' hit).2.trans idSame.symm))) member]
    rw [if_pos ⟨by rw [idSame]; rfl, (targetIn member).mpr filed⟩, idSame]

/-- The records (with heights) that `payer` paid for. -/
def paidBy (log : List IntentRecord) (payer : Nat) : List (IntentRecord × Nat) :=
  (log.zipIdx 1).filter fun entry => (fleetOf entry.1).map (·.1) = some payer

/-- **The payer family means how many fleet turns the account paid, the latest
one's height and its transaction id.** -/
theorem payer_meaning (log : List IntentRecord) (payer : Nat)
    (distinct : KeysDistinct keyHash ((Family.payer :: accountBytes payer) :: hashInputs log)) :
    declared log (payerKey payer) =
      (paidBy log payer).getLast?.map fun entry => payerValue (paidBy log payer).length entry.2 entry.1.transactionId := by
  rw [(declared_family log).2.2.2.1 rfl]
  have same : paying log (payerKey payer) = paidBy log payer := by
    unfold paying paidBy
    apply List.filter_congr
    intro entry member
    have inLog := List.fst_mem_of_mem_zipIdx member
    cases hf : fleetOf entry.1 with
    | none => simp
    | some fleet =>
        simp only [Option.map_some, Option.some.injEq, decide_eq_decide]
        constructor
        · intro hit
          simp only [payerKey, IndexKey.mk.injEq, true_and, and_true] at hit
          have input : (Family.payer :: accountBytes fleet.1) ∈ recordInputs entry.1 := by
            unfold recordInputs; rw [hf]; exact List.mem_append_right _ List.mem_cons_self
          have := keyHash_cons_injective distinct (List.mem_cons_of_mem _ (record_inputs_in inLog _ input))
            List.mem_cons_self hit
          exact accountBytes_injective this
        · intro hit; rw [hit]
  unfold declared6
  rw [same]

/-- **The incoming family means the payments to the account**: the value at
`(destination, height)` is present exactly when the record at that height is a
fleet turn whose transfer pays `destination`, and it is that record's
transaction id. -/
theorem incoming_meaning (log : List IntentRecord) (destination height : Nat) (v : List UInt8)
    (distinct : KeysDistinct keyHash ((Family.incoming :: accountBytes destination) :: hashInputs log))
    (fits : log.length < 256 ^ 32) (heightFits : height < 256 ^ 32) :
    declared log (incomingKey destination height) = some v ↔
      ∃ record, (record, height) ∈ log.zipIdx 1 ∧ (fleetOf record).bind (·.2) = some destination ∧
        v = transactionValue record.transactionId := by
  rw [(declared_family log).2.2.2.2 rfl]
  unfold declared7
  have hit : ∀ entry ∈ (log.zipIdx 1).reverse, ∀ w, incomingAt entry.1 entry.2 (incomingKey destination height) = some w →
      entry.2 = height ∧ (fleetOf entry.1).bind (·.2) = some destination ∧ w = transactionValue entry.1.transactionId := by
    intro entry member w found
    have inZip := List.mem_reverse.mp member
    have inLog := List.fst_mem_of_mem_zipIdx inZip
    have bound := (List.mem_zipIdx (x := entry.1) (i := entry.2) inZip).2.1
    unfold incomingAt at found
    rcases hf : fleetOf entry.1 with _ | ⟨payer, _ | d⟩ <;> rw [hf] at found
    · cases found
    · cases found
    · dsimp only at found
      by_cases same : incomingKey d entry.2 = incomingKey destination height
      · rw [if_pos same] at found
        simp only [incomingKey, IndexKey.mk.injEq, true_and] at same
        have input : (Family.incoming :: accountBytes d) ∈ recordInputs entry.1 := by
          unfold recordInputs; rw [hf]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have dSame := accountBytes_injective (keyHash_cons_injective distinct
          (List.mem_cons_of_mem _ (record_inputs_in inLog _ input)) List.mem_cons_self same.1)
        have hSame := heightSecondary_injective (by omega) heightFits same.2
        cases found
        exact ⟨hSame, by simp [dSame], rfl⟩
      · rw [if_neg same] at found
        cases found
  constructor
  · intro found
    obtain ⟨entry, member, yields⟩ := List.exists_of_findSome?_eq_some found
    obtain ⟨atHeight, pays, rfl⟩ := hit entry member v yields
    exact ⟨entry.1, by rw [← atHeight]; exact List.mem_reverse.mp member, pays, rfl⟩
  · rintro ⟨record, member, pays, rfl⟩
    have yields : incomingAt record height (incomingKey destination height) =
        some (transactionValue record.transactionId) := by
      unfold incomingAt
      rcases hf : fleetOf record with _ | ⟨payer, _ | d⟩ <;> rw [hf] at pays
      · cases pays
      · cases pays
      · have dSame : d = destination := by simpa using pays
        subst dSame
        exact if_pos rfl
    rw [findSome?_single _ _ (a := (record, height)) (fun entry inE differ => by
      cases found : incomingAt entry.1 entry.2 (incomingKey destination height) with
      | none => rfl
      | some w =>
          exfalso
          obtain ⟨atHeight, _, _⟩ := hit entry inE w found
          apply differ
          have inZip := List.mem_reverse.mp inE
          have first := (List.mem_zipIdx (x := entry.1) (i := entry.2) inZip).2.2
          have second := (List.mem_zipIdx (x := record) (i := height) member).2.2
          obtain ⟨r, h⟩ := entry
          simp only at atHeight first
          subst atHeight
          rw [first, second]) (List.mem_reverse.mpr member)]
    exact yields

end Meaning

/-! ## Executed probes: the families through `setAll` and through `IndexRows.apply`

`FamiliesProbe.incremental_matches_canonical`: a sequence of sets over every
family's real keys — presence, a link inserted then RETARGETED (its family-4
value updated in place, its old backlink deleted, a new one inserted), a link
UNLINKED (its family-4 and family-5 leaves deleted, the subtree collapsing), a
payer count updated in place, two incoming heights, then every key deleted — and
after every step the incremental root is `rootOf` of the logical map, every
key's lookup verifies and answers the map's value, and each family's reveal
answers exactly its members.

`FamiliesProbe.records_match_declared`: real records (content cells whose
canonical bytes hold link records) through `IndexRows.apply` over in-memory rows,
the record's priors read by the trie's own verified lookups and reveals: after
every record the root is `rootOf` of the map the changes produce, and that map
answers `declared` of the log at every key the log names. -/

namespace FamiliesProbe

open Minidregg.Compiler.HyperdocumentCell (contentMaterializer)

def subjectA : SubjectId := ⟨41⟩
def subjectB : SubjectId := ⟨42⟩
def cellA : CellId := ⟨501⟩
def cellB : CellId := ⟨502⟩
def linkA : LinkId := ⟨⟨601⟩⟩
def linkB : LinkId := ⟨⟨602⟩⟩
def documentA : DocumentId := ⟨⟨701⟩⟩
def documentB : DocumentId := ⟨⟨702⟩⟩

def linkTo (document : DocumentId) (operation : Nat) : LinkRecord where
  sourceDocument := ⟨⟨100⟩⟩
  source := none
  target := .document document
  relation := ⟨1⟩
  author := ⟨⟨7⟩, .object, ⟨11⟩⟩
  operation := ⟨⟨operation⟩⟩
  tombstonedAt := none

def keys : List IndexKey :=
  [presenceKey subjectA cellA, presenceKey subjectA cellB, presenceKey subjectB cellA,
   linkKey cellA linkA, linkKey cellA linkB, linkKey cellB linkA,
   backlinkKey (targetPrimary (.document documentA)) cellA linkA,
   backlinkKey (targetPrimary (.document documentB)) cellA linkA,
   backlinkKey (targetPrimary (.document documentB)) cellA linkB,
   payerKey 9, incomingKey 7 3, incomingKey 7 5]

def factsA (document : DocumentId) (operation height : Nat) : List UInt8 :=
  factsValue cellA linkA (linkTo document operation) height

/-- Key index ↦ new value (`none` deletes). -/
def ops : List (Nat × Option (List UInt8)) :=
  [(0, some (presenceValue cellA 1)), (1, some (presenceValue cellB 1)), (2, some (presenceValue cellA 2)),
   (3, some (factsA documentA 300 1)), (6, some (rowValue cellA linkA (linkTo documentA 300) 1)),
   (4, some (factsValue cellA linkB (linkTo documentB 301) 1)),
   (8, some (rowValue cellA linkB (linkTo documentB 301) 1)),
   (5, some (factsValue cellB linkA (linkTo documentA 302) 2)),
   -- retarget linkA of cellA to document B at height 3
   (3, some (factsA documentB 303 3)), (6, none), (7, some (rowValue cellA linkA (linkTo documentB 303) 3)),
   -- unlink linkB of cellA
   (4, none), (8, none),
   -- payer: count 1 then 2 (same key), incoming at heights 3 and 5
   (9, some (payerValue 1 3 ⟨900⟩)), (10, some (transactionValue ⟨900⟩)),
   (9, some (payerValue 2 5 ⟨901⟩)), (11, some (transactionValue ⟨901⟩)),
   -- presence overwritten in place, then everything deleted
   (0, some (presenceValue cellA 5)),
   (0, none), (1, none), (2, none), (3, none), (5, none), (7, none), (9, none), (10, none), (11, none)]

def familyPrefix (family : UInt8) : List Bool := (bitsOf ⟨family, 0, 0⟩).take 8

def sameSet (a b : List (IndexKey × List UInt8)) : Bool :=
  a.length == b.length && a.all (b.contains ·) && b.all (a.contains ·)

def stepOk (rows : List Bool → Option Row) (root : Digest) (model : List (IndexKey × List UInt8)) : Bool :=
  root == rootOf model &&
  keys.all (fun k => match lookupRows rows root k with
    | .ok answer => answer.value == mapLookup model k
    | .error _ => false) &&
  [Family.presence, Family.links, Family.backlinks, Family.payer, Family.incoming].all (fun family =>
    match revealRows rows root (familyPrefix family) with
    | .ok revealed => sameSet revealed.members (model.filter (·.1.family = family))
    | .error _ => false) &&
  -- the prefix a cell's links are revealed under answers exactly that cell's links
  (match revealRows rows root (linkPrefix cellA) with
    | .ok revealed => sameSet revealed.members
        (model.filter fun e => e.1.family = Family.links ∧ e.1.primary = cellPrimary cellA)
    | .error _ => false)

def run : List (Nat × Option (List UInt8)) → List (List Bool × Row) → Digest →
    List (IndexKey × List UInt8) → Bool
  | [], _, root, model => model.isEmpty && root == emptyDigest
  | (i, value) :: rest, written, root, model =>
      let k := keys.getD i (payerKey 0)
      match setAll (overlay (fun _ => none) written) root [(k, value)] with
      | .error _ => false
      | .ok (root', rows) =>
          let written' := rows ++ written
          let model' := modelSet model k value
          stepOk (overlay (fun _ => none) written') root' model' && run rest written' root' model'

theorem incremental_matches_canonical : run ops [] emptyDigest [] = true := by native_decide

/-! ### Records through `IndexRows.apply` -/

/-- The canonical bytes of a live content cell holding exactly `links`. -/
def contentImage (links : List (LinkId × LinkRecord)) : List UInt8 :=
  [68, 82, 2, 1, 68, 82, 1, 1] ++ contentMaterializer.codec.encode
    (StoreCodec.fromEntries (links.map fun link => ⟨⟨.links, link.1⟩, link.2⟩))

def write (cell : CellId) (links : List (LinkId × LinkRecord)) : DataWrite :=
  ⟨cell, ⟨0⟩, ⟨0⟩, contentImage links⟩

def recordOf (number : Nat) (subject : Option SubjectId) (writes : List DataWrite) : IntentRecord :=
  ⟨⟨1000 + number⟩, writes, [], [⟨1, ⟨700⟩, ⟨number⟩, [UInt8.ofNat number]⟩], fun _ => 1,
    ⟨1, ⟨800⟩, ⟨number⟩, [UInt8.ofNat number]⟩, subject⟩

/-- Five records: two links of cell A; linkA retargeted (its record changes:
live-since restarts) while linkB is untouched (live-since kept); linkB unlinked
by another subject; cell B written with linkA by no subject; cell A rewritten
with linkA unchanged (kept). -/
def firstRecord : IntentRecord :=
  recordOf 1 (some subjectA) [write cellA [(linkA, linkTo documentA 300), (linkB, linkTo documentB 301)]]

def records : List IntentRecord :=
  [firstRecord,
   recordOf 2 (some subjectA) [write cellA [(linkA, linkTo documentB 303), (linkB, linkTo documentB 301)]],
   recordOf 3 (some subjectB) [write cellA [(linkA, linkTo documentB 303)]],
   recordOf 4 none [write cellB [(linkA, linkTo documentA 302)]],
   recordOf 5 (some subjectA) [write cellA [(linkA, linkTo documentB 303)], write cellB []]]

/-- Every key the probe log names (and a few it does not). -/
def namedKeys : List IndexKey :=
  keys ++ (records.flatMap keys01) ++ [presenceKey subjectB cellB, linkKey cellB linkB]

/-- The map's priors for a record, read the way `apply` reads them. -/
def priorsOf (model : List (IndexKey × List UInt8)) (record : IntentRecord) : Priors :=
  IndexRows.priorsWith (mapLookup model)
    (fun p => model.filter fun e => (bitsOf e.1).take p.length = p) record

def applyAll : List IntentRecord → List IntentRecord → List (List Bool × Row) → Digest →
    List (IndexKey × List UInt8) → Bool
  | [], _, _, _, _ => true
  | record :: rest, done, written, root, model =>
      let height := done.length + 1
      match IndexRows.apply (overlay (fun _ => none) written) root height record with
      | .error _ => false
      | .ok (root', rows) =>
          let model' := modelApply model (IndexRows.changes height record (priorsOf model record))
          let done' := done ++ [record]
          root' == rootOf model' &&
            namedKeys.all (fun k => mapLookup model' k == declared done' k) &&
            applyAll rest done' (rows ++ written) root' model'

theorem records_match_declared : applyAll records [] [] emptyDigest [] = true := by native_decide

/-- The live-since heights the log assigns, read back from the index after the
five records: linkA of cell A restarted at 2 (retargeted) and was kept through 3
and 5; linkB is gone; linkA of cell B was written at 4 and its cell emptied at 5. -/
theorem heights_after : (declared records (linkKey cellA linkA),
      declared records (linkKey cellA linkB), declared records (linkKey cellB linkA),
      declared records (backlinkKey (targetPrimary (.document documentA)) cellA linkA),
      declared records (presenceKey subjectB cellA)) =
    (some (factsValue cellA linkA (linkTo documentB 303) 2), none, none, none,
      some (presenceValue cellA 3)) := by native_decide

/-! ### DEPUTY-KERNEL condition 2: a record that drops and re-adds a link

The executor never accepts such a record (`DurableCommitProtocol.Intent.preflight`
refuses two writes of one cell, `duplicateCell`), so it is planted directly at
`IndexRows.apply`, the function every append and the audit run: one record
writes cell A twice — first without linkB, then with it again, unchanged. The
index reflects the FINAL write: linkB stays, live since height 1. The control,
a record whose only write drops linkB, deletes it. -/

def twoWrites : IntentRecord :=
  recordOf 2 (some subjectA) [write cellA [(linkA, linkTo documentA 300)],
    write cellA [(linkA, linkTo documentA 300), (linkB, linkTo documentB 301)]]

def dropOnly : IntentRecord :=
  recordOf 2 (some subjectA) [write cellA [(linkA, linkTo documentA 300)]]

def afterSecond (second : IntentRecord) : Option (Option (List UInt8)) :=
  match IndexRows.apply (overlay (fun _ => none) []) emptyDigest 1 firstRecord with
  | .error _ => none
  | .ok (root, rows) =>
      match IndexRows.apply (overlay (fun _ => none) rows) root 2 second with
      | .error _ => none
      | .ok (root', rows') =>
          match lookupRows (overlay (fun _ => none) (rows' ++ rows)) root' (linkKey cellA linkB) with
          | .ok answer => some answer.value
          | .error _ => none

theorem drop_and_readd_indexes_final : afterSecond twoWrites =
    some (some (factsValue cellA linkB (linkTo documentB 301) 1)) := by native_decide

theorem drop_only_deletes : afterSecond dropOnly = some none := by native_decide

end FamiliesProbe

#assert_axioms lastFor_append
#assert_axioms mapLookup_append
#assert_axioms mapLookup_cons
#assert_axioms mapLookup_filter_ne
#assert_axioms mapLookup_modelSet
#assert_axioms mapLookup_modelApply
#assert_axioms modelSet_nodup
#assert_axioms modelApply_nodup
#assert_axioms lastFor_none_of_keys
#assert_axioms lastFor_flatMap_none
#assert_axioms lastFor_flatMap_one
#assert_axioms keyHash_cons_injective
#assert_axioms digest_bytes_injective
#assert_axioms cellBytes_injective
#assert_axioms linkBytes_injective
#assert_axioms pairBytes_injective
#assert_axioms linkRecordBytes_injective
#assert_axioms targetBytes_injective
#assert_axioms zipIdx_snoc
#assert_axioms linkState_snoc
#assert_axioms logCells_snoc
#assert_axioms logLinks_snoc
#assert_axioms mem_writtenCells
#assert_axioms writtenCells_nodup
#assert_axioms lastWrite_none
#assert_axioms lastWrite_some
#assert_axioms linkState_unwritten
#assert_axioms linkState_written
#assert_axioms linkState_never
#assert_axioms linkState_ids_nodup
#assert_axioms mem_lastLinks
#assert_axioms mem_linkState
#assert_axioms mem_logCells_of_linkState
#assert_axioms find?_of_unique
#assert_axioms eq_of_mem_of_fst_eq
#assert_axioms mapLookup_map
#assert_axioms mapLookup_none_of_keys
#assert_axioms mem_of_mapLookup
#assert_axioms mapLookup_of_mem
#assert_axioms mapLookup_congr
#assert_axioms take_bytesBits
#assert_axioms prefix264
#assert_axioms linkPrefix_iff
#assert_axioms mem_hashInputs_cell
#assert_axioms mem_hashInputs_link
#assert_axioms cellPrimary_injective
#assert_axioms linkSecondary_injective
#assert_axioms recordDigest_injective
#assert_axioms pairSecondary_injective
#assert_axioms targetPrimary_injective
#assert_axioms lastFor_filterMap_self
#assert_axioms diff_getD
#assert_axioms lastFor_diff_away
#assert_axioms linkKey_eq_iff
#assert_axioms backlinkKey_eq_iff
#assert_axioms declared5_eq
#assert_axioms mapLookup_rowsOf
#assert_axioms findSome?_none_of
#assert_axioms findSome?_single
#assert_axioms declared4_cell
#assert_axioms declared5_owner
#assert_axioms cells_sub
#assert_axioms links_sub
#assert_axioms written_in_log
#assert_axioms lastLinks_in_log
#assert_axioms declared_family
#assert_axioms mem_iff_lookup
#assert_axioms prior_mem
#assert_axioms decode_facts
#assert_axioms linkState_find_key
#assert_axioms priorFacts_mem
#assert_axioms newFacts_eq
#assert_axioms before_keys
#assert_axioms after_keys
#assert_axioms lastFor_map_some
#assert_axioms findSome?_congr
#assert_axioms step01
#assert_axioms step2
#assert_axioms payerCount_value
#assert_axioms step6
#assert_axioms step7
#assert_axioms prior_lookup
#assert_axioms step4
#assert_axioms cell5_none_of
#assert_axioms step5
#assert_axioms lastFor_family_none
#assert_axioms mem_diff_keys
#assert_axioms changesLinks_family
#assert_axioms IndexRows.changes_exact
#assert_axioms keyHash_value
#assert_axioms keysDistinct_or_collision
#assert_axioms KeysDistinct.mono
#assert_compiled Teeth.keysDistinct_deployed
#assert_axioms Teeth.keysDistinct_refuted
#assert_axioms subjectBytes_injective
#assert_axioms accountBytes_injective
#assert_axioms hashInputs_snoc_sub
#assert_axioms find?_congr
#assert_axioms lastSeen_snoc
#assert_axioms presenceAt_key
#assert_axioms presence_meaning
#assert_axioms record_inputs_in
#assert_axioms linkState_keys
#assert_axioms links_meaning
#assert_axioms backlinks_meaning
#assert_axioms payer_meaning
#assert_axioms incoming_meaning
#assert_compiled FamiliesProbe.incremental_matches_canonical
#assert_compiled FamiliesProbe.records_match_declared
#assert_compiled FamiliesProbe.heights_after
#assert_compiled FamiliesProbe.drop_and_readd_indexes_final
#assert_compiled FamiliesProbe.drop_only_deletes

end Minidregg.Compiler.DurableIndex
