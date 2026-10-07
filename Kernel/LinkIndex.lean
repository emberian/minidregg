/-
# Kernel.LinkIndex — links and backlinks of hyperdocuments (K-DOC-INDEX)

The link index is a function of the accepted log, built the way
`Kernel.PresenceIndex` is:

* `sources : cell ↦ [entry]` — the live links of each content cell as of its
  latest accepted write: every link record of the cell's post-state whose
  `tombstonedAt` is `none`, each with the log height from which it has been
  live without a break (the forward index);
* `reverse : target ↦ [(cell, entry)]` — the same entries keyed by what they
  point at (the backlink index), updated INCREMENTALLY with the forward map:
  a write of a cell drops that cell's old pairs and adds its new ones
  (`setCell`), never re-inverting the whole forward map. `Exact` states that
  its membership is the inversion of the forward map (`RevExact`, the same
  statement as `mem_lookup_invert`); the rows of a target are held in
  insertion order but SERVED in a canonical order (`pairLe`: source cell, then
  link identifier), so what a reader sees depends on the forward map and not
  on the order writes arrived in (`backlinks_state`).

A link leaves both maps when a later accepted write of its cell no longer
holds it live (`ContentResource.Action.unlink` tombstones it), because the
forward map is replaced cell-by-cell from each write's post-state
(`sources_exact`).

**Where it lives.** The index is `ofRecords image.accepted`, cached on the
loaded image (`DurableReceiverIO.Loaded.links`, exact by `linksExact`) and
advanced by `Index.admit` on every append, beside the presence index. It is
not stored, not checkpointed, and not an authority-cell or `World` plane: the
log that determines it is MAC-chained and read whole on every open.

**What a reader sees.** `Index.backlinks visible keys` keeps only entries whose
SOURCE cell satisfies `visible` (`backlinks_covered`); the observation
controller instantiates `visible` with the cells a standing capability the
reader holds lets it observe, so a backlink from a document the reader cannot
read is not disclosed.
-/
import Kernel.PresenceIndex
import Compiler.CanonicalCellRegistry

namespace Minidregg.Kernel.LinkIndex

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.PresenceIndex (Occurs occurs_append_left occurs_snoc)

set_option autoImplicit false

abbrev ContentStore := Store.Store Hyperdocument.layout

/-- A link as stored: its identifier and its record. -/
abbrev LinkKey := LinkId × LinkRecord

/-! ## The live links of one cell image -/

/-- The content store a canonical cell image holds, when it is a live content cell. -/
def contentOf (bytes : List UInt8) : Option ContentStore :=
  match ResourceBirthCodec.LifecycleImage.rawDecode CanonicalCellRegistry.registry bytes with
  | some (.live cell) =>
      match cell with
      | ⟨.content, payload⟩ => some payload.logical
      | _ => none
  | _ => none

/-- The live (untombstoned) link records of a content store, in canonical entry order. -/
def linksOfStore (store : ContentStore) : List LinkKey :=
  (StoreCodec.entries HyperdocumentCell.contentWire store).filterMap fun entry =>
    match entry with
    | ⟨⟨.links, identifier⟩, record⟩ =>
        let identifier : LinkId := identifier
        let record : LinkRecord := record
        if record.tombstonedAt = none then some (identifier, record) else none
    | _ => none

/-- The live links of a cell image, decoding it fully; none for any cell that
is not live content. This is the specification; `liveLinks` computes it. -/
def liveLinksFull (bytes : List UInt8) : List LinkKey :=
  match contentOf bytes with
  | some store => linksOfStore store
  | none => []

/-- The cheap prefix test: a lifecycle `live` image (`68,82,2,1`) whose cell
envelope (`68,82,1`) carries the content kind tag (`1`). Every other cell (the
authority cell, books, clocks, streams, retired and fresh images) is skipped
without decoding its payload. -/
def contentPrefix : List UInt8 → Bool
  | 68 :: 82 :: 2 :: 1 :: 68 :: 82 :: 1 :: 1 :: _ => true
  | _ => false

theorem registry_content_tag : CanonicalCellRegistry.registry.tag .content = 1 := rfl

theorem kindAtTag_content (tag : UInt8) (found : CanonicalCellRegistry.kindAtTag tag = some .content) :
    tag = 1 := by
  unfold CanonicalCellRegistry.kindAtTag at found
  split at found <;> first | rfl | (cases found)

/-- Live content has the content prefix. -/
theorem contentPrefix_of_contentOf (bytes : List UInt8) (store : ContentStore)
    (found : contentOf bytes = some store) : contentPrefix bytes = true := by
  unfold contentOf at found
  cases decoded : ResourceBirthCodec.LifecycleImage.rawDecode CanonicalCellRegistry.registry bytes with
  | none => simp [decoded] at found
  | some image =>
      rw [decoded] at found
      cases image with
      | fresh => simp at found
      | retired => simp at found
      | live cell =>
          unfold ResourceBirthCodec.LifecycleImage.rawDecode at decoded
          split at decoded
          · cases decoded
          · cases decoded
          · rename_i payload
            simp only [Option.map_eq_some_iff] at decoded
            obtain ⟨packed, packedDecoded, same⟩ := decoded
            cases same
            unfold CellRegistry.PackedCell.decode at packedDecoded
            split at packedDecoded
            · rename_i tag rest
              split at packedDecoded
              · cases packedDecoded
              · rename_i kind kindFound
                simp only [Option.map_eq_some_iff] at packedDecoded
                obtain ⟨logical, _, rfl⟩ := packedDecoded
                cases kind <;> simp at found
                have := kindAtTag_content tag kindFound
                subst this
                rfl
            · cases packedDecoded
          · cases decoded

/-- The live links of a cell image; none for any cell that is not live content.
The kind-tag prefix is tested before the payload is decoded. -/
def liveLinks (bytes : List UInt8) : List LinkKey :=
  if contentPrefix bytes then liveLinksFull bytes else []

/-- **The prefilter changes nothing**: the live links are the full decode's. -/
theorem liveLinks_eq (bytes : List UInt8) : liveLinks bytes = liveLinksFull bytes := by
  unfold liveLinks
  split
  · rfl
  · rename_i skipped
    unfold liveLinksFull
    cases found : contentOf bytes with
    | none => rfl
    | some store => exact absurd (contentPrefix_of_contentOf bytes store found) skipped

/-- **A content store's live links have distinct identifiers**: its entries
are strictly ordered by address, and a link's address is its identifier. -/
theorem linksOfStore_ids_nodup (store : ContentStore) :
    ((linksOfStore store).map Prod.fst).Nodup := by
  unfold linksOfStore
  rw [List.Nodup, List.pairwise_map, List.pairwise_filterMap]
  refine (StoreCodec.entries_pairwise HyperdocumentCell.contentWire store).imp ?_
  rintro ⟨⟨spaceA, keyA⟩, valueA⟩ ⟨⟨spaceB, keyB⟩, valueB⟩ ordered x hx y hy
  cases spaceA <;> cases spaceB <;> first | (simp at hx; done) | (simp at hy; done) | skip
  dsimp only at hx hy
  split at hx <;> split at hy <;> first
    | (simp at hx; done)
    | (simp at hy; done)
    | skip
  simp only [Option.some.injEq] at hx hy
  subst hx
  subst hy
  intro same
  have same' : keyA = keyB := same
  subst same'
  exact lt_irrefl _ ordered

theorem liveLinks_ids_nodup (bytes : List UInt8) : ((liveLinks bytes).map Prod.fst).Nodup := by
  rw [liveLinks_eq]
  unfold liveLinksFull
  cases contentOf bytes with
  | none => exact List.nodup_nil
  | some store => exact linksOfStore_ids_nodup store

/-! ## Association lists with unique keys -/

section Map

variable {κ α : Type} [DecidableEq κ]

/-- The value at a key (first match), `[]` when absent. -/
def lookup : List (κ × List α) → κ → List α
  | [], _ => []
  | entry :: rest, key => if entry.1 = key then entry.2 else lookup rest key

/-- Set a key: the new pair first, every other pair for that key dropped. -/
def store (map : List (κ × List α)) (key : κ) (value : List α) : List (κ × List α) :=
  (key, value) :: map.filter fun entry => entry.1 ≠ key

theorem lookup_filter_ne (map : List (κ × List α)) {key key' : κ} (other : key ≠ key') :
    lookup (map.filter fun entry => entry.1 ≠ key) key' = lookup map key' := by
  induction map with
  | nil => rfl
  | cons entry rest ih =>
      rw [List.filter_cons]
      by_cases same : entry.1 = key
      · have miss : entry.1 ≠ key' := same ▸ other
        rw [if_neg (by simp [same]), ih]
        simp only [lookup, miss, if_false]
      · rw [if_pos (by simp [same])]
        simp only [lookup]
        split
        · rfl
        · exact ih

theorem lookup_store (map : List (κ × List α)) (key key' : κ) (value : List α) :
    lookup (store map key value) key' = if key = key' then value else lookup map key' := by
  by_cases same : key = key'
  · simp [store, lookup, same]
  · simp only [store, lookup, same, if_false]
    exact lookup_filter_ne map same

theorem lookup_nil_or_mem (map : List (κ × List α)) (key : κ) :
    lookup map key = [] ∨ (key, lookup map key) ∈ map := by
  induction map with
  | nil => exact Or.inl rfl
  | cons entry rest ih =>
      by_cases hit : entry.1 = key
      · right
        simp only [lookup, hit, if_true, List.mem_cons]
        exact Or.inl (by rw [← hit])
      · simp only [lookup, hit, if_false, List.mem_cons]
        rcases ih with empty | found
        · exact Or.inl empty
        · exact Or.inr (Or.inr found)

theorem store_nodup {map : List (κ × List α)} (unique : (map.map Prod.fst).Nodup) (key : κ)
    (value : List α) : ((store map key value).map Prod.fst).Nodup := by
  simp only [store, List.map_cons, List.nodup_cons]
  refine ⟨?_, ?_⟩
  · simp
  · exact (List.filter_sublist).map Prod.fst |>.nodup unique

theorem lookup_filter_self (map : List (κ × List α)) (key : κ) :
    lookup (map.filter fun entry => entry.1 ≠ key) key = [] := by
  induction map with
  | nil => rfl
  | cons entry rest ih =>
      rw [List.filter_cons]
      by_cases same : entry.1 = key
      · rw [if_neg (by simp [same]), ih]
      · rw [if_pos (by simp [same])]
        simp only [lookup, same, if_false]
        exact ih

/-- Set a key, dropping the key altogether when its value is empty (a lookup
of a missing key is `[]`, so nothing observable differs; the map does not
accumulate emptied keys). -/
def put (map : List (κ × List α)) (key : κ) (value : List α) : List (κ × List α) :=
  if value.isEmpty then map.filter (fun entry => entry.1 ≠ key) else store map key value

theorem lookup_put (map : List (κ × List α)) (key key' : κ) (value : List α) :
    lookup (put map key value) key' = if key = key' then value else lookup map key' := by
  unfold put
  split
  · rename_i empty
    have : value = [] := List.isEmpty_iff.mp empty
    subst this
    by_cases same : key = key'
    · subst same; simpa using lookup_filter_self map key
    · rw [if_neg same, lookup_filter_ne map same]
  · exact lookup_store map key key' value

theorem lookup_of_mem {map : List (κ × List α)} (unique : (map.map Prod.fst).Nodup)
    {pair : κ × List α} (member : pair ∈ map) : lookup map pair.1 = pair.2 := by
  induction map with
  | nil => cases member
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with rfl | inRest
      · simp [lookup]
      · have other : entry.1 ≠ pair.1 := by
          intro same
          exact unique.1 (same ▸ List.mem_map_of_mem inRest)
        simp only [lookup, other, if_false]
        exact ih unique.2 inRest

end Map

/-! ## Entries and targets -/

/-- One live link: its identifier, record, and the log height from which it
has been live in its cell without a break. -/
structure Entry where
  link : LinkId
  record : LinkRecord
  height : Nat
  deriving DecidableEq

def Entry.key (entry : Entry) : LinkKey := (entry.link, entry.record)

/-- What a link points at, as an index key. A range of a document is a link
to that document; an external target is keyed by its exact bytes. -/
inductive TargetKey where
  | document (id : DocumentId)
  | element (id : ElementId)
  | transclusion (id : TransclusionId)
  | external (scheme authority path : List UInt8)
  deriving DecidableEq

def TargetKey.of : LinkTarget → TargetKey
  | .document id => .document id
  | .element id => .element id
  | .range doc _ => .document doc
  | .transclusion id _ => .transclusion id
  | .external scheme authority path => .external scheme authority path

/-- The target's kind, as the view reports it: document 0, element 1, range 2,
transclusion 3, external 4. -/
def targetKind : LinkTarget → Nat
  | .document _ => 0
  | .element _ => 1
  | .range _ _ => 2
  | .transclusion _ _ => 3
  | .external _ _ _ => 4

/-- The identifier the view reports for a target (the document of a range;
`0` for an external target, whose bytes the source cell itself shows). -/
def targetId : LinkTarget → Nat
  | .document id => id.digest.value
  | .element id => id.digest.value
  | .range doc _ => doc.digest.value
  | .transclusion id _ => id.digest.value
  | .external _ _ _ => 0

/-- The keys a document answers to: itself (and so every range of it) and
each element its content store holds. -/
def documentKeys (document : DocumentId) (store : ContentStore) : List TargetKey :=
  .document document :: (StoreCodec.entries HyperdocumentCell.contentWire store).filterMap fun entry =>
    match entry with
    | ⟨⟨.elements, identifier⟩, _⟩ =>
        let identifier : ElementId := identifier
        some (.element identifier)
    | _ => none

/-- The new live links of a cell, each keeping the height of an identical
entry it already had (still live without a break), else starting at `height`. -/
def refresh (old : List Entry) (height : Nat) (links : List LinkKey) : List Entry :=
  links.map fun key =>
    ⟨key.1, key.2, ((old.find? fun entry => entry.key = key).map Entry.height).getD height⟩

theorem refresh_keys (old : List Entry) (height : Nat) (links : List LinkKey) :
    (refresh old height links).map Entry.key = links := by
  simp [refresh, Entry.key, Function.comp_def]

theorem mem_refresh {old : List Entry} {height : Nat} {links : List LinkKey} {entry : Entry}
    (member : entry ∈ refresh old height links) :
    entry.key ∈ links ∧
      ((∃ earlier ∈ old, earlier.key = entry.key ∧ earlier.height = entry.height) ∨
        entry.height = height) := by
  obtain ⟨key, inLinks, rfl⟩ := List.mem_map.mp member
  refine ⟨by simpa [Entry.key] using inLinks, ?_⟩
  cases found : old.find? (fun entry => entry.key = key) with
  | none => right; simp
  | some earlier =>
      left
      have holds := List.find?_some found
      refine ⟨earlier, List.mem_of_find?_eq_some found, ?_, by simp⟩
      simpa [Entry.key] using holds

theorem refresh_nil (old : List Entry) (height : Nat) : refresh old height [] = [] := rfl

/-! ## The index -/

abbrev Sources := List (CellId × List Entry)
abbrev Reverse := List (TargetKey × List (CellId × Entry))

/-- Every (cell, entry) pair of the forward map. -/
def pairs (sources : Sources) : List (CellId × Entry) :=
  sources.flatMap fun source => source.2.map fun entry => (source.1, entry)

def addPair (reverse : Reverse) (pair : CellId × Entry) : Reverse :=
  store reverse (TargetKey.of pair.2.record.target)
    (pair :: lookup reverse (TargetKey.of pair.2.record.target))

theorem lookup_addPair (reverse : Reverse) (pair : CellId × Entry) (key : TargetKey) :
    lookup (addPair reverse pair) key =
      if TargetKey.of pair.2.record.target = key then pair :: lookup reverse key
      else lookup reverse key := by
  unfold addPair
  rw [lookup_store]
  split <;> rename_i hit
  · subst hit; rfl
  · rfl

/-- The backlink map of a forward map. -/
def invert (sources : Sources) : Reverse :=
  (pairs sources).foldr (fun pair reverse => addPair reverse pair) []

theorem mem_lookup_foldr (list : List (CellId × Entry)) (key : TargetKey) (pair : CellId × Entry) :
    pair ∈ lookup (list.foldr (fun pair reverse => addPair reverse pair) []) key ↔
      pair ∈ list ∧ TargetKey.of pair.2.record.target = key := by
  induction list with
  | nil => simp [lookup]
  | cons head rest ih =>
      rw [List.foldr_cons, lookup_addPair]
      by_cases hit : TargetKey.of head.2.record.target = key
      · rw [if_pos hit, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨inRest, same⟩)
          · exact ⟨List.mem_cons_self .., hit⟩
          · exact ⟨List.mem_cons_of_mem _ inRest, same⟩
        · rintro ⟨member, same⟩
          rcases List.mem_cons.mp member with rfl | inRest
          · exact Or.inl rfl
          · exact Or.inr ⟨inRest, same⟩
      · rw [if_neg hit, ih]
        constructor
        · rintro ⟨inRest, same⟩
          exact ⟨List.mem_cons_of_mem _ inRest, same⟩
        · rintro ⟨member, same⟩
          rcases List.mem_cons.mp member with rfl | inRest
          · exact absurd same hit
          · exact ⟨inRest, same⟩

/-- **The backlink map is exactly the forward map, inverted.** -/
theorem mem_lookup_invert (sources : Sources) (key : TargetKey) (pair : CellId × Entry) :
    pair ∈ lookup (invert sources) key ↔
      pair ∈ pairs sources ∧ TargetKey.of pair.2.record.target = key :=
  mem_lookup_foldr _ key pair

theorem mem_pairs {sources : Sources} {pair : CellId × Entry} :
    pair ∈ pairs sources ↔ ∃ source ∈ sources, source.1 = pair.1 ∧ pair.2 ∈ source.2 := by
  simp only [pairs, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨source, inSources, entry, inEntries, rfl⟩
    exact ⟨source, inSources, rfl, inEntries⟩
  · rintro ⟨source, inSources, same, inEntries⟩
    exact ⟨source, inSources, pair.2, inEntries, by rw [same]⟩

/-- The link index: the forward map and its inversion. -/
structure Index where
  sources : Sources
  reverse : Reverse

def Index.empty : Index := ⟨[], []⟩

/-- Drop one pair from the backlink map. -/
def dropPair (reverse : Reverse) (pair : CellId × Entry) : Reverse :=
  put reverse (TargetKey.of pair.2.record.target)
    ((lookup reverse (TargetKey.of pair.2.record.target)).filter fun other => other ≠ pair)

/-- Add a pair unless the target's row already holds it, so a target's row
never repeats a pair (`nodup_lookup_addUnique`). -/
def addUnique (reverse : Reverse) (pair : CellId × Entry) : Reverse :=
  if pair ∈ lookup reverse (TargetKey.of pair.2.record.target) then reverse else addPair reverse pair

/-- Replace a cell's entries: the forward map is set, and the backlink map
drops the cell's old pairs and adds its new ones. This is the whole cost of a
write: it never re-inverts the forward map. A cell with neither old nor new
links leaves both maps as they were. -/
def setCell (acc : Sources × Reverse) (cell : CellId) (height : Nat) (links : List LinkKey) :
    Sources × Reverse :=
  let old := lookup acc.1 cell
  if links.isEmpty ∧ old.isEmpty then acc
  else
    let new := refresh old height links
    (store acc.1 cell new,
      (new.map fun entry => (cell, entry)).foldl addUnique
        ((old.map fun entry => (cell, entry)).foldl dropPair acc.2))

/-- One write at log height `height`: the written cell's entries become its
post-state's live links. -/
def admitWrite (height : Nat) (acc : Sources × Reverse) (write : DataWrite) : Sources × Reverse :=
  setCell acc write.cellId height (liveLinks write.canonicalPostBytes)

def admitWrites (height : Nat) (writes : List DataWrite) (acc : Sources × Reverse) :
    Sources × Reverse :=
  writes.foldl (admitWrite height) acc

/-- Admit one record at log height `height`. -/
def Index.admit (index : Index) (height : Nat) (record : IntentRecord) : Index :=
  let next := admitWrites height record.writes (index.sources, index.reverse)
  ⟨next.1, next.2⟩

/-- Fold the records after height `start`; the first is admitted at `start + 1`. -/
def Index.extend : Index → Nat → List IntentRecord → Index
  | index, _, [] => index
  | index, start, record :: records => (index.admit (start + 1) record).extend (start + 1) records

/-- The link index of a log. -/
def ofRecords (records : List IntentRecord) : Index := Index.empty.extend 0 records

theorem Index.extend_append (index : Index) (start : Nat) (left right : List IntentRecord) :
    index.extend start (left ++ right) = (index.extend start left).extend (start + left.length) right := by
  induction left generalizing index start with
  | nil => rfl
  | cons record rest ih =>
      show (index.admit (start + 1) record).extend (start + 1) (rest ++ right) = _
      rw [ih]
      show _ = ((index.admit (start + 1) record).extend (start + 1) rest).extend _ right
      congr 1
      simp only [List.length_cons]
      omega

/-- The index of a longer log is the shorter log's index advanced by the
suffix: what a resumed open and a checkpoint suffix replay both compute. -/
theorem ofRecords_append (left right : List IntentRecord) :
    ofRecords (left ++ right) = (ofRecords left).extend left.length right := by
  unfold ofRecords
  rw [Index.extend_append, Nat.zero_add]

theorem ofRecords_snoc (log : List IntentRecord) (record : IntentRecord) :
    ofRecords (log ++ [record]) = (ofRecords log).admit (log.length + 1) record := by
  rw [ofRecords_append]
  rfl

/-! ## One record -/

theorem lookup_setCell (acc : Sources × Reverse) (cell : CellId) (height : Nat) (links : List LinkKey)
    (other : CellId) :
    lookup (setCell acc cell height links).1 other =
      if cell = other then refresh (lookup acc.1 cell) height links else lookup acc.1 other := by
  unfold setCell
  dsimp only
  split
  · rename_i quiet
    split
    · rename_i same
      subst same
      have l : links = [] := List.isEmpty_iff.mp quiet.1
      have o : lookup acc.1 cell = [] := List.isEmpty_iff.mp quiet.2
      rw [l, o, refresh_nil]
    · rfl
  · rw [lookup_store]

theorem lookup_admitWrite (height : Nat) (acc : Sources × Reverse) (write : DataWrite) (cell : CellId) :
    lookup (admitWrite height acc write).1 cell =
      if write.cellId = cell then refresh (lookup acc.1 cell) height (liveLinks write.canonicalPostBytes)
      else lookup acc.1 cell := by
  unfold admitWrite
  rw [lookup_setCell]
  split <;> rename_i same
  · subst same; rfl
  · rfl

theorem setCell_nodup (acc : Sources × Reverse) (cell : CellId) (height : Nat) (links : List LinkKey)
    (unique : (acc.1.map Prod.fst).Nodup) : ((setCell acc cell height links).1.map Prod.fst).Nodup := by
  unfold setCell
  dsimp only
  split
  · exact unique
  · exact store_nodup unique _ _

theorem admitWrite_nodup (height : Nat) (acc : Sources × Reverse) (write : DataWrite)
    (unique : (acc.1.map Prod.fst).Nodup) : ((admitWrite height acc write).1.map Prod.fst).Nodup :=
  setCell_nodup _ _ _ _ unique

theorem admitWrites_nodup (height : Nat) :
    ∀ (writes : List DataWrite) (acc : Sources × Reverse), (acc.1.map Prod.fst).Nodup →
      ((admitWrites height writes acc).1.map Prod.fst).Nodup
  | [], _, unique => unique
  | write :: rest, acc, unique =>
      admitWrites_nodup height rest (admitWrite height acc write) (admitWrite_nodup height acc write unique)

/-! ## The backlink map stays the inversion of the forward map

`RevExact` is `mem_lookup_invert`'s statement, for the maintained map. -/

/-- The backlink map holds exactly the pairs of the forward map, under their targets. -/
def RevExact (sources : Sources) (reverse : Reverse) : Prop :=
  ∀ (key : TargetKey) (pair : CellId × Entry),
    pair ∈ lookup reverse key ↔ pair ∈ pairs sources ∧ TargetKey.of pair.2.record.target = key

theorem mem_pairs_iff_lookup {sources : Sources} (unique : (sources.map Prod.fst).Nodup)
    (pair : CellId × Entry) : pair ∈ pairs sources ↔ pair.2 ∈ lookup sources pair.1 := by
  constructor
  · intro member
    obtain ⟨source, inSources, same, inEntries⟩ := mem_pairs.mp member
    rw [← same, lookup_of_mem unique inSources]
    exact inEntries
  · intro member
    rcases lookup_nil_or_mem sources pair.1 with empty | found
    · rw [empty] at member; cases member
    · exact mem_pairs.mpr ⟨_, found, rfl, member⟩

/-- **The inversion of a forward map is exact** (the specification). -/
theorem revExact_invert (sources : Sources) : RevExact sources (invert sources) :=
  fun key pair => mem_lookup_invert sources key pair

theorem mem_lookup_dropPair (reverse : Reverse) (pair other : CellId × Entry) (key : TargetKey) :
    other ∈ lookup (dropPair reverse pair) key ↔
      other ∈ lookup reverse key ∧ ¬ (other = pair ∧ TargetKey.of pair.2.record.target = key) := by
  unfold dropPair
  rw [lookup_put]
  by_cases hit : TargetKey.of pair.2.record.target = key
  · rw [if_pos hit, List.mem_filter]
    simp only [decide_eq_true_eq, ne_eq, hit, and_true]
  · rw [if_neg hit]
    simp [hit]

theorem mem_lookup_foldl_dropPair (cell : CellId) (old : List Entry) :
    ∀ (reverse : Reverse) (key : TargetKey) (other : CellId × Entry),
      other ∈ lookup ((old.map fun entry => (cell, entry)).foldl dropPair reverse) key ↔
        other ∈ lookup reverse key ∧
          ¬ (other.1 = cell ∧ other.2 ∈ old ∧ TargetKey.of other.2.record.target = key) := by
  induction old with
  | nil => intro reverse key other; simp
  | cons entry rest ih =>
      intro reverse key other
      rw [List.map_cons, List.foldl_cons, ih, mem_lookup_dropPair]
      constructor
      · rintro ⟨⟨found, notHead⟩, notRest⟩
        refine ⟨found, ?_⟩
        rintro ⟨rfl, member, targetKey⟩
        rcases List.mem_cons.mp member with rfl | inRest
        · exact notHead ⟨rfl, targetKey⟩
        · exact notRest ⟨rfl, inRest, targetKey⟩
      · rintro ⟨found, gone⟩
        refine ⟨⟨found, ?_⟩, ?_⟩
        · rintro ⟨same, targetKey⟩
          exact gone ⟨by rw [same], by rw [same]; exact List.mem_cons_self .., by rw [same]; exact targetKey⟩
        · rintro ⟨same, member, targetKey⟩
          exact gone ⟨same, List.mem_cons_of_mem _ member, targetKey⟩

theorem mem_lookup_addUnique (reverse : Reverse) (head other : CellId × Entry) (key : TargetKey) :
    other ∈ lookup (addUnique reverse head) key ↔
      other ∈ lookup reverse key ∨ (other = head ∧ TargetKey.of head.2.record.target = key) := by
  unfold addUnique
  split
  · rename_i present
    constructor
    · exact Or.inl
    · rintro (found | ⟨rfl, hit⟩)
      · exact found
      · rw [hit] at present; exact present
  · rw [lookup_addPair]
    by_cases hit : TargetKey.of head.2.record.target = key
    · rw [if_pos hit, List.mem_cons]
      constructor
      · rintro (rfl | found)
        · exact Or.inr ⟨rfl, hit⟩
        · exact Or.inl found
      · rintro (found | ⟨rfl, _⟩)
        · exact Or.inr found
        · exact Or.inl rfl
    · rw [if_neg hit]
      constructor
      · exact Or.inl
      · rintro (found | ⟨_, same⟩)
        · exact found
        · exact absurd same hit

theorem mem_lookup_foldl_addUnique (list : List (CellId × Entry)) :
    ∀ (reverse : Reverse) (key : TargetKey) (other : CellId × Entry),
      other ∈ lookup (list.foldl addUnique reverse) key ↔
        other ∈ lookup reverse key ∨ (other ∈ list ∧ TargetKey.of other.2.record.target = key) := by
  induction list with
  | nil => intro reverse key other; simp
  | cons head rest ih =>
      intro reverse key other
      rw [List.foldl_cons, ih, mem_lookup_addUnique]
      constructor
      · rintro ((found | ⟨rfl, hit⟩) | ⟨inRest, same⟩)
        · exact Or.inl found
        · exact Or.inr ⟨List.mem_cons_self .., hit⟩
        · exact Or.inr ⟨List.mem_cons_of_mem _ inRest, same⟩
      · rintro (found | ⟨member, same⟩)
        · exact Or.inl (Or.inl found)
        · rcases List.mem_cons.mp member with rfl | inRest
          · exact Or.inl (Or.inr ⟨rfl, same⟩)
          · exact Or.inr ⟨inRest, same⟩

/-! ### No row repeats a pair -/

/-- Every target's row is duplicate-free. -/
def NodupRev (reverse : Reverse) : Prop := ∀ key, (lookup reverse key).Nodup

theorem nodupRev_dropPair {reverse : Reverse} (nodup : NodupRev reverse) (pair : CellId × Entry) :
    NodupRev (dropPair reverse pair) := by
  intro key
  unfold dropPair
  rw [lookup_put]
  split
  · exact (nodup _).filter _
  · exact nodup key

theorem nodupRev_foldl_dropPair (cell : CellId) (old : List Entry) :
    ∀ {reverse : Reverse}, NodupRev reverse →
      NodupRev ((old.map fun entry => (cell, entry)).foldl dropPair reverse) := by
  induction old with
  | nil => intro reverse nodup; exact nodup
  | cons entry rest ih =>
      intro reverse nodup
      rw [List.map_cons, List.foldl_cons]
      exact ih (nodupRev_dropPair nodup _)

theorem nodupRev_addUnique {reverse : Reverse} (nodup : NodupRev reverse) (pair : CellId × Entry) :
    NodupRev (addUnique reverse pair) := by
  intro key
  unfold addUnique
  split
  · exact nodup key
  · rename_i absent
    rw [lookup_addPair]
    split
    · rename_i hit
      rw [hit] at absent
      exact List.nodup_cons.mpr ⟨absent, nodup key⟩
    · exact nodup key

theorem nodupRev_foldl_addUnique (list : List (CellId × Entry)) :
    ∀ {reverse : Reverse}, NodupRev reverse → NodupRev (list.foldl addUnique reverse) := by
  induction list with
  | nil => intro reverse nodup; exact nodup
  | cons head rest ih =>
      intro reverse nodup
      rw [List.foldl_cons]
      exact ih (nodupRev_addUnique nodup _)

theorem setCell_nodupRev (acc : Sources × Reverse) (cell : CellId) (height : Nat) (links : List LinkKey)
    (nodup : NodupRev acc.2) : NodupRev (setCell acc cell height links).2 := by
  unfold setCell
  dsimp only
  split
  · exact nodup
  · exact nodupRev_foldl_addUnique _ (nodupRev_foldl_dropPair _ _ nodup)

/-- **A write keeps the backlink map the inversion of the forward map.** -/
theorem setCell_rev (acc : Sources × Reverse) (cell : CellId) (height : Nat) (links : List LinkKey)
    (unique : (acc.1.map Prod.fst).Nodup) (rev : RevExact acc.1 acc.2) :
    RevExact (setCell acc cell height links).1 (setCell acc cell height links).2 := by
  unfold setCell
  dsimp only
  split
  · exact rev
  · intro key pair
    have unique' := store_nodup unique cell (refresh (lookup acc.1 cell) height links)
    rw [mem_pairs_iff_lookup unique', lookup_store,
      mem_lookup_foldl_addUnique, mem_lookup_foldl_dropPair, rev key pair,
      mem_pairs_iff_lookup unique]
    by_cases same : cell = pair.1
    · subst same
      simp only [if_true, List.mem_map]
      constructor
      · rintro (⟨⟨inOld, targetKey⟩, gone⟩ | ⟨⟨entry, member, hpair⟩, targetKey⟩)
        · exact absurd (by simp [inOld, targetKey]) gone
        · have e : entry = pair.2 := congrArg Prod.snd hpair
          rw [e] at member
          exact ⟨member, targetKey⟩
      · rintro ⟨member, targetKey⟩
        exact Or.inr ⟨⟨pair.2, member, rfl⟩, targetKey⟩
    · simp only [if_neg same, List.mem_map]
      constructor
      · rintro (⟨found, _⟩ | ⟨⟨entry, _, hpair⟩, _⟩)
        · exact found
        · exact absurd (congrArg Prod.fst hpair) same
      · rintro found
        exact Or.inl ⟨found, fun ⟨h, _⟩ => same h.symm⟩

/-- The last write of `cell` in a record. -/
def lastWrite (cell : CellId) (record : IntentRecord) : Option DataWrite :=
  (record.writes.filter fun write => write.cellId = cell).getLast?

/-- Within one record the cell's keys are the live links of its last write. -/
theorem admitWrites_keys (height : Nat) (cell : CellId) :
    ∀ (writes : List DataWrite) (acc : Sources × Reverse),
      (lookup (admitWrites height writes acc).1 cell).map Entry.key =
        match (writes.filter fun write => write.cellId = cell).getLast? with
        | some write => liveLinks write.canonicalPostBytes
        | none => (lookup acc.1 cell).map Entry.key
  | [], _ => rfl
  | write :: rest, acc => by
      have tail := admitWrites_keys height cell rest (admitWrite height acc write)
      unfold admitWrites at tail ⊢
      rw [List.foldl_cons, tail, lookup_admitWrite]
      by_cases same : write.cellId = cell
      · rw [if_pos same, refresh_keys, List.filter_cons, if_pos (by simpa using same)]
        cases last : (rest.filter fun write => write.cellId = cell).getLast? with
        | none =>
            rw [List.getLast?_eq_none_iff.mp last]
            rfl
        | some other =>
            rw [List.getLast?_cons, last]
            rfl
      · rw [if_neg same, List.filter_cons, if_neg (by simpa using same)]

/-- Within one record each entry of the cell is an earlier entry (same key,
same height) or new at this height from one of the record's writes of it. -/
theorem admitWrites_heights (height : Nat) (cell : CellId) :
    ∀ (writes : List DataWrite) (acc : Sources × Reverse) (entry : Entry),
      entry ∈ lookup (admitWrites height writes acc).1 cell →
        (∃ earlier ∈ lookup acc.1 cell, earlier.key = entry.key ∧ earlier.height = entry.height) ∨
          (entry.height = height ∧ ∃ write ∈ writes, write.cellId = cell ∧
            entry.key ∈ liveLinks write.canonicalPostBytes)
  | [], _, entry, member => Or.inl ⟨entry, member, rfl, rfl⟩
  | write :: rest, acc, entry, member => by
      unfold admitWrites at member
      rw [List.foldl_cons] at member
      rcases admitWrites_heights height cell rest (admitWrite height acc write) entry member with
        ⟨earlier, inMiddle, sameKey, sameHeight⟩ | ⟨atHeight, other, inRest, wrote, live⟩
      · rw [lookup_admitWrite] at inMiddle
        split at inMiddle
        · rename_i same
          rcases mem_refresh inMiddle with ⟨live, ⟨older, inOld, olderKey, olderHeight⟩ | atHeight⟩
          · exact Or.inl ⟨older, inOld, olderKey.trans sameKey, olderHeight.trans sameHeight⟩
          · exact Or.inr ⟨sameHeight ▸ atHeight, write, List.mem_cons_self .., same, sameKey ▸ live⟩
        · exact Or.inl ⟨earlier, inMiddle, sameKey, sameHeight⟩
      · exact Or.inr ⟨atHeight, other, List.mem_cons_of_mem _ inRest, wrote, live⟩

/-! ## Exactness against the log -/

/-- The live links of `cell` after its latest write in `log` (none if never written). -/
def latestLinks (cell : CellId) (log : List IntentRecord) : List LinkKey :=
  log.foldl (fun links record => match lastWrite cell record with
    | some write => liveLinks write.canonicalPostBytes
    | none => links) []

theorem latestLinks_snoc (cell : CellId) (log : List IntentRecord) (record : IntentRecord) :
    latestLinks cell (log ++ [record]) = match lastWrite cell record with
      | some write => liveLinks write.canonicalPostBytes
      | none => latestLinks cell log := by
  simp [latestLinks, List.foldl_append]

/-- The record writes `cell` with `key` live in that write's post-state. -/
def WroteLink (cell : CellId) (key : LinkKey) (record : IntentRecord) : Prop :=
  ∃ write ∈ record.writes, write.cellId = cell ∧ key ∈ liveLinks write.canonicalPostBytes

/-- The index invariant: unique source keys, the reverse map is the inversion
of the forward map, and every cell's entries are exactly its latest live links,
each live since a height at which an accepted record wrote it. -/
def Exact (log : List IntentRecord) (index : Index) : Prop :=
  (index.sources.map Prod.fst).Nodup ∧ RevExact index.sources index.reverse ∧
    ∀ cell, (lookup index.sources cell).map Entry.key = latestLinks cell log ∧
      ∀ entry ∈ lookup index.sources cell, Occurs (WroteLink cell entry.key) log entry.height

theorem admitWrites_rev (height : Nat) :
    ∀ (writes : List DataWrite) (acc : Sources × Reverse), (acc.1.map Prod.fst).Nodup →
      RevExact acc.1 acc.2 → RevExact (admitWrites height writes acc).1 (admitWrites height writes acc).2
  | [], _, _, rev => rev
  | write :: rest, acc, unique, rev =>
      admitWrites_rev height rest (admitWrite height acc write)
        (admitWrite_nodup height acc write unique) (setCell_rev acc _ _ _ unique rev)

theorem exact_admit (log : List IntentRecord) (index : Index) (record : IntentRecord)
    (exact : Exact log index) : Exact (log ++ [record]) (index.admit (log.length + 1) record) := by
  obtain ⟨unique, reverse, cells⟩ := exact
  refine ⟨admitWrites_nodup _ _ _ unique, admitWrites_rev _ _ _ unique reverse, fun cell => ⟨?_, ?_⟩⟩
  · show (lookup (admitWrites _ _ _).1 cell).map Entry.key = _
    rw [admitWrites_keys, latestLinks_snoc]
    unfold lastWrite
    split
    · rfl
    · exact (cells cell).1
  · intro entry member
    rcases admitWrites_heights _ cell record.writes _ entry member with
      ⟨earlier, inOld, sameKey, sameHeight⟩ | ⟨atHeight, write, written, wrote, live⟩
    · have occurs := (cells cell).2 earlier inOld
      rw [sameKey, sameHeight] at occurs
      exact occurs_append_left occurs [record]
    · exact (occurs_snoc log record _).mpr (Or.inr ⟨atHeight, write, written, wrote, live⟩)

/-- **The link index is exact for every log**: the forward map holds each
cell's latest live links, each live since a height at which an accepted
record wrote it, and the backlink map is its inversion. -/
theorem ofRecords_exact (log : List IntentRecord) : Exact log (ofRecords log) := by
  induction log using List.reverseRecOn with
  | nil =>
      refine ⟨List.nodup_nil, fun key pair => by simp [ofRecords, Index.extend, Index.empty, lookup, pairs], fun cell => ⟨rfl, fun entry member => ?_⟩⟩
      cases member
  | append_singleton log record ih =>
      rw [ofRecords_snoc]
      exact exact_admit log _ record ih

theorem admitWrites_nodupRev (height : Nat) :
    ∀ (writes : List DataWrite) (acc : Sources × Reverse), NodupRev acc.2 →
      NodupRev (admitWrites height writes acc).2
  | [], _, nodup => nodup
  | write :: rest, acc, nodup =>
      admitWrites_nodupRev height rest (admitWrite height acc write) (setCell_nodupRev acc _ _ _ nodup)

theorem Index.extend_nodupRev :
    ∀ (records : List IntentRecord) (index : Index) (start : Nat), NodupRev index.reverse →
      NodupRev (index.extend start records).reverse
  | [], _, _, nodup => nodup
  | record :: rest, index, start, nodup =>
      Index.extend_nodupRev rest (index.admit (start + 1) record) (start + 1)
        (admitWrites_nodupRev _ _ _ nodup)

/-- **No target's backlink row repeats a pair**, for every log. -/
theorem ofRecords_nodupRev (log : List IntentRecord) : NodupRev (ofRecords log).reverse :=
  Index.extend_nodupRev log Index.empty 0 (fun _ => List.nodup_nil)

/-! ## Reads -/

/-- The live links a cell holds (the forward view). -/
def Index.links (index : Index) (cell : CellId) : List Entry := lookup index.sources cell

/-- The canonical order of backlink rows: by source cell, then by link
identifier. It is a function of the pair alone, so a served row order never
depends on the order in which writes arrived. -/
def pairLe (a b : CellId × Entry) : Bool :=
  decide (a.1.value < b.1.value ∨ (a.1.value = b.1.value ∧ a.2.link.digest.value ≤ b.2.link.digest.value))

theorem pairLe_trans (a b c : CellId × Entry) (h₁ : pairLe a b = true) (h₂ : pairLe b c = true) :
    pairLe a c = true := by
  simp only [pairLe, decide_eq_true_eq] at *
  omega

theorem pairLe_total (a b : CellId × Entry) : (pairLe a b || pairLe b a) = true := by
  simp only [pairLe, Bool.or_eq_true, decide_eq_true_eq]
  omega

/-- The backlinks to any of `keys` whose SOURCE cell the reader sees, each
target's row in the canonical order (`pairLe`). -/
def Index.backlinks (index : Index) (visible : CellId → Bool) (keys : List TargetKey) :
    List (CellId × Entry) :=
  keys.flatMap fun key => ((lookup index.reverse key).mergeSort pairLe).filter fun pair => visible pair.1

/-- **A reader's backlinks come only from cells it sees.** -/
theorem backlinks_covered (index : Index) (visible : CellId → Bool) (keys : List TargetKey)
    {pair : CellId × Entry} (member : pair ∈ index.backlinks visible keys) : visible pair.1 = true := by
  obtain ⟨_, _, kept⟩ := List.mem_flatMap.mp member
  exact (List.mem_filter.mp kept).2

/-- **Every backlink is a live link of the log**: its source cell is seen, it
points at one of the asked keys, it is live in the source cell's latest
accepted write (a link tombstoned or written away since is gone), and it has
been live since its height, at which an accepted record wrote it. -/
theorem backlinks_sound (log : List IntentRecord) (visible : CellId → Bool) (keys : List TargetKey)
    {pair : CellId × Entry} (member : pair ∈ (ofRecords log).backlinks visible keys) :
    visible pair.1 = true ∧ TargetKey.of pair.2.record.target ∈ keys ∧
      pair.2.key ∈ latestLinks pair.1 log ∧ Occurs (WroteLink pair.1 pair.2.key) log pair.2.height := by
  obtain ⟨unique, reverse, cells⟩ := ofRecords_exact log
  obtain ⟨key, asked, kept⟩ := List.mem_flatMap.mp member
  obtain ⟨found, shown⟩ := List.mem_filter.mp kept
  rw [List.mem_mergeSort, reverse] at found
  obtain ⟨paired, targetKey⟩ := found
  obtain ⟨source, inSources, sameCell, inEntries⟩ := mem_pairs.mp paired
  have exactCell : lookup (ofRecords log).sources pair.1 = source.2 := by
    rw [← sameCell]; exact lookup_of_mem unique inSources
  rw [← exactCell] at inEntries
  refine ⟨shown, targetKey ▸ asked, ?_, (cells pair.1).2 pair.2 inEntries⟩
  rw [← (cells pair.1).1]
  exact List.mem_map_of_mem inEntries

/-- **Every live link of a seen cell is a backlink of its target**: the read
misses nothing the reader may see. -/
theorem backlinks_complete (log : List IntentRecord) (visible : CellId → Bool) (keys : List TargetKey)
    {cell : CellId} {key : LinkKey} (live : key ∈ latestLinks cell log) (shown : visible cell = true)
    (asked : TargetKey.of key.2.target ∈ keys) :
    ∃ entry, entry.key = key ∧ (cell, entry) ∈ (ofRecords log).backlinks visible keys := by
  obtain ⟨_, reverse, cells⟩ := ofRecords_exact log
  rw [← (cells cell).1] at live
  obtain ⟨entry, inEntries, sameKey⟩ := List.mem_map.mp live
  have present : (cell, lookup (ofRecords log).sources cell) ∈ (ofRecords log).sources := by
    rcases lookup_nil_or_mem (ofRecords log).sources cell with empty | found
    · rw [empty] at inEntries; cases inEntries
    · exact found
  have target : entry.record = key.2 := by rw [← sameKey]; rfl
  refine ⟨entry, sameKey, List.mem_flatMap.mpr ⟨TargetKey.of key.2.target, asked, ?_⟩⟩
  refine List.mem_filter.mpr ⟨List.mem_mergeSort.mpr ?_, shown⟩
  rw [reverse]
  exact ⟨mem_pairs.mpr ⟨_, present, rfl, inEntries⟩, by rw [target]⟩

/-- **The forward view is exact**: a cell's links are its latest live links. -/
theorem links_exact (log : List IntentRecord) (cell : CellId) :
    ((ofRecords log).links cell).map Entry.key = latestLinks cell log :=
  ((ofRecords_exact log).2.2 cell).1

/-! ## The served order is a function of state

`backlinks` sorts each target's row by `pairLe`. Two histories that reach the
same forward map serve the same rows in the same order
(`backlinks_state`): the rows are duplicate-free (`ofRecords_nodupRev`), the
pairs of a cell are distinguished by link identifier
(`latestLinks_ids_nodup`), and `pairLe` is antisymmetric on such pairs. -/

theorem latestLinks_ids_nodup (cell : CellId) (log : List IntentRecord) :
    ((latestLinks cell log).map Prod.fst).Nodup := by
  induction log using List.reverseRecOn with
  | nil => exact List.nodup_nil
  | append_singleton log record ih =>
      rw [latestLinks_snoc]
      cases lastWrite cell record with
      | none => exact ih
      | some write => exact liveLinks_ids_nodup _

/-- A cell's entries are distinguished by link identifier. -/
theorem entry_unique (log : List IntentRecord) {cell : CellId} {e₁ e₂ : Entry}
    (m₁ : e₁ ∈ lookup (ofRecords log).sources cell) (m₂ : e₂ ∈ lookup (ofRecords log).sources cell)
    (same : e₁.link = e₂.link) : e₁ = e₂ := by
  have keys := links_exact log cell
  have nodup : ((lookup (ofRecords log).sources cell).map Entry.link).Nodup := by
    have ids := latestLinks_ids_nodup cell log
    rw [← keys] at ids
    simpa [Index.links, List.map_map, Function.comp_def, Entry.key] using ids
  exact List.inj_on_of_nodup_map nodup m₁ m₂ same

theorem pairLe_antisymm_keys (p q : CellId × Entry) (h₁ : pairLe p q = true) (h₂ : pairLe q p = true) :
    p.1 = q.1 ∧ p.2.link = q.2.link := by
  simp only [pairLe, decide_eq_true_eq] at h₁ h₂
  obtain ⟨⟨a⟩, ⟨⟨⟨b⟩⟩, r, h⟩⟩ := p
  obtain ⟨⟨a'⟩, ⟨⟨⟨b'⟩⟩, r', h'⟩⟩ := q
  simp only at h₁ h₂
  have ha : a = a' := by omega
  have hb : b = b' := by omega
  subst ha hb
  exact ⟨rfl, rfl⟩

/-- A row's pairs are the forward map's pairs of that target. -/
theorem mem_reverse_iff (log : List IntentRecord) (key : TargetKey) (pair : CellId × Entry) :
    pair ∈ lookup (ofRecords log).reverse key ↔
      pair.2 ∈ lookup (ofRecords log).sources pair.1 ∧ TargetKey.of pair.2.record.target = key := by
  obtain ⟨unique, reverse, _⟩ := ofRecords_exact log
  rw [reverse key pair, mem_pairs_iff_lookup unique]

/-- **Backlinks are a function of the forward map**: any two logs whose
indexes hold the same links serve the same rows in the same order, whatever
order their writes arrived in. -/
theorem backlinks_state (log₁ log₂ : List IntentRecord)
    (same : ∀ cell, (ofRecords log₁).links cell = (ofRecords log₂).links cell)
    (visible : CellId → Bool) (keys : List TargetKey) :
    (ofRecords log₁).backlinks visible keys = (ofRecords log₂).backlinks visible keys := by
  unfold Index.backlinks
  congr 1
  funext key
  have members : ∀ pair, pair ∈ lookup (ofRecords log₁).reverse key ↔
      pair ∈ lookup (ofRecords log₂).reverse key := by
    intro pair
    rw [mem_reverse_iff, mem_reverse_iff]
    have := same pair.1
    unfold Index.links at this
    rw [this]
  have perm : (lookup (ofRecords log₁).reverse key).Perm (lookup (ofRecords log₂).reverse key) :=
    (List.perm_ext_iff_of_nodup (ofRecords_nodupRev log₁ key) (ofRecords_nodupRev log₂ key)).mpr members
  have sortedEq : ((lookup (ofRecords log₁).reverse key).mergeSort pairLe) =
      ((lookup (ofRecords log₂).reverse key).mergeSort pairLe) := by
    refine List.Perm.eq_of_pairwise (le := fun a b => pairLe a b = true) ?_ (List.pairwise_mergeSort pairLe_trans pairLe_total _)
      (List.pairwise_mergeSort pairLe_trans pairLe_total _)
      ((List.mergeSort_perm _ _).trans (perm.trans (List.mergeSort_perm _ _).symm))
    intro a b ha hb hab hba
    rw [List.mem_mergeSort] at ha hb
    obtain ⟨sameCell, sameLink⟩ := pairLe_antisymm_keys a b hab hba
    have ma := ((mem_reverse_iff log₁ key a).mp ha).1
    have mb := ((mem_reverse_iff log₂ key b).mp hb).1
    have mb' : b.2 ∈ lookup (ofRecords log₁).sources a.1 := by
      have := same a.1
      unfold Index.links at this
      rw [this, sameCell]
      exact mb
    have e : a.2 = b.2 := entry_unique log₁ ma mb' sameLink
    exact Prod.ext sameCell e
  rw [sortedEq]

/-! ## A transclusion is a backlink of the document it reads

A transclusion's forward link targets the TRANSCLUSION record (`TargetKey.of`
keys it under its own id), not the source document, so the source's backlinks
would miss it. `transclusionKeys index D` collects the keys of every live
transclusion link whose reference reads D; a backlinks read of D asks them too,
so a reader who may ask about D, and who sees the transcluding cell, gets the
transclusion as a backlink of D (`transclusion_backlink_complete`), and only
transclusions that read D are added (`transclusionKeys_sound`). -/

/-- The document a link's target reads: a transclusion's source (the stored
reference's `objectRoot`, the source cell's identifier); none otherwise. -/
def transcludedDocument : LinkTarget → Option DocumentId
  | .transclusion _ reference => some ⟨reference.source.objectRoot⟩
  | _ => none

/-- The keys of the live transclusion links that read `document`. -/
def Index.transclusionKeys (index : Index) (document : DocumentId) : List TargetKey :=
  (pairs index.sources).filterMap fun pair =>
    if transcludedDocument pair.2.record.target = some document then
      some (TargetKey.of pair.2.record.target)
    else none

/-- **Only transclusions of D are added**: each added key is the key of a live
link of the log (in its cell's latest accepted write) whose transclusion reads D. -/
theorem transclusionKeys_sound (log : List IntentRecord) (document : DocumentId) {key : TargetKey}
    (member : key ∈ (ofRecords log).transclusionKeys document) :
    ∃ cell link, link ∈ latestLinks cell log ∧ transcludedDocument link.2.target = some document ∧
      TargetKey.of link.2.target = key := by
  obtain ⟨unique, _, cells⟩ := ofRecords_exact log
  obtain ⟨pair, paired, made⟩ := List.mem_filterMap.mp member
  split at made
  · rename_i reads
    cases made
    obtain ⟨source, inSources, sameCell, inEntries⟩ := mem_pairs.mp paired
    have exactCell : lookup (ofRecords log).sources pair.1 = source.2 := by
      rw [← sameCell]; exact lookup_of_mem unique inSources
    rw [← exactCell] at inEntries
    refine ⟨pair.1, pair.2.key, ?_, reads, rfl⟩
    rw [← (cells pair.1).1]
    exact List.mem_map_of_mem inEntries
  · cases made

/-- **A transclusion of D is a backlink of D**: every live link of a seen cell
whose transclusion reads D is a row of D's backlinks once D's transclusion keys
are asked, whatever else is asked. -/
theorem transclusion_backlink_complete (log : List IntentRecord) (visible : CellId → Bool)
    (keys : List TargetKey) {document : DocumentId} {cell : CellId} {key : LinkKey}
    (live : key ∈ latestLinks cell log) (shown : visible cell = true)
    (reads : transcludedDocument key.2.target = some document) :
    ∃ entry, entry.key = key ∧
      (cell, entry) ∈ (ofRecords log).backlinks visible ((ofRecords log).transclusionKeys document ++ keys) := by
  apply backlinks_complete log visible _ live shown
  obtain ⟨_, _, cells⟩ := ofRecords_exact log
  rw [← (cells cell).1] at live
  obtain ⟨entry, inEntries, sameKey⟩ := List.mem_map.mp live
  have present : (cell, lookup (ofRecords log).sources cell) ∈ (ofRecords log).sources := by
    rcases lookup_nil_or_mem (ofRecords log).sources cell with empty | found
    · rw [empty] at inEntries; cases inEntries
    · exact found
  have target : entry.record = key.2 := by rw [← sameKey]; rfl
  refine List.mem_append_left _ (List.mem_filterMap.mpr ⟨(cell, entry), ?_, ?_⟩)
  · exact mem_pairs.mpr ⟨_, present, rfl, inEntries⟩
  · simp [target, reads]

namespace Example

/-- Refuting pole: a link to a document reads no document as a transclusion,
so it never adds a transclusion key. -/
theorem document_link_reads_nothing (document : DocumentId) :
    transcludedDocument (.document document) = none := rfl

end Example

/-! ## Poles -/

namespace Example

/-- The empty log has no links and no backlinks. -/
theorem empty_has_none (cell : CellId) : (ofRecords []).links cell = [] := rfl

theorem empty_backlinks_none (visible : CellId → Bool) (keys : List TargetKey) :
    (ofRecords []).backlinks visible keys = [] := by
  simp [ofRecords, Index.extend, Index.empty, Index.backlinks, lookup]

/-- Bytes that are not a cell image hold no links. -/
theorem garbage_has_no_links : liveLinks [0] = [] := by
  simp [liveLinks, contentPrefix]

end Example

/-- info: 'Minidregg.Kernel.LinkIndex.ofRecords_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofRecords_exact
/-- info: 'Minidregg.Kernel.LinkIndex.backlinks_covered' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms backlinks_covered
/-- info: 'Minidregg.Kernel.LinkIndex.backlinks_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms backlinks_sound
/-- info: 'Minidregg.Kernel.LinkIndex.backlinks_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms backlinks_complete
/-- info: 'Minidregg.Kernel.LinkIndex.links_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms links_exact
/-- info: 'Minidregg.Kernel.LinkIndex.mem_lookup_invert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_lookup_invert

/-- info: 'Minidregg.Kernel.LinkIndex.transclusionKeys_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transclusionKeys_sound
/-- info: 'Minidregg.Kernel.LinkIndex.transclusion_backlink_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transclusion_backlink_complete
/-- info: 'Minidregg.Kernel.LinkIndex.Example.document_link_reads_nothing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.document_link_reads_nothing

/-- info: 'Minidregg.Kernel.LinkIndex.setCell_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms setCell_rev
/-- info: 'Minidregg.Kernel.LinkIndex.liveLinks_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms liveLinks_eq
/-- info: 'Minidregg.Kernel.LinkIndex.revExact_invert' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revExact_invert
/-- info: 'Minidregg.Kernel.LinkIndex.mem_lookup_foldl_dropPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_lookup_foldl_dropPair
/-- info: 'Minidregg.Kernel.LinkIndex.mem_lookup_foldl_addUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_lookup_foldl_addUnique
/-- info: 'Minidregg.Kernel.LinkIndex.lookup_put' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookup_put

/-- info: 'Minidregg.Kernel.LinkIndex.backlinks_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms backlinks_state
/-- info: 'Minidregg.Kernel.LinkIndex.ofRecords_nodupRev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofRecords_nodupRev
/-- info: 'Minidregg.Kernel.LinkIndex.linksOfStore_ids_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms linksOfStore_ids_nodup

end Minidregg.Kernel.LinkIndex
