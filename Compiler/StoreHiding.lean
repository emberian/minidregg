/-
# Compiler.StoreHiding -- what a narrowed reader of a salted root holds

`Compiler.StoreCodec` roots a store over salted per-entry leaves.  This module
states what a reader shown only some entries receives, and what it can and
cannot learn from it.

A view under a visibility predicate is the cell root and one ITEM per entry, in
canonical order: an entry the reader may see is OPENED (its salt and its
canonical entry bytes, together); any other entry is SEALED (its 32-byte leaf
only).  The reader recomputes every opened leaf and then the root
(`view_root_recomputes`), so the view stays authenticated.

* `narrowed_view_independent_of_uncovered_given_salts` — the view is a function
  of the opened entries with their salts and the sealed entries' commitments;
  nothing else of an uncovered entry reaches the reader.
* `salt_disclosed_iff_value_disclosed` — an entry's salt is in the view exactly
  when its bytes are.
* `sealed_item_is_keyed_leaf` / `commitment_hides` — a sealed item is the leaf
  under the cell's key, which the reader does not hold; that it hides the entry
  is the named premise `SaltedLeafHiding deployedLeafScheme` on KMAC256 +
  cSHAKE256, assumed and not proved (`hiding_at_equality_is_a_collision`: it
  cannot be read at `=`); its poles sit at toy schemes
  (`constLeafScheme_hiding`, `identityLeafScheme_not_hiding`).
* `change_detection_only_via_root` — what a narrowed reader STILL learns under
  the per-write blinding ratchet (K-HIDE-ROTATE): a write to a sealed entry
  leaves every opened ENTRY unchanged and moves the root (THAT the cell was
  written), and moves EVERY sealed leaf, so WHICH entry changed and whether a
  value returned are no longer visible.  The entry count and the position of an
  inserted or removed entry still are.
* `narrowed_view_independent_of_uncovered_across_writes` — across a write, two
  stores that differ only in what the reader may not see give byte-identical
  opened items and views that are renderings of two transcripts the named
  premise `RatchetedViewHiding` makes indistinguishable; poles
  `toyRatchet_hides` / `toyStatic_reveals`.
* `ratchet_determined_by_birth` / `ratchet_advances_on_write` — the blinding the
  Host holds after any write history is the chain the owner's client derives
  from the birth blinding and the write heights; reads do not move it.

The defect this replaces is a theorem in
`Kernel.NarrowedViewHidingWitness.narrowed_view_not_independent`.
-/
import Compiler.StoreCodec

namespace Minidregg.Compiler.StoreHiding

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.StoreCodec
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- One item of a view: an opened entry (salt and entry bytes) or a sealed
leaf. -/
abbrev Item := Sum Opening (List UInt8)

def Item.leaf : Item → List UInt8
  | .inl opening => opening.leaf
  | .inr leaf => leaf

/-- Items on the wire: tag `0` then the salt and the entry bytes, or tag `1`
then the leaf. -/
def itemStream : StreamCodec Item where
  encode
    | .inl opening => 0 :: bytesStream.encode opening.salt ++ bytesStream.encode opening.entry
    | .inr leaf => 1 :: bytesStream.encode leaf
  decodePrefix
    | 0 :: bytes => do
        let (salt, afterSalt) ← bytesStream.decodePrefix bytes
        let (entry, suffix) ← bytesStream.decodePrefix afterSalt
        some (.inl ⟨salt, entry⟩, suffix)
    | 1 :: bytes => do
        let (leaf, suffix) ← bytesStream.decodePrefix bytes
        some (.inr leaf, suffix)
    | _ => none
  decodePrefix_encode := by
    intro item suffix
    cases item with
    | inl opening =>
        simp [List.append_assoc, bytesStream.decodePrefix_encode]
    | inr leaf =>
        simp [bytesStream.decodePrefix_encode]

section View

variable {L : Layout.{0, 0, 0}} (W : Wire L) (visible : Address L → Prop)
  [DecidablePred visible]

/-- The item of one entry. -/
def itemOf (store : Store L) (entry : Entry L) : Item :=
  if visible entry.1 then .inl (opening W store entry) else .inr (opening W store entry).leaf

/-- The items of a store, in canonical entry order. -/
def items (store : Store L) : List Item :=
  (entries W store).map (itemOf W visible store)

/-- What a reader under `visible` receives: the root and the items. -/
def view (store : Store L) : Digest × List Item :=
  (saltedRoot W store, items W visible store)

/-- The root a reader recomputes from the items alone. -/
def rootOfItems (itemList : List Item) : Digest :=
  rootOfLeaves W (itemList.map Item.leaf)

/-- The opened part of a view. -/
def opened (store : Store L) : List Opening :=
  (items W visible store).filterMap Sum.getLeft?

theorem itemOf_leaf (store : Store L) (entry : Entry L) :
    (itemOf W visible store entry).leaf = (opening W store entry).leaf := by
  unfold itemOf
  split <;> rfl

theorem items_leaves (store : Store L) :
    (items W visible store).map Item.leaf = leaves W store := by
  simp [items, leaves, List.map_map, Function.comp_def, itemOf_leaf]

/-- **The view stays authenticated.**  The root is recomputed from the items. -/
theorem view_root_recomputes (store : Store L) :
    (view W visible store).1 = rootOfItems W (view W visible store).2 := by
  simp [view, rootOfItems, items_leaves, saltedRoot]

theorem view_eq_render (store : Store L) :
    view W visible store = (rootOfItems W (items W visible store), items W visible store) := by
  have root := view_root_recomputes W visible store
  simp only [view] at root ⊢
  rw [root]

/-- **Independence of uncovered entries, given their commitments.**  Two stores
whose items agree — the same opened entries with the same salts, the same
sealed commitments — give the reader the same view.  An uncovered entry
reaches the view only through its sealed leaf. -/
theorem narrowed_view_independent_of_uncovered_given_salts {left right : Store L}
    (same : items W visible left = items W visible right) :
    view W visible left = view W visible right := by
  rw [view_eq_render, view_eq_render, same]

theorem opened_item_exact (store : Store L) {entry : Entry L} (shown : visible entry.1) :
    itemOf W visible store entry = .inl (opening W store entry) := by
  simp [itemOf, shown]

theorem sealed_item_exact (store : Store L) {entry : Entry L} (hidden : ¬ visible entry.1) :
    itemOf W visible store entry = .inr (opening W store entry).leaf := by
  simp [itemOf, hidden]

/-- **An entry's salt is disclosed exactly when its value is.**  An opened item
carries the salt and the entry bytes together; a sealed item carries a leaf and
neither of them. -/
theorem salt_disclosed_iff_value_disclosed (store : Store L) (entry : Entry L) :
    (∃ disclosed : Opening, itemOf W visible store entry = .inl disclosed) ↔ visible entry.1 := by
  constructor
  · rintro ⟨disclosed, item⟩
    by_contra hidden
    rw [sealed_item_exact W visible store hidden] at item
    cases item
  · intro shown
    exact ⟨_, opened_item_exact W visible store shown⟩

/-! ## Hiding: a named premise -/

/-- A salted-leaf scheme: the salt of an entry under a cell key, and the hash
of the salted preimage (`Opening.preimage`: the length-prefixed salt, then the
entry bytes).  The hiding premise below is stated over a scheme so that its
poles can be exhibited at toy schemes; the deployed one is
`deployedLeafScheme`. -/
structure LeafScheme where
  salt : List UInt8 → List UInt8 → List UInt8
  hash : List UInt8 → List UInt8

/-- The leaf of an entry under a cell key, in a scheme. -/
def LeafScheme.leaf (scheme : LeafScheme) (key entry : List UInt8) : List UInt8 :=
  scheme.hash (Opening.mk (scheme.salt key entry) entry).preimage

/-- The deployed scheme: the KMAC256 salt of `StoreCodec.salt` and the
cSHAKE256 leaf of `Opening.leaf`. -/
def deployedLeafScheme : LeafScheme where
  salt key entry := StoreCodec.salt (some key) entry
  hash := Sp800185Cshake256.cshake256Bytes StoreCodec.leafCustomization

/-- The leaf of an entry under a cell key, in the deployed scheme. -/
def keyedLeaf (key entry : List UInt8) : List UInt8 :=
  deployedLeafScheme.leaf key entry

/-- What a reader receives for a sealed entry of a blinded cell is the leaf
under the cell's key — a key it does not hold. -/
theorem sealed_item_is_keyed_leaf {store : Store L} {key : List UInt8}
    (blinded : blindingKey W store = some key) {entry : Entry L} (hidden : ¬ visible entry.1) :
    itemOf W visible store entry = .inr (keyedLeaf key (entryBytes W entry)) := by
  rw [sealed_item_exact W visible store hidden]
  simp only [opening, blinded, keyedLeaf, LeafScheme.leaf, deployedLeafScheme, Opening.leaf]

end View

/-- **The hiding premise, assumed and not proved at `deployedLeafScheme`.**
As a function of an unknown cell key, the leaf of one entry is
indistinguishable from the leaf of any other.  Under the PRF security of KMAC256 the salt is a fresh uniform
32-byte value per entry, and under the random-oracle reading of cSHAKE256 the
leaf of a uniform salt reveals nothing of the entry; a q-query distinguisher's
advantage is about q/2^256.  This tree has no model of feasible computation, so
the premise is a schema over the scheme and the indistinguishability relation;
at the deployed scheme it is discharged nowhere.  Its poles, at the one
relation this tree decides (equality) and at toy schemes:
`constLeafScheme_hiding` satisfies it, `identityLeafScheme_not_hiding` refutes
it.  At equality a satisfying scheme is necessarily a colliding one
(`hiding_at_equality_is_a_collision`), which is why the deployed reading is
meaningful only at a computational relation.  The multi-entry form (one key salts every entry of a
cell, and a reader holds the salts of its opened entries) is the PRF's
multi-query security over distinct entry bytes, also not formalized. -/
def SaltedLeafHiding (scheme : LeafScheme)
    (Indistinguishable : (List UInt8 → List UInt8) → (List UInt8 → List UInt8) → Prop) : Prop :=
  ∀ entry entry' : List UInt8,
    Indistinguishable (fun key => scheme.leaf key entry) (fun key => scheme.leaf key entry')

/-- **The commitment hides, reduced to the premise.**  The item a reader
receives for a sealed entry of a blinded cell is `keyedLeaf` under the cell
key (`sealed_item_is_keyed_leaf`); under `SaltedLeafHiding` it is
indistinguishable from the item any other entry would give. -/
theorem commitment_hides
    (Indistinguishable : (List UInt8 → List UInt8) → (List UInt8 → List UInt8) → Prop)
    (premise : SaltedLeafHiding deployedLeafScheme Indistinguishable)
    {L : Layout.{0, 0, 0}} (W : Wire L) (entry entry' : Entry L) :
    Indistinguishable (fun key => keyedLeaf key (entryBytes W entry))
      (fun key => keyedLeaf key (entryBytes W entry')) :=
  premise _ _

/-- The premise cannot be read at `=`: equality of the two keyed leaves would
be a cSHAKE256 collision between two distinct leaf preimages, at every key. -/
theorem hiding_at_equality_is_a_collision
    (premise : SaltedLeafHiding deployedLeafScheme (· = ·))
    (key : List UInt8) {entry entry' : List UInt8} (different : entry ≠ entry') :
    LeafCollision ⟨salt (some key) entry, entry⟩ ⟨salt (some key) entry', entry'⟩ :=
  ⟨fun same => different (congrArg Opening.entry same), congrFun (premise entry entry') key⟩

/-- A toy scheme whose leaf ignores the entry: no salt, a constant hash. -/
def constLeafScheme : LeafScheme where
  salt _ _ := []
  hash _ := List.replicate 32 0

/-- **Satisfiable** (toy scheme): a constant leaf hides every entry at the
strongest relation, equality. -/
theorem constLeafScheme_hiding : SaltedLeafHiding constLeafScheme (· = ·) :=
  fun _ _ => rfl

/-- A toy scheme whose "hash" is the identity: the leaf is the salted preimage
itself, so it carries the entry bytes. -/
def identityLeafScheme : LeafScheme where
  salt _ _ := []
  hash := id

/-- **Refutable** (toy scheme): under the identity hash the leaves of entries
`[0]` and `[1]` differ at the empty key. -/
theorem identityLeafScheme_not_hiding : ¬ SaltedLeafHiding identityLeafScheme (· = ·) := by
  intro premise
  have same := congrFun (premise [0] [1]) []
  revert same
  decide +kernel

/-! ## The ratchet: what a narrowed reader learns across writes (K-HIDE-ROTATE)

Every admitted write leg of a blinded cell ends with the kernel's ratchet
(`StoreCodec.Blinding.patch`): the blinding becomes the next link of a KMAC256
chain, so every salt and every leaf of the cell is re-keyed at every write.
What a narrowed reader comparing two views of the cell still learns, and what it
no longer learns:

* **still visible:** THAT the cell was written (the root moves at every write,
  covered or not, because the blinding entry itself changes); the entry COUNT;
  and, when an uncovered entry is inserted or removed, where it falls among the
  opened entries (items are in address order).  Padding the count is a separate
  decision and is not done here.  The opened salts move too (they are keyed by
  the new blinding); the opened entry bytes do not.
* **closed:** WHICH uncovered entry changed — every sealed leaf moves at every
  write, written or not (`change_detection_only_via_root`) — and whether an
  entry RETURNED to an earlier value: its leaf under a later link is its old
  leaf only by a KMAC coincidence across two keys or a cSHAKE256 collision
  (`leaf_survives_only_by_coincidence`).

Across a write, two stores that differ only in what the reader may not see give
views that are byte-identical in every opened item and are, as functions of the
cell key the reader does not hold, the renderings of two transcripts that the
named premise `RatchetedViewHiding` makes indistinguishable
(`narrowed_view_independent_of_uncovered_across_writes`).  The sealed leaves
themselves differ between the two stores (they commit to different entries);
"byte-identical sealed leaves" holds only at a scheme that hides at `=`, which
is necessarily a colliding one (`hiding_at_equality_is_a_collision`).  The
premise's poles sit at toy schemes: the toy ratchet satisfies it at the
survival-pattern relation (`toyRatchet_hides`), and the same scheme with a
STATIC key refutes it — the pattern shows which leaf moved
(`toyStatic_reveals`). -/

section Ratchet

variable {L : Layout.{0, 0, 0}} (W : Wire L) (visible : Address L → Prop)
  [DecidablePred visible]

private theorem opened_eq_filterMap (store : Store L) :
    opened W visible store = (sortedSupport W store).filterMap fun address =>
      ((store address).map fun value => (⟨address, value⟩ : Entry L)).bind fun entry =>
        if visible entry.1 then some (opening W store entry) else none := by
  unfold opened items entries
  rw [List.filterMap_map, List.filterMap_filterMap]
  congr 1
  funext address
  cases store address with
  | none => rfl
  | some value =>
      simp only [Option.map_some, Option.bind_some, Function.comp_apply, itemOf]
      split <;> rfl

/-- The sealed leaves of a view, in order. -/
def sealedLeaves (store : Store L) : List (List UInt8) :=
  (items W visible store).filterMap Sum.getRight?

/-- The opened entry bytes of a view, in order (the salts dropped). -/
def openedEntries (store : Store L) : List (List UInt8) :=
  (opened W visible store).map Opening.entry

omit [DecidablePred visible] in
theorem mem_entries {store : Store L} {entry : Entry L} (member : entry ∈ entries W store) :
    store entry.1 = some entry.2 := by
  unfold entries at member
  obtain ⟨address, _, found⟩ := List.mem_filterMap.mp member
  obtain ⟨value, present, rfl⟩ := Option.map_eq_some_iff.mp found
  exact present

omit [DecidablePred visible] in
theorem sortedSupport_congr {left right : Store L}
    (same : ∀ address, left address = none ↔ right address = none) :
    sortedSupport W left = sortedSupport W right := by
  have supports : left.support = right.support := by
    ext address
    have l := mem_sortedSupport W left address
    have r := mem_sortedSupport W right address
    rw [sortedSupport_eq, Finset.mem_sort] at l r
    rw [l, r]
    exact not_congr (same address)
  rw [sortedSupport_eq, sortedSupport_eq, supports]

theorem openedEntries_eq_filterMap (store : Store L) :
    openedEntries W visible store = (sortedSupport W store).filterMap fun address =>
      (store address).bind fun value =>
        if visible address then some (entryBytes W ⟨address, value⟩) else none := by
  unfold openedEntries
  rw [opened_eq_filterMap, List.map_filterMap]
  congr 1
  funext address
  cases store address with
  | none => rfl
  | some value =>
      simp only [Option.map_some, Option.bind_some]
      split <;> rfl

/-- The opened entry bytes are a function of the support and of what the
reader may see. -/
theorem openedEntries_congr {left right : Store L}
    (sameSupport : ∀ address, left address = none ↔ right address = none)
    (agree : ∀ address, visible address → left address = right address) :
    openedEntries W visible left = openedEntries W visible right := by
  rw [openedEntries_eq_filterMap, openedEntries_eq_filterMap, sortedSupport_congr W sameSupport]
  apply List.filterMap_congr
  intro address _
  by_cases shown : visible address
  · rw [agree address shown]
  · cases left address <;> cases right address <;> simp [shown]

/-- Every sealed leaf of a blinded store is the keyed leaf of one of its
entries the reader may not see. -/
theorem mem_sealedLeaves {store : Store L} {key : List UInt8}
    (blinded : blindingKey W store = some key) {leaf : List UInt8}
    (member : leaf ∈ sealedLeaves W visible store) :
    ∃ entry ∈ entries W store, ¬ visible entry.1 ∧ leaf = keyedLeaf key (entryBytes W entry) := by
  unfold sealedLeaves items at member
  obtain ⟨item, itemMember, right⟩ := List.mem_filterMap.mp member
  obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp itemMember
  by_cases shown : visible entry.1
  · rw [opened_item_exact W visible store shown] at right
    simp at right
  · rw [sealed_item_is_keyed_leaf W visible blinded shown] at right
    simp only [Sum.getRight?_inr, Option.some.injEq] at right
    exact ⟨entry, entryMember, shown, right.symm⟩

omit [DecidablePred visible] in
/-- **A leaf survives a change of key only by coincidence.**  The keyed leaf of
an entry under one key equals the keyed leaf of an entry under another only when
it is the same entry AND the two keys' KMAC256 salts of it coincide, or
cSHAKE256 collides on two distinct leaf preimages. -/
theorem leaf_survives_only_by_coincidence {key key' entry entry' : List UInt8}
    (same : keyedLeaf key' entry' = keyedLeaf key entry) :
    (entry' = entry ∧ salt (some key') entry = salt (some key) entry) ∨
      LeafCollision ⟨salt (some key') entry', entry'⟩ ⟨salt (some key) entry, entry⟩ := by
  by_cases openings :
      (⟨salt (some key') entry', entry'⟩ : Opening) = ⟨salt (some key) entry, entry⟩
  · obtain ⟨salts, entries⟩ := Opening.mk.inj openings
    subst entries
    exact .inl ⟨rfl, salts⟩
  · exact .inr ⟨openings, same⟩

/-- **Change detection only via the root, under the ratchet.**  The owner writes
an entry the reader may not see (in place), and the kernel advances the
blinding.  Then: (1) every opened ENTRY of the view is byte-identical (the
opened salts are re-keyed); (2) the root moves unless cSHAKE256 collides — the
reader learns THAT the cell was written; (3) NO sealed leaf survives the write,
written or not, except by a KMAC256 coincidence across the two keys or a
cSHAKE256 collision — the reader does not learn WHICH entry moved.  This
replaces K-NARROW-HIDE's statement of the same name, under which the unwritten
sealed leaves stayed put and exactly the written one moved. -/
theorem change_detection_only_via_root (B : Blinding W) (keyHidden : ¬ visible B.address)
    {store : Store L} {key : List UInt8} (blinded : blindingKey W store = some key)
    {address : Address L} (hidden : ¬ visible address) (notKey : address ≠ B.address)
    {before after : L.Value address.1} (present : store address = some before)
    (changed : before ≠ after) (height : Nat) :
    openedEntries W visible (Patch.run (store.set address (some after)) (B.patch store height)) =
        openedEntries W visible store ∧
      (saltedRoot W (Patch.run (store.set address (some after)) (B.patch store height)) ≠
          saltedRoot W store ∨
        RootCollision W (Patch.run (store.set address (some after)) (B.patch store height)) store ∨
        ∃ first ∈ (entries W (Patch.run (store.set address (some after)) (B.patch store height))).map
            (opening W (Patch.run (store.set address (some after)) (B.patch store height))),
          ∃ second ∈ (entries W store).map (opening W store), LeafCollision first second) ∧
      ∀ leaf ∈ sealedLeaves W visible
          (Patch.run (store.set address (some after)) (B.patch store height)),
        leaf ∈ sealedLeaves W visible store →
          (∃ entry, salt (some (B.step height key)) entry = salt (some key) entry) ∨
            ∃ first second, LeafCollision first second := by
  set written := Patch.run (store.set address (some after)) (B.patch store height) with writtenDef
  have writtenKey : blindingKey W written = some (B.step height key) :=
    B.run_patch_blinding store _ height blinded
  have keyPresent : ∀ s : Store L, blindingKey W s ≠ none → s B.address ≠ none := by
    intro s found absent
    rw [B.blindingKey_eq, absent] at found
    exact found rfl
  have writtenAt : written address = some after := by
    rw [writtenDef, B.run_patch_frame _ _ _ _ notKey, Store.set_eq]
  have frame : ∀ other, other ≠ address → other ≠ B.address → written other = store other := by
    intro other notWritten notBlinding
    rw [writtenDef, B.run_patch_frame _ _ _ _ notBlinding, Store.set_ne _ _ _ _ notWritten]
  have sameSupport : ∀ other, written other = none ↔ store other = none := by
    intro other
    by_cases atWrite : other = address
    · subst atWrite
      rw [writtenAt, present]
      simp
    · by_cases atKey : other = B.address
      · subst atKey
        have l := keyPresent written (by rw [writtenKey]; simp)
        have r := keyPresent store (by rw [blinded]; simp)
        exact ⟨fun h => absurd h l, fun h => absurd h r⟩
      · rw [frame other atWrite atKey]
  refine ⟨?_, ?_, ?_⟩
  · apply openedEntries_congr W visible sameSupport
    intro other shown
    exact frame other (fun same => hidden (same ▸ shown)) (fun same => keyHidden (same ▸ shown))
  · by_cases roots : saltedRoot W written = saltedRoot W store
    · rcases root_binds_salted_entries W roots with equal | collision
      · exfalso
        have atAddress := congrArg (fun s : Store L => s address) equal
        simp only [writtenAt, present, Option.some.injEq] at atAddress
        exact changed atAddress.symm
      · exact .inr collision
    · exact .inl roots
  · intro leaf afterMember beforeMember
    obtain ⟨entry', _, _, rfl⟩ := mem_sealedLeaves W visible writtenKey afterMember
    obtain ⟨entry, _, _, same⟩ := mem_sealedLeaves W visible blinded beforeMember
    rcases leaf_survives_only_by_coincidence same with ⟨_, salts⟩ | collision
    · exact .inl ⟨_, salts⟩
    · exact .inr ⟨_, _, collision⟩

/-- **A covered write still shows** (the accepting pole): when the owner writes
an entry the reader MAY see, the opened entry bytes change. -/
theorem covered_write_shows (B : Blinding W) (keyHidden : ¬ visible B.address)
    {store : Store L} {address : Address L} (shown : visible address)
    {before after : L.Value address.1} (present : store address = some before)
    (changed : before ≠ after) (height : Nat) :
    openedEntries W visible (Patch.run (store.set address (some after)) (B.patch store height)) ≠
      openedEntries W visible store := by
  intro same
  have notKey : address ≠ B.address := fun at_ => keyHidden (at_ ▸ shown)
  have writtenAt : Patch.run (store.set address (some after)) (B.patch store height) address =
      some after := by
    rw [B.run_patch_frame _ _ _ _ notKey, Store.set_eq]
  have inWritten : entryBytes W ⟨address, after⟩ ∈
      openedEntries W visible (Patch.run (store.set address (some after)) (B.patch store height)) := by
    rw [openedEntries_eq_filterMap]
    refine List.mem_filterMap.mpr
      ⟨address, (mem_sortedSupport W _ address).mpr (by simp [writtenAt]), ?_⟩
    simp [writtenAt, shown]
  rw [same, openedEntries_eq_filterMap] at inWritten
  obtain ⟨other, _, found⟩ := List.mem_filterMap.mp inWritten
  cases stored : store other with
  | none => simp [stored] at found
  | some value =>
      simp only [stored, Option.bind_some] at found
      split at found
      · have entriesSame := entryBytes_injective W (Option.some.inj found)
        cases entriesSame
        rw [present] at stored
        exact changed (Option.some.inj stored)
      · cases found

/-! ### The across-writes statement -/

/-- What a reader holds of one entry, with the cell key abstracted: an entry it
may see (its bytes), an entry it may not (its bytes, which it never receives),
or the cell's own blinding entry. -/
inductive Slot where
  | covered (entry : List UInt8)
  | hidden (entry : List UInt8)
  | key
  deriving DecidableEq

/-- What of a slot is public: the bytes of a covered entry; for the others,
only which kind of slot it is. -/
def Slot.shape : Slot → Option (Option (List UInt8))
  | .covered entry => some (some entry)
  | .hidden _ => some none
  | .key => none

/-- The item a slot renders as under a scheme and a cell key; `self` gives the
blinding entry's bytes from the key (the key IS that entry's value bytes). -/
def Slot.item (scheme : LeafScheme) (self : List UInt8 → List UInt8) (key : List UInt8) :
    Slot → Item
  | .covered entry => .inl ⟨scheme.salt key entry, entry⟩
  | .hidden entry => .inr (scheme.leaf key entry)
  | .key => .inr (scheme.leaf key (self key))

/-- Two views of a cell, before and after a write. -/
abbrev Transcript := List Item × List Item

/-- The two views as a function of the cell key: the second is rendered under
the next link of the ratchet. -/
def transcript (scheme : LeafScheme) (self step : List UInt8 → List UInt8)
    (before after : List Slot) (key : List UInt8) : Transcript :=
  (before.map (Slot.item scheme self key), after.map (Slot.item scheme self (step key)))

/-- **The ratcheted-view hiding premise, assumed and not proved at
`deployedLeafScheme`.**  For an unknown key, the pair of views before and after
one ratchet step is indistinguishable from the pair of any other two stores
with the same public shape (the same opened entries in the same positions, the
same count, the blinding in the same place).  At the deployed scheme it is the
multi-query PRF security of KMAC256 under two keys related by the ratchet (the
second derived from the first by KMAC256 itself) with cSHAKE256 read as a
random oracle; this tree has no model of feasible computation, so it is a
schema over the relation, discharged nowhere at the deployed scheme.  Poles:
`toyRatchet_hides` (satisfied, survival-pattern relation) and
`toyStatic_reveals` (refuted: the same scheme without the ratchet). -/
def RatchetedViewHiding (scheme : LeafScheme) (self step : List UInt8 → List UInt8)
    (Indistinguishable : (List UInt8 → Transcript) → (List UInt8 → Transcript) → Prop) : Prop :=
  ∀ before after before' after' : List Slot,
    before.map Slot.shape = before'.map Slot.shape →
    after.map Slot.shape = after'.map Slot.shape →
    Indistinguishable (transcript scheme self step before after)
      (transcript scheme self step before' after')

omit [DecidablePred visible] in
/-- The bytes of the blinding entry whose value bytes are `key`. -/
def selfBytes (B : Blinding W) (key : List UInt8) : List UInt8 :=
  (addressStream W).encode B.address ++ key

/-- The slot of one entry of a store. -/
def slotOf (B : Blinding W) (entry : Entry L) : Slot :=
  if addressKey W entry.1 = addressKey W B.address then .key
  else if visible entry.1 then .covered (entryBytes W entry) else .hidden (entryBytes W entry)

/-- The slots of a store, in canonical entry order. -/
def slots (B : Blinding W) (store : Store L) : List Slot :=
  (entries W store).map (slotOf W visible B)

/-- A blinded store's items are its slots rendered under its key. -/
theorem items_eq_slots (B : Blinding W) (keyHidden : ¬ visible B.address) {store : Store L}
    {key : List UInt8} (blinded : blindingKey W store = some key) :
    items W visible store =
      (slots W visible B store).map (Slot.item deployedLeafScheme (selfBytes W B) key) := by
  unfold items slots
  rw [List.map_map]
  apply List.map_congr_left
  intro entry member
  simp only [Function.comp_apply, slotOf]
  split
  · rename_i atKey
    obtain ⟨address, value⟩ := entry
    have isKey : address = B.address := addressKey_injective W atKey
    subst isKey
    have stored := mem_entries W member
    have keyIs : key = (W.valueStream B.space).encode value := by
      have bytes := blinded
      rw [B.blindingKey_eq] at bytes
      simp only at stored
      rw [stored] at bytes
      exact (Option.some.inj bytes).symm
    rw [sealed_item_is_keyed_leaf W visible blinded keyHidden, keyIs]
    rfl
  · split
    · rename_i _ shown
      simp [itemOf, shown, opening, blinded, Slot.item, deployedLeafScheme]
    · rename_i _ hidden
      rw [sealed_item_is_keyed_leaf W visible blinded hidden]
      rfl

/-- The public shape of a store's slots is a function of its support and of
what the reader may see. -/
theorem slots_shape_congr (B : Blinding W) {left right : Store L}
    (sameSupport : ∀ address, left address = none ↔ right address = none)
    (agree : ∀ address, visible address → left address = right address) :
    (slots W visible B left).map Slot.shape = (slots W visible B right).map Slot.shape := by
  unfold slots entries
  rw [List.map_map, List.map_map, List.map_filterMap, List.map_filterMap,
    sortedSupport_congr W sameSupport]
  apply List.filterMap_congr
  intro address _
  by_cases shown : visible address
  · rw [agree address shown]
  · rcases l : left address with _ | value <;> rcases r : right address with _ | value'
    · rfl
    · exact absurd ((sameSupport address).mp l) (by rw [r]; simp)
    · exact absurd ((sameSupport address).mpr r) (by rw [l]; simp)
    · by_cases atKey : addressKey W address = addressKey W B.address <;>
        simp [slotOf, atKey, shown, Slot.shape]

/-- Slots of one shape render, under one key, the same opened items. -/
theorem opened_of_shape (scheme : LeafScheme) (self : List UInt8 → List UInt8) (key : List UInt8) :
    ∀ (left right : List Slot), left.map Slot.shape = right.map Slot.shape →
      (left.map (Slot.item scheme self key)).filterMap Sum.getLeft? =
        (right.map (Slot.item scheme self key)).filterMap Sum.getLeft?
  | [], [], _ => rfl
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same
  | first :: rest, first' :: rest', same => by
      simp only [List.map_cons, List.cons.injEq] at same
      have tail := opened_of_shape scheme self key rest rest' same.2
      cases first <;> cases first' <;>
        simp_all [Slot.shape, Slot.item]

/-- An uncovered write: none, or one in-place write of an entry the reader may
not see that is not the blinding. -/
def UncoveredWrite (B : Blinding W) (store written : Store L) : Prop :=
  written = store ∨ ∃ address : Address L, ¬ visible address ∧ address ≠ B.address ∧
    store address ≠ none ∧ ∃ value : L.Value address.1, written = store.set address (some value)

omit [DecidablePred visible] in
theorem uncoveredWrite_after (B : Blinding W) (keyHidden : ¬ visible B.address)
    {store written : Store L} (write : UncoveredWrite W visible B store written)
    {key : List UInt8} (blinded : blindingKey W store = some key) (height : Nat) :
    (∀ address, Patch.run written (B.patch store height) address = none ↔ store address = none) ∧
      (∀ address, visible address →
        Patch.run written (B.patch store height) address = store address) ∧
      blindingKey W (Patch.run written (B.patch store height)) = some (B.step height key) := by
  have afterKey := B.run_patch_blinding store written height blinded
  have keyPresent : ∀ s : Store L, blindingKey W s ≠ none → s B.address ≠ none := by
    intro s found absent
    rw [B.blindingKey_eq, absent] at found
    exact found rfl
  have writtenFrame : ∀ address, address ≠ B.address →
      (written address = none ↔ store address = none) ∧
        (visible address → written address = store address) := by
    intro address notKey
    rcases write with same | ⟨target, hidden, _, present, value, rfl⟩
    · subst same; exact ⟨Iff.rfl, fun _ => rfl⟩
    · by_cases at_ : address = target
      · subst at_
        refine ⟨?_, fun shown => absurd shown hidden⟩
        rw [Store.set_eq]
        exact ⟨fun h => (by cases h), fun h => absurd h present⟩
      · rw [Store.set_ne _ _ _ _ at_]
        exact ⟨Iff.rfl, fun _ => rfl⟩
  refine ⟨?_, ?_, afterKey⟩
  · intro address
    by_cases atKey : address = B.address
    · subst atKey
      have l := keyPresent _ (by rw [afterKey]; simp)
      have r := keyPresent store (by rw [blinded]; simp)
      exact ⟨fun h => absurd h l, fun h => absurd h r⟩
    · rw [B.run_patch_frame _ _ _ _ atKey]
      exact (writtenFrame address atKey).1
  · intro address shown
    have notKey : address ≠ B.address := fun at_ => keyHidden (at_ ▸ shown)
    rw [B.run_patch_frame _ _ _ _ notKey]
    exact (writtenFrame address notKey).2 shown

omit [DecidablePred visible] in
/-- Two views as the reader receives them, roots included. -/
def render (t : Transcript) : (Digest × List Item) × (Digest × List Item) :=
  ((rootOfItems W t.1, t.1), (rootOfItems W t.2, t.2))

/-- **Independence of uncovered entries, across a write.**  Two blinded stores
under the same key that agree on everything the reader may see and have the
same support; each then takes an uncovered write (or none) and the kernel's
ratchet at `height`.  Then the reader's opened items are byte-identical between
the two, before AND after (salts included: same key, same covered entries), and
each store's pair of views — roots and items — is the rendering, at the key the
reader does not hold, of a transcript function; under the named premise the two
transcript functions are indistinguishable.  What the reader can tell the two
apart by is exactly what `RatchetedViewHiding` names: nothing but the sealed
leaves' dependence on the hidden entries under an unknown key. -/
theorem narrowed_view_independent_of_uncovered_across_writes
    (B : Blinding W) (keyHidden : ¬ visible B.address) (height : Nat)
    (Indistinguishable : (List UInt8 → Transcript) → (List UInt8 → Transcript) → Prop)
    (premise : RatchetedViewHiding deployedLeafScheme (selfBytes W B) (B.step height)
      Indistinguishable)
    {left right leftWritten rightWritten : Store L} {key : List UInt8}
    (leftKey : blindingKey W left = some key) (rightKey : blindingKey W right = some key)
    (sameSupport : ∀ address, left address = none ↔ right address = none)
    (agree : ∀ address, visible address → left address = right address)
    (leftWrite : UncoveredWrite W visible B left leftWritten)
    (rightWrite : UncoveredWrite W visible B right rightWritten) :
    opened W visible left = opened W visible right ∧
      opened W visible (Patch.run leftWritten (B.patch left height)) =
        opened W visible (Patch.run rightWritten (B.patch right height)) ∧
      ∃ leftTranscript rightTranscript : List UInt8 → Transcript,
        (view W visible left, view W visible (Patch.run leftWritten (B.patch left height))) =
            render W (leftTranscript key) ∧
          (view W visible right, view W visible (Patch.run rightWritten (B.patch right height))) =
            render W (rightTranscript key) ∧
          Indistinguishable leftTranscript rightTranscript := by
  obtain ⟨leftSupport, leftAgree, leftAfterKey⟩ :=
    uncoveredWrite_after W visible B keyHidden leftWrite leftKey height
  obtain ⟨rightSupport, rightAgree, rightAfterKey⟩ :=
    uncoveredWrite_after W visible B keyHidden rightWrite rightKey height
  have shapes := slots_shape_congr W visible B sameSupport agree
  have shapes' := slots_shape_congr W visible B
    (left := Patch.run leftWritten (B.patch left height))
    (right := Patch.run rightWritten (B.patch right height))
    (fun address => by rw [leftSupport, rightSupport]; exact sameSupport address)
    (fun address shown => by
      rw [leftAgree address shown, rightAgree address shown]; exact agree address shown)
  have itemsLeft := items_eq_slots W visible B keyHidden leftKey
  have itemsRight := items_eq_slots W visible B keyHidden rightKey
  have itemsLeft' := items_eq_slots W visible B keyHidden leftAfterKey
  have itemsRight' := items_eq_slots W visible B keyHidden rightAfterKey
  refine ⟨?_, ?_, transcript deployedLeafScheme (selfBytes W B) (B.step height)
      (slots W visible B left) (slots W visible B (Patch.run leftWritten (B.patch left height))),
    transcript deployedLeafScheme (selfBytes W B) (B.step height)
      (slots W visible B right) (slots W visible B (Patch.run rightWritten (B.patch right height))),
    ?_, ?_, premise _ _ _ _ shapes shapes'⟩
  · unfold opened
    rw [itemsLeft, itemsRight]
    exact opened_of_shape _ _ _ _ _ shapes
  · unfold opened
    rw [itemsLeft', itemsRight']
    exact opened_of_shape _ _ _ _ _ shapes'
  · rw [view_eq_render, view_eq_render, itemsLeft, itemsLeft']
    rfl
  · rw [view_eq_render, view_eq_render, itemsRight, itemsRight']
    rfl

omit [DecidablePred visible] in
/-- A cell's write history, replayed: each write its source patch and its
admission height, then the kernel's ratchet. -/
def replay (B : Blinding W) : Store L → List (Patch L × Nat) → Store L
  | store, [] => store
  | store, (source, height) :: rest =>
      replay B (Patch.run store (source ++ B.patch store height)) rest

omit [DecidablePred visible] in
/-- **The ratchet is determined by the birth** (the client's derivation equals
the Host's, at every height).  Replaying any write history from a blinded birth
leaves the blinding at the chain of the birth key over the heights of the
writes — for every history, hence at every prefix.  The owner's client computes
`Blinding.chain` from the birth blinding it derives from its seed and the
heights of the writes; no other key material. -/
theorem ratchet_determined_by_birth (B : Blinding W) :
    ∀ (history : List (Patch L × Nat)) (birth : Store L) {key : List UInt8},
      blindingKey W birth = some key →
        blindingKey W (replay W B birth history) = some (B.chain key (history.map Prod.snd))
  | [], _, _, blinded => by simpa [replay, Blinding.chain] using blinded
  | (source, height) :: rest, birth, _, blinded => by
      have next := B.run_leg_blinding birth source height blinded
      simpa [replay, Blinding.chain, List.foldl_cons] using
        ratchet_determined_by_birth B rest _ next

omit [DecidablePred visible] in
/-- A patch of reads changes nothing. -/
theorem run_reads : ∀ (store : Store L) (reads : Patch L),
    (∀ op ∈ reads, op.writeAddress? = none) → Patch.run store reads = store
  | _, [], _ => rfl
  | store, op :: rest, readOnly => by
      have opRead := readOnly op (by simp)
      have applied : op.apply store = store := by
        cases op <;> simp_all [Op.writeAddress?, Op.apply]
      rw [Patch.run_cons, applied]
      exact run_reads store rest (fun other member => readOnly other (by simp [member]))

omit [DecidablePred visible] in
/-- **The ratchet advances on a write and not on a read.**  A write leg (any
source patch, then the ratchet) leaves the blinding one link on; a read leaves
the store — its blinding, its root and every leaf — exactly as it was. -/
theorem ratchet_advances_on_write (B : Blinding W) {pre : Store L} {key : List UInt8}
    (blinded : blindingKey W pre = some key) (source : Patch L) (height : Nat)
    (reads : Patch L) (readOnly : ∀ op ∈ reads, op.writeAddress? = none) :
    blindingKey W (Patch.run pre (source ++ B.patch pre height)) = some (B.step height key) ∧
      Patch.run pre reads = pre :=
  ⟨B.run_leg_blinding pre source height blinded, run_reads pre reads readOnly⟩

end Ratchet

/-! ### Poles of `RatchetedViewHiding`, decided on a small store at toy schemes -/

/-- A toy keyed scheme: the salt is the key itself and the "hash" is the
identity, so a leaf carries its key and its entry in the clear. -/
def toyKeyedScheme : LeafScheme where
  salt key _ := key
  hash := _root_.id

/-- A toy ratchet step. -/
def toyStep (key : List UInt8) : List UInt8 := 1 :: key

/-- Which items of the after-view equal which items of the before-view: the
test a reader runs to see which leaf moved or which value returned. -/
def survivalPattern (t : Transcript) : List (List Bool) :=
  t.2.map fun after => t.1.map fun before => decide (after = before)

/-- Indistinguishability by the survival pattern, at every key. -/
def SamePattern (left right : List UInt8 → Transcript) : Prop :=
  ∀ key, survivalPattern (left key) = survivalPattern (right key)

/-- Under the toy ratchet no item of the after-view equals any item of the
before-view. -/
theorem toy_items_differ (key : List UInt8) (slot slot' : Slot) :
    Slot.item toyKeyedScheme _root_.id (toyStep key) slot' ≠ Slot.item toyKeyedScheme _root_.id key slot := by
  intro same
  cases slot' <;> cases slot <;>
    simp only [Slot.item, toyKeyedScheme, LeafScheme.leaf, _root_.id, reduceCtorEq] at same <;>
    first
    | (have openings := Opening.preimage_injective (Sum.inr.inj same)
       simp [toyStep] at openings)
    | (have openings := Sum.inl.inj same
       simp [toyStep] at openings)

/-- **Satisfiable** (toy scheme, survival-pattern relation): under the toy
ratchet every survival pattern is all-false, so it depends on nothing but the
count — a reader cannot tell which leaf moved or whether a value returned. -/
theorem toyRatchet_hides : RatchetedViewHiding toyKeyedScheme _root_.id toyStep SamePattern := by
  intro before after before' after' shapes shapes' key
  have lengths : before.length = before'.length := by
    simpa using congrArg List.length shapes
  have lengths' : after.length = after'.length := by
    simpa using congrArg List.length shapes'
  have allFalse : ∀ (first second : List Slot),
      survivalPattern (transcript toyKeyedScheme _root_.id toyStep first second key) =
        second.map fun _ => first.map fun _ => false := by
    intro first second
    simp only [survivalPattern, transcript, List.map_map]
    apply List.map_congr_left
    intro slot' _
    simp only [Function.comp_apply]
    apply List.map_congr_left
    intro slot _
    simp [toy_items_differ]
  rw [allFalse, allFalse]
  simp [List.map_const', lengths, lengths']

/-- **Refutable** (the same toy scheme with a STATIC key): writing the second
of two hidden entries and writing the first give different survival patterns —
the unwritten leaf survives and the written one does not, so the reader sees
WHICH entry moved.  This is the channel K-NARROW-HIDE left open. -/
theorem toyStatic_reveals : ¬ RatchetedViewHiding toyKeyedScheme _root_.id id SamePattern := by
  intro premise
  have same := premise [.hidden [0], .hidden [1]] [.hidden [0], .hidden [2]]
    [.hidden [0], .hidden [1]] [.hidden [3], .hidden [1]] rfl rfl []
  revert same
  decide +kernel

/-- **Return to an old value**, decided on the toy scheme: an entry written
20 → 30 → 20 has its old leaf back under a static key, and not under the toy
ratchet (two links on). -/
theorem toy_return_to_old_value :
    survivalPattern (transcript toyKeyedScheme _root_.id id [.hidden [20]] [.hidden [20]] []) =
        [[true]] ∧
      survivalPattern (transcript toyKeyedScheme _root_.id (toyStep ∘ toyStep)
        [.hidden [20]] [.hidden [20]] []) = [[false]] := by
  decide +kernel

/-! ## Axiom pins -/

/-- info: 'Minidregg.Compiler.StoreHiding.view_root_recomputes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms view_root_recomputes
/-- info: 'Minidregg.Compiler.StoreHiding.narrowed_view_independent_of_uncovered_given_salts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms narrowed_view_independent_of_uncovered_given_salts
/-- info: 'Minidregg.Compiler.StoreHiding.salt_disclosed_iff_value_disclosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms salt_disclosed_iff_value_disclosed
/-- info: 'Minidregg.Compiler.StoreHiding.sealed_item_is_keyed_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sealed_item_is_keyed_leaf
/-- info: 'Minidregg.Compiler.StoreHiding.commitment_hides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commitment_hides
/-- info: 'Minidregg.Compiler.StoreHiding.hiding_at_equality_is_a_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hiding_at_equality_is_a_collision
/-- info: 'Minidregg.Compiler.StoreHiding.constLeafScheme_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms constLeafScheme_hiding
/-- info: 'Minidregg.Compiler.StoreHiding.identityLeafScheme_not_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms identityLeafScheme_not_hiding
/-- info: 'Minidregg.Compiler.StoreHiding.change_detection_only_via_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms change_detection_only_via_root
/-- info: 'Minidregg.Compiler.StoreHiding.covered_write_shows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms covered_write_shows
/-- info: 'Minidregg.Compiler.StoreHiding.leaf_survives_only_by_coincidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms leaf_survives_only_by_coincidence
/-- info: 'Minidregg.Compiler.StoreHiding.items_eq_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms items_eq_slots
/-- info: 'Minidregg.Compiler.StoreHiding.narrowed_view_independent_of_uncovered_across_writes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms narrowed_view_independent_of_uncovered_across_writes
/-- info: 'Minidregg.Compiler.StoreHiding.ratchet_determined_by_birth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ratchet_determined_by_birth
/-- info: 'Minidregg.Compiler.StoreHiding.ratchet_advances_on_write' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ratchet_advances_on_write
/-- info: 'Minidregg.Compiler.StoreHiding.toy_items_differ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toy_items_differ
/-- info: 'Minidregg.Compiler.StoreHiding.toyRatchet_hides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toyRatchet_hides
/-- info: 'Minidregg.Compiler.StoreHiding.toyStatic_reveals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toyStatic_reveals
/-- info: 'Minidregg.Compiler.StoreHiding.toy_return_to_old_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toy_return_to_old_value

end Minidregg.Compiler.StoreHiding
