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
* `change_detection_only_via_root` — what a narrowed reader STILL learns: a
  write to a sealed entry leaves every opened item unchanged, and moves the
  root unless cSHAKE256 collides.  That an uncovered entry changed, and where
  it sits in address order, is the metadata channel; so are the entry count and
  an entry's return to an earlier value (its leaf returns too).

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

/-! ## What a narrowed reader still learns -/

section Change

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

/-- **Change detection only via the root.**  A write to an entry the reader may
not see, in place (present before and after), leaves every opened item of the
view unchanged — so the covered bytes, and their salts, are byte-identical — and
moves the root unless cSHAKE256 collides.  The second half is the metadata
channel stated: a narrowed reader learns THAT something it may not read
changed (its sealed leaf and the root move), not what. -/
theorem change_detection_only_via_root {store : Store L} {address : Address L}
    (hidden : ¬ visible address) (notKey : W.blinding ≠ some address)
    {before after : L.Value address.1} (present : store address = some before)
    (changed : before ≠ after) :
    opened W visible (store.set address (some after)) = opened W visible store ∧
      (saltedRoot W (store.set address (some after)) ≠ saltedRoot W store ∨
        RootCollision W (store.set address (some after)) store ∨
        ∃ first ∈ (entries W (store.set address (some after))).map
            (opening W (store.set address (some after))),
          ∃ second ∈ (entries W store).map (opening W store), LeafCollision first second) := by
  set written := store.set address (some after) with writtenDef
  have frame : ∀ other, other ≠ address → written other = store other := fun other different =>
    Store.set_ne store address _ other different
  have sameKey : blindingKey W written = blindingKey W store := by
    unfold blindingKey
    cases blindingAddress : W.blinding with
    | none => rfl
    | some keyAddress =>
        have different : keyAddress ≠ address := fun same => notKey (by rw [blindingAddress, same])
        simp [frame keyAddress different]
  have sameSupport : written.support = store.support := by
    ext other
    rw [DFinsupp.mem_support_toFun, DFinsupp.mem_support_toFun]
    by_cases at_ : other = address
    · subst at_
      simp [writtenDef, present]
    · rw [frame other at_]
  have sameSorted : sortedSupport W written = sortedSupport W store := by
    unfold sortedSupport
    rw [sameSupport]
  refine ⟨?_, ?_⟩
  · rw [opened_eq_filterMap, opened_eq_filterMap, sameSorted]
    apply List.filterMap_congr
    intro other _
    by_cases at_ : other = address
    · subst at_
      cases written other <;> cases store other <;> simp [hidden]
    · rw [frame other at_]
      cases store other with
      | none => rfl
      | some value =>
          simp only [Option.map_some, Option.bind_some]
          split <;> simp [opening, sameKey]
  · by_cases roots : saltedRoot W written = saltedRoot W store
    · rcases root_binds_salted_entries W roots with equal | collision
      · exfalso
        have atAddress := congrArg (fun s : Store L => s address) equal
        simp [writtenDef, present] at atAddress
        exact changed atAddress.symm
      · exact .inr collision
    · exact .inl roots

end Change

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

end Minidregg.Compiler.StoreHiding
