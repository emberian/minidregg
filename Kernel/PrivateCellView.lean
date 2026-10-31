/-
# Kernel.PrivateCellView — a reader's class openings of the private index are its view

The seam of docs/PRIVATE-CELLS-STATE.md, item 3. A registry kind with a store
wire keys its private index (`Compiler.PrivateCellIndex.indexEntries`, the
blinding left out) by `keyBits`: the field's class tag under `bitCode 256`
(`Kernel.PrivateCellScope`) followed by `addrBits`, a fixed-width path of the
address (in the receiver, the bits of a hash of the address's canonical bytes).
A reader under `fields` opens one reveal per prefix of its cut scope
(`scopePrefixes (bitCode 256) (fitScope 256 fields)`, at most one per named field).

* `isBlinding_iff`: the wire's exclusion is `CanonicalCellRegistry.isBlinding`.
* `ViewOpeningExact` / `viewOpeningExact`: on a store the index admitted
  (`addressFits 256` at every live address), verifying reveals at those prefixes
  answer exactly the reader's view, the store `narrowPacked` hands it
  (`DFinsupp.filter (Visible fields kind)`), each value as its value bytes; or two
  distinct live addresses share `addrBits` (the index's own collision, scoped to
  this store; at the receiver's `hashedAddrBits`, a collision of the truncated
  hash on distinct canonical address bytes, `viewOpeningExact_hashed`); or a
  reveal's comparison scope holds a digest collision
  (`Theory.PrivateCellTrie.revealNodes`, the scope `reveal_sound` compares).
* `honest_accepted`: the honest reveals verify whenever live paths are distinct,
  so the premise is inhabited.

Owed: a concrete witness excluding both collision alternatives (a registry wire,
an admitted store with two visible entries, another class and the blinding,
under a free node digest), and the admission check (`addressFits`) enforced on
the receiver's birth, import and write paths.

The reveal's members are not bounded here: an honest reveal stopping early shows
members outside the prefix, which the answer filters out. Hiding them is the ZK
opening's obligation.
-/
module

public import Kernel.PrivateCellScope
public import Compiler.PrivateCellIndex
public import Theory.PrivateCellTrie

@[expose] public section

namespace Minidregg.Kernel.PrivateCellView

set_option autoImplicit false

open Minidregg.Compiler
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (CellField)
open Minidregg.Kernel.ResourceObservationAdmission
open Minidregg.Kernel.PrivateCellScope
open Minidregg.Theory.AuthTrie (NodeIn Reveal revealVerify root lastVal canon mem_canon CollisionAmong
  reveal_sound revealFor reveal_complete)
open Minidregg.Theory.AuthTrie.Cache (PathsInjective wf_canon)
open Minidregg.Compiler.PrivateCellIndex (indexEntries valueBytes indexExact)

/-- **The wire's exclusion is the registry's blinding.** -/
theorem isBlinding_iff {kind : CanonicalCellRegistry.Kind} {wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)}
    (selected : CanonicalCellRegistry.wire? kind = some wire) (address : Address (CanonicalCellRegistry.layout kind)) :
    CanonicalCellRegistry.isBlinding kind address = true ↔ some address = wire.blinding := by
  simp only [CanonicalCellRegistry.isBlinding, selected, decide_eq_true_eq]
  exact eq_comm

variable {kind : CanonicalCellRegistry.Kind}

/-- A private index key path: the class tag, then the address's fixed-width path. -/
def keyBits (addrBits : Address (CanonicalCellRegistry.layout kind) → List Bool)
    (address : Address (CanonicalCellRegistry.layout kind)) : List Bool :=
  (bitCode 256).tag (fieldOf kind address) ++ addrBits address

/-- Two distinct live addresses of the index on one key path (one class tag and
one path below it). -/
def AddressCollision {V : Type} (addrBits : Address (CanonicalCellRegistry.layout kind) → List Bool)
    (es : List (Address (CanonicalCellRegistry.layout kind) × V)) : Prop :=
  ∃ a a', a ≠ a' ∧ (lastVal es a).isSome ∧ (lastVal es a').isSome ∧ keyBits addrBits a = keyBits addrBits a'

/-- The prefixes a reader under `fields` opens. -/
noncomputable def readerPrefixes (fields : Option (Finset CellField)) : Finset (List Bool) :=
  scopePrefixes (bitCode 256) (fitScope 256 fields)

/-- **A reader's class openings are its view (statement).** -/
def ViewOpeningExact (kind : CanonicalCellRegistry.Kind) (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)) : Prop :=
  ∀ {D : Type} [DecidableEq D] (dig : NodeIn (Address (CanonicalCellRegistry.layout kind)) (List UInt8) D → D)
    (addrBits : Address (CanonicalCellRegistry.layout kind) → List Bool) (A : Nat),
    (∀ a, (addrBits a).length = A) →
    ∀ (store : Store (CanonicalCellRegistry.layout kind)) (fields : Option (Finset CellField))
      (reveals : List Bool → Reveal (Address (CanonicalCellRegistry.layout kind)) (List UInt8) D),
      (∀ a, store a ≠ none → addressFits 256 kind a = true) →
      (∀ p ∈ readerPrefixes fields,
        revealVerify dig (keyBits addrBits) (260 + A) (root dig (keyBits addrBits) (260 + A) (indexEntries wire store))
          p (reveals p) = true) →
      (∀ a v, (∃ p ∈ readerPrefixes fields, (a, v) ∈ (reveals p).answer (keyBits addrBits) p) ↔
          ∃ value, DFinsupp.filter (Visible fields kind) store a = some value ∧ v = valueBytes wire a value) ∨
        AddressCollision addrBits (indexEntries wire store) ∨
        ∃ p ∈ readerPrefixes fields, CollisionAmong dig
          (Theory.PrivateCellTrie.revealNodes dig (keyBits addrBits) (260 + A) (indexEntries wire store) p (reveals p))

theorem keyBits_length {addrBits : Address (CanonicalCellRegistry.layout kind) → List Bool} {A : Nat}
    (lengths : ∀ a, (addrBits a).length = A) (a : Address (CanonicalCellRegistry.layout kind)) :
    (keyBits addrBits a).length = 260 + A := by
  simp [keyBits, bitCode, bitTag_length, lengths]

/-- Distinct paths below the tag, or the index's own collision. -/
theorem pathsInjective_or {V : Type} {addrBits : Address (CanonicalCellRegistry.layout kind) → List Bool}
    (es : List (Address (CanonicalCellRegistry.layout kind) × V)) :
    PathsInjective (keyBits addrBits) es ∨ AddressCollision addrBits es := by
  by_cases collides : AddressCollision addrBits es
  · exact Or.inr collides
  · left
    intro a a' la la' same
    by_contra differ
    exact collides ⟨a, a', differ, la, la', same⟩

theorem readerPrefixes_short (fields : Option (Finset CellField)) :
    ∀ p ∈ readerPrefixes fields, p.length ≤ 260 := by
  intro p member
  unfold readerPrefixes at member
  cases fields with
  | none => simp [fitScope, scopePrefixes] at member; subst member; simp
  | some named =>
      simp only [fitScope, scopePrefixes, Finset.mem_image] at member
      obtain ⟨outer, inNamed, rfl⟩ := member
      exact opens_length_le (bitCode 256) outer (Finset.mem_filter.mp inNamed).2

theorem viewOpeningExact {wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)}
    (selected : CanonicalCellRegistry.wire? kind = some wire) : ViewOpeningExact kind wire := by
  intro D _ dig addrBits A lengths store fields reveals admitted accepted
  rcases pathsInjective_or (addrBits := addrBits) (indexEntries wire store) with inj | collides
  · by_cases revealCollides : ∃ p ∈ readerPrefixes fields, CollisionAmong dig
        (Theory.PrivateCellTrie.revealNodes dig (keyBits addrBits) (260 + A) (indexEntries wire store) p (reveals p))
    · exact Or.inr (Or.inr revealCollides)
    · left
      push_neg at revealCollides
      have answers : ∀ p ∈ readerPrefixes fields, ∀ a v, (a, v) ∈ (reveals p).answer (keyBits addrBits) p ↔
          lastVal (indexEntries wire store) a = some v ∧ (keyBits addrBits a).take p.length = p := by
        intro p member a v
        rcases reveal_sound dig (keyBits addrBits) (260 + A) (keyBits_length lengths) (canon (indexEntries wire store))
            (wf_canon (keyBits_length lengths) inj) p (reveals p) (accepted p member) with same | collision
        · rw [same a v, mem_canon]
        · exact absurd collision (revealCollides p member)
      intro a v
      have live := indexExact wire store a
      constructor
      · rintro ⟨p, member, answered⟩
        obtain ⟨found, prefixed⟩ := (answers p member a v).mp answered
        rw [live] at found
        split_ifs at found with blind
        obtain ⟨value, present, rfl⟩ := Option.map_eq_some_iff.mp found
        have notBlinding : CanonicalCellRegistry.isBlinding kind a = false := by
          cases h : CanonicalCellRegistry.isBlinding kind a
          · rfl
          · exact absurd ((isBlinding_iff selected a).mp h) blind
        have fits := fits_of_addressFits (by decide) kind a (admitted a (by simp [present]))
        have visible : Visible fields kind a := by
          rw [← visible_fitScope 256 fields kind a fits,
            scopeSelectsPath (bitCode 256) kind (fitScope 256 fields) a (addrBits a) (fitScope_fits 256 fields)
              fits notBlinding]
          exact ⟨p, member, List.prefix_iff_eq_take.mpr prefixed.symm⟩
        exact ⟨value, by rw [DFinsupp.filter_apply_pos _ visible, present], rfl⟩
      · rintro ⟨value, present, rfl⟩
        by_cases visible : Visible fields kind a
        · rw [DFinsupp.filter_apply_pos _ visible] at present
          have fits := fits_of_addressFits (by decide) kind a (admitted a (by simp [present]))
          have notBlinding := visible.2
          have selects := (scopeSelectsPath (bitCode 256) kind (fitScope 256 fields) a (addrBits a)
            (fitScope_fits 256 fields) fits notBlinding).mp ((visible_fitScope 256 fields kind a fits).mpr visible)
          obtain ⟨p, member, prefixed⟩ := selects
          refine ⟨p, member, (answers p member a _).mpr ⟨?_, (List.prefix_iff_eq_take.mp prefixed).symm⟩⟩
          rw [live, if_neg (fun blind => by
            have := (isBlinding_iff selected a).mpr blind
            rw [notBlinding] at this; cases this), present]
          rfl
        · rw [DFinsupp.filter_apply_neg _ visible] at present
          cases present
  · exact Or.inr (Or.inl collides)

/-- **Premise inhabitation**: with distinct live paths, the honest reveals at a
reader's prefixes verify. -/
theorem honest_accepted {wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)} {D : Type} [DecidableEq D]
    (dig : NodeIn (Address (CanonicalCellRegistry.layout kind)) (List UInt8) D → D)
    {addrBits : Address (CanonicalCellRegistry.layout kind) → List Bool} {A : Nat}
    (lengths : ∀ a, (addrBits a).length = A) (store : Store (CanonicalCellRegistry.layout kind))
    (fields : Option (Finset CellField)) (inj : PathsInjective (keyBits addrBits) (indexEntries wire store)) :
    ∀ p ∈ readerPrefixes fields,
      revealVerify dig (keyBits addrBits) (260 + A) (root dig (keyBits addrBits) (260 + A) (indexEntries wire store)) p
        (revealFor dig (keyBits addrBits) (260 + A) (canon (indexEntries wire store)) p) = true := by
  intro p member
  exact reveal_complete dig (keyBits addrBits) (260 + A) (keyBits_length lengths) _
    (wf_canon (keyBits_length lengths) inj) p (by have := readerPrefixes_short fields p member; omega)


/-! ## The receiver's address path: a hash of the canonical address bytes -/

/-- The address path of the receiver: the first `A` bits of a hash of the
address's canonical bytes (`StoreCodec.addressStream`), the hash any function
to bit lists. -/
def hashedAddrBits (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)) (A : Nat)
    (hash : List UInt8 → List Bool) (address : Address (CanonicalCellRegistry.layout kind)) : List Bool :=
  ((hash ((StoreCodec.addressStream wire).encode address)) ++ List.replicate A false).take A

theorem hashedAddrBits_length (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)) (A : Nat)
    (hash : List UInt8 → List Bool) (address : Address (CanonicalCellRegistry.layout kind)) :
    (hashedAddrBits wire A hash address).length = A := by
  simp [hashedAddrBits]

/-- **The index's collision is the hash's.** Two distinct live addresses on one
key path have distinct canonical bytes (the address codec is injective) whose
truncated hashes agree: a collision of the truncated hash among this store's live
addresses, not a global one. -/
theorem addressCollision_is_hash {V : Type} {wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)} {A : Nat}
    {hash : List UInt8 → List Bool} {es : List (Address (CanonicalCellRegistry.layout kind) × V)}
    (collides : AddressCollision (hashedAddrBits wire A hash) es) :
    ∃ a a', (lastVal es a).isSome ∧ (lastVal es a').isSome ∧
      (StoreCodec.addressStream wire).encode a ≠ (StoreCodec.addressStream wire).encode a' ∧
      (hash ((StoreCodec.addressStream wire).encode a) ++ List.replicate A false).take A =
        (hash ((StoreCodec.addressStream wire).encode a') ++ List.replicate A false).take A := by
  obtain ⟨a, a', differ, la, la', same⟩ := collides
  have tags : ((bitCode 256).tag (fieldOf kind a)).length = ((bitCode 256).tag (fieldOf kind a')).length := by
    simp [bitCode, bitTag_length]
  exact ⟨a, a', la, la', fun bytes => differ (StoreCodec.streamEncode_injective _ bytes),
    (List.append_inj same tags).2⟩

/-- `viewOpeningExact` at the receiver's address path. -/
theorem viewOpeningExact_hashed {wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)}
    (selected : CanonicalCellRegistry.wire? kind = some wire) {D : Type} [DecidableEq D]
    (dig : NodeIn (Address (CanonicalCellRegistry.layout kind)) (List UInt8) D → D) (A : Nat)
    (hash : List UInt8 → List Bool) (store : Store (CanonicalCellRegistry.layout kind))
    (fields : Option (Finset CellField))
    (reveals : List Bool → Reveal (Address (CanonicalCellRegistry.layout kind)) (List UInt8) D)
    (admitted : ∀ a, store a ≠ none → addressFits 256 kind a = true)
    (accepted : ∀ p ∈ readerPrefixes fields,
      revealVerify dig (keyBits (hashedAddrBits wire A hash)) (260 + A)
        (root dig (keyBits (hashedAddrBits wire A hash)) (260 + A) (indexEntries wire store)) p (reveals p) = true) :
    (∀ a v, (∃ p ∈ readerPrefixes fields, (a, v) ∈ (reveals p).answer (keyBits (hashedAddrBits wire A hash)) p) ↔
        ∃ value, DFinsupp.filter (Visible fields kind) store a = some value ∧ v = valueBytes wire a value) ∨
      (∃ a a', (lastVal (indexEntries wire store) a).isSome ∧ (lastVal (indexEntries wire store) a').isSome ∧
        (StoreCodec.addressStream wire).encode a ≠ (StoreCodec.addressStream wire).encode a' ∧
        (hash ((StoreCodec.addressStream wire).encode a) ++ List.replicate A false).take A =
          (hash ((StoreCodec.addressStream wire).encode a') ++ List.replicate A false).take A) ∨
      ∃ p ∈ readerPrefixes fields, CollisionAmong dig
        (Theory.PrivateCellTrie.revealNodes dig (keyBits (hashedAddrBits wire A hash)) (260 + A)
          (indexEntries wire store) p (reveals p)) := by
  rcases viewOpeningExact selected dig (hashedAddrBits wire A hash) A (hashedAddrBits_length wire A hash) store fields
      reveals admitted accepted with answered | collides | revealCollides
  · exact Or.inl answered
  · exact Or.inr (Or.inl (addressCollision_is_hash collides))
  · exact Or.inr (Or.inr revealCollides)

#assert_axioms isBlinding_iff
#assert_axioms pathsInjective_or
#assert_axioms viewOpeningExact
#assert_axioms honest_accepted
#assert_axioms addressCollision_is_hash
#assert_axioms viewOpeningExact_hashed

end Minidregg.Kernel.PrivateCellView
