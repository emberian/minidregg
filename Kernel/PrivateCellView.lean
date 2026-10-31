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

* `viewOpeningExact_deployed`: at the receiver's real parameters (a 256-bit
  cSHAKE256 address hash, a cSHAKE256 node digest over injective node bytes) each
  collision alternative is a genuine cSHAKE256 collision on distinct inputs among
  this store's live addresses or one reveal's scope. The address alternative
  ranges over every live address of the store, not only the reader's classes.
* `storeFits` / `FitStore` / `admit`: the gate over a whole store, refusing
  (`admit_refuses`); `admitted_of_storeFits` discharges `admitted`.
* `Witness`: a declared cell with two data fields, another class and the
  blinding, under a free injective node digest and an injective address path:
  both collision alternatives refuted (`Witness.exact`), honest reveals verify,
  a slot-1 reader is answered its field and refused slot 2, the other class, the
  blinding and an altered value; the full scope is answered every data field and
  never the blinding; a reader naming an overflowing slot whose tag aliases slot
  1 is answered nothing, and such a store is refused at the gate.

Owed: the receiver calls `admit` on its birth, import and write paths (it does
not exist yet; the flat receivers serve the full `Visible` view, so no reader
sees less today).

The reveal's members are not bounded here: an honest reveal stopping early shows
members outside the prefix, which the answer filters out. Hiding them is the ZK
opening's obligation.
-/
module

public import Kernel.PrivateCellScope
public import Compiler.PrivateCellIndex
public import Theory.PrivateCellTrie
public import Kernel.WorldRoot
public import Compiler.PrivateCellRoot

@[expose] public section

namespace Minidregg.Kernel.PrivateCellView

set_option autoImplicit false

open Minidregg.Compiler
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (CellField Digest)
open Minidregg.Kernel.ResourceObservationAdmission
open Minidregg.Kernel.PrivateCellScope
open Minidregg.Theory.AuthTrie (NodeIn Reveal revealVerify root lastVal canon mem_canon CollisionAmong
  reveal_sound revealFor reveal_complete)
open Minidregg.Theory.AuthTrie.Cache (PathsInjective wf_canon)
open Minidregg.Compiler.PrivateCellIndex (indexEntries valueBytes indexExact)
open Minidregg.Compiler.PrivateCellRoot (hashedAddrBits hashedAddrBits_length nodeBytesWith nodeBytesWith_injective
  addressCustomization nodeCustomization addressHash addressHash_length deployedDig untaggedClass)

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

/-- The class tag of an address with no field is `Compiler.PrivateCellRoot.untaggedClass`. -/
theorem untagged_eq : (bitCode 256).tag none = untaggedClass := by
  have zero : bitsW 256 0 = List.replicate 256 false := by
    unfold bitsW
    have : (Nat.testBit 0) = fun _ => false := funext Nat.zero_testBit
    rw [this, List.map_const', List.length_range]
  show family none ++ detail 256 none = untaggedClass
  rw [show detail 256 none = false :: bitsW 256 0 from rfl, zero]
  rfl

/-- The private index tag of a registry kind: its address's field class. -/
def kindTag (kind : CanonicalCellRegistry.Kind) : Compiler.PrivateCellRoot.KeyTag (CanonicalCellRegistry.layout kind) :=
  ⟨fun a => (bitCode 256).tag (fieldOf kind a), fun a => bitTag_length 256 _⟩

/-- A kind whose addresses carry no field has the untagged key paths. -/
theorem kindTag_untagged {kind : CanonicalCellRegistry.Kind} (none : ∀ a, fieldOf kind a = none) :
    (kindTag kind).tag = (Compiler.PrivateCellRoot.untagged _).tag := by
  funext a
  simp only [kindTag, Compiler.PrivateCellRoot.untagged, none a, untagged_eq]

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



/-! ## The admission gate over a whole store -/

/-- The private index's gate over a store: every canonical entry's address
passes `addressFits 256`. Decidable from the store's canonical entries. -/
def storeFits (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind))
    (store : Store (CanonicalCellRegistry.layout kind)) : Bool :=
  (StoreCodec.entries wire store).all fun entry => addressFits 256 kind entry.1

/-- **The gate discharges `admitted`.** -/
theorem admitted_of_storeFits {wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)}
    {store : Store (CanonicalCellRegistry.layout kind)} (gate : storeFits wire store = true) :
    ∀ a, store a ≠ none → addressFits 256 kind a = true := by
  intro a live
  have inSupport := (StoreCodec.mem_sortedSupport wire store a).mpr live
  rw [← StoreCodec.entries_keys wire store] at inSupport
  obtain ⟨entry, member, rfl⟩ := List.mem_map.mp inSupport
  exact List.all_eq_true.mp gate entry member

/-- A store the private index holds: its gate passed. Every way a store enters a
private cell (birth, import, write) produces one, so `admitted` is a field, not a
caller's promise. -/
structure FitStore (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)) where
  store : Store (CanonicalCellRegistry.layout kind)
  fits : storeFits wire store = true

/-- The gate as the receiver applies it: a store that fails is refused (`none`). -/
def admit (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind))
    (store : Store (CanonicalCellRegistry.layout kind)) : Option (FitStore wire) :=
  if h : storeFits wire store = true then some ⟨store, h⟩ else none

theorem admit_refuses {wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)}
    {store : Store (CanonicalCellRegistry.layout kind)} {a : Address (CanonicalCellRegistry.layout kind)}
    (live : store a ≠ none) (overflows : addressFits 256 kind a = false) : admit wire store = none := by
  unfold admit
  split
  · rename_i gate
    have := admitted_of_storeFits gate a live
    rw [overflows] at this; cases this
  · rfl

/-! ## The receiver's address path: a hash of the canonical address bytes -/

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


/-! ## At the deployed shape: cSHAKE256 nodes and address hashes -/

open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec digestStream)

theorem output_eq {o₁ o₂ : Sp800185Cshake256.Output} (same : o₁.bytes = o₂.bytes) : o₁ = o₂ := by
  cases o₁; cases o₂; simp only at same; subst same; rfl

theorem output_eq_of_digest_eq {o₁ o₂ : Sp800185Cshake256.Output} (same : o₁.digest = o₂.digest) : o₁ = o₂ := by
  apply output_eq
  have bytesEq := congrArg Sp800185Cshake256.digestBytesLE same
  simp only [Sp800185Cshake256.Output.digest] at bytesEq
  rwa [Sp800185Cshake256.digestBytesLE_digestOfBytesLE _ o₁.length_exact,
    Sp800185Cshake256.digestBytesLE_digestOfBytesLE _ o₂.length_exact] at bytesEq

/-- **The deployed seam.** At the receiver's address hash (`addressHash`, 256
bits) and node digest (`deployedDig`), a verifying reveal family answers exactly
the reader's view, or cSHAKE256 under the address customization collides on the
distinct canonical bytes of two of this store's live addresses, or cSHAKE256
under the node customization collides on the distinct bytes of two nodes of one
reveal's scope. The address alternative ranges over every live address of the
store, not only the reader's classes: an over-approximation, conservative but
not local. -/
theorem viewOpeningExact_deployed {wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind)}
    (selected : CanonicalCellRegistry.wire? kind = some wire) (store : Store (CanonicalCellRegistry.layout kind))
    (fields : Option (Finset CellField))
    (reveals : List Bool → Reveal (Address (CanonicalCellRegistry.layout kind)) (List UInt8) Digest)
    (admitted : ∀ a, store a ≠ none → addressFits 256 kind a = true)
    (accepted : ∀ p ∈ readerPrefixes fields,
      revealVerify (deployedDig wire) (keyBits (hashedAddrBits wire 256 addressHash)) (260 + 256)
        (root (deployedDig wire) (keyBits (hashedAddrBits wire 256 addressHash)) (260 + 256) (indexEntries wire store))
        p (reveals p) = true) :
    (∀ a v, (∃ p ∈ readerPrefixes fields, (a, v) ∈ (reveals p).answer (keyBits (hashedAddrBits wire 256 addressHash)) p) ↔
        ∃ value, DFinsupp.filter (Visible fields kind) store a = some value ∧ v = valueBytes wire a value) ∨
      (∃ a a', (lastVal (indexEntries wire store) a).isSome ∧ (lastVal (indexEntries wire store) a').isSome ∧
        (StoreCodec.addressStream wire).encode a ≠ (StoreCodec.addressStream wire).encode a' ∧
        Sp800185Cshake256.hash addressCustomization ((StoreCodec.addressStream wire).encode a) =
          Sp800185Cshake256.hash addressCustomization ((StoreCodec.addressStream wire).encode a')) ∨
      ∃ p ∈ readerPrefixes fields, ∃ x y,
        Theory.PrivateCellTrie.revealNodes (deployedDig wire) (keyBits (hashedAddrBits wire 256 addressHash)) (260 + 256)
          (indexEntries wire store) p (reveals p) x ∧
        Theory.PrivateCellTrie.revealNodes (deployedDig wire) (keyBits (hashedAddrBits wire 256 addressHash)) (260 + 256)
          (indexEntries wire store) p (reveals p) y ∧
        nodeBytesWith wire digestStream x ≠ nodeBytesWith wire digestStream y ∧
        Sp800185Cshake256.hash nodeCustomization (nodeBytesWith wire digestStream x) =
          Sp800185Cshake256.hash nodeCustomization (nodeBytesWith wire digestStream y) := by
  rcases viewOpeningExact_hashed selected (deployedDig wire) 256 addressHash store fields reveals admitted accepted
      with answered | ⟨a, a', la, la', differ, same⟩ | ⟨p, member, x, y, hx, hy, ne, same⟩
  · exact Or.inl answered
  · refine Or.inr (Or.inl ⟨a, a', la, la', differ, output_eq (WorldRoot.bytesBits_injective ?_)⟩)
    have trunc : ∀ bytes, (addressHash bytes ++ List.replicate 256 false).take 256 = addressHash bytes := by
      intro bytes
      rw [List.take_append_of_le_length (by rw [addressHash_length]),
        List.take_of_length_le (by rw [addressHash_length])]
    rw [trunc, trunc] at same
    exact same
  · exact Or.inr (Or.inr ⟨p, member, x, y, hx, hy,
      fun eq => ne (nodeBytesWith_injective wire digestStream eq), output_eq_of_digest_eq same⟩)

/-! ## A concrete opening: both collision branches refuted -/

namespace Witness

open Minidregg.Theory.EffectDeclaration (StateKey)
open Minidregg.Compiler.IntStream (intStream)

abbrev K := Address (CanonicalCellRegistry.layout .declaredObject)

def wire : StoreCodec.Wire (CanonicalCellRegistry.layout .declaredObject) := DeclaredEffectCell.wire

theorem selected : CanonicalCellRegistry.wire? .declaredObject = some wire := rfl

def object : Minidregg.Theory.TypedAuthorization.ResourceId .object := ⟨7⟩

/-- Two visible data fields, a field of another class (the declaration's
openness, class `code`), and the blinding. -/
def a1 : K := (StateKey.objectField object ⟨1⟩).address
def a2 : K := (StateKey.objectField object ⟨2⟩).address
def aCode : K := (StateKey.fieldsOpen object).address
def aBlind : K := StateKey.blinding.address

def store : Store (CanonicalCellRegistry.layout .declaredObject) :=
  StoreCodec.fromEntries [⟨a1, (5 : Int)⟩, ⟨a2, (7 : Int)⟩, ⟨aCode, (1 : Int)⟩, ⟨aBlind, (9 : Int)⟩]

/-- A free node digest: the node bytes themselves, children as byte lists. -/
def freeDig : NodeIn K (List UInt8) (List UInt8) → List UInt8 :=
  nodeBytesWith wire (StreamCodec.list StreamCodec.byte)

theorem freeDig_no_collision (S : NodeIn K (List UInt8) (List UInt8) → Prop) : ¬ CollisionAmong freeDig S := by
  rintro ⟨x, y, _, _, ne, same⟩
  exact ne (nodeBytesWith_injective wire _ same)

/-- An address path injective on the store's addresses. -/
def addrBits (a : K) : List Bool :=
  bitsW 2 (if a = a1 then 0 else if a = a2 then 1 else if a = aCode then 2 else 3)

theorem addrBits_length (a : K) : (addrBits a).length = 2 := bitsW_length _ _

theorem distinct : ([⟨a1, (5 : Int)⟩, ⟨a2, (7 : Int)⟩, ⟨aCode, (1 : Int)⟩, ⟨aBlind, (9 : Int)⟩] :
    List (Entry (CanonicalCellRegistry.layout .declaredObject))).map Sigma.fst |>.Nodup := by decide

theorem live_mem {a : K} (live : store a ≠ none) : a = a1 ∨ a = a2 ∨ a = aCode ∨ a = aBlind := by
  have := (not_congr (StoreCodec.fromEntries_apply_eq_none_iff _ a)).mp live
  simp only [not_not, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at this
  exact this

theorem admitted : ∀ a, store a ≠ none → addressFits 256 .declaredObject a = true := by
  intro a live
  rcases live_mem live with rfl | rfl | rfl | rfl <;> decide

/-- The overflowing field of the teeth would be refused at the gate. -/
theorem overflow_store_refused :
    admit wire (StoreCodec.fromEntries [⟨(StateKey.objectField object ⟨2 ^ 256⟩).address, (0 : Int)⟩]) = none :=
  admit_refuses (a := (StateKey.objectField object ⟨2 ^ 256⟩).address)
    (by rw [StoreCodec.fromEntries_apply_of_mem _ (by simp) (entry := ⟨_, (0 : Int)⟩) (by simp)]; simp)
    (by simp [addressFits, keyFits, StateKey.address])

theorem index_live {a : K} (live : (lastVal (indexEntries wire store) a).isSome) :
    a = a1 ∨ a = a2 ∨ a = aCode := by
  rw [indexExact wire store a] at live
  split_ifs at live with blind
  · cases live
  · have present : store a ≠ none := by intro none_; rw [none_] at live; cases live
    rcases live_mem present with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · subst h; exact (blind rfl).elim

theorem inj : PathsInjective (keyBits addrBits) (indexEntries wire store) := by
  intro a a' la la' same
  have tags : ((bitCode 256).tag (fieldOf .declaredObject a)).length =
      ((bitCode 256).tag (fieldOf .declaredObject a')).length := by simp [bitCode, bitTag_length]
  have bits := (List.append_inj same tags).2
  rcases index_live la with rfl | rfl | rfl <;> rcases index_live la' with rfl | rfl | rfl <;>
    first | rfl | exact absurd bits (by decide)

/-- **The opening is exact at this store**: for every scope and every verifying
reveal family, the answers are exactly the reader's view. -/
theorem exact (fields : Option (Finset CellField)) (reveals : List Bool → Reveal K (List UInt8) (List UInt8))
    (accepted : ∀ p ∈ readerPrefixes fields,
      revealVerify freeDig (keyBits addrBits) (260 + 2) (root freeDig (keyBits addrBits) (260 + 2) (indexEntries wire store))
        p (reveals p) = true) :
    ∀ a v, (∃ p ∈ readerPrefixes fields, (a, v) ∈ (reveals p).answer (keyBits addrBits) p) ↔
      ∃ value, DFinsupp.filter (Visible fields .declaredObject) store a = some value ∧ v = valueBytes wire a value := by
  rcases viewOpeningExact selected freeDig addrBits 2 addrBits_length store fields reveals admitted accepted
      with answered | ⟨a, a', differ, la, la', same⟩ | ⟨p, _, collision⟩
  · exact answered
  · exact absurd (inj a a' la la' same) differ
  · exact absurd collision (freeDig_no_collision _)

/-- The honest reveals of every scope verify here. -/
theorem honest (fields : Option (Finset CellField)) :
    ∀ p ∈ readerPrefixes fields,
      revealVerify freeDig (keyBits addrBits) (260 + 2) (root freeDig (keyBits addrBits) (260 + 2) (indexEntries wire store))
        p (revealFor freeDig (keyBits addrBits) (260 + 2) (canon (indexEntries wire store)) p) = true :=
  honest_accepted freeDig addrBits_length store fields inj

theorem store_a1 : store a1 = some (5 : Int) :=
  StoreCodec.fromEntries_apply_of_mem _ distinct (entry := ⟨a1, (5 : Int)⟩) (by simp)
theorem store_a2 : store a2 = some (7 : Int) :=
  StoreCodec.fromEntries_apply_of_mem _ distinct (entry := ⟨a2, (7 : Int)⟩) (by simp)
theorem store_aCode : store aCode = some (1 : Int) :=
  StoreCodec.fromEntries_apply_of_mem _ distinct (entry := ⟨aCode, (1 : Int)⟩) (by simp)

/-- The value bytes of a field are injective in the value. -/
theorem valueBytes_injective (a : K) {x y : Int} (same : valueBytes wire a x = valueBytes wire a y) : x = y :=
  StoreCodec.streamEncode_injective _ same

def slot1 : Option (Finset CellField) := some {.slot 1}

/-- A reader of slot 1 is answered `a1`'s value by the honest reveals. -/
theorem slot1_answers_a1 : ∃ p ∈ readerPrefixes slot1,
    (a1, valueBytes wire a1 (5 : Int)) ∈
      (revealFor freeDig (keyBits addrBits) (260 + 2) (canon (indexEntries wire store)) p).answer (keyBits addrBits) p :=
  (exact slot1 _ (honest slot1) a1 _).mpr
    ⟨5, by rw [DFinsupp.filter_apply_pos _ (by decide), store_a1], rfl⟩

/-- No verifying reveal family answers a reader of slot 1 with slot 2, the
other class, the blinding, or an altered value of slot 1. -/
theorem slot1_refuses (reveals : List Bool → Reveal K (List UInt8) (List UInt8))
    (accepted : ∀ p ∈ readerPrefixes slot1,
      revealVerify freeDig (keyBits addrBits) (260 + 2) (root freeDig (keyBits addrBits) (260 + 2) (indexEntries wire store))
        p (reveals p) = true) (v : List UInt8) :
    (¬ ∃ p ∈ readerPrefixes slot1, (a2, v) ∈ (reveals p).answer (keyBits addrBits) p) ∧
      (¬ ∃ p ∈ readerPrefixes slot1, (aCode, v) ∈ (reveals p).answer (keyBits addrBits) p) ∧
      (¬ ∃ p ∈ readerPrefixes slot1, (aBlind, v) ∈ (reveals p).answer (keyBits addrBits) p) ∧
      (¬ ∃ p ∈ readerPrefixes slot1, (a1, valueBytes wire a1 (6 : Int)) ∈ (reveals p).answer (keyBits addrBits) p) := by
  have ex := exact slot1 reveals accepted
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨_, present, _⟩ := (ex a2 v).mp h
    rw [DFinsupp.filter_apply_neg _ (by decide)] at present; cases present
  · obtain ⟨_, present, _⟩ := (ex aCode v).mp h
    rw [DFinsupp.filter_apply_neg _ (by decide)] at present; cases present
  · obtain ⟨_, present, _⟩ := (ex aBlind v).mp h
    rw [DFinsupp.filter_apply_neg _ (by decide)] at present; cases present
  · obtain ⟨value, present, same⟩ := (ex a1 _).mp h
    rw [DFinsupp.filter_apply_pos _ (by decide), store_a1] at present
    cases present
    exact absurd (valueBytes_injective a1 same) (by decide)

/-- The full scope is answered every data field and never the blinding. -/
theorem full_answers (reveals : List Bool → Reveal K (List UInt8) (List UInt8))
    (accepted : ∀ p ∈ readerPrefixes none,
      revealVerify freeDig (keyBits addrBits) (260 + 2) (root freeDig (keyBits addrBits) (260 + 2) (indexEntries wire store))
        p (reveals p) = true) (v : List UInt8) :
    (∃ p ∈ readerPrefixes none, (a2, valueBytes wire a2 (7 : Int)) ∈ (reveals p).answer (keyBits addrBits) p) ∧
      (∃ p ∈ readerPrefixes none, (aCode, valueBytes wire aCode (1 : Int)) ∈ (reveals p).answer (keyBits addrBits) p) ∧
      ¬ ∃ p ∈ readerPrefixes none, (aBlind, v) ∈ (reveals p).answer (keyBits addrBits) p := by
  have ex := exact none reveals accepted
  refine ⟨(ex a2 _).mpr ⟨7, by rw [DFinsupp.filter_apply_pos _ (by decide), store_a2], rfl⟩,
    (ex aCode _).mpr ⟨1, by rw [DFinsupp.filter_apply_pos _ (by decide), store_aCode], rfl⟩, fun h => ?_⟩
  obtain ⟨_, present, _⟩ := (ex aBlind v).mp h
  rw [DFinsupp.filter_apply_neg _ (by decide)] at present; cases present

def overflow : Option (Finset CellField) := some {.slot (2 ^ 256 + 1)}

/-- A reader naming an overflowing slot is answered nothing, although that slot's
tag aliases slot 1's: the cut (`fitScope`) is what keeps `a1` out. -/
theorem overflow_answers_nothing (reveals : List Bool → Reveal K (List UInt8) (List UInt8))
    (accepted : ∀ p ∈ readerPrefixes overflow,
      revealVerify freeDig (keyBits addrBits) (260 + 2) (root freeDig (keyBits addrBits) (260 + 2) (indexEntries wire store))
        p (reveals p) = true) (a : K) (v : List UInt8) :
    (¬ ∃ p ∈ readerPrefixes overflow, (a, v) ∈ (reveals p).answer (keyBits addrBits) p) ∧
      (bitCode 256).opens (.slot (2 ^ 256 + 1)) = (bitCode 256).tag (some (.slot 1)) := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨_, present, _⟩ := (exact overflow reveals accepted a v).mp h
    by_cases visible : Visible overflow .declaredObject a
    · rw [DFinsupp.filter_apply_pos _ visible] at present
      have live : store a ≠ none := by rw [present]; simp
      have fits := fits_of_addressFits (by decide) .declaredObject a (admitted a live)
      obtain ⟨kept, _⟩ := visible
      unfold Kept at kept
      split at kept
      · rename_i f found
        obtain ⟨outer, member, covers⟩ := kept
        rw [Finset.mem_singleton] at member
        subst member
        have eq := CellField.covers_eq_of_ne_body (by simp) covers
        have big : bitFits 256 f := fits f found
        rw [← eq] at big
        exact absurd big (Nat.not_lt.mpr (Nat.le_succ _))
      · simp [overflow] at kept
    · rw [DFinsupp.filter_apply_neg _ visible] at present; cases present
  · have low : ∀ i ∈ List.range 256, (2 ^ 256 + 1).testBit i = Nat.testBit 1 i := by
      intro i member
      exact Nat.testBit_two_pow_add_gt (List.mem_range.mp member) 1
    show bitTag 256 _ = bitTag 256 _
    simp only [bitTag, detail, bitsW, family, List.map_congr_left low]

end Witness

#assert_axioms isBlinding_iff
#assert_axioms pathsInjective_or
#assert_axioms viewOpeningExact
#assert_axioms honest_accepted
#assert_axioms addressCollision_is_hash
#assert_axioms viewOpeningExact_hashed
#assert_axioms viewOpeningExact_deployed
#assert_axioms admitted_of_storeFits
#assert_axioms admit_refuses
#assert_axioms Witness.exact
#assert_axioms Witness.honest
#assert_axioms Witness.slot1_answers_a1
#assert_axioms Witness.slot1_refuses
#assert_axioms Witness.full_answers
#assert_axioms Witness.overflow_answers_nothing
#assert_axioms Witness.overflow_store_refused

end Minidregg.Kernel.PrivateCellView
