/-
# Compiler.StoreCodec -- the canonical unbounded encoding of one cell store

A cell's state is one finitely-supported typed store `Store L` over a layout
`L` (`Kernel.SparseAuthenticatedState`).  This module is its single wire
representation, for every layout at once:

* **payload** — the store's support, sorted by the canonical bytes of each
  address, written as one length-prefixed list of `(address, value)` entries.
  An address is its namespace's bytes followed by its key's bytes; a value is
  its namespace's value bytes.  There is no capacity, no slot, no shard, and no
  per-entry absence tag: a store's `none` is absence, so absence is simply not
  written and "explicit none" is not representable.
* **order** — lexicographic order on address BYTES.  It is derived from the
  address codec, so it cannot disagree with the wire and a verifier can check
  canonical order on bytes without knowing the key types.  (It is not numeric
  order: naturals are base-255 little-endian digits.)
* **canonical decoding** — the lax decoder reads any well-formed entry list;
  the canonical decoder additionally re-encodes and compares.  Hence the
  accepted language is exactly the image of `encode`
  (`decode_eq_some_iff`), and at the entry-list level it is exactly the lists
  that are strictly increasing in address bytes (`decodePayload_list_eq_some_iff`).
  Out-of-order, duplicate, and non-minimal component encodings are refused.

## The frame: what the bytes commit to

`encode W s = frame W ++ payload`, with

```
frame W = "DREGG/STORE"  (11 bytes, UTF-8)
       ++ [1]            (store-encoding version)
       ++ layoutDigest W (32 bytes)
layoutDigest W = cSHAKE256(customization "DREGG.STORE.LAYOUT/v1", descriptor W)
descriptor W   = bytes(name)
              ++ nat(count of W.namespaces)
              ++ for each namespace, in W.namespaces order:
                   bytes(namespace tag bytes) ++ [discipline byte]
                   ++ bytes(key codec id) ++ bytes(value codec id)
```

(`bytes(x)` is the length-prefixed `bytesStream`, `nat` the base-255 natural,
the discipline byte `rom = 0, ram = 1, appendOnly = 2`; the whole descriptor is
one `layoutDescriptorStream` encoding, so it is prefix-free and injective in
the description, `descriptor_injective`.)  The frame therefore commits to the
encoding version and to the LAYOUT: its name, every namespace's wire tag, its
mutation discipline, and the declared identities of its key and value codecs.
It commits to no capacity and no shard modulus, because neither exists.  A
cell written under one layout is refused under another whose digest differs
(`decode_other_layout`), so a layout change is a refusal, never a
reinterpretation.  The namespace list must be complete (`namespaces_complete`),
so no namespace escapes the descriptor.  What the descriptor cannot see is the
body of a codec function: two codecs declared under the same id are the same
layout as far as the frame knows.  The id is the pin; changing a codec means
changing its id.  Distinct descriptors give distinct digests only up to a
cSHAKE256 collision; that is the frame's one cryptographic premise.

The cell root is `cSHAKE256("DREGG.STORE.ROOT/v1", encode W s)`.  Because the
hashed bytes begin with the layout digest, roots of different layouts are
domain-separated by the frame; a per-kind root customization would pin the
same fact twice.

This file proves round-trip, injectivity and canonicity GENERALLY, for every
layout and every store; the worked instances at the end are evaluated
witnesses, not the proofs.
-/
import Compiler.FiniteDependentMapCodec
import Compiler.Sp800185Cshake256
import Kernel.SparseAuthenticatedState
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort

namespace Minidregg.Compiler.StoreCodec

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.SparseAuthenticatedState
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Prefix codecs are injective -/

theorem streamEncode_injective {α : Type} (codec : StreamCodec α) :
    Function.Injective codec.encode := by
  intro left right same
  have decoded := codec.decodePrefix_encode left []
  rw [same, codec.decodePrefix_encode right []] at decoded
  exact (Prod.mk.inj (Option.some.inj decoded)).1.symm

/-! ## The wire description of a layout -/

/-- The codecs that put one layout on the wire, and the declared identities
the frame commits to.  Once `Theory.Store.Layout` carries its own key and
value streams, this structure is a projection of the layout. -/
structure Wire (L : Layout.{0, 0, 0}) where
  name : String
  namespaces : List L.Namespace
  namespaces_complete : ∀ space, space ∈ namespaces
  namespaceStream : StreamCodec L.Namespace
  keyStream : (space : L.Namespace) → StreamCodec (L.Key space)
  valueStream : (space : L.Namespace) → StreamCodec (L.Value space)
  keyCodecId : L.Namespace → String
  valueCodecId : L.Namespace → String

/-- One store entry: an address and a present value at that address. -/
abbrev Entry (L : Layout.{0, 0, 0}) := Σ address : Address L, L.Value address.1

section Wire

variable {L : Layout.{0, 0, 0}} (W : Wire L)

def disciplineByte : Discipline → UInt8
  | .rom => 0
  | .ram => 1
  | .appendOnly => 2

abbrev NamespaceDescriptor := List UInt8 × UInt8 × List UInt8 × List UInt8
abbrev LayoutDescriptor := List UInt8 × List NamespaceDescriptor

def layoutDescriptorStream : StreamCodec LayoutDescriptor :=
  StreamCodec.product bytesStream
    (StreamCodec.list (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.byte
        (StreamCodec.product bytesStream bytesStream))))

def namespaceDescriptor (space : L.Namespace) : NamespaceDescriptor :=
  (W.namespaceStream.encode space, disciplineByte (L.discipline space),
    (W.keyCodecId space).toUTF8.toList, (W.valueCodecId space).toUTF8.toList)

def layoutDescriptor : LayoutDescriptor :=
  (W.name.toUTF8.toList, W.namespaces.map (namespaceDescriptor W))

def descriptor : List UInt8 :=
  layoutDescriptorStream.encode (layoutDescriptor W)

/-- Descriptor bytes determine the first-order description exactly. -/
theorem descriptor_injective {L' : Layout.{0, 0, 0}} (W' : Wire L')
    (same : descriptor W = descriptor W') : layoutDescriptor W = layoutDescriptor W' :=
  streamEncode_injective layoutDescriptorStream same

def layoutCustomization : List UInt8 := "DREGG.STORE.LAYOUT/v1".toUTF8.toList

def layoutDigest : List UInt8 :=
  (Sp800185Cshake256.hash layoutCustomization (descriptor W)).bytes

theorem layoutDigest_length : (layoutDigest W).length = 32 :=
  (Sp800185Cshake256.hash layoutCustomization (descriptor W)).length_exact

/-- `"DREGG/STORE"` in UTF-8. -/
def magic : List UInt8 := [68, 82, 69, 71, 71, 47, 83, 84, 79, 82, 69]

def storeVersion : UInt8 := 1

def frame : List UInt8 := magic ++ storeVersion :: layoutDigest W

theorem magic_length : magic.length = 11 := rfl

theorem frame_length : (frame W).length = 44 := by
  simp [frame, magic_length, layoutDigest_length]

/-! ## Addresses and their byte order -/

def addressStream : StreamCodec (Address L) :=
  FiniteDependentMapCodec.entryStream W.namespaceStream W.keyStream

def entryStream : StreamCodec (Entry L) :=
  FiniteDependentMapCodec.entryStream (addressStream W)
    (fun address => W.valueStream address.1)

def entryListStream : StreamCodec (List (Entry L)) :=
  StreamCodec.list (entryStream W)

/-- The comparison key of an address: its canonical bytes. -/
def addressKey (address : Address L) : List Nat :=
  ((addressStream W).encode address).map UInt8.toNat

theorem addressKey_injective : Function.Injective (addressKey W) := by
  intro left right same
  apply streamEncode_injective (addressStream W)
  exact (List.map_injective_iff.mpr (fun _ _ h => UInt8.toNat_inj.mp h)) same

/-- Byte order on addresses, pulled back along the injective address codec. -/
@[reducible] def addressOrder : LinearOrder (Address L) :=
  LinearOrder.lift' (addressKey W) (addressKey_injective W)

/-- Strict byte order of two entries' addresses. -/
def AddressLT (left right : Entry L) : Prop :=
  addressKey W left.1 < addressKey W right.1

instance (left right : Entry L) : Decidable (AddressLT W left right) := by
  unfold AddressLT
  infer_instance

end Wire

/-! ## Sorted support and reconstruction -/

section Store

variable {L : Layout.{0, 0, 0}} (W : Wire L)
  [DecidableEq L.Namespace] [∀ space, DecidableEq (L.Key space)]
  [∀ space, DecidableEq (L.Value space)]

instance : DecidableEq (Store L) := fun left right =>
  decidable_of_iff (left.entries = right.entries) (by
    cases left; cases right; simp)

/-- The support of a store in canonical address-byte order. -/
def sortedSupport (store : Store L) : List (Address L) :=
  letI := addressOrder W
  store.entries.support.sort (· ≤ ·)

/-- The entries of a store in canonical order.  Every supported address has a
present value, so `filterMap` drops nothing (`entries_map`). -/
def entries (store : Store L) : List (Entry L) :=
  (sortedSupport W store).filterMap fun address =>
    (store.entries address).map fun value => ⟨address, value⟩

/-- An entry as a sparse-map coordinate. -/
def Entry.toCoordinate (entry : Entry L) : Σ address : Address L, Option (L.Value address.1) :=
  ⟨entry.1, some entry.2⟩

/-- Reconstruction from any entry list; the first occurrence of an address wins.
Canonical decoding never relies on that choice, since it re-encodes. -/
def fromEntries (entryList : List (Entry L)) : Store L :=
  ⟨FiniteDependentMapCodec.fromEntries (entryList.map Entry.toCoordinate)⟩

omit [∀ space, DecidableEq (L.Value space)] in
theorem fromEntries_cons (entry : Entry L) (entryList : List (Entry L)) :
    (fromEntries (entry :: entryList)).entries =
      (fromEntries entryList).entries.update entry.1 (some entry.2) :=
  rfl

omit [∀ space, DecidableEq (L.Value space)] in
theorem fromEntries_apply_eq_none_iff (entryList : List (Entry L)) (address : Address L) :
    (fromEntries entryList).entries address = none ↔
      address ∉ entryList.map Sigma.fst := by
  induction entryList with
  | nil => simp [fromEntries, FiniteDependentMapCodec.fromEntries]; rfl
  | cons entry rest induction =>
      rw [fromEntries_cons, DFinsupp.coe_update]
      by_cases same : address = entry.1
      · subst same
        simp
      · rw [Function.update_of_ne same, induction]
        simp [same]

omit [∀ space, DecidableEq (L.Value space)] in
theorem fromEntries_apply_of_mem (entryList : List (Entry L))
    (distinct : (entryList.map Sigma.fst).Nodup) {entry : Entry L}
    (member : entry ∈ entryList) :
    (fromEntries entryList).entries entry.1 = some entry.2 := by
  induction entryList with
  | nil => cases member
  | cons head rest induction =>
      rw [fromEntries_cons, DFinsupp.coe_update]
      rw [List.map_cons, List.nodup_cons] at distinct
      rcases List.mem_cons.mp member with same | inRest
      · subst same
        simp
      · have different : entry.1 ≠ head.1 := by
          intro equal
          exact distinct.1 (equal ▸ List.mem_map_of_mem inRest)
        rw [Function.update_of_ne different]
        exact induction distinct.2 inRest

omit [DecidableEq L.Namespace] [∀ space, DecidableEq (L.Key space)]
  [∀ space, DecidableEq (L.Value space)] in
private theorem filterMap_present (store : Store L) (addresses : List (Address L))
    (present : ∀ address ∈ addresses, store.entries address ≠ none) :
    (addresses.filterMap fun address =>
        (store.entries address).map fun value => (⟨address, value⟩ : Entry L)).map
          Entry.toCoordinate =
      addresses.map fun address => ⟨address, store.entries address⟩ := by
  induction addresses with
  | nil => rfl
  | cons head rest induction =>
      have tail := induction (fun address member => present address (by simp [member]))
      cases found : store.entries head with
      | none => exact absurd found (present head (by simp))
      | some value =>
          simp only [List.filterMap_cons, found, Option.map_some, List.map_cons, tail]
          rfl

theorem mem_sortedSupport (store : Store L) (address : Address L) :
    address ∈ sortedSupport W store ↔ store.entries address ≠ none := by
  unfold sortedSupport
  rw [Finset.mem_sort, DFinsupp.mem_support_toFun]
  rfl

theorem entries_map (store : Store L) :
    (entries W store).map Entry.toCoordinate =
      (sortedSupport W store).map fun address => ⟨address, store.entries address⟩ :=
  filterMap_present store _ fun address member =>
    (mem_sortedSupport W store address).mp member

theorem fromEntries_entries (store : Store L) : fromEntries (entries W store) = store := by
  cases store with
  | mk map =>
      unfold fromEntries
      congr 1
      rw [entries_map]
      apply DFinsupp.ext
      intro address
      rw [FiniteDependentMapCodec.fromEntries_map]
      split_ifs with member
      · rfl
      · have absent := (mem_sortedSupport W ⟨map⟩ address).not.mp member
        exact (not_not.mp absent).symm

/-! ## Canonical order of `entries` -/

theorem sortedSupport_pairwise (store : Store L) :
    (sortedSupport W store).Pairwise fun left right =>
      addressKey W left < addressKey W right := by
  letI := addressOrder W
  have ordered := Finset.pairwise_sort store.entries.support (· ≤ ·)
  have distinct := Finset.sort_nodup store.entries.support (· ≤ ·)
  exact (ordered.and distinct).imp fun both =>
    lt_of_le_of_ne (show addressKey W _ ≤ addressKey W _ from both.1)
      ((addressKey_injective W).ne both.2)

theorem entries_pairwise (store : Store L) : (entries W store).Pairwise (AddressLT W) := by
  unfold entries
  rw [List.pairwise_filterMap]
  refine (sortedSupport_pairwise W store).imp ?_
  intro left right less first firstMember second secondMember
  rw [Option.map_eq_some_iff] at firstMember secondMember
  obtain ⟨_, _, rfl⟩ := firstMember
  obtain ⟨_, _, rfl⟩ := secondMember
  all_goals exact less

theorem entries_keys (store : Store L) :
    (entries W store).map Sigma.fst = sortedSupport W store := by
  have mapped := congrArg (List.map Sigma.fst) (entries_map W store)
  simpa [List.map_map, Function.comp_def, Entry.toCoordinate] using mapped

private theorem filterMap_eq_self {α : Type} (select : α → Option α) :
    ∀ (values : List α), (∀ value ∈ values, select value = some value) →
      values.filterMap select = values
  | [], _ => rfl
  | head :: rest, fixed => by
      rw [List.filterMap_cons_some (fixed head (by simp)),
        filterMap_eq_self select rest (fun value member => fixed value (by simp [member]))]

/-- The exact converse: a strictly byte-ordered entry list is the canonical
entry list of the store it denotes. -/
theorem entries_fromEntries_of_pairwise (entryList : List (Entry L))
    (ordered : entryList.Pairwise (AddressLT W)) :
    entries W (fromEntries entryList) = entryList := by
  letI := addressOrder W
  have keysOrdered : (entryList.map Sigma.fst).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact ordered
  have distinct : (entryList.map Sigma.fst).Nodup :=
    keysOrdered.imp fun less => ne_of_lt less
  have supportOrdered : (sortedSupport W (fromEntries entryList)).Pairwise (· < ·) :=
    sortedSupport_pairwise W _
  have sameKeys : sortedSupport W (fromEntries entryList) = entryList.map Sigma.fst := by
    apply supportOrdered.eq_of_mem_iff keysOrdered
    intro address
    rw [mem_sortedSupport, Ne, fromEntries_apply_eq_none_iff, not_not]
  have values : ∀ entry ∈ entryList,
      ((fromEntries entryList).entries entry.1).map (fun value => (⟨entry.1, value⟩ : Entry L)) =
        some entry := by
    intro entry member
    rw [fromEntries_apply_of_mem entryList distinct member]
    rfl
  unfold entries
  rw [sameKeys, List.filterMap_map]
  exact filterMap_eq_self _ entryList values

theorem entries_fromEntries_eq_iff (entryList : List (Entry L)) :
    entries W (fromEntries entryList) = entryList ↔ entryList.Pairwise (AddressLT W) := by
  constructor
  · intro same
    rw [← same]
    exact entries_pairwise W _
  · exact entries_fromEntries_of_pairwise W entryList

/-! ## Payload codec and canonical decoding -/

def payloadStream : StreamCodec (Store L) :=
  StreamCodec.xmap (entryListStream W) (entries W) fromEntries (fromEntries_entries W)

/-- Canonical payload decoding: lax decode, then exact re-encoding. -/
def decodePayload (payload : List UInt8) : Option (Store L) := do
  let store ← (payloadStream W).toLawful.decode payload
  if (payloadStream W).encode store = payload then some store else none

theorem decodePayload_encode (store : Store L) :
    decodePayload W ((payloadStream W).encode store) = some store := by
  have lax := (payloadStream W).toLawful.decode_encode store
  change (payloadStream W).toLawful.decode ((payloadStream W).encode store) = some store at lax
  simp [decodePayload, lax]

theorem decodePayload_eq_some_iff (payload : List UInt8) (store : Store L) :
    decodePayload W payload = some store ↔ (payloadStream W).encode store = payload := by
  constructor
  · intro accepted
    unfold decodePayload at accepted
    cases lax : (payloadStream W).toLawful.decode payload with
    | none => simp [lax] at accepted
    | some decoded =>
        simp only [lax, Option.bind_eq_bind, Option.bind_some] at accepted
        split at accepted
        · rename_i exact
          cases Option.some.inj accepted
          exact exact
        · cases accepted
  · intro exact
    rw [← exact]
    exact decodePayload_encode W store

/-- The lax reading of a raw entry list is the store it denotes. -/
theorem lax_entryList (entryList : List (Entry L)) :
    (payloadStream W).toLawful.decode ((entryListStream W).encode entryList) =
      some (fromEntries entryList) := by
  have parsed := (entryListStream W).decodePrefix_encode entryList []
  simp only [List.append_nil] at parsed
  simp [StreamCodec.toLawful, payloadStream, StreamCodec.xmap, parsed]

/-- Exact acceptance law for every raw entry list: accepted iff it is the
canonical list of the store it denotes. -/
theorem decodePayload_list_eq_none_iff (entryList : List (Entry L)) :
    decodePayload W ((entryListStream W).encode entryList) = none ↔
      entries W (fromEntries entryList) ≠ entryList := by
  have reencode : (payloadStream W).encode (fromEntries entryList) =
      (entryListStream W).encode (entries W (fromEntries entryList)) := rfl
  simp only [decodePayload, lax_entryList, Option.bind_eq_bind, Option.bind_some, reencode]
  constructor
  · intro refused same
    rw [same] at refused
    simp at refused
  · intro different
    rw [if_neg]
    intro same
    exact different (streamEncode_injective (entryListStream W) same)

/-- **Canonicity, structurally.**  A raw entry list is accepted exactly when
its addresses are strictly increasing in byte order. -/
theorem decodePayload_list_eq_some_iff (entryList : List (Entry L)) :
    decodePayload W ((entryListStream W).encode entryList) = some (fromEntries entryList) ↔
      entryList.Pairwise (AddressLT W) := by
  rw [← entries_fromEntries_eq_iff]
  constructor
  · intro accepted
    by_contra different
    rw [(decodePayload_list_eq_none_iff W entryList).mpr different] at accepted
    cases accepted
  · intro canonical
    have encoded : (entryListStream W).encode entryList =
        (payloadStream W).encode (fromEntries entryList) := by
      change _ = (entryListStream W).encode (entries W (fromEntries entryList))
      rw [canonical]
    rw [encoded]
    exact decodePayload_encode W _

/-- **Refuted misuse.**  An entry list out of address-byte order (including a
repeated address) is refused, whatever its entries are. -/
theorem decodePayload_rejects_unordered (entryList : List (Entry L))
    (unordered : ¬ entryList.Pairwise (AddressLT W)) :
    decodePayload W ((entryListStream W).encode entryList) = none := by
  rw [decodePayload_list_eq_none_iff, Ne, entries_fromEntries_eq_iff]
  exact unordered

/-! ## The framed cell codec -/

def encode (store : Store L) : List UInt8 :=
  frame W ++ (payloadStream W).encode store

def decode (bytes : List UInt8) : Option (Store L) :=
  if bytes.take (frame W).length = frame W then
    decodePayload W (bytes.drop (frame W).length)
  else none

theorem decode_frame_append (payload : List UInt8) :
    decode W (frame W ++ payload) = decodePayload W payload := by
  simp [decode]

theorem decode_encode (store : Store L) : decode W (encode W store) = some store := by
  rw [encode, decode_frame_append, decodePayload_encode]

/-- **Canonicity.**  The accepted byte strings are exactly the encodings: each
accepted string re-encodes to itself and denotes one store. -/
theorem decode_eq_some_iff (bytes : List UInt8) (store : Store L) :
    decode W bytes = some store ↔ encode W store = bytes := by
  constructor
  · intro accepted
    unfold decode at accepted
    split at accepted
    · rename_i framed
      have payload := (decodePayload_eq_some_iff W _ store).mp accepted
      calc encode W store = bytes.take (frame W).length ++ bytes.drop (frame W).length := by
            rw [encode, payload, framed]
        _ = bytes := List.take_append_drop _ _
    · cases accepted
  · intro exact
    rw [← exact]
    exact decode_encode W store

theorem decode_reencodes {bytes : List UInt8} {store : Store L}
    (accepted : decode W bytes = some store) : encode W store = bytes :=
  (decode_eq_some_iff W bytes store).mp accepted

theorem encode_injective : Function.Injective (encode W) := by
  intro left right same
  have decoded := congrArg (decode W) same
  rwa [decode_encode, decode_encode, Option.some.injEq] at decoded

/-- One store, one byte string: two accepted strings denoting the same store
are equal. -/
theorem accepted_bytes_unique {first second : List UInt8} {store : Store L}
    (acceptedFirst : decode W first = some store)
    (acceptedSecond : decode W second = some store) : first = second :=
  (decode_reencodes W acceptedFirst).symm.trans (decode_reencodes W acceptedSecond)

theorem decode_rejects_unordered (entryList : List (Entry L))
    (unordered : ¬ entryList.Pairwise (AddressLT W)) :
    decode W (frame W ++ (entryListStream W).encode entryList) = none := by
  rw [decode_frame_append]
  exact decodePayload_rejects_unordered W entryList unordered

/-- Any header other than this layout's frame is refused, so a cell of a
layout with a different digest never decodes here. -/
theorem decode_other_header (header payload : List UInt8)
    (sameLength : header.length = (frame W).length) (different : header ≠ frame W) :
    decode W (header ++ payload) = none := by
  simp [decode, ← sameLength, different]

theorem decode_other_version (version : UInt8) (digest payload : List UInt8)
    (digestLength : digest.length = 32) (otherVersion : version ≠ storeVersion) :
    decode W (magic ++ version :: digest ++ payload) = none := by
  have header := decode_other_header W (magic ++ version :: digest) payload
    (by simp [frame_length, magic_length, digestLength])
    (by simp [frame, otherVersion])
  simpa using header

theorem decode_other_layout {L' : Layout.{0, 0, 0}} [DecidableEq L'.Namespace]
    [∀ space, DecidableEq (L'.Key space)] [∀ space, DecidableEq (L'.Value space)]
    (W' : Wire L') (store : Store L')
    (otherLayout : layoutDigest W' ≠ layoutDigest W) :
    decode W (encode W' store) = none := by
  apply decode_other_header W (frame W')
  · rw [frame_length, frame_length]
  · simp [frame, otherLayout]

/-! ## Root and materializer -/

def rootCustomization : List UInt8 := "DREGG.STORE.ROOT/v1".toUTF8.toList

def rootBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash rootCustomization bytes).digest

def codec : LawfulCodec (Store L) where
  encode := encode W
  decode := decode W
  decode_encode := decode_encode W

def materializer : Materializer L Digest where
  codec := codec W
  rootBytes := rootBytes

end Store

/-! ## Worked instance: a two-namespace layout -/

namespace Worked

inductive Space
  | field
  | label
  deriving DecidableEq, Repr

def Space.Value : Space → Type
  | .field => Nat
  | .label => List UInt8

def layout : Layout.{0, 0, 0} where
  Namespace := Space
  Key := fun _ => Nat
  Value := Space.Value
  discipline
    | .field => .ram
    | .label => .appendOnly

instance : DecidableEq layout.Namespace := inferInstanceAs (DecidableEq Space)

instance (space : layout.Namespace) : DecidableEq (layout.Key space) :=
  inferInstanceAs (DecidableEq Nat)

instance (space : layout.Namespace) : DecidableEq (layout.Value space) := by
  cases space
  · exact inferInstanceAs (DecidableEq Nat)
  · exact inferInstanceAs (DecidableEq (List UInt8))

def spaceStream : StreamCodec Space where
  encode
    | .field => [0]
    | .label => [1]
  decodePrefix
    | 0 :: suffix => some (.field, suffix)
    | 1 :: suffix => some (.label, suffix)
    | _ => none
  decodePrefix_encode := by intro space suffix; cases space <;> rfl

def valueStream : (space : Space) → StreamCodec (Space.Value space)
  | .field => StreamCodec.nat
  | .label => bytesStream

def wire : Wire layout where
  name := "example/v1"
  namespaces := [.field, .label]
  namespaces_complete := by intro space; cases space <;> simp
  namespaceStream := spaceStream
  keyStream := fun _ => StreamCodec.nat
  valueStream := valueStream
  keyCodecId := fun _ => "nat/base255"
  valueCodecId
    | .field => "nat/base255"
    | .label => "bytes/length-prefixed"

def fieldEntry (key value : Nat) : Entry layout :=
  ⟨⟨Space.field, key⟩, (value : Nat)⟩

def labelEntry (key : Nat) (value : List UInt8) : Entry layout :=
  ⟨⟨Space.label, key⟩, value⟩

/-- Byte order is not numeric order: key `0` is written as the lone terminator
`255`, so it sorts after every key whose first digit is below `255`. -/
theorem zero_key_sorts_after_one : AddressLT wire (fieldEntry 1 0) (fieldEntry 0 0) := by
  decide +kernel

/-- A resource with 32 present fields, keys `1 … 32`, listed in canonical
(address-byte) order. -/
def fields32 : List (Entry layout) :=
  (List.range 32).map fun index => fieldEntry (index + 1) (1000 + index)

def store32 : Store layout := fromEntries fields32

theorem store32_support_card : store32.entries.support.card = 32 := by
  decide +kernel

/-! ### What the kernel evaluates, and what only the compiler reaches

`Finset.sort` is Mathlib's `List.mergeSort`, which is well-founded recursion;
the kernel does not reduce it (measured: `decide +kernel` refuses
`[3,1,2].mergeSort = [1,2,3]` and the same for `Finset.sort`, while the
structurally recursive `insertionSort` reduces).  The encoder keeps merge sort
because it is the production path and an insertion sort would make every
1000-record write quadratic.  So the kernel-checked 32-field instance goes
through the general canonical-order theorem: the only evaluated fact is the
canonicity condition itself (the 32 addresses are strictly increasing in
bytes), and the encoder's output bytes FOLLOW from it
(`store32_encode_eq`).  The compiled encoder and decoder are then run
end to end by `native_decide` (`store32_compiled_roundtrip`,
`store1000_compiled_roundtrip`); those two are confessed by the `_native`
axiom their `#print axioms` pin shows, and nothing general depends on them. -/

theorem fields32_ordered : fields32.Pairwise (AddressLT wire) := by
  decide +kernel

/-- The 32 literal entries are exactly the canonical entry list of `store32`. -/
theorem store32_entries : entries wire store32 = fields32 :=
  entries_fromEntries_of_pairwise wire fields32 fields32_ordered

/-- The encoder's bytes for the 32-field store, without evaluating the sort. -/
theorem store32_encode_eq :
    (payloadStream wire).encode store32 = (entryListStream wire).encode fields32 := by
  change (entryListStream wire).encode (entries wire store32) = _
  rw [store32_entries]

/-- Wire-size pin: count `[32, 255]`, then six bytes per field: namespace tag,
one key digit and terminator, two value digits (`1000 + i` in base 255) and
terminator. -/
theorem store32_payload_length : ((entryListStream wire).encode fields32).length = 194 := by
  decide +kernel

/-- The 32-field payload bytes are accepted and denote `store32`
(kernel-checked). -/
theorem store32_bytes_accepted :
    decodePayload wire ((entryListStream wire).encode fields32) = some store32 :=
  (decodePayload_list_eq_some_iff wire fields32).mpr fields32_ordered

/-- The framed round trip at 32 fields.  The frame's layout digest is a
cSHAKE256 output, which the kernel does not evaluate, so the frame is
discharged by `decode_frame_append`. -/
theorem store32_roundtrip :
    decode wire (frame wire ++ (entryListStream wire).encode fields32) = some store32 := by
  rw [decode_frame_append]
  exact store32_bytes_accepted

/-- CONFESSED `native_decide`: the compiled encoder, merge sort and canonical
decoder run end to end on the 32-field store. -/
theorem store32_compiled_roundtrip :
    decodePayload wire ((payloadStream wire).encode store32) = some store32 := by
  native_decide

def store1000 : Store layout :=
  fromEntries ((List.range 1000).map fun index => fieldEntry index (7 * index))

/-- CONFESSED `native_decide`: the compiled path at the journey's 1000-record
scale. -/
theorem store1000_compiled_roundtrip :
    decodePayload wire ((payloadStream wire).encode store1000) = some store1000 := by
  native_decide

/-- Satisfiable pole of canonical order: two entries across both namespaces in
address-byte order are accepted. -/
theorem ordered_pair_accepted :
    decode wire (frame wire ++ (entryListStream wire).encode
      [fieldEntry 3 30, labelEntry 1 [7]]) =
      some (fromEntries [fieldEntry 3 30, labelEntry 1 [7]]) := by
  rw [decode_frame_append, decodePayload_list_eq_some_iff]
  decide +kernel

/-- Refuted misuse: the same two entries in the other order are refused. -/
theorem swapped_pair_rejected :
    decode wire (frame wire ++ (entryListStream wire).encode
      [labelEntry 1 [7], fieldEntry 3 30]) = none := by
  apply decode_rejects_unordered
  decide +kernel

/-- Refuted misuse: a repeated address is refused even with equal values. -/
theorem duplicate_address_rejected :
    decode wire (frame wire ++ (entryListStream wire).encode
      [fieldEntry 3 30, fieldEntry 3 30]) = none := by
  apply decode_rejects_unordered
  decide +kernel

/-- Refuted misuse: a non-minimal natural (`3` written as digits `3, 0`) is
read by the lax decoder but refused by re-encoding. -/
theorem noncanonical_value_bytes_rejected :
    decode wire (frame wire ++ [1, 255, 0, 3, 255, 3, 0, 255]) = none := by
  rw [decode_frame_append]
  decide +kernel

theorem noncanonical_value_bytes_lax :
    (payloadStream wire).toLawful.decode [1, 255, 0, 3, 255, 3, 0, 255] =
      some (fromEntries [fieldEntry 3 3]) := by
  decide +kernel

end Worked

/-! ## Unbounded capacity (DATAMODEL §4.12) -/

section Capacity

open Worked

def storeOfSize (size : Nat) : Store layout :=
  fromEntries ((List.range size).map fun index => fieldEntry index index)

theorem storeOfSize_card (size : Nat) : (storeOfSize size).entries.support.card = size := by
  have keys : ((List.range size).map fun index => fieldEntry index index).map Sigma.fst =
      (List.range size).map fun index => (⟨Space.field, index⟩ : Address layout) := by
    rw [List.map_map]
    rfl
  have support : (storeOfSize size).entries.support =
      ((List.range size).map fun index => (⟨Space.field, index⟩ : Address layout)).toFinset := by
    ext address
    rw [DFinsupp.mem_support_toFun, List.mem_toFinset, ← keys]
    exact (fromEntries_apply_eq_none_iff _ address).not.trans not_not
  rw [support, List.toFinset_card_of_nodup]
  · rw [List.length_map]
    exact List.length_range
  · apply List.Nodup.map
    · intro left right same
      simpa using same
    · exact List.nodup_range

/-- Theorem 4.12: for every size there is a store of exactly that many present
addresses, and it round-trips through the framed codec. -/
theorem capacity_unbounded (size : Nat) :
    ∃ store : Store layout, store.entries.support.card = size ∧
      decode wire (encode wire store) = some store :=
  ⟨storeOfSize size, storeOfSize_card size, decode_encode wire _⟩

theorem capacity_32 : ∃ store : Store layout, store.entries.support.card = 32 ∧
    decode wire (encode wire store) = some store :=
  capacity_unbounded 32

theorem capacity_1000 : ∃ store : Store layout, store.entries.support.card = 1000 ∧
    decode wire (encode wire store) = some store :=
  capacity_unbounded 1000

end Capacity

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.StoreCodec.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_encode
/-- info: 'Minidregg.Compiler.StoreCodec.decode_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_eq_some_iff
/-- info: 'Minidregg.Compiler.StoreCodec.encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encode_injective
/-- info: 'Minidregg.Compiler.StoreCodec.accepted_bytes_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_bytes_unique
/-- info: 'Minidregg.Compiler.StoreCodec.decodePayload_list_eq_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodePayload_list_eq_some_iff
/-- info: 'Minidregg.Compiler.StoreCodec.decode_rejects_unordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_rejects_unordered
/-- info: 'Minidregg.Compiler.StoreCodec.decode_other_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_other_layout
/-- info: 'Minidregg.Compiler.StoreCodec.decode_other_version' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decode_other_version
/-- info: 'Minidregg.Compiler.StoreCodec.capacity_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms capacity_unbounded
/-- info: 'Minidregg.Compiler.StoreCodec.Worked.store32_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Worked.store32_roundtrip
/-- info: 'Minidregg.Compiler.StoreCodec.Worked.store32_encode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Worked.store32_encode_eq
/-- info: 'Minidregg.Compiler.StoreCodec.Worked.store32_compiled_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound,
  Worked.store32_compiled_roundtrip._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms Worked.store32_compiled_roundtrip
/-- info: 'Minidregg.Compiler.StoreCodec.Worked.store1000_compiled_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound,
  Worked.store1000_compiled_roundtrip._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms Worked.store1000_compiled_roundtrip
/-- info: 'Minidregg.Compiler.StoreCodec.Worked.swapped_pair_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Worked.swapped_pair_rejected
/-- info: 'Minidregg.Compiler.StoreCodec.Worked.noncanonical_value_bytes_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Worked.noncanonical_value_bytes_rejected

end Minidregg.Compiler.StoreCodec
