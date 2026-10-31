/-
# Compiler.PrivateCellRoot — the private root of a store wire, and its materializer

The private cell root, over any `StoreCodec.Wire`, below the cell registry so a cell module can
select it (docs/PRIVATE-CELLS-STATE.md, FORMAT (a)). A store's private index is the
`Theory.AuthTrie` over its index entries (`Compiler.PrivateCellIndex.indexEntries`: every live
address but the blinding, each value as its value bytes), keyed by a 260-bit class tag followed
by 256 bits of cSHAKE256 of the address's canonical bytes (`paths`). Each node is hashed by
cSHAKE256 over the bytes of its path-keyed image (`deployedDig = pathDig ∘ nodeImage`): a leaf is
its 65 packed path bytes and its content digest (cSHAKE256 under `DREGG/PRIVATE-CELL/CONTENT/v1`
over the framed address bytes and value bytes), a fixed 98 bytes, so a reveal of the image never
carries a hidden value of unbounded size; `DigestCollision` / `deployedDig_collision`: two
distinct nodes with one digest are a cSHAKE256 collision on distinct node or content bytes. The root is one outer cSHAKE256 over the kind-level
context (`kindCtx`: the protocol version and the wire's frame), the blinding bytes (`maskOf`; `[]`
for an unblinded wire) and the index digest (`privateRoot`).

* `materializer W T`: the wire's store codec, rooted by `rootBytes` (the private root of the store
  the bytes denote), carrying `aux`: the kept index and blinding bytes. `materializer_rootOf`: the
  root of every store is its private root.
* `aux`: total (`keptBuild`, one bulk build over key-distinct entries); `set` at the blinding
  address replaces the held bytes and leaves the index, at any other address is one index walk
  (`indexStep`: an insert or an erase, `set_index`); the read is always present
  (`rootAvailable`), so a cell's root is never computed from its bytes.
* `untagged`: the class tag of a kind whose addresses carry no field (`ResourceObservationAdmission.fieldOf`
  is `none` on every address), the tag `Kernel.PrivateCellScope.bitCode 256` gives `none`.

Hiding is not claimed here: a blinded wire's narrowed readers are served by the salted ratchet
root until the zero-knowledge selective opening exists (FORMAT (b)); this module's materializer
is selected only by unblinded kinds.
-/
module

public import Compiler.PrivateCellIndex
public import Theory.AuthTrieErase
public import Theory.CellState
public import Kernel.WorldRoot
public import Compiler.Tower256ConcreteBackend
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Compiler.PrivateCellRoot

set_option autoImplicit false

open Minidregg.Compiler
open Minidregg.Compiler.StoreCodec
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.AuthTrie (NodeIn lastVal lastVal_snoc)
open Minidregg.Compiler.PrivateCellIndex (indexEntries valueBytes indexExact indexIgnoresBlinding)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec digestStream)

variable {L : Layout.{0, 0, 0}} (W : Wire L)

/-! ## Key paths and node digests -/

/-- The first `A` bits of a hash of the address's canonical bytes (`StoreCodec.addressStream`). -/
def hashedAddrBits (A : Nat) (hash : List UInt8 → List Bool) (address : Address L) : List Bool :=
  ((hash ((StoreCodec.addressStream W).encode address)) ++ List.replicate A false).take A

theorem hashedAddrBits_length (A : Nat) (hash : List UInt8 → List Bool) (address : Address L) :
    (hashedAddrBits W A hash address).length = A := by
  simp [hashedAddrBits]

/-- What a node digest hashes: a tag byte, then a leaf's canonical address bytes
and value bytes, or a branch's two child digests under `child`. -/
def nodeBytesWith {D : Type} (child : StreamCodec D) : NodeIn (Address L) (List UInt8) D → List UInt8
  | .empty => [2]
  | .leaf a v => 0 :: ((StoreCodec.addressStream W).encode a ++ v)
  | .branch l r => 1 :: (StreamCodec.product child child).encode (l, r)

theorem nodeBytesWith_injective {D : Type} (child : StreamCodec D) {a b : NodeIn (Address L) (List UInt8) D}
    (same : nodeBytesWith W child a = nodeBytesWith W child b) : a = b := by
  cases a with
  | empty => cases b <;> simp_all [nodeBytesWith]
  | leaf k v =>
      cases b with
      | empty => simp [nodeBytesWith] at same
      | branch _ _ => simp [nodeBytesWith] at same
      | leaf k' v' =>
          simp only [nodeBytesWith, List.cons.injEq, true_and] at same
          have decoded := (StoreCodec.addressStream W).decodePrefix_encode k v
          rw [same, (StoreCodec.addressStream W).decodePrefix_encode k' v'] at decoded
          have := (Prod.mk.inj (Option.some.inj decoded))
          rw [this.1, this.2]
  | branch l r =>
      cases b with
      | empty => simp [nodeBytesWith] at same
      | leaf _ _ => simp [nodeBytesWith] at same
      | branch l' r' =>
          simp only [nodeBytesWith, List.cons.injEq, true_and] at same
          have decoded := (StreamCodec.product child child).decodePrefix_encode (l, r) []
          rw [same, (StreamCodec.product child child).decodePrefix_encode (l', r') []] at decoded
          have := (Prod.mk.inj (Option.some.inj decoded)).1
          simp only [Prod.mk.injEq] at this
          rw [this.1, this.2]

def addressCustomization : List UInt8 := "DREGG/PRIVATE-CELL/ADDRESS/v1".toUTF8.toList
def nodeCustomization : List UInt8 := "DREGG/PRIVATE-CELL/NODE/v1".toUTF8.toList
def outerCustomization : List UInt8 := "DREGG/PRIVATE-CELL/OUTER/v1".toUTF8.toList

/-- The address hash: the 256 bits of cSHAKE256 over the bytes. -/
def addressHash (bytes : List UInt8) : List Bool :=
  Kernel.WorldRoot.bytesBits (Sp800185Cshake256.hash addressCustomization bytes).bytes

theorem addressHash_length (bytes : List UInt8) : (addressHash bytes).length = 256 := by
  simp [addressHash, Kernel.WorldRoot.bytesBits_length, (Sp800185Cshake256.hash _ _).length_exact]

/-- A 260-bit class tag per address (the reader's visibility class). -/
structure KeyTag (L : Layout.{0, 0, 0}) where
  tag : Address L → List Bool
  length : ∀ a, (tag a).length = 260

/-- The class bits of an address with no field: `bitCode 256`'s tag of `none`
(`Kernel.PrivateCellView.untagged_eq`). -/
def untaggedClass : List Bool := [true, false, true] ++ false :: List.replicate 256 false

/-- The tag of a kind whose addresses carry no field. -/
theorem untaggedClass_length : untaggedClass.length = 260 := by
  simp only [untaggedClass, List.length_append, List.length_cons, List.length_replicate, List.length_nil]

def untagged (L : Layout.{0, 0, 0}) : KeyTag L := ⟨fun _ => untaggedClass, fun _ => untaggedClass_length⟩

variable (T : KeyTag L)

/-- The key path: the class tag, then the address's 256 hashed bits. -/
def paths (address : Address L) : List Bool := T.tag address ++ hashedAddrBits W 256 addressHash address

theorem paths_length (address : Address L) : (paths W T address).length = 516 := by
  simp [paths, T.length, hashedAddrBits_length]

/-! ## cSHAKE256 outputs -/

theorem output_eq {o₁ o₂ : Sp800185Cshake256.Output} (same : o₁.bytes = o₂.bytes) : o₁ = o₂ := by
  cases o₁; cases o₂; simp only at same; subst same; rfl

theorem output_eq_of_digest_eq {o₁ o₂ : Sp800185Cshake256.Output} (same : o₁.digest = o₂.digest) : o₁ = o₂ := by
  apply output_eq
  have bytesEq := congrArg Sp800185Cshake256.digestBytesLE same
  simp only [Sp800185Cshake256.Output.digest] at bytesEq
  rwa [Sp800185Cshake256.digestBytesLE_digestOfBytesLE _ o₁.length_exact,
    Sp800185Cshake256.digestBytesLE_digestOfBytesLE _ o₂.length_exact] at bytesEq

/-! ## Fixed-size leaves: the content digest and the path-keyed node bytes -/

def contentCustomization : List UInt8 := "DREGG/PRIVATE-CELL/CONTENT/v1".toUTF8.toList

/-- What a leaf's content digest hashes: the address's canonical bytes, length-framed, then the
value bytes. -/
def contentBytes (a : Address L) (v : List UInt8) : List UInt8 :=
  (StreamCodec.list StreamCodec.byte).encode ((StoreCodec.addressStream W).encode a) ++ v

theorem contentBytes_injective {a a' : Address L} {v v' : List UInt8}
    (same : contentBytes W a v = contentBytes W a' v') : a = a' ∧ v = v' := by
  unfold contentBytes at same
  have decoded := (StreamCodec.list StreamCodec.byte).decodePrefix_encode ((StoreCodec.addressStream W).encode a) v
  rw [same, (StreamCodec.list StreamCodec.byte).decodePrefix_encode] at decoded
  obtain ⟨bytes, rest⟩ := Prod.mk.inj (Option.some.inj decoded)
  exact ⟨(StoreCodec.streamEncode_injective _ bytes).symm, rest.symm⟩

/-- A leaf's content digest: cSHAKE256 under the content customization over its content bytes. -/
def contentDigest (a : Address L) (v : List UInt8) : Digest :=
  (Sp800185Cshake256.hash contentCustomization (contentBytes W a v)).digest

/-- Eight bits, most significant first, as one byte. -/
def packByte8 (bits : List Bool) : UInt8 :=
  UInt8.ofNat (bits.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0)

theorem byteBits_packByte8 : ∀ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Bool,
    Kernel.WorldRoot.byteBits (packByte8 [b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇]) = [b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇] := by
  decide

theorem byteBits_packByte8_of_length (l : List Bool) (h : l.length = 8) :
    Kernel.WorldRoot.byteBits (packByte8 l) = l := by
  match l, h with
  | [b₀, b₁, b₂, b₃, b₄, b₅, b₆, b₇], _ => exact byteBits_packByte8 b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h
    | [_, _, _, _, _, _], h | [_, _, _, _, _, _, _], h => exact absurd h (by simp)
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp only [List.length_cons] at h; omega

/-- `k` bytes, eight bits each. -/
def packN : Nat → List Bool → List UInt8
  | 0, _ => []
  | k + 1, bits => packByte8 (bits.take 8) :: packN k (bits.drop 8)

theorem bytesBits_packN : ∀ (k : Nat) (bits : List Bool), bits.length = 8 * k →
    Kernel.WorldRoot.bytesBits (packN k bits) = bits
  | 0, bits, len => by simp at len; subst len; rfl
  | k + 1, bits, len => by
      have head : (bits.take 8).length = 8 := by rw [List.length_take, len]; omega
      have tail : (bits.drop 8).length = 8 * k := by rw [List.length_drop, len]; omega
      show (packByte8 (bits.take 8) :: packN k (bits.drop 8)).flatMap Kernel.WorldRoot.byteBits = bits
      rw [List.flatMap_cons, byteBits_packByte8_of_length _ head]
      have rest := bytesBits_packN k (bits.drop 8) tail
      simp only [Kernel.WorldRoot.bytesBits] at rest
      rw [rest, List.take_append_drop]

/-- A 516-bit path as 65 bytes (four zero padding bits). -/
def packPath (p : List Bool) : List UInt8 := packN 65 (p ++ List.replicate 4 false)

theorem packN_length : ∀ (k : Nat) (bits : List Bool), (packN k bits).length = k
  | 0, _ => rfl
  | k + 1, bits => by simp [packN, packN_length k]

theorem packPath_length (p : List Bool) : (packPath p).length = 65 := packN_length 65 _

theorem packPath_injective {p q : List Bool} (hp : p.length = 516) (hq : q.length = 516)
    (same : packPath p = packPath q) : p = q := by
  have unpack : ∀ r : List Bool, r.length = 516 → Kernel.WorldRoot.bytesBits (packPath r) = r ++ List.replicate 4 false :=
    fun r len => bytesBits_packN 65 _ (by simp [len])
  have := unpack p hp
  rw [same, unpack q hq] at this
  exact (List.append_inj_left' this rfl).symm

/-- A key path of the private index: exactly 516 bits. -/
abbrev Path := {p : List Bool // p.length = 516}

/-- What a path-keyed node digest hashes: a tag byte, then a leaf's 65 packed path bytes and
its content digest (fixed size), or a branch's two child digests. -/
def pathNodeBytes : NodeIn Path Digest Digest → List UInt8
  | .empty => [2]
  | .leaf p d => 0 :: (packPath p.1 ++ digestStream.encode d)
  | .branch l r => 1 :: (StreamCodec.product digestStream digestStream).encode (l, r)

theorem pathNodeBytes_injective {x y : NodeIn Path Digest Digest} (same : pathNodeBytes x = pathNodeBytes y) :
    x = y := by
  cases x with
  | empty => cases y <;> simp_all [pathNodeBytes]
  | leaf p d =>
      cases y with
      | empty => simp [pathNodeBytes] at same
      | branch _ _ => simp [pathNodeBytes] at same
      | leaf p' d' =>
          simp only [pathNodeBytes, List.cons.injEq, true_and] at same
          obtain ⟨paths, digests⟩ := List.append_inj same (by rw [packPath_length, packPath_length])
          rw [Subtype.ext (packPath_injective p.2 p'.2 paths), StoreCodec.streamEncode_injective _ digests]
  | branch l r =>
      cases y with
      | empty => simp [pathNodeBytes] at same
      | leaf _ _ => simp [pathNodeBytes] at same
      | branch l' r' =>
          simp only [pathNodeBytes, List.cons.injEq, true_and] at same
          have := StoreCodec.streamEncode_injective _ same
          simp only [Prod.mk.injEq] at this
          rw [this.1, this.2]

/-- The path-keyed node digest: cSHAKE256 under the node customization over its bytes. -/
def pathDig (node : NodeIn Path Digest Digest) : Digest :=
  (Sp800185Cshake256.hash nodeCustomization (pathNodeBytes node)).digest

/-- An index node's image: its address replaced by its path, its value bytes by its content
digest. -/
def nodeImage : NodeIn (Address L) (List UInt8) Digest → NodeIn Path Digest Digest
  | .empty => .empty
  | .leaf a v => .leaf ⟨paths W T a, paths_length W T a⟩ (contentDigest W a v)
  | .branch l r => .branch l r

/-- **The deployed node digest**: the path-keyed digest of the node's image. Every leaf hashes a
fixed 98 bytes (tag, packed path, content digest), so an early-stop reveal carries no hidden
payload of unbounded size. -/
def deployedDig (node : NodeIn (Address L) (List UInt8) Digest) : Digest := pathDig (nodeImage W T node)

/-- **A collision of the deployed digest**, as a collision of cSHAKE256 on distinct inputs: two
distinct node byte strings under the node customization, or two leaves whose distinct content
bytes collide under the content customization. -/
def DigestCollision (x y : NodeIn (Address L) (List UInt8) Digest) : Prop :=
  (pathNodeBytes (nodeImage W T x) ≠ pathNodeBytes (nodeImage W T y) ∧
      Sp800185Cshake256.hash nodeCustomization (pathNodeBytes (nodeImage W T x)) =
        Sp800185Cshake256.hash nodeCustomization (pathNodeBytes (nodeImage W T y))) ∨
    ∃ a v a' v', x = .leaf a v ∧ y = .leaf a' v' ∧ contentBytes W a v ≠ contentBytes W a' v' ∧
      Sp800185Cshake256.hash contentCustomization (contentBytes W a v) =
        Sp800185Cshake256.hash contentCustomization (contentBytes W a' v')

/-- Two distinct index nodes with one deployed digest are a `DigestCollision`. -/
theorem deployedDig_collision {x y : NodeIn (Address L) (List UInt8) Digest} (ne : x ≠ y)
    (same : deployedDig W T x = deployedDig W T y) : DigestCollision W T x y := by
  by_cases bytes : pathNodeBytes (nodeImage W T x) = pathNodeBytes (nodeImage W T y)
  · right
    have images := pathNodeBytes_injective bytes
    cases x with
    | empty => cases y <;> simp_all [nodeImage]
    | branch l r => cases y <;> simp_all [nodeImage]
    | leaf a v =>
        cases y with
        | empty => simp [nodeImage] at images
        | branch _ _ => simp [nodeImage] at images
        | leaf a' v' =>
            simp only [nodeImage, NodeIn.leaf.injEq] at images
            refine ⟨a, v, a', v', rfl, rfl, fun content => ne ?_, output_eq_of_digest_eq images.2⟩
            obtain ⟨rfl, rfl⟩ := contentBytes_injective W content
            rfl
  · exact Or.inl ⟨bytes, output_eq_of_digest_eq same⟩

/-- A store's kept private index. -/
abbrev Index := Theory.AuthTrie.Cache (deployedDig W T) (paths W T) 516

/-! ## The root -/

/-- The outer commitment: cSHAKE256 over the context, the mask and the index digest. -/
def outerRoot (ctx mask : List UInt8) (inner : Digest) : Digest :=
  (Sp800185Cshake256.hash outerCustomization
    ((StreamCodec.product (StreamCodec.list StreamCodec.byte)
      (StreamCodec.product (StreamCodec.list StreamCodec.byte) digestStream)).encode (ctx, mask, inner))).digest

/-- The private-cell protocol version, bound into every kind's context. -/
def protocolVersion : Nat := 1

/-- **The kind-level context**: the protocol version and the wire's frame (magic, store version
and layout digest). A function of the wire alone. -/
def kindCtx : List UInt8 :=
  (StreamCodec.product StreamCodec.nat (StreamCodec.list StreamCodec.byte)).encode
    (protocolVersion, StoreCodec.frame W)

/-- The store's mask: its blinding value's bytes (none, and every unblinded wire: `[]`). -/
def maskOf (store : Store L) : List UInt8 :=
  (StoreCodec.blindingKey W store).getD []

/-- **The private root (specification)**: the outer commitment over the context, the mask and
the canonical root of the store's index, from the whole store. -/
def privateRoot (ctx : List UInt8) (store : Store L) : Digest :=
  outerRoot ctx (maskOf W store) (Theory.AuthTrie.root (deployedDig W T) (paths W T) 516 (indexEntries W store))

/-- The root of a wire's bytes: the private root of the store they denote at the wire's
context; bytes that do not decode are hashed under their own label. Irreducible for the
elaborator, as `StoreCodec.rootBytes` is, so no proof unfolds a concrete Keccak. -/
@[irreducible] def rootBytes (bytes : List UInt8) : Digest :=
  match (payloadStream W).toLawful.decode (bytes.drop 44) with
  | some store => privateRoot W T (kindCtx W) store
  | none => (Sp800185Cshake256.hash undecodableCustomization bytes).digest

theorem rootBytes_encode (store : Store L) :
    rootBytes W T (StoreCodec.encode W store) = privateRoot W T (kindCtx W) store := by
  have payload : (StoreCodec.encode W store).drop 44 = (payloadStream W).encode store := by
    rw [StoreCodec.encode, ← frame_length W, List.drop_left]
  have lax : (payloadStream W).toLawful.decode ((payloadStream W).encode store) = some store :=
    (payloadStream W).toLawful.decode_encode store
  unfold rootBytes
  rw [payload, lax]

/-! ## The carried structure -/

theorem lastVal_index_set_some (store : Store L) {a : Address L} (blind : ¬ some a = W.blinding)
    (x : L.Value a.1) (k : Address L) :
    lastVal (indexEntries W (store.set a (some x))) k =
      lastVal (indexEntries W store ++ [(a, valueBytes W a x)]) k := by
  rw [lastVal_snoc, indexExact, indexExact]
  by_cases same : a = k
  · subst same
    simp [blind]
  · have ne : k ≠ a := fun h => same h.symm
    simp only [same, if_false, Store.set_ne store a (some x) k ne]

theorem lastVal_index_set_none (store : Store L) {a : Address L} (blind : ¬ some a = W.blinding)
    (k : Address L) :
    lastVal (indexEntries W (store.set a none)) k =
      lastVal (Theory.AuthTrie.Trie.dropKey a (indexEntries W store)) k := by
  rw [Theory.AuthTrie.lastVal_dropKey, indexExact, indexExact]
  by_cases same : k = a
  · subst same
    simp
  · simp only [same, if_false, Store.set_ne store a none k same]

theorem maskOf_set_other {store : Store L} {a : Address L} (blind : ¬ some a = W.blinding)
    (v : Option (L.Value a.1)) : maskOf W (store.set a v) = maskOf W store := by
  unfold maskOf StoreCodec.blindingKey
  cases h : W.blinding with
  | none => rfl
  | some b =>
      have ne : b ≠ a := fun same => blind (by rw [h, same])
      simp [Store.set_ne store a v b ne]

/-- The blinding bytes after a write at the blinding address. -/
def maskAfter (a : Address L) (v : Option (L.Value a.1)) : List UInt8 :=
  (v.map (W.valueStream a.1).encode).getD []

theorem maskOf_set_blind {store : Store L} {a : Address L} (blind : some a = W.blinding)
    (v : Option (L.Value a.1)) : maskOf W (store.set a v) = maskAfter W a v := by
  unfold maskOf StoreCodec.blindingKey maskAfter
  rw [← blind]
  simp [Store.set]

theorem index_set_blind {store : Store L} {a : Address L} (blind : some a = W.blinding)
    (v : Option (L.Value a.1)) : indexEntries W (store.set a v) = indexEntries W store :=
  indexIgnoresBlinding W _ _ fun address other => by
    have : address ≠ a := fun same => other (same ▸ blind)
    simp [Store.set, this]

/-- The index after one data write: a function of the old index, one insert or one erase. -/
def indexStep (index : Index W T) (a : Address L) (v : Option (L.Value a.1)) : Index W T :=
  match v with
  | some x => index.insert (paths_length W T) a (valueBytes W a x)
  | none => index.erase a

/-- What a private cell carries: its index and its held blinding bytes. -/
structure Kept where
  index : Index W T
  mask : List UInt8

/-- The relation: the index holds the store's index entries, the bytes are its blinding bytes. -/
def KeptHolds (kept : Kept W T) (store : Store L) : Prop :=
  kept.index.Holds (indexEntries W store) ∧ kept.mask = maskOf W store

/-- One write on the carried structure: the blinding bytes, or one index walk. -/
def keptSet (kept : Kept W T) (a : Address L) (v : Option (L.Value a.1)) : Kept W T :=
  if some a = W.blinding then ⟨kept.index, maskAfter W a v⟩ else ⟨indexStep W T kept.index a v, kept.mask⟩

theorem keptSet_holds {kept : Kept W T} {store : Store L} (a : Address L) (v : Option (L.Value a.1))
    (h : KeptHolds W T kept store) : KeptHolds W T (keptSet W T kept a v) (store.set a v) := by
  unfold keptSet
  by_cases blind : some a = W.blinding
  · simp only [blind, if_true]
    exact ⟨(index_set_blind W blind v).symm ▸ h.1, (maskOf_set_blind W blind v).symm⟩
  · simp only [blind, if_false]
    refine ⟨?_, h.2.trans (maskOf_set_other W blind v).symm⟩
    cases v with
    | some x =>
        exact (Theory.AuthTrie.Cache.insert_holds (paths_length W T) h.1 a _).congr fun k =>
          (lastVal_index_set_some W store blind x k).symm
    | none =>
        exact (Theory.AuthTrie.Cache.erase_holds h.1 a).congr fun k =>
          (lastVal_index_set_none W store blind k).symm

/-- The one bulk build: the index entries are key-distinct, so no canonicalization pass
(`Cache.buildNodup`, linear in the entries). -/
def keptBuild (store : Store L) : {kept : Kept W T // KeptHolds W T kept store} :=
  ⟨⟨Theory.AuthTrie.Cache.buildNodup (paths_length W T) (indexEntries W store)
      (PrivateCellIndex.indexEntries_keys_nodup W store), maskOf W store⟩,
    Theory.AuthTrie.Cache.buildNodup_holds (paths_length W T) _
      (PrivateCellIndex.indexEntries_keys_nodup W store), rfl⟩

section Aux

variable (ctx : List UInt8) (codec : Minidregg.Theory.IndexedProgram.LawfulCodec (Store L))
  (rootOfBytes : List UInt8 → Digest)
  (agree : ∀ store, rootOfBytes (codec.encode store) = privateRoot W T ctx store)

/-- The read: the outer hash of the held bytes and the kept digest. -/
def keptRoot (kept : Kept W T) : Digest := outerRoot ctx kept.mask kept.index.digest

theorem keptRoot_eq {kept : Kept W T} {store : Store L} (h : KeptHolds W T kept store) :
    keptRoot W T ctx kept = privateRoot W T ctx store := by
  unfold keptRoot privateRoot
  rw [Theory.AuthTrie.Cache.digest_eq h.1, h.2]

/-- **The persistent structure**, over any root bytes that read the private root of the store
at context `ctx`. -/
def aux : Theory.CellStateAux.AuxCache (fun store => rootOfBytes (codec.encode store)) where
  Aux := Kept W T
  Holds := KeptHolds W T
  build := keptBuild W T
  set := keptSet W T
  set_holds := fun a v h => keptSet_holds W T a v h
  root? kept := some (keptRoot W T ctx kept)
  root?_sound := fun h read => by
    cases Option.some.inj read
    exact (keptRoot_eq W T ctx h).trans (agree _).symm
  root?_agree := fun ha hb => by
    show some _ = some _
    rw [keptRoot_eq W T ctx ha, keptRoot_eq W T ctx hb]

/-- **The fast path at every store**: the read is always present. -/
theorem rootAvailable (Admitted : Store L → Prop) :
    Theory.CellStateAux.RootAvailable (aux W T ctx codec rootOfBytes agree) Admitted :=
  fun _ _ => rfl

/-- **Per write, no rebuild**: a write at a data address is exactly one index walk on the
carried index, a write at the blinding address leaves it; neither reads the store. -/
theorem set_index (kept : Kept W T) (a : Address L) (v : Option (L.Value a.1)) :
    ((aux W T ctx codec rootOfBytes agree).set kept a v).index =
      if some a = W.blinding then kept.index else indexStep W T kept.index a v := by
  show (keptSet W T kept a v).index = _
  unfold keptSet
  by_cases blind : some a = W.blinding <;> simp [blind]

end Aux

/-! ## The materializer -/

/-- **The private materializer of a wire**: the wire's store codec, rooted by the private root
at the wire's context, carrying the kept index. -/
def materializer : Theory.CellState.Materializer L Digest where
  codec := StoreCodec.codec W
  rootBytes := rootBytes W T
  aux := aux W T (kindCtx W) (StoreCodec.codec W) (rootBytes W T) (rootBytes_encode W T)

/-- **The root law**: the root of every store is its private root. -/
theorem materializer_rootOf (store : Store L) :
    (materializer W T).rootOf store = privateRoot W T (kindCtx W) store :=
  rootBytes_encode W T store

/-- And the materializer's carried read is present at every store. -/
theorem materializer_rootAvailable (Admitted : Store L → Prop) :
    Theory.CellStateAux.RootAvailable (materializer W T).aux Admitted :=
  rootAvailable W T (kindCtx W) (StoreCodec.codec W) (rootBytes W T) (rootBytes_encode W T) Admitted

#assert_axioms nodeBytesWith_injective
#assert_axioms contentBytes_injective
#assert_axioms packPath_injective
#assert_axioms pathNodeBytes_injective
#assert_axioms deployedDig_collision
#assert_axioms paths_length
#assert_axioms rootBytes_encode
#assert_axioms keptSet_holds
#assert_axioms keptRoot_eq
#assert_axioms rootAvailable
#assert_axioms set_index
#assert_axioms materializer_rootOf
#assert_axioms materializer_rootAvailable

end Minidregg.Compiler.PrivateCellRoot
