/-
# Kernel.PrivateCellOpening — the selective opening's relation, exact against the committed store

Epoch (b)'s prerequisite (docs/RATCHET-LOG-DESIGN.md §3.2, §4 hybrid 2): a reader of a blinded
cell under the private root receives a statement (root, cell, version, scope, view) and a proof
that the view is the COMPLETE projection of the committed store onto the scope. No sibling digest,
path, mask or other-class entry reaches the reader: they stay in the witness.

This module fixes the relation the proof system will prove, so no backend chooses its meaning:

* The path-keyed image (`imageEntries`): each index entry as its 516-bit path and its content
  digest. The deployed node digest of the index is the path-keyed digest of its image
  (`innerRoot_image`, from `PrivateCellTrie.tree_image`), so a reveal of the image is fixed-size:
  an early-stop terminal is a path and a digest, never a hidden value.
* `Statement`, `Witness`, `OpeningRel`: the root is the outer commitment over the kind's context,
  the witness's mask and index digest; the mask's kind-level custody decode names the statement's
  cell and version; every reader prefix's reveal of the image verifies against the index digest
  at depth 516; the reveals answer exactly the view's image (the view is a store, so its order
  and encoding are the wire's).
* `DeployedCollision`: the comparison's collisions, each between inputs fixed by the store, the
  statement and the witness: two live addresses of the store on one key path, two nodes of one
  reveal's comparison scope (node bytes), a view entry against a store entry (content bytes), or
  the witness's outer input against the store's (`outerCollision_is_hash`); each a cSHAKE256
  collision on distinct bytes.
* `openingRel_exact` (sound): against the private root of a gated store, a witness in the relation
  answers exactly the store's view and its custody cell and version, or a `DeployedCollision`.
* `honest_rel` (complete): every gated store with distinct live key paths and a custody mask
  decoding to its cell and version has its honest statement in the relation with `honestWitness`.
  Completeness fails exactly on an address collision, which the receiver refuses at insert.

ATLAS fields: satisfiable `honest_rel`; teeth `openingRel_exact` (a wrong view, cell or version
needs a named collision); premise inhabitation `honest_rel`'s premises at the receiver's states.

Next (astra rounds 14-16, board/seats/privacy.md): the circuit pinned
to an emitted gate system with its acceptance output and public length bounds, and the proof system
in a shared ROM interpreter: query-bounded adversaries, one stateful simulator of bounded work,
straight-line extraction from the prover's query log, and the receiver's randomized adapter that
discharges `HidingSetting.hiding_of_hybrids`'s `zk` premise.
-/
module

public import Kernel.PrivateCellReceiver
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Kernel.PrivateCellOpening

set_option autoImplicit false

open Minidregg.Compiler
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (CellField Digest)
open Minidregg.Kernel.ResourceObservationAdmission (Visible)
open Minidregg.Kernel.PrivateCellView (kindTag storeFits readerPrefixes keyBits AddressCollision pathsInjective_or
  addressCollision_deployed admitted_of_storeFits prefixed_iff readerPrefixes_short)
open Minidregg.Kernel.PrivateCellReceiver (CustodyDecode bits)
open Minidregg.Compiler.PrivateCellIndex (indexEntries valueBytes)
open Minidregg.Compiler.PrivateCellRoot (privateRoot outerRoot outerCustomization kindCtx maskOf deployedDig hashedAddrBits
  addressHash addressCustomization nodeCustomization Path pathDig pathNodeBytes pathNodeBytes_injective contentBytes
  contentBytes_injective contentDigest contentCustomization paths paths_length output_eq_of_digest_eq)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec digestStream)
open Minidregg.Theory.AuthTrie (NodeIn Reveal revealVerify lastVal revealFor canon mem_canon entries tree
  CollisionAmong reveal_sound reveal_complete revealFor_answer)
open Minidregg.Theory.AuthTrie.Cache (PathsInjective wf_canon)
open Minidregg.Theory.PrivateCellTrie (entryImage tree_image wf_image)

/-! ## The path-keyed image of the index -/

variable {kind : CanonicalCellRegistry.Kind} (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind))

/-- An address's 516-bit key path. -/
abbrev pathKey (a : Address (CanonicalCellRegistry.layout kind)) : Path :=
  ⟨paths wire (kindTag kind) a, paths_length wire (kindTag kind) a⟩

/-- The canonical digest of a store's private index (inside the outer commitment). -/
abbrev innerRoot (S : Store (CanonicalCellRegistry.layout kind)) : Digest :=
  Theory.AuthTrie.root (deployedDig wire (kindTag kind)) (bits wire) 516 (indexEntries wire S)

/-- The index's path-keyed image: each canonical entry as its path and its content digest. Every
key and value has a fixed size. -/
def imageEntries (S : Store (CanonicalCellRegistry.layout kind)) : List (Path × Digest) :=
  (canon (indexEntries wire S)).map fun kv => (pathKey wire kv.1, contentDigest wire kv.1 kv.2)

theorem entries_image (S : Store (CanonicalCellRegistry.layout kind)) :
    entries Subtype.val (imageEntries wire S) =
      (entries (bits wire) (canon (indexEntries wire S))).map (entryImage (pathKey wire) (contentDigest wire)) := by
  simp [imageEntries, entries, entryImage, List.map_map, Function.comp_def]

/-- **The index digest is the image's**: the deployed digest of an index node is the path-keyed
digest of its image, so the canonical trees agree (`tree_image`). -/
theorem innerRoot_image (S : Store (CanonicalCellRegistry.layout kind)) :
    innerRoot wire S = tree pathDig 516 (entries Subtype.val (imageEntries wire S)) := by
  rw [entries_image, tree_image (deployedDig wire (kindTag kind)) pathDig (pathKey wire) (contentDigest wire)
    rfl (fun _ _ => rfl) (fun _ _ => rfl)]
  rfl

theorem mem_imageEntries {S : Store (CanonicalCellRegistry.layout kind)} {k : Path} {d : Digest} :
    (k, d) ∈ imageEntries wire S ↔
      ∃ a vb, lastVal (indexEntries wire S) a = some vb ∧ k = pathKey wire a ∧ d = contentDigest wire a vb := by
  simp only [imageEntries, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨a, vb⟩, member, rfl, rfl⟩
    exact ⟨a, vb, (mem_canon _ _).mp member, rfl, rfl⟩
  · rintro ⟨a, vb, live, rfl, rfl⟩
    exact ⟨(a, vb), (mem_canon _ (a, vb)).mpr live, rfl, rfl⟩

/-! ## The reference relation (fixed; no implementation chooses it) -/

/-- What a reader holds: the root, the cell and version it was published for, its scope, and
the answer, the visible store itself (so the answer's order and encoding are the wire's). -/
structure Statement where
  root : Digest
  cell : List UInt8
  version : Nat
  fields : Option (Finset CellField)
  view : Store (CanonicalCellRegistry.layout kind)

/-- What stays with the prover: the mask bytes, the index digest under the outer commitment, and
one reveal of the path-keyed image per reader prefix. Every sibling, key and value in it has a
fixed size: an early-stop terminal is a path and a content digest, never a hidden value. -/
structure Witness where
  mask : List UInt8
  inner : Digest
  reveals : List Bool → Reveal Path Digest Digest

/-- An address and value of a store, as the image pair a reveal answers. -/
def ImagePair (V : Store (CanonicalCellRegistry.layout kind)) (k : Path) (d : Digest) : Prop :=
  ∃ a value, V a = some value ∧ k = pathKey wire a ∧ d = contentDigest wire a (valueBytes wire a value)

/-- The reveals answer exactly the view's image: a pair is answered at some reader prefix iff it
is the path and content digest of a live address of the view. -/
def Answers (st : Statement (kind := kind)) (w : Witness) : Prop :=
  ∀ k d, (∃ p ∈ readerPrefixes st.fields, (k, d) ∈ (w.reveals p).answer Subtype.val p) ↔ ImagePair wire st.view k d

/-- **The bounded shape** (astra round 16): a reveal that stops above its prefix carries at most
one member, the terminal leaf there. With `revealVerify`'s `siblings.length ≤ p.length`, every
reveal is at most the prefix's sibling digests and either one terminal or exactly the entries
under the prefix, so the circuit's shape is fixed by the public prefix and answer. -/
def Shaped (fields : Option (Finset CellField)) (w : Witness) : Prop :=
  ∀ p ∈ readerPrefixes fields, (w.reveals p).siblings.length < p.length → (w.reveals p).members.length ≤ 1

/-- **The opening relation.** The root is the outer commitment over the kind's context, the
witness's mask and index digest; the mask's kind-level custody decode names the statement's cell
and version (a relabelled version is refused unless the custody bytes say it); every reader
prefix's reveal of the image verifies against the index digest at depth 516; the reveals
answer exactly the view's image; and every reveal is `Shaped`. -/
def OpeningRel (decode : CustodyDecode) (st : Statement (kind := kind)) (w : Witness) : Prop :=
  st.root = outerRoot (kindCtx wire) w.mask w.inner ∧
    (∃ secret, decode w.mask = some (st.cell, st.version, secret)) ∧
    (∀ p ∈ readerPrefixes st.fields, revealVerify pathDig Subtype.val 516 w.inner p (w.reveals p) = true) ∧
    Answers wire st w ∧ Shaped st.fields w

/-- Two distinct live addresses of the store whose canonical bytes collide under the address
customization of cSHAKE256 (two entries on one key path). -/
def AddressCollisionOf (S : Store (CanonicalCellRegistry.layout kind)) : Prop :=
  ∃ a a', (lastVal (indexEntries wire S) a).isSome ∧ (lastVal (indexEntries wire S) a').isSome ∧
    (StoreCodec.addressStream wire).encode a ≠ (StoreCodec.addressStream wire).encode a' ∧
    Sp800185Cshake256.hash addressCustomization ((StoreCodec.addressStream wire).encode a) =
      Sp800185Cshake256.hash addressCustomization ((StoreCodec.addressStream wire).encode a')

/-- Two nodes of one reveal's comparison scope against the store's image (`AuthTrie.revealNodes`:
the walked path and selected subtree of the image's canonical tree, the reveal's climb and member
tree) whose distinct node bytes collide under the node customization. -/
def NodeCollisionOf (S : Store (CanonicalCellRegistry.layout kind)) (fields : Option (Finset CellField))
    (reveals : List Bool → Reveal Path Digest Digest) : Prop :=
  ∃ p ∈ readerPrefixes fields, ∃ x y,
    Theory.AuthTrie.revealNodes pathDig Subtype.val 516 (entries Subtype.val (imageEntries wire S)) p (reveals p) x ∧
    Theory.AuthTrie.revealNodes pathDig Subtype.val 516 (entries Subtype.val (imageEntries wire S)) p (reveals p) y ∧
    pathNodeBytes x ≠ pathNodeBytes y ∧
    Sp800185Cshake256.hash nodeCustomization (pathNodeBytes x) = Sp800185Cshake256.hash nodeCustomization (pathNodeBytes y)

/-- An entry of the view and an entry of the store whose distinct content bytes collide under the
content customization. -/
def ContentCollisionOf (S V : Store (CanonicalCellRegistry.layout kind)) : Prop :=
  ∃ a x a' y, V a = some x ∧ S a' = some y ∧
    contentBytes wire a (valueBytes wire a x) ≠ contentBytes wire a' (valueBytes wire a' y) ∧
    Sp800185Cshake256.hash contentCustomization (contentBytes wire a (valueBytes wire a x)) =
      Sp800185Cshake256.hash contentCustomization (contentBytes wire a' (valueBytes wire a' y))

/-- The witness's outer input differs from the store's and commits to the same root. -/
def OuterCollisionOf (S : Store (CanonicalCellRegistry.layout kind)) (w : Witness) : Prop :=
  (w.mask, w.inner) ≠ (maskOf wire S, innerRoot wire S) ∧
    outerRoot (kindCtx wire) w.mask w.inner = outerRoot (kindCtx wire) (maskOf wire S) (innerRoot wire S)

/-- **The comparison's collisions**, each between inputs fixed by the store, the statement and the
witness: no implementation chooses where a collision may be drawn from. -/
def DeployedCollision (S : Store (CanonicalCellRegistry.layout kind)) (st : Statement (kind := kind))
    (w : Witness) : Prop :=
  AddressCollisionOf wire S ∨ NodeCollisionOf wire S st.fields w.reveals ∨ ContentCollisionOf wire S st.view ∨
    OuterCollisionOf wire S w

/-- The bytes the outer commitment hashes: the context, the mask and the index digest. -/
def outerBytes (mask : List UInt8) (inner : Digest) : List UInt8 :=
  (StreamCodec.product (StreamCodec.list StreamCodec.byte)
    (StreamCodec.product (StreamCodec.list StreamCodec.byte) digestStream)).encode (kindCtx wire, mask, inner)

/-- An outer collision is a cSHAKE256 collision under the outer customization on two distinct
byte strings. -/
theorem outerCollision_is_hash {S : Store (CanonicalCellRegistry.layout kind)} {w : Witness}
    (collision : OuterCollisionOf wire S w) :
    outerBytes wire w.mask w.inner ≠ outerBytes wire (maskOf wire S) (innerRoot wire S) ∧
      Sp800185Cshake256.hash outerCustomization (outerBytes wire w.mask w.inner) =
        Sp800185Cshake256.hash outerCustomization (outerBytes wire (maskOf wire S) (innerRoot wire S)) := by
  refine ⟨fun same => collision.1 ?_, output_eq_of_digest_eq collision.2⟩
  have := StoreCodec.streamEncode_injective _ same
  simp only [Prod.mk.injEq, true_and] at this
  rw [this.1, this.2]

/-! ## Exactness and completeness -/

/-- **The image's answers under the reader's prefixes are the view's image**: when every prefix's
answer is exactly the image's pairs under it, the union is the image of the store's visible
entries. -/
theorem imageUnion_iff (selected : CanonicalCellRegistry.wire? kind = some wire)
    (S : Store (CanonicalCellRegistry.layout kind)) (fields : Option (Finset CellField))
    (admitted : ∀ a, S a ≠ none → PrivateCellScope.addressFits 256 kind a = true)
    (reveals : List Bool → Reveal Path Digest Digest)
    (answers : ∀ p ∈ readerPrefixes fields, ∀ k d, (k, d) ∈ (reveals p).answer Subtype.val p ↔
      (k, d) ∈ imageEntries wire S ∧ k.1.take p.length = p) :
    ∀ k d, (∃ p ∈ readerPrefixes fields, (k, d) ∈ (reveals p).answer Subtype.val p) ↔
      ImagePair wire (Minidregg.Theory.SparseMap.filterKeys (Visible fields kind) S) k d := by
  intro k d
  have prefixed := prefixed_iff selected (hashedAddrBits wire 256 addressHash) S fields admitted
  constructor
  · rintro ⟨p, member, answered⟩
    obtain ⟨inImage, under⟩ := (answers p member k d).mp answered
    obtain ⟨a, vb, live, rfl, rfl⟩ := (mem_imageEntries wire).mp inImage
    obtain ⟨value, visible, rfl⟩ := (prefixed a vb).mp ⟨p, member, live, under⟩
    exact ⟨a, value, visible, rfl, rfl⟩
  · rintro ⟨a, value, visible, rfl, rfl⟩
    obtain ⟨p, member, live, under⟩ := (prefixed a _).mpr ⟨value, visible, rfl⟩
    exact ⟨p, member, (answers p member _ _).mpr ⟨(mem_imageEntries wire).mpr ⟨a, _, live, rfl, rfl⟩, under⟩⟩

theorem live_of_filterKeys {fields : Option (Finset CellField)} {S : Store (CanonicalCellRegistry.layout kind)}
    {a : Address (CanonicalCellRegistry.layout kind)} {y : (CanonicalCellRegistry.layout kind).Value a.1}
    (h : Minidregg.Theory.SparseMap.filterKeys (Visible fields kind) S a = some y) : S a = some y := by
  rw [Minidregg.Theory.SparseMap.filterKeys_apply] at h
  split at h
  · exact h
  · cases h

/-- **Equal images are equal views, or a content collision.** -/
theorem view_eq_of_images {fields : Option (Finset CellField)} {V S : Store (CanonicalCellRegistry.layout kind)}
    (same : ∀ k d, ImagePair wire V k d ↔
      ImagePair wire (Minidregg.Theory.SparseMap.filterKeys (Visible fields kind) S) k d) :
    V = Minidregg.Theory.SparseMap.filterKeys (Visible fields kind) S ∨ ContentCollisionOf wire S V := by
  by_cases collision : ContentCollisionOf wire S V
  · exact Or.inr collision
  · left
    refine Minidregg.Theory.SparseMap.ext fun a => ?_
    cases hV : V a with
    | some x =>
        obtain ⟨a', y, hy, keys, digests⟩ := (same _ _).mp ⟨a, x, hV, rfl, rfl⟩
        by_cases bytes : contentBytes wire a (valueBytes wire a x) = contentBytes wire a' (valueBytes wire a' y)
        · obtain ⟨rfl, values⟩ := contentBytes_injective wire bytes
          rw [hy, StoreCodec.streamEncode_injective _ values]
        · exact absurd ⟨a, x, a', y, hV, live_of_filterKeys hy, bytes, output_eq_of_digest_eq digests⟩ collision
    | none =>
        cases hS : Minidregg.Theory.SparseMap.filterKeys (Visible fields kind) S a with
        | none => rfl
        | some y =>
            obtain ⟨a'', x, hx, keys, digests⟩ := (same _ _).mpr ⟨a, y, hS, rfl, rfl⟩
            by_cases bytes : contentBytes wire a'' (valueBytes wire a'' x) = contentBytes wire a (valueBytes wire a y)
            · obtain ⟨rfl, _⟩ := contentBytes_injective wire bytes
              rw [hV] at hx; cases hx
            · exact absurd ⟨a'', x, a, y, hx, live_of_filterKeys hS, bytes, output_eq_of_digest_eq digests.symm⟩ collision

/-- **The relation is exact against the committed store.** A statement whose root is the private
root of a gated store, with a witness in the relation, answers exactly that store's view and names
its custody cell and version, or the comparison exhibits one of the fixed collisions. -/
theorem openingRel_exact (selected : CanonicalCellRegistry.wire? kind = some wire) (decode : CustodyDecode)
    (S : Store (CanonicalCellRegistry.layout kind)) (gate : storeFits wire S = true)
    (st : Statement (kind := kind)) (w : Witness)
    (root : st.root = privateRoot wire (kindTag kind) (kindCtx wire) S) (holds : OpeningRel wire decode st w) :
    (st.view = Minidregg.Theory.SparseMap.filterKeys (Visible st.fields kind) S ∧
        ∃ secret, decode (maskOf wire S) = some (st.cell, st.version, secret)) ∨
      DeployedCollision wire S st w := by
  obtain ⟨outer, custody, verifies, answers, -⟩ := holds
  by_cases same : (w.mask, w.inner) = (maskOf wire S, innerRoot wire S)
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨same, outer.symm.trans root⟩)))
  obtain ⟨hm, hi⟩ := Prod.mk.inj same
  rcases pathsInjective_or (addrBits := hashedAddrBits wire 256 addressHash) (indexEntries wire S) with inj | collides
  swap
  · exact Or.inr (Or.inl (addressCollision_deployed collides))
  have wf : Theory.AuthTrie.WF 516 (entries Subtype.val (imageEntries wire S)) := by
    rw [entries_image]
    exact wf_image _ _ (wf_canon (fun a => paths_length wire (kindTag kind) a) inj)
  have sound : ∀ p ∈ readerPrefixes st.fields,
      (∀ k d, (k, d) ∈ (w.reveals p).answer Subtype.val p ↔ (k, d) ∈ imageEntries wire S ∧ k.1.take p.length = p) ∨
        CollisionAmong pathDig (Theory.AuthTrie.revealNodes pathDig Subtype.val 516
          (entries Subtype.val (imageEntries wire S)) p (w.reveals p)) := by
    intro p member
    have accepted := verifies p member
    rw [hi, innerRoot_image] at accepted
    exact reveal_sound pathDig Subtype.val 516 (fun k => k.2) _ wf p (w.reveals p) accepted
  by_cases node : ∃ p ∈ readerPrefixes st.fields, CollisionAmong pathDig (Theory.AuthTrie.revealNodes pathDig
      Subtype.val 516 (entries Subtype.val (imageEntries wire S)) p (w.reveals p))
  · obtain ⟨p, member, x, y, hx, hy, ne, digest⟩ := node
    exact Or.inr (Or.inr (Or.inl ⟨p, member, x, y, hx, hy, fun bytes => ne (pathNodeBytes_injective bytes),
      output_eq_of_digest_eq digest⟩))
  push_neg at node
  have exactAnswers : ∀ p ∈ readerPrefixes st.fields, ∀ k d, (k, d) ∈ (w.reveals p).answer Subtype.val p ↔
      (k, d) ∈ imageEntries wire S ∧ k.1.take p.length = p :=
    fun p member => (sound p member).resolve_right (node p member)
  have images := imageUnion_iff wire selected S st.fields (admitted_of_storeFits gate) w.reveals exactAnswers
  rcases view_eq_of_images wire (fun k d => (answers k d).symm.trans (images k d)) with equal | content
  · refine Or.inl ⟨equal, ?_⟩
    rw [← hm]; exact custody
  · exact Or.inr (Or.inr (Or.inr (Or.inl content)))

/-- The honest statement of a store under a scope, for a cell and version. -/
def honestStatement (S : Store (CanonicalCellRegistry.layout kind)) (fields : Option (Finset CellField))
    (cell : List UInt8) (version : Nat) : Statement (kind := kind) :=
  ⟨privateRoot wire (kindTag kind) (kindCtx wire) S, cell, version, fields,
    Minidregg.Theory.SparseMap.filterKeys (Visible fields kind) S⟩

/-- The honest witness: the store's mask and index digest, and the honest reveal of the image at
every prefix. -/
def honestWitness (S : Store (CanonicalCellRegistry.layout kind)) : Witness :=
  ⟨maskOf wire S, innerRoot wire S, fun p => revealFor pathDig Subtype.val 516 (imageEntries wire S) p⟩

/-- **Completeness of the relation**: every gated store whose live addresses lie on distinct key
paths, under a custody mask that decodes to its cell and version, has the honest statement in the
relation with the honest witness. The domain excludes stores with an address collision, which the
receiver refuses at insert. -/
theorem honest_rel (selected : CanonicalCellRegistry.wire? kind = some wire) (decode : CustodyDecode)
    (S : Store (CanonicalCellRegistry.layout kind)) (gate : storeFits wire S = true)
    (inj : PathsInjective (bits wire) (indexEntries wire S)) (fields : Option (Finset CellField))
    {cell : List UInt8} {version : Nat} {secret : List UInt8}
    (custody : decode (maskOf wire S) = some (cell, version, secret)) :
    OpeningRel wire decode (honestStatement wire S fields cell version) (honestWitness wire S) := by
  have wf : Theory.AuthTrie.WF 516 (entries Subtype.val (imageEntries wire S)) := by
    rw [entries_image]
    exact wf_image _ _ (wf_canon (fun a => paths_length wire (kindTag kind) a) inj)
  refine ⟨rfl, ⟨secret, custody⟩, fun p member => ?_, fun k d => ?_, fun p member early => ?_⟩
  · show revealVerify pathDig Subtype.val 516 (innerRoot wire S) p
      (revealFor pathDig Subtype.val 516 (imageEntries wire S) p) = true
    rw [innerRoot_image]
    exact reveal_complete pathDig Subtype.val 516 (fun k => k.2) _ wf p
      (by have := readerPrefixes_short fields p member; omega)
  · exact imageUnion_iff wire selected S fields (admitted_of_storeFits gate) _
      (fun p _ k d => revealFor_answer pathDig Subtype.val 516 _ p k d) k d
  · exact Theory.AuthTrie.revealFor_shaped pathDig Subtype.val 516 _ p
      (by have := readerPrefixes_short fields p member; omega) early

#assert_axioms innerRoot_image
#assert_axioms imageUnion_iff
#assert_axioms view_eq_of_images
#assert_axioms openingRel_exact
#assert_axioms honest_rel
#assert_axioms outerCollision_is_hash

end Minidregg.Kernel.PrivateCellOpening
