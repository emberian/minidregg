/-
# Kernel.PrivateCellOpening — the selective opening's relation, exact against the committed store

Epoch (b)'s prerequisite (docs/RATCHET-LOG-DESIGN.md §3.2, §4 hybrid 2): a reader of a blinded
cell under the private root receives a statement (root, cell, version, scope, view) and a proof
that the view is the COMPLETE projection of the committed store onto the scope. No sibling digest,
path, mask or other-class entry reaches the reader: they stay in the witness.

This module fixes the relation the proof system will prove, so no backend chooses its meaning:

* `Statement`, `Witness`, `OpeningRel`: the root is the outer commitment over the kind's context,
  the witness's mask and index digest; the mask's kind-level custody decode names the statement's
  cell and version; every reader prefix's reveal verifies against the index digest at depth 516;
  the reveals answer exactly the view (a store, so its order and encoding are the wire's).
* `DeployedCollision`: the comparison's collisions, each between inputs fixed by the store, the
  scope and the witness: two live addresses of the store on one key path, two nodes of one
  reveal's comparison scope, or the witness's outer input against the store's
  (`outerCollision_is_hash`: a cSHAKE256 collision on distinct bytes).
* `openingRel_exact` (sound): against the private root of a gated store, a witness in the relation
  answers exactly the store's view and its custody cell and version, or a `DeployedCollision`.
* `honest_rel` (complete): every gated store with distinct live key paths and a custody mask
  decoding to its cell and version has its honest statement in the relation with `honestWitness`.
  Completeness fails exactly on an address collision, which the receiver refuses at insert.

ATLAS fields: satisfiable `honest_rel`; teeth `openingRel_exact` (a wrong view, cell or version
needs a named collision); premise inhabitation `honest_rel`'s premises at the receiver's states.

Next (astra rounds 14-15, docs in board/seats/privacy.md): the leaf format with fixed-size hidden
payloads (an early-stop reveal must not carry a hidden value of unbounded size), the circuit pinned
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
open Minidregg.Kernel.PrivateCellView (kindTag storeFits readerPrefixes keyBits viewOpeningExact_deployed
  admitted_of_storeFits honest_accepted honest_answers)
open Minidregg.Kernel.PrivateCellReceiver (CustodyDecode bits)
open Minidregg.Compiler.PrivateCellIndex (indexEntries valueBytes)
open Minidregg.Compiler.PrivateCellRoot (privateRoot outerRoot outerCustomization kindCtx maskOf deployedDig nodeBytesWith hashedAddrBits
  hashedAddrBits_length addressHash addressCustomization nodeCustomization)
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec digestStream)
open Minidregg.Theory.AuthTrie (Reveal revealVerify lastVal revealFor canon)
open Minidregg.Theory.AuthTrie.Cache (PathsInjective)

/-! ## The reference relation (fixed; no implementation chooses it) -/

variable {kind : CanonicalCellRegistry.Kind} (wire : StoreCodec.Wire (CanonicalCellRegistry.layout kind))

/-- The canonical digest of a store's private index (inside the outer commitment). -/
abbrev innerRoot (S : Store (CanonicalCellRegistry.layout kind)) : Digest :=
  Theory.AuthTrie.root (deployedDig wire) (bits wire) 516 (indexEntries wire S)

/-- What a reader holds: the root, the cell and version it was published for, its scope, and
the answer, the visible store itself (so the answer's order and encoding are the wire's). -/
structure Statement where
  root : Digest
  cell : List UInt8
  version : Nat
  fields : Option (Finset CellField)
  view : Store (CanonicalCellRegistry.layout kind)

/-- What stays with the prover: the mask bytes, the index digest under the outer commitment,
and one reveal per reader prefix (sibling digests and the members below the stop). -/
structure Witness where
  mask : List UInt8
  inner : Digest
  reveals : List Bool → Reveal (Address (CanonicalCellRegistry.layout kind)) (List UInt8) Digest

/-- The reveals answer exactly the statement's view: a pair is answered at some reader prefix
iff it is a live address of the view with its value bytes. -/
def Answers (st : Statement (kind := kind)) (w : Witness (kind := kind)) : Prop :=
  ∀ a v, (∃ p ∈ readerPrefixes st.fields, (a, v) ∈ (w.reveals p).answer (bits wire) p) ↔
    ∃ value, st.view a = some value ∧ v = valueBytes wire a value

/-- **The opening relation.** The root is the outer commitment over the kind's context, the
witness's mask and index digest; the mask's kind-level custody decode names the statement's cell
and version (item 6: a relabelled version is refused unless the custody bytes say it); every
reader prefix's reveal verifies against the index digest at depth 516; and the reveals answer
exactly the view. -/
def OpeningRel (decode : CustodyDecode) (st : Statement (kind := kind)) (w : Witness (kind := kind)) : Prop :=
  st.root = outerRoot (kindCtx wire) w.mask w.inner ∧
    (∃ secret, decode w.mask = some (st.cell, st.version, secret)) ∧
    (∀ p ∈ readerPrefixes st.fields,
      revealVerify (deployedDig wire) (bits wire) 516 w.inner p (w.reveals p) = true) ∧
    Answers wire st w

/-- Two distinct live addresses of the store whose canonical bytes collide under the address
customization of cSHAKE256 (two entries on one key path). -/
def AddressCollisionOf (S : Store (CanonicalCellRegistry.layout kind)) : Prop :=
  ∃ a a', (lastVal (indexEntries wire S) a).isSome ∧ (lastVal (indexEntries wire S) a').isSome ∧
    (StoreCodec.addressStream wire).encode a ≠ (StoreCodec.addressStream wire).encode a' ∧
    Sp800185Cshake256.hash addressCustomization ((StoreCodec.addressStream wire).encode a) =
      Sp800185Cshake256.hash addressCustomization ((StoreCodec.addressStream wire).encode a')

/-- Two nodes of one reveal's comparison scope against the store (`PrivateCellTrie.revealNodes`:
the store's walked path and selected subtree, the reveal's climb and member tree) whose distinct
node bytes collide under the node customization. -/
def NodeCollisionOf (S : Store (CanonicalCellRegistry.layout kind)) (fields : Option (Finset CellField))
    (reveals : List Bool → Reveal (Address (CanonicalCellRegistry.layout kind)) (List UInt8) Digest) : Prop :=
  ∃ p ∈ readerPrefixes fields, ∃ x y,
    Theory.PrivateCellTrie.revealNodes (deployedDig wire) (keyBits (hashedAddrBits wire 256 addressHash)) (260 + 256)
      (indexEntries wire S) p (reveals p) x ∧
    Theory.PrivateCellTrie.revealNodes (deployedDig wire) (keyBits (hashedAddrBits wire 256 addressHash)) (260 + 256)
      (indexEntries wire S) p (reveals p) y ∧
    nodeBytesWith wire digestStream x ≠ nodeBytesWith wire digestStream y ∧
    Sp800185Cshake256.hash nodeCustomization (nodeBytesWith wire digestStream x) =
      Sp800185Cshake256.hash nodeCustomization (nodeBytesWith wire digestStream y)

/-- The witness's outer input differs from the store's and commits to the same root: a collision
of the outer commitment (cSHAKE256 under the outer customization over the injective encoding of
context, mask and index digest) on these two inputs. -/
def OuterCollisionOf (S : Store (CanonicalCellRegistry.layout kind)) (w : Witness (kind := kind)) : Prop :=
  (w.mask, w.inner) ≠ (maskOf wire S, innerRoot wire S) ∧
    outerRoot (kindCtx wire) w.mask w.inner = outerRoot (kindCtx wire) (maskOf wire S) (innerRoot wire S)

/-- **The comparison's collisions**, each between named inputs fixed by the store, the scope and
the witness (items 1 and 2): no implementation chooses where a collision may be drawn from. -/
def DeployedCollision (S : Store (CanonicalCellRegistry.layout kind)) (fields : Option (Finset CellField))
    (w : Witness (kind := kind)) : Prop :=
  AddressCollisionOf wire S ∨ NodeCollisionOf wire S fields w.reveals ∨ OuterCollisionOf wire S w

/-- The bytes the outer commitment hashes: the context, the mask and the index digest. -/
def outerBytes (mask : List UInt8) (inner : Digest) : List UInt8 :=
  (StreamCodec.product (StreamCodec.list StreamCodec.byte)
    (StreamCodec.product (StreamCodec.list StreamCodec.byte) digestStream)).encode (kindCtx wire, mask, inner)

/-- An outer collision is a cSHAKE256 collision under the outer customization on two distinct
byte strings. -/
theorem outerCollision_is_hash {S : Store (CanonicalCellRegistry.layout kind)} {w : Witness (kind := kind)}
    (collision : OuterCollisionOf wire S w) :
    outerBytes wire w.mask w.inner ≠ outerBytes wire (maskOf wire S) (innerRoot wire S) ∧
      Sp800185Cshake256.hash outerCustomization (outerBytes wire w.mask w.inner) =
        Sp800185Cshake256.hash outerCustomization (outerBytes wire (maskOf wire S) (innerRoot wire S)) := by
  refine ⟨fun same => collision.1 ?_, Kernel.PrivateCellView.output_eq_of_digest_eq collision.2⟩
  have := StoreCodec.streamEncode_injective _ same
  simp only [Prod.mk.injEq, true_and] at this
  rw [this.1, this.2]

/-- Two views answering the same value bytes at every address are one store. -/
theorem view_eq_of_bytes {V S : Store (CanonicalCellRegistry.layout kind)}
    (same : ∀ a v, (∃ value, V a = some value ∧ v = valueBytes wire a value) ↔
      ∃ value, S a = some value ∧ v = valueBytes wire a value) : V = S := by
  refine Minidregg.Theory.SparseMap.ext fun a => ?_
  cases hV : V a with
  | some x =>
      obtain ⟨y, hy, bytes⟩ := (same a _).mp ⟨x, hV, rfl⟩
      rw [hy, StoreCodec.streamEncode_injective _ bytes]
  | none =>
      cases hS : S a with
      | none => rfl
      | some y =>
          obtain ⟨x, hx, _⟩ := (same a _).mpr ⟨y, hS, rfl⟩
          rw [hV] at hx; cases hx

/-- **The relation is exact against the committed store.** A statement whose root is the
private root of a gated store, with a witness in the relation, answers exactly that store's
view and names its custody cell and version, or the comparison exhibits one of the fixed
collisions. Proved from `viewOpeningExact_deployed`. -/
theorem openingRel_exact (selected : CanonicalCellRegistry.wire? kind = some wire) (decode : CustodyDecode)
    (S : Store (CanonicalCellRegistry.layout kind)) (gate : storeFits wire S = true)
    (st : Statement (kind := kind)) (w : Witness (kind := kind))
    (root : st.root = privateRoot wire (kindTag kind) (kindCtx wire) S) (holds : OpeningRel wire decode st w) :
    (st.view = Minidregg.Theory.SparseMap.filterKeys (Visible st.fields kind) S ∧
        ∃ secret, decode (maskOf wire S) = some (st.cell, st.version, secret)) ∨
      DeployedCollision wire S st.fields w := by
  obtain ⟨outer, custody, verifies, answers⟩ := holds
  by_cases same : (w.mask, w.inner) = (maskOf wire S, innerRoot wire S)
  · obtain ⟨hm, hi⟩ := Prod.mk.inj same
    rcases viewOpeningExact_deployed selected S st.fields w.reveals (admitted_of_storeFits gate)
        (fun p member => by have := verifies p member; rw [hi] at this; exact this) with answered | address | node
    · refine Or.inl ⟨view_eq_of_bytes wire fun a v => (answers a v).symm.trans (answered a v), ?_⟩
      rw [← hm]; exact custody
    · exact Or.inr (Or.inl address)
    · exact Or.inr (Or.inr (Or.inl node))
  · exact Or.inr (Or.inr (Or.inr ⟨same, outer.symm.trans root⟩))

/-- The honest statement of a store under a scope, for a cell and version. -/
def honestStatement (S : Store (CanonicalCellRegistry.layout kind)) (fields : Option (Finset CellField))
    (cell : List UInt8) (version : Nat) : Statement (kind := kind) :=
  ⟨privateRoot wire (kindTag kind) (kindCtx wire) S, cell, version, fields, Minidregg.Theory.SparseMap.filterKeys (Visible fields kind) S⟩

/-- The honest witness: the store's mask and index digest, and the honest reveal of every prefix
(`AuthTrie.revealFor`, served from the kept trie by `Trie.reveal`). -/
def honestWitness (S : Store (CanonicalCellRegistry.layout kind)) : Witness (kind := kind) :=
  ⟨maskOf wire S, innerRoot wire S, fun p =>
    revealFor (deployedDig wire) (bits wire) 516 (canon (indexEntries wire S)) p⟩

/-- **Completeness of the relation**: every gated store whose live addresses lie on distinct key
paths, under a custody mask that decodes to its cell and version, has the honest statement in the
relation with the honest witness. The domain excludes stores with an address collision (whose
index loses an entry), which the receiver refuses at insert. -/
theorem honest_rel (selected : CanonicalCellRegistry.wire? kind = some wire) (decode : CustodyDecode)
    (S : Store (CanonicalCellRegistry.layout kind)) (gate : storeFits wire S = true)
    (inj : PathsInjective (bits wire) (indexEntries wire S)) (fields : Option (Finset CellField))
    {cell : List UInt8} {version : Nat} {secret : List UInt8}
    (custody : decode (maskOf wire S) = some (cell, version, secret)) :
    OpeningRel wire decode (honestStatement wire S fields cell version) (honestWitness wire S) :=
  ⟨rfl, ⟨secret, custody⟩, honest_accepted (deployedDig wire) (hashedAddrBits_length wire 256 addressHash) S fields inj,
    fun a v => honest_answers selected (deployedDig wire) (hashedAddrBits wire 256 addressHash) 516 S fields
      (admitted_of_storeFits gate) a v⟩

#assert_axioms view_eq_of_bytes
#assert_axioms openingRel_exact
#assert_axioms honest_rel
#assert_axioms outerCollision_is_hash

end Minidregg.Kernel.PrivateCellOpening
