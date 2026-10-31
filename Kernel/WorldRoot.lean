/-
# Kernel.WorldRoot -- the world root: the compressed trie over the world's slot roots

docs/DATAMODEL.md §3.2/§3.4, step C1.  The world root is `Theory.AuthTrie`'s compressed
trie over the world's slots (`Key.system` and `Key.cell c`), each slot holding
its root.  A key alone under a prefix is a leaf at the highest level where it is
alone; a branch is hashed only over two or more keys.  `Kernel.World` left the
root function a parameter of `Checkpoint`; this module supplies it.

* `rootOf cellRoot sysRoot dig ix L w` is the root of a `Kernel.World`:
  `AuthTrie.root` of its slot roots (`slotRoots`), the LAST value per key.  It
  is a function of each key's last value (`AuthTrie.root_congr`), so it does
  not depend on the order slots were written in, with no premise.
* **Binding.**  `rootOf_binds` turns root equality into world equality under
  `RootBinding` (per key: the honest opening of one world, checked against the
  other's root, reads what the other reads; index paths distinct; leaf roots
  separate contents).  `rootOf_eq_exhibits_collision` is the same fact with no
  premise: equal roots of different worlds exhibit a node collision, an index
  collision or a leaf-root collision.  `resume_sound_rootOf` is
  `Kernel.World.resume_sound` with its `binds` premise discharged this way.
* `deployedRoot` is the root the host runs: nodes framed by `nodeBytes` (tag
  0 empty / 1 leaf key ++ digest / 2 branch left ++ right) under cSHAKE256
  `DREGG.WORLD-ROOT/v2`, keys at a 256-bit hashed index.  `worldDig_collision`
  and `deployedIx_collision` reduce a node or index collision to a collision of
  the deployed hash, so `deployedRoot_binds` is premise-free up to one.
* `cshakeHistory` is the turn digest and log chain `Kernel.World.History`
  handed on: cSHAKE over a turn's canonical bytes, chained.

Poles (toy world root at a constant hash, over `Kernel.World`'s toy worlds):
`honest_checkpoint_resumes` (the carrier holds at the honest checkpoint at
every hash) and `tampered_checkpoint_accepted` (a tampered world with the
honest root: the check passes, the resume disagrees with the fold, and the
carrier fails).
-/
module

public import Theory.AuthMap
public import Theory.AuthTrieCache
public import Kernel.World
public import Compiler.Tower256ConcreteBackend
public import Compiler.PersistedCodecTags.Core

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Mathlib.Data.List.Sort

@[expose] public section

namespace Minidregg.Kernel.WorldRoot

open Minidregg.Theory
open Minidregg.Theory.AuthMap (PrefixFree PrefixFree.injective unaryFrame unaryFrame_prefixFree)
open Minidregg.Theory.Store
open Minidregg.Kernel.World
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option linter.dupNamespace false

/-! ## Framing -/

/-- A stream codec's encoding is prefix-free: `decodePrefix` splits it off. -/
theorem streamPrefixFree {α : Type} (codec : StreamCodec α) : PrefixFree codec.encode := by
  intro a b s t h
  have ha := codec.decodePrefix_encode a s
  have hb := codec.decodePrefix_encode b t
  rw [h, hb] at ha
  simp only [Option.some.injEq, Prod.mk.injEq] at ha
  exact ⟨ha.1.symm, ha.2.symm⟩

/-! ## The world's keys -/

/-- A slot of the world map: the system cell, or a cell by its id. -/
inductive Key
  | system
  | cell (c : CellId)
  deriving DecidableEq, Repr, Hashable

instance : LawfulHashable Key where
  hash_eq a b same := by
    cases eq_of_beq same
    rfl

def keyBytes : Key → List UInt8
  | .system => [0]
  | .cell c => 1 :: StreamCodec.nat.encode c

theorem keyBytes_prefixFree : PrefixFree keyBytes := by
  intro a b s t h
  rcases a with _ | a <;> rcases b with _ | b
  · simp only [keyBytes, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
    exact ⟨rfl, h⟩
  · simp [keyBytes] at h
  · simp [keyBytes] at h
  · simp only [keyBytes, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨hab, hst⟩ := streamPrefixFree StreamCodec.nat a b s t h
    exact ⟨by rw [hab], hst⟩

/-! ## Bits of bytes -/

/-- The eight bits of a byte, most significant first. -/
def byteBits (b : UInt8) : List Bool := (List.range 8).reverse.map fun i => b.toNat.testBit i

def bytesBits (bs : List UInt8) : List Bool := bs.flatMap byteBits

@[simp] theorem byteBits_length (b : UInt8) : (byteBits b).length = 8 := by simp [byteBits]

theorem bytesBits_length (bs : List UInt8) : (bytesBits bs).length = 8 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [bytesBits, List.flatMap_cons, List.length_append, byteBits_length,
        List.length_cons] at ih ⊢
      rw [ih]; ring

theorem byteBits_injective : Function.Injective byteBits := by
  intro a b h
  have hbits : ∀ i, a.toNat.testBit i = b.toNat.testBit i := by
    intro i
    by_cases hi : i < 8
    · exact List.map_inj_left.mp h i (by simp [hi])
    · have hle : 2 ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have ha : a.toNat < 2 ^ i := lt_of_lt_of_le a.toNat_lt hle
      have hb : b.toNat < 2 ^ i := lt_of_lt_of_le b.toNat_lt hle
      rw [Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb]
  exact UInt8.toNat_inj.mp (Nat.eq_of_testBit_eq hbits)

theorem bytesBits_injective : Function.Injective bytesBits := by
  intro as bs h
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => rfl
      | cons b bs =>
          have := congrArg List.length h
          simp [bytesBits_length] at this
  | cons a as ih =>
      cases bs with
      | nil =>
          have := congrArg List.length h
          simp [bytesBits_length] at this
      | cons b bs =>
          simp only [bytesBits, List.flatMap_cons] at h
          obtain ⟨hab, hrest⟩ := List.append_inj h (by simp)
          rw [byteBits_injective hab, ih hrest]


section WorldRoot

variable {R : Registry} {TxId D : Type} [DecidableEq TxId] [DecidableEq D]
variable {V Dg : Type} [DecidableEq V] [DecidableEq Dg]

/-- A slot's content: the system cell or a cell. -/
inductive Slot (R : Registry) (TxId D : Type) [DecidableEq TxId] [DecidableEq D]
  | system (s : Store (sysLayout TxId D))
  | cell (c : Cell R)

variable (cellRoot : Cell R → V) (sysRoot : Store (sysLayout TxId D) → V)

/-- A slot's root. -/
def slotRoot : Slot R TxId D → V
  | .system s => sysRoot s
  | .cell c => cellRoot c

instance optionNeZeroDecidable {α : Type} (x : Option α) : Decidable (x ≠ 0) :=
  decidable_of_iff (x.isSome = true) (by cases x <;> simp <;> rfl)

/-- A multiset of ids as its increasing list (insertion sort, so the kernel
evaluates it). -/
def sortIds (s : Multiset CellId) : List CellId :=
  Quot.liftOn s (List.insertionSort (· ≤ ·)) fun a b hab =>
    List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ a) (List.pairwise_insertionSort _ b)
      ((List.perm_insertionSort _ a).trans (hab.trans (List.perm_insertionSort _ b).symm))

theorem mem_sortIds (s : Multiset CellId) (c : CellId) : c ∈ sortIds s ↔ c ∈ s := by
  induction s using Quot.inductionOn with
  | h l => exact (List.perm_insertionSort _ l).mem_iff

/-- The present cell ids, in increasing order. -/
def presentIds (w : World R TxId D) : List CellId := sortIds w.cells.support.val

theorem mem_presentIds (w : World R TxId D) (c : CellId) :
    c ∈ presentIds w ↔ w.cells c ≠ none := by
  rw [presentIds, mem_sortIds, Finset.mem_val, DFinsupp.mem_support_iff]
  rfl

/-- The world's entries: the system cell, then every present cell. -/
def entries (w : World R TxId D) : List (Key × Slot R TxId D) :=
  (Key.system, .system w.system) ::
    (presentIds w).filterMap fun c => (w.cells c).map fun cell => (Key.cell c, .cell cell)


/-- The keys the world's entries name. -/
def keys (w : World R TxId D) : List Key := (entries w).map (·.1)

theorem mem_keys_cell (w : World R TxId D) (c : CellId) :
    Key.cell c ∈ keys w ↔ w.cells c ≠ none := by
  constructor
  · intro h
    simp only [keys, entries, List.map_cons, List.mem_cons, reduceCtorEq, false_or, List.mem_map,
      List.mem_filterMap] at h
    obtain ⟨e, ⟨c', _, he⟩, hk⟩ := h
    rcases hw : w.cells c' with _ | cell
    · simp [hw] at he
    · simp only [hw, Option.map_some, Option.some.injEq] at he
      subst he
      simp only [Key.cell.injEq] at hk
      subst hk
      simp [hw]
  · intro h
    rcases hw : w.cells c with _ | cell
    · exact absurd hw h
    · simp only [keys, entries, List.map_cons, List.mem_cons, reduceCtorEq, false_or, List.mem_map,
        List.mem_filterMap]
      exact ⟨(Key.cell c, Slot.cell cell), ⟨c, (mem_presentIds w c).2 h, by simp [hw]⟩, rfl⟩

/-- Index paths do not collide among one world's keys. -/
theorem system_mem_keys (w : World R TxId D) : Key.system ∈ keys w := by
  simp [keys, entries]


/-- The world's reading at a slot: the last entry its entries give the key. -/
theorem lastVal_entries (w : World R TxId D) :
    ∀ k, AuthTrie.lastVal (entries w) k =
      match k with
      | .system => some (.system w.system)
      | .cell c => (w.cells c).map .cell := by
  intro k
  by_cases hk : k ∈ keys w
  · unfold AuthTrie.lastVal
    cases k with
    | system =>
        simp only [entries, List.filter_cons, decide_true, if_true]
        have : ((presentIds w).filterMap fun c => (w.cells c).map fun cell =>
            ((Key.cell c, Slot.cell cell) : Key × Slot R TxId D)).filter
              (fun e => decide (e.1 = Key.system)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro e he
          rcases List.mem_filterMap.mp he with ⟨c, _, hc⟩
          rcases hw : w.cells c with _ | cell
          · simp [hw] at hc
          · simp only [hw, Option.map_some, Option.some.injEq] at hc
            subst hc; simp
        rw [this]; rfl
    | cell c =>
        simp only [entries, List.filter_cons, reduceCtorEq, decide_false, Bool.false_eq_true,
          if_false]
        have hsub : ∀ e ∈ ((presentIds w).filterMap fun c' => (w.cells c').map fun cell =>
            ((Key.cell c', Slot.cell cell) : Key × Slot R TxId D)).filter
              (fun e => decide (e.1 = Key.cell c)),
              ∃ cell, w.cells c = some cell ∧ e = (Key.cell c, .cell cell) := by
          intro e he
          rcases List.mem_filter.mp he with ⟨he, hk⟩
          rcases List.mem_filterMap.mp he with ⟨c', _, hc⟩
          rcases hw : w.cells c' with _ | cell
          · simp [hw] at hc
          · simp only [hw, Option.map_some, Option.some.injEq] at hc
            subst hc
            simp only [decide_eq_true_eq, Key.cell.injEq] at hk
            subst hk
            exact ⟨cell, hw, rfl⟩
        rcases hl : (((presentIds w).filterMap fun c' => (w.cells c').map fun cell =>
            ((Key.cell c', Slot.cell cell) : Key × Slot R TxId D)).filter
              (fun e => decide (e.1 = Key.cell c))).getLast? with _ | e
        · exfalso
          have hpres := (mem_keys_cell w c).1 hk
          rcases hw : w.cells c with _ | cell
          · exact hpres hw
          · have hin : (Key.cell c, Slot.cell cell) ∈ (((presentIds w).filterMap fun c' =>
                (w.cells c').map fun cell =>
                  ((Key.cell c', Slot.cell cell) : Key × Slot R TxId D)).filter
                  (fun e => decide (e.1 = Key.cell c))) :=
              List.mem_filter.mpr ⟨List.mem_filterMap.mpr
                ⟨c, (mem_presentIds w c).2 hpres, by simp [hw]⟩, by simp⟩
            rw [List.getLast?_eq_none_iff] at hl
            simp [hl] at hin
        · obtain ⟨cell, hw, rfl⟩ := hsub e (List.mem_of_getLast? hl)
          simp [hw, hl]
  · have absent : AuthTrie.lastVal (entries w) k = none := by
      cases h : AuthTrie.lastVal (entries w) k with
      | none => rfl
      | some x =>
          exfalso
          obtain ⟨e, he, hek⟩ := (AuthTrie.lastVal_isSome (es := entries w) (k := k)).mp (by rw [h]; rfl)
          exact hk (by rw [← hek]; exact List.mem_map_of_mem he)
    rw [absent]
    cases k with
    | system => exact absurd (system_mem_keys w) hk
    | cell c =>
        have : w.cells c = none := by
          by_contra h
          exact hk ((mem_keys_cell w c).2 h)
        simp [this]

variable (dig : AuthTrie.NodeIn Key V Dg → Dg) (ix : Key → List Bool) (L : Nat)

/-- The world's slot roots: the system slot, then every present cell. -/
def slotRoots (w : World R TxId D) : List (Key × V) :=
  (entries w).map fun e => (e.1, slotRoot cellRoot sysRoot e.2)

/-- **The world root**: the compressed trie over the slot roots. -/
def rootOf (w : World R TxId D) : Dg := AuthTrie.root dig ix L (slotRoots cellRoot sysRoot w)

omit [DecidableEq V] in
theorem lastVal_slotRoots (w : World R TxId D) (k : Key) :
    AuthTrie.lastVal (slotRoots cellRoot sysRoot w) k =
      (AuthTrie.lastVal (entries w) k).map (slotRoot cellRoot sysRoot) :=
  AuthTrie.lastVal_map _ _ k

/-- Index paths do not collide among one world's keys. -/
def IndexInjective (w : World R TxId D) : Prop :=
  ∀ k ∈ keys w, ∀ k' ∈ keys w, ix k = ix k' → k = k'

omit [DecidableEq V] in
theorem pathsInjective {w : World R TxId D} (hix : IndexInjective ix w) :
    AuthTrie.Cache.PathsInjective ix (slotRoots cellRoot sysRoot w) := by
  have mem : ∀ k, (AuthTrie.lastVal (slotRoots cellRoot sysRoot w) k).isSome → k ∈ keys w := by
    intro k h
    obtain ⟨e, he, rfl⟩ := AuthTrie.lastVal_isSome.mp h
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact List.mem_map_of_mem hx
  intro k k' hk hk' same
  exact hix k (mem k hk) k' (mem k' hk') same

theorem world_ext {w w' : World R TxId D} (hc : ∀ c, w.cells c = w'.cells c)
    (hs : w.system = w'.system) : w = w' := by
  rcases w with ⟨cells, system⟩
  rcases w' with ⟨cells', system'⟩
  simp only at hc hs
  subst hs
  have : cells = cells' := DFinsupp.ext hc
  subst this
  rfl

omit [DecidableEq V] in
/-- Two worlds giving every key the same slot root, whose leaf roots separate
their contents, are equal. -/
theorem eq_of_lastVals {w w' : World R TxId D}
    (cells : ∀ c a b, w.cells c = some a → w'.cells c = some b → cellRoot a = cellRoot b → a = b)
    (system : sysRoot w.system = sysRoot w'.system → w.system = w'.system)
    (hl : ∀ k, AuthTrie.lastVal (slotRoots cellRoot sysRoot w') k =
      AuthTrie.lastVal (slotRoots cellRoot sysRoot w) k) :
    w = w' := by
  have read : ∀ k, (AuthTrie.lastVal (entries w') k).map (slotRoot cellRoot sysRoot) =
      (AuthTrie.lastVal (entries w) k).map (slotRoot cellRoot sysRoot) := by
    intro k
    have := hl k
    rwa [lastVal_slotRoots, lastVal_slotRoots] at this
  refine world_ext (fun c => ?_) ?_
  · have := read (Key.cell c)
    rw [lastVal_entries w, lastVal_entries w'] at this
    rcases ha : w.cells c with _ | a <;> rcases hb : w'.cells c with _ | b <;>
      simp only [ha, hb, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
        slotRoot] at this ⊢
    exact (cells c a b ha hb this.symm)
  · have := read Key.system
    rw [lastVal_entries w, lastVal_entries w'] at this
    simp only [Option.map_some, Option.some.injEq, slotRoot] at this
    exact system this.symm

/-- **The carrier** for comparing two worlds by root.  Each field names only
the pairs the comparison uses:
* `openings` — at every key, the honest opening of `w'`, checked against `w`'s
  root, reads what `w` reads (the node inputs one opening check compares);
* `index'` — no two keys of `w'` share an index path (so its honest openings exist);
* `cells`, `system` — the leaf roots separate the two worlds' contents at the
  same slot. -/
structure RootBinding (lengths : ∀ k, (ix k).length = L) (w w' : World R TxId D) : Prop where
  openings : ∀ k, AuthTrie.verify dig ix (rootOf cellRoot sysRoot dig ix L w) k
      (AuthTrie.lastVal (slotRoots cellRoot sysRoot w') k)
      ((AuthTrie.Cache.build (dig := dig) lengths (slotRoots cellRoot sysRoot w')).opening k) = true →
    AuthTrie.lastVal (slotRoots cellRoot sysRoot w') k = AuthTrie.lastVal (slotRoots cellRoot sysRoot w) k
  index' : IndexInjective ix w'
  cells : ∀ c a b, w.cells c = some a → w'.cells c = some b → cellRoot a = cellRoot b → a = b
  system : sysRoot w.system = sysRoot w'.system → w.system = w'.system

/-- **Binding.**  Under the carrier, equal world roots mean equal worlds. -/
theorem rootOf_binds (lengths : ∀ k, (ix k).length = L) {w w' : World R TxId D}
    (hb : RootBinding cellRoot sysRoot dig ix L lengths w w')
    (hr : rootOf cellRoot sysRoot dig ix L w = rootOf cellRoot sysRoot dig ix L w') : w = w' := by
  refine eq_of_lastVals cellRoot sysRoot hb.cells hb.system (fun k => hb.openings k ?_)
  have built := AuthTrie.Cache.build_holds (dig := dig) lengths (slotRoots cellRoot sysRoot w')
  have opened := AuthTrie.Cache.opening_complete lengths built
    (pathsInjective cellRoot sysRoot ix hb.index') k
  have root : (AuthTrie.Cache.build (dig := dig) lengths (slotRoots cellRoot sysRoot w')).digest =
      rootOf cellRoot sysRoot dig ix L w := (AuthTrie.Cache.digest_eq built).trans hr.symm
  rwa [root] at opened

/-- **Satisfiable at every hash:** a world against itself meets the carrier
whenever its own keys do not collide in the index. -/
theorem rootBinding_self (lengths : ∀ k, (ix k).length = L) (w : World R TxId D)
    (hix : IndexInjective ix w) : RootBinding cellRoot sysRoot dig ix L lengths w w where
  openings := fun _ _ => rfl
  index' := hix
  cells := fun _ _ _ ha hb _ => Option.some.inj (ha.symm.trans hb)
  system := fun _ => rfl

/-- The carrier holds when no two node inputs share a digest and neither
world's keys collide in the index. -/
theorem rootBinding_of_noCollision (lengths : ∀ k, (ix k).length = L) {w w' : World R TxId D}
    (nodes : ¬ AuthTrie.Collision dig) (hix : IndexInjective ix w) (hix' : IndexInjective ix w')
    (cells : ∀ c a b, w.cells c = some a → w'.cells c = some b → cellRoot a = cellRoot b → a = b)
    (system : sysRoot w.system = sysRoot w'.system → w.system = w'.system) :
    RootBinding cellRoot sysRoot dig ix L lengths w w' where
  openings := fun k accepted => by
    rcases AuthTrie.verify_sound dig ix L lengths _
        (AuthTrie.Cache.wf_canon lengths (pathsInjective cellRoot sysRoot ix hix)) k _ _ accepted with
      read | collision
    · rwa [AuthTrie.Cache.lookup_canon] at read
    · exact absurd (AuthTrie.CollisionAmong.global dig collision) nodes
  index' := hix'
  cells := cells
  system := system

/-- **The reduction, with no premise.**  Different worlds with one root exhibit
one of: two distinct node inputs with one digest; two keys of one world at one
index path; two different cells at one id with one cell root; two different
system cells with one system root. -/
theorem rootOf_eq_exhibits_collision (lengths : ∀ k, (ix k).length = L) {w w' : World R TxId D}
    (hr : rootOf cellRoot sysRoot dig ix L w = rootOf cellRoot sysRoot dig ix L w') (hne : w ≠ w') :
    AuthTrie.Collision dig ∨ ¬ IndexInjective ix w ∨ ¬ IndexInjective ix w' ∨
      (∃ c a b, w.cells c = some a ∧ w'.cells c = some b ∧ a ≠ b ∧ cellRoot a = cellRoot b) ∨
      (w.system ≠ w'.system ∧ sysRoot w.system = sysRoot w'.system) := by
  by_contra hno
  simp only [not_or, not_exists, not_and, not_not] at hno
  obtain ⟨hH, hix, hix', hcells, hsys⟩ := hno
  exact hne (rootOf_binds cellRoot sysRoot dig ix L lengths
    (rootBinding_of_noCollision cellRoot sysRoot dig ix L lengths hH hix hix'
      (fun c a b ha hb he => by_contra fun hab => hcells c a b ha hb hab he)
      (fun he => by_contra fun hs => hsys hs he)) hr)

/-- **Checkpoint soundness at the world root (§4.4).**  `Kernel.World.resume_sound`
with the root supplied and its `binds` premise discharged by the carrier. -/
theorem resume_sound_rootOf {Ev : Type} (H : History R TxId Ev D) (lengths : ∀ k, (ix k).length = L)
    (g W_h : World R TxId D) (log : List (Turn R TxId Ev D)) (c : Checkpoint R TxId D Dg)
    (prefixed : fold H g (log.take c.height) = some W_h)
    (honestRoot : c.root = rootOf cellRoot sysRoot dig ix L W_h)
    (carrier : RootBinding cellRoot sysRoot dig ix L lengths c.world W_h)
    (checks : c.check (rootOf cellRoot sysRoot dig ix L) = true) :
    c.resume H (rootOf cellRoot sysRoot dig ix L) (log.drop c.height) = fold H g log :=
  resume_sound H (rootOf cellRoot sysRoot dig ix L) g W_h log c prefixed honestRoot
    (rootOf_binds cellRoot sysRoot dig ix L lengths carrier) checks

end WorldRoot

/-! ## The deployed root -/

section Deployed

open Minidregg.Compiler.Sp800185Cshake256

/-- The registered world-root tag (`PersistedCodecTags.world_root_v2`): it enters the persisted
codec corpus, so the Store epoch's schema component moves with it and a Store of the v1 root
refuses to open naming `schema-refs`. -/
def worldCustomization : List UInt8 := Minidregg.Compiler.PersistedCodecTags.world_root_v2.toUTF8.toList

/-- The deployed hash: cSHAKE256 under the world-root customization. -/
def deployedHash (x : List UInt8) : Digest := (hash worldCustomization x).digest

/-- A node of the deployed trie: keys, slot-root digests, child digests. -/
abbrev Node := AuthTrie.NodeIn Key Digest Digest

/-- A node's hash input: a tag byte, then its fields, each prefix-free. -/
def nodeBytes : Node → List UInt8
  | .empty => [0]
  | .leaf k v => 1 :: (keyBytes k ++ digestStream.encode v)
  | .branch l r => 2 :: (digestStream.encode l ++ digestStream.encode r)

theorem nodeBytes_injective : Function.Injective nodeBytes := by
  intro a b h
  cases a with
  | empty => cases b <;> simp_all [nodeBytes]
  | leaf k v =>
      cases b with
      | empty => simp [nodeBytes] at h
      | branch => simp [nodeBytes] at h
      | leaf k' v' =>
          simp only [nodeBytes, List.cons.injEq, true_and] at h
          obtain ⟨hk, hv⟩ := keyBytes_prefixFree k k' _ _ h
          rw [hk, (streamPrefixFree digestStream).injective hv]
  | branch l r =>
      cases b with
      | empty => simp [nodeBytes] at h
      | leaf => simp [nodeBytes] at h
      | branch l' r' =>
          simp only [nodeBytes, List.cons.injEq, true_and] at h
          obtain ⟨hl, hr⟩ := streamPrefixFree digestStream l l' _ _ h
          rw [hl, (streamPrefixFree digestStream).injective hr]

/-- The empty node's digest, computed once. -/
def emptyDigest : Digest := deployedHash (nodeBytes .empty)

/-- **The deployed node hash.** -/
def worldDig : Node → Digest
  | .empty => emptyDigest
  | .leaf k v => deployedHash (nodeBytes (.leaf k v))
  | .branch l r => deployedHash (nodeBytes (.branch l r))

theorem worldDig_eq : ∀ n : Node, worldDig n = deployedHash (nodeBytes n)
  | .empty => rfl
  | .leaf .. => rfl
  | .branch .. => rfl

/-- A node collision is a collision of the deployed hash on two distinct inputs. -/
theorem worldDig_collision (h : AuthTrie.Collision worldDig) :
    ∃ x y, x ≠ y ∧ deployedHash x = deployedHash y := by
  obtain ⟨a, b, hne, heq⟩ := h
  exact ⟨nodeBytes a, nodeBytes b, fun e => hne (nodeBytes_injective e), by
    rwa [worldDig_eq, worldDig_eq] at heq⟩

/-- A3's Q2 index: the 256 bits of the hash of the tagged key bytes. -/
def deployedIx (k : Key) : List Bool := bytesBits (cshake256Bytes worldCustomization (3 :: keyBytes k))

theorem deployedIx_length (k : Key) : (deployedIx k).length = 256 := by
  simp [deployedIx, bytesBits_length]

/-- An index collision of two distinct keys is a collision of the deployed hash
on two distinct inputs. -/
theorem deployedIx_collision {k k' : Key} (hne : k ≠ k') (h : deployedIx k = deployedIx k') :
    (3 :: keyBytes k) ≠ (3 :: keyBytes k') ∧
      deployedHash (3 :: keyBytes k) = deployedHash (3 :: keyBytes k') := by
  refine ⟨fun e => hne (keyBytes_prefixFree.injective (List.cons.inj e).2), ?_⟩
  have hb := bytesBits_injective h
  show digestOfBytesLE (cshake256Bytes worldCustomization (3 :: keyBytes k)) =
    digestOfBytesLE (cshake256Bytes worldCustomization (3 :: keyBytes k'))
  rw [hb]

/-- **The deployed root** of an entry list of slot roots: the compressed trie
over each key's last value. -/
def deployedRoot (es : List (Key × Digest)) : Digest := AuthTrie.root worldDig deployedIx 256 es

/-- The deployed root over one-pass canonicalization. -/
def deployedRootFast (es : List (Key × Digest)) : Digest := AuthTrie.rootFast worldDig deployedIx 256 es

/-- Compiled deployed roots use the hash-map canonicalizer; proofs keep the specification. -/
@[csimp] theorem deployedRoot_eq_deployedRootFast : @deployedRoot = @deployedRootFast := by
  funext es
  exact AuthTrie.root_eq_rootFast worldDig deployedIx 256 es

/-- The deployed root depends only on each key's last value. -/
theorem deployedRoot_congr {es es' : List (Key × Digest)}
    (same : ∀ k, AuthTrie.lastVal es k = AuthTrie.lastVal es' k) : deployedRoot es = deployedRoot es' :=
  AuthTrie.root_congr worldDig deployedIx 256 same

/-- Distinct keys of any list have distinct paths, up to a deployed-hash collision. -/
theorem deployed_paths (es : List (Key × Digest)) :
    AuthTrie.Cache.PathsInjective deployedIx es ∨ ∃ x y, x ≠ y ∧ deployedHash x = deployedHash y := by
  by_cases h : AuthTrie.Cache.PathsInjective deployedIx es
  · exact Or.inl h
  · right
    simp only [AuthTrie.Cache.PathsInjective, not_forall] at h
    obtain ⟨k, k', _, _, same, hne⟩ := h
    exact ⟨_, _, deployedIx_collision hne same⟩

/-- **Binding of the deployed root, premise-free.**  Two lists with one deployed
root give every key the same last value, or the deployed hash collides. -/
theorem deployedRoot_binds {es es' : List (Key × Digest)} (hr : deployedRoot es = deployedRoot es')
    (k : Key) :
    AuthTrie.lastVal es' k = AuthTrie.lastVal es k ∨ ∃ x y, x ≠ y ∧ deployedHash x = deployedHash y := by
  rcases deployed_paths es with inj | c
  · rcases deployed_paths es' with inj' | c
    · rcases AuthTrie.Cache.root_lastVal_eq deployedIx_length inj inj' hr k with same | c
      · exact Or.inl same
      · exact Or.inr (worldDig_collision (AuthTrie.CollisionAmong.global _ c))
    · exact Or.inr c
  · exact Or.inr c

end Deployed

/-! ## The turn digest and the log chain -/

section History

open Minidregg.Compiler.Sp800185Cshake256

def turnCustomization : List UInt8 := "DREGG.TURN/v1".toUTF8.toList
def logCustomization : List UInt8 := "DREGG.LOG/v1".toUTF8.toList

/-- The digest of a turn's canonical bytes. -/
def turnDigestOfBytes (bytes : List UInt8) : Digest := (hash turnCustomization bytes).digest

/-- One link of the log chain. -/
def chainDigest (acc turn : Digest) : Digest :=
  (hash logCustomization (digestStream.encode acc ++ digestStream.encode turn)).digest

/-- The history surface `Kernel.World` handed on, at the deployed hash: the
turn digest is cSHAKE over the turn's canonical bytes; the chain links it to
the previous log root; a pin compares `cellDigest` (the deployed per-cell
root of the slot's canonical bytes). -/
def cshakeHistory {R : Registry} {TxId Ev : Type} (encode : Turn R TxId Ev Digest → List UInt8)
    (logRoot0 : Digest) (legBytes : Leg R → Nat) (imageBytes : Cell R → Nat)
    (eventBytes : Ev → Nat) (cellDigest : Option (Cell R) → Digest) : History R TxId Ev Digest where
  turnDigest t := turnDigestOfBytes (encode t)
  chain := chainDigest
  logRoot0 := logRoot0
  legBytes := legBytes
  imageBytes := imageBytes
  eventBytes := eventBytes
  cellDigest := cellDigest

/-- `classify_conflict`'s `separates` premise at the deployed history: two turns
with different canonical bytes, where the hash binds that one pair. -/
theorem cshakeHistory_separates {R : Registry} {TxId Ev : Type}
    (encode : Turn R TxId Ev Digest → List UInt8) (logRoot0 : Digest) (legBytes : Leg R → Nat)
    (imageBytes : Cell R → Nat) (eventBytes : Ev → Nat) (cellDigest : Option (Cell R) → Digest)
    {t t' : Turn R TxId Ev Digest}
    (hne : encode t ≠ encode t')
    (binds : turnDigestOfBytes (encode t) = turnDigestOfBytes (encode t') → encode t = encode t') :
    (cshakeHistory encode logRoot0 legBytes imageBytes eventBytes cellDigest).turnDigest t ≠
      (cshakeHistory encode logRoot0 legBytes imageBytes eventBytes cellDigest).turnDigest t' :=
  fun h => hne (binds h)

end History

/-! ## Poles: the honest checkpoint resumes; a tampered one passes a non-binding root -/

namespace Example

open Minidregg.Kernel.World.Example

/-- Two index bits: the system slot at `00`, cells 0, 1, 2 at `01`, `10`, `11`. -/
def toyIx : Key → List Bool
  | .system => [false, false]
  | .cell c => [decide ((c + 1) / 2 % 2 = 1), decide ((c + 1) % 2 = 1)]

theorem toyIx_length (k : Key) : (toyIx k).length = 2 := by cases k <;> rfl

/-- A constant node hash: deliberately NOT binding. -/
def toyDig : AuthTrie.NodeIn Key Nat Nat → Nat := fun _ => 0

/-- A cell's toy root: its value at key 0. -/
def toyCellRoot (cell : Cell toyR) : Nat :=
  (((cell.storeAt false).bind fun s => s ⟨(), (0 : Nat)⟩ : Option Nat)).getD 0

/-- The system cell's toy root: the height. -/
def toySysRoot (s : Store (sysLayout Nat Nat)) : Nat :=
  ((s ⟨SysSpace.head, ()⟩).map fun hv => hv.1).getD 0

abbrev toyRootOf : ToyWorld → Nat := rootOf toyCellRoot toySysRoot toyDig toyIx 2

theorem w1_index : IndexInjective toyIx w1 := by unfold IndexInjective; decide +kernel

def honestCk : Checkpoint toyR Nat Nat Nat := ⟨1, w1, toyRootOf w1⟩

/-- **Satisfiable pole.**  The honest checkpoint checks, meets the carrier (at
this non-binding hash too: `rootBinding_self`), and resumes to the fold. -/
theorem honest_checkpoint_resumes :
    honestCk.check toyRootOf = true ∧
      honestCk.resume toyH toyRootOf (log2.drop honestCk.height) = fold toyH g log2 :=
  ⟨by decide +kernel,
    resume_sound_rootOf toyCellRoot toySysRoot toyDig toyIx 2 toyH toyIx_length g w1 log2 honestCk
      w1_prefix rfl (rootBinding_self toyCellRoot toySysRoot toyDig toyIx 2 toyIx_length w1 w1_index)
      (by decide +kernel)⟩

theorem tampered_root_eq : toyRootOf tamperedWorld = toyRootOf w1 := by decide +kernel

def tamperedCk : Checkpoint toyR Nat Nat Nat := ⟨1, tamperedWorld, toyRootOf w1⟩

/-- **Refuting pole.**  At the non-binding hash a tampered world carries the
honest root: the checkpoint checks, its resume disagrees with the fold from
genesis, and the carrier fails.  So `resume_sound_rootOf`'s carrier premise is
load-bearing. -/
theorem tampered_checkpoint_accepted :
    tamperedCk.check toyRootOf = true ∧
      ((tamperedCk.resume toyH toyRootOf (log2.drop 1)).map fun w => val w 1) ≠
        (fold toyH g log2).map (fun w => val w 1) ∧
      ¬ RootBinding toyCellRoot toySysRoot toyDig toyIx 2 toyIx_length tamperedWorld w1 := by
  refine ⟨by decide +kernel, by decide +kernel, fun hb => ?_⟩
  have heq := rootOf_binds toyCellRoot toySysRoot toyDig toyIx 2 toyIx_length hb tampered_root_eq
  have hv : val tamperedWorld 1 ≠ val w1 1 := by decide +kernel
  exact hv (by rw [heq])

end Example

/-! ## Axiom pins -/

#assert_axioms streamPrefixFree
#assert_axioms keyBytes_prefixFree
#assert_axioms byteBits_injective
#assert_axioms bytesBits_injective
#assert_axioms mem_presentIds
#assert_axioms mem_keys_cell
#assert_axioms system_mem_keys
#assert_axioms lastVal_entries
#assert_axioms pathsInjective
#assert_axioms world_ext
#assert_axioms eq_of_lastVals
#assert_axioms rootOf_binds
#assert_axioms rootBinding_self
#assert_axioms rootBinding_of_noCollision
#assert_axioms rootOf_eq_exhibits_collision
#assert_axioms resume_sound_rootOf
#assert_axioms nodeBytes_injective
#assert_axioms worldDig_collision
#assert_axioms deployedIx_collision
#assert_axioms deployedRoot_eq_deployedRootFast
#assert_axioms deployedRoot_congr
#assert_axioms deployed_paths
#assert_axioms deployedRoot_binds
#assert_axioms cshakeHistory_separates
#assert_axioms Example.w1_index
#assert_axioms Example.honest_checkpoint_resumes
#assert_axioms Example.tampered_root_eq
#assert_axioms Example.tampered_checkpoint_accepted

end Minidregg.Kernel.WorldRoot
