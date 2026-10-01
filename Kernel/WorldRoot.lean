/-
# Kernel.WorldRoot -- the world root: an authenticated map over cell roots

DATAMODEL §3.2/§3.4, step C1.  The world root is `Theory.AuthMap`'s two-level
form: an authenticated map whose keys are the world's slots (`Key.system` and
`Key.cell c`) and whose leaves are the slots' roots.  `Kernel.World` left the
root function a parameter of `Checkpoint`; this module supplies it.

* `slotsOf ix es` is the slot map of an entry list (the last entry at each index
  path).  `entryRoot S leafRoot es := worldRoot S leafRoot (slotsOf S.ix es)` is
  A3's `worldRoot` over it, so `world_opening`, `worldRoot_write` and
  `world_sound` apply to every root this module defines.
* `sparse` evaluates `Scheme.root` in one hash per nonempty tree node instead of
  one per node of the full tree (`entryRoot_eq_sparse`).  It is what runs.
* `rootOf cellRoot sysRoot S w` is the root of a `Kernel.World`: the system cell
  at `Key.system`, each present cell at `Key.cell c`.
* **Binding.**  `rootOf_binds` turns root equality into world equality under
  `RootBinding`, which is A3's `PathBinding` at every key plus the index and
  leaf-root carriers, each scoped to the pairs the comparison names.
  `rootOf_eq_exhibits_collision` is the same fact with no premise: equal roots
  of different worlds exhibit an explicit collision.  `resume_sound_rootOf` is
  `Kernel.World.resume_sound` with its `binds` premise discharged this way.
* `deployed` is the scheme the host runs: cSHAKE256 under
  `DREGG.WORLD-ROOT/v1`, a 256-bit hashed index (A3's Q2), digests framed by
  `digestStream`.  `deployedIx_collision` reduces an index collision to a hash
  collision.
* `cshakeHistory` is the turn digest and log chain `Kernel.World.History`
  handed on: cSHAKE over a turn's canonical bytes, chained.

Poles (toy scheme at a one-bit hash, over `Kernel.World`'s toy worlds):
`honest_checkpoint_resumes` (the carrier holds at the honest checkpoint at
every hash) and `tampered_checkpoint_accepted` (a tampered world with the
honest root: the check passes, the resume disagrees with the fold, and the
carrier fails).
-/
import Theory.AuthMap
import Kernel.World
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Kernel.WorldRoot

open Minidregg.Theory.AuthMap
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
  deriving DecidableEq, Repr

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

/-! ## The slot map of an entry list -/

section Entries

variable {K C : Type} [DecidableEq K] (ix : K → List Bool)

/-- The slot map of an entry list: at each index path, the last entry whose
key indexes there.  A function of the list; `lookup` reads it. -/
def slotsOf (es : List (K × C)) : Map K C :=
  fun p => (es.filter fun e => decide (ix e.1 = p)).getLast?

omit [DecidableEq K] in
theorem slotsOf_wf (es : List (K × C)) : WF ix (slotsOf ix es) := by
  intro p k x h
  have hm := List.mem_of_getLast? h
  simp only [List.mem_filter, decide_eq_true_eq] at hm
  exact hm.2

/-- Reading key `k` returns the last entry at `k`, when no other entry key
shares `k`'s index. -/
theorem lookup_slotsOf (es : List (K × C)) (k : K)
    (hix : ∀ e ∈ es, ix e.1 = ix k → e.1 = k) :
    lookup ix (slotsOf ix es) k = ((es.filter fun e => decide (e.1 = k)).getLast?).map (·.2) := by
  have hf : (es.filter fun e => decide (ix e.1 = ix k)) = es.filter fun e => decide (e.1 = k) := by
    apply List.filter_congr
    intro e he
    by_cases h : e.1 = k
    · simp [h]
    · simp only [h, decide_false, decide_eq_false_iff_not]
      exact fun hi => h (hix e he hi)
  unfold lookup slotsOf
  rw [hf]
  rcases hl : (es.filter fun e => decide (e.1 = k)).getLast? with _ | ⟨k', x⟩
  · simp [hl, readAt]
  · have hm := List.mem_of_getLast? hl
    simp only [List.mem_filter, decide_eq_true_eq] at hm
    simp [hl, readAt, hm.2]

theorem worldSlots_slotsOf {V : Type} (leafRoot : C → V) (es : List (K × C)) :
    worldSlots leafRoot (slotsOf ix es) = slotsOf ix (es.map fun e => (e.1, leafRoot e.2)) := by
  funext p
  simp only [worldSlots, slotsOf, List.filter_map, List.getLast?_map]
  rfl

end Entries

/-! ## Evaluating the root sparsely -/

section Sparse

variable {K V D : Type} [DecidableEq K] (S : Scheme K V D)

/-- The root of the empty subtree with `i` levels. -/
def empties : Nat → D
  | 0 => S.leafDigest none
  | i + 1 => S.nodeHash (empties i) (empties i)

theorem subRoot_empty : ∀ (i : Nat) (p : List Bool), S.subRoot Map.empty i p = empties S i
  | 0, _ => rfl
  | i + 1, p => by simp only [Scheme.subRoot, empties, subRoot_empty i]

/-- Entries below one branch, with the branch bit removed. -/
def strip (b : Bool) (e : List Bool × (K × V)) : Option (List Bool × (K × V)) :=
  match e.1 with
  | c :: r => if c = b then some (r, e.2) else none
  | [] => none

/-- The root of the subtree with `i` levels holding the given (remaining path,
entry) pairs.  An empty subtree costs a table lookup; a nonempty one costs one
node hash plus its children. -/
def sparse (E : Nat → D) : Nat → List (List Bool × (K × V)) → D
  | 0, L => S.leafDigest (L.getLast?.map (·.2))
  | i + 1, L =>
    if L.isEmpty then E (i + 1)
    else S.nodeHash (sparse E i (L.filterMap (strip false))) (sparse E i (L.filterMap (strip true)))

omit [DecidableEq K] in
theorem filter_strip (b : Bool) (q : List Bool) :
    ∀ L : List (List Bool × (K × V)),
      ((L.filterMap (strip b)).filter fun e => decide (e.1 = q)).map (·.2) =
        (L.filter fun e => decide (e.1 = b :: q)).map (·.2)
  | [] => rfl
  | e :: L => by
      rcases e with ⟨bits, entry⟩
      have ih := filter_strip b q L
      cases bits with
      | nil =>
          rw [List.filterMap_cons, show strip b (([] : List Bool), entry) = none from rfl]
          simpa using ih
      | cons c r =>
          rw [List.filterMap_cons,
            show strip b ((c :: r, entry) : List Bool × (K × V)) =
              if c = b then some (r, entry) else none from rfl]
          by_cases hc : c = b
          · subst hc
            rw [if_pos rfl]
            by_cases hr : r = q
            · subst hr; simp [ih]
            · simp [List.filter_cons, hr, ih]
          · rw [if_neg hc]; simp [List.filter_cons, hc, ih]

/-- `L` represents the subtree of `m` at prefix `p` with `i` levels. -/
def Represents (m : Map K V) (p : List Bool) (i : Nat) (L : List (List Bool × (K × V))) : Prop :=
  (∀ e ∈ L, e.1.length = i) ∧
    ∀ q : List Bool, q.length = i → m (p ++ q) = ((L.filter fun e => decide (e.1 = q)).getLast?).map (·.2)

theorem sparse_eq (E : Nat → D) (hE : ∀ i, E i = empties S i) :
    ∀ (i : Nat) (p : List Bool) (L : List (List Bool × (K × V))) (m : Map K V),
      Represents m p i L → sparse S E i L = S.subRoot m i p
  | 0, p, L, m, ⟨hlen, hm⟩ => by
      have hall : (L.filter fun e => decide (e.1 = [])) = L := by
        apply List.filter_eq_self.mpr
        intro e he
        simpa using List.length_eq_zero_iff.mp (hlen e he)
      have := hm [] rfl
      rw [hall, List.append_nil] at this
      simp only [sparse, Scheme.subRoot, this]
  | i + 1, p, L, m, ⟨hlen, hm⟩ => by
      by_cases hL : L.isEmpty
      · have hnil : L = [] := List.isEmpty_iff.mp hL
        subst hnil
        simp only [sparse, List.isEmpty_nil, if_true, hE]
        rw [← subRoot_empty S (i + 1) p]
        apply S.subRoot_congr
        intro q hq
        simp [hm q hq, Map.empty]
      · simp only [sparse, hL, Bool.false_eq_true, if_false, Scheme.subRoot]
        have rep : ∀ b : Bool, Represents m (p ++ [b]) i (L.filterMap (strip b)) := by
          intro b
          refine ⟨?_, ?_⟩
          · intro e he
            rcases List.mem_filterMap.mp he with ⟨e0, he0, hs⟩
            rcases e0 with ⟨bits, entry⟩
            cases bits with
            | nil => simp [strip] at hs
            | cons c r =>
                simp only [strip] at hs
                split_ifs at hs
                cases hs
                have := hlen _ he0
                simpa using this
          · intro q hq
            have h1 := hm (b :: q) (by simp [hq])
            rw [List.append_assoc, List.singleton_append, h1, ← List.getLast?_map, ← List.getLast?_map,
              filter_strip]
        rw [sparse_eq E hE i (p ++ [false]) _ m (rep false),
          sparse_eq E hE i (p ++ [true]) _ m (rep true)]

/-- The root of an entry list, evaluated sparsely. -/
def sparseRoot (E : Nat → D) (es : List (K × V)) : D :=
  sparse S E S.depth (es.map fun e => (S.ix e.1, e))

theorem sparseRoot_eq (E : Nat → D) (hE : ∀ i, E i = empties S i) (es : List (K × V)) :
    sparseRoot S E es = S.root (slotsOf S.ix es) := by
  apply sparse_eq S E hE
  refine ⟨?_, ?_⟩
  · intro e he
    rcases List.mem_map.mp he with ⟨e0, _, rfl⟩
    exact S.ix_length _
  · intro q _
    simp only [slotsOf, List.nil_append, List.filter_map, List.map_map, ← List.getLast?_map]
    congr 1
    simp only [Function.comp_def, List.map_id']
    exact List.filter_congr (fun x _ => by simp)

/-- A table of empty-subtree roots, `table[i] = empties i`. -/
def emptyTable (n : Nat) : Array D :=
  (List.iterate (fun e => S.nodeHash e e) (S.leafDigest none) n).toArray

theorem empties_iterate : ∀ i, empties S i = (fun e => S.nodeHash e e)^[i] (S.leafDigest none)
  | 0 => rfl
  | i + 1 => by rw [Function.iterate_succ_apply', ← empties_iterate i]; rfl

/-- The table-backed lookup that `sparse` runs with. -/
def tableEmpties (table : Array D) (i : Nat) : D := (table[i]?).getD (empties S i)

theorem tableEmpties_emptyTable (n i : Nat) : tableEmpties S (emptyTable S n) i = empties S i := by
  unfold tableEmpties emptyTable
  by_cases hi : i < n
  · have hlen : i < (List.iterate (fun e => S.nodeHash e e) (S.leafDigest none) n).length := by
      simpa using hi
    rw [List.getElem?_toArray, List.getElem?_eq_getElem hlen, List.getElem_iterate, Option.getD_some,
      empties_iterate]
  · rw [List.getElem?_toArray, List.getElem?_eq_none (by simpa using hi)]; rfl

end Sparse

/-! ## The root of an entry list, and why it binds -/

section Binding

variable {K C V D : Type} [DecidableEq K] [DecidableEq D] (S : Scheme K V D) (leafRoot : C → V)

/-- A3's two-level `worldRoot` over the slot map of an entry list. -/
def entryRoot (es : List (K × C)) : D := worldRoot S leafRoot (slotsOf S.ix es)

omit [DecidableEq D] in
theorem entryRoot_eq_sparse (E : Nat → D) (hE : ∀ i, E i = empties S i) (es : List (K × C)) :
    entryRoot S leafRoot es = sparseRoot S E (es.map fun e => (e.1, leafRoot e.2)) := by
  rw [sparseRoot_eq S E hE, entryRoot, worldRoot, worldSlots_slotsOf]

/-- The carrier at a pair of slot maps: at every key, the opening in `m'`
checked against `m`'s root meets A3's `PathBinding`.  It names, per key, the
pairs of hash inputs one opening check compares; it is not global injectivity. -/
def MapBinding (m m' : Map K V) : Prop :=
  ∀ k, S.PathBinding m k (lookup S.ix m' k) (S.opening m' k)

omit [DecidableEq D] in
/-- Satisfiable at every hash: a map against itself (A3's `honest_binding`). -/
theorem mapBinding_self (m : Map K V) : MapBinding S m m := fun k => S.honest_binding m k

/-- Under the carrier, one root means one logical map. -/
theorem lookup_eq_of_root_eq {m m' : Map K V} (hb : MapBinding S m m')
    (hr : S.root m = S.root m') (k : K) : lookup S.ix m' k = lookup S.ix m k := by
  have hv := S.verify_opening m' k
  rw [← hr] at hv
  exact S.verify_sound m k _ _ (hb k) hv

/-- With no premise: two maps with one root and different readings at a key
exhibit two distinct inputs of `H` with one digest. -/
theorem root_eq_exhibits_collision {m m' : Map K V} (hr : S.root m = S.root m') (k : K)
    (hne : lookup S.ix m' k ≠ lookup S.ix m k) : ∃ x y, x ≠ y ∧ S.H x = S.H y := by
  have hv := S.verify_opening m' k
  rw [← hr] at hv
  obtain ⟨_, _, x, y, _, hxy, hH⟩ := S.forgery_exhibits_collision m k _ _ hv hne
  exact ⟨x, y, hxy, hH⟩

end Binding

/-! ## The world instance -/

section WorldRoot

variable {R : Registry} {TxId D : Type} [DecidableEq TxId] [DecidableEq D]
variable {V Dg : Type} [DecidableEq Dg]

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

/-- **The world root.**  A3's `worldRoot` over (slot ↦ slot root). -/
def rootOf (S : Scheme Key V Dg) (w : World R TxId D) : Dg :=
  entryRoot S (slotRoot cellRoot sysRoot) (entries w)

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
def IndexInjective (S : Scheme Key V Dg) (w : World R TxId D) : Prop :=
  ∀ k ∈ keys w, ∀ k' ∈ keys w, S.ix k = S.ix k' → k = k'

theorem system_mem_keys (w : World R TxId D) : Key.system ∈ keys w := by
  simp [keys, entries]

/-- A slot map never reads a key no entry carries. -/
theorem lookup_slotsOf_absent {K C : Type} [DecidableEq K] (ix : K → List Bool)
    (es : List (K × C)) (k : K) (habs : ∀ e ∈ es, e.1 ≠ k) : lookup ix (slotsOf ix es) k = none := by
  unfold lookup slotsOf
  rcases hl : (es.filter fun e => decide (ix e.1 = ix k)).getLast? with _ | ⟨k', x⟩
  · simp [hl, readAt]
  · have hm := List.mem_of_getLast? hl
    simp only [List.mem_filter] at hm
    simp [hl, readAt, habs _ hm.1]

/-- The world's reading at a slot. -/
theorem lookup_entries (S : Scheme Key V Dg) (w : World R TxId D) (hix : IndexInjective S w) :
    ∀ k, lookup S.ix (slotsOf S.ix (entries w)) k =
      match k with
      | .system => some (.system w.system)
      | .cell c => (w.cells c).map .cell := by
  intro k
  by_cases hk : k ∈ keys w
  · rw [lookup_slotsOf S.ix _ k (fun e he hi => hix e.1 (List.mem_map_of_mem he) k hk hi)]
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
  · rw [lookup_slotsOf_absent S.ix _ k (fun e he hek => hk (hek ▸ List.mem_map_of_mem he))]
    cases k with
    | system => exact absurd (system_mem_keys w) hk
    | cell c =>
        have : w.cells c = none := by
          by_contra h
          exact hk ((mem_keys_cell w c).2 h)
        simp [this]

theorem world_ext {w w' : World R TxId D} (hc : ∀ c, w.cells c = w'.cells c)
    (hs : w.system = w'.system) : w = w' := by
  rcases w with ⟨cells, system⟩
  rcases w' with ⟨cells', system'⟩
  simp only at hc hs
  subst hs
  have : cells = cells' := DFinsupp.ext hc
  subst this
  rfl

/-- Two worlds with the same slot-root reading at every key, no index
collision in either, and leaf roots that separate their contents, are equal. -/
theorem eq_of_lookups (S : Scheme Key V Dg) {w w' : World R TxId D}
    (hix : IndexInjective S w) (hix' : IndexInjective S w')
    (cells : ∀ c a b, w.cells c = some a → w'.cells c = some b → cellRoot a = cellRoot b → a = b)
    (system : sysRoot w.system = sysRoot w'.system → w.system = w'.system)
    (hl : ∀ k, lookup S.ix (worldSlots (slotRoot cellRoot sysRoot) (slotsOf S.ix (entries w'))) k =
      lookup S.ix (worldSlots (slotRoot cellRoot sysRoot) (slotsOf S.ix (entries w))) k) :
    w = w' := by
  have read : ∀ k, (lookup S.ix (slotsOf S.ix (entries w')) k).map (slotRoot cellRoot sysRoot) =
      (lookup S.ix (slotsOf S.ix (entries w)) k).map (slotRoot cellRoot sysRoot) := by
    intro k
    have := hl k
    rwa [lookup_worldSlots, lookup_worldSlots] at this
  refine world_ext (fun c => ?_) ?_
  · have := read (Key.cell c)
    rw [lookup_entries S w hix, lookup_entries S w' hix'] at this
    rcases ha : w.cells c with _ | a <;> rcases hb : w'.cells c with _ | b <;>
      simp only [ha, hb, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
        slotRoot] at this ⊢
    exact (cells c a b ha hb this.symm)
  · have := read Key.system
    rw [lookup_entries S w hix, lookup_entries S w' hix'] at this
    simp only [Option.map_some, Option.some.injEq, slotRoot] at this
    exact system this.symm

/-- **The carrier** for comparing two worlds by root.  Each field names only
the pairs the comparison uses:
* `paths` — A3's `PathBinding` at every key, between the two slot-root maps;
* `index`, `index'` — no two keys of one world share an index path;
* `cells`, `system` — the leaf roots separate the two worlds' contents at the
  same slot. -/
structure RootBinding (S : Scheme Key V Dg) (w w' : World R TxId D) : Prop where
  paths : MapBinding S (worldSlots (slotRoot cellRoot sysRoot) (slotsOf S.ix (entries w)))
    (worldSlots (slotRoot cellRoot sysRoot) (slotsOf S.ix (entries w')))
  index : IndexInjective S w
  index' : IndexInjective S w'
  cells : ∀ c a b, w.cells c = some a → w'.cells c = some b → cellRoot a = cellRoot b → a = b
  system : sysRoot w.system = sysRoot w'.system → w.system = w'.system

/-- **Binding.**  Under the carrier, equal world roots mean equal worlds. -/
theorem rootOf_binds (S : Scheme Key V Dg) {w w' : World R TxId D}
    (hb : RootBinding cellRoot sysRoot S w w')
    (hr : rootOf cellRoot sysRoot S w = rootOf cellRoot sysRoot S w') : w = w' :=
  eq_of_lookups cellRoot sysRoot S hb.index hb.index' hb.cells hb.system
    (lookup_eq_of_root_eq S hb.paths hr)

/-- **Satisfiable at every hash:** a world against itself meets the carrier
whenever its own keys do not collide in the index. -/
theorem rootBinding_self (S : Scheme Key V Dg) (w : World R TxId D) (hix : IndexInjective S w) :
    RootBinding cellRoot sysRoot S w w where
  paths := mapBinding_self S _
  index := hix
  index' := hix
  cells := fun _ a b ha hb _ => Option.some.inj (ha.symm.trans hb)
  system := fun _ => rfl

/-- **The reduction, with no premise.**  Different worlds with one root exhibit
one of: two distinct inputs of `H` with one digest; two keys of one world at one
index path; two different cells at one id with one cell root; two different
system cells with one system root. -/
theorem rootOf_eq_exhibits_collision (S : Scheme Key V Dg) {w w' : World R TxId D}
    (hr : rootOf cellRoot sysRoot S w = rootOf cellRoot sysRoot S w') (hne : w ≠ w') :
    (∃ x y, x ≠ y ∧ S.H x = S.H y) ∨ ¬ IndexInjective S w ∨ ¬ IndexInjective S w' ∨
      (∃ c a b, w.cells c = some a ∧ w'.cells c = some b ∧ a ≠ b ∧ cellRoot a = cellRoot b) ∨
      (w.system ≠ w'.system ∧ sysRoot w.system = sysRoot w'.system) := by
  by_contra hno
  simp only [not_or, not_exists, not_and, not_not] at hno
  obtain ⟨hH, hix, hix', hcells, hsys⟩ := hno
  apply hne
  refine eq_of_lookups cellRoot sysRoot S hix hix'
    (fun c a b ha hb he => by_contra fun hab => hcells c a b ha hb hab he)
    (fun he => by_contra fun hs => hsys hs he) (fun k => ?_)
  by_contra hk
  obtain ⟨x, y, hxy, hxyH⟩ := root_eq_exhibits_collision S hr k hk
  exact hH x y hxy hxyH

/-- **Checkpoint soundness at the world root (§4.4).**  `Kernel.World.resume_sound`
with the root supplied and its `binds` premise discharged by the carrier. -/
theorem resume_sound_rootOf {Ev : Type} (H : History R TxId Ev D) (S : Scheme Key V Dg)
    (g W_h : World R TxId D) (log : List (Turn R TxId Ev D)) (c : Checkpoint R TxId D Dg)
    (prefixed : fold H g (log.take c.height) = some W_h)
    (honestRoot : c.root = rootOf cellRoot sysRoot S W_h)
    (carrier : RootBinding cellRoot sysRoot S c.world W_h)
    (checks : c.check (rootOf cellRoot sysRoot S) = true) :
    c.resume H (rootOf cellRoot sysRoot S) (log.drop c.height) = fold H g log :=
  resume_sound H (rootOf cellRoot sysRoot S) g W_h log c prefixed honestRoot
    (rootOf_binds cellRoot sysRoot S carrier) checks

end WorldRoot

/-! ## The deployed scheme -/

section Deployed

open Minidregg.Compiler.Sp800185Cshake256

def worldCustomization : List UInt8 := "DREGG.WORLD-ROOT/v1".toUTF8.toList

/-- The deployed hash: cSHAKE256 under the world-root customization. -/
def deployedHash (x : List UInt8) : Digest := (hash worldCustomization x).digest

/-- A3's Q2 index: the 256 bits of the hash of the tagged key bytes. -/
def deployedIx (k : Key) : List Bool := bytesBits (cshake256Bytes worldCustomization (3 :: keyBytes k))

def deployed : Scheme Key Digest Digest where
  H := deployedHash
  digestBytes := digestStream.encode
  keyBytes := keyBytes
  valBytes := digestStream.encode
  digestBytes_prefixFree := streamPrefixFree digestStream
  keyBytes_prefixFree := keyBytes_prefixFree
  valBytes_injective := (streamPrefixFree digestStream).injective
  depth := 256
  ix := deployedIx
  ix_length := fun k => by simp [deployedIx, bytesBits_length]

/-- An index collision of two distinct keys is a collision of the deployed hash
on two distinct inputs. -/
theorem deployedIx_collision {k k' : Key} (hne : k ≠ k') (h : deployedIx k = deployedIx k') :
    (3 :: keyBytes k) ≠ (3 :: keyBytes k') ∧
      deployed.H (3 :: keyBytes k) = deployed.H (3 :: keyBytes k') := by
  refine ⟨fun e => hne (keyBytes_prefixFree.injective (List.cons.inj e).2), ?_⟩
  have hb := bytesBits_injective h
  show digestOfBytesLE (cshake256Bytes worldCustomization (3 :: keyBytes k)) =
    digestOfBytesLE (cshake256Bytes worldCustomization (3 :: keyBytes k'))
  rw [hb]

/-- The empty-subtree roots of the deployed scheme, computed once. -/
def deployedTable : Array Digest := emptyTable deployed (deployed.depth + 1)

/-- The deployed root of an entry list of slot roots, evaluated sparsely. -/
def deployedRoot (es : List (Key × Digest)) : Digest :=
  sparseRoot deployed (tableEmpties deployed deployedTable) es

theorem deployedRoot_eq (es : List (Key × Digest)) :
    deployedRoot es = deployed.root (slotsOf deployed.ix es) :=
  sparseRoot_eq deployed _ (tableEmpties_emptyTable deployed _) es

/-- The deployed root is A3's two-level `worldRoot` over any entry list and leaf
root function, evaluated sparsely. -/
theorem entryRoot_deployed {C : Type} (leafRoot : C → Digest) (es : List (Key × C)) :
    entryRoot deployed leafRoot es = deployedRoot (es.map fun e => (e.1, leafRoot e.2)) :=
  entryRoot_eq_sparse deployed leafRoot _ (tableEmpties_emptyTable deployed _) es

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
the previous log root. -/
def cshakeHistory {R : Registry} {TxId Ev : Type} (encode : Turn R TxId Ev Digest → List UInt8)
    (logRoot0 : Digest) (legBytes : Leg R → Nat) (imageBytes : Cell R → Nat) :
    History R TxId Ev Digest where
  turnDigest t := turnDigestOfBytes (encode t)
  chain := chainDigest
  logRoot0 := logRoot0
  legBytes := legBytes
  imageBytes := imageBytes

/-- `classify_conflict`'s `separates` premise at the deployed history: two turns
with different canonical bytes, where the hash binds that one pair. -/
theorem cshakeHistory_separates {R : Registry} {TxId Ev : Type}
    (encode : Turn R TxId Ev Digest → List UInt8) (logRoot0 : Digest) (legBytes : Leg R → Nat)
    (imageBytes : Cell R → Nat) {t t' : Turn R TxId Ev Digest}
    (hne : encode t ≠ encode t')
    (binds : turnDigestOfBytes (encode t) = turnDigestOfBytes (encode t') → encode t = encode t') :
    (cshakeHistory encode logRoot0 legBytes imageBytes).turnDigest t ≠
      (cshakeHistory encode logRoot0 legBytes imageBytes).turnDigest t' :=
  fun h => hne (binds h)

end History

/-! ## Poles: the honest checkpoint resumes; a tampered one passes a non-binding root -/

namespace Example

open Minidregg.Kernel.World.Example

theorem prefixFree_comp {α β : Type} {f : β → List UInt8} {g : α → β} (hf : PrefixFree f)
    (hg : Function.Injective g) : PrefixFree (f ∘ g) := by
  intro a b s t h
  obtain ⟨hab, hst⟩ := hf _ _ s t h
  exact ⟨hg hab, hst⟩

def toyNatRender (n : Nat) : List UInt8 := List.replicate n 0

theorem toyNatRender_injective : Function.Injective toyNatRender := by
  intro a b h
  simpa [toyNatRender] using congrArg List.length h

def toyKeyRender : Key → List UInt8
  | .system => []
  | .cell c => List.replicate (c + 1) 0

theorem toyKeyRender_injective : Function.Injective toyKeyRender := by
  intro a b h
  have hl := congrArg List.length h
  cases a <;> cases b <;> simp_all [toyKeyRender]

/-- Two index bits: the system slot at `00`, cells 0, 1, 2 at `01`, `10`, `11`. -/
def toyIx : Key → List Bool
  | .system => [false, false]
  | .cell c => [decide ((c + 1) / 2 % 2 = 1), decide ((c + 1) % 2 = 1)]

/-- A toy scheme at a one-bit hash (the parity of the input length):
deliberately NOT binding. -/
def toyScheme : Scheme Key Nat Nat where
  H := fun bs => bs.length % 2
  digestBytes := unaryFrame ∘ toyNatRender
  keyBytes := unaryFrame ∘ toyKeyRender
  valBytes := unaryFrame ∘ toyNatRender
  digestBytes_prefixFree := prefixFree_comp unaryFrame_prefixFree toyNatRender_injective
  keyBytes_prefixFree := prefixFree_comp unaryFrame_prefixFree toyKeyRender_injective
  valBytes_injective := (prefixFree_comp unaryFrame_prefixFree toyNatRender_injective).injective
  depth := 2
  ix := toyIx
  ix_length := fun k => by cases k <;> rfl

/-- A cell's toy root: its value at key 0. -/
def toyCellRoot (cell : Cell toyR) : Nat :=
  (((cell.storeAt false).bind fun s => s ⟨(), (0 : Nat)⟩ : Option Nat)).getD 0

/-- The system cell's toy root: the height. -/
def toySysRoot (s : Store (sysLayout Nat Nat)) : Nat :=
  ((s ⟨SysSpace.head, ()⟩).map fun hv => hv.1).getD 0

abbrev toyRootOf : ToyWorld → Nat := rootOf toyCellRoot toySysRoot toyScheme

theorem w1_index : IndexInjective toyScheme w1 := by unfold IndexInjective; decide +kernel

def honestCk : Checkpoint toyR Nat Nat Nat := ⟨1, w1, toyRootOf w1⟩

/-- **Satisfiable pole.**  The honest checkpoint checks, meets the carrier (at
this non-binding hash too: `rootBinding_self`), and resumes to the fold. -/
theorem honest_checkpoint_resumes :
    honestCk.check toyRootOf = true ∧
      honestCk.resume toyH toyRootOf (log2.drop honestCk.height) = fold toyH g log2 :=
  ⟨by decide +kernel,
    resume_sound_rootOf toyCellRoot toySysRoot toyH toyScheme g w1 log2 honestCk w1_prefix rfl
      (rootBinding_self toyCellRoot toySysRoot toyScheme w1 w1_index) (by decide +kernel)⟩

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
      ¬ RootBinding toyCellRoot toySysRoot toyScheme tamperedWorld w1 := by
  refine ⟨by decide +kernel, by decide +kernel, fun hb => ?_⟩
  have heq := rootOf_binds toyCellRoot toySysRoot toyScheme hb tampered_root_eq
  have hv : val tamperedWorld 1 ≠ val w1 1 := by decide +kernel
  exact hv (by rw [heq])

end Example

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.WorldRoot.streamPrefixFree' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms streamPrefixFree
/-- info: 'Minidregg.Kernel.WorldRoot.keyBytes_prefixFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keyBytes_prefixFree
/-- info: 'Minidregg.Kernel.WorldRoot.byteBits_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byteBits_injective
/-- info: 'Minidregg.Kernel.WorldRoot.bytesBits_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bytesBits_injective
/-- info: 'Minidregg.Kernel.WorldRoot.slotsOf_wf' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms slotsOf_wf
/-- info: 'Minidregg.Kernel.WorldRoot.lookup_slotsOf' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms lookup_slotsOf
/-- info: 'Minidregg.Kernel.WorldRoot.lookup_slotsOf_absent' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms lookup_slotsOf_absent
/-- info: 'Minidregg.Kernel.WorldRoot.worldSlots_slotsOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms worldSlots_slotsOf
/-- info: 'Minidregg.Kernel.WorldRoot.subRoot_empty' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms subRoot_empty
/-- info: 'Minidregg.Kernel.WorldRoot.filter_strip' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms filter_strip
/-- info: 'Minidregg.Kernel.WorldRoot.sparse_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sparse_eq
/-- info: 'Minidregg.Kernel.WorldRoot.sparseRoot_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sparseRoot_eq
/-- info: 'Minidregg.Kernel.WorldRoot.empties_iterate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms empties_iterate
/-- info: 'Minidregg.Kernel.WorldRoot.tableEmpties_emptyTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tableEmpties_emptyTable
/-- info: 'Minidregg.Kernel.WorldRoot.entryRoot_eq_sparse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entryRoot_eq_sparse
/-- info: 'Minidregg.Kernel.WorldRoot.mapBinding_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapBinding_self
/-- info: 'Minidregg.Kernel.WorldRoot.lookup_eq_of_root_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookup_eq_of_root_eq
/-- info: 'Minidregg.Kernel.WorldRoot.root_eq_exhibits_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms root_eq_exhibits_collision
/-- info: 'Minidregg.Kernel.WorldRoot.mem_presentIds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_presentIds
/-- info: 'Minidregg.Kernel.WorldRoot.mem_keys_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mem_keys_cell
/-- info: 'Minidregg.Kernel.WorldRoot.system_mem_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms system_mem_keys
/-- info: 'Minidregg.Kernel.WorldRoot.lookup_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookup_entries
/-- info: 'Minidregg.Kernel.WorldRoot.world_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms world_ext
/-- info: 'Minidregg.Kernel.WorldRoot.eq_of_lookups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eq_of_lookups
/-- info: 'Minidregg.Kernel.WorldRoot.rootOf_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rootOf_binds
/-- info: 'Minidregg.Kernel.WorldRoot.rootBinding_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rootBinding_self
/-- info: 'Minidregg.Kernel.WorldRoot.rootOf_eq_exhibits_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rootOf_eq_exhibits_collision
/-- info: 'Minidregg.Kernel.WorldRoot.resume_sound_rootOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resume_sound_rootOf
/-- info: 'Minidregg.Kernel.WorldRoot.deployedIx_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployedIx_collision
/-- info: 'Minidregg.Kernel.WorldRoot.deployedRoot_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deployedRoot_eq
/-- info: 'Minidregg.Kernel.WorldRoot.entryRoot_deployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms entryRoot_deployed
/-- info: 'Minidregg.Kernel.WorldRoot.cshakeHistory_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cshakeHistory_separates
/-- info: 'Minidregg.Kernel.WorldRoot.Example.prefixFree_comp' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Example.prefixFree_comp
/-- info: 'Minidregg.Kernel.WorldRoot.Example.toyNatRender_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Example.toyNatRender_injective
/-- info: 'Minidregg.Kernel.WorldRoot.Example.toyKeyRender_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Example.toyKeyRender_injective
/-- info: 'Minidregg.Kernel.WorldRoot.Example.w1_index' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.w1_index
/-- info: 'Minidregg.Kernel.WorldRoot.Example.honest_checkpoint_resumes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.honest_checkpoint_resumes
/-- info: 'Minidregg.Kernel.WorldRoot.Example.tampered_root_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.tampered_root_eq
/-- info: 'Minidregg.Kernel.WorldRoot.Example.tampered_checkpoint_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Example.tampered_checkpoint_accepted

end Minidregg.Kernel.WorldRoot
