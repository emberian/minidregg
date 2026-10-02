/-
# Kernel.WorldRootCache — the world root, cached: one path per write

The specification root stays `Scheme.root` of the slot map (A3; C1's
`WorldRoot.entryRoot`, evaluated sparsely by `deployedRoot`). Evaluating it in
full costs one node hash per level per nonempty path — at depth 256 that is
`entries × 256` hashes on every use (C1, measured: 10 slots 0.5 s).

This module keeps the evaluated tree. A `Tree` stores the digest of every
nonempty internal node; `Tree.set` rewrites the slot at one index and rehashes
only the nodes on that index's path (`depth` node hashes), reusing every
sibling digest. `Good m i p t` says `t` is the cached evaluation of map `m`
below prefix `p`; the theorems are

* `digest_eq`: a good tree's digest IS the specification subtree root;
* `insertWrite_good`: writing `(k, v)` keeps it good for `write S.ix m k v`,
  so `insertWrite_root` — the cached root after a write IS `S.root (write …)`
  (A3's `root_update`, now over the cache rather than an opening);
* `ofEntries_root`: the cache built by writing an entry list is the
  specification root of `slotsOf` that list, so it agrees with C1's
  `entryRoot`/`deployedRoot` on the same entries.

Poles (LengthToy scheme, `decide`): `cached_write_root` (the maintained cache
tracks a write) and `stale_cache_refuted` (a cache that skipped the dirty path
after a write keeps a digest that is no longer the root).
-/
import Kernel.WorldRoot

namespace Minidregg.Kernel.WorldRootCache

open Minidregg.Theory.AuthMap
open Minidregg.Kernel.WorldRoot
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- A sparse cached tree: empty subtrees, occupied leaves, and internal nodes
carrying their digest. Heights are positional. -/
inductive Tree (K V D : Type) where
  | empty
  | leaf (entry : K × V)
  | node (digest : D) (left right : Tree K V D)

namespace Tree

variable {K V D : Type}

def occupant : Tree K V D → Option (K × V)
  | .leaf entry => some entry
  | _ => none

def children : Tree K V D → Tree K V D × Tree K V D
  | .node _ left right => (left, right)
  | _ => (.empty, .empty)

def ofSlot : Option (K × V) → Tree K V D
  | none => .empty
  | some entry => .leaf entry

/-- The digest of a tree of height `i`; empty subtrees read the table. -/
def digest (S : Scheme K V D) (E : Nat → D) (i : Nat) : Tree K V D → D
  | .empty => E i
  | .leaf entry => S.leafDigest (some entry)
  | .node d _ _ => d

/-- Rewrite the slot at the end of `bits` with `f` of its occupant, rehashing
exactly the nodes on that path. -/
def set (S : Scheme K V D) (E : Nat → D) (f : Option (K × V) → Option (K × V)) :
    Nat → List Bool → Tree K V D → Tree K V D
  | 0, _, t => ofSlot (f t.occupant)
  | _ + 1, [], t => t
  | i + 1, b :: bs, t =>
      let left := if b then t.children.1 else set S E f i bs t.children.1
      let right := if b then set S E f i bs t.children.2 else t.children.2
      .node (S.nodeHash (left.digest S E i) (right.digest S E i)) left right

end Tree

section Cache

variable {K V D : Type} [DecidableEq K] (S : Scheme K V D) (E : Nat → D)

set_option linter.unusedSectionVars false

/-- `t` is the cached evaluation of `m` below prefix `p` at height `i`. -/
def Good (m : Map K V) : Nat → List Bool → Tree K V D → Prop
  | i, p, .empty => ∀ q : List Bool, q.length = i → m (p ++ q) = none
  | i, p, .leaf entry => i = 0 ∧ m p = some entry
  | 0, _, .node _ _ _ => False
  | i + 1, p, .node d left right =>
      Good m i (p ++ [false]) left ∧ Good m i (p ++ [true]) right ∧
        d = S.nodeHash (left.digest S E i) (right.digest S E i)

theorem good_empty (i : Nat) (p : List Bool) : Good S E (Map.empty : Map K V) i p .empty := by
  simp only [Good]
  intro _ _
  rfl

/-- A good tree's digest is the specification subtree root. -/
theorem digest_eq (hE : ∀ i, E i = empties S i) (m : Map K V) :
    ∀ (t : Tree K V D) (i : Nat) (p : List Bool), Good S E m i p t →
      t.digest S E i = S.subRoot m i p
  | .empty, i, p, good => by
      simp only [Good] at good
      rw [Tree.digest, hE, ← subRoot_empty S i p]
      apply S.subRoot_congr
      intro q hq
      rw [good q hq]
      rfl
  | .leaf entry, i, p, good => by
      simp only [Good] at good
      obtain ⟨rfl, occupied⟩ := good
      simp [Tree.digest, Scheme.subRoot, occupied]
  | .node d left right, 0, p, good => by simp only [Good] at good
  | .node d left right, i + 1, p, good => by
      simp only [Good] at good
      obtain ⟨gl, gr, hd⟩ := good
      rw [Tree.digest, hd, Scheme.subRoot, digest_eq hE m left i _ gl, digest_eq hE m right i _ gr]

/-- Goodness depends only on the map below the prefix. -/
theorem good_congr {m m' : Map K V} :
    ∀ (t : Tree K V D) (i : Nat) (p : List Bool),
      (∀ q : List Bool, q.length = i → m' (p ++ q) = m (p ++ q)) →
      Good S E m i p t → Good S E m' i p t
  | .empty, i, p, same, good => by
      simp only [Good] at good ⊢
      exact fun q hq => (same q hq).trans (good q hq)
  | .leaf entry, i, p, same, good => by
      simp only [Good] at good ⊢
      obtain ⟨rfl, occupied⟩ := good
      exact ⟨rfl, by simpa using (same [] rfl).trans (by simpa using occupied)⟩
  | .node d left right, 0, p, _, good => by simp only [Good] at good
  | .node d left right, i + 1, p, same, good => by
      simp only [Good] at good ⊢
      obtain ⟨gl, gr, hd⟩ := good
      refine ⟨good_congr left i _ (fun q hq => ?_) gl, good_congr right i _ (fun q hq => ?_) gr, hd⟩
      · simpa using same (false :: q) (by simp [hq])
      · simpa using same (true :: q) (by simp [hq])

/-- The occupant a good height-0 tree reports is the map's slot. -/
theorem good_occupant {m : Map K V} {p : List Bool} :
    ∀ (t : Tree K V D), Good S E m 0 p t → t.occupant = m p
  | .empty, good => by
      simp only [Good] at good
      simpa [Tree.occupant] using (good [] rfl).symm
  | .leaf entry, good => by
      simp only [Good] at good
      simp [Tree.occupant, good.2]
  | .node _ _ _, good => by simp only [Good] at good

/-- The children of a good tree are good below the two child prefixes. -/
theorem good_children {m : Map K V} {i : Nat} {p : List Bool} :
    ∀ (t : Tree K V D), Good S E m (i + 1) p t →
      Good S E m i (p ++ [false]) t.children.1 ∧ Good S E m i (p ++ [true]) t.children.2
  | .empty, good => by
      simp only [Good] at good
      simp only [Tree.children, Good]
      exact ⟨fun q hq => by simpa using good (false :: q) (by simp [hq]),
        fun q hq => by simpa using good (true :: q) (by simp [hq])⟩
  | .leaf entry, good => by
      simp only [Good] at good
      cases good.1
  | .node _ left right, good => by
      simp only [Good] at good
      exact ⟨good.1, good.2.1⟩

/-- The map with the slot at `path` rewritten by `f`. -/
def update (m : Map K V) (path : List Bool) (f : Option (K × V) → Option (K × V)) : Map K V :=
  fun q => if q = path then f (m path) else m q

theorem set_good (f : Option (K × V) → Option (K × V)) (m : Map K V) :
    ∀ (i : Nat) (bits p : List Bool) (t : Tree K V D), bits.length = i → Good S E m i p t →
      Good S E (update m (p ++ bits) f) i p (t.set S E f i bits)
  | 0, bits, p, t, hlen, good => by
      have hnil : bits = [] := List.length_eq_zero_iff.mp hlen
      subst hnil
      simp only [Tree.set, good_occupant S E t good, List.append_nil]
      cases hf : f (m p) with
      | none =>
          simp only [Tree.ofSlot, Good]
          intro q hq
          have hq' : q = [] := List.length_eq_zero_iff.mp hq
          subst hq'
          simp [update, hf]
      | some entry =>
          simp only [Tree.ofSlot, Good]
          exact ⟨by trivial, by simp [update, hf]⟩
  | i + 1, [], p, t, hlen, _ => by simp at hlen
  | i + 1, b :: bs, p, t, hlen, good => by
      have hbs : bs.length = i := by simpa using hlen
      obtain ⟨gl, gr⟩ := good_children S E t good
      have outside : ∀ (c : Bool), c ≠ b → ∀ q : List Bool, q.length = i →
          update m (p ++ b :: bs) f (p ++ [c] ++ q) = m (p ++ [c] ++ q) := by
        intro c hc q _
        have hne : p ++ [c] ++ q ≠ p ++ b :: bs := by
          intro heq
          simp only [List.append_assoc, List.singleton_append, List.append_cancel_left_eq,
            List.cons.injEq] at heq
          exact hc heq.1
        unfold update
        rw [if_neg hne]
      cases b with
      | false =>
          simp only [Tree.set, Good, if_false, Bool.false_eq_true]
          refine ⟨?_, ?_, by trivial⟩
          · have := set_good f m i bs (p ++ [false]) t.children.1 hbs gl
            simpa using this
          · exact good_congr S E t.children.2 i _ (outside true (by decide)) gr
      | true =>
          simp only [Tree.set, Good, if_true]
          refine ⟨?_, ?_, by trivial⟩
          · exact good_congr S E t.children.1 i _ (outside false (by decide)) gl
          · have := set_good f m i bs (p ++ [true]) t.children.2 hbs gr
            simpa using this

theorem write_eq_update (m : Map K V) (k : K) (v : Option V) :
    write S.ix m k v = update m (S.ix k) (fun occupant => slotAfter occupant k v) := by
  funext q
  unfold write update
  split <;> simp_all

/-- Write `(k, v)` into the cache: one path of `depth` node hashes. -/
def insertWrite (t : Tree K V D) (k : K) (v : Option V) : Tree K V D :=
  t.set S E (fun occupant => slotAfter occupant k v) S.depth (S.ix k)

theorem insertWrite_good {m : Map K V} {t : Tree K V D} (good : Good S E m S.depth [] t)
    (k : K) (v : Option V) :
    Good S E (write S.ix m k v) S.depth [] (insertWrite S E t k v) := by
  rw [write_eq_update]
  have := set_good S E (fun occupant => slotAfter occupant k v) m S.depth (S.ix k) [] t
    (S.ix_length k) good
  simpa using this

/-- **The cached root after a write is the specification root after it.** -/
theorem insertWrite_root (hE : ∀ i, E i = empties S i) {m : Map K V} {t : Tree K V D}
    (good : Good S E m S.depth [] t) (k : K) (v : Option V) :
    (insertWrite S E t k v).digest S E S.depth = S.root (write S.ix m k v) :=
  digest_eq S E hE _ _ _ _ (insertWrite_good S E good k v)

/-- The cache of an entry list, built by writing its entries in order. -/
def ofEntries (es : List (K × V)) : Tree K V D :=
  es.foldl (fun t e => insertWrite S E t e.1 (some e.2)) .empty

theorem slotsOf_snoc (es : List (K × V)) (e : K × V) :
    slotsOf S.ix (es ++ [e]) = write S.ix (slotsOf S.ix es) e.1 (some e.2) := by
  funext p
  unfold slotsOf write
  by_cases hp : p = S.ix e.1
  · subst hp
    simp [List.filter_append, slotAfter]
  · have hne : ¬ S.ix e.1 = p := fun h => hp h.symm
    simp [List.filter_append, hp, hne]

theorem ofEntries_good_from (es₀ : List (K × V)) :
    ∀ (rest : List (K × V)) (t : Tree K V D), Good S E (slotsOf S.ix es₀) S.depth [] t →
      Good S E (slotsOf S.ix (es₀ ++ rest)) S.depth []
        (rest.foldl (fun t e => insertWrite S E t e.1 (some e.2)) t)
  | [], t, good => by simpa using good
  | e :: rest, t, good => by
      have step := insertWrite_good S E good e.1 (some e.2)
      rw [← slotsOf_snoc] at step
      have := ofEntries_good_from (es₀ ++ [e]) rest _ step
      simpa [List.foldl_cons, List.append_assoc] using this

theorem ofEntries_good (es : List (K × V)) :
    Good S E (slotsOf S.ix es) S.depth [] (ofEntries S E es) := by
  have := ofEntries_good_from S E [] es .empty (by simp only [Good]; intro q _; simp [slotsOf])
  simpa [ofEntries] using this

/-- The cache built from an entry list has the specification root of that list. -/
theorem ofEntries_root (hE : ∀ i, E i = empties S i) (es : List (K × V)) :
    (ofEntries S E es).digest S E S.depth = S.root (slotsOf S.ix es) :=
  digest_eq S E hE _ _ _ _ (ofEntries_good S E es)

end Cache

/-! ## Reading the cache, and when an entry list's order does not matter

`Tree.find` walks one index path of the cached tree (no hashing): on a good
tree it reads the slot map (`find_good`). An entry list whose keys never share
an index path (`KeysInjective`, checked through `find`, never assumed) has a
slot map that depends only on the value it last gives each key (`lastVal`):
`slotsOf_eq_of_lastVal`. That is what lets a cache whose entries were written
in log order stand for a served entry list written in enumeration order. -/

namespace Tree

variable {K V D : Type}

/-- The slot at the end of `bits`, read down a tree of height `i`. -/
def find : Nat → List Bool → Tree K V D → Option (K × V)
  | 0, _, t => t.occupant
  | _ + 1, [], _ => none
  | i + 1, b :: bs, t => find i bs (if b then t.children.2 else t.children.1)

end Tree

section Read

variable {K V D : Type} [DecidableEq K] (S : Scheme K V D) (E : Nat → D)

set_option linter.unusedSectionVars false

/-- On a good tree, `find` reads the slot map. -/
theorem find_good (m : Map K V) :
    ∀ (i : Nat) (bits p : List Bool) (t : Tree K V D), bits.length = i → Good S E m i p t →
      t.find i bits = m (p ++ bits)
  | 0, bits, p, t, hlen, good => by
      have hnil : bits = [] := List.length_eq_zero_iff.mp hlen
      subst hnil
      simpa [Tree.find] using good_occupant S E t good
  | i + 1, [], _, _, hlen, _ => by simp at hlen
  | i + 1, b :: bs, p, t, hlen, good => by
      have hbs : bs.length = i := by simpa using hlen
      obtain ⟨gl, gr⟩ := good_children S E t good
      cases b with
      | false =>
          simp only [Tree.find, Bool.false_eq_true, if_false]
          rw [find_good m i bs _ _ hbs gl]
          simp
      | true =>
          simp only [Tree.find, if_true]
          rw [find_good m i bs _ _ hbs gr]
          simp

end Read

section Order

variable {K C : Type} [DecidableEq K] (ix : K → List Bool)

/-- The value an entry list last gives key `k`. -/
def lastVal (es : List (K × C)) (k : K) : Option C :=
  ((es.filter fun e => decide (e.1 = k)).getLast?).map (·.2)

/-- No two distinct keys of the list share an index path. -/
def KeysInjective (es : List (K × C)) : Prop :=
  ∀ e ∈ es, ∀ e' ∈ es, ix e.1 = ix e'.1 → e.1 = e'.1

theorem lastVal_isSome {es : List (K × C)} {k : K} :
    (lastVal es k).isSome ↔ ∃ e ∈ es, e.1 = k := by
  unfold lastVal
  rw [Option.isSome_map]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    have hm := List.mem_of_getLast? hx
    rw [List.mem_filter, decide_eq_true_eq] at hm
    exact ⟨x, hm.1, hm.2⟩
  · rintro ⟨e, he, hk⟩
    rw [Option.isSome_iff_ne_none, Ne, List.getLast?_eq_none_iff]
    exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨he, by simpa using hk⟩)

theorem lastVal_append (es fs : List (K × C)) (k : K) :
    lastVal (es ++ fs) k = (lastVal fs k).or (lastVal es k) := by
  unfold lastVal
  rw [List.filter_append, List.getLast?_append]
  cases (fs.filter fun e => decide (e.1 = k)).getLast? <;>
    cases (es.filter fun e => decide (e.1 = k)).getLast? <;> rfl

theorem lastVal_cons (e : K × C) (es : List (K × C)) (k : K) :
    lastVal (e :: es) k = (lastVal es k).or (if e.1 = k then some e.2 else none) := by
  have := lastVal_append [e] es k
  rw [List.singleton_append] at this
  rw [this]
  by_cases h : e.1 = k <;> simp [lastVal, h]

/-- Under injective keys a slot-map read is the key's last value. -/
theorem lookup_slotsOf_injective (es : List (K × C)) (inj : KeysInjective ix es) (k : K) :
    lookup ix (slotsOf ix es) k = lastVal es k := by
  by_cases present : ∃ e ∈ es, e.1 = k
  · obtain ⟨e₀, he₀, hk₀⟩ := present
    rw [lookup_slotsOf ix es k (fun e he hi => (inj e he e₀ he₀ (hi.trans (by rw [hk₀]))).trans hk₀)]
    rfl
  · have absent : ∀ e ∈ es, e.1 ≠ k := fun e he hk => present ⟨e, he, hk⟩
    rw [lookup_slotsOf_absent ix es k absent]
    have := (lastVal_isSome (es := es) (k := k)).not.mpr present
    exact (by simpa using this : lastVal es k = none).symm

/-- Lists that give every key the same last value have the same keys, so
injectivity transfers. -/
theorem keysInjective_of_lastVal {es es' : List (K × C)} (inj : KeysInjective ix es)
    (same : ∀ k, lastVal es k = lastVal es' k) : KeysInjective ix es' := by
  intro e he e' he' hi
  have fe : (lastVal es e.1).isSome := by
    rw [same]; exact lastVal_isSome.mpr ⟨e, he, rfl⟩
  have fe' : (lastVal es e'.1).isSome := by
    rw [same]; exact lastVal_isSome.mpr ⟨e', he', rfl⟩
  obtain ⟨a, ha, hka⟩ := lastVal_isSome.mp fe
  obtain ⟨b, hb, hkb⟩ := lastVal_isSome.mp fe'
  rw [← hka, ← hkb]
  exact inj a ha b hb (by rw [hka, hkb, hi])

/-- **Order does not matter under injective keys**: two entry lists that give
every key the same last value have one slot map. -/
theorem slotsOf_eq_of_lastVal {es es' : List (K × C)} (inj : KeysInjective ix es)
    (same : ∀ k, lastVal es k = lastVal es' k) : slotsOf ix es = slotsOf ix es' :=
  map_eq_of_lookup ix (slotsOf_wf ix es) (slotsOf_wf ix es') fun k => by
    rw [lookup_slotsOf_injective ix es inj, lookup_slotsOf_injective ix es'
      (keysInjective_of_lastVal ix inj same), same k]

omit [DecidableEq K] in
/-- The slot at a path some entry indexes to is occupied by an entry of the list
that indexes there. -/
theorem slotsOf_occupied {es : List (K × C)} {e : K × C} (he : e ∈ es) :
    ∃ x ∈ es, slotsOf ix es (ix e.1) = some x ∧ ix x.1 = ix e.1 := by
  unfold slotsOf
  have ne : (es.filter fun a => decide (ix a.1 = ix e.1)) ≠ [] :=
    List.ne_nil_of_mem (List.mem_filter.mpr ⟨he, by simp⟩)
  cases hx : (es.filter fun a => decide (ix a.1 = ix e.1)).getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hx; exact absurd hx ne
  | some x =>
      have hm := List.mem_of_getLast? hx
      rw [List.mem_filter, decide_eq_true_eq] at hm
      exact ⟨x, hm.1, rfl, hm.2⟩

omit [DecidableEq K] in
/-- **The check**: when every entry's own index path holds its key, the keys
are injective. -/
theorem keysInjective_of_occupants (es : List (K × C))
    (occ : ∀ e ∈ es, ∃ x, slotsOf ix es (ix e.1) = some x ∧ x.1 = e.1) : KeysInjective ix es := by
  intro e he e' he' hi
  obtain ⟨x, hx, hkx⟩ := occ e he
  obtain ⟨x', hx', hkx'⟩ := occ e' he'
  rw [hi, hx'] at hx
  cases hx
  rw [← hkx, hkx']

omit [DecidableEq K] in
/-- Appending an entry whose index path is empty or already holds its key keeps
the keys injective. -/
theorem keysInjective_snoc {es : List (K × C)} (inj : KeysInjective ix es) (e : K × C)
    (free : ∀ x, slotsOf ix es (ix e.1) = some x → x.1 = e.1) : KeysInjective ix (es ++ [e]) := by
  have toE : ∀ a ∈ es, ix a.1 = ix e.1 → a.1 = e.1 := by
    intro a ha hi
    obtain ⟨x, hx, hslot, hxi⟩ := slotsOf_occupied ix ha
    rw [hi] at hslot
    rw [inj a ha x hx hxi.symm, free x hslot]
  intro a ha b hb hi
  rw [List.mem_append, List.mem_singleton] at ha hb
  rcases ha with ha | rfl <;> rcases hb with hb | rfl
  · exact inj a ha b hb hi
  · exact toE a ha hi
  · exact (toE b hb hi.symm).symm
  · rfl

end Order

/-! ## The deployed cache -/

/-- The cached tree under the deployed scheme and its precomputed empty table. -/
abbrev DeployedTree := Tree Key Digest Digest

def deployedEmpties : Nat → Digest := tableEmpties deployed deployedTable

def deployedOf (es : List (Key × Digest)) : DeployedTree := ofEntries deployed deployedEmpties es

def deployedWrite (t : DeployedTree) (k : Key) (v : Option Digest) : DeployedTree :=
  insertWrite deployed deployedEmpties t k v

def deployedDigest (t : DeployedTree) : Digest := t.digest deployed deployedEmpties deployed.depth

theorem deployedEmpties_eq (i : Nat) : deployedEmpties i = empties deployed i :=
  tableEmpties_emptyTable deployed _ i

/-- The deployed cache built from an entry list is C1's `deployedRoot` of it. -/
theorem deployedOf_root (es : List (Key × Digest)) :
    deployedDigest (deployedOf es) = deployedRoot es := by
  rw [deployedRoot_eq]
  exact ofEntries_root deployed deployedEmpties deployedEmpties_eq es

/-- A deployed cache that is good for the slots of `es`, after writing `(k, v)`,
has the specification root of the appended list — one path rehashed. -/
theorem deployedWrite_root {es : List (Key × Digest)} {t : DeployedTree}
    (good : Good deployed deployedEmpties (slotsOf deployed.ix es) deployed.depth [] t)
    (k : Key) (v : Digest) :
    deployedDigest (deployedWrite t k (some v)) = deployedRoot (es ++ [(k, v)]) := by
  rw [deployedRoot_eq, slotsOf_snoc]
  exact insertWrite_root deployed deployedEmpties deployedEmpties_eq good k (some v)

/-! ## Poles (length toy: a deliberately weak hash, so equalities are computed) -/

namespace Toy

open Minidregg.Theory.AuthMap.LengthToy (ix)

/-- The length toy's renderings with a byte-mixing hash, so that a write
moves the root (the length hash cannot see a value change). Still toy-weak. -/
def scheme : Scheme UInt8 UInt8 UInt8 :=
  { LengthToy.scheme with H := fun bs => bs.foldl (fun acc b => acc * 31 + b) 7 }

def E : Nat → UInt8 := empties scheme

def m0 : Map UInt8 UInt8 := slotsOf ix [(5, 7), (2, 1)]

def t0 : Tree UInt8 UInt8 UInt8 := ofEntries scheme E [(5, 7), (2, 1)]

/-- Satisfiable pole: the maintained cache tracks a write that changes the root. -/
theorem cached_write_root :
    (insertWrite scheme E t0 6 (some 200)).digest scheme E scheme.depth =
      scheme.root (write ix m0 6 (some 200)) := by decide

/-- The write moves the specification root at this scheme. -/
theorem write_moves_root : scheme.root (write ix m0 6 (some 200)) ≠ scheme.root m0 := by decide

/-- Refuting pole: a cache that skipped the dirty path — the tree before the
write — no longer has the root. -/
theorem stale_cache_refuted :
    t0.digest scheme E scheme.depth ≠ scheme.root (write ix m0 6 (some 200)) := by decide

end Toy

end Minidregg.Kernel.WorldRootCache

/-- info: 'Minidregg.Kernel.WorldRootCache.insertWrite_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.WorldRootCache.insertWrite_root
/-- info: 'Minidregg.Kernel.WorldRootCache.ofEntries_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.WorldRootCache.ofEntries_root
/-- info: 'Minidregg.Kernel.WorldRootCache.deployedOf_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.WorldRootCache.deployedOf_root
/-- info: 'Minidregg.Kernel.WorldRootCache.deployedWrite_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.WorldRootCache.deployedWrite_root
/-- info: 'Minidregg.Kernel.WorldRootCache.Toy.stale_cache_refuted' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.WorldRootCache.Toy.stale_cache_refuted
