/-
# Theory.AuthTrieErase — removing a key from the kept trie along one walk

`Trie.eraseCounted` walks the key's path once, removes its entry, and re-joins
each branch on the way up: a branch left holding one entry becomes that entry's
leaf one level higher (a leaf's digest does not depend on its remaining bits, so
the lone leaf rises without rehashing), anything else is a branch with a fresh
digest. The count it returns is the work done: node visits, digest evaluations
(`joinCost`, the empty-node digests a fresh branch reads included) and a clash's
size.

* `eraseCounted_entries`: the trie's entries lose exactly the key's entry.
* `eraseCounted_inv`: `Inv` is kept, with no premise beyond `Inv` itself.
* `Cache.erase_holds`: a cache holding `es` holds `dropKey k es` after erasing
  `k` (the `EraseCorrect` target of `Theory.PrivateCellTrie`).
* `Cache.eraseCounted_count`: on a cache whose live keys have distinct paths the
  count is at most `4 * L + 1` (no clash is reachable), constants independent of
  `L` and of the store.
-/
module

public import Theory.AuthTrieCache

@[expose] public section

namespace Minidregg.Theory.AuthTrie

set_option autoImplicit false

namespace Trie

variable {K V D : Type} (dig : NodeIn K V D → D)

/-- Re-join two children after one of them lost an entry. -/
def join (l r : Trie K V D) : Trie K V D :=
  match l, r with
  | .empty, .empty => .empty
  | .empty, .leaf d rest k v => .leaf d (true :: rest) k v
  | .leaf d rest k v, .empty => .leaf d (false :: rest) k v
  | l, r => mkBranch dig l r

/-- Digest evaluations `Trie.digest` performs on a node: the empty node and a
clash bucket hash `.empty`; a leaf or branch returns its cached digest. -/
def digestCost : Trie K V D → Nat
  | .empty => 1
  | .clash _ => 1
  | .leaf .. => 0
  | .branch .. => 0

/-- Digest evaluations `join` performs: a lone leaf rises without rehashing; a
fresh branch hashes once and reads both children's digests. -/
def joinCost (l r : Trie K V D) : Nat :=
  match l, r with
  | .empty, .empty => 0
  | .empty, .leaf .. => 0
  | .leaf .., .empty => 0
  | l, r => 1 + digestCost l + digestCost r

theorem digestCost_le_one (t : Trie K V D) : digestCost t ≤ 1 := by
  cases t <;> simp [digestCost]

theorem joinCost_le_three (l r : Trie K V D) : joinCost l r ≤ 3 := by
  have := digestCost_le_one l
  have := digestCost_le_one r
  cases l <;> cases r <;> simp only [joinCost] <;> omega

/-- A height-0 bucket after a removal. -/
def clashOf : List (K × V) → Trie K V D
  | [] => .empty
  | [kv] => mkLeaf dig [] kv.1 kv.2
  | kvs@(_ :: _ :: _) => .clash kvs

theorem join_entries (l r : Trie K V D) :
    (join dig l r).entries = l.entries.map (consBit false) ++ r.entries.map (consBit true) := by
  cases l <;> cases r <;> simp [join, mkBranch, entries, consBit]

theorem clashOf_entries (kvs : List (K × V)) :
    (clashOf dig kvs).entries = kvs.map fun kv => (kv.1, [], kv.2) := by
  match kvs with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

theorem clashOf_inv (kvs : List (K × V)) : Inv dig 0 (clashOf dig kvs) := by
  match kvs with
  | [] => trivial
  | [_] => exact ⟨rfl, rfl⟩
  | _ :: _ :: _ => simp [clashOf, Inv]

theorem two_le_of_inv_branch {n : Nat} {d : D} {l r : Trie K V D} (inv : Inv dig n (.branch d l r)) :
    2 ≤ (Trie.branch d l r).entries.length := by
  cases n with
  | zero => simp [Inv] at inv
  | succ n => simpa [entries] using inv.2.2.2

theorem two_le_of_inv_clash {n : Nat} {kvs : List (K × V)} (inv : Inv dig n (.clash kvs)) :
    2 ≤ (Trie.clash kvs : Trie K V D).entries.length := by
  cases n with
  | zero => simpa [Inv, entries] using inv
  | succ n => simp [Inv] at inv

@[simp] theorem length_entries_empty : (Trie.empty : Trie K V D).entries.length = 0 := rfl
@[simp] theorem length_entries_leaf (d : D) (rest : List Bool) (k : K) (v : V) :
    (Trie.leaf d rest k v).entries.length = 1 := rfl
@[simp] theorem length_entries_branch (d : D) (l r : Trie K V D) :
    (Trie.branch d l r).entries.length = l.entries.length + r.entries.length := by simp [entries]
@[simp] theorem length_entries_clash (kvs : List (K × V)) :
    (Trie.clash kvs : Trie K V D).entries.length = kvs.length := by simp [entries]

/-- Re-joining two well-formed children is well formed one level up. -/
theorem join_inv (n : Nat) (l r : Trie K V D) (il : Inv dig n l) (ir : Inv dig n r) :
    Inv dig (n + 1) (join dig l r) := by
  have branchInv : 2 ≤ l.entries.length + r.entries.length → Inv dig (n + 1) (mkBranch dig l r) :=
    fun two => ⟨il, ir, rfl, two⟩
  cases l with
  | empty =>
      cases r with
      | empty => trivial
      | leaf d rest k v =>
          simp only [Inv] at ir
          exact ⟨by simp [ir.1], ir.2⟩
      | branch =>
          have := two_le_of_inv_branch dig ir
          exact branchInv (by simp only [length_entries_empty, length_entries_branch] at this ⊢; omega)
      | clash =>
          have := two_le_of_inv_clash dig ir
          exact branchInv (by simp only [length_entries_empty, length_entries_clash] at this ⊢; omega)
  | leaf d rest k v =>
      cases r with
      | empty =>
          simp only [Inv] at il
          exact ⟨by simp [il.1], il.2⟩
      | leaf => exact branchInv (by simp)
      | branch =>
          have := two_le_of_inv_branch dig ir
          exact branchInv (by simp only [length_entries_leaf, length_entries_branch] at this ⊢; omega)
      | clash =>
          have := two_le_of_inv_clash dig ir
          exact branchInv (by simp only [length_entries_leaf, length_entries_clash] at this ⊢; omega)
  | branch d' l' r' =>
      have := two_le_of_inv_branch dig il
      exact branchInv (by simp only [length_entries_branch] at this ⊢; omega)
  | clash kvs =>
      have := two_le_of_inv_clash dig il
      exact branchInv (by simp only [length_entries_clash] at this ⊢; omega)

variable [DecidableEq K]

/-- Remove `k` along the walk `bits`. The count is the work done: one per node
visited, every digest evaluation (`joinCost` per re-joined level; one for the
leaf a filtered clash bucket may become), and the size of a clash bucket it
filters. -/
def eraseCounted (k : K) : Nat → List Bool → Trie K V D → Trie K V D × Nat
  | n + 1, b :: bs, .branch _ l r =>
      if b then
        let below := eraseCounted k n bs r
        (join dig l below.1, below.2 + 1 + joinCost l below.1)
      else
        let below := eraseCounted k n bs l
        (join dig below.1 r, below.2 + 1 + joinCost below.1 r)
  | _, _, .empty => (.empty, 1)
  | _, _, .leaf d rest k' v => (if k' = k then .empty else .leaf d rest k' v, 1)
  | _, _, .clash kvs => (clashOf dig (dropKey k kvs), kvs.length + 2)
  | _, _, .branch d l r => (.branch d l r, 1)

/-- **What an erase does**: exactly the key's entry leaves. -/
theorem eraseCounted_entries (k : K) : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D),
    Inv dig n t → KeyAt t.entries k bits →
      (eraseCounted dig k n bits t).1.entries = dropKey k t.entries
  | n + 1, b :: bs, .branch d l r, inv, at_ => by
      obtain ⟨il, ir, _, _⟩ := inv
      cases b with
      | false =>
          have atL : KeyAt l.entries k bs := keyAt_consBit (fun e he hk =>
            at_ e (List.mem_append_left _ he) hk)
          have absent := keyAt_absent (b := false) (bs := bs) (es := r.entries) (k := k)
            (fun e he hk => at_ e (List.mem_append_right _ he) hk)
          simp only [eraseCounted, Bool.false_eq_true, ite_false, join_entries, entries,
            eraseCounted_entries k n bs l il atL, dropKey_append, dropKey_consBit, absent]
      | true =>
          have atR : KeyAt r.entries k bs := keyAt_consBit (fun e he hk =>
            at_ e (List.mem_append_right _ he) hk)
          have absent := keyAt_absent (b := true) (bs := bs) (es := l.entries) (k := k)
            (fun e he hk => at_ e (List.mem_append_left _ he) hk)
          simp only [eraseCounted, ite_true, join_entries, entries,
            eraseCounted_entries k n bs r ir atR, dropKey_append, dropKey_consBit, absent]
  | 0, _, .branch .., inv, _ => by simp [Inv] at inv
  | _ + 1, [], .branch d l r, _, at_ => by
      simp only [eraseCounted]
      refine (dropKey_of_absent k _ fun e he hk => ?_).symm
      have := at_ e he hk
      simp only [entries, List.mem_append, List.mem_map] at he
      rcases he with ⟨x, _, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [consBit] at this
  | n, bits, .empty, _, _ => by cases n <;> cases bits <;> simp [eraseCounted, entries, dropKey_nil]
  | n, bits, .leaf d rest k' v, _, _ => by
      have : eraseCounted dig k n bits (.leaf d rest k' v) =
          (if k' = k then .empty else .leaf d rest k' v, 1) := by
        cases n <;> cases bits <;> rfl
      rw [this]
      by_cases same : k' = k
      · simp [same, entries, dropKey_cons_eq, dropKey_nil]
      · simp [same, entries, dropKey_cons_ne k (k', rest, v) [] same, dropKey_nil]
  | n, bits, .clash kvs, _, _ => by
      have : eraseCounted dig k n bits (.clash kvs) = (clashOf dig (dropKey k kvs), kvs.length + 2) := by
        cases n <;> cases bits <;> rfl
      rw [this, clashOf_entries]
      simp only [entries]
      unfold dropKey
      rw [List.filter_map]
      rfl

/-- **An erase keeps the cache well formed.** -/
theorem eraseCounted_inv (k : K) : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D),
    Inv dig n t → Inv dig n (eraseCounted dig k n bits t).1
  | n + 1, b :: bs, .branch d l r, inv => by
      obtain ⟨il, ir, _, _⟩ := inv
      cases b with
      | false => exact join_inv dig n _ r (eraseCounted_inv k n bs l il) ir
      | true => exact join_inv dig n l _ il (eraseCounted_inv k n bs r ir)
  | 0, _, .branch .., inv => by simp [Inv] at inv
  | _ + 1, [], .branch d l r, inv => inv
  | n, bits, .empty, _ => by cases n <;> cases bits <;> trivial
  | n, bits, .leaf d rest k' v, inv => by
      have : eraseCounted dig k n bits (.leaf d rest k' v) =
          (if k' = k then .empty else .leaf d rest k' v, 1) := by
        cases n <;> cases bits <;> rfl
      rw [this]
      by_cases same : k' = k
      · simp only [same, ite_true]
        cases n <;> trivial
      · simpa [same] using inv
  | 0, bits, .clash kvs, _ => by
      have : eraseCounted dig k 0 bits (.clash kvs) = (clashOf dig (dropKey k kvs), kvs.length + 2) := by
        cases bits <;> rfl
      rw [this]
      exact clashOf_inv dig _
  | _ + 1, _, .clash _, inv => by simp [Inv] at inv

/-- No `clash` bucket anywhere in the trie. -/
def NoClash : Trie K V D → Prop
  | .empty => True
  | .leaf .. => True
  | .branch _ l r => NoClash l ∧ NoClash r
  | .clash _ => False

omit [DecidableEq K] in
/-- Distinct remaining paths leave no clash bucket in a well-formed trie. -/
theorem noClash_of_nodup : ∀ (n : Nat) (t : Trie K V D), Inv dig n t → (t.entries.map (·.2.1)).Nodup →
    NoClash t
  | _, .empty, _, _ => trivial
  | _, .leaf .., _, _ => trivial
  | 0, .branch .., inv, _ => by simp [Inv] at inv
  | n + 1, .branch _ l r, inv, nd => by
      simp only [entries, List.map_append, List.map_map] at nd
      have ⟨ndl, ndr, _⟩ := List.nodup_append.mp nd
      refine ⟨noClash_of_nodup n l inv.1 ?_, noClash_of_nodup n r inv.2.1 ?_⟩
      · refine List.Nodup.of_map (List.cons false) ?_
        simpa [List.map_map, Function.comp_def, consBit] using ndl
      · refine List.Nodup.of_map (List.cons true) ?_
        simpa [List.map_map, Function.comp_def, consBit] using ndr
  | 0, .clash kvs, inv, nd => by
      match kvs, inv, nd with
      | [], inv, _ => simp [Inv] at inv
      | [_], inv, _ => simp [Inv] at inv
      | _ :: _ :: _, _, nd => simp [entries] at nd
  | _ + 1, .clash _, inv, _ => by simp [Inv] at inv

/-- **The counted bound**: with no clash, at most four per level (one visit,
at most three digest evaluations) and one at the bottom. -/
theorem eraseCounted_count (k : K) : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D),
    NoClash t → (eraseCounted dig k n bits t).2 ≤ 4 * n + 1
  | n + 1, b :: bs, .branch d l r, nc => by
      cases b with
      | false =>
          have := eraseCounted_count k n bs l nc.1
          have := joinCost_le_three (eraseCounted dig k n bs l).1 r
          simp only [eraseCounted, Bool.false_eq_true, ite_false]
          omega
      | true =>
          have := eraseCounted_count k n bs r nc.2
          have := joinCost_le_three l (eraseCounted dig k n bs r).1
          simp only [eraseCounted, ite_true]
          omega
  | 0, _, .branch .., _ => by simp [eraseCounted]
  | _ + 1, [], .branch .., _ => by simp [eraseCounted]
  | n, bits, .empty, _ => by cases n <;> cases bits <;> simp [eraseCounted]
  | n, bits, .leaf .., _ => by cases n <;> cases bits <;> simp [eraseCounted]
  | _, _, .clash _, nc => nc.elim

end Trie

/-! ## The cache -/

section CacheErase

variable {K V D : Type} [DecidableEq K] {dig : NodeIn K V D → D}

open Trie

/-- A key's last value after dropping a key. -/
theorem lastVal_dropKey (k : K) : ∀ (es : List (K × V)) (j : K),
    lastVal (dropKey k es) j = if j = k then none else lastVal es j
  | [], j => by simp [dropKey_nil, lastVal]
  | e :: rest, j => by
      have ih := lastVal_dropKey k rest j
      by_cases ek : e.1 = k
      · rw [dropKey_cons_eq k e rest ek, ih, lastVal_cons]
        by_cases jk : j = k
        · simp [jk]
        · have : e.1 ≠ j := fun h => jk (h ▸ ek)
          simp [jk, this]
      · rw [dropKey_cons_ne k e rest ek, lastVal_cons, lastVal_cons, ih]
        by_cases jk : j = k
        · subst jk
          simp [ek]
        · simp [jk]

theorem canon_dropKey (k : K) (es : List (K × V)) : (dropKey k (canon es)).Perm (canon (dropKey k es)) := by
  refine (List.perm_ext_iff_of_nodup
    (nodup_of_nodupKeys (((dropKey_sublist k _).map _).nodup (nodupKeys_canon es)))
    (nodup_of_nodupKeys (nodupKeys_canon _))).mpr fun x => ?_
  rw [mem_dropKey, mem_canon, mem_canon, lastVal_dropKey]
  by_cases h : x.1 = k <;> simp [h]

namespace Cache

variable {bitsOf : K → List Bool} {L : Nat}

/-- Erase `k`: one walk, at most one branch digest per level re-joined on it, and the count. -/
def eraseCounted (cache : Cache dig bitsOf L) (k : K) : Cache dig bitsOf L × Nat :=
  let r := Trie.eraseCounted dig k L (bitsOf k) cache.trie
  have at_ : KeyAt cache.trie.entries k (bitsOf k) := fun e he hk => by rw [cache.paths e he, hk]
  have same := Trie.eraseCounted_entries dig k L (bitsOf k) cache.trie cache.inv at_
  ({ trie := r.1
     inv := Trie.eraseCounted_inv dig k L (bitsOf k) cache.trie cache.inv
     paths := fun e he => by
       rw [same] at he
       exact cache.paths e (mem_dropKey.mp he).1
     nodup := by
       rw [same]
       exact ((dropKey_sublist k _).map _).nodup cache.nodup }, r.2)

/-- Erase `k`. -/
def erase (cache : Cache dig bitsOf L) (k : K) : Cache dig bitsOf L := (cache.eraseCounted k).1

theorem erase_holds {cache : Cache dig bitsOf L} {es : List (K × V)} (h : cache.Holds es) (k : K) :
    (cache.erase k).Holds (dropKey k es) := by
  unfold Holds
  have at_ : KeyAt cache.trie.entries k (bitsOf k) := fun e he hk => by rw [cache.paths e he, hk]
  show (Trie.eraseCounted dig k L (bitsOf k) cache.trie).1.entries.Perm _
  rw [Trie.eraseCounted_entries dig k L (bitsOf k) cache.trie cache.inv at_]
  refine (h.filter _).trans ?_
  have : dropKey k (AuthTrie.entries bitsOf (canon es)) = AuthTrie.entries bitsOf (dropKey k (canon es)) := by
    unfold dropKey AuthTrie.entries
    rw [List.filter_map]
    rfl
  unfold dropKey at this
  rw [this]
  exact (canon_dropKey k es).map _

theorem eraseCounted_count [DecidableEq V] [DecidableEq D] {cache : Cache dig bitsOf L} {es : List (K × V)} (h : cache.Holds es)
    (inj : PathsInjective bitsOf es) (k : K) : (cache.eraseCounted k).2 ≤ 4 * L + 1 := by
  have := Trie.eraseCounted_count dig k L (bitsOf k) cache.trie
    (noClash_of_nodup dig L cache.trie cache.inv (paths_nodup h inj))
  simpa [eraseCounted] using this

end Cache

end CacheErase

end Minidregg.Theory.AuthTrie
