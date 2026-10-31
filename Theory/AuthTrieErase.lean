/-
# Theory.AuthTrieErase — removing a key from the kept trie along one walk

`Trie.erase` walks the key's path once, removes its entry, and re-joins each
branch on the way up: a branch left holding one entry becomes that entry's leaf
one level higher (a leaf's digest does not depend on its remaining bits, so the
lone leaf rises without rehashing), anything else is a branch with a fresh
digest.

* `erase_entries`: the trie's entries lose exactly the key's entry.
* `erase_inv`: `Inv` is kept, with no premise beyond `Inv` itself.
* `Cache.erase_holds`: a cache holding `es` holds `dropKey k es` after erasing
  `k` (the `EraseCorrect` target of `Theory.PrivateCellTrie`).

**Cost is the interpreter's count, not the operation's.** `eraseM` is the same
walk written over node handles and three operations (`Ops`: hash, load,
store). Instantiated at `Prog`, a program whose every operation is a
constructor, with handles that are heap indices, it is interpreted by `run`
over a heap, one per operation and a clash load charged its size. The program
receives only the root's handle, so it reaches a node's contents only by loading
it. `eraseM_sim`: on any heap representing the trie (`Repr`), the result handle
represents `Trie.erase`, the heap only grows, and on a trie with no clash the
count is at most `7 * n + 3`. The count is of abstract operations on a heap with
constant-time access: `run`'s list heap is a model (its indexing is not
constant time), and pure computation between operations is not metered.
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

/-- Remove `k` along the walk `bits`. -/
def erase (k : K) : Nat → List Bool → Trie K V D → Trie K V D
  | n + 1, b :: bs, .branch _ l r =>
      if b then join dig l (erase k n bs r) else join dig (erase k n bs l) r
  | _, _, .empty => .empty
  | _, _, .leaf d rest k' v => if k' = k then .empty else .leaf d rest k' v
  | _, _, .clash kvs => clashOf dig (dropKey k kvs)
  | _, _, .branch d l r => .branch d l r

/-- **What an erase does**: exactly the key's entry leaves. -/
theorem erase_entries (k : K) : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D),
    Inv dig n t → KeyAt t.entries k bits →
      (erase dig k n bits t).entries = dropKey k t.entries
  | n + 1, b :: bs, .branch d l r, inv, at_ => by
      obtain ⟨il, ir, _, _⟩ := inv
      cases b with
      | false =>
          have atL : KeyAt l.entries k bs := keyAt_consBit (fun e he hk =>
            at_ e (List.mem_append_left _ he) hk)
          have absent := keyAt_absent (b := false) (bs := bs) (es := r.entries) (k := k)
            (fun e he hk => at_ e (List.mem_append_right _ he) hk)
          simp only [erase, Bool.false_eq_true, ite_false, join_entries, entries,
            erase_entries k n bs l il atL, dropKey_append, dropKey_consBit, absent]
      | true =>
          have atR : KeyAt r.entries k bs := keyAt_consBit (fun e he hk =>
            at_ e (List.mem_append_right _ he) hk)
          have absent := keyAt_absent (b := true) (bs := bs) (es := l.entries) (k := k)
            (fun e he hk => at_ e (List.mem_append_left _ he) hk)
          simp only [erase, ite_true, join_entries, entries,
            erase_entries k n bs r ir atR, dropKey_append, dropKey_consBit, absent]
  | 0, _, .branch .., inv, _ => by simp [Inv] at inv
  | _ + 1, [], .branch d l r, _, at_ => by
      simp only [erase]
      refine (dropKey_of_absent k _ fun e he hk => ?_).symm
      have := at_ e he hk
      simp only [entries, List.mem_append, List.mem_map] at he
      rcases he with ⟨x, _, rfl⟩ | ⟨x, _, rfl⟩ <;> simp [consBit] at this
  | n, bits, .empty, _, _ => by cases n <;> cases bits <;> simp [erase, entries, dropKey_nil]
  | n, bits, .leaf d rest k' v, _, _ => by
      have : erase dig k n bits (.leaf d rest k' v) =
          (if k' = k then .empty else .leaf d rest k' v) := by
        cases n <;> cases bits <;> rfl
      rw [this]
      by_cases same : k' = k
      · simp [same, entries, dropKey_cons_eq, dropKey_nil]
      · simp [same, entries, dropKey_cons_ne k (k', rest, v) [] same, dropKey_nil]
  | n, bits, .clash kvs, _, _ => by
      have : erase dig k n bits (.clash kvs) = clashOf dig (dropKey k kvs) := by
        cases n <;> cases bits <;> rfl
      rw [this, clashOf_entries]
      simp only [entries]
      unfold dropKey
      rw [List.filter_map]
      rfl

/-- **An erase keeps the cache well formed.** -/
theorem erase_inv (k : K) : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D),
    Inv dig n t → Inv dig n (erase dig k n bits t)
  | n + 1, b :: bs, .branch d l r, inv => by
      obtain ⟨il, ir, _, _⟩ := inv
      cases b with
      | false => exact join_inv dig n _ r (erase_inv k n bs l il) ir
      | true => exact join_inv dig n l _ il (erase_inv k n bs r ir)
  | 0, _, .branch .., inv => by simp [Inv] at inv
  | _ + 1, [], .branch d l r, inv => inv
  | n, bits, .empty, _ => by cases n <;> cases bits <;> trivial
  | n, bits, .leaf d rest k' v, inv => by
      have : erase dig k n bits (.leaf d rest k' v) =
          (if k' = k then .empty else .leaf d rest k' v) := by
        cases n <;> cases bits <;> rfl
      rw [this]
      by_cases same : k' = k
      · simp only [same, ite_true]
        cases n <;> trivial
      · simpa [same] using inv
  | 0, bits, .clash kvs, _ => by
      have : erase dig k 0 bits (.clash kvs) = clashOf dig (dropKey k kvs) := by
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

omit [DecidableEq K] in
theorem join_noClash (l r : Trie K V D) (nl : NoClash l) (nr : NoClash r) : NoClash (join dig l r) := by
  cases l <;> cases r <;> first | exact nl.elim | exact nr.elim | exact trivial | exact ⟨nl, nr⟩

/-- Erasing from a trie with no clash leaves none. -/
theorem erase_noClash (k : K) : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D),
    NoClash t → NoClash (erase dig k n bits t)
  | n + 1, b :: bs, .branch d l r, nc => by
      cases b with
      | false => exact join_noClash dig _ r (erase_noClash k n bs l nc.1) nc.2
      | true => exact join_noClash dig l _ nc.1 (erase_noClash k n bs r nc.2)
  | 0, _, .branch .., nc => nc
  | _ + 1, [], .branch .., nc => nc
  | n, bits, .empty, _ => by cases n <;> cases bits <;> trivial
  | n, bits, .leaf d rest k' v, _ => by
      have : erase dig k n bits (.leaf d rest k' v) =
          (if k' = k then .empty else .leaf d rest k' v) := by
        cases n <;> cases bits <;> rfl
      rw [this]
      split <;> trivial
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

/-- Erase `k`: one walk. -/
def erase (cache : Cache dig bitsOf L) (k : K) : Cache dig bitsOf L :=
  have at_ : KeyAt cache.trie.entries k (bitsOf k) := fun e he hk => by rw [cache.paths e he, hk]
  have same := Trie.erase_entries dig k L (bitsOf k) cache.trie cache.inv at_
  { trie := Trie.erase dig k L (bitsOf k) cache.trie
    inv := Trie.erase_inv dig k L (bitsOf k) cache.trie cache.inv
    paths := fun e he => by
      rw [same] at he
      exact cache.paths e (mem_dropKey.mp he).1
    nodup := by
      rw [same]
      exact ((dropKey_sublist k _).map _).nodup cache.nodup }

theorem erase_holds {cache : Cache dig bitsOf L} {es : List (K × V)} (h : cache.Holds es) (k : K) :
    (cache.erase k).Holds (dropKey k es) := by
  unfold Holds
  have at_ : KeyAt cache.trie.entries k (bitsOf k) := fun e he hk => by rw [cache.paths e he, hk]
  show (Trie.erase dig k L (bitsOf k) cache.trie).entries.Perm _
  rw [Trie.erase_entries dig k L (bitsOf k) cache.trie cache.inv at_]
  refine (h.filter _).trans ?_
  have : dropKey k (AuthTrie.entries bitsOf (canon es)) = AuthTrie.entries bitsOf (dropKey k (canon es)) := by
    unfold dropKey AuthTrie.entries
    rw [List.filter_map]
    rfl
  unfold dropKey at this
  rw [this]
  exact (canon_dropKey k es).map _

end Cache

end CacheErase


/-! ## The erase over an oracle: cost charged by the handler -/

/-- One layer of a node, its children as handles. -/
inductive Layer (K V D N : Type) where
  | empty
  | leaf (d : D) (rest : List Bool) (k : K) (v : V)
  | branch (d : D) (left right : N)
  | clash (kvs : List (K × V))

/-- What a trie algorithm may do with nodes it cannot see: hash a node, load a
handle's layer, store a layer as a new handle. -/
structure Ops (M : Type → Type) (K V D N : Type) where
  hash : NodeIn K V D → M D
  load : N → M (Layer K V D N)
  store : Layer K V D N → M N

namespace Trie

variable {K V D : Type}

def layer : Trie K V D → Layer K V D (Trie K V D)
  | .empty => .empty
  | .leaf d rest k v => .leaf d rest k v
  | .branch d l r => .branch d l r
  | .clash kvs => .clash kvs

def ofLayer : Layer K V D (Trie K V D) → Trie K V D
  | .empty => .empty
  | .leaf d rest k v => .leaf d rest k v
  | .branch d l r => .branch d l r
  | .clash kvs => .clash kvs

/-- The entries a load charges for: a clash bucket's size, else none. -/
def clashSize : Trie K V D → Nat
  | .clash kvs => kvs.length
  | _ => 0

end Trie

section Oracle

variable {K V D : Type} [DecidableEq K] {M : Type → Type} [Monad M] {N : Type}
variable (ops : Ops M K V D N)

/-- A layer's digest: cached for a leaf or branch, the empty node's otherwise. -/
def layerDigest : Layer K V D N → M D
  | .empty => ops.hash .empty
  | .leaf d .. => pure d
  | .branch d .. => pure d
  | .clash _ => ops.hash .empty

/-- `Trie.join` over handles. -/
def joinM (l r : N) : M N := do
  let ll ← ops.load l
  let rl ← ops.load r
  match ll, rl with
  | .empty, .empty => ops.store .empty
  | .empty, .leaf d rest k v => ops.store (.leaf d (true :: rest) k v)
  | .leaf d rest k v, .empty => ops.store (.leaf d (false :: rest) k v)
  | ll, rl => do
      let dl ← layerDigest ops ll
      let dr ← layerDigest ops rl
      let d ← ops.hash (.branch dl dr)
      ops.store (.branch d l r)

/-- `Trie.clashOf` over handles. -/
def clashM : List (K × V) → M N
  | [] => ops.store .empty
  | [kv] => do
      let d ← ops.hash (.leaf kv.1 kv.2)
      ops.store (.leaf d [] kv.1 kv.2)
  | kvs@(_ :: _ :: _) => ops.store (.clash kvs)

/-- Where the walk stops: the loaded layer of handle `x`. -/
def finishM (k : K) (x : N) : Layer K V D N → M N
  | .empty => pure x
  | .leaf _ _ k' _ => if k' = k then ops.store .empty else pure x
  | .branch .. => pure x
  | .clash kvs => clashM ops (Trie.dropKey k kvs)

/-- **The erase over an oracle**: `Trie.erase`, seeing nodes only through `ops`. -/
def eraseM (k : K) : Nat → List Bool → N → M N
  | n + 1, b :: bs, x => do
      let layer ← ops.load x
      match layer with
      | .branch _ l r =>
          if b then do
            let r' ← eraseM k n bs r
            joinM ops l r'
          else do
            let l' ← eraseM k n bs l
            joinM ops l' r
      | layer => finishM ops k x layer
  | _, _, x => do
      let layer ← ops.load x
      finishM ops k x layer

end Oracle

/-! ### Programs over a heap: the cost is the interpreter's -/

/-- A trie program: every digest, node read and node write is an operation the
interpreter performs; a handle is a heap index, so the program reaches a node's
contents only by loading it. -/
inductive Prog (K V D α : Type) where
  | done (a : α)
  | hash (x : NodeIn K V D) (next : D → Prog K V D α)
  | load (handle : Nat) (next : Layer K V D Nat → Prog K V D α)
  | store (layer : Layer K V D Nat) (next : Nat → Prog K V D α)

namespace Prog

variable {K V D : Type}

def bind {α β : Type} : Prog K V D α → (α → Prog K V D β) → Prog K V D β
  | .done a, f => f a
  | .hash x next, f => .hash x fun d => (next d).bind f
  | .load h next, f => .load h fun l => (next l).bind f
  | .store l next, f => .store l fun n => (next n).bind f

instance : Monad (Prog K V D) where
  pure := .done
  bind := bind

/-- The program's handles: hash, load and store, each one operation. -/
def ops : Ops (Prog K V D) K V D Nat := ⟨fun x => .hash x .done, fun h => .load h .done, fun l => .store l .done⟩

end Prog

/-- The heap: layer `h` is node `h`. -/
abbrev Heap (K V D : Type) := List (Layer K V D Nat)

def Layer.size {K V D N : Type} : Layer K V D N → Nat
  | .clash kvs => kvs.length
  | _ => 0

def Heap.get {K V D : Type} (heap : Heap K V D) (h : Nat) : Layer K V D Nat := (heap[h]?).getD .empty

/-- **The interpreter**: the result, the final heap, and the cost: one per
operation, and a clash layer's size when it is loaded. -/
def run {K V D : Type} (dig : NodeIn K V D → D) {α : Type} : Heap K V D → Prog K V D α → α × Heap K V D × Nat
  | heap, .done a => (a, heap, 0)
  | heap, .hash x next =>
      let r := run dig heap (next (dig x))
      (r.1, r.2.1, r.2.2 + 1)
  | heap, .load h next =>
      let r := run dig heap (next (heap.get h))
      (r.1, r.2.1, r.2.2 + 1 + (heap.get h).size)
  | heap, .store l next =>
      let r := run dig (heap ++ [l]) (next heap.length)
      (r.1, r.2.1, r.2.2 + 1)

/-- Handle `h` of `heap` holds trie `t`. -/
def Repr {K V D : Type} (heap : Heap K V D) (h : Nat) : Trie K V D → Prop
  | .empty => heap[h]? = some .empty
  | .leaf d rest k v => heap[h]? = some (.leaf d rest k v)
  | .branch d l r => ∃ hl hr, heap[h]? = some (.branch d hl hr) ∧ Repr heap hl l ∧ Repr heap hr r
  | .clash kvs => heap[h]? = some (.clash kvs)

section Interpreter

variable {K V D : Type} (dig : NodeIn K V D → D)

@[simp] theorem run_done {α : Type} (heap : Heap K V D) (a : α) :
    run dig heap (pure a : Prog K V D α) = (a, heap, 0) := rfl

theorem run_bind {α β : Type} : ∀ (heap : Heap K V D) (p : Prog K V D α) (f : α → Prog K V D β),
    run dig heap (p >>= f) =
      ((run dig (run dig heap p).2.1 (f (run dig heap p).1)).1,
        (run dig (run dig heap p).2.1 (f (run dig heap p).1)).2.1,
        (run dig heap p).2.2 + (run dig (run dig heap p).2.1 (f (run dig heap p).1)).2.2)
  | heap, .done a, f => by
      show run dig heap (f a) = _
      simp [run]
  | heap, .hash x next, f => by
      show run dig heap (.hash x fun d => (next d).bind f) = _
      have := run_bind heap (next (dig x)) f
      simp only [run]
      rw [show (next (dig x)).bind f = next (dig x) >>= f from rfl, this]
      simp only [Prod.mk.injEq, true_and]
      omega
  | heap, .load h next, f => by
      show run dig heap (.load h fun l => (next l).bind f) = _
      have := run_bind heap (next (heap.get h)) f
      simp only [run]
      rw [show (next (heap.get h)).bind f = next (heap.get h) >>= f from rfl, this]
      simp only [Prod.mk.injEq, true_and]
      omega
  | heap, .store l next, f => by
      show run dig heap (.store l fun n => (next n).bind f) = _
      have := run_bind (heap ++ [l]) (next heap.length) f
      simp only [run]
      rw [show (next heap.length).bind f = next heap.length >>= f from rfl, this]
      simp only [Prod.mk.injEq, true_and]
      omega

@[simp] theorem run_hash (heap : Heap K V D) (x : NodeIn K V D) :
    run dig heap (Prog.ops.hash x) = (dig x, heap, 1) := rfl
@[simp] theorem run_load (heap : Heap K V D) (h : Nat) :
    run dig heap (Prog.ops.load h) = (heap.get h, heap, 1 + (heap.get h).size) := by
  simp [Prog.ops, run]
@[simp] theorem run_store (heap : Heap K V D) (l : Layer K V D Nat) :
    run dig heap (Prog.ops.store l) = (heap.length, heap ++ [l], 1) := rfl

theorem getElem?_append_of_some {α : Type} {heap more : List α} {h : Nat} {x : α}
    (at_ : heap[h]? = some x) : (heap ++ more)[h]? = some x := by
  obtain ⟨short, _⟩ := List.getElem?_eq_some_iff.mp at_
  rw [List.getElem?_append_left short]
  exact at_

theorem Repr.extend {heap : Heap K V D} (more : Heap K V D) :
    ∀ {h : Nat} {t : Trie K V D}, Repr heap h t → Repr (heap ++ more) h t
  | _, .empty, r => getElem?_append_of_some r
  | _, .leaf .., r => getElem?_append_of_some r
  | _, .clash _, r => getElem?_append_of_some r
  | _, .branch _ _ _, ⟨hl, hr, at_, rl, rr⟩ =>
      ⟨hl, hr, getElem?_append_of_some at_, Repr.extend more rl, Repr.extend more rr⟩

/-- The stored layer of a represented trie, its children as handles. -/
theorem Repr.get {heap : Heap K V D} {h : Nat} {t : Trie K V D} (r : Repr heap h t) :
    match t with
    | .empty => heap.get h = .empty
    | .leaf d rest k v => heap.get h = .leaf d rest k v
    | .branch d l r => ∃ hl hr, heap.get h = .branch d hl hr ∧ Repr heap hl l ∧ Repr heap hr r
    | .clash kvs => heap.get h = .clash kvs := by
  cases t with
  | empty => simp [Heap.get, show heap[h]? = some .empty from r]
  | leaf d rest k v => simp [Heap.get, show heap[h]? = some (.leaf d rest k v) from r]
  | clash kvs => simp [Heap.get, show heap[h]? = some (.clash kvs) from r]
  | branch d l rt =>
      obtain ⟨hl, hr, at_, rl, rr⟩ := r
      exact ⟨hl, hr, by simp [Heap.get, at_], rl, rr⟩

/-- A step of the simulation: the heap only grows, the result handle holds `t`,
and the cost is within `bound` when the input has no clash. -/
def Sim (heap : Heap K V D) (res : Nat × Heap K V D × Nat) (t : Trie K V D) (cost : Prop) : Prop :=
  (∃ more, res.2.1 = heap ++ more) ∧ Repr res.2.1 res.1 t ∧ cost

theorem repr_store (heap : Heap K V D) (l : Layer K V D Nat) :
    (heap ++ [l])[heap.length]? = some l := by simp

/-- Hashes `layerDigest` spends on a node: the empty node's digest for an empty
node or a clash, none for a cached digest. -/
def digestCostOf : Trie K V D → Nat
  | .empty => 1
  | .clash _ => 1
  | _ => 0

theorem layerDigest_sim {heap : Heap K V D} {h : Nat} {t : Trie K V D} (r : Repr heap h t) :
    run dig heap (layerDigest Prog.ops (heap.get h)) = (t.digest dig, heap, digestCostOf t) := by
  have g := r.get
  cases t <;> simp only at g <;>
    first
    | (rw [g]; rfl)
    | (obtain ⟨_, _, g, _, _⟩ := g; rw [g]; rfl)

end Interpreter


section Simulation

variable {K V D : Type} [DecidableEq K] (dig : NodeIn K V D → D)

open Trie

theorem Sim.trans {heap : Heap K V D} {mid : Nat × Heap K V D × Nat} {res : Nat × Heap K V D × Nat}
    {t u : Trie K V D} {c c' : Prop} (first : Sim heap mid t c) (second : Sim mid.2.1 res u c') :
    Sim heap res u c' := by
  obtain ⟨⟨more, grown⟩, _, _⟩ := first
  obtain ⟨⟨more', grown'⟩, r, cost⟩ := second
  exact ⟨⟨more ++ more', by rw [grown', grown, List.append_assoc]⟩, r, cost⟩

/-- Re-joining two represented children. -/
theorem joinM_sim {heap : Heap K V D} {hl hr : Nat} {l r : Trie K V D} (rl : Repr heap hl l)
    (rr : Repr heap hr r) :
    Sim heap (run dig heap (joinM Prog.ops hl hr)) (join dig l r)
      (NoClash l → NoClash r → (run dig heap (joinM Prog.ops hl hr)).2.2 ≤ 6) := by
  have gl := rl.get
  have gr := rr.get
  cases l <;> cases r <;> simp only at gl gr <;>
    (try obtain ⟨_, _, gl, _, _⟩ := gl) <;> (try obtain ⟨_, _, gr, _, _⟩ := gr) <;>
    simp only [Sim, joinM, run_bind, run_load, run_store, run_hash, run_done, gl, gr, layerDigest,
      Layer.size, join, mkBranch, Trie.digest, NoClash] <;>
    refine ⟨⟨_, rfl⟩, ?_, ?_⟩ <;>
    first
    | exact repr_store _ _
    | exact ⟨_, _, repr_store _ _, rl.extend _, rr.extend _⟩
    | (intro _ _; omega)
    | (intro nl nr; exact nl.elim)
    | (intro nl nr; exact nr.elim)

/-- A bucket after a removal. -/
theorem clashM_sim (heap : Heap K V D) (kvs : List (K × V)) :
    Sim heap (run dig heap (clashM Prog.ops kvs)) (clashOf dig kvs) True := by
  match kvs with
  | [] => exact ⟨⟨_, rfl⟩, by simp [clashM, clashOf, Repr], trivial⟩
  | [_] => exact ⟨⟨_, rfl⟩, by simp [clashM, clashOf, mkLeaf, Repr, run_bind], trivial⟩
  | _ :: _ :: _ => exact ⟨⟨_, rfl⟩, by simp [clashM, clashOf, Repr], trivial⟩

/-- Where the walk stops: load the handle and finish on its layer. -/
theorem finish_sim (k : K) (n : Nat) (bits : List Bool) {heap : Heap K V D} {x : Nat} {t : Trie K V D}
    (rx : Repr heap x t) (stops : ∀ b bs m d l r, n = m + 1 → bits = b :: bs → t ≠ .branch d l r) :
    Sim heap (run dig heap (Prog.ops.load x >>= fun layer => finishM Prog.ops k x layer))
      (erase dig k n bits t)
      (NoClash t → (run dig heap (Prog.ops.load x >>= fun layer => finishM Prog.ops k x layer)).2.2 ≤ 3) := by
  have g := rx.get
  have eraseEq : ∀ d l r, t = .branch d l r → erase dig k n bits t = t := by
    rintro d l r rfl
    cases n with
    | zero => rfl
    | succ m =>
        cases bits with
        | nil => rfl
        | cons b bs => exact absurd rfl (stops b bs m d l r rfl rfl)
  cases t with
  | empty =>
      simp only at g
      have : erase dig k n bits .empty = .empty := by cases n <;> cases bits <;> rfl
      rw [this]
      simp only [Sim, run_bind, run_load, g, finishM, run_done, Layer.size]
      exact ⟨⟨[], by simp⟩, rx, fun _ => by omega⟩
  | leaf d rest k' v =>
      simp only at g
      have : erase dig k n bits (.leaf d rest k' v) = (if k' = k then .empty else .leaf d rest k' v) := by
        cases n <;> cases bits <;> rfl
      rw [this]
      by_cases same : k' = k
      · simp only [Sim, run_bind, run_load, g, finishM, same, ite_true, run_store, Layer.size]
        exact ⟨⟨_, rfl⟩, by simp [Repr], fun _ => by omega⟩
      · simp only [Sim, run_bind, run_load, g, finishM, same, ite_false, run_done, Layer.size]
        exact ⟨⟨[], by simp⟩, rx, fun _ => by omega⟩
  | branch d l r =>
      obtain ⟨_, _, g, _, _⟩ := g
      rw [eraseEq d l r rfl]
      simp only [Sim, run_bind, run_load, g, finishM, run_done, Layer.size]
      exact ⟨⟨[], by simp⟩, rx, fun _ => by omega⟩
  | clash kvs =>
      simp only at g
      have : erase dig k n bits (.clash kvs) = clashOf dig (dropKey k kvs) := by
        cases n <;> cases bits <;> rfl
      rw [this]
      obtain ⟨grown, r, _⟩ := clashM_sim dig heap (dropKey k kvs)
      simp only [Sim, run_bind, run_load, g, finishM, Layer.size]
      exact ⟨grown, r, fun nc => nc.elim⟩

/-- **The heap simulation**: the program erase leaves a handle holding
`Trie.erase`, only grows the heap, and on a trie with no clash spends at most
`7 * n + 3` interpreter operations. -/
theorem eraseM_sim (k : K) : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D) (heap : Heap K V D) (x : Nat),
    Repr heap x t →
      Sim heap (run dig heap (eraseM Prog.ops k n bits x)) (erase dig k n bits t)
        (NoClash t → (run dig heap (eraseM Prog.ops k n bits x)).2.2 ≤ 7 * n + 3)
  | 0, bits, t, heap, x, rx => by
      have := finish_sim dig k 0 bits rx (fun _ _ _ _ _ _ h => by cases h)
      have e : eraseM (Prog.ops (K := K) (V := V) (D := D)) k 0 bits x =
          (Prog.ops.load x >>= fun layer => finishM Prog.ops k x layer) := by
        cases bits <;> rfl
      rw [e]
      exact ⟨this.1, this.2.1, fun nc => by have := this.2.2 nc; omega⟩
  | n + 1, [], t, heap, x, rx => by
      have := finish_sim dig k (n + 1) [] rx (fun _ _ _ _ _ _ _ h => by cases h)
      have e : eraseM (Prog.ops (K := K) (V := V) (D := D)) k (n + 1) [] x =
          (Prog.ops.load x >>= fun layer => finishM Prog.ops k x layer) := rfl
      rw [e]
      exact ⟨this.1, this.2.1, fun nc => by have := this.2.2 nc; omega⟩
  | n + 1, b :: bs, .branch d l r, heap, x, rx => by
      obtain ⟨hl, hr, at_, rl, rr⟩ := rx
      have g : heap.get x = .branch d hl hr := by simp [Heap.get, at_]
      cases b with
      | true =>
          have below := eraseM_sim k n bs r heap hr rr
          obtain ⟨⟨more, grown⟩, rBelow, costBelow⟩ := below
          have joined := joinM_sim dig (rl.extend more |> (grown ▸ ·)) rBelow
          simp only [eraseM, run_bind, run_load, g, Layer.size, ite_true]
          refine (Sim.trans ⟨⟨more, grown⟩, rBelow, trivial⟩ joined).imp_right fun ⟨r', _⟩ => ⟨?_, ?_⟩
          · exact r'
          · intro nc
            have c1 := costBelow nc.2
            have c2 := joined.2.2 nc.1 (erase_noClash dig k n bs r nc.2)
            omega
      | false =>
          have below := eraseM_sim k n bs l heap hl rl
          obtain ⟨⟨more, grown⟩, rBelow, costBelow⟩ := below
          have joined := joinM_sim dig rBelow (rr.extend more |> (grown ▸ ·))
          simp only [eraseM, run_bind, run_load, g, Layer.size, Bool.false_eq_true, ite_false]
          refine (Sim.trans ⟨⟨more, grown⟩, rBelow, trivial⟩ joined).imp_right fun ⟨r', _⟩ => ⟨?_, ?_⟩
          · exact r'
          · intro nc
            have c1 := costBelow nc.1
            have c2 := joined.2.2 (erase_noClash dig k n bs l nc.1) nc.2
            omega
  | n + 1, b :: bs, .empty, heap, x, rx => by
      have := finish_sim dig k (n + 1) (b :: bs) rx (fun _ _ _ _ _ _ _ _ h => by cases h)
      have g := rx.get
      simp only at g
      simp only [eraseM, run_bind, run_load, g] at this ⊢
      exact ⟨this.1, this.2.1, fun nc => by have := this.2.2 nc; omega⟩
  | n + 1, b :: bs, .leaf d rest k' v, heap, x, rx => by
      have := finish_sim dig k (n + 1) (b :: bs) rx (fun _ _ _ _ _ _ _ _ h => by cases h)
      have g := rx.get
      simp only at g
      simp only [eraseM, run_bind, run_load, g] at this ⊢
      exact ⟨this.1, this.2.1, fun nc => by have := this.2.2 nc; omega⟩
  | n + 1, b :: bs, .clash kvs, heap, x, rx => by
      have := finish_sim dig k (n + 1) (b :: bs) rx (fun _ _ _ _ _ _ _ _ h => by cases h)
      have g := rx.get
      simp only at g
      simp only [eraseM, run_bind, run_load, g] at this ⊢
      exact ⟨this.1, this.2.1, fun nc => nc.elim⟩

end Simulation

/-- Store a trie in a heap, children first. -/
def storeTrie {K V D : Type} : Trie K V D → Heap K V D → Nat × Heap K V D
  | .empty, heap => (heap.length, heap ++ [.empty])
  | .leaf d rest k v, heap => (heap.length, heap ++ [.leaf d rest k v])
  | .clash kvs, heap => (heap.length, heap ++ [.clash kvs])
  | .branch d l r, heap =>
      let left := storeTrie l heap
      let right := storeTrie r left.2
      (right.2.length, right.2 ++ [.branch d left.1 right.1])

theorem storeTrie_repr {K V D : Type} : ∀ (t : Trie K V D) (heap : Heap K V D),
    (∃ more, (storeTrie t heap).2 = heap ++ more) ∧ Repr (storeTrie t heap).2 (storeTrie t heap).1 t
  | .empty, heap => ⟨⟨_, rfl⟩, by simp [storeTrie, Repr]⟩
  | .leaf .., heap => ⟨⟨_, rfl⟩, by simp [storeTrie, Repr]⟩
  | .clash _, heap => ⟨⟨_, rfl⟩, by simp [storeTrie, Repr]⟩
  | .branch d l r, heap => by
      obtain ⟨⟨moreL, grownL⟩, reprL⟩ := storeTrie_repr l heap
      obtain ⟨⟨moreR, grownR⟩, reprR⟩ := storeTrie_repr r (storeTrie l heap).2
      have stored : storeTrie (.branch d l r) heap =
          ((storeTrie r (storeTrie l heap).2).2.length,
            (storeTrie r (storeTrie l heap).2).2 ++
              [.branch d (storeTrie l heap).1 (storeTrie r (storeTrie l heap).2).1]) := rfl
      rw [stored]
      refine ⟨⟨moreL ++ moreR ++ [Layer.branch d (storeTrie l heap).1 (storeTrie r (storeTrie l heap).2).1], ?_⟩, ?_⟩
      · generalize (Layer.branch d (storeTrie l heap).1 (storeTrie r (storeTrie l heap).2).1 :
          Layer K V D Nat) = top
        show (storeTrie r (storeTrie l heap).2).2 ++ [top] = _
        rw [grownR, grownL]
        simp
      exact ⟨_, _, repr_store _ _, (by rw [grownR]; exact reprL.extend moreR : Repr _ _ l).extend _,
        reprR.extend _⟩

namespace Cache

variable {K V D : Type} [DecidableEq K] {dig : NodeIn K V D → D} {bitsOf : K → List Bool} {L : Nat}

/-- **The program erase on a cache**: on any heap holding the cache's trie, the
result handle holds the cache's erase, and on live keys with distinct paths the
interpreter spends at most `7 * L + 3` operations. -/
theorem eraseM_cache [DecidableEq V] [DecidableEq D] {cache : Cache dig bitsOf L} {es : List (K × V)}
    (h : cache.Holds es) (k : K) {heap : Heap K V D} {x : Nat} (rx : Repr heap x cache.trie) :
    Repr (run dig heap (eraseM Prog.ops k L (bitsOf k) x)).2.1 (run dig heap (eraseM Prog.ops k L (bitsOf k) x)).1
        (cache.erase k).trie ∧
      (PathsInjective bitsOf es → (run dig heap (eraseM Prog.ops k L (bitsOf k) x)).2.2 ≤ 7 * L + 3) := by
  obtain ⟨_, r, cost⟩ := eraseM_sim dig k L (bitsOf k) cache.trie heap x rx
  exact ⟨r, fun inj => cost (Trie.noClash_of_nodup dig L cache.trie cache.inv (paths_nodup h inj))⟩

end Cache

end Minidregg.Theory.AuthTrie
