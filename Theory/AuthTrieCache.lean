/-
# Theory.AuthTrieCache — the compressed trie, kept: one root, maintained by inserts

`Theory.AuthTrie.tree` is the canonical root of an entry list. This module keeps
the evaluated trie (`Trie`: every branch carries its digest) and proves it equal
to that root, so a process can hold the trie and advance it by inserts:

* `tree_perm`: the canonical root depends only on the entries, not their order.
* `Trie.digest_eq`: a trie satisfying `Inv` has digest `tree n` of its entries.
* `Trie.build` (bulk, one digest per branch and leaf) and `Trie.insert` (one per
  branch on the key's walk, about `log₂ n`, never `n`) keep `Inv`; an insert
  removes the key's old entry and adds the new one (`insert_entries`).
* `root bitsOf L es`: the root of a key/value list, last value per key wins
  (`canon`); `root_congr`: two lists giving every key the same last value have
  one root. `Cache.root_eq`: a cache built and advanced from `es` has that root.
* `Trie.opening` / `opening_complete`: the honest walk is an `AuthTrie.Opening`
  that `verify` accepts — the completeness `AuthTrie` left open.

A key that shares its whole path with another (an index collision) is a `clash`
at height 0, whose digest is what `tree` gives there (`dig .empty`), so even
then the cache is the specification: no premise, no fallback rebuild.
-/
module

public import Theory.AuthTrie
public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Perm.Basic

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

@[expose] public section

namespace Minidregg.Theory.AuthTrie

set_option autoImplicit false
set_option linter.unusedSectionVars false

section Perm

variable {K V D : Type} (dig : NodeIn K V D → D)

theorem strip_perm (b : Bool) {es es' : List (Entry K V)} (h : es.Perm es') :
    (strip b es).Perm (strip b es') := h.filterMap _

theorem tree_nil (n : Nat) : tree dig n ([] : List (Entry K V)) = dig .empty := by
  cases n <;> rfl

theorem tree_single (n : Nat) (e : Entry K V) : tree dig n [e] = dig (.leaf e.1 e.2.2) := by
  cases n <;> rfl

theorem tree_zero_two {es : List (Entry K V)} (two : 2 ≤ es.length) : tree dig 0 es = dig .empty := by
  match es, two with
  | _ :: _ :: _, _ => rfl

theorem tree_succ_two (n : Nat) {es : List (Entry K V)} (two : 2 ≤ es.length) :
    tree dig (n + 1) es = dig (.branch (tree dig n (strip false es)) (tree dig n (strip true es))) := by
  match es, two with
  | _ :: _ :: _, _ => rfl

/-- **The canonical root is a function of the entries, not their order.** -/
theorem tree_perm : ∀ (n : Nat) {es es' : List (Entry K V)}, es.Perm es' → tree dig n es = tree dig n es'
  | n, [], es', h => by rw [List.Perm.nil_eq h]
  | n, [e], es', h => by rw [List.perm_singleton.mp h.symm]
  | 0, a :: b :: rest, es', h => by
      rw [tree_zero_two dig (by simp), tree_zero_two dig (by rw [← h.length_eq]; simp)]
  | n + 1, a :: b :: rest, es', h => by
      rw [tree_succ_two dig n (by simp), tree_succ_two dig n (by rw [← h.length_eq]; simp),
        tree_perm n (strip_perm false h), tree_perm n (strip_perm true h)]

end Perm

/-! ## The kept trie -/

/-- The evaluated trie: every leaf and branch carries its digest; a key alone under a
prefix is a leaf holding its remaining bits; keys sharing a whole path are a
`clash` (height 0 only). -/
inductive Trie (K V D : Type) where
  | empty
  | leaf (d : D) (rest : List Bool) (k : K) (v : V)
  | branch (d : D) (left right : Trie K V D)
  | clash (kvs : List (K × V))

namespace Trie

variable {K V D : Type} (dig : NodeIn K V D → D)

def digest : Trie K V D → D
  | .empty => dig .empty
  | .leaf d _ _ _ => d
  | .branch d _ _ => d
  | .clash _ => dig .empty

/-- Put one bit in front of an entry's remaining path. -/
def consBit (b : Bool) (e : Entry K V) : Entry K V := (e.1, b :: e.2.1, e.2.2)

/-- The entries a trie holds, with their remaining bits. -/
def entries : Trie K V D → List (Entry K V)
  | .empty => []
  | .leaf _ rest k v => [(k, rest, v)]
  | .branch _ l r => l.entries.map (consBit false) ++ r.entries.map (consBit true)
  | .clash kvs => kvs.map fun kv => (kv.1, [], kv.2)

/-- A leaf, its digest computed once. -/
def mkLeaf (rest : List Bool) (k : K) (v : V) : Trie K V D := .leaf (dig (.leaf k v)) rest k v

/-- A branch over two children, its digest computed once. -/
def mkBranch (l r : Trie K V D) : Trie K V D := .branch (dig (.branch (l.digest dig) (r.digest dig))) l r

/-- The cached evaluation is well formed at height `n`. -/
def Inv : Nat → Trie K V D → Prop
  | _, .empty => True
  | n, .leaf d rest k v => rest.length = n ∧ d = dig (.leaf k v)
  | 0, .branch .. => False
  | n + 1, .branch d l r =>
      Inv n l ∧ Inv n r ∧ d = dig (.branch (l.digest dig) (r.digest dig)) ∧
        2 ≤ l.entries.length + r.entries.length
  | 0, .clash kvs => 2 ≤ kvs.length
  | _ + 1, .clash _ => False

theorem strip_false_branch (l r : List (Entry K V)) :
    strip false (l.map (consBit false) ++ r.map (consBit true)) = l := by
  simp [strip, List.filterMap_append, consBit, List.filterMap_map, Function.comp_def]

theorem strip_true_branch (l r : List (Entry K V)) :
    strip true (l.map (consBit false) ++ r.map (consBit true)) = r := by
  simp [strip, List.filterMap_append, consBit, List.filterMap_map, Function.comp_def]

/-- **The kept digest is the canonical root of the kept entries.** -/
theorem digest_eq : ∀ (n : Nat) (t : Trie K V D), Inv dig n t → t.digest dig = tree dig n t.entries
  | n, .empty, _ => by simp [digest, entries, tree_nil]
  | n, .leaf d rest k v, inv => by
      simp only [Inv] at inv
      simp [digest, entries, tree_single, inv.2]
  | 0, .branch .., inv => by simp [Inv] at inv
  | n + 1, .branch d l r, inv => by
      obtain ⟨il, ir, hd, two⟩ := inv
      simp only [digest, entries]
      rw [tree_succ_two dig n (by simpa using two), strip_false_branch, strip_true_branch,
        ← digest_eq n l il, ← digest_eq n r ir, hd]
  | 0, .clash kvs, inv => by
      simp only [Inv] at inv
      simp only [digest, entries]
      rw [tree_zero_two dig (by simpa using inv)]
  | _ + 1, .clash _, inv => by simp [Inv] at inv

/-! ### Bulk build: `tree`'s own recursion, keeping every digest -/

def build : Nat → List (Entry K V) → Trie K V D
  | _, [] => .empty
  | _, [e] => mkLeaf dig e.2.1 e.1 e.2.2
  | 0, es@(_ :: _ :: _) => .clash (es.map fun e => (e.1, e.2.2))
  | n + 1, es@(_ :: _ :: _) => mkBranch dig (build n (strip false es)) (build n (strip true es))

/-- Every entry has `n` remaining bits. -/
def Lengths (n : Nat) (es : List (Entry K V)) : Prop := ∀ e ∈ es, e.2.1.length = n

theorem lengths_strip {n : Nat} {es : List (Entry K V)} (b : Bool) (h : Lengths (n + 1) es) :
    Lengths n (strip b es) := by
  intro e he
  simp only [strip, List.mem_filterMap] at he
  obtain ⟨x, hx, hxe⟩ := he
  obtain ⟨k, bits, v⟩ := x
  have hl := h _ hx
  cases bits with
  | nil => simp at hxe
  | cons c cs =>
      simp only at hxe
      split at hxe
      · cases hxe; simpa using hl
      · cases hxe

/-- Splitting by the first bit and putting it back is a permutation. -/
theorem split_perm : ∀ (es : List (Entry K V)), (∀ e ∈ es, e.2.1 ≠ []) →
    ((strip false es).map (consBit false) ++ (strip true es).map (consBit true)).Perm es
  | [], _ => by simp [strip]
  | e :: rest, ne => by
      obtain ⟨k, bits, v⟩ := e
      have ih := split_perm rest (fun x hx => ne x (List.mem_cons_of_mem _ hx))
      cases bits with
      | nil => exact absurd rfl (ne _ (List.mem_cons_self ..))
      | cons c cs =>
          cases c
          · simp only [strip, List.filterMap_cons, if_true, Bool.false_eq_true, if_false,
              List.map_cons, List.cons_append] at ih ⊢
            exact List.Perm.cons _ ih
          · simp only [strip, List.filterMap_cons, if_true, Bool.true_eq_false, if_false,
              List.map_cons] at ih ⊢
            exact (List.perm_middle).trans (List.Perm.cons _ ih)

theorem build_entries : ∀ (n : Nat) (es : List (Entry K V)), Lengths n es →
    ((build dig n es).entries).Perm es
  | _, [], _ => by simp [build, entries]
  | _, [e], _ => by simp [build, mkLeaf, entries]
  | 0, a :: b :: rest, h => by
      simp only [build, entries, List.map_map]
      have : ∀ e ∈ a :: b :: rest, e.2.1 = [] := fun e he => List.eq_nil_of_length_eq_zero (h e he)
      rw [List.map_congr_left (l := a :: b :: rest) (g := id) (fun e he => by
        obtain ⟨k, bits, v⟩ := e
        have := this _ he
        simp only at this
        subst this
        rfl), List.map_id]
  | n + 1, a :: b :: rest, h => by
      simp only [build, mkBranch, entries]
      refine List.Perm.trans ?_ (split_perm _ (fun e he => by
        have := h e he
        intro hnil; rw [hnil] at this; simp at this))
      exact List.Perm.append ((build_entries n _ (lengths_strip false h)).map _)
        ((build_entries n _ (lengths_strip true h)).map _)

theorem build_inv : ∀ (n : Nat) (es : List (Entry K V)), Lengths n es → Inv dig n (build dig n es)
  | _, [], _ => by simp [build, Inv]
  | n, [e], h => by simpa [build, mkLeaf, Inv] using h e (by simp)
  | 0, a :: b :: rest, _ => by simp [build, Inv]
  | n + 1, a :: b :: rest, h => by
      simp only [build, mkBranch]
      refine ⟨build_inv n _ (lengths_strip false h), build_inv n _ (lengths_strip true h), rfl, ?_⟩
      have pl := (build_entries dig n _ (lengths_strip false h)).length_eq
      have pr := (build_entries dig n _ (lengths_strip true h)).length_eq
      have whole := (split_perm (a :: b :: rest) (fun e he => by
        have := h e he
        intro hnil; rw [hnil] at this; simp at this)).length_eq
      simp only [List.length_append, List.length_map] at whole
      rw [pl, pr, whole]
      simp

/-! ### Insert: one walk, one digest per branch on it -/

variable [DecidableEq K]

/-- Drop every entry of key `k`. -/
def dropKey {α : Type} (k : K) (es : List (K × α)) : List (K × α) := es.filter fun e => decide (e.1 ≠ k)

theorem dropKey_nil {α : Type} (k : K) : dropKey k ([] : List (K × α)) = [] := rfl

theorem dropKey_cons_eq {α : Type} (k : K) (e : K × α) (rest : List (K × α)) (h : e.1 = k) :
    dropKey k (e :: rest) = dropKey k rest := by
  simp [dropKey, h]

theorem dropKey_cons_ne {α : Type} (k : K) (e : K × α) (rest : List (K × α)) (h : e.1 ≠ k) :
    dropKey k (e :: rest) = e :: dropKey k rest := by
  simp [dropKey, h]

theorem dropKey_of_absent {α : Type} (k : K) (es : List (K × α)) (h : ∀ x ∈ es, x.1 ≠ k) :
    dropKey k es = es :=
  List.filter_eq_self.mpr fun x hx => by simpa using h x hx

theorem mem_dropKey {α : Type} {k : K} {es : List (K × α)} {x : K × α} :
    x ∈ dropKey k es ↔ x ∈ es ∧ x.1 ≠ k := by
  simp [dropKey]

theorem dropKey_append {α : Type} (k : K) (a b : List (K × α)) :
    dropKey k (a ++ b) = dropKey k a ++ dropKey k b := List.filter_append ..

theorem dropKey_sublist {α : Type} (k : K) (es : List (K × α)) : (dropKey k es).Sublist es :=
  List.filter_sublist

/-- Keys are distinct. -/
def NodupKeys {α : Type} (es : List (K × α)) : Prop := (es.map (·.1)).Nodup

theorem length_dropKey {α : Type} (k : K) :
    ∀ (es : List (K × α)), NodupKeys es → es.length ≤ (dropKey k es).length + 1
  | [], _ => by simp [dropKey_nil]
  | e :: rest, nd => by
      have nd' : NodupKeys rest := (List.nodup_cons.mp nd).2
      have ih := length_dropKey k rest nd'
      by_cases same : e.1 = k
      · have fresh : ∀ x ∈ rest, x.1 ≠ k := by
          intro x hx hxk
          exact (List.nodup_cons.mp nd).1 (List.mem_map.mpr ⟨x, hx, hxk.trans same.symm⟩)
        rw [dropKey_cons_eq k e rest same, dropKey_of_absent k rest fresh]
        simp
      · rw [dropKey_cons_ne k e rest same]
        simp only [List.length_cons]
        omega

theorem nodupKeys_snoc {α : Type} (es : List (K × α)) (nd : NodupKeys es) (k : K) (a : α) :
    NodupKeys (dropKey k es ++ [(k, a)]) := by
  unfold NodupKeys at nd ⊢
  rw [List.map_append, List.nodup_append]
  refine ⟨((dropKey_sublist k es).map _).nodup nd, by simp, ?_⟩
  intro x hx y hy
  simp only [List.mem_map] at hx
  obtain ⟨e, he, rfl⟩ := hx
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hy
  subst hy
  exact (mem_dropKey.mp he).2

/-- Remove `k`'s entry and add `(k, bits, v)`: what an insert does to the entries. -/
def upsert (es : List (Entry K V)) (k : K) (bits : List Bool) (v : V) : List (Entry K V) :=
  dropKey k es ++ [(k, bits, v)]

theorem nodupKeys_upsert (es : List (Entry K V)) (nd : NodupKeys es) (k : K) (bits : List Bool) (v : V) :
    NodupKeys (upsert es k bits v) := nodupKeys_snoc es nd k (bits, v)

theorem length_upsert (es : List (Entry K V)) (nd : NodupKeys es) (k : K) (bits : List Bool) (v : V) :
    es.length ≤ (upsert es k bits v).length := by
  have := length_dropKey k es nd
  simp only [upsert, List.length_append, List.length_singleton]
  omega

theorem dropKey_consBit (es : List (Entry K V)) (k : K) (b : Bool) :
    dropKey k (es.map (consBit b)) = (dropKey k es).map (consBit b) := by
  unfold dropKey
  rw [List.filter_map]
  rfl

theorem nodupKeys_map_consBit (es : List (Entry K V)) (b : Bool) :
    NodupKeys (es.map (consBit b)) ↔ NodupKeys es := by
  simp [NodupKeys, List.map_map, Function.comp_def, consBit]

theorem nodupKeys_branch {d : D} {l r : Trie K V D} (nd : NodupKeys (Trie.branch d l r).entries) :
    NodupKeys l.entries ∧ NodupKeys r.entries := by
  simp only [entries, NodupKeys, List.map_append] at nd
  have := List.nodup_append.mp nd
  exact ⟨(nodupKeys_map_consBit _ false).mp this.1, (nodupKeys_map_consBit _ true).mp this.2.1⟩

/-- The two children of a leaf pushed down one level. -/
def expand (c : Bool) (cs : List Bool) (d : D) (k : K) (v : V) : Trie K V D × Trie K V D :=
  if c then (.empty, .leaf d cs k v) else (.leaf d cs k v, .empty)

def insert (k : K) (v : V) : Nat → List Bool → Trie K V D → Trie K V D
  | 0, bits, .empty => mkLeaf dig bits k v
  | 0, bits, .leaf _ _ k' v' => if k' = k then mkLeaf dig bits k v else .clash [(k', v'), (k, v)]
  | 0, _, .clash kvs => .clash (dropKey k kvs ++ [(k, v)])
  | 0, _, t@(.branch ..) => t
  | _ + 1, bits, .empty => mkLeaf dig bits k v
  | n + 1, bits, .leaf d' rest k' v' =>
      if k' = k then mkLeaf dig bits k v else
      match bits, rest with
      | b :: bs, c :: cs =>
          let lr := expand c cs d' k' v'
          if b then mkBranch dig lr.1 (insert k v n bs lr.2)
          else mkBranch dig (insert k v n bs lr.1) lr.2
      | _, _ => mkLeaf dig bits k v
  | n + 1, b :: bs, .branch _ l r =>
      if b then mkBranch dig l (insert k v n bs r) else mkBranch dig (insert k v n bs l) r
  | _ + 1, [], t@(.branch ..) => t
  | _ + 1, _, t@(.clash _) => t

/-- The key's own entries carry its bits (true at the top for paths `bitsOf k`). -/
def KeyAt (es : List (Entry K V)) (k : K) (bits : List Bool) : Prop := ∀ e ∈ es, e.1 = k → e.2.1 = bits

theorem keyAt_consBit {es : List (Entry K V)} {k : K} {b : Bool} {bs : List Bool}
    (h : KeyAt (es.map (consBit b)) k (b :: bs)) : KeyAt es k bs := by
  intro e he hk
  have := h (consBit b e) (List.mem_map_of_mem he) hk
  simpa [consBit] using this

theorem keyAt_absent {es : List (Entry K V)} {k : K} {b : Bool} {bs : List Bool}
    (h : KeyAt (es.map (consBit (!b))) k (b :: bs)) : dropKey k es = es := by
  apply dropKey_of_absent
  intro e he hk
  have := h (consBit (!b) e) (List.mem_map_of_mem he) hk
  simp only [consBit, List.cons.injEq] at this
  cases b <;> simp at this

theorem upsert_left (l r : List (Entry K V)) (k : K) (bs : List Bool) (v : V)
    (absent : dropKey k r = r) :
    ((upsert l k bs v).map (consBit false) ++ r.map (consBit true)).Perm
      (upsert (l.map (consBit false) ++ r.map (consBit true)) k (false :: bs) v) := by
  unfold upsert
  rw [dropKey_append, dropKey_consBit, dropKey_consBit, absent]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  refine List.Perm.append_left _ ?_
  simpa [consBit] using (List.perm_append_comm (l₁ := [(k, false :: bs, v)]) (l₂ := r.map (consBit true)))

theorem upsert_right (l r : List (Entry K V)) (k : K) (bs : List Bool) (v : V)
    (absent : dropKey k l = l) :
    (l.map (consBit false) ++ (upsert r k bs v).map (consBit true)).Perm
      (upsert (l.map (consBit false) ++ r.map (consBit true)) k (true :: bs) v) := by
  unfold upsert
  rw [dropKey_append, dropKey_consBit, dropKey_consBit, absent]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  rfl

theorem expand_entries (c : Bool) (cs : List Bool) (d : D) (k : K) (v : V) :
    (expand c cs d k v).1.entries.map (consBit false) ++
      (expand c cs d k v).2.entries.map (consBit true) = [(k, c :: cs, v)] := by
  cases c <;> simp [expand, entries, consBit]

theorem expand_inv (c : Bool) (cs : List Bool) (d : D) (k : K) (v : V) (n : Nat) (h : cs.length = n)
    (hd : d = dig (.leaf k v)) :
    Inv dig n (expand c cs d k v).1 ∧ Inv dig n (expand c cs d k v).2 := by
  cases c <;> simp [expand, Inv, h, hd]

/-- An expanded child holds nothing or the leaf's one entry. -/
theorem expand_cases (c : Bool) (cs : List Bool) (d : D) (k : K) (v : V) :
    ((expand c cs d k v).1.entries = [] ∨ (expand c cs d k v).1.entries = [(k, cs, v)]) ∧
    ((expand c cs d k v).2.entries = [] ∨ (expand c cs d k v).2.entries = [(k, cs, v)]) := by
  cases c <;> simp [expand, entries]

theorem small_keyAt {x : Trie K V D} {k k' : K} {cs bs : List Bool} {v' : V} (ne : k' ≠ k)
    (h : x.entries = [] ∨ x.entries = [(k', cs, v')]) : KeyAt x.entries k bs ∧ dropKey k x.entries = x.entries := by
  rcases h with h | h <;> rw [h]
  · exact ⟨by simp [KeyAt], rfl⟩
  · exact ⟨by simp [KeyAt, ne], dropKey_of_absent k _ (by simpa using ne)⟩

theorem small_nodup {x : Trie K V D} {k' : K} {cs : List Bool} {v' : V}
    (h : x.entries = [] ∨ x.entries = [(k', cs, v')]) : NodupKeys x.entries := by
  rcases h with h | h <;> rw [h] <;> simp [NodupKeys]

/-- **What an insert does**: the key's old entry leaves, the new one arrives. -/
theorem insert_entries (k : K) (v : V) : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D),
    Inv dig n t → bits.length = n → KeyAt t.entries k bits →
      (insert dig k v n bits t).entries.Perm (upsert t.entries k bits v)
  | 0, bits, .empty, _, _, _ => by simp [insert, mkLeaf, entries, upsert, dropKey_nil]
  | 0, bits, .leaf d' rest k' v', inv, len, at_ => by
      simp only [Inv] at inv
      by_cases same : k' = k
      · subst same
        have := at_ (k', rest, v') (by simp [entries]) rfl
        simp only at this
        subst this
        simp [insert, mkLeaf, entries, upsert, dropKey_cons_eq, dropKey_nil]
      · have hb : bits = [] := List.eq_nil_of_length_eq_zero len
        have hr : rest = [] := List.eq_nil_of_length_eq_zero inv.1
        subst hb hr
        simp [insert, entries, upsert, same, dropKey_cons_ne, dropKey_nil]
  | 0, bits, .clash kvs, _, len, _ => by
      have hb : bits = [] := List.eq_nil_of_length_eq_zero len
      subst hb
      simp only [insert, entries, upsert, List.map_append, List.map_cons, List.map_nil]
      unfold dropKey
      rw [List.filter_map]
      rfl
  | 0, _, .branch .., inv, _, _ => by simp [Inv] at inv
  | n + 1, bits, .empty, _, _, _ => by simp [insert, mkLeaf, entries, upsert, dropKey_nil]
  | n + 1, bits, .leaf d' rest k' v', inv, len, at_ => by
      simp only [Inv] at inv
      by_cases same : k' = k
      · subst same
        have := at_ (k', rest, v') (by simp [entries]) rfl
        simp only at this
        subst this
        simp [insert, mkLeaf, entries, upsert, dropKey_cons_eq, dropKey_nil]
      · match bits, rest, len, inv with
        | b :: bs, c :: cs, len, inv =>
            have lbs : bs.length = n := by simpa using len
            have lcs : cs.length = n := by simpa using inv.1
            have hEntries := expand_entries c cs d' k' v'
            have ⟨i1, i2⟩ := expand_inv dig c cs d' k' v' n lcs inv.2
            have ⟨c1, c2⟩ := expand_cases c cs d' k' v'
            have target : upsert (Trie.leaf d' (c :: cs) k' v').entries k (b :: bs) v =
                [(k', c :: cs, v'), (k, b :: bs, v)] := by
              simp only [entries, upsert, dropKey_cons_ne k (k', c :: cs, v') [] same, dropKey_nil]
              rfl
            rw [target]
            cases b with
            | false =>
                simp only [insert, same, if_false, Bool.false_eq_true, mkBranch, entries]
                refine (List.Perm.append_right _
                  ((insert_entries k v n bs _ i1 lbs (small_keyAt same c1).1).map _)).trans ?_
                refine (upsert_left _ _ k bs v (small_keyAt (bs := bs) same c2).2).trans ?_
                rw [hEntries]
                simp [upsert, dropKey_cons_ne k (k', c :: cs, v') [] same, dropKey_nil]
            | true =>
                simp only [insert, same, if_false, if_true, mkBranch, entries]
                refine (List.Perm.append_left _
                  ((insert_entries k v n bs _ i2 lbs (small_keyAt same c2).1).map _)).trans ?_
                refine (upsert_right _ _ k bs v (small_keyAt (bs := bs) same c1).2).trans ?_
                rw [hEntries]
                simp [upsert, dropKey_cons_ne k (k', c :: cs, v') [] same, dropKey_nil]
        | [], _, len, _ => simp at len
        | _ :: _, [], _, inv => simp at inv
  | n + 1, b :: bs, .branch d l r, inv, len, at_ => by
      obtain ⟨il, ir, _, _⟩ := inv
      have lbs : bs.length = n := by simpa using len
      cases b with
      | false =>
          simp only [insert, Bool.false_eq_true, if_false, mkBranch, entries]
          have atL : KeyAt l.entries k bs := keyAt_consBit (fun e he hk =>
            at_ e (List.mem_append_left _ he) hk)
          have absent := keyAt_absent (b := false) (bs := bs) (es := r.entries) (k := k)
            (fun e he hk => at_ e (List.mem_append_right _ he) hk)
          exact (List.Perm.append_right _ ((insert_entries k v n bs l il lbs atL).map _)).trans
            (upsert_left _ _ k bs v absent)
      | true =>
          simp only [insert, if_true, mkBranch, entries]
          have atR : KeyAt r.entries k bs := keyAt_consBit (fun e he hk =>
            at_ e (List.mem_append_right _ he) hk)
          have absent := keyAt_absent (b := true) (bs := bs) (es := l.entries) (k := k)
            (fun e he hk => at_ e (List.mem_append_left _ he) hk)
          exact (List.Perm.append_left _ ((insert_entries k v n bs r ir lbs atR).map _)).trans
            (upsert_right _ _ k bs v absent)
  | n + 1, [], .branch .., _, len, _ => by simp at len
  | n + 1, _, .clash _, inv, _, _ => by simp [Inv] at inv

theorem length_insert (k : K) (v : V) (n : Nat) (bits : List Bool) (t : Trie K V D)
    (inv : Inv dig n t) (len : bits.length = n) (at_ : KeyAt t.entries k bits) (nd : NodupKeys t.entries) :
    t.entries.length ≤ (insert dig k v n bits t).entries.length := by
  rw [(insert_entries dig k v n bits t inv len at_).length_eq]
  exact length_upsert _ nd k bits v

theorem nodup_insert (k : K) (v : V) (n : Nat) (bits : List Bool) (t : Trie K V D)
    (inv : Inv dig n t) (len : bits.length = n) (at_ : KeyAt t.entries k bits) (nd : NodupKeys t.entries) :
    NodupKeys (insert dig k v n bits t).entries := by
  have p := (insert_entries dig k v n bits t inv len at_).map (·.1)
  exact p.nodup_iff.mpr (nodupKeys_upsert _ nd k bits v)

/-- **An insert keeps the cache well formed.** -/
theorem insert_inv (k : K) (v : V) : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D),
    Inv dig n t → bits.length = n → KeyAt t.entries k bits → NodupKeys t.entries →
      Inv dig n (insert dig k v n bits t)
  | 0, bits, .empty, _, len, _, _ => by simpa [insert, mkLeaf, Inv] using len
  | 0, bits, .leaf d' rest k' v', inv, len, _, _ => by
      by_cases same : k' = k
      · simpa [insert, mkLeaf, Inv, same] using len
      · simp [insert, Inv, same]
  | 0, _, .clash kvs, inv, _, _, nd => by
      simp only [Inv] at inv
      have nd' : NodupKeys kvs := by
        simpa [NodupKeys, entries, List.map_map, Function.comp_def] using nd
      have := length_dropKey k kvs nd'
      simp only [insert, Inv, List.length_append, List.length_singleton]
      omega
  | 0, _, .branch .., inv, _, _, _ => by simp [Inv] at inv
  | n + 1, bits, .empty, _, len, _, _ => by simpa [insert, mkLeaf, Inv] using len
  | n + 1, bits, .leaf d' rest k' v', inv, len, at_, nd => by
      have whole := insert_entries dig k v (n + 1) bits (.leaf d' rest k' v') inv len at_
      simp only [Inv] at inv
      by_cases same : k' = k
      · simpa [insert, mkLeaf, Inv, same] using len
      · match bits, rest, len, inv, whole with
        | b :: bs, c :: cs, len, inv, whole =>
            have lbs : bs.length = n := by simpa using len
            have lcs : cs.length = n := by simpa using inv.1
            have ⟨i1, i2⟩ := expand_inv dig c cs d' k' v' n lcs inv.2
            have ⟨c1, c2⟩ := expand_cases c cs d' k' v'
            have count : (insert dig k v (n + 1) (b :: bs) (.leaf d' (c :: cs) k' v')).entries.length = 2 := by
              rw [whole.length_eq]
              simp only [entries, upsert, dropKey_cons_ne k (k', c :: cs, v') [] same, dropKey_nil]
              rfl
            cases b with
            | false =>
                simp only [insert, same, if_false, Bool.false_eq_true] at count ⊢
                refine ⟨insert_inv k v n bs _ i1 lbs (small_keyAt same c1).1 (small_nodup c1), i2, rfl, ?_⟩
                simp only [mkBranch, entries, List.length_append, List.length_map] at count
                omega
            | true =>
                simp only [insert, same, if_false, if_true] at count ⊢
                refine ⟨i1, insert_inv k v n bs _ i2 lbs (small_keyAt same c2).1 (small_nodup c2), rfl, ?_⟩
                simp only [mkBranch, entries, List.length_append, List.length_map] at count
                omega
        | [], _, len, _, _ => simp at len
        | _ :: _, [], _, inv, _ => simp at inv
  | n + 1, b :: bs, .branch d l r, inv, len, at_, nd => by
      have whole := length_insert dig k v (n + 1) (b :: bs) (.branch d l r) inv len at_ nd
      obtain ⟨il, ir, _, two⟩ := inv
      have lbs : bs.length = n := by simpa using len
      have ⟨ndl, ndr⟩ := nodupKeys_branch nd
      simp only [entries, List.length_append, List.length_map] at whole
      cases b with
      | false =>
          have atL : KeyAt l.entries k bs := keyAt_consBit (fun e he hk =>
            at_ e (List.mem_append_left _ he) hk)
          simp only [insert, Bool.false_eq_true, if_false] at whole ⊢
          refine ⟨insert_inv k v n bs l il lbs atL ndl, ir, rfl, ?_⟩
          simp only [mkBranch, entries, List.length_append, List.length_map] at whole
          omega
      | true =>
          have atR : KeyAt r.entries k bs := keyAt_consBit (fun e he hk =>
            at_ e (List.mem_append_right _ he) hk)
          simp only [insert, if_true] at whole ⊢
          refine ⟨il, insert_inv k v n bs r ir lbs atR ndr, rfl, ?_⟩
          simp only [mkBranch, entries, List.length_append, List.length_map] at whole
          omega
  | n + 1, [], .branch .., _, len, _, _ => by simp at len
  | n + 1, _, .clash _, inv, _, _, _ => by simp [Inv] at inv

end Trie

/-! ## The root of a key/value list, and the cache that holds it -/

section Root

variable {K V D : Type} [DecidableEq K] (dig : NodeIn K V D → D)

open Trie

/-- The value a list last gives key `k`. -/
def lastVal (es : List (K × V)) (k : K) : Option V :=
  ((es.filter fun e => decide (e.1 = k)).getLast?).map (·.2)

theorem lastVal_append (es fs : List (K × V)) (k : K) :
    lastVal (es ++ fs) k = (lastVal fs k).or (lastVal es k) := by
  unfold lastVal
  rw [List.filter_append, List.getLast?_append]
  cases (fs.filter fun e => decide (e.1 = k)).getLast? <;>
    cases (es.filter fun e => decide (e.1 = k)).getLast? <;> rfl

theorem lastVal_snoc (es : List (K × V)) (e : K × V) (k : K) :
    lastVal (es ++ [e]) k = if e.1 = k then some e.2 else lastVal es k := by
  rw [lastVal_append]
  by_cases h : e.1 = k <;> simp [lastVal, h]

theorem lastVal_isSome {es : List (K × V)} {k : K} :
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

theorem lastVal_cons (e : K × V) (es : List (K × V)) (k : K) :
    lastVal (e :: es) k = (lastVal es k).or (if e.1 = k then some e.2 else none) := by
  have := lastVal_append [e] es k
  rw [List.singleton_append] at this
  rw [this]
  by_cases h : e.1 = k <;> simp [lastVal, h]

/-- Mapping the values maps every key's last value. -/
theorem lastVal_map {C : Type} (f : V → C) (es : List (K × V)) (k : K) :
    lastVal (es.map fun e => (e.1, f e.2)) k = (lastVal es k).map f := by
  unfold lastVal
  rw [List.filter_map, List.getLast?_map, Option.map_map, Option.map_map]
  rfl

/-- One entry per key, its last value. -/
def canon (es : List (K × V)) : List (K × V) := es.foldl (fun L e => dropKey e.1 L ++ [e]) []

section Fast

variable [Hashable K] [LawfulHashable K]

/-- Read the input from the end, keeping only a key's first (hence the original
list's last) occurrence. The hash map makes each duplicate test constant-time;
prepending restores the specification's last-occurrence order. -/
def canonFastGo (seen : Std.HashMap K Unit) (out : List (K × V)) : List (K × V) → List (K × V)
  | [] => out
  | e :: rest =>
      if seen.contains e.1 then canonFastGo seen out rest
      else canonFastGo (seen.insert e.1 ()) (e :: out) rest

theorem mem_canonFastGo (seen : Std.HashMap K Unit) (out rest : List (K × V)) (x : K × V) :
    x ∈ canonFastGo seen out rest ↔
      x ∈ out ∨ (x.1 ∉ seen ∧ lastVal rest.reverse x.1 = some x.2) := by
  induction rest generalizing seen out with
  | nil => simp [canonFastGo, lastVal]
  | cons e rest ih =>
      obtain ⟨k, v⟩ := e
      obtain ⟨xk, xv⟩ := x
      by_cases seenKey : seen.contains k
      · have mem : k ∈ seen := Std.HashMap.contains_iff_mem.mp seenKey
        simp only [canonFastGo, seenKey, if_true, ih, List.reverse_cons,
          lastVal_snoc, List.mem_cons]
        by_cases same : k = xk
        · subst k
          simp [mem]
        · simp [same]
      · have mem : k ∉ seen := fun h => seenKey (Std.HashMap.contains_iff_mem.mpr h)
        rw [canonFastGo, if_neg seenKey, ih, List.reverse_cons, lastVal_snoc]
        simp only [List.mem_cons, Std.HashMap.mem_insert]
        by_cases same : k = xk
        · subst k
          simp [mem, or_comm, eq_comm]
        · have different : xk ≠ k := Ne.symm same
          simp [same, different, mem, or_assoc]

theorem nodupKeys_canonFastGo (seen : Std.HashMap K Unit) (out rest : List (K × V))
    (nd : NodupKeys out) (bound : ∀ x ∈ out, x.1 ∈ seen) :
    NodupKeys (canonFastGo seen out rest) := by
  induction rest generalizing seen out with
  | nil => simpa [canonFastGo] using nd
  | cons e rest ih =>
      by_cases seenKey : seen.contains e.1
      · simpa [canonFastGo, seenKey] using ih seen out nd bound
      · rw [canonFastGo, if_neg seenKey]
        apply ih
        · simp only [NodupKeys, List.map_cons, List.nodup_cons]
          refine ⟨?_, nd⟩
          intro fresh
          obtain ⟨x, hx, keyEq⟩ := List.mem_map.mp fresh
          have inSeen := bound x hx
          have same : e.1 ∈ seen := keyEq ▸ inSeen
          exact seenKey (Std.HashMap.contains_iff_mem.mpr same)
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact Std.HashMap.mem_insert_self
          · exact Std.HashMap.mem_insert.mpr (Or.inr (bound x hx))

/-- The linear canonicalizer used by compiled root construction. -/
def canonFast (es : List (K × V)) : List (K × V) := canonFastGo ∅ [] es.reverse

theorem mem_canonFast (es : List (K × V)) (x : K × V) :
    x ∈ canonFast es ↔ lastVal es x.1 = some x.2 := by
  simp [canonFast, mem_canonFastGo]

theorem nodupKeys_canonFast (es : List (K × V)) : NodupKeys (canonFast es) :=
  nodupKeys_canonFastGo ∅ [] es.reverse (by simp [NodupKeys]) (by simp)

end Fast

theorem canon_snoc (es : List (K × V)) (e : K × V) : canon (es ++ [e]) = dropKey e.1 (canon es) ++ [e] := by
  simp [canon, List.foldl_append]

theorem nodupKeys_canon (es : List (K × V)) : NodupKeys (canon es) := by
  induction es using List.reverseRecOn with
  | nil => simp [canon, NodupKeys]
  | append_singleton es e ih =>
      rw [canon_snoc]
      exact nodupKeys_snoc _ ih e.1 e.2

theorem mem_canon (es : List (K × V)) (x : K × V) : x ∈ canon es ↔ lastVal es x.1 = some x.2 := by
  induction es using List.reverseRecOn with
  | nil => simp [canon, lastVal]
  | append_singleton es e ih =>
      rw [canon_snoc, lastVal_snoc, List.mem_append, mem_dropKey, ih, List.mem_singleton]
      by_cases h : e.1 = x.1
      · simp only [h, if_true, ne_eq, not_true_eq_false, and_false, false_or, Option.some.injEq]
        constructor
        · rintro rfl; rfl
        · intro hv; obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := e; simp_all
      · have : x ≠ e := fun hx => h (by rw [hx])
        simp [h, Ne.symm h, this]

theorem nodup_of_nodupKeys {α : Type} {es : List (K × α)} (nd : NodupKeys es) : es.Nodup :=
  List.Nodup.of_map _ nd

/-- The fast pass has exactly the specification's entries, up to order. -/
theorem canonFast_perm [Hashable K] [LawfulHashable K] (es : List (K × V)) :
    (canonFast es).Perm (canon es) :=
  (List.perm_ext_iff_of_nodup (nodup_of_nodupKeys (nodupKeys_canonFast es))
    (nodup_of_nodupKeys (nodupKeys_canon es))).mpr fun x => by rw [mem_canonFast, mem_canon]

/-- A key-distinct list is its own canonical form, up to order. -/
theorem canon_perm_self : ∀ (es : List (K × V)), NodupKeys es → (canon es).Perm es := by
  intro es
  induction es using List.reverseRecOn with
  | nil => intro _; simp [canon]
  | append_singleton es e ih =>
      intro nd
      rw [canon_snoc]
      have split := List.nodup_append.mp (by simpa [NodupKeys, List.map_append] using nd)
      have nd' : NodupKeys es := split.1
      have notin : ∀ x ∈ es, x.1 ≠ e.1 := fun x hx same =>
        split.2.2 x.1 (List.mem_map_of_mem hx) e.1 (List.mem_singleton_self _) same
      have drop : dropKey e.1 es = es := List.filter_eq_self.mpr fun x hx => by
        simpa using notin x hx
      have perm : (dropKey e.1 (canon es)).Perm (dropKey e.1 es) := (ih nd').filter _
      rw [drop] at perm
      exact perm.append_right [e]

/-- **Order does not matter**: lists giving every key the same last value have
one canonical form, up to order. -/
theorem canon_perm {es es' : List (K × V)} (same : ∀ k, lastVal es k = lastVal es' k) :
    (canon es).Perm (canon es') :=
  (List.perm_ext_iff_of_nodup (nodup_of_nodupKeys (nodupKeys_canon es))
    (nodup_of_nodupKeys (nodupKeys_canon es'))).mpr fun x => by rw [mem_canon, mem_canon, same]

theorem dropKey_entries (bitsOf : K → List Bool) (k : K) (kvs : List (K × V)) :
    dropKey k (entries bitsOf kvs) = entries bitsOf (dropKey k kvs) := by
  unfold dropKey entries
  rw [List.filter_map]
  rfl

theorem entries_canon_snoc (bitsOf : K → List Bool) (es : List (K × V)) (k : K) (v : V) :
    entries bitsOf (canon (es ++ [(k, v)])) = upsert (entries bitsOf (canon es)) k (bitsOf k) v := by
  rw [canon_snoc, upsert, dropKey_entries]
  simp [entries]

theorem upsert_perm {es es' : List (Entry K V)} (p : es.Perm es') (k : K) (bits : List Bool) (v : V) :
    (upsert es k bits v).Perm (upsert es' k bits v) :=
  List.Perm.append_right _ (p.filter _)

/-- **The world root of a key/value list**: the canonical compressed root of
its last value per key, every key at its full path `bitsOf k` of length `L`. -/
def root (bitsOf : K → List Bool) (L : Nat) (es : List (K × V)) : D :=
  tree dig L (entries bitsOf (canon es))

/-- Root construction over the one-pass canonicalizer. -/
def rootFast [Hashable K] [LawfulHashable K] (bitsOf : K → List Bool) (L : Nat) (es : List (K × V)) : D :=
  tree dig L (entries bitsOf (canonFast es))

/-- The hash-map canonicalizer gives the logical root. -/
theorem root_eq_rootFast [Hashable K] [LawfulHashable K]
    (bitsOf : K → List Bool) (L : Nat) (es : List (K × V)) :
    root dig bitsOf L es = rootFast dig bitsOf L es :=
  tree_perm dig L ((canonFast_perm es).map _).symm

theorem root_congr (bitsOf : K → List Bool) (L : Nat) {es es' : List (K × V)}
    (same : ∀ k, lastVal es k = lastVal es' k) : root dig bitsOf L es = root dig bitsOf L es' :=
  tree_perm dig L ((canon_perm same).map _)

/-- A kept trie for paths `bitsOf` of length `L`, well formed. -/
structure Cache (bitsOf : K → List Bool) (L : Nat) where
  trie : Trie K V D
  inv : Inv dig L trie
  paths : ∀ e ∈ trie.entries, e.2.1 = bitsOf e.1
  nodup : NodupKeys trie.entries

variable {dig}

namespace Cache

variable {bitsOf : K → List Bool} {L : Nat}

def digest (cache : Cache dig bitsOf L) : D := cache.trie.digest dig

/-- The cache holds the list `es`: its entries are `es`'s last values, in some order. -/
def Holds (cache : Cache dig bitsOf L) (es : List (K × V)) : Prop :=
  cache.trie.entries.Perm (entries bitsOf (canon es))

theorem Holds.congr {cache : Cache dig bitsOf L} {es es' : List (K × V)} (h : cache.Holds es)
    (same : ∀ k, lastVal es k = lastVal es' k) : cache.Holds es' :=
  h.trans ((canon_perm same).map _)

/-- **The kept digest is the root of the list it holds.** -/
theorem digest_eq {cache : Cache dig bitsOf L} {es : List (K × V)} (h : cache.Holds es) :
    cache.digest = root dig bitsOf L es := by
  rw [digest, Trie.digest_eq dig L cache.trie cache.inv, root, tree_perm dig L h]

variable (lengths : ∀ k, (bitsOf k).length = L)
include lengths

theorem lengths_entries (es : List (K × V)) : Lengths L (entries bitsOf es) := by
  intro e he
  obtain ⟨kv, _, rfl⟩ := List.mem_map.mp he
  exact lengths kv.1

/-- Bulk build: one digest per branch and per leaf. -/
def build (es : List (K × V)) : Cache dig bitsOf L where
  trie := Trie.build dig L (entries bitsOf (canon es))
  inv := build_inv dig L _ (lengths_entries lengths _)
  paths := by
    intro e he
    have := ((build_entries dig L _ (lengths_entries lengths _)).subset he)
    obtain ⟨kv, _, rfl⟩ := List.mem_map.mp this
    rfl
  nodup := by
    have p := (build_entries dig L _ (lengths_entries lengths (canon es))).map (·.1)
    refine p.nodup_iff.mpr ?_
    have := nodupKeys_canon es
    simpa [NodupKeys, entries, List.map_map, Function.comp_def] using this

theorem build_holds (es : List (K × V)) : (build (dig := dig) lengths es).Holds es :=
  build_entries dig L _ (lengths_entries lengths _)

/-- Bulk build over the one-pass canonicalizer. Its digest is the same root;
the kept entry order may differ, which `Holds` already abstracts over. -/
def buildFast [Hashable K] [LawfulHashable K] (es : List (K × V)) : Cache dig bitsOf L where
  trie := Trie.build dig L (entries bitsOf (canonFast es))
  inv := build_inv dig L _ (lengths_entries lengths _)
  paths := by
    intro e he
    have := ((build_entries dig L _ (lengths_entries lengths _)).subset he)
    obtain ⟨kv, _, rfl⟩ := List.mem_map.mp this
    rfl
  nodup := by
    have p := (build_entries dig L _ (lengths_entries lengths (canonFast es))).map (·.1)
    refine p.nodup_iff.mpr ?_
    have := nodupKeys_canonFast es
    simpa [NodupKeys, entries, List.map_map, Function.comp_def] using this

/-- Bulk build of a key-distinct list: no canonicalization, one digest per branch and leaf. -/
def buildNodup (es : List (K × V)) (nd : NodupKeys es) : Cache dig bitsOf L where
  trie := Trie.build dig L (entries bitsOf es)
  inv := build_inv dig L _ (lengths_entries lengths _)
  paths := by
    intro e he
    have := ((build_entries dig L _ (lengths_entries lengths _)).subset he)
    obtain ⟨kv, _, rfl⟩ := List.mem_map.mp this
    rfl
  nodup := by
    have p := (build_entries dig L _ (lengths_entries lengths es)).map (·.1)
    refine p.nodup_iff.mpr ?_
    simpa [NodupKeys, entries, List.map_map, Function.comp_def] using nd

theorem buildNodup_holds (es : List (K × V)) (nd : NodupKeys es) :
    (buildNodup (dig := dig) lengths es nd).Holds es :=
  (build_entries dig L _ (lengths_entries lengths es)).trans ((canon_perm_self es nd).symm.map _)

theorem buildFast_holds [Hashable K] [LawfulHashable K] (es : List (K × V)) :
    (buildFast (dig := dig) lengths es).Holds es :=
  (build_entries dig L _ (lengths_entries lengths (canonFast es))).trans ((canonFast_perm es).map _)

/-- Write `(k, v)`: one walk, one digest per branch on it. -/
def insert (cache : Cache dig bitsOf L) (k : K) (v : V) : Cache dig bitsOf L where
  trie := Trie.insert dig k v L (bitsOf k) cache.trie
  inv := insert_inv dig k v L (bitsOf k) cache.trie cache.inv (lengths k)
    (fun e he hk => by rw [cache.paths e he, hk]) cache.nodup
  paths := by
    intro e he
    have := (insert_entries dig k v L (bitsOf k) cache.trie cache.inv (lengths k)
      (fun e he hk => by rw [cache.paths e he, hk])).subset he
    rcases List.mem_append.mp this with h | h
    · exact cache.paths e (mem_dropKey.mp h).1
    · simp only [List.mem_singleton] at h; subst h; rfl
  nodup := nodup_insert dig k v L (bitsOf k) cache.trie cache.inv (lengths k)
    (fun e he hk => by rw [cache.paths e he, hk]) cache.nodup

theorem insert_holds {cache : Cache dig bitsOf L} {es : List (K × V)} (h : cache.Holds es) (k : K) (v : V) :
    (cache.insert lengths k v).Holds (es ++ [(k, v)]) := by
  unfold Holds
  rw [entries_canon_snoc]
  exact (insert_entries dig k v L (bitsOf k) cache.trie cache.inv (lengths k)
    (fun e he hk => by rw [cache.paths e he, hk])).trans (upsert_perm h k (bitsOf k) v)

/-- Write a list of slots in order. -/
def insertAll (cache : Cache dig bitsOf L) (slots : List (K × V)) : Cache dig bitsOf L :=
  slots.foldl (fun c s => c.insert lengths s.1 s.2) cache

theorem insertAll_holds : ∀ {cache : Cache dig bitsOf L} {es : List (K × V)} (slots : List (K × V)),
    cache.Holds es → (cache.insertAll lengths slots).Holds (es ++ slots)
  | _, _, [], h => by simpa [insertAll] using h
  | cache, es, s :: rest, h => by
      have := insertAll_holds (cache := cache.insert lengths s.1 s.2) (es := es ++ [s]) rest
        (insert_holds lengths h s.1 s.2)
      simpa [insertAll, List.foldl_cons] using this

end Cache

end Root

/-! ## Openings read off the kept trie, and their completeness -/

namespace Trie

variable {K V D : Type} (dig : NodeIn K V D → D)

/-- The honest opening of a path: one sibling per branch walked, then the terminal. -/
def opening : List Bool → Trie K V D → Opening K V D
  | b :: bs, .branch _ l r =>
      if b then ⟨l.digest dig :: (opening bs r).siblings, (opening bs r).terminal⟩
      else ⟨r.digest dig :: (opening bs l).siblings, (opening bs l).terminal⟩
  | _, .leaf _ _ k v => ⟨[], .leaf k v⟩
  | _, _ => ⟨[], .empty⟩

theorem climb_nil (bits : List Bool) (below : D) : climb dig bits [] below = below := by
  cases bits <;> rfl

/-- The honest walk climbs back to the kept digest. -/
theorem opening_climb : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D), Inv dig n t → bits.length = n →
    (opening dig bits t).siblings.length ≤ n ∧
      climb dig (bits.take (opening dig bits t).siblings.length) (opening dig bits t).siblings
        (dig (opening dig bits t).terminal.input) = t.digest dig
  | n, bits, .empty, _, _ => by
      cases bits <;> simp [opening, climb_nil, digest, Terminal.input]
  | n, bits, .leaf d _ k v, inv, _ => by
      simp only [Inv] at inv
      cases bits <;> simp [opening, climb_nil, digest, Terminal.input, inv.2]
  | n, bits, .clash _, _, _ => by
      cases bits <;> simp [opening, climb_nil, digest, Terminal.input]
  | 0, _, .branch .., inv, _ => by simp [Inv] at inv
  | n + 1, [], .branch .., _, len => by simp at len
  | n + 1, b :: bs, .branch d l r, inv, len => by
      obtain ⟨il, ir, hd, _⟩ := inv
      have lbs : bs.length = n := by simpa using len
      cases b with
      | false =>
          have ⟨short, up⟩ := opening_climb n bs l il lbs
          simp only [opening, Bool.false_eq_true, if_false, List.length_cons, List.take_succ_cons, climb]
          exact ⟨by omega, by rw [up, hd]; rfl⟩
      | true =>
          have ⟨short, up⟩ := opening_climb n bs r ir lbs
          simp only [opening, if_true, List.length_cons, List.take_succ_cons, climb]
          exact ⟨by omega, by rw [up, hd]; rfl⟩

/-- A leaf terminal is an entry under the walked prefix. -/
theorem opening_leaf : ∀ (bits : List Bool) (t : Trie K V D) (k : K) (v : V),
    (opening dig bits t).terminal = .leaf k v →
      ∃ rest, (k, bits.take (opening dig bits t).siblings.length ++ rest, v) ∈ t.entries
  | bits, .empty, k, v, h => by cases bits <;> simp [opening] at h
  | bits, .clash _, k, v, h => by cases bits <;> simp [opening] at h
  | bits, .leaf _ rest k' v', k, v, h => by
      have : k' = k ∧ v' = v := by cases bits <;> simpa [opening] using h
      obtain ⟨rfl, rfl⟩ := this
      exact ⟨rest, by cases bits <;> simp [opening, entries]⟩
  | [], .branch .., k, v, h => by simp [opening] at h
  | b :: bs, .branch d l r, k, v, h => by
      cases b with
      | false =>
          simp only [opening, Bool.false_eq_true, if_false] at h ⊢
          obtain ⟨rest, mem⟩ := opening_leaf bs l k v h
          refine ⟨rest, ?_⟩
          simp only [List.length_cons, List.take_succ_cons, entries, List.mem_append]
          exact Or.inl (List.mem_map.mpr ⟨_, mem, rfl⟩)
      | true =>
          simp only [opening, if_true] at h ⊢
          obtain ⟨rest, mem⟩ := opening_leaf bs r k v h
          refine ⟨rest, ?_⟩
          simp only [List.length_cons, List.take_succ_cons, entries, List.mem_append]
          exact Or.inr (List.mem_map.mpr ⟨_, mem, rfl⟩)

/-- Under distinct paths, a present path's walk ends at its own leaf. -/
theorem opening_present : ∀ (n : Nat) (bits : List Bool) (t : Trie K V D), Inv dig n t →
    (t.entries.map (·.2.1)).Nodup → ∀ e ∈ t.entries, e.2.1 = bits →
      (opening dig bits t).terminal = .leaf e.1 e.2.2
  | _, bits, .empty, _, _, e, he, _ => by simp [entries] at he
  | _, bits, .leaf _ rest k v, _, _, e, he, _ => by
      simp only [entries, List.mem_singleton] at he
      subst he
      cases bits <;> rfl
  | 0, bits, .clash kvs, inv, nd, e, he, _ => by
      simp only [Inv] at inv
      exfalso
      match kvs, inv with
      | a :: b :: rest, _ =>
          simp [entries] at nd
  | _ + 1, _, .clash _, inv, _, _, _, _ => by simp [Inv] at inv
  | 0, _, .branch .., inv, _, _, _, _ => by simp [Inv] at inv
  | n + 1, bits, .branch d l r, inv, nd, e, he, hb => by
      obtain ⟨il, ir, _, _⟩ := inv
      simp only [entries, List.map_append, List.map_map] at nd
      have ⟨ndl, ndr, _⟩ := List.nodup_append.mp nd
      simp only [entries, List.mem_append, List.mem_map] at he
      rcases he with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
      · simp only [consBit] at hb
        subst hb
        simp only [opening, Bool.false_eq_true, if_false]
        exact opening_present n x.2.1 l il
          (List.Nodup.of_map (List.cons false) (by
            simpa [List.map_map, Function.comp_def, consBit] using ndl)) x hx rfl
      · simp only [consBit] at hb
        subst hb
        simp only [opening, if_true]
        exact opening_present n x.2.1 r ir
          (List.Nodup.of_map (List.cons true) (by
            simpa [List.map_map, Function.comp_def, consBit] using ndr)) x hx rfl

end Trie

namespace Cache

variable {K V D : Type} [DecidableEq K] [DecidableEq V] [DecidableEq D] {dig : NodeIn K V D → D}
  {bitsOf : K → List Bool} {L : Nat}

/-- The honest opening of key `k`, read off the kept trie (no hashing). -/
def opening (cache : Cache dig bitsOf L) (k : K) : Opening K V D := cache.trie.opening dig (bitsOf k)

/-- An opening has at most one sibling per path bit. -/
theorem opening_length (lengths : ∀ k, (bitsOf k).length = L) (cache : Cache dig bitsOf L) (k : K) :
    (cache.opening k).siblings.length ≤ L :=
  (Trie.opening_climb dig L (bitsOf k) cache.trie cache.inv (lengths k)).1

/-- No two keys the list gives a value share a path. -/
def PathsInjective (bitsOf : K → List Bool) (es : List (K × V)) : Prop :=
  ∀ k k', (lastVal es k).isSome → (lastVal es k').isSome → bitsOf k = bitsOf k' → k = k'

theorem mem_holds {cache : Cache dig bitsOf L} {es : List (K × V)} (h : cache.Holds es) {e : Entry K V}
    (he : e ∈ cache.trie.entries) : lastVal es e.1 = some e.2.2 ∧ e.2.1 = bitsOf e.1 := by
  have := h.subset he
  obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp this
  exact ⟨(mem_canon es kv).mp hkv, rfl⟩

/-- Under distinct paths the kept entries have distinct paths. -/
theorem paths_nodup {cache : Cache dig bitsOf L} {es : List (K × V)} (h : cache.Holds es)
    (inj : PathsInjective bitsOf es) : (cache.trie.entries.map (·.2.1)).Nodup := by
  refine List.Nodup.map_on ?_ (List.Nodup.of_map _ cache.nodup)
  intro x hx y hy same
  have ⟨vx, px⟩ := mem_holds h hx
  have ⟨vy, py⟩ := mem_holds h hy
  have keys : x.1 = y.1 := inj _ _ (by simp [vx]) (by simp [vy]) (by rw [← px, ← py]; exact same)
  exact List.inj_on_of_nodup_map cache.nodup hx hy keys

/-- A present key's opening ends at its own leaf. -/
theorem opening_terminal {cache : Cache dig bitsOf L} {es : List (K × V)} (h : cache.Holds es)
    (inj : PathsInjective bitsOf es) {k : K} {v : V} (hv : lastVal es k = some v) :
    (cache.opening k).terminal = .leaf k v := by
  have mem : (k, bitsOf k, v) ∈ cache.trie.entries :=
    h.symm.subset (List.mem_map.mpr ⟨(k, v), (mem_canon es (k, v)).mpr hv, rfl⟩)
  exact Trie.opening_present dig L (bitsOf k) cache.trie cache.inv (paths_nodup h inj) _ mem rfl

/-- **Completeness**: the honest opening verifies, answering the list's last value. -/
theorem opening_complete (lengths : ∀ k, (bitsOf k).length = L) {cache : Cache dig bitsOf L}
    {es : List (K × V)} (h : cache.Holds es) (inj : PathsInjective bitsOf es) (k : K) :
    verify dig bitsOf cache.digest k (lastVal es k) (cache.opening k) = true := by
  have ndPaths := paths_nodup h inj
  have ⟨short, up⟩ := Trie.opening_climb dig L (bitsOf k) cache.trie cache.inv (lengths k)
  unfold verify opening digest
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by rw [lengths]; exact short, ?_⟩, up⟩
  cases hans : lastVal es k with
  | some v =>
      have mem : (k, bitsOf k, v) ∈ cache.trie.entries :=
        h.symm.subset (List.mem_map.mpr ⟨(k, v), (mem_canon es (k, v)).mpr hans, rfl⟩)
      rw [Trie.opening_present dig L (bitsOf k) cache.trie cache.inv ndPaths _ mem rfl]
      simp
  | none =>
      cases hterm : (cache.trie.opening dig (bitsOf k)).terminal with
      | empty => rfl
      | leaf other value =>
          obtain ⟨rest, mem⟩ := Trie.opening_leaf dig (bitsOf k) cache.trie other value hterm
          have ⟨vo, po⟩ := mem_holds h mem
          simp only at vo po
          have ne : other ≠ k := by
            intro same; rw [same, hans] at vo; cases vo
          have takeLen : ((bitsOf k).take (cache.trie.opening dig (bitsOf k)).siblings.length).length =
              (cache.trie.opening dig (bitsOf k)).siblings.length := by
            rw [List.length_take, lengths]; exact Nat.min_eq_left short
          simp only [decide_eq_true_eq]
          exact ⟨ne, by rw [← po, List.take_left' takeLen]⟩

/-- The canonical entries answer `lookup` with the list's last value. -/
theorem lookup_canon (es : List (K × V)) (k : K) :
    lookup (entries bitsOf (canon es)) k = lastVal es k := by
  unfold lookup
  cases hfind : (entries bitsOf (canon es)).find? (fun e => e.1 = k) with
  | none =>
      rw [List.find?_eq_none] at hfind
      cases hl : lastVal es k with
      | none => rfl
      | some v =>
          exfalso
          have mem : (k, bitsOf k, v) ∈ entries bitsOf (canon es) :=
            List.mem_map.mpr ⟨(k, v), (mem_canon es (k, v)).mpr hl, rfl⟩
          exact hfind _ mem (by simp)
  | some f =>
      have hk : f.1 = k := by simpa using List.find?_some hfind
      obtain ⟨kv, hkv, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfind)
      simp only at hk
      subst hk
      simp [(mem_canon es kv).mp hkv]

/-- Under distinct paths the canonical entries are well formed. -/
theorem wf_canon (lengths : ∀ k, (bitsOf k).length = L) {es : List (K × V)}
    (inj : PathsInjective bitsOf es) : WF L (entries bitsOf (canon es)) := by
  refine ⟨fun e he => ?_, ?_⟩
  · obtain ⟨kv, _, rfl⟩ := List.mem_map.mp he
    exact lengths kv.1
  · simp only [entries, List.map_map, Function.comp_def]
    refine List.Nodup.map_on ?_ (nodup_of_nodupKeys (nodupKeys_canon es))
    intro x hx y hy same
    have vx := (mem_canon es x).mp hx
    have vy := (mem_canon es y).mp hy
    have keys : x.1 = y.1 := inj _ _ (by simp [vx]) (by simp [vy]) same
    exact List.inj_on_of_nodup_map (nodupKeys_canon es) hx hy keys

/-- **Binding of the root of a list.**  Two lists with distinct paths and one
root give every key the same last value — or two different node inputs share
a digest, each hashed by the canonical tree over `es` or by the climb of the
honest opening of `k` built from `es'` (finitely many, fixed by the two lists). -/
theorem root_lastVal_eq (lengths : ∀ k, (bitsOf k).length = L) {es es' : List (K × V)}
    (inj : PathsInjective bitsOf es) (inj' : PathsInjective bitsOf es')
    (hr : root dig bitsOf L es = root dig bitsOf L es') (k : K) :
    lastVal es' k = lastVal es k ∨
      CollisionAmong dig (fun x => TreeNode dig L (entries bitsOf (canon es)) x ∨
        ClimbNode dig ((build (dig := dig) lengths es').opening k).terminal
          ((bitsOf k).take ((build (dig := dig) lengths es').opening k).siblings.length)
          ((build (dig := dig) lengths es').opening k).siblings x) := by
  have built := build_holds (dig := dig) lengths es'
  have opened := opening_complete lengths built inj' k
  rw [digest_eq built, ← hr, root] at opened
  have := verify_sound dig bitsOf L lengths (canon es) (wf_canon lengths inj) k _ _ opened
  rwa [lookup_canon] at this

end Cache

end Minidregg.Theory.AuthTrie

#assert_axioms Minidregg.Theory.AuthTrie.tree_perm
#assert_axioms Minidregg.Theory.AuthTrie.Trie.digest_eq
#assert_axioms Minidregg.Theory.AuthTrie.Trie.insert_entries
#assert_axioms Minidregg.Theory.AuthTrie.Trie.insert_inv
#assert_axioms Minidregg.Theory.AuthTrie.root_congr
#assert_axioms Minidregg.Theory.AuthTrie.canonFast_perm
#assert_axioms Minidregg.Theory.AuthTrie.canon_perm_self
#assert_axioms Minidregg.Theory.AuthTrie.root_eq_rootFast
#assert_axioms Minidregg.Theory.AuthTrie.Cache.digest_eq
#assert_axioms Minidregg.Theory.AuthTrie.Cache.buildFast_holds
#assert_axioms Minidregg.Theory.AuthTrie.Cache.insertAll_holds
#assert_axioms Minidregg.Theory.AuthTrie.Cache.opening_complete
#assert_axioms Minidregg.Theory.AuthTrie.Cache.root_lastVal_eq
