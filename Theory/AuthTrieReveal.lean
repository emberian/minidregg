/-
# Theory.AuthTrieReveal — honest reveals verify (the spec `revealFor`; the kept trie's `Trie.reveal` equality owed)

`Theory.AuthTrieRange.reveal_sound` says what a verifying reveal answers. This
module supplies the other half and the operation that serves it:

* `walkReveal_climb`: the honest walk's siblings climb the canonical root of the
  entries where it stops back to the whole canonical root.
* `reveal_complete`: the honest reveal `revealFor` of any prefix verifies against
  the canonical root of a store with distinct paths of length `L`, and answers
  exactly the store's pairs under the prefix (with `reveal_sound`, the answer of
  every verifying reveal is that one, up to a scoped collision).
* `Trie.reveal` (its equality with `revealFor`, `Cache.reveal_eq`, is owed): the same reveal read off the kept trie, one
  sibling digest per walked branch and the stopped subtree's entries, so its work
  is the walked depth plus the answer, never the store.
-/
module

public import Theory.AuthTrieRange
public import Theory.AuthTrieCache

@[expose] public section

namespace Minidregg.Theory.AuthTrie

set_option autoImplicit false

section Complete

variable {K V D : Type} [DecidableEq K] [DecidableEq V] [DecidableEq D]
variable (dig : NodeIn K V D → D)

omit [DecidableEq K] [DecidableEq V] [DecidableEq D] in
/-- **The honest walk climbs back.** Its siblings are at most the prefix and the
height; where it stops it holds the entries under the walked prefix; and their
canonical root climbs, along the walked bits, to the canonical root. -/
theorem walkReveal_climb : ∀ (n : Nat) (es : List (Entry K V)) (p : List Bool),
    (walkReveal dig n es p).1.length ≤ p.length ∧ (walkReveal dig n es p).1.length ≤ n ∧
      (walkReveal dig n es p).2 = select (p.take (walkReveal dig n es p).1.length) es ∧
      climb dig (p.take (walkReveal dig n es p).1.length) (walkReveal dig n es p).1
        (tree dig (n - (walkReveal dig n es p).1.length) (walkReveal dig n es p).2) = tree dig n es
  | n, es, [] => by
      cases n <;> cases es <;> simp [walkReveal, select, climb]
  | n, [], _ :: _ => by simp [walkReveal, select, climb]
  | n, [e], _ :: _ => by simp [walkReveal, select, climb]
  | 0, _ :: _ :: _, _ :: _ => by simp [walkReveal, select, climb]
  | n + 1, a :: c :: rest, b :: p => by
      obtain ⟨short, low, stop, climbed⟩ := walkReveal_climb n (strip b (a :: c :: rest)) p
      simp only [walkReveal, List.length_cons, List.take_succ_cons, select]
      refine ⟨by omega, by omega, stop, ?_⟩
      rw [Nat.add_sub_add_right, tree_succ_two dig n (by simp)]
      cases b
      · simp only [climb, Bool.false_eq_true, ite_false, climbed, Bool.not_false]
      · simp only [climb, ite_true, climbed, Bool.not_true]

/-- The revealed members, carried back below the stop depth, are exactly the
entries under the walked prefix. -/
theorem entriesBelow_select (bitsOf : K → List Bool) (kvs : List (K × V)) (q : List Bool) :
    Reveal.entriesBelow bitsOf q.length
        ((select q (entries bitsOf kvs)).map fun e => (e.1, e.2.2)) =
      select q (entries bitsOf kvs) := by
  rw [Reveal.entriesBelow, List.map_map]
  conv_rhs => rw [← List.map_id (select q (entries bitsOf kvs))]
  refine List.map_congr_left fun e he => ?_
  obtain ⟨k, rest, v⟩ := e
  have mem := (mem_select q _ k rest v).mp he
  obtain ⟨kv, _, eq⟩ := List.mem_map.mp mem
  simp only [Prod.mk.injEq] at eq
  obtain ⟨hk, hbits, _⟩ := eq
  subst hk
  simp [hbits]

/-- **Reveal completeness.** The honest reveal of a prefix of length at most `L`
verifies against the canonical root of a store with distinct paths of length `L`. -/
theorem reveal_complete (bitsOf : K → List Bool) (L : Nat) (lengths : ∀ k, (bitsOf k).length = L)
    (kvs : List (K × V)) (wf : WF L (entries bitsOf kvs)) (p : List Bool) (short : p.length ≤ L) :
    revealVerify dig bitsOf L (tree dig L (entries bitsOf kvs)) p (revealFor dig bitsOf L kvs p) = true := by
  obtain ⟨walkShort, walkLow, stop, climbed⟩ := walkReveal_climb dig L (entries bitsOf kvs) p
  generalize hw : walkReveal dig L (entries bitsOf kvs) p = w at walkShort walkLow stop climbed
  obtain ⟨sibs, stopped⟩ := w
  simp only at walkShort walkLow stop climbed
  subst stop
  have takeLen : (p.take sibs.length).length = sibs.length := by
    rw [List.length_take]; exact Nat.min_eq_left walkShort
  have below := entriesBelow_select bitsOf kvs (p.take sibs.length)
  rw [takeLen] at below
  simp only [revealVerify, revealFor, hw, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨walkShort, short⟩, ?_⟩, ?_⟩, ?_⟩
  · intro kv hkv
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hkv
    obtain ⟨k, rest, v⟩ := e
    have mem := (mem_select _ _ k rest v).mp he
    obtain ⟨kv', _, eq⟩ := List.mem_map.mp mem
    simp only [Prod.mk.injEq] at eq
    obtain ⟨hk, hbits, _⟩ := eq
    subst hk
    simp only
    rw [hbits, List.take_append_of_le_length (by rw [takeLen]; exact Nat.le_refl _), List.take_of_length_le (by rw [takeLen]; exact Nat.le_refl _)]
  · have nd := (select_wf (p.take sibs.length) (L - sibs.length) _
      (by rw [takeLen, Nat.add_sub_cancel' walkLow]; exact wf)).2
    convert nd using 1
    conv_rhs => rw [← below]
    simp [Reveal.entriesBelow, List.map_map, Function.comp_def]
  · rw [below]
    exact climbed

/-- With `reveal_sound`: the honest reveal answers exactly the store's pairs under
the prefix. -/
theorem revealFor_answer (bitsOf : K → List Bool) (L : Nat) (kvs : List (K × V))
    (p : List Bool) (k : K) (v : V) :
    (k, v) ∈ (revealFor dig bitsOf L kvs p).answer bitsOf p ↔
      (k, v) ∈ kvs ∧ (bitsOf k).take p.length = p := by
  obtain ⟨walkShort, _, stop, _⟩ := walkReveal_climb dig L (entries bitsOf kvs) p
  generalize hw : walkReveal dig L (entries bitsOf kvs) p = w at walkShort stop
  obtain ⟨sibs, stopped⟩ := w
  simp only at walkShort stop
  subst stop
  simp only [Reveal.answer, revealFor, hw, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨mem, pre⟩
    obtain ⟨e, he, eq⟩ := List.mem_map.mp mem
    obtain ⟨k', rest, v'⟩ := e
    simp only [Prod.mk.injEq] at eq
    obtain ⟨hk, hv⟩ := eq
    rw [hk, hv] at he
    have := (mem_select _ _ k rest v).mp he
    obtain ⟨kv, kvMem, eq⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at eq
    obtain ⟨hk', _, hv'⟩ := eq
    have : kv = (k, v) := Prod.ext hk' hv'
    exact ⟨this ▸ kvMem, pre⟩
  · rintro ⟨mem, pre⟩
    refine ⟨List.mem_map.mpr ⟨(k, (bitsOf k).drop sibs.length, v), ?_, rfl⟩, pre⟩
    rw [mem_select]
    have under : (bitsOf k).take sibs.length = p.take sibs.length := by
      calc (bitsOf k).take sibs.length = ((bitsOf k).take p.length).take sibs.length := by
            rw [List.take_take, Nat.min_eq_left walkShort]
        _ = p.take sibs.length := by rw [pre]
    rw [← under, List.take_append_drop]
    exact List.mem_map.mpr ⟨(k, v), mem, rfl⟩

end Complete

/-! ## The reveal read off the kept trie -/

namespace Trie

variable {K V D : Type} (dig : NodeIn K V D → D)

/-- Walk the kept trie down a prefix: one sibling digest per branch walked, and
the stopped subtree's pairs. -/
def reveal : List Bool → Trie K V D → List D × List (K × V)
  | b :: p, .branch _ l r =>
      let below := reveal p (if b then r else l)
      ((if b then l else r).digest dig :: below.1, below.2)
  | _, t => ([], t.entries.map fun e => (e.1, e.2.2))

end Trie

end Minidregg.Theory.AuthTrie
