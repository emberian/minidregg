/-
# Theory.AuthTrieReveal — honest reveals verify, and the kept trie serves them

`Theory.AuthTrieRange.reveal_sound` says what a verifying reveal answers. This
module supplies the other half and the operation that serves it:

* `walkReveal_climb`: the honest walk's siblings climb the canonical root of the
  entries where it stops back to the whole canonical root.
* `reveal_complete`: the honest reveal `revealFor` of any prefix verifies against
  the canonical root of a store with distinct paths of length `L`, and answers
  exactly the store's pairs under the prefix (with `reveal_sound`, the answer of
  every verifying reveal is that one, up to a scoped collision).
* `Trie.reveal`: the same reveal read off the kept trie: one cached sibling
  digest per walked branch, then the stopped subtree's entries, listed by
  `Trie.entries` (work about that subtree's size times its height). It touches
  the walked path and the stopped subtree only; the subtree is the answer
  under a full-length prefix, and can be the whole store under a short one. `Cache.reveal_eq`: its siblings are the
  honest reveal's and its members a permutation of them; `Cache.reveal_verifies`:
  it verifies against the cache's logical root (verification is invariant under
  permuting members, `revealVerify_perm`).
-/
module

public import Theory.AuthTrieRange
public import Theory.AuthTrieCache
public import Theory.AssertAxioms

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

/-- **The honest walk stops early only at one leaf or none**: on a prefix no longer than the
remaining depth, a walk with fewer siblings than prefix bits stopped at a subtree of at most one
entry. A bounded opening carries at most one terminal member per prefix that it stops above. -/
theorem walkReveal_short_stop : ∀ (n : Nat) (es : List (Entry K V)) (p : List Bool), p.length ≤ n →
    (walkReveal dig n es p).1.length < p.length → (walkReveal dig n es p).2.length ≤ 1
  | _, es, [], _, short => by simp at short
  | _, [], _ :: _, _, _ => by simp [walkReveal]
  | _, [e], _ :: _, _, _ => by simp [walkReveal]
  | 0, _ :: _ :: _, _ :: _, depth, _ => by simp at depth
  | n + 1, e₁ :: e₂ :: rest, b :: p, depth, short => by
      simp only [walkReveal, List.length_cons] at short ⊢
      exact walkReveal_short_stop n _ p (by simp at depth; omega) (by omega)

/-- The honest reveal is bounded: fewer siblings than prefix bits means at most one member. -/
theorem revealFor_shaped (bitsOf : K → List Bool) (L : Nat) (kvs : List (K × V)) (p : List Bool)
    (short : p.length ≤ L) (early : (revealFor dig bitsOf L kvs p).siblings.length < p.length) :
    (revealFor dig bitsOf L kvs p).members.length ≤ 1 := by
  simp only [revealFor, List.length_map] at early ⊢
  exact walkReveal_short_stop dig L _ p short early

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


section Kept

variable {K V D : Type} [DecidableEq K] [DecidableEq V] [DecidableEq D]
variable (dig : NodeIn K V D → D)

omit [DecidableEq K] [DecidableEq V] [DecidableEq D] in
/-- **The kept trie's reveal is the honest walk**: the same siblings, and the
members up to order. -/
theorem Trie.reveal_walk : ∀ (n : Nat) (t : Trie K V D) (es : List (Entry K V)) (p : List Bool),
    Trie.Inv dig n t → t.entries.Perm es →
      (Trie.reveal dig p t).1 = (walkReveal dig n es p).1 ∧
        (Trie.reveal dig p t).2.Perm ((walkReveal dig n es p).2.map fun e => (e.1, e.2.2))
  | n, t, es, [], _, h => by
      have served : Trie.reveal dig [] t = ([], t.entries.map fun e => (e.1, e.2.2)) := by
        cases t <;> rfl
      rw [served]
      exact ⟨by simp [walkReveal], by simpa [walkReveal] using h.map (fun e => (e.1, e.2.2))⟩
  | n, .empty, es, _ :: _, _, h => by
      simp only [Trie.entries] at h
      obtain rfl := h.nil_eq
      cases n <;> exact ⟨rfl, List.Perm.refl _⟩
  | n, .leaf d rest k v, es, _ :: _, _, h => by
      simp only [Trie.entries] at h
      obtain rfl := List.perm_singleton.mp h.symm
      cases n <;> exact ⟨rfl, List.Perm.refl _⟩
  | 0, .clash kvs, es, b :: p, inv, h => by
      have two : 2 ≤ es.length := by
        have := h.length_eq
        simp only [Trie.Inv] at inv
        simp only [Trie.entries, List.length_map] at this
        omega
      match es, two with
      | a :: c :: rest, _ => exact ⟨rfl, h.map _⟩
  | _ + 1, .clash _, _, _ :: _, inv, _ => by simp [Trie.Inv] at inv
  | 0, .branch .., _, _ :: _, inv, _ => by simp [Trie.Inv] at inv
  | n + 1, .branch d l r, es, b :: p, inv, h => by
      obtain ⟨il, ir, _, twoLR⟩ := inv
      have two : 2 ≤ es.length := by
        have := h.length_eq
        simp only [Trie.entries, List.length_append, List.length_map] at this
        omega
      match es, two, h with
      | a :: c :: rest, _, h =>
        cases b with
        | false =>
            have hl : l.entries.Perm (strip false (a :: c :: rest)) := by
              have := strip_perm false h
              rwa [Trie.entries, Trie.strip_false_branch] at this
            have hr : r.entries.Perm (strip true (a :: c :: rest)) := by
              have := strip_perm true h
              rwa [Trie.entries, Trie.strip_true_branch] at this
            obtain ⟨s, m⟩ := Trie.reveal_walk n l _ p il hl
            refine ⟨?_, m⟩
            simp only [Trie.reveal, walkReveal, Bool.false_eq_true, ite_false, Bool.not_false, s]
            rw [Trie.digest_eq dig n r ir, tree_perm dig n hr]
        | true =>
            have hl : l.entries.Perm (strip false (a :: c :: rest)) := by
              have := strip_perm false h
              rwa [Trie.entries, Trie.strip_false_branch] at this
            have hr : r.entries.Perm (strip true (a :: c :: rest)) := by
              have := strip_perm true h
              rwa [Trie.entries, Trie.strip_true_branch] at this
            obtain ⟨s, m⟩ := Trie.reveal_walk n r _ p ir hr
            refine ⟨?_, m⟩
            simp only [Trie.reveal, walkReveal, ite_true, Bool.not_true, s]
            rw [Trie.digest_eq dig n l il, tree_perm dig n hl]

/-- Verification does not depend on the order of the revealed members. -/
theorem revealVerify_perm (bitsOf : K → List Bool) (L : Nat) (root : D) (p : List Bool)
    {r r' : Reveal K V D} (hs : r.siblings = r'.siblings) (h : r.members.Perm r'.members) :
    revealVerify dig bitsOf L root p r = revealVerify dig bitsOf L root p r' := by
  rw [Bool.eq_iff_iff]
  simp only [revealVerify, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Reveal.entriesBelow, hs]
  rw [tree_perm dig _ (h.map (fun kv => (kv.1, (bitsOf kv.1).drop r'.siblings.length, kv.2))),
    (h.map (fun kv => (bitsOf kv.1).drop r'.siblings.length)).nodup_iff]
  simp only [h.mem_iff]
  constructor
  · rintro ⟨rest, climbed⟩
    exact ⟨rest, decide_eq_true climbed⟩
  · rintro ⟨rest, climbed⟩
    exact ⟨rest, of_decide_eq_true climbed⟩

namespace Cache

variable {dig} {bitsOf : K → List Bool} {L : Nat}

omit [DecidableEq V] [DecidableEq D] in
/-- **`Cache.reveal_eq`**: the reveal served by the kept trie has the honest
reveal's siblings and, up to order, its members. -/
theorem reveal_eq {cache : Cache dig bitsOf L} {es : List (K × V)} (h : cache.Holds es) (p : List Bool) :
    (Trie.reveal dig p cache.trie).1 = (revealFor dig bitsOf L (canon es) p).siblings ∧
      (Trie.reveal dig p cache.trie).2.Perm (revealFor dig bitsOf L (canon es) p).members :=
  Trie.reveal_walk dig L cache.trie _ p cache.inv h

/-- **The served reveal verifies** against the cache's logical root. -/
theorem reveal_verifies {cache : Cache dig bitsOf L} {es : List (K × V)} (h : cache.Holds es)
    (lengths : ∀ k, (bitsOf k).length = L) (inj : PathsInjective bitsOf es) (p : List Bool)
    (short : p.length ≤ L) :
    revealVerify dig bitsOf L (root dig bitsOf L es) p
      ⟨(Trie.reveal dig p cache.trie).1, (Trie.reveal dig p cache.trie).2⟩ = true := by
  obtain ⟨s, m⟩ := reveal_eq h p
  have honest := reveal_complete dig bitsOf L lengths (canon es) (wf_canon lengths inj) p short
  exact (revealVerify_perm dig bitsOf L _ p (r' := revealFor dig bitsOf L (canon es) p) s m).trans honest

end Cache

end Kept

#assert_axioms reveal_complete
#assert_axioms walkReveal_short_stop
#assert_axioms revealFor_shaped
#assert_axioms Trie.reveal_walk
#assert_axioms Cache.reveal_eq
#assert_axioms Cache.reveal_verifies

end Minidregg.Theory.AuthTrie
