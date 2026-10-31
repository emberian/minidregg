/-
# Theory.AuthTrieRange — subtree reveals of the compressed authenticated trie

KN2-STORE-OPEN's keyed index (`Compiler.DurableIndex`) answers multi-valued
queries (backlinks of a target, links of a cell, payments to a destination) by
revealing EVERY entry under a key prefix, verified against the root. The
single-key opening of `Theory.AuthTrie` cannot say "these are all of them"; a
reveal can.

* `tree_injective` — two well-formed entry lists with one canonical root hold the
  same key/value pairs, or two distinct nodes of the two trees share a digest.
* `climb_digest_sound` — a digest that climbs, with a sibling for every walked
  bit, to the canonical root is the canonical root of the entries under the
  walked prefix, or two distinct nodes of the tree and the climb share a digest.
* `revealVerify` / `reveal_sound` — a verifying reveal for prefix `p` answers
  exactly the key/value pairs whose key path starts with `p`: nothing omitted,
  nothing forged, or two distinct nodes of this comparison's finite scope
  (`revealNodes`) share a digest. No premise about the reveal
  or the Store's rows.
* `reveal_complete` — the honest reveal verifies.
* Decided poles: an honest reveal is accepted; one that omits a member, forges a
  value, or adds a non-member is refused.

Paging (a large set is read as a sequence of reveals of consecutive sub-prefixes)
is the caller's cursor over these reveals: each page is one `revealVerify`.
-/
module

public import Theory.AuthTrie

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

section Range

variable {K V D : Type} [DecidableEq K] [DecidableEq V] [DecidableEq D]
variable (dig : NodeIn K V D → D)

set_option linter.unusedSectionVars false

/-- Two entry lists hold the same key/value pairs (whatever their remaining paths). -/
def SameKV (es₁ es₂ : List (Entry K V)) : Prop :=
  ∀ k v, (∃ bits, (k, bits, v) ∈ es₁) ↔ (∃ bits, (k, bits, v) ∈ es₂)

theorem mem_strip (b : Bool) (es : List (Entry K V)) (k : K) (rest : List Bool) (v : V) :
    (k, rest, v) ∈ strip b es ↔ (k, b :: rest, v) ∈ es := by
  simp only [strip, List.mem_filterMap]
  constructor
  · rintro ⟨⟨k', bits, v'⟩, mem, h⟩
    cases bits with
    | nil => simp at h
    | cons bit tail =>
        simp only at h
        split at h
        · rename_i same
          cases h
          subst same
          exact mem
        · cases h
  · intro mem
    exact ⟨(k, b :: rest, v), mem, by simp⟩

/-- An entry under a prefix is an entry of the list whose path is the prefix
followed by its remaining path. -/
theorem mem_select : ∀ (q : List Bool) (es : List (Entry K V)) (k : K) (rest : List Bool) (v : V),
    (k, rest, v) ∈ select q es ↔ (k, q ++ rest, v) ∈ es
  | [], es, k, rest, v => by simp [select]
  | b :: q, es, k, rest, v => by
      simp only [select, List.cons_append]
      rw [mem_select q (strip b es) k rest v, mem_strip]

theorem select_wf : ∀ (q : List Bool) (n : Nat) (es : List (Entry K V)),
    WF (q.length + n) es → WF n (select q es)
  | [], n, es, wf => by simpa [select] using wf
  | b :: q, n, es, wf => by
      simp only [select]
      apply select_wf q n (strip b es)
      apply strip_wf
      simpa [Nat.add_assoc, Nat.add_comm 1, List.length_cons] using wf

/-- Two distinct entries of a well-formed list at 0 remaining bits are impossible. -/
private theorem wf_zero_pair {a b : Entry K V} {rest : List (Entry K V)}
    (wf : WF 0 (a :: b :: rest)) : False := by
  have la : a.2.1 = [] := List.eq_nil_of_length_eq_zero (wf.1 a (by simp))
  have lb : b.2.1 = [] := List.eq_nil_of_length_eq_zero (wf.1 b (by simp))
  have := (List.nodup_cons.mp wf.2).1
  exact this (List.mem_map.mpr ⟨b, by simp, by show b.2.1 = a.2.1; rw [la, lb]⟩)

/-- At `n + 1` remaining bits, an entry's key/value is under one of the two halves. -/
private theorem sameKV_of_strips (n : Nat) (es₁ es₂ : List (Entry K V))
    (wf₁ : WF (n + 1) es₁) (wf₂ : WF (n + 1) es₂)
    (left : SameKV (strip false es₁) (strip false es₂))
    (right : SameKV (strip true es₁) (strip true es₂)) : SameKV es₁ es₂ := by
  have half : ∀ (es : List (Entry K V)), WF (n + 1) es → ∀ k v,
      (∃ bits, (k, bits, v) ∈ es) ↔
        (∃ bits, (k, bits, v) ∈ strip false es) ∨ (∃ bits, (k, bits, v) ∈ strip true es) := by
    intro es wf k v
    constructor
    · rintro ⟨bits, mem⟩
      have len := wf.1 _ mem
      cases bits with
      | nil => simp at len
      | cons bit tail =>
          cases bit
          · exact Or.inl ⟨tail, (mem_strip false es k tail v).mpr mem⟩
          · exact Or.inr ⟨tail, (mem_strip true es k tail v).mpr mem⟩
    · rintro (⟨bits, mem⟩ | ⟨bits, mem⟩)
      · exact ⟨false :: bits, (mem_strip false es k bits v).mp mem⟩
      · exact ⟨true :: bits, (mem_strip true es k bits v).mp mem⟩
  intro k v
  rw [half es₁ wf₁ k v, half es₂ wf₂ k v, left k v, right k v]

/-- Two canonical roots that agree in digest but not in node input collide among
the two trees' nodes. -/
private theorem roots_collide {n : Nat} {es₁ es₂ : List (Entry K V)}
    (equal : tree dig n es₁ = tree dig n es₂) (ne : treeNode dig n es₁ ≠ treeNode dig n es₂) :
    CollisionAmong dig (fun x => TreeNode dig n es₁ x ∨ TreeNode dig n es₂ x) :=
  ⟨_, _, Or.inl (TreeNode.root _ _), Or.inr (TreeNode.root _ _), ne,
    by rw [← tree_eq_treeNode dig n es₁, ← tree_eq_treeNode dig n es₂]; exact equal⟩

/-- **The canonical root determines the key/value pairs**, or two distinct nodes
of the two canonical trees share a digest. -/
theorem tree_injective : ∀ (n : Nat) (es₁ es₂ : List (Entry K V)),
    WF n es₁ → WF n es₂ → tree dig n es₁ = tree dig n es₂ →
      SameKV es₁ es₂ ∨ CollisionAmong dig (fun x => TreeNode dig n es₁ x ∨ TreeNode dig n es₂ x)
  | _, [], [], _, _, _ => Or.inl fun _ _ => Iff.rfl
  | _, [], [e], _, _, equal =>
      Or.inr (roots_collide dig equal (by rw [treeNode_nil, treeNode_single]; simp))
  | _, [e], [], _, _, equal =>
      Or.inr (roots_collide dig equal (by rw [treeNode_nil, treeNode_single]; simp))
  | _, [e₁], [e₂], _, _, equal => by
      by_cases same : (NodeIn.leaf e₁.1 e₁.2.2 : NodeIn K V D) = .leaf e₂.1 e₂.2.2
      · left
        simp only [NodeIn.leaf.injEq] at same
        obtain ⟨hk, hv⟩ := same
        intro k v
        constructor
        · rintro ⟨bits, mem⟩
          simp only [List.mem_singleton] at mem
          refine ⟨e₂.2.1, ?_⟩
          simp only [List.mem_singleton]
          obtain ⟨k₂, b₂, v₂⟩ := e₂
          simp only at hk hv
          rw [← hk, ← hv, ← mem]
        · rintro ⟨bits, mem⟩
          simp only [List.mem_singleton] at mem
          refine ⟨e₁.2.1, ?_⟩
          simp only [List.mem_singleton]
          obtain ⟨k₁, b₁, v₁⟩ := e₁
          simp only at hk hv
          rw [hk, hv, ← mem]
      · exact Or.inr (roots_collide dig equal (by rw [treeNode_single, treeNode_single]; exact same))
  | 0, a :: b :: rest, _, wf₁, _, _ => (wf_zero_pair wf₁).elim
  | 0, _, a :: b :: rest, _, wf₂, _ => (wf_zero_pair wf₂).elim
  | m + 1, [], a :: b :: rest, _, _, equal =>
      Or.inr (roots_collide dig equal (by rw [treeNode_nil]; simp [treeNode]))
  | m + 1, a :: b :: rest, [], _, _, equal =>
      Or.inr (roots_collide dig equal (by rw [treeNode_nil]; simp [treeNode]))
  | m + 1, [e], a :: b :: rest, _, _, equal =>
      Or.inr (roots_collide dig equal (by rw [treeNode_single]; simp [treeNode]))
  | m + 1, a :: b :: rest, [e], _, _, equal =>
      Or.inr (roots_collide dig equal (by rw [treeNode_single]; simp [treeNode]))
  | m + 1, a :: b :: rest, c :: d :: more, wf₁, wf₂, equal => by
      by_cases same : treeNode dig (m + 1) (a :: b :: rest) = treeNode dig (m + 1) (c :: d :: more)
      · simp only [treeNode, NodeIn.branch.injEq] at same
        have lift : ∀ (bb : Bool) (x : NodeIn K V D),
            (TreeNode dig m (strip bb (a :: b :: rest)) x ∨ TreeNode dig m (strip bb (c :: d :: more)) x) →
              (TreeNode dig (m + 1) (a :: b :: rest) x ∨ TreeNode dig (m + 1) (c :: d :: more) x) := by
          intro bb x hx
          rcases hx with hx | hx
          · exact Or.inl (TreeNode.child _ _ bb _ hx)
          · exact Or.inr (TreeNode.child _ _ bb _ hx)
        rcases tree_injective m _ _ (strip_wf m false _ wf₁) (strip_wf m false _ wf₂) same.1 with
          left | collision
        · rcases tree_injective m _ _ (strip_wf m true _ wf₁) (strip_wf m true _ wf₂) same.2 with
            right | collision
          · exact Or.inl (sameKV_of_strips m _ _ wf₁ wf₂ left right)
          · exact Or.inr (CollisionAmong.mono dig (lift true) collision)
        · exact Or.inr (CollisionAmong.mono dig (lift false) collision)
      · exact Or.inr (roots_collide dig equal same)

/-- The branch nodes a climb from digest `below` hashes. -/
inductive ClimbDigestNode (below : D) : List Bool → List D → NodeIn K V D → Prop
  | left (bits : List Bool) (s : D) (siblings : List D) :
      ClimbDigestNode below (false :: bits) (s :: siblings) (.branch (climb dig bits siblings below) s)
  | right (bits : List Bool) (s : D) (siblings : List D) :
      ClimbDigestNode below (true :: bits) (s :: siblings) (.branch s (climb dig bits siblings below))
  | deeper (b : Bool) (bits : List Bool) (s : D) (siblings : List D) (x : NodeIn K V D) :
      ClimbDigestNode below bits siblings x → ClimbDigestNode below (b :: bits) (s :: siblings) x

/-- A node of the canonical tree under a prefix is a node of the whole tree. -/
theorem treeNode_select : ∀ (q : List Bool) (n : Nat) (es : List (Entry K V)) (x : NodeIn K V D),
    q.length ≤ n → TreeNode dig (n - q.length) (select q es) x → TreeNode dig n es x
  | [], n, es, x, _, h => by simpa [select] using h
  | b :: q, 0, _, _, long, _ => by simp at long
  | b :: q, m + 1, es, x, long, h => by
      simp only [select, List.length_cons, Nat.add_sub_add_right] at h
      exact TreeNode.child _ _ b _ (treeNode_select q m (strip b es) x (by simpa using long) h)

/-- **Digest climb soundness.** A digest that climbs, with one sibling per walked
bit, to the canonical root is the canonical root of the entries under the walked
prefix, or two distinct nodes among the canonical tree's and the climb's share a
digest. -/
theorem climb_digest_sound : ∀ (n : Nat) (es : List (Entry K V)) (bits : List Bool) (siblings : List D)
    (below : D), WF n es → siblings.length = bits.length → bits.length ≤ n →
      climb dig bits siblings below = tree dig n es →
      below = tree dig (n - bits.length) (select bits es) ∨
        CollisionAmong dig (fun x => TreeNode dig n es x ∨ ClimbDigestNode dig below bits siblings x)
  | n, es, [], [], below, _, _, _, climbed => by
      left; simpa [climb, select] using climbed
  | _, _, [], _ :: _, _, _, same, _, _ => by simp at same
  | _, _, _ :: _, [], _, _, same, _, _ => by simp at same
  | n, es, b :: bits, s :: siblings, below, wf, same, long, climbed => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at same
      simp only [climb] at climbed
      match n, es, wf with
      | 0, _, _ => simp at long
      | m + 1, [], _ =>
          right
          have root := TreeNode.root (dig := dig) (m + 1) ([] : List (Entry K V))
          rw [treeNode_nil] at root
          cases b
          · exact ⟨.branch (climb dig bits siblings below) s, .empty,
              Or.inr (ClimbDigestNode.left _ _ _), Or.inl root, by simp, by simpa [tree] using climbed⟩
          · exact ⟨.branch s (climb dig bits siblings below), .empty,
              Or.inr (ClimbDigestNode.right _ _ _), Or.inl root, by simp, by simpa [tree] using climbed⟩
      | m + 1, [e], _ =>
          right
          have root := TreeNode.root (dig := dig) (m + 1) [e]
          rw [treeNode_single] at root
          cases b
          · exact ⟨.branch (climb dig bits siblings below) s, .leaf e.1 e.2.2,
              Or.inr (ClimbDigestNode.left _ _ _), Or.inl root, by simp, by simpa [tree] using climbed⟩
          · exact ⟨.branch s (climb dig bits siblings below), .leaf e.1 e.2.2,
              Or.inr (ClimbDigestNode.right _ _ _), Or.inl root, by simp, by simpa [tree] using climbed⟩
      | m + 1, a :: c :: rest, wf =>
          have rootEq : tree dig (m + 1) (a :: c :: rest) =
              dig (.branch (tree dig m (strip false (a :: c :: rest)))
                (tree dig m (strip true (a :: c :: rest)))) := by simp [tree]
          rw [rootEq] at climbed
          have long' : bits.length ≤ m := by simpa using long
          have sub : m + 1 - (bits.length + 1) = m - bits.length := by omega
          have root := TreeNode.root (dig := dig) (m + 1) (a :: c :: rest)
          simp only [treeNode] at root
          have lift : ∀ (bb : Bool) (x : NodeIn K V D),
              (TreeNode dig m (strip bb (a :: c :: rest)) x ∨ ClimbDigestNode dig below bits siblings x) →
              (TreeNode dig (m + 1) (a :: c :: rest) x ∨
                ClimbDigestNode dig below (b :: bits) (s :: siblings) x) := by
            intro bb x hx
            rcases hx with hx | hx
            · exact Or.inl (TreeNode.child _ _ bb _ hx)
            · exact Or.inr (ClimbDigestNode.deeper _ _ _ _ _ hx)
          simp only [List.length_cons, sub, select]
          cases b with
          | false =>
              simp only [Bool.false_eq_true, ite_false] at climbed
              by_cases agree : (NodeIn.branch (climb dig bits siblings below) s : NodeIn K V D) =
                  .branch (tree dig m (strip false (a :: c :: rest))) (tree dig m (strip true (a :: c :: rest)))
              · simp only [NodeIn.branch.injEq] at agree
                exact (climb_digest_sound m _ bits siblings below (strip_wf m false _ wf) same long'
                  agree.1).imp_right (CollisionAmong.mono dig (lift false))
              · exact Or.inr ⟨_, _, Or.inr (ClimbDigestNode.left _ _ _), Or.inl root, agree, climbed⟩
          | true =>
              simp only [ite_true] at climbed
              by_cases agree : (NodeIn.branch s (climb dig bits siblings below) : NodeIn K V D) =
                  .branch (tree dig m (strip false (a :: c :: rest))) (tree dig m (strip true (a :: c :: rest)))
              · simp only [NodeIn.branch.injEq] at agree
                exact (climb_digest_sound m _ bits siblings below (strip_wf m true _ wf) same long'
                  agree.2).imp_right (CollisionAmong.mono dig (lift true))
              · exact Or.inr ⟨_, _, Or.inr (ClimbDigestNode.right _ _ _), Or.inl root, agree, climbed⟩

/-- A reveal: the siblings of the walk to depth `siblings.length` along the
prefix, and every key/value pair under the walked prefix. -/
structure Reveal (K V D : Type) where
  siblings : List D
  members : List (K × V)

/-- The revealed members as entries carrying their remaining paths below `depth`. -/
def Reveal.entriesBelow (bitsOf : K → List Bool) (depth : Nat) (members : List (K × V)) :
    List (Entry K V) :=
  members.map fun kv => (kv.1, (bitsOf kv.1).drop depth, kv.2)

/-- **The reveal verifier.** The walk stops at depth `d ≤ |p|` (the honest walk
stops early only where the subtree is one leaf or empty); every revealed key
lies under the walked prefix, their remaining paths are distinct, and the
canonical root of the revealed members climbs to the root. -/
def revealVerify (bitsOf : K → List Bool) (L : Nat) (root : D) (p : List Bool)
    (reveal : Reveal K V D) : Bool :=
  let depth := reveal.siblings.length
  decide (depth ≤ p.length) && decide (p.length ≤ L) &&
  reveal.members.all (fun kv => decide ((bitsOf kv.1).take depth = p.take depth)) &&
  decide ((reveal.members.map fun kv => (bitsOf kv.1).drop depth).Nodup) &&
  decide (climb dig (p.take depth) reveal.siblings
    (tree dig (L - depth) (Reveal.entriesBelow bitsOf depth reveal.members)) = root)

/-- What a verified reveal answers: the revealed members whose key path starts with `p`. -/
def Reveal.answer (bitsOf : K → List Bool) (p : List Bool) (reveal : Reveal K V D) : List (K × V) :=
  reveal.members.filter fun kv => decide ((bitsOf kv.1).take p.length = p)

/-- A finite comparison scope containing the nodes one reveal comparison hashes:
the canonical tree over `es`, the reveal's climb from the revealed subtree to the
root, and the canonical tree of the revealed members below the stop depth. Fixed
by `es` and the reveal. It over-approximates the nodes actually hashed
(`TreeNode.child` also descends beneath singleton leaves), and it still admits a
collision elsewhere in the same store; restricting the store side to the
authentication path and the selected subtree is the stronger locality. -/
def revealNodes (bitsOf : K → List Bool) (L : Nat) (es : List (Entry K V)) (p : List Bool)
    (reveal : Reveal K V D) : NodeIn K V D → Prop := fun x =>
  TreeNode dig L es x ∨
    ClimbDigestNode dig (tree dig (L - reveal.siblings.length)
      (Reveal.entriesBelow bitsOf reveal.siblings.length reveal.members))
      (p.take reveal.siblings.length) reveal.siblings x ∨
    TreeNode dig (L - reveal.siblings.length)
      (Reveal.entriesBelow bitsOf reveal.siblings.length reveal.members) x

/-- **Reveal soundness.** Over the canonical root of `kvs` (full paths of length
`L`), a verifying reveal for `p` answers EXACTLY the pairs of `kvs` whose key
path starts with `p` — none omitted, none forged — or two distinct nodes among
the comparison scope (`revealNodes`) share a digest. -/
theorem reveal_sound (bitsOf : K → List Bool) (L : Nat) (lengths : ∀ k, (bitsOf k).length = L)
    (kvs : List (K × V)) (wf : WF L (entries bitsOf kvs)) (p : List Bool) (reveal : Reveal K V D)
    (accepted : revealVerify dig bitsOf L (tree dig L (entries bitsOf kvs)) p reveal = true) :
    (∀ k v, (k, v) ∈ reveal.answer bitsOf p ↔ (k, v) ∈ kvs ∧ (bitsOf k).take p.length = p) ∨
      CollisionAmong dig (revealNodes dig bitsOf L (entries bitsOf kvs) p reveal) := by
  simp only [revealVerify, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at accepted
  unfold revealNodes
  obtain ⟨⟨⟨⟨short, withinL⟩, under⟩, nodup⟩, climbed⟩ := accepted
  generalize hdepth : reveal.siblings.length = depth at *
  have takeLen : (p.take depth).length = depth := by
    rw [List.length_take]; exact Nat.min_eq_left short
  rcases climb_digest_sound dig L (entries bitsOf kvs) (p.take depth) reveal.siblings _ wf
      (hdepth.trans takeLen.symm) (by rw [takeLen]; omega) climbed with same | collision
  · rw [takeLen] at same
    have wfSel : WF (L - depth) (select (p.take depth) (entries bitsOf kvs)) :=
      select_wf (p.take depth) (L - depth) _ (by rw [takeLen, Nat.add_sub_cancel' (by omega)]; exact wf)
    have wfRev : WF (L - depth) (Reveal.entriesBelow bitsOf depth reveal.members) := by
      refine ⟨?_, ?_⟩
      · intro e he
        obtain ⟨kv, _, rfl⟩ := List.mem_map.mp he
        simp [lengths]
      · simpa [Reveal.entriesBelow, Function.comp_def] using nodup
    rcases tree_injective dig (L - depth) _ _ wfRev wfSel same with kvSame | collision
    · left
      intro k v
      simp only [Reveal.answer, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨mem, pre⟩
        have inRev : ∃ bits, (k, bits, v) ∈ Reveal.entriesBelow bitsOf depth reveal.members :=
          ⟨(bitsOf k).drop depth, List.mem_map.mpr ⟨(k, v), mem, rfl⟩⟩
        obtain ⟨bits, inSel⟩ := (kvSame k v).mp inRev
        have inAll := (mem_select (p.take depth) _ k bits v).mp inSel
        obtain ⟨kv, kvMem, eq⟩ := List.mem_map.mp inAll
        simp only [Prod.mk.injEq] at eq
        obtain ⟨hk, _, hv⟩ := eq
        subst hk; subst hv
        exact ⟨kvMem, pre⟩
      · rintro ⟨mem, pre⟩
        have underDepth : (bitsOf k).take depth = p.take depth := by
          have : (bitsOf k).take depth = ((bitsOf k).take p.length).take depth := by
            rw [List.take_take, Nat.min_eq_left short]
          rw [this, pre]
        have inSel : (k, (bitsOf k).drop depth, v) ∈ select (p.take depth) (entries bitsOf kvs) := by
          rw [mem_select]
          rw [← underDepth, List.take_append_drop]
          exact List.mem_map.mpr ⟨(k, v), mem, rfl⟩
        obtain ⟨bits, inRev⟩ := (kvSame k v).mpr ⟨_, inSel⟩
        obtain ⟨kv, kvMem, eq⟩ := List.mem_map.mp inRev
        simp only [Prod.mk.injEq] at eq
        obtain ⟨hk, _, hv⟩ := eq
        have : kv = (k, v) := by
          obtain ⟨k', v'⟩ := kv
          simp only at hk hv
          rw [hk, hv]
        exact ⟨this ▸ kvMem, pre⟩
    · refine Or.inr (CollisionAmong.mono dig (fun x hx => ?_) collision)
      rcases hx with hx | hx
      · exact Or.inr (Or.inr hx)
      · refine Or.inl (treeNode_select dig (p.take depth) L _ x (by rw [takeLen]; omega) ?_)
        rw [takeLen]
        exact hx
  · refine Or.inr (CollisionAmong.mono dig (fun x hx => ?_) collision)
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)

/-- The honest walk for a reveal: down the prefix while the subtree has two or more
entries, one sibling per step; the entries of the subtree where it stops. -/
def walkReveal : Nat → List (Entry K V) → List Bool → List D × List (Entry K V)
  | _, es, [] => ([], es)
  | _, [], _ :: _ => ([], [])
  | _, [e], _ :: _ => ([], [e])
  | 0, es, _ :: _ => ([], es)
  | n + 1, es@(_ :: _ :: _), b :: p =>
      let below := walkReveal n (strip b es) p
      (tree dig n (strip (!b) es) :: below.1, below.2)

/-- The honest reveal of prefix `p` over `kvs`. -/
def revealFor (bitsOf : K → List Bool) (L : Nat) (kvs : List (K × V)) (p : List Bool) : Reveal K V D :=
  let walked := walkReveal dig L (entries bitsOf kvs) p
  ⟨walked.1, walked.2.map fun e => (e.1, e.2.2)⟩

end Range

/-! ## Decided poles: the 3-bit toy of `AuthTrie.Poles` -/

namespace RangePoles

open Poles (bitsOf toy kvs root)

/-- Under `[false]`: keys 001 and 011. -/
def honest : Reveal (List Bool) Nat String := revealFor toy bitsOf 3 kvs [false]

theorem honest_members : honest.members = [([false, false, true], 7), ([false, true, true], 9)] := by decide
theorem honest_verified : revealVerify toy bitsOf 3 root [false] honest = true := by decide
theorem honest_answer : honest.answer bitsOf [false] = [([false, false, true], 7), ([false, true, true], 9)] := by
  decide

/-- A reveal that omits a member is refused. -/
theorem omitted_refused :
    revealVerify toy bitsOf 3 root [false] ⟨honest.siblings, [([false, false, true], 7)]⟩ = false := by decide

/-- A reveal with a forged value is refused. -/
theorem forged_value_refused :
    revealVerify toy bitsOf 3 root [false]
      ⟨honest.siblings, [([false, false, true], 8), ([false, true, true], 9)]⟩ = false := by decide

/-- A reveal that adds a non-member is refused. -/
theorem added_refused :
    revealVerify toy bitsOf 3 root [false]
      ⟨honest.siblings, [([false, false, true], 7), ([false, true, false], 1), ([false, true, true], 9)]⟩ =
        false := by decide

/-- An empty prefix subtree (`[true, false]`): the honest reveal answers nothing, verified. -/
theorem empty_verified : revealVerify toy bitsOf 3 root [true, false] (revealFor toy bitsOf 3 kvs [true, false]) = true ∧
    (revealFor toy bitsOf 3 kvs [true, false] : Reveal (List Bool) Nat String).answer bitsOf [true, false] = [] := by
  decide

/-- Claiming a member under an empty subtree is refused: a forged `100 ↦ 5` beside the
subtree's only leaf `110`. -/
theorem empty_claimed_member_refused :
    revealVerify toy bitsOf 3 root [true, false]
      ⟨(revealFor toy bitsOf 3 kvs [true, false] : Reveal (List Bool) Nat String).siblings,
        [([true, false, false], 5), ([true, true, false], 3)]⟩ = false := by decide

/-- Withholding the leaf the walk stopped at (to claim the subtree empty) is refused. -/
theorem empty_withheld_leaf_refused :
    revealVerify toy bitsOf 3 root [true, false]
      ⟨(revealFor toy bitsOf 3 kvs [true, false] : Reveal (List Bool) Nat String).siblings, []⟩ = false := by
  decide

end RangePoles

#assert_axioms mem_strip
#assert_axioms mem_select
#assert_axioms select_wf
#assert_axioms tree_injective
#assert_axioms climb_digest_sound
#assert_axioms reveal_sound
#assert_axioms RangePoles.honest_verified
#assert_axioms RangePoles.honest_answer
#assert_axioms RangePoles.omitted_refused
#assert_axioms RangePoles.forged_value_refused
#assert_axioms RangePoles.added_refused
#assert_axioms RangePoles.empty_verified
#assert_axioms RangePoles.empty_claimed_member_refused
#assert_axioms RangePoles.empty_withheld_leaf_refused

end Minidregg.Theory.AuthTrie
