/-
# Theory.AuthTrie — a compressed authenticated binary trie with O(log n) openings

KN2-STORE-OPEN's spent set and transaction index (`Compiler.DurableSpent`).
`Theory.AuthMap` is the uncompressed sparse Merkle map: its openings cost
`depth + 1 = 257` hashes. Here a subtree holding exactly one entry is that
entry's leaf, at the highest level where it is alone; an empty subtree is the
empty digest; anything else is a branch. The root is a function of the entry
list, and an opening is one sibling per branch walked (about `log₂ n`).

* `tree n es` — the canonical root over entries carrying their remaining
  `n` path bits; `select p es` — the entries under prefix `p`.
* `climb` — the climb of a claimed terminal along the key's bits; `verify`.
* `climb_sound` / `verify_sound` — a verifying opening for `k` either reports
  exactly the entries under its prefix (so the answer is `lookup`), or exhibits
  a collision of the node digest (`Collision`: two different node inputs, one
  digest). No premise about the opening or the Store's rows.
* NOT proved here (cv task, see the KN2 index range): completeness of the honest
  opening, and the incremental insert's root equation. A wrong incremental root
  is caught by `store audit` (it rebuilds every stored node version); reads rely
  only on `verify_sound`.
-/
import Theory.AssertAxioms

namespace Minidregg.Theory.AuthTrie

set_option autoImplicit false

/-- What a node digest is computed from. -/
inductive NodeIn (K V D : Type) where
  | empty
  | leaf (k : K) (v : V)
  | branch (left right : D)
  deriving DecidableEq

/-- Where a key's walk ends. -/
inductive Terminal (K V : Type) where
  | empty
  | leaf (k : K) (v : V)
  deriving DecidableEq

section Generic

variable {K V D : Type} [DecidableEq K] [DecidableEq V] [DecidableEq D]
variable (dig : NodeIn K V D → D)

/-- An entry: its key, its REMAINING path bits, its value. -/
abbrev Entry (K V : Type) := K × List Bool × V

/-- The entries whose next bit is `b`, that bit removed. -/
def strip (b : Bool) (es : List (Entry K V)) : List (Entry K V) :=
  es.filterMap fun e =>
    match e.2.1 with
    | bit :: rest => if bit = b then some (e.1, rest, e.2.2) else none
    | [] => none

/-- The entries under a prefix. -/
def select : List Bool → List (Entry K V) → List (Entry K V)
  | [], es => es
  | b :: p, es => select p (strip b es)

def Terminal.input : Terminal K V → NodeIn K V D
  | .empty => .empty
  | .leaf k v => .leaf k v

/-- The canonical root over entries with `n` remaining bits. -/
def tree : Nat → List (Entry K V) → D
  | _, [] => dig .empty
  | _, [e] => dig (.leaf e.1 e.2.2)
  | 0, _ :: _ :: _ => dig .empty
  | n + 1, es@(_ :: _ :: _) => dig (.branch (tree n (strip false es)) (tree n (strip true es)))

/-- Climb a claimed terminal up along the walked bits (top bit first). -/
def climb : List Bool → List D → D → D
  | b :: bits, s :: siblings, below =>
      if b then dig (.branch s (climb bits siblings below))
      else dig (.branch (climb bits siblings below) s)
  | _, _, below => below

/-- Two different node inputs with one digest. -/
def Collision : Prop := ∃ a b : NodeIn K V D, a ≠ b ∧ dig a = dig b

/-- Entries are well formed at `n` remaining bits: every remaining path has
length `n`, and no two entries share one (keys are distinct as paths). -/
def WF (n : Nat) (es : List (Entry K V)) : Prop :=
  (∀ e ∈ es, e.2.1.length = n) ∧ (es.map fun e => e.2.1).Nodup

theorem strip_wf (n : Nat) (b : Bool) (es : List (Entry K V)) (wf : WF (n + 1) es) :
    WF n (strip b es) := by
  obtain ⟨lengths, nodup⟩ := wf
  induction es with
  | nil => exact ⟨by simp [strip], by simp [strip]⟩
  | cons e rest ih =>
      have restWf := ih (fun x hx => lengths x (List.mem_cons_of_mem _ hx)) (List.nodup_cons.mp nodup).2
      obtain ⟨k, bits, v⟩ := e
      have fresh := (List.nodup_cons.mp nodup).1
      cases bits with
      | nil => simp [strip, List.filterMap_cons] at restWf ⊢; exact restWf
      | cons bit tail =>
          by_cases same : bit = b
          · subst same
            have tailLen : tail.length = n := by
              have := lengths (k, bit :: tail, v) (List.mem_cons_self ..); simpa using this
            refine ⟨?_, ?_⟩
            · intro x hx
              simp only [strip, List.filterMap_cons, if_true] at hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact tailLen
              · exact restWf.1 x hx
            · simp only [strip, List.filterMap_cons, if_true, List.map_cons]
              refine List.nodup_cons.mpr ⟨?_, restWf.2⟩
              intro member
              obtain ⟨x, hx, eq⟩ := List.mem_map.mp member
              simp only [List.mem_filterMap] at hx
              obtain ⟨y, hy, hyx⟩ := hx
              obtain ⟨ky, by_, vy⟩ := y
              cases by_ with
              | nil => simp at hyx
              | cons b' t' =>
                  simp only at hyx
                  split at hyx
                  · rename_i same'
                    cases hyx
                    apply fresh
                    exact List.mem_map.mpr ⟨_, hy, by simp only [same', List.cons.injEq, true_and]; simpa using eq⟩
                  · cases hyx
          · simpa [strip, List.filterMap_cons, same] using restWf

/-- What a terminal at the end of a walk says about the entries under its prefix. -/
def Reports : Terminal K V → List (Entry K V) → Prop
  | .empty, es => es = []
  | .leaf k v, es => ∃ bits, es = [(k, bits, v)]

theorem tree_dig_terminal (n : Nat) (es : List (Entry K V)) (wf : WF n es) (t : Terminal K V)
    (equal : dig t.input = tree dig n es) : Reports t es ∨ Collision dig := by
  match n, es, wf, t with
  | _, [], _, .empty => exact Or.inl rfl
  | _, [], _, .leaf k v =>
      exact Or.inr ⟨.leaf k v, .empty, by simp, by simpa [Terminal.input, tree] using equal⟩
  | _, [e], _, .empty =>
      exact Or.inr ⟨.empty, .leaf e.1 e.2.2, by simp, by simpa [Terminal.input, tree] using equal⟩
  | _, [e], _, .leaf k v =>
      by_cases same : (NodeIn.leaf k v : NodeIn K V D) = .leaf e.1 e.2.2
      · simp only [NodeIn.leaf.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        exact Or.inl ⟨e.2.1, rfl⟩
      · exact Or.inr ⟨_, _, same, by simpa [Terminal.input, tree] using equal⟩
  | 0, a :: b :: rest, wf, t =>
      exfalso
      have la : a.2.1 = [] := List.eq_nil_of_length_eq_zero (wf.1 a (by simp))
      have lb : b.2.1 = [] := List.eq_nil_of_length_eq_zero (wf.1 b (by simp))
      have := (List.nodup_cons.mp wf.2).1
      exact this (List.mem_map.mpr ⟨b, by simp, by show b.2.1 = a.2.1; rw [la, lb]⟩)
  | m + 1, a :: b :: rest, _, t =>
      refine Or.inr ⟨t.input, .branch (tree dig m (strip false (a :: b :: rest)))
        (tree dig m (strip true (a :: b :: rest))), ?_, by simpa [tree] using equal⟩
      cases t <;> simp [Terminal.input]

/-- **Climb soundness.** A claimed terminal that climbs, along the query's
bits, to the canonical root reports exactly the entries under the walked
prefix — or a node collision is exhibited. -/
theorem climb_sound :
    ∀ (n : Nat) (es : List (Entry K V)) (bits : List Bool) (siblings : List D) (t : Terminal K V),
      WF n es → siblings.length ≤ bits.length → bits.length ≤ n →
      climb dig bits siblings (dig t.input) = tree dig n es →
      Reports t (select (bits.take siblings.length) es) ∨ Collision dig
  | n, es, bits, [], t, wf, _, _, climbed => by
      have : climb dig bits [] (dig t.input) = dig t.input := by cases bits <;> rfl
      rw [this] at climbed
      simpa [select] using tree_dig_terminal dig n es wf t climbed
  | n, es, [], s :: siblings, t, _, short, _, _ => by simp at short
  | n, es, b :: bits, s :: siblings, t, wf, short, long, climbed => by
      simp only [climb] at climbed
      match n, es, wf with
      | 0, es, _ => simp at long
      | m + 1, [], _ =>
          right
          cases b
          · exact ⟨.branch (climb dig bits siblings (dig t.input)) s, .empty, by simp,
              by simpa [tree] using climbed⟩
          · exact ⟨.branch s (climb dig bits siblings (dig t.input)), .empty, by simp,
              by simpa [tree] using climbed⟩
      | m + 1, [e], _ =>
          right
          cases b
          · exact ⟨.branch (climb dig bits siblings (dig t.input)) s, .leaf e.1 e.2.2, by simp,
              by simpa [tree] using climbed⟩
          · exact ⟨.branch s (climb dig bits siblings (dig t.input)), .leaf e.1 e.2.2, by simp,
              by simpa [tree] using climbed⟩
      | m + 1, a :: c :: rest, wf =>
          have rootEq : tree dig (m + 1) (a :: c :: rest) =
              dig (.branch (tree dig m (strip false (a :: c :: rest)))
                (tree dig m (strip true (a :: c :: rest)))) := by simp [tree]
          rw [rootEq] at climbed
          have short' : siblings.length ≤ bits.length := by simpa using short
          have long' : bits.length ≤ m := by simpa using long
          cases b with
          | false =>
              simp only [Bool.false_eq_true, if_false] at climbed
              by_cases same : (NodeIn.branch (climb dig bits siblings (dig t.input)) s : NodeIn K V D) =
                  .branch (tree dig m (strip false (a :: c :: rest))) (tree dig m (strip true (a :: c :: rest)))
              · simp only [NodeIn.branch.injEq] at same
                have ih := climb_sound m (strip false (a :: c :: rest)) bits siblings t
                  (strip_wf m false _ wf) short' long' same.1
                simpa [select] using ih
              · exact Or.inr ⟨_, _, same, climbed⟩
          | true =>
              simp only [if_true] at climbed
              by_cases same : (NodeIn.branch s (climb dig bits siblings (dig t.input)) : NodeIn K V D) =
                  .branch (tree dig m (strip false (a :: c :: rest))) (tree dig m (strip true (a :: c :: rest)))
              · simp only [NodeIn.branch.injEq] at same
                have ih := climb_sound m (strip true (a :: c :: rest)) bits siblings t
                  (strip_wf m true _ wf) short' long' same.2
                simpa [select] using ih
              · exact Or.inr ⟨_, _, same, climbed⟩

/-- Look a full key up in entries carrying their full paths. -/
def lookup (es : List (Entry K V)) (k : K) : Option V :=
  (es.find? fun e => e.1 = k).map (·.2.2)

/-- An opening: siblings from the root down, and the terminal. -/
structure Opening (K V D : Type) where
  siblings : List D
  terminal : Terminal K V

/-- **The verifier.** `bitsOf` gives every key its full path. -/
def verify (bitsOf : K → List Bool) (root : D) (k : K) (answer : Option V) (opening : Opening K V D) : Bool :=
  let depth := opening.siblings.length
  decide (depth ≤ (bitsOf k).length) &&
  (match opening.terminal, answer with
    | .empty, none => true
    | .leaf other value, some claimed => decide (other = k ∧ value = claimed)
    | .leaf other _, none => decide (other ≠ k ∧ (bitsOf other).take depth = (bitsOf k).take depth)
    | .empty, some _ => false) &&
  decide (climb dig ((bitsOf k).take depth) opening.siblings (dig opening.terminal.input) = root)

/-- Entries built from keys with their full paths. -/
def entries (bitsOf : K → List Bool) (kvs : List (K × V)) : List (Entry K V) :=
  kvs.map fun kv => (kv.1, bitsOf kv.1, kv.2)

theorem select_entries_mem (bitsOf : K → List Bool) :
    ∀ (p : List Bool) (es : List (Entry K V)) (e : Entry K V),
      e ∈ es → e.2.1.take p.length = p → ∃ e' ∈ select p es, e'.1 = e.1 ∧ e'.2.2 = e.2.2
  | [], es, e, mem, _ => ⟨e, mem, rfl, rfl⟩
  | b :: p, es, e, mem, pre => by
      obtain ⟨k, bits, v⟩ := e
      cases bits with
      | nil => simp at pre
      | cons bit rest =>
          simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at pre
          obtain ⟨rfl, pre⟩ := pre
          have inStrip : (k, rest, v) ∈ strip bit es := by
            simp only [strip, List.mem_filterMap]
            exact ⟨(k, bit :: rest, v), mem, by simp⟩
          exact select_entries_mem bitsOf p (strip bit es) (k, rest, v) inStrip pre

/-- **Soundness at a fixed path length.** If the entries are the key/value
pairs `kvs` at their full paths (length `L`, injective on keys), an opening
that verifies against the canonical root answers `lookup` — or a node
collision is exhibited. -/
theorem verify_sound (bitsOf : K → List Bool) (L : Nat) (lengths : ∀ k, (bitsOf k).length = L)
    (kvs : List (K × V)) (wf : WF L (entries bitsOf kvs))
    (k : K) (answer : Option V) (opening : Opening K V D)
    (accepted : verify dig bitsOf (tree dig L (entries bitsOf kvs)) k answer opening = true) :
    answer = lookup (entries bitsOf kvs) k ∨ Collision dig := by
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨short, consistent⟩, climbed⟩ := accepted
  have reports := climb_sound dig L (entries bitsOf kvs) ((bitsOf k).take opening.siblings.length)
    opening.siblings opening.terminal wf (by simp [short])
    (by rw [List.length_take, lengths]; exact Nat.min_le_right _ _) climbed
  rcases reports with reports | collision
  · left
    have takeLen : ((bitsOf k).take opening.siblings.length).take opening.siblings.length =
        (bitsOf k).take opening.siblings.length := by rw [List.take_take, Nat.min_self]
    rw [takeLen] at reports
    -- every entry with k's prefix is under the walked prefix
    have under : ∀ e ∈ entries bitsOf kvs, e.1 = k →
        ∃ e' ∈ select ((bitsOf k).take opening.siblings.length) (entries bitsOf kvs),
          e'.1 = e.1 ∧ e'.2.2 = e.2.2 := by
      intro e he hk
      apply select_entries_mem bitsOf _ _ e he
      obtain ⟨kv, _, rfl⟩ := List.mem_map.mp he
      simp only at hk ⊢
      rw [hk, List.length_take, Nat.min_eq_left short]
    cases hterm : opening.terminal with
    | empty =>
        rw [hterm] at reports consistent
        cases answer with
        | some _ => simp at consistent
        | none =>
            simp only [Reports] at reports
            symm
            simp only [lookup, Option.map_eq_none_iff, List.find?_eq_none]
            intro e he hk
            obtain ⟨e', he', _⟩ := under e he (by simpa using hk)
            rw [reports] at he'
            cases he'
    | leaf other value =>
        rw [hterm] at reports consistent
        obtain ⟨rest, only⟩ := reports
        cases answer with
        | some claimed =>
            simp at consistent
            obtain ⟨hother, hvalue⟩ := consistent
            subst hvalue
            rw [hother] at only
            -- the only entry under the prefix is (k, value)
            have found : ∃ e ∈ entries bitsOf kvs, e.1 = k ∧ e.2.2 = value := by
              have : (k, rest, value) ∈ select ((bitsOf k).take opening.siblings.length)
                  (entries bitsOf kvs) := by rw [only]; simp
              exact select_mem_origin _ _ _ this
            obtain ⟨e, he, hk, hv⟩ := found
            simp only [lookup]
            cases hfind : (entries bitsOf kvs).find? (fun e => e.1 = k) with
            | none =>
                rw [List.find?_eq_none] at hfind
                exact absurd (by simpa using hk) (hfind e he)
            | some f =>
                have hf := List.find?_some hfind
                have fmem := List.mem_of_find?_eq_some hfind
                obtain ⟨f', hf', hk', hv'⟩ := under f fmem (by simpa using hf)
                rw [only] at hf'
                simp only [List.mem_singleton] at hf'
                subst hf'
                simp only [Option.map_some, Option.some.injEq]
                simpa using hv'
        | none =>
            simp at consistent
            obtain ⟨differs, _⟩ := consistent
            symm
            simp only [lookup, Option.map_eq_none_iff, List.find?_eq_none]
            intro e he hk
            obtain ⟨e', he', hk', _⟩ := under e he (by simpa using hk)
            rw [only] at he'
            simp only [List.mem_singleton] at he'
            subst he'
            exact differs (by simpa using hk'.trans (by simpa using hk))
  · exact Or.inr collision
where
  /-- An entry under a prefix came from an entry of the list with the same key and value. -/
  select_mem_origin : ∀ (p : List Bool) (es : List (Entry K V)) (e : Entry K V),
      e ∈ select p es → ∃ e' ∈ es, e'.1 = e.1 ∧ e'.2.2 = e.2.2
    | [], es, e, mem => ⟨e, mem, rfl, rfl⟩
    | b :: p, es, e, mem => by
        obtain ⟨e1, he1, hk1, hv1⟩ := select_mem_origin p (strip b es) e mem
        simp only [strip, List.mem_filterMap] at he1
        obtain ⟨e0, he0, h0⟩ := he1
        obtain ⟨k0, bits0, v0⟩ := e0
        cases bits0 with
        | nil => simp at h0
        | cons bit rest =>
            simp only at h0
            split at h0
            · cases h0; exact ⟨_, he0, hk1, hv1⟩
            · cases h0

end Generic

/-! ## Decided poles: 3-bit keys, a toy injective digest -/

namespace Poles

/-- Keys are their own 3-bit paths. -/
def bitsOf (k : List Bool) : List Bool := k

/-- An injective rendering standing in for the node hash. -/
def toy : NodeIn (List Bool) Nat String → String
  | .empty => "E"
  | .leaf k v => s!"L({k},{v})"
  | .branch l r => s!"B({l},{r})"

def kvs : List (List Bool × Nat) := [([false, false, true], 7), ([false, true, true], 9), ([true, true, false], 3)]

def root : String := tree toy 3 (entries bitsOf kvs)

/-- The honest absence opening of `[false, false, false]`: it shares its first two bits with key 1. -/
def absentOpening : Opening (List Bool) Nat String :=
  ⟨[tree toy 2 (strip true (entries bitsOf kvs)), tree toy 1 (strip true (strip false (entries bitsOf kvs)))],
    .leaf [false, false, true] 7⟩

theorem absent_verified : verify toy bitsOf root [false, false, false] none absentOpening = true := by decide
theorem absent_claimed_present_refused :
    verify toy bitsOf root [false, false, false] (some 7) absentOpening = false := by decide
theorem present_verified :
    verify toy bitsOf root [false, false, true] (some 7) absentOpening = true := by decide
theorem present_wrong_value_refused :
    verify toy bitsOf root [false, false, true] (some 8) absentOpening = false := by decide

end Poles

#assert_axioms strip_wf
#assert_axioms tree_dig_terminal
#assert_axioms climb_sound
#assert_axioms verify_sound
#assert_axioms Poles.absent_verified
#assert_axioms Poles.absent_claimed_present_refused
#assert_axioms Poles.present_verified
#assert_axioms Poles.present_wrong_value_refused

end Minidregg.Theory.AuthTrie
