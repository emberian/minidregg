/-
# Theory.LogAccumulator — a Merkle mountain range over log heights

The durable log keeps an append-only accumulator so that ONE record can be
authenticated without the rest of the history: its leaf, a path of at most
`log₂ n` sibling nodes read from the Store, and the authenticated frontier
(`Compiler.DurableHistory`, KN2-STORE-OPEN).

* `block node leaf k e` — the digest of the perfect tree over the `2^k` leaves
  ending at height `e` (1-based): the specification of every stored node.
* A **frontier** is a list of peaks `(k, digest)`, newest (rightmost) first;
  `push` appends one leaf and merges equal-size peaks. `Honest leaf n f`: the
  peaks of `f` are the blocks that tile `1..n` from the right.
* `locate` finds the peak covering height `j`; `rootOfPath` climbs from a
  claimed leaf with sibling nodes looked up by `(level, end)`; `verify` is the
  check a read runs.

Theorems:
* `push_honest`, `frontierOf_honest` — the incremental frontier is the
  specification after every append (no alignment premise is needed);
* `verify_complete` — honest frontier and honest nodes: every height verifies
  (the satisfying pole, for every `n` and `j`);
* `verify_sound` — under an honest frontier, a claimed leaf that verifies with
  ANY nodes is the honest leaf, or the run exhibits a collision of `node`
  (two different child pairs, one digest). No premise about the nodes;
* decided poles over a toy injective pairing: honest accepted; a tampered leaf
  at height 2 of 5 refused; a tampered sibling node refused.
-/
import Theory.AssertAxioms

namespace Minidregg.Theory.LogAccumulator

set_option autoImplicit false

section Generic

variable {D : Type} (node : D → D → D) (leaf : Nat → D)

/-- The perfect tree over the `2^k` leaves ending at `e`: left child ends at
`e - 2^k`, right child at `e`. -/
def block : Nat → Nat → D
  | 0, e => leaf e
  | k + 1, e => node (block k (e - 2 ^ k)) (block k e)

/-- Append a peak of size `2^k`, merging while the newest peak has the same size. -/
def push : List (Nat × D) → Nat → D → List (Nat × D)
  | [], k, r => [(k, r)]
  | (k', l) :: rest, k, r =>
      if k' = k then push rest (k + 1) (node l r) else (k, r) :: (k', l) :: rest

/-- The peaks of `f` are the blocks tiling `1..n` from the right, newest first. -/
def Honest : Nat → List (Nat × D) → Prop
  | n, [] => n = 0
  | n, (k, d) :: rest => 2 ^ k ≤ n ∧ d = block node leaf k n ∧ Honest (n - 2 ^ k) rest

/-- The frontier after leaves `1..n`, by `n` single-leaf pushes. -/
def frontierOf : Nat → List (Nat × D)
  | 0 => []
  | n + 1 => push node (frontierOf n) 0 (leaf (n + 1))

theorem push_honest :
    ∀ (f : List (Nat × D)) (m k : Nat), Honest node leaf m f →
      Honest node leaf (m + 2 ^ k) (push node f k (block node leaf k (m + 2 ^ k)))
  | [], m, k, honest => by
      have : m = 0 := honest
      subst this
      simp [push, Honest]
  | (k', l) :: rest, m, k, honest => by
      obtain ⟨fits, isBlock, restHonest⟩ := honest
      unfold push
      split
      · rename_i same
        subst same
        have merged : node l (block node leaf k' (m + 2 ^ k')) = block node leaf (k' + 1) (m + 2 ^ k') := by
          rw [isBlock]
          simp [block]
        rw [merged]
        have arith : m - 2 ^ k' + 2 ^ (k' + 1) = m + 2 ^ k' := by
          rw [Nat.pow_succ]; omega
        have := push_honest rest (m - 2 ^ k') (k' + 1) restHonest
        rw [arith] at this
        exact this
      · refine ⟨Nat.le_add_left _ _, rfl, ?_⟩
        rw [Nat.add_sub_cancel]
        exact ⟨fits, isBlock, restHonest⟩

theorem frontierOf_honest : ∀ n, Honest node leaf n (frontierOf node leaf n)
  | 0 => rfl
  | n + 1 => by
      have := push_honest node leaf (frontierOf node leaf n) n 0 (frontierOf_honest n)
      simpa [frontierOf, block] using this

/-- The peak covering height `j`: its size exponent, end and digest. -/
def locate (j : Nat) : Nat → List (Nat × D) → Option (Nat × Nat × D)
  | _, [] => none
  | e, (k, d) :: rest => if e - 2 ^ k < j ∧ j ≤ e then some (k, e, d) else locate j (e - 2 ^ k) rest

/-- Climb from the claimed leaf of `j` to the block `(k, e)`, reading each
sibling by `(level, end)`. `none` when a sibling is missing. -/
def rootOfPath (claimed : D) (nodes : Nat → Nat → Option D) (j : Nat) : Nat → Nat → Option D
  | 0, _ => some claimed
  | k + 1, e =>
      if j ≤ e - 2 ^ k then do
        let left ← rootOfPath claimed nodes j k (e - 2 ^ k)
        let right ← nodes k e
        pure (node left right)
      else do
        let left ← nodes k (e - 2 ^ k)
        let right ← rootOfPath claimed nodes j k e
        pure (node left right)

/-- The sibling keys `(level, end)` a read of `j` inside block `(k, e)` needs. -/
def pathKeys (j : Nat) : Nat → Nat → List (Nat × Nat)
  | 0, _ => []
  | k + 1, e =>
      if j ≤ e - 2 ^ k then (k, e) :: pathKeys j k (e - 2 ^ k)
      else (k, e - 2 ^ k) :: pathKeys j k e

/-- **The inclusion check a read runs.** -/
def verify [DecidableEq D] (frontier : List (Nat × D)) (n j : Nat) (claimed : D)
    (nodes : Nat → Nat → Option D) : Bool :=
  match locate j n frontier with
  | none => false
  | some (k, e, d) => rootOfPath node claimed nodes j k e == some d

theorem locate_honest (j : Nat) (pos : 1 ≤ j) :
    ∀ (f : List (Nat × D)) (n : Nat), Honest node leaf n f → j ≤ n →
      ∃ k e d, locate j n f = some (k, e, d) ∧ d = block node leaf k e ∧ e - 2 ^ k < j ∧ j ≤ e
  | [], n, honest, within => by
      have : n = 0 := honest
      omega
  | (k, d) :: rest, n, honest, within => by
      obtain ⟨fits, isBlock, restHonest⟩ := honest
      unfold locate
      split
      · rename_i inside
        exact ⟨k, n, d, rfl, isBlock, inside.1, inside.2⟩
      · rename_i outside
        exact locate_honest j pos rest (n - 2 ^ k) restHonest (by omega)

theorem rootOfPath_honest (j : Nat) (nodes : Nat → Nat → Option D)
    (honestNodes : ∀ k e, nodes k e = some (block node leaf k e)) :
    ∀ k e, e - 2 ^ k < j → j ≤ e →
      rootOfPath node (leaf j) nodes j k e = some (block node leaf k e)
  | 0, e, low, high => by
      have : j = e := by simp at low; omega
      subst this
      rfl
  | k + 1, e, low, high => by
      have pow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      unfold rootOfPath
      split
      · rename_i left
        rw [rootOfPath_honest j nodes honestNodes k (e - 2 ^ k) (by omega) left, honestNodes]
        rfl
      · rename_i right
        rw [honestNodes, rootOfPath_honest j nodes honestNodes k e (by omega) high]
        rfl

/-- **Completeness**: an honest frontier and honest nodes verify every height. -/
theorem verify_complete [DecidableEq D] (n j : Nat) (pos : 1 ≤ j) (within : j ≤ n)
    (frontier : List (Nat × D)) (honest : Honest node leaf n frontier)
    (nodes : Nat → Nat → Option D) (honestNodes : ∀ k e, nodes k e = some (block node leaf k e)) :
    verify node frontier n j (leaf j) nodes = true := by
  obtain ⟨k, e, d, found, isBlock, low, high⟩ := locate_honest node leaf j pos frontier n honest within
  unfold verify
  simp only [found]
  rw [rootOfPath_honest node leaf j nodes honestNodes k e low high, isBlock]
  simp

/-- Two different child pairs with one parent digest. -/
def NodeCollision : Prop := ∃ a b c d : D, (a, b) ≠ (c, d) ∧ node a b = node c d

theorem rootOfPath_sound (j : Nat) (claimed : D) (nodes : Nat → Nat → Option D) :
    ∀ k e, e - 2 ^ k < j → j ≤ e →
      rootOfPath node claimed nodes j k e = some (block node leaf k e) →
      claimed = leaf j ∨ NodeCollision node
  | 0, e, low, high, climbed => by
      have : j = e := by simp at low; omega
      subst this
      left
      simpa [rootOfPath, block] using climbed
  | k + 1, e, low, high, climbed => by
      have pow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      unfold rootOfPath at climbed
      split at climbed
      · rename_i left
        cases sub : rootOfPath node claimed nodes j k (e - 2 ^ k) with
        | none => simp [sub] at climbed
        | some l =>
            cases sib : nodes k e with
            | none => simp [sub, sib] at climbed
            | some r =>
                simp only [sub, sib, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                  Option.some.injEq, block] at climbed
                by_cases same : (l, r) = (block node leaf k (e - 2 ^ k), block node leaf k e)
                · simp only [Prod.mk.injEq] at same
                  rw [same.1] at sub
                  exact rootOfPath_sound j claimed nodes k (e - 2 ^ k) (by omega) left sub
                · exact Or.inr ⟨_, _, _, _, same, climbed⟩
      · rename_i right
        cases sib : nodes k (e - 2 ^ k) with
        | none => simp [sib] at climbed
        | some l =>
            cases sub : rootOfPath node claimed nodes j k e with
            | none => simp [sub, sib] at climbed
            | some r =>
                simp only [sub, sib, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                  Option.some.injEq, block] at climbed
                by_cases same : (l, r) = (block node leaf k (e - 2 ^ k), block node leaf k e)
                · simp only [Prod.mk.injEq] at same
                  rw [same.2] at sub
                  exact rootOfPath_sound j claimed nodes k e (by omega) high sub
                · exact Or.inr ⟨_, _, _, _, same, climbed⟩

/-- **Soundness**: under an honest frontier, a claimed leaf that verifies with
ANY sibling nodes is the honest leaf of `j`, or the run exhibits a collision
of `node`. The nodes are untrusted Store bytes; only the frontier is trusted. -/
theorem verify_sound [DecidableEq D] (n j : Nat) (pos : 1 ≤ j) (within : j ≤ n)
    (frontier : List (Nat × D)) (honest : Honest node leaf n frontier)
    (claimed : D) (nodes : Nat → Nat → Option D)
    (accepted : verify node frontier n j claimed nodes = true) :
    claimed = leaf j ∨ NodeCollision node := by
  obtain ⟨k, e, d, found, isBlock, low, high⟩ := locate_honest node leaf j pos frontier n honest within
  unfold verify at accepted
  rw [found] at accepted
  have climbed : rootOfPath node claimed nodes j k e = some (block node leaf k e) := by
    rw [← isBlock]; simpa using accepted
  exact rootOfPath_sound node leaf j claimed nodes k e low high climbed

/-- Every sibling a read of `j` needs is a stored block `(level, end)` with
`end ≤ n`: nodes come from the Store's settled prefix only. -/
theorem pathKeys_within (j : Nat) :
    ∀ k e (key : Nat × Nat), key ∈ pathKeys j k e → key.2 ≤ e
  | 0, _, _, member => by simp [pathKeys] at member
  | k + 1, e, key, member => by
      unfold pathKeys at member
      split at member
      · rcases List.mem_cons.mp member with rfl | rest
        · exact Nat.le_refl _
        · exact Nat.le_trans (pathKeys_within j k (e - 2 ^ k) key rest) (Nat.sub_le _ _)
      · rcases List.mem_cons.mp member with rfl | rest
        · exact Nat.sub_le _ _
        · exact pathKeys_within j k e key rest

end Generic

/-! ## Decided poles: five leaves, an injective toy pairing -/

namespace Poles

/-- Cantor pairing, shifted: injective, so no `NodeCollision` exists here. -/
def toyNode (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b + 1

def toyLeaf (h : Nat) : Nat := 10 * h

def five : List (Nat × Nat) := frontierOf toyNode toyLeaf 5

def honestNodes (k e : Nat) : Option Nat := some (block toyNode toyLeaf k e)

/-- The node at (level 0, end 1) — the sibling height 2 climbs past — rewritten. -/
def tamperedNodes (k e : Nat) : Option Nat :=
  if k = 0 ∧ e = 1 then some 7 else honestNodes k e

theorem honest_height_two_accepted :
    verify toyNode five 5 2 (toyLeaf 2) honestNodes = true := by decide

theorem tampered_record_height_two_refused :
    verify toyNode five 5 2 (toyLeaf 2 + 1) honestNodes = false := by decide

theorem tampered_node_refused :
    verify toyNode five 5 2 (toyLeaf 2) tamperedNodes = false := by decide

theorem head_accepted : verify toyNode five 5 5 (toyLeaf 5) honestNodes = true := by decide

theorem beyond_head_refused : verify toyNode five 5 6 (toyLeaf 6) honestNodes = false := by decide

end Poles

#assert_axioms push_honest
#assert_axioms frontierOf_honest
#assert_axioms locate_honest
#assert_axioms rootOfPath_honest
#assert_axioms verify_complete
#assert_axioms rootOfPath_sound
#assert_axioms verify_sound
#assert_axioms pathKeys_within
#assert_axioms Poles.honest_height_two_accepted
#assert_axioms Poles.tampered_record_height_two_refused
#assert_axioms Poles.tampered_node_refused
#assert_axioms Poles.head_accepted
#assert_axioms Poles.beyond_head_refused

end Minidregg.Theory.LogAccumulator
