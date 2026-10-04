/-
# Compiler.DurableLogTags — every stored log tag is read

Entry `h` of the durable log carries `entryTag key h chainₕ rootₕ` (the root after
entry `h`, kept at append, then the MAC binding it)
(`Compiler.DurableCheckpointCodec`). Open (`DurableReceiverIO.load`) and the
live extension (`DurableReceiverIO.extendFrom`) verify the tag of EVERY entry
they read against the chain prefix at its height, and refuse the first one
that differs by name and height. Before this module only the head entry's tag
was compared, so a flipped tag below the head opened and passed `audit`.

`firstBadTag` is the pure verifier, generic in the tag function and the chain
type so the decided poles below run on small concrete values; `verifyTags` is
it at `entryTag key` over `chainPrefixes`, the chain values the open path
already computes for the checkpoint check (no second chain pass).
-/
import Compiler.DurableCheckpointCodec
import Theory.AssertAxioms

namespace Minidregg.Compiler.DurableLogTags

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler.DurableCheckpointCodec

set_option autoImplicit false

/-! ## The generic verifier -/

section Generic

variable {D T : Type} [DecidableEq T]

/-- `chains` is the chain before the first entry followed by the chain after
each entry; entry `i` (0-based) sits at `height + i + 1`. The first entry
whose tag differs — or that has no chain value — is named by its height. -/
def firstBadTag (tag : Nat → D → T) : Nat → List D → List T → Option Nat
  | _, _, [] => none
  | height, _ :: next :: chains, stored :: tags =>
      if stored = tag (height + 1) next then firstBadTag tag (height + 1) (next :: chains) tags
      else some (height + 1)
  | height, _, _ :: _ => some (height + 1)

/-- Every tag is the tag of its height and its chain value. -/
def TagsHonest (tag : Nat → D → T) (height : Nat) (chains : List D) (tags : List T) : Prop :=
  ∀ i (hi : i < tags.length), ∃ chain, chains[i + 1]? = some chain ∧
    tags[i] = tag (height + i + 1) chain

theorem firstBadTag_eq_none_iff (tag : Nat → D → T) :
    ∀ (height : Nat) (chains : List D) (tags : List T),
      firstBadTag tag height chains tags = none ↔ TagsHonest tag height chains tags
  | height, chains, [] => by simp [firstBadTag, TagsHonest]
  | height, [], stored :: tags => by
      simp only [firstBadTag, reduceCtorEq, false_iff, TagsHonest]
      intro all
      obtain ⟨_, none, _⟩ := all 0 (by simp)
      simp at none
  | height, [_], stored :: tags => by
      simp only [firstBadTag, reduceCtorEq, false_iff, TagsHonest]
      intro all
      obtain ⟨_, none, _⟩ := all 0 (by simp)
      simp at none
  | height, previous :: next :: chains, stored :: tags => by
      have rest := firstBadTag_eq_none_iff tag (height + 1) (next :: chains) tags
      simp only [firstBadTag]
      split
      · rename_i good
        rw [rest]
        constructor
        · intro honest i hi
          cases i with
          | zero => exact ⟨next, by simp, by simpa using good⟩
          | succ i =>
              obtain ⟨chain, at_, eq⟩ := honest i (by simpa using hi)
              exact ⟨chain, by simpa using at_, by simpa [Nat.add_assoc, Nat.add_comm 1] using eq⟩
        · intro honest i hi
          obtain ⟨chain, at_, eq⟩ := honest (i + 1) (by simpa using hi)
          exact ⟨chain, by simpa using at_, by
            simpa [Nat.add_assoc, Nat.add_comm 1, Nat.add_left_comm] using eq⟩
      · rename_i bad
        simp only [reduceCtorEq, false_iff, TagsHonest]
        intro honest
        obtain ⟨chain, at_, eq⟩ := honest 0 (by simp)
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at at_
        subst at_
        exact bad (by simpa using eq)

/-- **The first wrong tag is named**: honest entries before it, whatever after. -/
theorem firstBadTag_names_first (tag : Nat → D → T) :
    ∀ (height : Nat) (chains : List D) (pre post : List T) (stored : T) (chain : D),
      TagsHonest tag height chains pre →
      chains[pre.length + 1]? = some chain →
      stored ≠ tag (height + pre.length + 1) chain →
      firstBadTag tag height chains (pre ++ stored :: post) = some (height + pre.length + 1)
  | height, [], [], post, stored, chain, _, at_, _ => by simp at at_
  | height, [_], [], post, stored, chain, _, at_, _ => by simp at at_
  | height, previous :: next :: chains, [], post, stored, chain, _, at_, bad => by
      simp only [List.length_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at at_
      subst at_
      simp only [List.length_nil, Nat.add_zero] at bad
      simp [firstBadTag, bad]
  | height, [], first :: pre, post, stored, chain, honest, _, _ => by
      obtain ⟨_, none, _⟩ := honest 0 (by simp); simp at none
  | height, [_], first :: pre, post, stored, chain, honest, _, _ => by
      obtain ⟨_, none, _⟩ := honest 0 (by simp); simp at none
  | height, previous :: next :: chains, first :: pre, post, stored, chain, honest, at_, bad => by
      obtain ⟨c0, at0, eq0⟩ := honest 0 (by simp)
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at at0
      subst at0
      have tail : TagsHonest tag (height + 1) (next :: chains) pre := by
        intro i hi
        obtain ⟨c, atc, eqc⟩ := honest (i + 1) (by simpa using hi)
        exact ⟨c, by simpa using atc, by
          simpa [Nat.add_assoc, Nat.add_comm 1, Nat.add_left_comm] using eqc⟩
      have step := firstBadTag_names_first tag (height + 1) (next :: chains) pre post stored chain
        tail (by simpa using at_) (by simpa [Nat.add_assoc, Nat.add_comm 1] using bad)
      simp only [List.cons_append, firstBadTag]
      rw [if_pos (by simpa using eq0), step]
      simp [Nat.add_assoc, Nat.add_comm 1]

end Generic

/-! ## The chain prefixes -/

/-- Chain values before and after each record: element `i` is the chain after `i` records. -/
def chainPrefixes (start : Digest) (records : List IntentRecord) : List Digest :=
  records.scanl chainStep start

theorem chainPrefixes_getElem? (start : Digest) :
    ∀ (records : List IntentRecord) (i : Nat), i ≤ records.length →
      (chainPrefixes start records)[i]? = some (chainAfter start (records.take i))
  | [], i, within => by
      have : i = 0 := by simpa using within
      subst this; simp [chainPrefixes, chainAfter]
  | record :: records, 0, _ => by simp [chainPrefixes, chainAfter]
  | record :: records, i + 1, within => by
      have rest := chainPrefixes_getElem? (chainStep start record) records i (by simpa using within)
      simpa [chainPrefixes, chainAfter, List.scanl_cons] using rest

/-- The last prefix is the head chain, so `load` hashes the log once, not twice. -/
theorem chainPrefixes_getLast? (start : Digest) (records : List IntentRecord) :
    (chainPrefixes start records).getLast?.getD start = chainAfter start records := by
  have len : (chainPrefixes start records).length = records.length + 1 := by
    simp [chainPrefixes]
  rw [List.getLast?_eq_getElem?, len, Nat.add_sub_cancel,
    chainPrefixes_getElem? start records records.length (Nat.le_refl _)]
  simp

/-! ## The deployed verifier -/

def tagRefusal (height : Nat) : String :=
  s!"durable log entry tag refused at height {height}"

/-- Generic in the tag function so the poles below decide without a KMAC. -/
def verifyTagsWith {D T : Type} [DecidableEq T] (tag : Nat → D → T) (height : Nat)
    (chains : List D) (tags : List T) : Except String Unit :=
  match firstBadTag tag height chains tags with
  | none => .ok ()
  | some bad => .error (tagRefusal bad)

/-- Each chain value beside the root the stored tag after it carries: element
`i + 1` is (the chain after entry `i + 1`, the root stored tag `i` carries).
Element `0` (the chain before the first entry) carries no tag. -/
def rootedChains (chains : List Digest) (tags : List (List UInt8)) : List (Digest × Digest) :=
  match chains with
  | [] => []
  | first :: rest => (first, ⟨0⟩) :: rest.zipWith (fun chain tag => (chain, (tagRoot tag).getD ⟨0⟩)) tags

/-- The deployed tag of a height at a (chain, root) pair. -/
def rootedTag (key : MacKey) (height : Nat) (point : Digest × Digest) : List UInt8 :=
  entryTag key height point.1 point.2

/-- Every stored tag, the first entry at `height + 1`, against `chains`
(`chainPrefixes` from the chain at `height`) and the root it carries. -/
def verifyTags (key : MacKey) (height : Nat) (chains : List Digest) (tags : List (List UInt8)) :
    Except String Unit :=
  verifyTagsWith (rootedTag key) height (rootedChains chains tags) tags

theorem rootedChains_getElem? (chains : List Digest) (tags : List (List UInt8)) (i : Nat)
    (tag : List UInt8) (stored : tags[i]? = some tag) :
    (rootedChains chains tags)[i + 1]? =
      chains[i + 1]?.map fun chain => (chain, (tagRoot tag).getD ⟨0⟩) := by
  cases chains with
  | nil => simp [rootedChains]
  | cons first rest =>
      simp only [rootedChains, List.getElem?_cons_succ, List.getElem?_zipWith, stored]
      cases rest[i]? <;> rfl

/-- **The stored check is read**: the verifier accepts exactly the stores whose
every tag is the MAC of its height, the chain after the records up to it, and
the root it carries. -/
theorem verifyTags_ok_iff (key : MacKey) (height : Nat) (start : Digest)
    (records : List IntentRecord) (tags : List (List UInt8)) (lengths : tags.length ≤ records.length) :
    verifyTags key height (chainPrefixes start records) tags = .ok () ↔
      ∀ i (hi : i < tags.length), ∃ root,
        tags[i] = entryTag key (height + i + 1) (chainAfter start (records.take (i + 1))) root := by
  have none_iff := firstBadTag_eq_none_iff (rootedTag key) height
    (rootedChains (chainPrefixes start records) tags) tags
  have pointAt : ∀ i (hi : i < tags.length),
      (rootedChains (chainPrefixes start records) tags)[i + 1]? =
        some (chainAfter start (records.take (i + 1)), (tagRoot tags[i]).getD ⟨0⟩) := by
    intro i hi
    rw [rootedChains_getElem? _ tags i tags[i] (List.getElem?_eq_getElem hi),
      chainPrefixes_getElem? start records (i + 1) (by omega)]
    rfl
  constructor
  · intro accepted i hi
    have : firstBadTag (rootedTag key) height (rootedChains (chainPrefixes start records) tags)
        tags = none := by
      unfold verifyTags verifyTagsWith at accepted
      split at accepted
      · assumption
      · cases accepted
    obtain ⟨point, at_, eq⟩ := none_iff.mp this i hi
    rw [pointAt i hi] at at_
    cases at_
    exact ⟨_, eq⟩
  · intro honest
    have : firstBadTag (rootedTag key) height (rootedChains (chainPrefixes start records) tags)
        tags = none :=
      none_iff.mpr fun i hi => by
        obtain ⟨root, eq⟩ := honest i hi
        refine ⟨_, pointAt i hi, ?_⟩
        unfold rootedTag
        rw [eq, tagRoot_entryTag]
        rfl
    simp [verifyTags, verifyTagsWith, this]

/-- **A wrong tag at any height refuses, naming that height** — the first wrong
one, whatever root it claims; the entries after it do not matter. -/
theorem verifyTags_refuses_at (key : MacKey) (height : Nat) (start : Digest)
    (records : List IntentRecord) (pre post : List (List UInt8)) (stored : List UInt8)
    (within : pre.length < records.length)
    (honest : ∀ i (hi : i < pre.length), ∃ root,
      pre[i] = entryTag key (height + i + 1) (chainAfter start (records.take (i + 1))) root)
    (bad : ∀ root, stored ≠ entryTag key (height + pre.length + 1)
      (chainAfter start (records.take (pre.length + 1))) root) :
    verifyTags key height (chainPrefixes start records) (pre ++ stored :: post) =
      .error (tagRefusal (height + pre.length + 1)) := by
  let tags := pre ++ stored :: post
  have pointAt : ∀ i (hi : i < tags.length) (hr : i < records.length),
      (rootedChains (chainPrefixes start records) tags)[i + 1]? =
        some (chainAfter start (records.take (i + 1)), (tagRoot tags[i]).getD ⟨0⟩) := by
    intro i hi hr
    rw [rootedChains_getElem? _ tags i tags[i] (List.getElem?_eq_getElem hi),
      chainPrefixes_getElem? start records (i + 1) (by omega)]
    rfl
  have named := firstBadTag_names_first (rootedTag key) height
    (rootedChains (chainPrefixes start records) tags) pre post stored _
    (fun i hi => by
      obtain ⟨root, eq⟩ := honest i hi
      have hi' : i < tags.length := by simp [tags]; omega
      refine ⟨_, pointAt i hi' (by omega), ?_⟩
      have same : tags[i] = pre[i] := by simp [tags, List.getElem_append_left hi]
      unfold rootedTag
      rw [same, eq, tagRoot_entryTag]
      rfl)
    (pointAt pre.length (by simp [tags]) within)
    (by
      have same : tags[pre.length]'(by simp [tags]) = stored := by simp [tags]
      unfold rootedTag
      simp only [same]
      exact bad _)
  simp [verifyTags, verifyTagsWith, tags, named]

/-- **The head is no exception**: a wrong last tag refuses at the head's height. -/
theorem verifyTags_refuses_head (key : MacKey) (height : Nat) (start : Digest)
    (records : List IntentRecord) (pre : List (List UInt8)) (stored : List UInt8)
    (exact : pre.length + 1 = records.length)
    (honest : ∀ i (hi : i < pre.length), ∃ root,
      pre[i] = entryTag key (height + i + 1) (chainAfter start (records.take (i + 1))) root)
    (bad : ∀ root, stored ≠ entryTag key (height + records.length) (chainAfter start records) root) :
    verifyTags key height (chainPrefixes start records) (pre ++ [stored]) =
      .error (tagRefusal (height + records.length)) := by
  have := verifyTags_refuses_at key height start records pre [] stored (by omega) honest
    (by
      intro root
      rw [exact, List.take_of_length_le (by omega), Nat.add_assoc, exact]
      exact bad root)
  rw [this, ← exact, Nat.add_assoc]

/-- **Every verified root is bound**: a store the verifier accepts carries, at
each height, exactly the root its tag was sealed with — the root a historical
receipt reads (`DurableReceiverIO.Loaded.rootLog`). -/
theorem verifyTags_root (key : MacKey) (height : Nat) (start : Digest)
    (records : List IntentRecord) (tags : List (List UInt8)) (lengths : tags.length ≤ records.length)
    (accepted : verifyTags key height (chainPrefixes start records) tags = .ok ())
    (i : Nat) (hi : i < tags.length) :
    tags[i] = entryTag key (height + i + 1) (chainAfter start (records.take (i + 1)))
      ((tagRoot tags[i]).getD ⟨0⟩) := by
  obtain ⟨root, eq⟩ := (verifyTags_ok_iff key height start records tags lengths).mp accepted i hi
  rw [eq, tagRoot_entryTag]
  rfl

/-! ## Decided poles: three records, tag = (height, chain), chain = running sum -/

/-- The toy tag, so the poles decide without evaluating a KMAC. -/
def poleTag (height chain : Nat) : Nat × Nat := (height, chain)

/-- Chains before and after records 1, 2, 3 (running sum from 0). -/
def poleChains : List Nat := [1, 2, 3].scanl (· + ·) 0

theorem pole_honest_accepted :
    verifyTagsWith poleTag 0 poleChains [(1, 1), (2, 3), (3, 6)] = .ok () := by decide

theorem pole_middle_refused :
    verifyTagsWith poleTag 0 poleChains [(1, 1), (2, 2), (3, 6)] = .error (tagRefusal 2) := by
  decide

theorem pole_head_refused :
    verifyTagsWith poleTag 0 poleChains [(1, 1), (2, 3), (3, 7)] = .error (tagRefusal 3) := by
  decide

theorem pole_base_height_named :
    verifyTagsWith poleTag 40 poleChains [(41, 1), (43, 3), (43, 6)] = .error (tagRefusal 42) := by
  decide

#assert_axioms firstBadTag_eq_none_iff
#assert_axioms firstBadTag_names_first
#assert_axioms chainPrefixes_getElem?
#assert_axioms chainPrefixes_getLast?
#assert_axioms verifyTags_ok_iff
#assert_axioms verifyTags_refuses_at
#assert_axioms verifyTags_refuses_head
#assert_axioms rootedChains_getElem?
#assert_axioms verifyTags_root
#assert_axioms pole_honest_accepted
#assert_axioms pole_middle_refused
#assert_axioms pole_head_refused
#assert_axioms pole_base_height_named

end Minidregg.Compiler.DurableLogTags
