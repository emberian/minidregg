/- The checked set of the agreement engine, retained: `State.checked` keeps the maximal
source histories the native checker has replayed, `validBlock` asks whether a block's
source history is a prefix of one of them, and a committed payload leaves the offers.

Kernel-only. Stated and proved here:
* `validBlock_iff`: validity is "a prefix of a kept history";
* `validBlock_prefix`: validity is prefix-closed (a replay replays every prefix);
* `addChecked_exact`: checking a block makes valid exactly the prefixes of its history,
  and keeps everything that was valid (`addChecked_valid`, `addChecked_mono` follow);
* `addChecked_antichain`: no kept history is a prefix of another;
* `addChecked_chain`: checking a history that extends every kept one keeps exactly it, so a
  replica that checks one growing chain holds one entry however long the chain;
* `doCommit_offers`: a commit only removes offers, and a delivering commit removes every
  payload it newly commits. -/
import Kernel.GenericSimplex

namespace Minidregg.Kernel.GenericSimplexChecked
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

theorem isPrefix_iff (a b : Block) : isPrefix a b = true ↔ a <+: b := by
  unfold isPrefix
  rw [beq_iff_eq, List.prefix_iff_eq_take]
  exact eq_comm

/-- No kept history is a prefix of a different kept one. -/
def Antichain (checked : List Block) : Prop :=
  checked.Pairwise fun a b => ¬ a <+: b ∧ ¬ b <+: a

theorem validBlock_iff (s : State) (block : Block) :
    validBlock s block = true ↔
      applicationHistory block = [] ∨ ∃ kept ∈ s.checked, applicationHistory block <+: kept := by
  unfold validBlock
  simp only [Bool.or_eq_true, List.isEmpty_iff, List.any_eq_true, isPrefix_iff]

/-- Validity is prefix-closed. -/
theorem validBlock_prefix (s : State) {a b : Block} (ab : a <+: b)
    (valid : validBlock s b = true) : validBlock s a = true := by
  rw [validBlock_iff] at valid ⊢
  have histories := applicationHistory_preserves_prefix ab
  rcases valid with empty | ⟨kept, inside, under⟩
  · left
    rw [empty] at histories
    exact List.prefix_nil.mp histories
  · exact Or.inr ⟨kept, inside, histories.trans under⟩

theorem mem_addChecked (checked : List Block) (block kept : Block) :
    kept ∈ addChecked checked block →
      kept ∈ checked ∨ kept = applicationHistory block := by
  unfold addChecked
  dsimp only
  split
  · exact Or.inl
  · intro inside
    rcases List.mem_append.mp inside with old | new
    · exact Or.inl (List.mem_filter.mp old).1
    · exact Or.inr (List.mem_singleton.mp new)

/-- **Exactness.** After a block is checked, a block is valid exactly when it was valid
before or its source history is a prefix of the checked one. -/
theorem addChecked_exact (s : State) (checkedBlock block : Block) :
    validBlock { s with checked := addChecked s.checked checkedBlock } block = true ↔
      validBlock s block = true ∨ applicationHistory block <+: applicationHistory checkedBlock := by
  rw [validBlock_iff, validBlock_iff]
  show _ ∨ (∃ kept ∈ addChecked s.checked checkedBlock, _) ↔ _
  constructor
  · rintro (empty | ⟨kept, inside, under⟩)
    · exact Or.inl (Or.inl empty)
    · rcases mem_addChecked _ _ _ inside with old | new
      · exact Or.inl (Or.inr ⟨kept, old, under⟩)
      · exact Or.inr (new ▸ under)
  · rintro ((empty | ⟨kept, inside, under⟩) | under)
    · exact Or.inl empty
    · -- A kept history survives, or the new one extends it.
      unfold addChecked
      dsimp only
      split
      · exact Or.inr ⟨kept, inside, under⟩
      · by_cases extended : isPrefix kept (applicationHistory checkedBlock) = true
        · exact Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl),
            under.trans ((isPrefix_iff _ _).mp extended)⟩
        · exact Or.inr ⟨kept, List.mem_append_left _
            (List.mem_filter.mpr ⟨inside, by simpa using extended⟩), under⟩
    · by_cases empty : applicationHistory block = []
      · exact Or.inl empty
      · right
        unfold addChecked
        dsimp only
        split
        · rename_i already
          rcases Bool.or_eq_true _ _ ▸ already with none | some
          · rw [List.isEmpty_iff] at none
            rw [none] at under
            exact absurd (List.prefix_nil.mp under) empty
          · obtain ⟨kept, inside, covers⟩ := List.any_eq_true.mp some
            exact ⟨kept, inside, under.trans ((isPrefix_iff _ _).mp covers)⟩
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton.mpr rfl), under⟩

/-- The checked block is valid. -/
theorem addChecked_valid (s : State) (block : Block) :
    validBlock { s with checked := addChecked s.checked block } block = true :=
  (addChecked_exact s block block).mpr (Or.inr (List.prefix_refl _))

/-- Nothing valid stops being valid. -/
theorem addChecked_mono (s : State) (checkedBlock block : Block)
    (valid : validBlock s block = true) :
    validBlock { s with checked := addChecked s.checked checkedBlock } block = true :=
  (addChecked_exact s checkedBlock block).mpr (Or.inl valid)

theorem addChecked_antichain (checked : List Block) (block : Block)
    (old : Antichain checked) : Antichain (addChecked checked block) := by
  unfold addChecked
  dsimp only
  split
  · exact old
  · rename_i fresh
    simp only [Bool.or_eq_true, List.any_eq_true, not_or, not_exists, not_and,
      Bool.not_eq_true] at fresh
    unfold Antichain
    rw [List.pairwise_append]
    refine ⟨old.sublist List.filter_sublist, List.pairwise_singleton _ _, ?_⟩
    intro kept inside new last
    rw [List.mem_singleton.mp last]
    obtain ⟨member, notUnder⟩ := List.mem_filter.mp inside
    constructor
    · intro under
      have : isPrefix kept (applicationHistory block) = true := (isPrefix_iff _ _).mpr under
      simp [this] at notUnder
    · intro over
      have := fresh.2 kept member
      rw [(isPrefix_iff _ _).mpr over] at this
      exact Bool.noConfusion this

/-- **One chain, one entry.** Checking a nonempty history that extends every kept one keeps
exactly that history. -/
theorem addChecked_chain (checked : List Block) (block : Block)
    (nonempty : applicationHistory block ≠ [])
    (strict : ∀ kept ∈ checked, kept <+: applicationHistory block ∧ kept ≠ applicationHistory block) :
    addChecked checked block = [applicationHistory block] := by
  unfold addChecked
  dsimp only
  have fresh : (applicationHistory block).isEmpty = false ∧
      checked.any (fun kept => isPrefix (applicationHistory block) kept) = false := by
    refine ⟨by simpa using nonempty, ?_⟩
    rw [List.any_eq_false]
    intro kept inside covers
    have under := (strict kept inside).1
    have over := (isPrefix_iff _ _).mp covers
    exact (strict kept inside).2 (under.eq_of_length (Nat.le_antisymm under.length_le over.length_le))
  rw [fresh.1, fresh.2]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  have gone : checked.filter (fun kept => !isPrefix kept (applicationHistory block)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro kept inside
    simp [(isPrefix_iff _ _).mpr (strict kept inside).1]
  rw [gone]
  rfl

/-- A commit only removes offers. -/
theorem doCommit_offers_subset (s : State) (number : Nat) (block : Block) :
    ∀ payload ∈ (doCommit s number block).offers, payload ∈ s.offers := by
  have cleared : (clear s number (some block)).offers = s.offers := by
    unfold clear; dsimp only; split <;> rfl
  intro payload
  unfold doCommit
  dsimp only
  repeat' split
  all_goals first
    | exact id
    | (intro inside; exact cleared ▸ inside)
    | (intro inside; exact cleared ▸ (List.mem_filter.mp inside).1)

/-- What `doCommit` leaves offered is not among the payloads it newly committed. -/
theorem doCommit_offers (s : State) (number : Nat) (block : Block)
    (moved : (doCommit s number block).committedTip ≠ s.committedTip) :
    ∀ payload ∈ (doCommit s number block).offers,
      payload ∉ (doCommit s number block).committedTip.drop s.committedTip.length := by
  have cleared : (clear s number (some block)).committedTip = s.committedTip := by
    unfold clear; dsimp only; split <;> rfl
  revert moved
  unfold doCommit
  dsimp only
  repeat' split
  all_goals first
    | (intro moved; exact absurd rfl moved)
    | (intro moved; exact absurd cleared moved)
    | (intro _ payload inside
       have kept : (!((block.drop (clear s number (some block)).committedTip.length).contains
           payload)) = true := (List.mem_filter.mp inside).2
       rw [cleared] at kept
       simpa using kept)

end Minidregg.Kernel.GenericSimplexChecked
