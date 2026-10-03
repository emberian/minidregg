import Kernel.GenericSimplexLocal

namespace Minidregg.Kernel.GenericSimplexCausal
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexLocal
set_option autoImplicit false

/-- Executable view indices, rather than an assumed per-view map. -/
def ViewsUnique (s : State) : Prop := (s.views.map View.number).Nodup

theorem viewAt_number (s : State) (number : Nat) :
    (viewAt s number).number = number := by
  unfold viewAt
  cases found : s.views.find? (fun v => v.number == number) with
  | none => rfl
  | some v =>
    have test := List.find?_some found
    simpa using test

/-- Replacement keeps every existing index. This matters because flags must
remain attached to their actual view throughout register/broadcast. -/
theorem replacement_numbers (views : List View) (v : View) :
    (views.map (fun old => if old.number == v.number then v else old)).map View.number =
      views.map View.number := by
  induction views with
  | nil => rfl
  | cons old rest ih =>
    simp only [List.map_cons]
    split <;> simp_all

/-- First-match replacement is the supplied view even with duplicate input
indices; uniqueness is needed separately for unambiguous retained history. -/
theorem find_replacement (views : List View) (v : View)
    (existsView : views.any (fun old => old.number == v.number) = true) :
    (views.map (fun old => if old.number == v.number then v else old)).find?
      (fun old => old.number == v.number) = some v := by
  induction views with
  | nil => simp at existsView
  | cons old rest ih =>
    simp only [List.any_cons, Bool.or_eq_true] at existsView
    simp only [List.map_cons, List.find?_cons]
    by_cases same : old.number = v.number
    · simp [same]
    · simp [same]
      exact ih (existsView.resolve_left (by simpa using same))

theorem viewAt_put_same (s : State) (v : View) :
    viewAt (putView s v) v.number = v := by
  unfold putView viewAt
  split
  next present => simp [find_replacement s.views v present]
  next absent =>
    have missing : s.views.find? (fun old => old.number == v.number) = none := by
      apply List.find?_eq_none.mpr
      intro old member
      have tests := List.any_eq_false.mp (Bool.eq_false_iff.mpr absent) old member
      exact tests
    simp [List.find?_append, missing]

/-- An already recorded vote/disable request cannot emit another vote. -/
theorem castVote_guarded (s : State) (number : Nat) (block : Block)
    (guard : (viewAt s number).voted = true ∨
      (viewAt s number).disableRequested = true) :
    castVote s number block = s := by
  rcases guard with voted | disabled
  · simp [castVote, voted]
  · simp [castVote, disabled]

theorem broadcast_voted (s : State) (number : Nat) (kind : Kind) (arg : Argument) :
    (viewAt (broadcast s number kind arg) number).voted = (viewAt s number).voted := by
  unfold broadcast register
  dsimp only
  have numberExact := viewAt_number s number
  simpa only [numberExact] using congrArg View.voted
    (viewAt_put_same s {viewAt s number with received :=
      addUnique (viewAt s number).received ⟨s.self, number, kind, arg⟩})

/-- A successful local VOTE sets the durable per-view guard before broadcast. -/
theorem castVote_sets_guard (s : State) (number : Nat) (block : Block)
    (enabled : (viewAt s number).voted = false)
    (notDisabled : (viewAt s number).disableRequested = false) :
    (viewAt (castVote s number block) number).voted = true := by
  simp only [castVote, enabled, notDisabled, Bool.false_or, Bool.false_eq_true,
    if_false]
  rw [broadcast_voted]
  have numberExact := viewAt_number s number
  simpa only [numberExact] using congrArg View.voted
    (viewAt_put_same s {viewAt s number with voted := true})

/-- The second attempted vote emits nothing, independently of its block. -/
theorem castVote_once (s : State) (number : Nat) (first second : Block) :
    castVote (castVote s number first) number second = castVote s number first := by
  by_cases voted : (viewAt s number).voted = true
  · rw [castVote_guarded s number first (Or.inl voted)]
    exact castVote_guarded s number second (Or.inl voted)
  · by_cases disabled : (viewAt s number).disableRequested = true
    · rw [castVote_guarded s number first (Or.inr disabled)]
      exact castVote_guarded s number second (Or.inr disabled)
    · apply castVote_guarded
      exact Or.inl (castVote_sets_guard s number first
        (Bool.eq_false_iff.mpr voted) (Bool.eq_false_iff.mpr disabled))

#assert_axioms broadcast_voted
#assert_axioms castVote_sets_guard
#assert_axioms castVote_once

#assert_axioms viewAt_number
#assert_axioms replacement_numbers
#assert_axioms find_replacement
#assert_axioms viewAt_put_same
#assert_axioms castVote_guarded
end Minidregg.Kernel.GenericSimplexCausal
