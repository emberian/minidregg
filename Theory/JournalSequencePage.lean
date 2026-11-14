/-
# Theory.JournalSequencePage -- one page of a journal sequence, with a horizon

A reader of a journal sequence (`Theory.JournalSequences`) resumes by position, under a row
limit and a byte budget, over a Store that may no longer hold the records below a height.
This module states what one such read answers (`Page`) and proves it:

* a page of rows is the next members in order, non-empty, within both limits, all held, and
  the members before the cursor followed by the page are the members before the resumed
  cursor, so a resumed cursor skips nothing and delivers nothing twice (`page_rows`);
* members whose records are not held are a NAMED gap through the last such position, and a
  read resumed there is not a gap (`page_gap`); an empty successful page does not exist:
  nothing above the cursor is the tip (`page_tip`);
* a member that alone exceeds the byte budget is named, held, and is the next member
  (`page_oversize`); maintained rows are never reported absent (`page_not_absent`);
* the read as it runs, each row and size fetched through a monad, is that page
  (`pageM_pure`). It reads the rows of one bisection and of the page.

Teeth: `PageExample` (a gap named from the start, resumption after it, the byte budget
cutting a page, an oversize member, the tip, a dropped row reported).
-/
module

public import Theory.JournalSequences
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Theory.JournalSequences

set_option autoImplicit false

/-! ## A page of a sequence, with a horizon

A reader resumes a sequence by position (`after`: the last position it consumed), under a row
limit and a byte budget, over a Store that may no longer hold the records at or below a
height (`retired`: a retired prefix, a checkpoint-only Store). A page is never an empty
success: it is rows, or one of three named states. -/

/-- What one page read answers. -/
inductive Page where
  /-- The members at positions `first, first + 1, …`, by height: at least one. -/
  | rows (first : Nat) (heights : List Nat)
  /-- Nothing above the cursor: the sequence has `count` members and the cursor is at or past it. -/
  | tip (count : Nat)
  /-- **A named gap**: the positions above the cursor through `through` are members whose
  records are not held. `through` is the last such position: a read resumed after it is not a gap. -/
  | gap (through : Nat)
  /-- The next member alone exceeds the byte budget; nothing was delivered or skipped. -/
  | oversize (position height : Nat)
  /-- A row inside the count is missing: the rows are not a maintained sequence. -/
  | absent (position : Nat)
  deriving DecidableEq, Repr

/-- The longest prefix whose sizes fit the budget. -/
def fitting (size : Nat → Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | budget, height :: rest =>
      if size height ≤ budget then height :: fitting size (budget - size height) rest else []

/-- One page: above position `after`, at most `max limit 1` members within `budget` bytes,
over rows whose records at heights at or below `retired` are not held. It reads the rows of
one bisection and of the page, whatever the sequence's length. -/
def page (rows : Nat → Option Nat) (size : Nat → Nat) (count retired after limit budget : Nat) : Page :=
  if count ≤ after then .tip count
  else
    let unheld := below rows retired (belowFuel count) 0 count
    if after < unheld then .gap unheld
    else
      match read rows (after + 1) (max limit 1) with
      | [] => .absent (after + 1)
      | height :: rest =>
          match fitting size budget (height :: rest) with
          | [] => .oversize (after + 1) height
          | fit => .rows (after + 1) fit

/-- The cursor a reader resumes from after a page. Rows and a gap advance it; the tip and an
oversize member leave it where it was. -/
def Page.resume (after : Nat) : Page → Nat
  | .rows _ heights => after + heights.length
  | .gap through => through
  | _ => after

theorem fitting_prefix (size : Nat → Nat) : ∀ (budget : Nat) (heights : List Nat),
    fitting size budget heights <+: heights
  | _, [] => List.prefix_refl _
  | budget, height :: rest => by
      unfold fitting
      split
      · exact List.cons_prefix_cons.mpr ⟨rfl, fitting_prefix size _ rest⟩
      · exact List.nil_prefix

theorem fitting_sum (size : Nat → Nat) : ∀ (budget : Nat) (heights : List Nat),
    ((fitting size budget heights).map size).sum ≤ budget
  | _, [] => Nat.zero_le _
  | budget, height :: rest => by
      unfold fitting
      split
      · have ih := fitting_sum size (budget - size height) rest
        simp only [List.map_cons, List.sum_cons]
        omega
      · exact Nat.zero_le _

private theorem unheld_spec (listed : List Nat) (sorted : listed.Pairwise (· < ·)) (retired : Nat) :
    below (itemOf listed) retired (belowFuel listed.length) 0 listed.length =
      (listed.filter (fun height => height ≤ retired)).length :=
  below_spec listed sorted retired (belowFuel listed.length) 0 listed.length (Nat.zero_le _)
    (Nat.le_refl _) (by simpa using lt_two_pow_belowFuel listed.length)
    (fun i height before _ => absurd before (Nat.not_lt_zero i))
    (fun i height beyond found => by
      rw [List.getElem?_eq_none beyond] at found; cases found)

private theorem held_above (listed : List Nat) (sorted : listed.Pairwise (· < ·)) (retired after : Nat)
    (past : (listed.filter (fun height => height ≤ retired)).length ≤ after) :
    ∀ height ∈ listed.drop after, retired < height := by
  intro height member
  have split : listed.drop after =
      (listed.drop (listed.filter (fun height => height ≤ retired)).length).drop
        (after - (listed.filter (fun height => height ≤ retired)).length) := by
    rw [List.drop_drop]; congr 1; omega
  rw [split, drop_below_eq_filter listed sorted retired] at member
  have kept := List.mem_of_mem_drop member
  simpa using (List.mem_filter.mp kept).2

private theorem take_append_prefix {A : Type} (list fit : List A) (after : Nat)
    (isPrefix : fit <+: list.drop after) : list.take after ++ fit = list.take (after + fit.length) := by
  obtain ⟨tail, eq⟩ := isPrefix
  by_cases inside : after ≤ list.length
  · have len : (list.take after ++ fit).length = after + fit.length := by
      simp only [List.length_append, List.length_take]; omega
    calc list.take after ++ fit = ((list.take after ++ fit) ++ tail).take (after + fit.length) :=
          (List.take_left' len).symm
      _ = list.take (after + fit.length) := by rw [List.append_assoc, eq, List.take_append_drop]
  · have none : list.drop after = [] := List.drop_eq_nil_of_le (by omega)
    rw [none] at eq
    have empty : fit = [] := (List.append_eq_nil_iff.mp eq).1
    subst empty
    simp only [List.append_nil, List.length_nil, Nat.add_zero]

/-- **A page of rows is the next members, in order, within both limits, all held.** The
members before the cursor followed by the page are the members before the resumed cursor: a
resumed cursor skips nothing and delivers nothing twice. -/
theorem page_rows (listed : List Nat) (sorted : listed.Pairwise (· < ·)) (size : Nat → Nat)
    (retired after limit budget first : Nat) (heights : List Nat)
    (answered : page (itemOf listed) size listed.length retired after limit budget = .rows first heights) :
    first = after + 1 ∧ heights ≠ [] ∧
      listed.take after ++ heights = listed.take (after + heights.length) ∧
      heights.length ≤ max limit 1 ∧ (heights.map size).sum ≤ budget ∧
      ∀ height ∈ heights, retired < height := by
  unfold page at answered
  split at answered
  · cases answered
  · rw [unheld_spec listed sorted retired] at answered
    simp only at answered
    split at answered
    · cases answered
    · rename_i past
      rw [read_itemOf] at answered
      split at answered
      · cases answered
      · rename_i height rest window
        split at answered
        · cases answered
        · rename_i nonempty
          injection answered with firstEq heightsEq
          subst heightsEq
          have whole : height :: rest <+: listed.drop after := by
            rw [← window]; exact List.take_prefix _ _
          have fromDrop : fitting size budget (height :: rest) <+: listed.drop after :=
            (fitting_prefix size budget (height :: rest)).trans whole
          have short : (fitting size budget (height :: rest)).length ≤ max limit 1 := by
            have fits := (fitting_prefix size budget (height :: rest)).length_le
            have taken := congrArg List.length window
            simp only [List.length_take] at taken
            omega
          refine ⟨firstEq.symm, ?_, take_append_prefix listed _ after fromDrop, short,
            fitting_sum size budget _, ?_⟩
          · intro empty
            exact nonempty empty
          · intro member inFit
            exact held_above listed sorted retired after (by omega) member (fromDrop.subset inFit)

/-- **A gap is named exactly**: the cursor is below `through`, and `through` is the number of
members whose records are not held, so the members above the cursor through it are all
unheld and a read resumed after it is not a gap. -/
theorem page_gap (listed : List Nat) (sorted : listed.Pairwise (· < ·)) (size : Nat → Nat)
    (retired after limit budget through : Nat)
    (answered : page (itemOf listed) size listed.length retired after limit budget = .gap through) :
    after < through ∧ through = (listed.filter (fun height => height ≤ retired)).length ∧
      ∀ again other : Nat, page (itemOf listed) size listed.length retired through again budget ≠ .gap other := by
  unfold page at answered
  split at answered
  · cases answered
  · rw [unheld_spec listed sorted retired] at answered
    simp only at answered
    split at answered
    · rename_i below_
      injection answered with same
      subst same
      refine ⟨below_, rfl, ?_⟩
      intro again other repeated
      unfold page at repeated
      split at repeated
      · cases repeated
      · rw [unheld_spec listed sorted retired] at repeated
        simp only at repeated
        split at repeated
        · rename_i loop; exact absurd loop (Nat.lt_irrefl _)
        · split at repeated
          · cases repeated
          · split at repeated <;> cases repeated
    · split at answered
      · cases answered
      · split at answered <;> cases answered

/-- **The tip is the tip**: the cursor is at or past the last member. -/
theorem page_tip (listed : List Nat) (size : Nat → Nat) (retired after limit budget count : Nat)
    (answered : page (itemOf listed) size listed.length retired after limit budget = .tip count) :
    count = listed.length ∧ listed.length ≤ after := by
  unfold page at answered
  split at answered
  · rename_i past
    injection answered with same
    exact ⟨same.symm, past⟩
  · simp only at answered
    split at answered
    · cases answered
    · split at answered
      · cases answered
      · split at answered <;> cases answered

/-- **An oversize member is the next member, held, and alone exceeds the budget.** -/
theorem page_oversize (listed : List Nat) (sorted : listed.Pairwise (· < ·)) (size : Nat → Nat)
    (retired after limit budget position height : Nat)
    (answered : page (itemOf listed) size listed.length retired after limit budget = .oversize position height) :
    position = after + 1 ∧ listed[after]? = some height ∧ budget < size height ∧ retired < height := by
  unfold page at answered
  split at answered
  · cases answered
  · rw [unheld_spec listed sorted retired] at answered
    simp only at answered
    split at answered
    · cases answered
    · rename_i past
      rw [read_itemOf] at answered
      split at answered
      · cases answered
      · rename_i first rest window
        split at answered
        · rename_i unfit
          injection answered with positionEq heightEq
          subst heightEq
          have whole : first :: rest <+: listed.drop after := by
            rw [← window]; exact List.take_prefix _ _
          have atCursor : listed[after]? = some first := by
            obtain ⟨tail, eq⟩ := whole
            have := congrArg (fun list => list[0]?) eq
            simpa [List.getElem?_drop] using this.symm
          refine ⟨positionEq.symm, atCursor, ?_, ?_⟩
          · unfold fitting at unfit
            split at unfit
            · cases unfit
            · omega
          · exact held_above listed sorted retired after (by omega) first (whole.subset List.mem_cons_self)
        · cases answered

/-- **Maintained rows are never reported absent.** -/
theorem page_not_absent (listed : List Nat) (size : Nat → Nat) (retired after limit budget position : Nat) :
    page (itemOf listed) size listed.length retired after limit budget ≠ .absent position := by
  intro answered
  unfold page at answered
  split at answered
  · cases answered
  · rename_i inside
    simp only at answered
    split at answered
    · cases answered
    · rw [read_itemOf] at answered
      split at answered
      · rename_i window
        have taken := congrArg List.length window
        simp only [List.length_take, List.length_drop, List.length_nil] at taken
        omega
      · split at answered <;> cases answered

/-- **Every page makes progress or says why not**: rows and a gap move the cursor forward. -/
theorem page_progress (listed : List Nat) (sorted : listed.Pairwise (· < ·)) (size : Nat → Nat)
    (retired after limit budget : Nat) :
    (∀ first heights, page (itemOf listed) size listed.length retired after limit budget = .rows first heights →
        after < Page.resume after (.rows first heights)) ∧
      (∀ through, page (itemOf listed) size listed.length retired after limit budget = .gap through →
        after < Page.resume after (.gap through)) := by
  refine ⟨fun first heights answered => ?_, fun through answered => ?_⟩
  · have facts := page_rows listed sorted size retired after limit budget first heights answered
    have positive : 0 < heights.length := List.length_pos_iff.mpr facts.2.1
    simp only [Page.resume]; omega
  · exact (page_gap listed sorted size retired after limit budget through answered).1

/-- `fitting`, each member's size read through `m`. -/
def fittingM {m : Type → Type} [Monad m] (size : Nat → m Nat) : Nat → List Nat → m (List Nat)
  | _, [] => pure []
  | budget, height :: rest => do
      let bytes ← size height
      if bytes ≤ budget then do
        let more ← fittingM size (budget - bytes) rest
        pure (height :: more)
      else pure []

/-- `page`, the count, each row and each member's size read through `m`: the page as the
served reader runs it. -/
def pageM {m : Type → Type} [Monad m] (count : m Nat) (rows : Nat → m (Option Nat)) (size : Nat → m Nat)
    (retired after limit budget : Nat) : m Page := do
  let counted ← count
  if counted ≤ after then pure (.tip counted)
  else do
    let unheld ← belowM rows retired (belowFuel counted) 0 counted
    if after < unheld then pure (.gap unheld)
    else do
      let heights ← readM rows (after + 1) (max limit 1)
      match heights with
      | [] => pure (.absent (after + 1))
      | height :: rest => do
          let fit ← fittingM size budget (height :: rest)
          match fit with
          | [] => pure (.oversize (after + 1) height)
          | fit => pure (.rows (after + 1) fit)

theorem fittingM_pure {m : Type → Type} [Monad m] [LawfulMonad m] (size : Nat → Nat) :
    ∀ (heights : List Nat) (budget : Nat),
      fittingM (m := m) (fun height => pure (size height)) budget heights = pure (fitting size budget heights)
  | [], _ => rfl
  | height :: rest, budget => by
      unfold fittingM fitting
      simp only [pure_bind]
      by_cases fits : size height ≤ budget
      · simp only [fits, ite_true, fittingM_pure size rest, pure_bind]
      · simp only [fits, ite_false]

/-- **The page that runs is the page that is specified.** -/
theorem pageM_pure {m : Type → Type} [Monad m] [LawfulMonad m] (count : Nat) (rows : Nat → Option Nat)
    (size : Nat → Nat) (retired after limit budget : Nat) :
    pageM (m := m) (pure count) (fun position => pure (rows position)) (fun height => pure (size height))
        retired after limit budget =
      pure (page rows size count retired after limit budget) := by
  unfold pageM page
  simp only [pure_bind, belowM_pure, readM_pure, fittingM_pure]
  by_cases past : count ≤ after
  · simp only [past, ite_true]
  · simp only [past, ite_false]
    split
    · rfl
    · split
      · rfl
      · split <;> rfl


namespace PageExample

/-- Members at heights 1, 2, 5, 7; records at or below height 2 are not held; a member's size
is its height. -/
def listed : List Nat := [1, 2, 5, 7]

/-- From the start the retired members are a named gap through position 2, never an empty page. -/
theorem gap_named : page (itemOf listed) id 4 2 0 8 100 = .gap 2 := by decide

/-- Resumed after the gap: the two held members, in order. -/
theorem resumed : page (itemOf listed) id 4 2 2 8 100 = .rows 3 [5, 7] := by decide

/-- The byte budget cuts the page after the first member; the reader resumes at position 3. -/
theorem budget_cuts : page (itemOf listed) id 4 2 2 8 6 = .rows 3 [5] ∧
    Page.resume 2 (.rows 3 [5]) = 3 := by decide

/-- A member larger than the whole budget is named, not skipped. -/
theorem oversize_named : page (itemOf listed) id 4 2 3 8 6 = .oversize 4 7 := by decide

/-- At the last member the answer is the tip, not an empty page of rows. -/
theorem tip_named : page (itemOf listed) id 4 2 4 8 100 = .tip 4 := by decide

/-- Rows that drop a position inside the count are reported, not served as the end. -/
theorem absent_named : page (fun position => if position = 3 then none else itemOf listed position) id 4 0 2 8 100 =
    .absent 3 := by decide

end PageExample

#assert_axioms page_rows
#assert_axioms page_gap
#assert_axioms page_tip
#assert_axioms page_oversize
#assert_axioms page_not_absent
#assert_axioms page_progress
#assert_axioms pageM_pure
#assert_axioms PageExample.gap_named
#assert_axioms PageExample.absent_named

end Minidregg.Theory.JournalSequences
