/-
# Theory.JournalSequences -- keyed append-only sequences over a journal, maintained

A journal is a list of accepted records. A record may belong to some *sequences* (the turns
one account paid for; the payments one account received on one topic). A served read wants a
sequence's newest member, its length, or its members above a cursor. Walking the journal for
that costs its whole length on every request; this module states the view that replaces the
walk and proves it is the walk's answer.

* `heights journal seq`: the recomputation, the heights (from 1) of the records that belong
  to `seq`, in order; `count` and `item` are its length and its `i`-th element.
* `Rows`: what is kept, a count per sequence and a height per `(sequence, position)`.
  `Rows.advance`: the update rule. A record writes two rows per sequence it belongs to
  (`writes_length`), whatever the journal holds; over a keyed trie each is one path.
* `maintained`: the `Theory.Retained.Maintained` instance, so
  `Retained.Maintained.reachable_eq_recompute` gives the keystone: after any run the kept
  rows answer `count` and `item` as the recomputation does (`advance_holds`).
* Reads: `item_count` (the newest member is the row at position `count`); `below` with
  `below_spec` and `window_spec` (members above a cursor, found by bisection over rows in
  `belowFuel count` probes, then read in order); `scanFrom_take`, `filter_getLast?` and
  `filter_length_eq_count` (a scan of the whole log that keeps a record exactly when it
  belongs to the sequence is those row reads).

Witnesses (ATLAS law 2). Satisfiable: `Example.reads` (a three-record journal, its rows
advanced from empty, answer the scan's count, newest member and window). Teeth:
`Example.stale_refuted` (rows not advanced by a member's record answer the old count);
`Example.window_excludes_cursor` (a member at the cursor is not in the window). Premise
inhabitation: `empty_holds`, and `advance_holds` has no premise beyond `Holds`.
-/
module

public import Theory.Retained
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Theory.JournalSequences

set_option autoImplicit false

variable {S : Type} [DecidableEq S]

/-- First occurrences, in order: a record belongs to a sequence once however often it names it. -/
def distinct : List S → List S
  | [] => []
  | a :: rest => a :: (distinct rest).filter (fun b => b ≠ a)

theorem mem_distinct (seq : S) : ∀ members : List S, seq ∈ distinct members ↔ seq ∈ members
  | [] => by simp [distinct]
  | a :: rest => by
      have ih := mem_distinct seq rest
      by_cases same : seq = a
      · simp [distinct, same]
      · simp [distinct, List.mem_filter, same, ih]

theorem distinct_nodup : ∀ members : List S, (distinct members).Nodup
  | [] => by simp [distinct]
  | a :: rest => by
      have ih := distinct_nodup rest
      simp only [distinct, List.nodup_cons, List.mem_filter]
      exact ⟨fun h => by simpa using h.2, ih.filter _⟩

theorem distinct_length_le : ∀ members : List S, (distinct members).length ≤ members.length
  | [] => by simp [distinct]
  | a :: rest => by
      have ih := distinct_length_le rest
      have filtered := List.length_filter_le (fun b => decide (b ≠ a)) (distinct rest)
      simp only [distinct, List.length_cons]
      omega

/-- The heights of the records that belong to `seq`, the record at list position `i` taking
height `start + i`. -/
def heightsFrom (seq : S) : Nat → List (List S) → List Nat
  | _, [] => []
  | start, members :: rest =>
      if seq ∈ members then start :: heightsFrom seq (start + 1) rest
      else heightsFrom seq (start + 1) rest

/-- **The recomputation**: the heights (from 1) of the journal's records that belong to `seq`. -/
def heights (journal : List (List S)) (seq : S) : List Nat := heightsFrom seq 1 journal

theorem heightsFrom_append (seq : S) : ∀ (start : Nat) (journal : List (List S)) (members : List S),
    heightsFrom seq start (journal ++ [members]) =
      heightsFrom seq start journal ++ (if seq ∈ members then [start + journal.length] else [])
  | start, [], members => by
      by_cases mem : seq ∈ members <;> simp [heightsFrom, mem]
  | start, first :: rest, members => by
      have ih := heightsFrom_append seq (start + 1) rest members
      have shift : start + 1 + rest.length = start + (rest.length + 1) := by omega
      by_cases mem : seq ∈ first <;> simp [heightsFrom, mem, ih, shift]

theorem heights_append (journal : List (List S)) (members : List S) (seq : S) :
    heights (journal ++ [members]) seq =
      heights journal seq ++ (if seq ∈ members then [journal.length + 1] else []) := by
  unfold heights
  rw [heightsFrom_append, Nat.add_comm]

/-- Every listed height is a record's: from `start` up to the journal's end. -/
theorem heightsFrom_bounds (seq : S) : ∀ (start : Nat) (journal : List (List S)) (height : Nat),
    height ∈ heightsFrom seq start journal → start ≤ height ∧ height < start + journal.length
  | _, [], _, member => by simp [heightsFrom] at member
  | start, first :: rest, height, member => by
      have ih := heightsFrom_bounds seq (start + 1) rest height
      simp only [heightsFrom] at member
      split at member
      · rcases List.mem_cons.mp member with here | later
        · subst here; simp
        · have := ih later; simp only [List.length_cons]; omega
      · have := ih member; simp only [List.length_cons]; omega

/-- The record at a listed height belongs to the sequence, and every record that belongs is
listed (the view names exactly the members). -/
theorem mem_heightsFrom (seq : S) : ∀ (start : Nat) (journal : List (List S)) (height : Nat),
    height ∈ heightsFrom seq start journal ↔
      ∃ index members, journal[index]? = some members ∧ height = start + index ∧ seq ∈ members
  | _, [], _ => by simp [heightsFrom]
  | start, first :: rest, height => by
      have ih := mem_heightsFrom seq (start + 1) rest height
      constructor
      · intro member
        simp only [heightsFrom] at member
        split at member
        · rename_i belongs
          rcases List.mem_cons.mp member with here | later
          · exact ⟨0, first, rfl, by omega, belongs⟩
          · obtain ⟨index, members, found, at_, belongs'⟩ := ih.mp later
            exact ⟨index + 1, members, by simpa using found, by omega, belongs'⟩
        · obtain ⟨index, members, found, at_, belongs'⟩ := ih.mp member
          exact ⟨index + 1, members, by simpa using found, by omega, belongs'⟩
      · rintro ⟨index, members, found, at_, belongs⟩
        cases index with
        | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst found
            simp [heightsFrom, belongs, at_]
        | succ index =>
            simp only [List.getElem?_cons_succ] at found
            have later : height ∈ heightsFrom seq (start + 1) rest :=
              ih.mpr ⟨index, members, found, by omega, belongs⟩
            simp only [heightsFrom]
            split
            · exact List.mem_cons_of_mem _ later
            · exact later

/-- Heights are listed in strictly increasing order. -/
theorem heightsFrom_sorted (seq : S) : ∀ (start : Nat) (journal : List (List S)),
    (heightsFrom seq start journal).Pairwise (· < ·)
  | _, [] => by simp [heightsFrom]
  | start, first :: rest => by
      have ih := heightsFrom_sorted seq (start + 1) rest
      simp only [heightsFrom]
      split
      · refine List.pairwise_cons.mpr ⟨fun later member => ?_, ih⟩
        have := (heightsFrom_bounds seq (start + 1) rest later member).1
        omega
      · exact ih

/-- The number of records that belong to `seq`. -/
def count (journal : List (List S)) (seq : S) : Nat := (heights journal seq).length

/-- The height of the `position`-th record that belongs to `seq` (positions from 1). -/
def item (journal : List (List S)) (seq : S) (position : Nat) : Option Nat :=
  if position = 0 then none else (heights journal seq)[position - 1]?

theorem heightsFrom_length_le (seq : S) : ∀ (start : Nat) (journal : List (List S)),
    (heightsFrom seq start journal).length ≤ journal.length
  | _, [] => by simp [heightsFrom]
  | start, first :: rest => by
      have ih := heightsFrom_length_le seq (start + 1) rest
      simp only [heightsFrom]
      split <;> simp only [List.length_cons] <;> omega

/-- A sequence never has more members than the journal has records. -/
theorem count_le_length (journal : List (List S)) (seq : S) : count journal seq ≤ journal.length :=
  heightsFrom_length_le seq 1 journal

theorem count_append (journal : List (List S)) (members : List S) (seq : S) :
    count (journal ++ [members]) seq = count journal seq + (if seq ∈ members then 1 else 0) := by
  unfold count
  rw [heights_append]
  by_cases mem : seq ∈ members <;> simp [mem]

theorem item_append (journal : List (List S)) (members : List S) (seq : S) (position : Nat) :
    item (journal ++ [members]) seq position =
      if seq ∈ members ∧ position = count journal seq + 1 then some (journal.length + 1)
      else item journal seq position := by
  unfold item count
  rw [heights_append]
  by_cases zero : position = 0
  · subst zero; simp
  · simp only [zero, ite_false]
    by_cases mem : seq ∈ members
    · simp only [mem, ite_true, true_and]
      by_cases last : position = (heights journal seq).length + 1
      · subst last; simp
      · simp only [last, ite_false]
        by_cases inside : position - 1 < (heights journal seq).length
        · rw [List.getElem?_append_left inside]
        · rw [List.getElem?_append_right (by omega)]
          have beyond : (heights journal seq).length ≤ position - 1 := by omega
          rw [List.getElem?_eq_none beyond]
          have : position - 1 - (heights journal seq).length ≠ 0 := by omega
          cases h : position - 1 - (heights journal seq).length with
          | zero => exact absurd h this
          | succ n => simp
    · simp [mem]

/-- **The newest member**: the last listed height is the item at position `count`. -/
theorem item_count (journal : List (List S)) (seq : S) :
    item journal seq (count journal seq) = (heights journal seq).getLast? := by
  unfold item count
  by_cases empty : (heights journal seq).length = 0
  · have isNil : heights journal seq = [] := List.eq_nil_of_length_eq_zero empty
    simp [isNil]
  · simp only [empty, ite_false]
    rw [List.getLast?_eq_getElem?]

/-! ## The maintained rows -/

/-- What is kept: the journal's height, one count per sequence (an absent row is 0) and one
row per `(sequence, position)`. -/
structure Rows (S : Type) where
  height : Nat
  count : S → Nat
  item : S → Nat → Option Nat

/-- The rows answer as the recomputation does. -/
def Holds (rows : Rows S) (journal : List (List S)) : Prop :=
  rows.height = journal.length ∧ (∀ seq, rows.count seq = count journal seq) ∧
    ∀ seq position, rows.item seq position = item journal seq position

def Rows.empty : Rows S := ⟨0, fun _ => 0, fun _ _ => none⟩

/-- One record's row writes, read against the rows before it: for each sequence it belongs to
(once), the count row and the row of the new last position. -/
inductive Write (S : Type) where
  | count (seq : S) (value : Nat)
  | item (seq : S) (position : Nat) (height : Nat)

def writes (rows : Rows S) (members : List S) : List (Write S) :=
  (distinct members).flatMap fun seq =>
    [.count seq (rows.count seq + 1), .item seq (rows.count seq + 1) (rows.height + 1)]

/-- **A record writes two rows per sequence it belongs to, whatever the journal holds.** -/
theorem writes_length (rows : Rows S) (members : List S) :
    (writes rows members).length = 2 * (distinct members).length := by
  unfold writes
  generalize distinct members = seqs
  induction seqs with
  | nil => rfl
  | cons seq rest ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil, ih]; omega

theorem writes_length_le (rows : Rows S) (members : List S) :
    (writes rows members).length ≤ 2 * members.length := by
  rw [writes_length]
  have := distinct_length_le members
  omega

def Rows.write (rows : Rows S) : Write S → Rows S
  | .count seq value => { rows with count := fun other => if other = seq then value else rows.count other }
  | .item seq position height =>
      { rows with item := fun other at_ => if other = seq ∧ at_ = position then some height
          else rows.item other at_ }

/-- **The update rule**: the record's writes applied in order, then the height advanced. -/
def Rows.advance (members : List S) (rows : Rows S) : Rows S :=
  let written := (writes rows members).foldl Rows.write rows
  { written with height := rows.height + 1 }

/-- The rows after writing the count and last-position rows of each of `seqs` (counts and
height read from `base`). -/
theorem foldl_write (base : Rows S) : ∀ (seqs : List S) (rows : Rows S),
    (seqs.flatMap fun seq =>
        [Write.count seq (base.count seq + 1), .item seq (base.count seq + 1) (base.height + 1)]).foldl
          Rows.write rows =
      { height := rows.height
        count := fun other => if other ∈ seqs then base.count other + 1 else rows.count other
        item := fun other at_ => if other ∈ seqs ∧ at_ = base.count other + 1 then some (base.height + 1)
          else rows.item other at_ }
  | [], rows => by simp
  | seq :: rest, rows => by
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons]
      rw [foldl_write base rest]
      simp only [Rows.write, Rows.mk.injEq, true_and]
      constructor
      · funext other
        by_cases inRest : other ∈ rest
        · simp [inRest]
        · by_cases same : other = seq <;> simp [inRest, same]
      · funext other at_
        by_cases inRest : other ∈ rest
        · by_cases last : at_ = base.count other + 1
          · simp [inRest, last]
          · by_cases same : other = seq
            · subst same; simp [inRest, last]
            · simp [inRest, last, same]
        · by_cases same : other = seq
          · subst same; simp [inRest]
          · simp [inRest, same]

/-- **The maintained rows are the recomputation's** (the step): rows that hold for a journal,
advanced by a record's sequences, hold for the journal with that record appended. -/
theorem advance_holds {rows : Rows S} {journal : List (List S)} (members : List S)
    (holds : Holds rows journal) : Holds (rows.advance members) (journal ++ [members]) := by
  obtain ⟨height, counts, items⟩ := holds
  unfold Rows.advance writes
  rw [foldl_write rows (distinct members) rows]
  refine ⟨by simp [height], fun seq => ?_, fun seq position => ?_⟩
  · simp only [mem_distinct]
    rw [count_append, counts]
    by_cases mem : seq ∈ members <;> simp [mem]
  · simp only [mem_distinct]
    rw [item_append, items, counts, height]

theorem empty_holds : Holds (Rows.empty : Rows S) [] := by
  refine ⟨rfl, fun _ => rfl, fun seq position => ?_⟩
  simp [Rows.empty, item, heights, heightsFrom]

/-! ## Reading a window above a cursor

A reader asks for members strictly above a height `cursor`. Heights are listed in increasing
order, so the number at or below the cursor is found by bisection over `item` (one row per
probe), and the window is the next positions in order. -/

/-- A list of heights read by position (positions from 1), as the item rows answer. -/
def itemOf (listed : List Nat) (position : Nat) : Option Nat :=
  if position = 0 then none else listed[position - 1]?

theorem item_eq_itemOf (journal : List (List S)) (seq : S) :
    item journal seq = itemOf (heights journal seq) := rfl

/-- Bisection: with every position at or below `lo` at or below the cursor and every position
above `hi` above it, the number of positions at or below the cursor. -/
def below (rows : Nat → Option Nat) (cursor : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi + 1) / 2
        match rows mid with
        | some height => if height ≤ cursor then below rows cursor fuel mid hi
            else below rows cursor fuel lo (mid - 1)
        | none => below rows cursor fuel lo (mid - 1)
      else lo

/-- The probes a bisection makes are bounded by its fuel: `Nat.log2 count + 1` suffices
(`below_spec`), so a window read costs logarithmically many rows in the sequence's length. -/
def belowFuel (count : Nat) : Nat := Nat.log2 count + 1

theorem lt_two_pow_belowFuel (count : Nat) : count < 2 ^ belowFuel count := by
  unfold belowFuel
  exact Nat.lt_log2_self

private theorem sorted_le {listed : List Nat} (sorted : listed.Pairwise (· < ·)) {i j : Nat} {a b : Nat}
    (order : i ≤ j) (atI : listed[i]? = some a) (atJ : listed[j]? = some b) : a ≤ b := by
  rcases Nat.lt_or_eq_of_le order with strict | same
  · obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp atI
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp atJ
    exact Nat.le_of_lt (List.pairwise_iff_getElem.mp sorted i j hi hj strict)
  · subst same
    rw [atI] at atJ
    exact Nat.le_of_eq (Option.some.inj atJ)

/-- A split position: everything before it at or below the cursor, everything from it above. -/
private theorem filter_length_of_split (listed : List Nat) (cursor split : Nat)
    (inside : split ≤ listed.length)
    (lower : ∀ i height, i < split → listed[i]? = some height → height ≤ cursor)
    (upper : ∀ i height, split ≤ i → listed[i]? = some height → cursor < height) :
    (listed.filter (fun height => height ≤ cursor)).length = split := by
  induction listed generalizing split with
  | nil => simp at inside; simp [inside]
  | cons first rest ih =>
      cases split with
      | zero =>
          have none : ∀ height ∈ first :: rest, ¬ height ≤ cursor := by
            intro height member
            obtain ⟨i, found⟩ := List.getElem?_of_mem member
            have := upper i height (Nat.zero_le _) found
            omega
          rw [List.filter_eq_nil_iff.mpr (by simpa using none)]
          rfl
      | succ split =>
          have firstLow : first ≤ cursor := lower 0 first (by omega) rfl
          have tail := ih split (by simpa using inside)
            (fun i height below found => lower (i + 1) height (by omega) (by simpa using found))
            (fun i height above found => upper (i + 1) height (by omega) (by simpa using found))
          simp [firstLow, tail]

/-- **Bisection is exact**: the number of listed heights at or below the cursor. -/
theorem below_spec (listed : List Nat) (sorted : listed.Pairwise (· < ·)) (cursor : Nat) :
    ∀ (fuel lo hi : Nat), lo ≤ hi → hi ≤ listed.length → hi - lo < 2 ^ fuel →
      (∀ i height, i < lo → listed[i]? = some height → height ≤ cursor) →
      (∀ i height, hi ≤ i → listed[i]? = some height → cursor < height) →
      below (itemOf listed) cursor fuel lo hi = (listed.filter (fun height => height ≤ cursor)).length
  | 0, lo, hi, order, inside, width, lower, upper => by
      have same : lo = hi := by simp at width; omega
      subst same
      simp only [below]
      exact (filter_length_of_split listed cursor lo inside lower upper).symm
  | fuel + 1, lo, hi, order, inside, width, lower, upper => by
      simp only [below]
      by_cases strict : lo < hi
      · simp only [strict, ite_true]
        have pow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [Nat.pow_succ, Nat.mul_comm]
        have midPos : (lo + hi + 1) / 2 ≠ 0 := by omega
        have midIn : (lo + hi + 1) / 2 - 1 < listed.length := by omega
        have found : itemOf listed ((lo + hi + 1) / 2) = some listed[(lo + hi + 1) / 2 - 1] := by
          simp [itemOf, midPos, List.getElem?_eq_getElem midIn]
        rw [found]
        simp only
        have atMid : listed[(lo + hi + 1) / 2 - 1]? = some listed[(lo + hi + 1) / 2 - 1] :=
          List.getElem?_eq_getElem midIn
        by_cases low : listed[(lo + hi + 1) / 2 - 1] ≤ cursor
        · simp only [low, ite_true]
          refine below_spec listed sorted cursor fuel _ hi (by omega) inside (by omega) ?_ upper
          intro i height before at_
          exact Nat.le_trans (sorted_le sorted (by omega) at_ atMid) low
        · simp only [low, ite_false]
          refine below_spec listed sorted cursor fuel lo _ (by omega) (by omega) (by omega) lower ?_
          intro i height after at_
          have := sorted_le sorted (show (lo + hi + 1) / 2 - 1 ≤ i by omega) atMid at_
          omega
      · simp only [strict, ite_false]
        have same : lo = hi := by omega
        subst same
        exact (filter_length_of_split listed cursor lo inside lower upper).symm

/-- The heights above the cursor are what follows the ones at or below it. -/
theorem drop_below_eq_filter (listed : List Nat) (sorted : listed.Pairwise (· < ·)) (cursor : Nat) :
    listed.drop (listed.filter (fun height => height ≤ cursor)).length =
      listed.filter (fun height => cursor < height) := by
  induction listed with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨firstBelow, restSorted⟩ := List.pairwise_cons.mp sorted
      by_cases low : first ≤ cursor
      · have notAbove : ¬ cursor < first := by omega
        simp [low, notAbove, ih restSorted]
      · have above : cursor < first := by omega
        have allAbove : ∀ height ∈ rest, cursor < height := fun height member => by
          have := firstBelow height member; omega
        have noneLow : rest.filter (fun height => height ≤ cursor) = [] :=
          List.filter_eq_nil_iff.mpr (by intro height member; have := allAbove height member; simp; omega)
        have allKept : rest.filter (fun height => cursor < height) = rest :=
          List.filter_eq_self.mpr (by intro height member; simpa using allAbove height member)
        simp [low, above, noneLow, allKept]

private theorem filterMap_congr' {A B : Type} {f g : A → Option B} : ∀ {list : List A},
    (∀ a ∈ list, f a = g a) → list.filterMap f = list.filterMap g
  | [], _ => rfl
  | first :: rest, same => by
      have ih := filterMap_congr' (list := rest) (fun a member => same a (List.mem_cons_of_mem _ member))
      simp only [List.filterMap_cons, same first List.mem_cons_self, ih]

/-- Positions read in order are a prefix. -/
theorem range_filterMap_getElem? {A : Type} (list : List A) : ∀ limit : Nat,
    (List.range limit).filterMap (fun i => list[i]?) = list.take limit
  | 0 => by simp
  | limit + 1 => by
      rw [List.range_succ, List.filterMap_append, range_filterMap_getElem? list limit, List.take_add_one]
      cases found : list[limit]? <;> simp [found]

/-- **The window read is exact.** Reading the count, bisecting for the cursor and then reading
`limit` positions in order yields exactly the first `limit` listed heights above the cursor. -/
theorem window_spec (listed : List Nat) (sorted : listed.Pairwise (· < ·)) (cursor limit : Nat) :
    (List.range limit).filterMap
        (fun i => itemOf listed (below (itemOf listed) cursor (belowFuel listed.length) 0 listed.length + 1 + i)) =
      (listed.filter (fun height => cursor < height)).take limit := by
  have split := below_spec listed sorted cursor (belowFuel listed.length) 0 listed.length (Nat.zero_le _)
    (Nat.le_refl _) (by simpa using lt_two_pow_belowFuel listed.length)
    (fun i height before _ => absurd before (Nat.not_lt_zero i))
    (fun i height beyond found => by
      rw [List.getElem?_eq_none beyond] at found; cases found)
  rw [split, ← drop_below_eq_filter listed sorted cursor, ← range_filterMap_getElem?]
  apply filterMap_congr'
  intro i _
  have position : (listed.filter (fun height => height ≤ cursor)).length + 1 + i - 1 =
      (listed.filter (fun height => height ≤ cursor)).length + i := by omega
  simp only [itemOf, List.getElem?_drop, position]
  split
  · omega
  · rfl

/-! ## The scan the index replaces

`scanFrom` is the shape of a journal read that walks every record: entries strictly above
`after`, the record at list position `i` taking height `start + i`. Where a record yields an
entry exactly when it belongs to the sequence, the scan is the listed heights above the
cursor, each read back at its height. -/

variable {R E : Type}

def scanFrom (entry : Nat → R → Option E) (after : Nat) : Nat → List R → List E
  | _, [] => []
  | height, record :: rest =>
      (if after < height then (entry height record).toList else []) ++
        scanFrom entry after (height + 1) rest

/-- The entry read back at a listed height. -/
def entryAt (entry : Nat → R → Option E) (start : Nat) (log : List R) (height : Nat) : Option E :=
  (log[height - start]?).bind (entry height)

private theorem entryAt_cons (entry : Nat → R → Option E) (start : Nat) (first : R) (rest : List R)
    (height : Nat) (above : start + 1 ≤ height) :
    entryAt entry start (first :: rest) height = entryAt entry (start + 1) rest height := by
  unfold entryAt
  have shift : height - start = (height - (start + 1)) + 1 := by omega
  rw [shift, List.getElem?_cons_succ]

/-- **The scan is the index read**: where a record yields an entry exactly when it belongs to
`seq`, scanning the log is filtering the sequence's heights by the cursor and reading each back. -/
theorem scanFrom_eq_heights (members : R → List S) (seq : S) (entry : Nat → R → Option E) (after : Nat) :
    ∀ (start : Nat) (log : List R),
      (∀ record ∈ log, ∀ height, (entry height record).isSome = true ↔ seq ∈ members record) →
      scanFrom entry after start log =
        ((heightsFrom seq start (log.map members)).filter (fun height => after < height)).filterMap
          (entryAt entry start log)
  | _, [], _ => by simp [scanFrom, heightsFrom]
  | start, first :: rest, exact => by
      have ih := scanFrom_eq_heights members seq entry after (start + 1) rest
        (fun record member => exact record (List.mem_cons_of_mem _ member))
      have tail : ((heightsFrom seq (start + 1) (rest.map members)).filter (fun height => after < height)).filterMap
            (entryAt entry start (first :: rest)) =
          ((heightsFrom seq (start + 1) (rest.map members)).filter (fun height => after < height)).filterMap
            (entryAt entry (start + 1) rest) := by
        apply filterMap_congr'
        intro height member
        exact entryAt_cons entry start first rest height
          (heightsFrom_bounds seq (start + 1) (rest.map members) height (List.mem_filter.mp member).1).1
      have here := exact first (List.mem_cons_self) start
      simp only [scanFrom, List.map_cons, heightsFrom]
      by_cases belongs : seq ∈ members first
      · obtain ⟨yielded, isSome⟩ := Option.isSome_iff_exists.mp (here.mpr belongs)
        simp only [belongs, ite_true, List.filter_cons]
        by_cases above : after < start
        · simp [above, isSome, entryAt, tail, ih]
        · simp [above, tail, ih]
      · have isNone : entry start first = none := by
          cases found : entry start first with
          | none => rfl
          | some yielded => exact absurd (here.mp (by simp [found])) belongs
        simp [belongs, isNone, tail, ih]

/-- Every listed height reads back an entry. -/
theorem entryAt_isSome (members : R → List S) (seq : S) (entry : Nat → R → Option E) :
    ∀ (start : Nat) (log : List R),
      (∀ record ∈ log, ∀ height, (entry height record).isSome = true ↔ seq ∈ members record) →
      ∀ height ∈ heightsFrom seq start (log.map members), (entryAt entry start log height).isSome = true := by
  intro start log exact height member
  obtain ⟨index, listed, found, at_, belongs⟩ := (mem_heightsFrom seq start (log.map members) height).mp member
  rw [List.getElem?_map] at found
  obtain ⟨record, inLog, rfl⟩ := Option.map_eq_some_iff.mp found
  have indexed : height - start = index := by omega
  unfold entryAt
  rw [indexed, inLog]
  exact (exact record (List.mem_of_getElem? inLog) height).mpr belongs

theorem filterMap_take_of_isSome {A B : Type} (f : A → Option B) : ∀ (list : List A) (limit : Nat),
    (∀ a ∈ list, (f a).isSome = true) → (list.filterMap f).take limit = (list.take limit).filterMap f
  | [], _, _ => by simp
  | _, 0, _ => by simp
  | first :: rest, limit + 1, all => by
      obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp (all first List.mem_cons_self)
      have ih := filterMap_take_of_isSome f rest limit (fun a member => all a (List.mem_cons_of_mem _ member))
      simp [found, ih]

/-- **A bounded read of the scan is the window's entries**: the first `limit` entries of the
scan are the entries read back at the first `limit` listed heights above the cursor. -/
theorem scanFrom_take (members : R → List S) (seq : S) (entry : Nat → R → Option E) (after limit start : Nat)
    (log : List R)
    (exact : ∀ record ∈ log, ∀ height, (entry height record).isSome = true ↔ seq ∈ members record) :
    (scanFrom entry after start log).take limit =
      (((heightsFrom seq start (log.map members)).filter (fun height => after < height)).take limit).filterMap
        (entryAt entry start log) := by
  rw [scanFrom_eq_heights members seq entry after start log exact]
  apply filterMap_take_of_isSome
  intro height member
  exact entryAt_isSome members seq entry start log exact height (List.mem_filter.mp member).1

/-- The records that belong, in order, are the records at the listed heights. -/
theorem filter_eq_heights (members : R → List S) (seq : S) : ∀ (start : Nat) (log : List R),
    log.filter (fun record => decide (seq ∈ members record)) =
      (heightsFrom seq start (log.map members)).filterMap (fun height => log[height - start]?)
  | _, [] => by simp [heightsFrom]
  | start, first :: rest => by
      have ih := filter_eq_heights members seq (start + 1) rest
      have tail : (heightsFrom seq (start + 1) (rest.map members)).filterMap
            (fun height => (first :: rest)[height - start]?) =
          (heightsFrom seq (start + 1) (rest.map members)).filterMap (fun height => rest[height - (start + 1)]?) := by
        apply filterMap_congr'
        intro height member
        have above := (heightsFrom_bounds seq (start + 1) (rest.map members) height member).1
        have shift : height - start = (height - (start + 1)) + 1 := by omega
        rw [shift, List.getElem?_cons_succ]
      simp only [List.map_cons, heightsFrom, List.filter_cons]
      by_cases belongs : seq ∈ members first
      · simp [belongs, tail, ih]
      · simp [belongs, tail, ih]

/-- The number of records that belong is the count. -/
theorem filter_length_eq_count (members : R → List S) (seq : S) (log : List R) :
    (log.filter (fun record => decide (seq ∈ members record))).length = count (log.map members) seq := by
  unfold count heights
  generalize 1 = start
  induction log generalizing start with
  | nil => simp [heightsFrom]
  | cons first rest ih =>
      simp only [List.map_cons, heightsFrom, List.filter_cons]
      by_cases belongs : seq ∈ members first <;> simp [belongs, ih (start + 1)]

theorem getLast?_filterMap_of_isSome {A B : Type} (f : A → Option B) : ∀ (list : List A),
    (∀ a ∈ list, (f a).isSome = true) → (list.filterMap f).getLast? = list.getLast?.bind f
  | [], _ => by simp
  | [only], all => by
      obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp (all only List.mem_cons_self)
      simp [found]
  | first :: second :: rest, all => by
      obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp (all first List.mem_cons_self)
      obtain ⟨next, foundNext⟩ := Option.isSome_iff_exists.mp
        (all second (List.mem_cons_of_mem _ List.mem_cons_self))
      have ih := getLast?_filterMap_of_isSome f (second :: rest)
        (fun a member => all a (List.mem_cons_of_mem _ member))
      rw [List.getLast?_cons_cons, ← ih]
      simp only [List.filterMap_cons, found, foundNext]
      rw [List.getLast?_cons_cons]

/-- **The newest member is the record at the last listed height.** -/
theorem filter_getLast? (members : R → List S) (seq : S) (start : Nat) (log : List R) :
    (log.filter (fun record => decide (seq ∈ members record))).getLast? =
      (heightsFrom seq start (log.map members)).getLast?.bind (fun height => log[height - start]?) := by
  rw [filter_eq_heights members seq start log]
  have all : ∀ height ∈ heightsFrom seq start (log.map members), (log[height - start]?).isSome = true := by
    intro height member
    obtain ⟨index, listed, found, at_, _⟩ := (mem_heightsFrom seq start (log.map members) height).mp member
    rw [List.getElem?_map] at found
    obtain ⟨record, inLog, _⟩ := Option.map_eq_some_iff.mp found
    have indexed : height - start = index := by omega
    rw [indexed, inLog]; rfl
  exact getLast?_filterMap_of_isSome _ _ all


/-! ## The view, maintained (`Theory.Retained`) -/

/-- The journal as a delta system: every record's sequences are admitted. -/
def system (S : Type) : Retained.DeltaSystem where
  State := List (List S)
  Delta := List S
  step := fun members journal => some (journal ++ [members])
  genesis := []

inductive Query (S : Type) where
  | count (seq : S)
  | item (seq : S) (position : Nat)

def Query.Answer : Query S → Type
  | .count _ => Nat
  | .item _ _ => Option Nat

/-- The recomputation: `count` and `item` over the whole journal. -/
def view (S : Type) [DecidableEq S] : Retained.View (List (List S)) where
  Q := Query S
  A := Query.Answer
  spec := fun journal query =>
    match query with
    | .count seq => count journal seq
    | .item seq position => item journal seq position

def Rows.answer (rows : Rows S) : (query : Query S) → query.Answer
  | .count seq => rows.count seq
  | .item seq position => rows.item seq position

/-- **The sequence rows are a maintained view of the journal.** -/
def maintained (S : Type) [DecidableEq S] : Retained.Maintained (system S) (view S) where
  Rep := Rows S
  Holds := Holds
  init := Rows.empty
  init_holds := empty_holds
  fetch := fun rows query => (rows.answer query, rows)
  fetch_sound := by
    intro rows journal holds query
    refine ⟨?_, holds⟩
    cases query with
    | count seq => exact holds.2.1 seq
    | item seq position => exact holds.2.2 seq position
  advance := Rows.advance
  advance_holds := by
    intro rows journal journal' members holds stepped
    cases stepped
    exact advance_holds members holds

/-- **The keystone** (`index_from_replay`): after any run of records from the empty journal,
the kept rows answer every count and position as the recomputation over that journal does. -/
theorem index_from_replay (records : List (List S)) (query : Query S) :
    (maintained S).ask ((maintained S).advanceAll records (maintained S).init) query =
      (view S).spec records query := by
  have run : ∀ (records journal : List (List S)),
      (system S).run journal records = some (journal ++ records) := by
    intro records
    induction records with
    | nil =>
        intro journal
        show some journal = some (journal ++ [])
        rw [List.append_nil]
    | cons first rest ih =>
        intro journal
        have step : (system S).run journal (first :: rest) = (system S).run (journal ++ [first]) rest := rfl
        have tail := ih (journal ++ [first])
        have joined : journal ++ [first] ++ rest = journal ++ first :: rest := by simp
        exact step.trans (tail.trans (congrArg some joined))
  have ran : (system S).run (system S).genesis records = some records := run records []
  exact (maintained S).reachable_eq_recompute records ran query

namespace Example

/-- Three records: the first and third belong to sequence 7, the second to 9. -/
def journal : List (List Nat) := [[7], [9], [7, 7]]

def rows : Rows Nat := Rows.advance [7, 7] (Rows.advance [9] (Rows.advance [7] Rows.empty))

/-- Satisfiable: the advanced rows answer the count, the newest member and the window above
height 1 of sequence 7, and each is the scan's answer. -/
theorem reads : rows.count 7 = 2 ∧ rows.item 7 (rows.count 7) = some 3 ∧
    (List.range 5).filterMap (fun i => rows.item 7 (below (rows.item 7) 1 (belowFuel (rows.count 7)) 0
      (rows.count 7) + 1 + i)) = [3] ∧
    count journal 7 = 2 ∧ (heights journal 7).filter (fun height => 1 < height) = [3] := by
  decide

/-- Teeth: rows that were not advanced by the third record still answer 1. -/
theorem stale_refuted :
    (Rows.advance [9] (Rows.advance [7] Rows.empty)).count 7 ≠ count journal 7 := by
  decide

/-- Teeth: a member at the cursor is not in the window above it. -/
theorem window_excludes_cursor :
    (List.range 5).filterMap (fun i => rows.item 7 (below (rows.item 7) 3 (belowFuel (rows.count 7)) 0
      (rows.count 7) + 1 + i)) = [] := by
  decide

end Example

#assert_axioms mem_distinct
#assert_axioms heights_append
#assert_axioms mem_heightsFrom
#assert_axioms heightsFrom_sorted
#assert_axioms count_append
#assert_axioms item_append
#assert_axioms item_count
#assert_axioms writes_length
#assert_axioms advance_holds
#assert_axioms below_spec
#assert_axioms window_spec
#assert_axioms scanFrom_take
#assert_axioms filter_length_eq_count
#assert_axioms filter_getLast?
#assert_axioms index_from_replay
#assert_axioms Example.reads
#assert_axioms Example.stale_refuted
#assert_axioms Example.window_excludes_cursor

end Minidregg.Theory.JournalSequences
