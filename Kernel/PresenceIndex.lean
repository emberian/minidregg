/-
# Kernel.PresenceIndex — who acted where, and when (PLACE §2.5, K-INDEX)

Two maps the world keeps, both functions of the accepted log:

* `lastSeen : (cell, subject) ↦ height` — the greatest log height at which a
  record signed by `subject` wrote `cell`;
* `touched : cell ↦ height` — the greatest log height at which any record
  wrote `cell`.

Heights are 1-based log positions: entry `h` is `accepted[h - 1]`, the count the
host's clock (`clockOf`) and the checkpoint cadence already use.

**Where it lives.** The index is `ofRecords image.accepted`, cached on the
loaded image (`DurableReceiverIO.Loaded.index`, exact by `indexExact`) and
advanced by `Index.admit` on every append. It is not trusted state and not a
second store: the log that determines it is MAC-chained, committed by the world
root's system slot, and read whole on every open, so a checkpoint carrying a
copy would add a trusted duplicate and nothing else. Not an authority-cell
plane: D2 took every field write off the authority cell (26,111 → 515 charged
bytes per write), and a per-turn index write would put it back. Not the
`World` system cell: the host does not run `World.step` (the Turn cutover is
undone), so a `SysSpace` namespace there would be a model-only twin.

**What it gives** (`Kernel.NativeObservationController`): `who R` = the
members of `R` with the greatest `lastSeen` over cells under `R` the reader
covers; `since R H` = the log entries above `H` that wrote such cells.
-/
import Kernel.DurableReceiver

namespace Minidregg.Kernel.PresenceIndex

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver

set_option autoImplicit false

/-! ## Finite maps with unique keys -/

section Map

variable {κ : Type} [DecidableEq κ]

/-- Look a key up in an association list (first match). -/
def get : List (κ × Nat) → κ → Option Nat
  | [], _ => none
  | entry :: rest, key => if entry.1 = key then some entry.2 else get rest key

/-- Overwrite a key in place, or append it. Keys stay unique. -/
def put : List (κ × Nat) → κ → Nat → List (κ × Nat)
  | [], key, value => [(key, value)]
  | entry :: rest, key, value =>
      if entry.1 = key then (key, value) :: rest else entry :: put rest key value

theorem get_put (map : List (κ × Nat)) (key key' : κ) (value : Nat) :
    get (put map key value) key' = if key = key' then some value else get map key' := by
  induction map with
  | nil => simp [put, get]
  | cons entry rest ih =>
      by_cases here : entry.1 = key
      · by_cases same : key = key'
        · simp [put, get, here, same]
        · simp [put, get, here, same]
      · by_cases same : key = key'
        · subst same
          simp [put, get, here, ih]
        · simp [put, get, here, same, ih]

/-- Write one value at every key of a list. -/
def putAll (map : List (κ × Nat)) (keys : List κ) (value : Nat) : List (κ × Nat) :=
  keys.foldl (fun acc key => put acc key value) map

theorem get_putAll (map : List (κ × Nat)) (keys : List κ) (value : Nat) (key' : κ) :
    get (putAll map keys value) key' = if key' ∈ keys then some value else get map key' := by
  induction keys generalizing map with
  | nil => simp [putAll]
  | cons key rest ih =>
      have step : putAll map (key :: rest) value = putAll (put map key value) rest value := rfl
      rw [step, ih, get_put]
      by_cases inRest : key' ∈ rest
      · simp [inRest]
      · by_cases same : key = key'
        · subst same; simp
        · simp [inRest, same, Ne.symm same]

end Map

/-! ## The index -/

/-- The presence index: `lastSeen (cell, subject)` and `touched cell`. -/
structure Index where
  lastSeen : List ((CellId × SubjectId) × Nat)
  touched : List (CellId × Nat)
  deriving DecidableEq, Repr

def Index.empty : Index := ⟨[], []⟩

/-- The cells a record writes. -/
def cellsOf (record : IntentRecord) : List CellId := record.writes.map DataWrite.cellId

/-- Admit one record at log height `height`. -/
def Index.admit (index : Index) (height : Nat) (record : IntentRecord) : Index where
  lastSeen :=
    match record.subject with
    | none => index.lastSeen
    | some subject => putAll index.lastSeen ((cellsOf record).map fun cell => (cell, subject)) height
  touched := putAll index.touched (cellsOf record) height

/-- Fold the records after height `start`; the first is admitted at `start + 1`. -/
def Index.extend : Index → Nat → List IntentRecord → Index
  | index, _, [] => index
  | index, start, record :: records => (index.admit (start + 1) record).extend (start + 1) records

/-- The index of a log. -/
def ofRecords (records : List IntentRecord) : Index := Index.empty.extend 0 records

def Index.lastSeenAt (index : Index) (cell : CellId) (subject : SubjectId) : Option Nat :=
  get index.lastSeen (cell, subject)

def Index.touchedAt (index : Index) (cell : CellId) : Option Nat :=
  get index.touched cell

theorem Index.extend_append (index : Index) (start : Nat) (left right : List IntentRecord) :
    index.extend start (left ++ right) = (index.extend start left).extend (start + left.length) right := by
  induction left generalizing index start with
  | nil => rfl
  | cons record rest ih =>
      show (index.admit (start + 1) record).extend (start + 1) (rest ++ right) = _
      rw [ih]
      show _ = ((index.admit (start + 1) record).extend (start + 1) rest).extend _ right
      congr 1
      simp only [List.length_cons]
      omega

/-- The index of a longer log is the shorter log's index advanced by the
suffix: what a resumed session and a checkpoint suffix replay both compute. -/
theorem ofRecords_append (left right : List IntentRecord) :
    ofRecords (left ++ right) = (ofRecords left).extend left.length right := by
  unfold ofRecords
  rw [Index.extend_append, Nat.zero_add]

theorem ofRecords_snoc (log : List IntentRecord) (record : IntentRecord) :
    ofRecords (log ++ [record]) = (ofRecords log).admit (log.length + 1) record := by
  rw [ofRecords_append]
  rfl

/-! ## Exactness: each map is the greatest height of its event -/

/-- Event `P` happens at log height `height` (1-based). -/
def Occurs (P : IntentRecord → Prop) (log : List IntentRecord) (height : Nat) : Prop :=
  ∃ index record, height = index + 1 ∧ log[index]? = some record ∧ P record

theorem occurs_le_length {P : IntentRecord → Prop} {log : List IntentRecord} {height : Nat}
    (occurs : Occurs P log height) : height ≤ log.length := by
  obtain ⟨index, record, rfl, found, _⟩ := occurs
  have := (List.getElem?_eq_some_iff.mp found).1
  omega

theorem occurs_append_left {P : IntentRecord → Prop} {log : List IntentRecord} {height : Nat}
    (occurs : Occurs P log height) (more : List IntentRecord) : Occurs P (log ++ more) height := by
  obtain ⟨index, record, rfl, found, holds⟩ := occurs
  have bound := (List.getElem?_eq_some_iff.mp found).1
  exact ⟨index, record, rfl, by rw [List.getElem?_append_left bound]; exact found, holds⟩

theorem occurs_snoc {P : IntentRecord → Prop} (log : List IntentRecord) (record : IntentRecord)
    (height : Nat) :
    Occurs P (log ++ [record]) height ↔ Occurs P log height ∨ (height = log.length + 1 ∧ P record) := by
  constructor
  · rintro ⟨index, found, rfl, at_, holds⟩
    by_cases bound : index < log.length
    · rw [List.getElem?_append_left bound] at at_
      exact Or.inl ⟨index, found, rfl, at_, holds⟩
    · rw [List.getElem?_append_right (by omega)] at at_
      have zero : index - log.length = 0 := by
        cases h : index - log.length with
        | zero => rfl
        | succ n => rw [h] at at_; simp at at_
      rw [zero] at at_
      simp only [List.getElem?_cons_zero, Option.some.injEq] at at_
      subst at_
      exact Or.inr ⟨by omega, holds⟩
  · rintro (occurs | ⟨rfl, holds⟩)
    · exact occurs_append_left occurs [record]
    · exact ⟨log.length, record, rfl, by simp, holds⟩

/-- A snoc-recurrent lookup is exactly "the greatest height of the event".
Both index maps are instances. -/
theorem greatest_of_snoc (P : IntentRecord → Prop) [DecidablePred P]
    (lookup : List IntentRecord → Option Nat) (nil : lookup [] = none)
    (snoc : ∀ log record, lookup (log ++ [record]) =
      if P record then some (log.length + 1) else lookup log) :
    ∀ log height, lookup log = some height ↔
      (Occurs P log height ∧ ∀ other, Occurs P log other → other ≤ height) := by
  intro log
  induction log using List.reverseRecOn with
  | nil =>
      intro height
      simp only [nil, reduceCtorEq, false_iff, not_and]
      rintro ⟨index, record, _, found, _⟩
      simp at found
  | append_singleton log record ih =>
      intro height
      rw [snoc]
      by_cases holds : P record
      · rw [if_pos holds]
        constructor
        · intro same
          cases Option.some.inj same
          refine ⟨(occurs_snoc log record _).mpr (Or.inr ⟨rfl, holds⟩), fun other occurs => ?_⟩
          have := occurs_le_length occurs
          simpa using this
        · rintro ⟨occurs, greatest⟩
          have top := greatest (log.length + 1) ((occurs_snoc log record _).mpr (Or.inr ⟨rfl, holds⟩))
          have bound := occurs_le_length occurs
          simp only [List.length_append, List.length_singleton] at bound
          exact congrArg some (by omega)
      · rw [if_neg holds, ih]
        have strip : ∀ other, Occurs P (log ++ [record]) other ↔ Occurs P log other := by
          intro other
          rw [occurs_snoc]
          exact ⟨fun h => h.elim id (fun h => absurd h.2 holds), Or.inl⟩
        simp only [strip]

theorem none_of_snoc (P : IntentRecord → Prop) [DecidablePred P]
    (lookup : List IntentRecord → Option Nat) (nil : lookup [] = none)
    (snoc : ∀ log record, lookup (log ++ [record]) =
      if P record then some (log.length + 1) else lookup log) :
    ∀ log, lookup log = none ↔ ∀ height, ¬ Occurs P log height := by
  intro log
  induction log using List.reverseRecOn with
  | nil =>
      simp only [nil, true_iff]
      rintro _ ⟨index, record, _, found, _⟩
      simp at found
  | append_singleton log record ih =>
      rw [snoc]
      by_cases holds : P record
      · rw [if_pos holds]
        simp only [reduceCtorEq, false_iff, not_forall, not_not]
        exact ⟨_, (occurs_snoc log record _).mpr (Or.inr ⟨rfl, holds⟩)⟩
      · rw [if_neg holds, ih]
        simp only [occurs_snoc, holds, and_false, or_false]

/-- A record signed by `subject` wrote `cell`. -/
def SignedWrite (cell : CellId) (subject : SubjectId) (record : IntentRecord) : Prop :=
  record.subject = some subject ∧ cell ∈ cellsOf record

instance (cell : CellId) (subject : SubjectId) : DecidablePred (SignedWrite cell subject) :=
  fun record => by unfold SignedWrite; infer_instance

/-- A record wrote `cell`. -/
def Wrote (cell : CellId) (record : IntentRecord) : Prop := cell ∈ cellsOf record

instance (cell : CellId) : DecidablePred (Wrote cell) :=
  fun record => by unfold Wrote; infer_instance

theorem lastSeen_snoc (log : List IntentRecord) (record : IntentRecord)
    (cell : CellId) (subject : SubjectId) :
    (ofRecords (log ++ [record])).lastSeenAt cell subject =
      if SignedWrite cell subject record then some (log.length + 1)
      else (ofRecords log).lastSeenAt cell subject := by
  rw [ofRecords_snoc]
  unfold Index.lastSeenAt Index.admit
  split
  next unsigned =>
    have absent : ¬ SignedWrite cell subject record := fun h => by
      have signed := h.1
      rw [unsigned] at signed
      cases signed
    rw [if_neg absent]
  next signer signed =>
    rw [get_putAll]
    by_cases hit : SignedWrite cell subject record
    · obtain ⟨same, member⟩ := hit
      rw [signed] at same
      cases same
      rw [if_pos (List.mem_map.mpr ⟨cell, member, rfl⟩), if_pos ⟨signed, member⟩]
    · rw [if_neg hit, if_neg]
      intro member
      obtain ⟨written, inCells, pair⟩ := List.mem_map.mp member
      cases pair
      exact hit ⟨signed, inCells⟩

theorem touched_snoc (log : List IntentRecord) (record : IntentRecord) (cell : CellId) :
    (ofRecords (log ++ [record])).touchedAt cell =
      if Wrote cell record then some (log.length + 1) else (ofRecords log).touchedAt cell := by
  rw [ofRecords_snoc]
  unfold Index.touchedAt Index.admit
  rw [get_putAll]
  by_cases member : cell ∈ cellsOf record
  · rw [if_pos member, if_pos (show Wrote cell record from member)]
  · rw [if_neg member, if_neg (show ¬ Wrote cell record from member)]

/-- **`lastSeen` is exact** (PLACE §2.5; DATAMODEL 4.9's shape): the index
names `h` for `(cell, subject)` iff a record signed by `subject` wrote `cell`
at height `h` and at no greater height. A tampered index disagrees with the
fold, which is what makes `who` refutable. -/
theorem lastSeen_exact (log : List IntentRecord) (cell : CellId) (subject : SubjectId) (height : Nat) :
    (ofRecords log).lastSeenAt cell subject = some height ↔
      (Occurs (SignedWrite cell subject) log height ∧
        ∀ other, Occurs (SignedWrite cell subject) log other → other ≤ height) :=
  greatest_of_snoc (SignedWrite cell subject) (fun log => (ofRecords log).lastSeenAt cell subject) rfl
    (fun log record => lastSeen_snoc log record cell subject) log height

theorem lastSeen_none (log : List IntentRecord) (cell : CellId) (subject : SubjectId) :
    (ofRecords log).lastSeenAt cell subject = none ↔
      ∀ height, ¬ Occurs (SignedWrite cell subject) log height :=
  none_of_snoc (SignedWrite cell subject) (fun log => (ofRecords log).lastSeenAt cell subject) rfl
    (fun log record => lastSeen_snoc log record cell subject) log

/-- **`touched` is exact**: the greatest height at which any record wrote `cell`. -/
theorem touched_exact (log : List IntentRecord) (cell : CellId) (height : Nat) :
    (ofRecords log).touchedAt cell = some height ↔
      (Occurs (Wrote cell) log height ∧ ∀ other, Occurs (Wrote cell) log other → other ≤ height) :=
  greatest_of_snoc (Wrote cell) (fun log => (ofRecords log).touchedAt cell) rfl
    (fun log record => touched_snoc log record cell) log height

/-- **Monotone**: extending the log never lowers or removes an entry. -/
theorem index_monotone (log more : List IntentRecord) (cell : CellId) (subject : SubjectId)
    {height : Nat} (seen : (ofRecords log).lastSeenAt cell subject = some height) :
    ∃ later, (ofRecords (log ++ more)).lastSeenAt cell subject = some later ∧ height ≤ later := by
  have occurs := ((lastSeen_exact log cell subject height).mp seen).1
  have longer := occurs_append_left occurs more
  cases found : (ofRecords (log ++ more)).lastSeenAt cell subject with
  | none => exact absurd longer ((lastSeen_none _ cell subject).mp found height)
  | some later =>
      exact ⟨later, rfl, ((lastSeen_exact _ cell subject later).mp found).2 height longer⟩

theorem touched_monotone (log more : List IntentRecord) (cell : CellId)
    {height : Nat} (seen : (ofRecords log).touchedAt cell = some height) :
    ∃ later, (ofRecords (log ++ more)).touchedAt cell = some later ∧ height ≤ later := by
  have occurs := ((touched_exact log cell height).mp seen).1
  have longer := occurs_append_left occurs more
  cases found : (ofRecords (log ++ more)).touchedAt cell with
  | none =>
      exact absurd longer ((none_of_snoc (Wrote cell) (fun log => (ofRecords log).touchedAt cell) rfl
        (fun log record => touched_snoc log record cell) _).mp found height)
  | some later => exact ⟨later, rfl, ((touched_exact _ cell later).mp found).2 height longer⟩

/-! ## Poles -/

namespace Example

def write (cell : Nat) : DataWrite := ⟨⟨cell⟩, ⟨0⟩, ⟨0⟩, []⟩
def event : StableEvent := ⟨0, ⟨0⟩, ⟨0⟩, []⟩
def turn (tx cell : Nat) (subject : Option Nat) : IntentRecord :=
  ⟨⟨tx⟩, [write cell], [], [], fun _ => 0, event, subject.map SubjectId.mk⟩

/-- A writes the room at 1, B writes it at 2, an unsigned settlement at 3. -/
def log : List IntentRecord := [turn 1 7 (some 1), turn 2 7 (some 2), turn 3 7 none]

theorem a_seen_at_one : (ofRecords log).lastSeenAt ⟨7⟩ ⟨1⟩ = some 1 := by decide
theorem b_seen_at_two : (ofRecords log).lastSeenAt ⟨7⟩ ⟨2⟩ = some 2 := by decide
theorem third_never_seen : (ofRecords log).lastSeenAt ⟨7⟩ ⟨3⟩ = none := by decide
theorem room_touched_at_three : (ofRecords log).touchedAt ⟨7⟩ = some 3 := by decide
theorem other_cell_untouched : (ofRecords log).touchedAt ⟨8⟩ = none := by decide

end Example

end Minidregg.Kernel.PresenceIndex

/-- info: 'Minidregg.Kernel.PresenceIndex.lastSeen_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.PresenceIndex.lastSeen_exact
/-- info: 'Minidregg.Kernel.PresenceIndex.lastSeen_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.PresenceIndex.lastSeen_none
/-- info: 'Minidregg.Kernel.PresenceIndex.touched_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.PresenceIndex.touched_exact
/-- info: 'Minidregg.Kernel.PresenceIndex.index_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.PresenceIndex.index_monotone
/-- info: 'Minidregg.Kernel.PresenceIndex.touched_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.PresenceIndex.touched_monotone
/-- info: 'Minidregg.Kernel.PresenceIndex.ofRecords_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.PresenceIndex.ofRecords_append
/-- info: 'Minidregg.Kernel.PresenceIndex.Example.b_seen_at_two' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.PresenceIndex.Example.b_seen_at_two
