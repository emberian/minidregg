/-
# Kernel.DurableCheckpoint — resume a durable image from a materialized state

A checkpoint is the statement "the replay of the first `h` accepted records is
this state" (DATAMODEL §3.3, §4.4). The host reopens by materializing that
state and replaying only the records after `h`; the genesis replay survives as
`Image.restore` (and, with signature re-admission, as the operator `audit`).

What a checkpoint cannot certify is that the prefix was correctly admitted.
That is trust in the host's own past execution, authenticated by the host-held
MAC in `Compiler.DurableCheckpointCodec` (DATAMODEL §6 Q1): an attacker who can
forge that MAC can already forge the host's receipts, so no new trust is
introduced. The theorems below say what the checkpoint buys under that trust:

* `resume_sound`: an honest checkpoint (its materialized state IS the prefix
  replay) resumes to exactly the genesis replay. It is `replay_append` — the
  one-model form of B2's `checkpoint_suffix` for the host's current record type.
* `resume_genesis`: the seed is the height-0 checkpoint.
* `dishonest_checkpoint_diverges`: the honesty premise is load-bearing; a state
  that is not the prefix replay resumes to a different world.

The materialized state carries every identifier ever seeded or written, the
consumed nullifiers and the remaining allowance. Journal and history are not
state: they are recovered from the retained log prefix, which the MAC chain in
the codec authenticates.
-/
import Kernel.DurableReceiver

namespace Minidregg.Kernel.DurableCheckpoint

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver

set_option autoImplicit false

/-- Erased replay identity of a stored record, computed without re-checking
its roots. For a bound record it is exactly the bound intent's erasure. -/
def IntentRecord.erase (record : IntentRecord) :
    Intent TransactionId CellId StableNullifier ReplayEnvelope where
  transactionId := record.transactionId
  rootWrites := record.writes.map fun write =>
    { cellId := write.cellId
      expectedPre := write.expectedPre
      exactPost := write.exactPost }
  nullifiers := record.nullifiers
  exactCharge := record.exactCharge
  event := { writes := record.writes, readGuards := record.readGuards, event := record.event }

theorem IntentRecord.erase_bind {rootBytes : List UInt8 → Digest} {record : IntentRecord}
    {intent : DataIntent rootBytes} (bound : record.bind? rootBytes = some intent) :
    intent.erase = IntentRecord.erase record := by
  have exact := IntentRecord.bind_exact bound
  subst exact
  rfl

/-- The materialized state at a checkpoint height: the cells and the
remaining allowance. The consumed nullifiers are NOT state: like the journal and
the history they are a function of the accepted prefix (`State.snapshot`), so a
checkpoint never carries them (KN2-STORE-OPEN: they were most of a checkpoint's
bytes) and nothing unverified can supply them. -/
structure State where
  absentBytes : List UInt8
  cells : List (CellId × List UInt8)
  available : Charge

/-- The genesis state: the seed. -/
def State.ofSeed (seed : Seed) : State :=
  ⟨seed.absentBytes, seed.cells, seed.available⟩

/-- Root table computed once per materialization; each entry's root is the
root function of its own bytes, by construction. -/
def rootTable (rootBytes : List UInt8 → Digest) (cells : List (CellId × List UInt8)) :
    List (CellId × List UInt8 × Digest) :=
  cells.map fun cell => (cell.1, cell.2, rootBytes cell.2)

def tableLookup (cellId : CellId) :
    List (CellId × List UInt8 × Digest) → Option (List UInt8 × Digest)
  | [] => none
  | (identifier, bytes, root) :: rest =>
      if identifier = cellId then some (bytes, root) else tableLookup cellId rest

theorem tableLookup_rootTable (rootBytes : List UInt8 → Digest)
    (cells : List (CellId × List UInt8)) (cellId : CellId) :
    tableLookup cellId (rootTable rootBytes cells) =
      (Seed.lookup cells cellId).map fun bytes => (bytes, rootBytes bytes) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
      obtain ⟨identifier, bytes⟩ := cell
      by_cases same : identifier = cellId
      · simp [rootTable, tableLookup, Seed.lookup, same]
      · simp only [rootTable, List.map_cons, tableLookup, Seed.lookup, same, ↓reduceIte]
        exact ih

/-- The snapshot at the checkpoint. Journal (newest first) and history
(chronological) come from the retained prefix exactly as `install` builds them. -/
def State.snapshot (rootBytes : List UInt8 → Digest) (state : State)
    (prefixRecords : List IntentRecord) : DataSnapshot rootBytes :=
  let table := rootTable rootBytes state.cells
  let absentRoot := rootBytes state.absentBytes
  let spent := prefixRecords.flatMap IntentRecord.nullifiers
  { model :=
      { roots := fun cellId =>
          match tableLookup cellId table with
          | some entry => entry.2
          | none => absentRoot
        consumed := fun nullifier => decide (nullifier ∈ spent)
        available := state.available
        history := prefixRecords.map fun record => (IntentRecord.erase record).event
        journal := (prefixRecords.map fun record =>
          (record.transactionId, IntentRecord.erase record)).reverse }
    canonicalBytes := fun cellId => (Seed.lookup state.cells cellId).getD state.absentBytes
    coherent := by
      intro cellId
      show rootBytes ((Seed.lookup state.cells cellId).getD state.absentBytes) =
        match tableLookup cellId (rootTable rootBytes state.cells) with
        | some entry => entry.2
        | none => rootBytes state.absentBytes
      rw [tableLookup_rootTable]
      cases Seed.lookup state.cells cellId <;> rfl }

/-- A checkpoint state is admissible for an image when its identifiers are
distinct, its fresh-identifier bytes are the seed's, and every identifier it
carries is enumerable in the image (seeded or written). -/
def State.Admissible (image : Image) (state : State) : Prop :=
  (state.cells.map Prod.fst).Nodup ∧ state.absentBytes = image.seed.absentBytes ∧
    ∀ cellId ∈ state.cells.map Prod.fst, cellId ∈ image.cellIds

/-- Admissibility against an identifier list given once. -/
def State.admissibleAgainst (ids : List CellId) (absent : List UInt8) (state : State) : Bool :=
  decide (state.cells.map Prod.fst).Nodup && decide (state.absentBytes = absent) &&
    (state.cells.map Prod.fst).all fun cellId => decide (cellId ∈ ids)

theorem State.admissibleAgainst_iff (image : Image) (state : State) :
    state.admissibleAgainst image.cellIds image.seed.absentBytes = true ↔ state.Admissible image := by
  simp [State.admissibleAgainst, State.Admissible, List.all_eq_true, and_assoc]

/-- Decided with the image's identifiers enumerated ONCE. The derived instance
re-enumerated `image.cellIds` (an `eraseDups` over every write in the log) for
each checkpoint cell: measured 17.5 s per `resume` at 2005 records and 1018
cells, paid by every cold open and every checkpoint rebase. -/
instance (image : Image) (state : State) : Decidable (state.Admissible image) :=
  decidable_of_iff _ (State.admissibleAgainst_iff image state)

/-- Resume: materialize the checkpoint at `height`, replay the records after
it. An inadmissible state refuses, as `Image.restore` refuses a duplicated seed. -/
def resume (rootBytes : List UInt8 → Digest) (image : Image) (height : Nat)
    (state : State) : Option (DataSnapshot rootBytes) :=
  if state.Admissible image then
    replay rootBytes (state.snapshot rootBytes (image.accepted.take height))
      (image.accepted.drop height)
  else none

theorem mem_cellIds_of_seed {image : Image} {cellId : CellId}
    (member : cellId ∈ image.seed.cells.map Prod.fst) : cellId ∈ image.cellIds := by
  unfold Image.cellIds
  exact List.mem_eraseDups.mpr (List.mem_append_left _ member)

theorem mem_cellIds_append {rootBytes : List UInt8 → Digest} {image : Image}
    {intent : DataIntent rootBytes} {cellId : CellId}
    (member : cellId ∈ image.cellIds) : cellId ∈ (image.append intent).cellIds := by
  unfold Image.cellIds at member ⊢
  rw [List.mem_eraseDups] at member ⊢
  simp only [Image.append, List.flatMap_append, List.mem_append] at member ⊢
  rcases member with seeded | written
  · exact Or.inl seeded
  · exact Or.inr (Or.inl written)

theorem ofSeed_admissible (image : Image) (valid : (image.seed.cells.map Prod.fst).Nodup) :
    (State.ofSeed image.seed).Admissible image :=
  ⟨valid, rfl, fun _ member => mem_cellIds_of_seed member⟩

/-- An identifier outside the image's support has the seed's fresh bytes in
every resumed snapshot, whatever admissible checkpoint it resumed from. -/
theorem resume_outside_support (rootBytes : List UInt8 → Digest) (image : Image)
    (height : Nat) (state : State) (snapshot : DataSnapshot rootBytes)
    (resumed : resume rootBytes image height state = some snapshot)
    (cellId : CellId) (missing : cellId ∉ image.cellIds) :
    snapshot.canonicalBytes cellId = image.seed.absentBytes := by
  unfold resume at resumed
  split at resumed
  next admissible =>
    obtain ⟨_, absent, support⟩ := admissible
    have notWritten : cellId ∉ (image.accepted.drop height).flatMap
        (fun record => record.writes.map DataWrite.cellId) := by
      intro written
      apply missing
      unfold Image.cellIds
      rw [List.mem_eraseDups]
      refine List.mem_append_right _ ?_
      obtain ⟨record, inDrop, inWrites⟩ := List.mem_flatMap.mp written
      exact List.mem_flatMap.mpr ⟨record, List.mem_of_mem_drop inDrop, inWrites⟩
    rw [replay_outside_support rootBytes _ _ cellId notWritten snapshot resumed]
    have notState : cellId ∉ state.cells.map Prod.fst := fun member => missing (support _ member)
    simp [State.snapshot, Seed.lookup_missing state.cells cellId notState, absent]
  next => simp at resumed

theorem ofSeed_snapshot (rootBytes : List UInt8 → Digest) (seed : Seed) :
    (State.ofSeed seed).snapshot rootBytes [] = seed.snapshot rootBytes := by
  simp only [State.snapshot, State.ofSeed, Seed.snapshot]
  congr 1
  · congr 1
    · funext cellId
      rw [tableLookup_rootTable]
      cases Seed.lookup seed.cells cellId <;> rfl

/-- The seed is the height-0 checkpoint: resuming it IS the genesis replay. -/
theorem resume_genesis (rootBytes : List UInt8 → Digest) (image : Image) :
    resume rootBytes image 0 (State.ofSeed image.seed) = image.restore rootBytes := by
  unfold resume Image.restore
  by_cases valid : (image.seed.cells.map Prod.fst).Nodup
  · rw [if_pos (ofSeed_admissible image valid), if_pos valid]
    simp only [List.take_zero, List.drop_zero, ofSeed_snapshot]
  · have notAdmissible : ¬ (State.ofSeed image.seed).Admissible image :=
      fun admissible => valid admissible.1
    rw [if_neg notAdmissible, if_neg valid]

/-- **Checkpoint soundness** (DATAMODEL §4.4 for the host's record type). If
the checkpoint's materialized state is the replay of the prefix it claims,
resuming from it is exactly the replay from genesis. -/
theorem resume_sound (rootBytes : List UInt8 → Digest) (image : Image) (height : Nat)
    (state : State) (atHeight : DataSnapshot rootBytes)
    (seedValid : (image.seed.cells.map Prod.fst).Nodup)
    (stateValid : state.Admissible image)
    (prefixReplay : replay rootBytes (image.seed.snapshot rootBytes)
      (image.accepted.take height) = some atHeight)
    (honest : state.snapshot rootBytes (image.accepted.take height) = atHeight) :
    resume rootBytes image height state = image.restore rootBytes := by
  unfold resume Image.restore
  rw [if_pos stateValid, if_pos seedValid]
  conv => rhs; rw [← List.take_append_drop height image.accepted]
  rw [replay_append, prefixReplay, Option.bind_some, honest]

/-- Appending a record the resumed snapshot accepts extends the resume by
exactly the executor's next snapshot. This is what lets a live session keep
its resumed state across appends without reopening. -/
theorem resume_append (rootBytes : List UInt8 → Digest) (image : Image) (height : Nat)
    (state : State) (before next : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (withinLog : height ≤ image.accepted.length)
    (resumed : resume rootBytes image height state = some before)
    (accepted : DurableDataIntent.execute .complete before intent = .accepted next) :
    resume rootBytes (image.append intent) height state = some next := by
  unfold resume at resumed ⊢
  split at resumed
  next valid =>
    have stillValid : state.Admissible (image.append intent) :=
      ⟨valid.1, valid.2.1, fun cellId member => mem_cellIds_append (valid.2.2 cellId member)⟩
    rw [if_pos stillValid]
    simp only [Image.append, List.take_append_of_le_length withinLog,
      List.drop_append_of_le_length withinLog, replay_append, resumed, Option.bind_some]
    simp [replay, IntentRecord.bind_ofIntent, accepted]
  next => simp at resumed

/-- A prepared append: the shared executor accepted the intent at the resumed
snapshot, and the appended image resumes to exactly its next snapshot. No
independent post image, root or journal can be substituted. -/
structure Ready (rootBytes : List UInt8 → Digest) (image : Image) (height : Nat)
    (state : State) (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes) where
  next : DataSnapshot rootBytes
  executed : DurableDataIntent.execute .complete before intent = .accepted next
  resumed : resume rootBytes (image.append intent) height state = some next

/-- The receiver calls the shared executor at the resumed snapshot. A stale
prepared append after a failed CAS is never retried: the caller reloads. -/
def prepare {rootBytes : List UInt8 → Digest} (image : Image) (height : Nat) (state : State)
    (before : DataSnapshot rootBytes) (withinLog : height ≤ image.accepted.length)
    (resumed : resume rootBytes image height state = some before)
    (intent : DataIntent rootBytes) :
    Sum (Ready rootBytes image height state before intent) (Outcome rootBytes) :=
  match executed : DurableDataIntent.execute .complete before intent with
  | .accepted next =>
      .inl ⟨next, executed,
        resume_append rootBytes image height state before next intent withinLog resumed executed⟩
  | outcome => .inr outcome

/-- The state a checkpoint at the head of `image` materializes: every
enumerable identifier with its current bytes, every consumed nullifier, the
remaining allowance. -/
def State.ofSnapshot {rootBytes : List UInt8 → Digest} (image : Image)
    (snapshot : DataSnapshot rootBytes) : State :=
  ⟨image.seed.absentBytes,
    image.cellIds.map fun cellId => (cellId, snapshot.canonicalBytes cellId),
    snapshot.model.available⟩

/-- `eraseDups` leaves no duplicates. -/
theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] : ∀ (list : List α), list.eraseDups.Nodup
  | [] => by simp
  | head :: rest => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr ⟨?_, nodup_eraseDups _⟩
      rw [List.mem_eraseDups]
      simp [List.mem_filter]
termination_by list => list.length
decreasing_by
  have := List.length_filter_le (fun element => !element == head) rest
  simp only [List.length_cons]
  omega

theorem ofSnapshot_admissible {rootBytes : List UInt8 → Digest} (image : Image)
    (snapshot : DataSnapshot rootBytes) : (State.ofSnapshot image snapshot).Admissible image := by
  refine ⟨?_, rfl, ?_⟩
  · simp only [State.ofSnapshot, List.map_map, Function.comp_def, List.map_id']
    exact nodup_eraseDups _
  · intro cellId member
    simp only [State.ofSnapshot, List.map_map, Function.comp_def, List.map_id'] at member
    exact member

namespace Witness

open DurableDataIntent.Witness
open DurableReceiver.Witness

/-- One accepted record on the witness seed. -/
def grown : Image := image.append intent

def honestState : State :=
  ⟨[], [(readCell, [1, 2, 3]), (writeCell, write.canonicalPostBytes)],
    fun lane => 10 - intent.exactCharge lane⟩

/-- A checkpoint whose state is not the prefix replay: the written cell is
rolled back to its seed bytes (same length, so the witness's length root
cannot tell them apart). -/
def rolledBackState : State :=
  ⟨[], [(readCell, [1, 2, 3]), (writeCell, [4, 5])],
    fun lane => 10 - intent.exactCharge lane⟩

/-- Satisfiable pole: an honest checkpoint at height 1 resumes to the same
written bytes as the genesis replay. -/
theorem honest_checkpoint_resumes :
    (resume lengthRoot grown 1 honestState).map (·.canonicalBytes writeCell) =
      (grown.restore lengthRoot).map (·.canonicalBytes writeCell) := by decide

/-- Refuting pole: the honesty premise of `resume_sound` is load-bearing. -/
theorem dishonest_checkpoint_diverges :
    (resume lengthRoot grown 1 rolledBackState).map (·.canonicalBytes writeCell) ≠
      (grown.restore lengthRoot).map (·.canonicalBytes writeCell) := by decide

end Witness

/-- info: 'Minidregg.Kernel.DurableCheckpoint.State.admissibleAgainst_iff' depends on axioms: [propext, Quot.sound]  -/
#guard_msgs (whitespace := lax) in #print axioms State.admissibleAgainst_iff

end Minidregg.Kernel.DurableCheckpoint

/-- info: 'Minidregg.Kernel.DurableCheckpoint.resume_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCheckpoint.resume_sound
/-- info: 'Minidregg.Kernel.DurableCheckpoint.resume_genesis' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCheckpoint.resume_genesis
/-- info: 'Minidregg.Kernel.DurableCheckpoint.resume_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCheckpoint.resume_append
/-- info: 'Minidregg.Kernel.DurableCheckpoint.Witness.honest_checkpoint_resumes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCheckpoint.Witness.honest_checkpoint_resumes
/-- info: 'Minidregg.Kernel.DurableCheckpoint.Witness.dishonest_checkpoint_diverges' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableCheckpoint.Witness.dishonest_checkpoint_diverges
