/-
# Kernel.DurableEngine — the durable snapshot as data, and `resume` compiled over it

`DataSnapshot` is the protocol's semantic snapshot: roots and canonical bytes
as functions, consumed nullifiers as a predicate, history and journal as lists.
Every theorem in the receiver is stated over it, and stays so. Built the way
the spec reads, it costs Θ(h) per record replayed at height h:

* `Snapshot.install` layers one closure per record over the cell lookups, and
  the checkpoint's cells are a list walked per lookup (`tableLookup`);
* the journal lookup that guards every replayed record walks the whole
  journal (`Snapshot.lookupRecorded`);
* the consumed check walks every spent nullifier of the prefix (`∈ spent`);
* (until history went newest first, the history append copied the whole history);
* admissibility enumerates the image's ids with an `eraseDups` (Θ(h·cells)).

`Engine` holds the same snapshot as data: the cells as a `CellTable` with
each cell's root carried beside it (`roots`: once per cell image, never per
query), the spent nullifiers as a hash set, the journal with a hash-set index of its
transaction ids. `view` is the
snapshot it represents, field for field; `replay_view` says the engine's replay
IS the protocol replay (`DurableReceiver.replay`) under `view`, and
`resume_eq_resumeFast` (`@[csimp]`) makes every compiled `resume` run it. No
statement changes: the spec is what the theorems name; this is what runs.
-/
module

public import Kernel.DurableCheckpoint
public import Kernel.CellTable
public import Kernel.SessionIndex
public import Std.Data.HashSet.Lemmas

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

namespace Minidregg.Kernel.DurableEngine

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableCheckpoint

set_option autoImplicit false

/-- Nullifiers hash by every field (equal nullifiers hash equal). -/
instance : Hashable StableNullifier :=
  ⟨fun nullifier => mixHash (hash nullifier.codecVersion) (mixHash (hash nullifier.domain.value)
    (mixHash (hash nullifier.nullifierId.value) (hash nullifier.canonicalBytes)))⟩

instance : LawfulHashable StableNullifier where
  hash_eq a b same := by
    cases eq_of_beq same
    rfl

/-- A journal lookup hits exactly the recorded transaction ids. -/
theorem lookupRecorded_isSome (transactionId : TransactionId) :
    ∀ (journal : List (TransactionId × Intent TransactionId CellId StableNullifier ReplayEnvelope)),
      (Snapshot.lookupRecorded transactionId journal).isSome =
        (journal.map Prod.fst).contains transactionId
  | [] => rfl
  | (recordedId, _) :: rest => by
      simp only [Snapshot.lookupRecorded, List.map_cons, List.contains_cons]
      by_cases same : recordedId = transactionId
      · simp [same]
      · simp only [same, ↓reduceIte, lookupRecorded_isSome transactionId rest]
        have : (transactionId == recordedId) = false := by simp [Ne.symm same]
        simp [this]

/-- Cell id value ↦ the cell's root, deferred: a checkpoint's cells are rooted
on first read and once (the thunk caches), a written cell carries the root its
write already bound (`DataIntent.postRootsBound`). -/
abbrev RootTable := Std.ExtTreeMap Nat (Thunk Digest) compare

/-- The durable snapshot as data. A cell's root is computed once per cell image
(`roots`, exact by `rootsExact`), never per query. -/
structure Engine (rootBytes : List UInt8 → Digest) where
  absent : List UInt8
  cells : CellTable
  /-- The root of every tabled cell, beside its bytes. -/
  roots : RootTable
  rootsExact : ∀ key : Nat, roots[key]?.map Thunk.get = cells[key]?.map rootBytes
  /-- The root of the fresh-identifier bytes. -/
  absentRoot : Thunk Digest
  absentRootExact : absentRoot.get = rootBytes absent
  available : Charge
  /-- The nullifiers consumed below the engine's base, as an oracle: nothing
  for a checkpoint's engine (its prefix sits in `spent`). -/
  spentBefore : StableNullifier → Bool
  spent : Std.HashSet StableNullifier
  /-- Newest first, as `Snapshot.install` conses it. Deferred: a past read
  that never asks for the journal never builds it. -/
  journal : Thunk (List (TransactionId × Intent TransactionId CellId StableNullifier ReplayEnvelope))
  /-- The journal's transaction ids below the base, as an oracle (as `spentBefore`). -/
  recordedBefore : TransactionId → Bool
  /-- The journal's transaction ids, indexed. -/
  recorded : Std.HashSet TransactionId
  recordedExact : ∀ transactionId,
    (recorded.contains transactionId || recordedBefore transactionId) =
      (journal.get.map Prod.fst).contains transactionId
  /-- Newest first, as `Snapshot.install` conses it; deferred as `journal`. -/
  historyRev : Thunk (List ReplayEnvelope)

namespace Engine

section accessors

variable {rootBytes : List UInt8 → Digest}

/-- A cell's bytes: the table's, else the fresh-identifier bytes. -/
def bytes (engine : Engine rootBytes) (cellId : CellId) : List UInt8 :=
  (engine.cells.get cellId).getD engine.absent

/-- A cell's root: the table's carried root, else the fresh-identifier root.
A lookup, not a hash (`root_eq`). -/
def root (engine : Engine rootBytes) (cellId : CellId) : Digest :=
  match engine.roots[cellId.value]? with
  | some root => root.get
  | none => engine.absentRoot.get

/-- **The carried root is the root of the cell's bytes.** -/
theorem root_eq (engine : Engine rootBytes) (cellId : CellId) :
    engine.root cellId = rootBytes (engine.bytes cellId) := by
  have exact := engine.rootsExact cellId.value
  unfold root bytes CellTable.get
  revert exact
  cases engine.roots[cellId.value]? <;> cases engine.cells[cellId.value]? <;> intro exact
  · exact engine.absentRootExact
  · simp at exact
  · simp at exact
  · exact Option.some.inj exact

/-- Whether a nullifier is consumed: installed here, or below the base. -/
@[inline] def consumed (engine : Engine rootBytes) (nullifier : StableNullifier) : Bool :=
  engine.spent.contains nullifier || engine.spentBefore nullifier

/-- Whether a transaction id is journaled: installed here, or below the base. -/
@[inline] def isRecorded (engine : Engine rootBytes) (transactionId : TransactionId) : Bool :=
  engine.recorded.contains transactionId || engine.recordedBefore transactionId

end accessors

variable (rootBytes : List UInt8 → Digest)

/-- **The snapshot this engine is**, field for field; its roots are the carried ones. -/
@[inline] def view (engine : Engine rootBytes) : DataSnapshot rootBytes where
  model :=
    { roots := engine.root
      consumed := fun nullifier => engine.consumed nullifier
      available := engine.available
      history := engine.historyRev.get
      journal := engine.journal.get }
  canonicalBytes := engine.bytes
  coherent := fun cellId => (engine.root_eq cellId).symm

/-- The same snapshot without history and journal: all that preflight reads. -/
@[inline] def light (engine : Engine rootBytes) : DataSnapshot rootBytes where
  model :=
    { roots := engine.root
      consumed := fun nullifier => engine.consumed nullifier
      available := engine.available
      history := []
      journal := [] }
  canonicalBytes := engine.bytes
  coherent := fun cellId => (engine.root_eq cellId).symm

/-- The carried roots of a cell table, each deferred to its first read. -/
def rootsOf (cells : CellTable) : RootTable :=
  cells.map fun _ bytes => Thunk.mk fun _ => rootBytes bytes

theorem rootsOf_exact (cells : CellTable) (key : Nat) :
    (rootsOf rootBytes cells)[key]?.map Thunk.get = cells[key]?.map rootBytes := by
  unfold rootsOf
  rw [Std.ExtTreeMap.getElem?_map, Option.map_map]
  rfl

/-- Each write's root, as its bound `exactPost`, installed beside its bytes. -/
theorem rootsExact_foldr (writes : List DataWrite)
    (bound : ∀ write, write ∈ writes → rootBytes write.canonicalPostBytes = write.exactPost)
    (cells : CellTable) (roots : RootTable)
    (exact : ∀ key : Nat, roots[key]?.map Thunk.get = cells[key]?.map rootBytes) (key : Nat) :
    (writes.foldr (fun write table => table.insert write.cellId.value (Thunk.pure write.exactPost))
        roots)[key]?.map Thunk.get =
      (writes.foldr (fun write table => table.insert write.cellId write.canonicalPostBytes)
        cells)[key]?.map rootBytes := by
  induction writes with
  | nil => exact exact key
  | cons write rest ih =>
      rw [List.foldr_cons, List.foldr_cons]
      show (Std.ExtTreeMap.insert _ _ _)[key]?.map Thunk.get =
        (Std.ExtTreeMap.insert _ _ _)[key]?.map rootBytes
      rw [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_insert]
      by_cases same : compare write.cellId.value key = .eq
      · rw [if_pos same, if_pos same]
        exact congrArg some (bound write List.mem_cons_self).symm
      · rw [if_neg same, if_neg same]
        exact ih fun other member => bound other (List.mem_cons_of_mem _ member)

/-- Preflight never reads history or journal. -/
theorem preflight_light (engine : Engine rootBytes) (intent : DataIntent rootBytes) :
    intent.preflight (engine.light rootBytes) = intent.preflight (engine.view rootBytes) := rfl

/-- One accepted record, installed as data: each write replaces its cell (the
first write of a cell wins, as `lookupPostBytes` reads), each nullifier joins
the set, the journal and history gain one cons each. -/
def install (engine : Engine rootBytes) (intent : DataIntent rootBytes) : Engine rootBytes where
  absent := engine.absent
  cells := intent.writes.foldr (fun write table => table.insert write.cellId write.canonicalPostBytes)
    engine.cells
  roots := intent.writes.foldr
    (fun write table => table.insert write.cellId.value (Thunk.pure write.exactPost)) engine.roots
  rootsExact := rootsExact_foldr rootBytes intent.writes intent.postRootsBound engine.cells
    engine.roots engine.rootsExact
  absentRoot := engine.absentRoot
  absentRootExact := engine.absentRootExact
  -- Keep the ten remaining allowances as values. Retaining the subtraction
  -- closure would re-evaluate every prior intent's charge on each later check.
  available := (Charge.materialize fun lane =>
    engine.available lane - intent.exactCharge lane + intent.credit lane).toCharge
  spentBefore := engine.spentBefore
  spent := intent.nullifiers.foldl (fun spent nullifier => spent.insert nullifier) engine.spent
  journal := Thunk.mk fun _ => (intent.transactionId, intent.erase) :: engine.journal.get
  recordedBefore := engine.recordedBefore
  recorded := engine.recorded.insert intent.transactionId
  recordedExact := by
    intro transactionId
    show ((engine.recorded.insert intent.transactionId).contains transactionId ||
        engine.recordedBefore transactionId) =
      (((intent.transactionId, intent.erase) :: engine.journal.get).map Prod.fst).contains
        transactionId
    rw [Std.HashSet.contains_insert, List.map_cons, List.contains_cons, ← engine.recordedExact]
    by_cases same : intent.transactionId = transactionId
    · subst same; simp
    · have differs : (intent.transactionId == transactionId) = false := by simp [same]
      have differs' : (transactionId == intent.transactionId) = false := by simp [Ne.symm same]
      simp [differs, differs']
  historyRev := Thunk.mk fun _ => intent.erase.event :: engine.historyRev.get

/-- Materializing the remaining budget preserves every lane, including exact
exhaustion and natural-number subtraction at zero. -/
theorem available_install (engine : Engine rootBytes) (intent : DataIntent rootBytes) :
    (engine.install rootBytes intent).available =
      fun lane => engine.available lane - intent.exactCharge lane + intent.credit lane :=
  Charge.materialize_eq _

theorem get_foldr (writes : List DataWrite) (table : CellTable) (cellId : CellId) :
    (writes.foldr (fun write table => table.insert write.cellId write.canonicalPostBytes) table).get
        cellId = (DataSnapshot.lookupPostBytes cellId writes).or (table.get cellId) := by
  induction writes with
  | nil => rfl
  | cons write rest ih =>
      rw [List.foldr_cons, CellTable.get_insert, ih]
      simp only [DataSnapshot.lookupPostBytes]
      split <;> rfl

theorem contains_foldl (nullifiers : List StableNullifier) (spent : Std.HashSet StableNullifier)
    (nullifier : StableNullifier) :
    (nullifiers.foldl (fun spent nullifier => spent.insert nullifier) spent).contains nullifier =
      (nullifiers.contains nullifier || spent.contains nullifier) := by
  induction nullifiers generalizing spent with
  | nil => simp
  | cons head rest ih =>
      rw [List.foldl_cons, ih, Std.HashSet.contains_insert]
      by_cases same : head = nullifier
      · subst same; simp
      · have differs : (head == nullifier) = false := by simp [same]
        rw [differs]
        simp [Ne.symm same]

/-- Two snapshots with the same model and bytes are equal (coherence is a proof). -/
theorem DataSnapshot.ext' {left right : DataSnapshot rootBytes} (model : left.model = right.model)
    (bytes : left.canonicalBytes = right.canonicalBytes) : left = right := by
  cases left
  cases right
  simp only at model bytes
  subst model bytes
  rfl

/-- **Install commutes with `view`**: the engine's install is the protocol's. -/
theorem view_install (engine : Engine rootBytes) (intent : DataIntent rootBytes) :
    (engine.install rootBytes intent).view rootBytes =
      DataSnapshot.install (engine.view rootBytes) intent := by
  have bytesEq : (engine.install rootBytes intent).bytes =
      (DataSnapshot.install (engine.view rootBytes) intent).canonicalBytes := by
    funext cellId
    show ((intent.writes.foldr _ engine.cells).get cellId).getD engine.absent =
      (DataSnapshot.lookupPostBytes cellId intent.writes).getD (engine.bytes cellId)
    rw [get_foldr]
    cases DataSnapshot.lookupPostBytes cellId intent.writes <;> rfl
  apply DataSnapshot.ext' rootBytes
  · have rootsEq : (engine.install rootBytes intent).root =
        (DataSnapshot.install (engine.view rootBytes) intent).model.roots := by
      funext cellId
      rw [root_eq, ← (DataSnapshot.install (engine.view rootBytes) intent).coherent cellId,
        bytesEq]
    show Snapshot.mk _ _ _ _ _ = Snapshot.install (engine.view rootBytes).model intent.erase
    unfold Snapshot.install
    congr 1
    all_goals first
      | exact rootsEq
      | exact Charge.materialize_eq _
      | (funext nullifier
         show ((intent.nullifiers.foldl _ engine.spent).contains nullifier ||
           engine.spentBefore nullifier) = _
         rw [contains_foldl]
         by_cases member : nullifier ∈ intent.nullifiers <;> simp [member, view, consumed])
      | rfl
  · exact bytesEq

/-- The engine at a checkpoint: the state's cells as a table, the prefix's
nullifiers and transaction ids as sets, its journal and history as `State.snapshot`
builds them (history kept newest first). -/
def ofState (state : State) (prefixRecords : List IntentRecord) : Engine rootBytes :=
  let cells := CellTable.ofList state.cells
  { absent := state.absentBytes
    cells := cells
    roots := rootsOf rootBytes cells
    rootsExact := rootsOf_exact rootBytes cells
    absentRoot := Thunk.mk fun _ => rootBytes state.absentBytes
    absentRootExact := rfl
    available := state.available
    spentBefore := fun _ => false
    spent := Std.HashSet.ofList (prefixRecords.flatMap IntentRecord.nullifiers)
    journal := Thunk.mk fun _ =>
      (prefixRecords.map fun record => (record.transactionId, IntentRecord.erase record)).reverse
    recordedBefore := fun _ => false
    recorded := Std.HashSet.ofList (prefixRecords.map IntentRecord.transactionId)
    recordedExact := by
      intro transactionId
      show ((Std.HashSet.ofList _).contains transactionId || false) =
        (((prefixRecords.map fun record => (record.transactionId, IntentRecord.erase record)).reverse).map
          Prod.fst).contains transactionId
      rw [Bool.or_false, Std.HashSet.contains_ofList, List.map_reverse, List.map_map]
      simp [Function.comp_def, IntentRecord.erase]
    historyRev := Thunk.mk fun _ =>
      (prefixRecords.map fun record => (IntentRecord.erase record).event).reverse }

/-- **The engine at a checkpoint is the checkpoint's snapshot.** -/
theorem view_ofState (state : State) (prefixRecords : List IntentRecord) :
    (ofState rootBytes state prefixRecords).view rootBytes = state.snapshot rootBytes prefixRecords := by
  have bytesEq : (ofState rootBytes state prefixRecords).bytes =
      (state.snapshot rootBytes prefixRecords).canonicalBytes := by
    funext cellId
    show ((CellTable.ofList state.cells).get cellId).getD state.absentBytes = _
    rw [CellTable.get_ofList]
    rfl
  apply DataSnapshot.ext' rootBytes
  · show Snapshot.mk _ _ _ _ _ = Snapshot.mk _ _ _ _ _
    congr 1
    all_goals first
      | (funext cellId
         rw [root_eq, congrFun bytesEq cellId]
         exact (state.snapshot rootBytes prefixRecords).coherent cellId)
      | (funext nullifier
         show ((Std.HashSet.ofList _).contains nullifier || false) = _
         rw [Bool.or_false, Std.HashSet.contains_ofList]
         exact List.elem_eq_mem _ _)
      | rfl
  · exact bytesEq

/-- Replay over the engine: the protocol's `replay`, with the journal guard
read off the index and preflight read off the light snapshot. -/
def replay (engine : Engine rootBytes) : List IntentRecord → Option (Engine rootBytes)
  | [] => some engine
  | record :: records =>
      match record.bind? rootBytes with
      | none => none
      | some intent =>
          if engine.isRecorded intent.transactionId then none
          else
            match intent.preflight (engine.light rootBytes) with
            | .ok () => replay (engine.install rootBytes intent) records
            | .error _ => none

/-- **The engine's replay is the protocol replay** under `view`. -/
theorem replay_view (engine : Engine rootBytes) (records : List IntentRecord) :
    DurableReceiver.replay rootBytes (engine.view rootBytes) records =
      (engine.replay rootBytes records).map (view rootBytes) := by
  induction records generalizing engine with
  | nil => rfl
  | cons record records ih =>
      simp only [DurableReceiver.replay, replay]
      cases record.bind? rootBytes with
      | none => rfl
      | some intent =>
          dsimp only [bind, Option.bind]
          by_cases hit : engine.isRecorded intent.transactionId = true
          · rw [if_pos hit]
            have found : (Snapshot.lookupRecorded intent.transactionId engine.journal.get).isSome := by
              rw [lookupRecorded_isSome, ← engine.recordedExact]; exact hit
            obtain ⟨recorded, isRecorded⟩ := Option.isSome_iff_exists.mp found
            unfold DurableDataIntent.execute
            rw [show (engine.view rootBytes).model.journal = engine.journal.get from rfl, isRecorded]
            dsimp only
            by_cases same : recorded.sameCheck intent.erase = true
            · rw [if_pos same]; rfl
            · rw [if_neg same]; rfl
          · rw [if_neg hit]
            have missing : Snapshot.lookupRecorded intent.transactionId engine.journal.get = none := by
              rw [← Option.not_isSome_iff_eq_none, lookupRecorded_isSome, ← engine.recordedExact]
              exact hit
            rw [preflight_light]
            cases checked : intent.preflight (engine.view rootBytes) with
            | error reason =>
                simp only [DurableDataIntent.execute]
                rw [show (engine.view rootBytes).model.journal = engine.journal.get from rfl, missing]
                simp only [checked]
                rfl
            | ok _ =>
                simp only [DurableDataIntent.execute]
                rw [show (engine.view rootBytes).model.journal = engine.journal.get from rfl, missing]
                simp only [checked]
                rw [← view_install, ih]

end Engine

/-- Duplicate-freedom by one pass with a hash set (`decide Nodup` is quadratic). -/
def nodupFast (ids : List CellId) : Bool := go ∅ ids
where
  go (seen : Std.HashSet CellId) : List CellId → Bool
    | [] => true
    | id :: rest => if seen.contains id then false else go (seen.insert id) rest

theorem nodupFast.go_iff (seen : Std.HashSet CellId) (ids : List CellId) :
    nodupFast.go seen ids = true ↔ ids.Nodup ∧ ∀ id ∈ ids, seen.contains id = false := by
  induction ids generalizing seen with
  | nil => simp [nodupFast.go]
  | cons id rest ih =>
      simp only [nodupFast.go]
      by_cases hit : seen.contains id = true
      · rw [if_pos hit]
        simp only [Bool.false_eq_true, false_iff, not_and]
        intro _ fresh
        have := fresh id List.mem_cons_self
        rw [hit] at this
        cases this
      · rw [if_neg hit, ih]
        have hfalse : seen.contains id = false := by simpa using hit
        constructor
        · rintro ⟨nodup, fresh⟩
          refine ⟨List.nodup_cons.mpr ⟨fun mem => ?_, nodup⟩, ?_⟩
          · have := fresh id mem
            rw [Std.HashSet.contains_insert] at this
            simp at this
          · intro other mem
            rcases List.mem_cons.mp mem with same | inRest
            · rw [same]; exact hfalse
            · have := fresh other inRest
              rw [Std.HashSet.contains_insert] at this
              simp only [Bool.or_eq_false_iff] at this
              exact this.2
        · rintro ⟨nodup, fresh⟩
          obtain ⟨notMem, nodupRest⟩ := List.nodup_cons.mp nodup
          refine ⟨nodupRest, fun other mem => ?_⟩
          rw [Std.HashSet.contains_insert]
          have differs : (id == other) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]
            intro same
            rw [same] at notMem
            exact notMem mem
          rw [differs, Bool.false_or]
          exact fresh other (List.mem_cons_of_mem _ mem)

theorem nodupFast_iff (ids : List CellId) : nodupFast ids = true ↔ ids.Nodup := by
  unfold nodupFast
  rw [nodupFast.go_iff]
  simp

/-- Admissibility with the image's identifiers in a hash set (no `eraseDups`). -/
def admissibleFast (image : Image) (state : State) : Bool :=
  let ids : Std.HashSet CellId := Std.HashSet.ofList
    (image.seed.cells.map Prod.fst ++
      image.accepted.flatMap fun record => record.writes.map DataWrite.cellId)
  nodupFast (state.cells.map Prod.fst) && decide (state.absentBytes = image.seed.absentBytes) &&
    (state.cells.map Prod.fst).all fun cellId => ids.contains cellId

theorem admissibleFast_iff (image : Image) (state : State) :
    admissibleFast image state = true ↔ state.Admissible image := by
  unfold admissibleFast State.Admissible Image.cellIds
  simp only [Bool.and_eq_true, nodupFast_iff, decide_eq_true_eq, List.all_eq_true,
    Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_eraseDups, and_assoc]

/-- The engine `resume` builds: admissibility off a hash set, the checkpoint's
engine (`Engine.ofState`), the suffix replayed over it. -/
def resumeEngine (rootBytes : List UInt8 → Digest) (image : Image) (height : Nat)
    (state : State) : Option (Engine rootBytes) :=
  if admissibleFast image state then
    (Engine.ofState rootBytes state (image.accepted.take height)).replay rootBytes (image.accepted.drop height)
  else none

/-- `resume`, compiled: the snapshot of the engine `resumeEngine` builds. -/
def resumeFast (rootBytes : List UInt8 → Digest) (image : Image) (height : Nat)
    (state : State) : Option (DataSnapshot rootBytes) :=
  (resumeEngine rootBytes image height state).map (Engine.view rootBytes)

/-- **Refinement, compiled**: every `resume` the host runs is `resumeFast`;
the replacement is this theorem, not a trusted `implemented_by`. -/
@[csimp] theorem resume_eq_resumeFast : @resume = @resumeFast := by
  funext rootBytes image height state
  unfold resume resumeFast resumeEngine
  by_cases admissible : state.Admissible image
  · rw [if_pos admissible, if_pos ((admissibleFast_iff image state).mpr admissible),
      ← Engine.replay_view, Engine.view_ofState]
  · rw [if_neg admissible, if_neg (fun fast => admissible ((admissibleFast_iff image state).mp fast))]
    rfl

/-- **A resume is the view of its engine**: a holder of the engine holds the
snapshot every theorem names. -/
theorem resume_eq_resumeEngine (rootBytes : List UInt8 → Digest) (image : Image) (height : Nat)
    (state : State) :
    resume rootBytes image height state =
      (resumeEngine rootBytes image height state).map (Engine.view rootBytes) := by
  rw [resume_eq_resumeFast]
  rfl

theorem resume_of_resumeEngine {rootBytes : List UInt8 → Digest} {image : Image} {height : Nat}
    {state : State} {engine : Engine rootBytes} (found : resumeEngine rootBytes image height state = some engine) :
    resume rootBytes image height state = some (engine.view rootBytes) := by
  rw [resume_eq_resumeEngine, found]
  rfl

/-! ## The executor over the engine -/

namespace Engine

variable (rootBytes : List UInt8 → Digest)

/-- The executor over the engine: the journal guard off the index, preflight
off the light snapshot. Only a recorded transaction id (a replay or a conflict)
reaches the protocol's journal walk. -/
def execute (engine : Engine rootBytes) (intent : DataIntent rootBytes) : Outcome rootBytes :=
  if engine.isRecorded intent.transactionId then
    DurableDataIntent.execute .complete (engine.view rootBytes) intent
  else
    match intent.preflight (engine.light rootBytes) with
    | .error reason => .rejected reason
    | .ok () => .accepted (DataSnapshot.install (engine.view rootBytes) intent)

/-- **The engine's executor is the protocol's** at the engine's snapshot. -/
theorem execute_eq (engine : Engine rootBytes) (intent : DataIntent rootBytes) :
    engine.execute rootBytes intent =
      DurableDataIntent.execute .complete (engine.view rootBytes) intent := by
  unfold execute
  by_cases hit : engine.isRecorded intent.transactionId = true
  · rw [if_pos hit]
  · rw [if_neg hit]
    have missing : Snapshot.lookupRecorded intent.transactionId engine.journal.get = none := by
      rw [← Option.not_isSome_iff_eq_none, lookupRecorded_isSome, ← engine.recordedExact]
      exact hit
    unfold DurableDataIntent.execute
    rw [show (engine.view rootBytes).model.journal = engine.journal.get from rfl, missing,
      preflight_light]
    cases intent.preflight (engine.view rootBytes) <;> rfl

end Engine

/-! ## What a resume holds: the whole log's journal, nullifiers and history -/

/-- What a replay does to the journal and the consumed set. -/
theorem replay_model {rootBytes : List UInt8 → Digest} :
    ∀ (records : List IntentRecord) (before after : DataSnapshot rootBytes),
      DurableReceiver.replay rootBytes before records = some after →
        after.model.journal =
            (records.map fun r => (r.transactionId, IntentRecord.erase r)).reverse ++
              before.model.journal ∧
          ∀ n, after.model.consumed n =
            (decide (n ∈ records.flatMap IntentRecord.nullifiers) || before.model.consumed n)
  | [], before, after, h => by
      simp only [DurableReceiver.replay, Option.some.injEq] at h
      subst h
      exact ⟨by simp, fun n => by simp⟩
  | r :: rs, before, after, h => by
      unfold DurableReceiver.replay at h
      cases hb : r.bind? rootBytes with
      | none => rw [hb] at h; cases h
      | some intent =>
          rw [hb] at h
          change (match DurableDataIntent.execute .complete before intent with
            | .accepted next => DurableReceiver.replay rootBytes next rs
            | _ => none) = some after at h
          split at h
          · rename_i next he
            have hn := DurableReceiver.execute_accepted_install _ _ _ he
            obtain ⟨hj, hc⟩ := replay_model rs next after h
            have he' := IntentRecord.erase_bind hb
            subst hn
            refine ⟨?_, fun n => ?_⟩
            · rw [hj]
              show _ ++ ((intent.erase.transactionId, intent.erase) :: before.model.journal) = _
              rw [he']
              simp [IntentRecord.erase]
            · rw [hc n]
              show (decide _ || (if n ∈ intent.erase.nullifiers then true else
                before.model.consumed n)) = _
              rw [he']
              by_cases hm : n ∈ r.nullifiers <;>
                simp [hm, IntentRecord.erase, List.flatMap_cons]
          · cases h

/-- What a replay does to the history (newest first). -/
theorem replay_history {rootBytes : List UInt8 → Digest} :
    ∀ (records : List IntentRecord) (before after : DataSnapshot rootBytes),
      DurableReceiver.replay rootBytes before records = some after →
        after.model.history =
          (records.map fun r => (IntentRecord.erase r).event).reverse ++ before.model.history
  | [], before, after, h => by
      simp only [DurableReceiver.replay, Option.some.injEq] at h
      subst h
      simp
  | r :: rs, before, after, h => by
      unfold DurableReceiver.replay at h
      cases hb : r.bind? rootBytes with
      | none => rw [hb] at h; cases h
      | some intent =>
          rw [hb] at h
          change (match DurableDataIntent.execute .complete before intent with
            | .accepted next => DurableReceiver.replay rootBytes next rs
            | _ => none) = some after at h
          split at h
          · rename_i next he
            have hn := DurableReceiver.execute_accepted_install _ _ _ he
            have hh := replay_history rs next after h
            have he' := IntentRecord.erase_bind hb
            subst hn
            rw [hh]
            show _ ++ (intent.erase.event :: before.model.history) = _
            rw [he']
            simp
          · cases h

/-- What a resume is: the whole log's journal, and the prefix's nullifiers plus
the replayed suffix's. -/
theorem resume_model {rootBytes : List UInt8 → Digest} {image : Image} {bh : Nat} {st : State}
    {snap : DataSnapshot rootBytes} (h : resume rootBytes image bh st = some snap) :
    snap.model.journal =
        (image.accepted.map fun r => (r.transactionId, IntentRecord.erase r)).reverse ∧
      ∀ n, snap.model.consumed n =
        (decide (n ∈ (image.accepted.drop bh).flatMap IntentRecord.nullifiers) ||
          decide (n ∈ (image.accepted.take bh).flatMap IntentRecord.nullifiers)) := by
  unfold resume at h
  split at h
  · obtain ⟨hj, hc⟩ := replay_model _ _ _ h
    refine ⟨?_, fun n => hc n⟩
    rw [hj]
    show _ ++ ((image.accepted.take bh).map fun r =>
      (r.transactionId, IntentRecord.erase r)).reverse = _
    rw [← List.reverse_append, ← List.map_append, List.take_append_drop]
  · cases h

/-- A resume's history is the whole log's events, newest first. -/
theorem resume_history {rootBytes : List UInt8 → Digest} {image : Image} {bh : Nat} {st : State}
    {snap : DataSnapshot rootBytes} (h : resume rootBytes image bh st = some snap) :
    snap.model.history = (image.accepted.map fun r => (IntentRecord.erase r).event).reverse := by
  unfold resume at h
  split at h
  · rw [replay_history _ _ _ h]
    show _ ++ ((image.accepted.take bh).map fun r => (IntentRecord.erase r).event).reverse = _
    rw [← List.reverse_append, ← List.map_append, List.take_append_drop]
  · cases h

theorem lookup_map_self (l : List CellId) (f : CellId → List UInt8) (c : CellId) :
    Seed.lookup (l.map fun x => (x, f x)) c = if c ∈ l then some (f c) else none := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons, Seed.lookup, List.mem_cons]
      by_cases e : x = c
      · subst e; simp
      · rw [if_neg e, ih]
        by_cases m : c ∈ rest
        · simp [m]
        · simp [m, Ne.symm e]

/-- **Rebasing at the head is the identity on the snapshot**: the head's state,
materialized as a checkpoint at the head (`State.ofSnapshot`), resumes to the
very snapshot it was taken from. A live session keeps its engine across a
rebase; nothing is rebuilt. -/
theorem resume_rebase {rootBytes : List UInt8 → Digest} {image : Image} {bh : Nat} {st : State}
    {snap : DataSnapshot rootBytes} (resumed : resume rootBytes image bh st = some snap) :
    resume rootBytes image image.accepted.length (State.ofSnapshot image snap) = some snap := by
  unfold resume
  rw [if_pos (ofSnapshot_admissible _ _), List.drop_length, List.take_length]
  simp only [DurableReceiver.replay, Option.some.injEq]
  have bytesEq : (State.snapshot rootBytes (State.ofSnapshot image snap) image.accepted).canonicalBytes =
      snap.canonicalBytes := by
    funext c
    show (Seed.lookup (image.cellIds.map fun c => (c, snap.canonicalBytes c)) c).getD
      image.seed.absentBytes = _
    rw [lookup_map_self]
    by_cases m : c ∈ image.cellIds
    · simp [m]
    · simp only [m, if_false, Option.getD_none]
      exact (resume_outside_support rootBytes _ _ _ _ resumed c m).symm
  apply Engine.DataSnapshot.ext' rootBytes _ bytesEq
  obtain ⟨journal, consumed⟩ := resume_model resumed
  show Snapshot.mk _ _ _ _ _ = snap.model
  cases model : snap.model with
  | mk roots consumedOf available history journalOf =>
    have rootsEq : (State.snapshot rootBytes (State.ofSnapshot image snap) image.accepted).model.roots =
        roots := by
      funext c
      rw [← (State.snapshot rootBytes (State.ofSnapshot image snap) image.accepted).coherent c,
        bytesEq, snap.coherent c, model]
    simp only [model] at journal consumed
    have hist := resume_history resumed
    simp only [model] at hist
    congr 1
    all_goals first
      | exact rootsEq
      | exact hist.symm
      | exact journal.symm
      | (show (State.ofSnapshot image snap).available = available
         show snap.model.available = available
         rw [model])
      | (funext n
         show decide (n ∈ image.accepted.flatMap IntentRecord.nullifiers) = _
         rw [consumed n]
         conv => lhs; rw [← List.take_append_drop bh image.accepted]
         rw [List.flatMap_append]
         by_cases h1 : n ∈ (image.accepted.drop bh).flatMap IntentRecord.nullifiers
         · simp only [h1, decide_true, Bool.true_or, List.mem_append, or_true]
         · simp only [h1, decide_false, Bool.false_or, List.mem_append, or_false])

#assert_axioms Engine.view_install
#assert_axioms Engine.view_ofState
#assert_axioms Engine.replay_view
#assert_axioms resume_eq_resumeFast
#assert_axioms resume_eq_resumeEngine
#assert_axioms Engine.execute_eq
#assert_axioms resume_rebase
#assert_axioms replay_model
#assert_axioms resume_model
#assert_axioms replay_history
#assert_axioms resume_history
#assert_axioms nodupFast_iff

end Minidregg.Kernel.DurableEngine
