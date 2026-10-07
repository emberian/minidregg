/-
# Compiler.DurableServed — the light state a request is served from (KN2 stage 2b-1)

A `Served` is the STATE of one opened Store at a height: every cell's root and
canonical bytes, the allowance, the cell enumeration, the fresh-cell bytes, the
seed, the log chain there and the world root. It holds NO history: no journal,
no consumed nullifiers, no history events. Its snapshot is private and bare
(`bare`: empty journal, nothing consumed, no history), so no consumer can read a
journal or a consumed bit off it and see a silent "absent".

The only way to obtain a `DataSnapshot` with journal or consumed answers is
`Served.viewAt`: the state plus a `VerifiedFootprint` read from the Store's
authenticated history (`Reader.footprint`), restricted to what was accepted at
or below the served height. `recordedAt_some` / `recordedAt_none` and
`spentAt_true` / `spentAt_false` say what those answers are; `viewAt_agrees`
glues them to `DurableView.AgreesOnKeys`, which every `Family` consumes.

The authority clock (`CredentialAuthorityDomainReceiver.clockOf`, the history
length on the full shape) is the served `height` here; `ofLoaded_height` says
the full shape's history length IS its height.

Producers:
* `ofLoaded` — from the full verified materialization (callers are on the
  ratchet list `scripts/ports/full-loaded-callers.txt`, which only shrinks);
* `ofStateAt` — a past height from `Reader.stateAt` (checkpoint at or below it,
  MAC-verified, plus verified records);
* the head's light opening (2b-1, `DurableReceiverIO`).

`Served` is indexed by the opened Store's identity, so a view can only be built
from a head of the same Store.
-/
import Compiler.DurableHistoryStore
import Std.Data.HashMap

namespace Minidregg.Compiler.DurableServed

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost (Charge)
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent (DataSnapshot CellId DataWrite TransactionId StableNullifier
  ReplayEnvelope)
open Minidregg.Kernel.DurableCommitProtocol (Intent Snapshot)
open Minidregg.Kernel.DurableReceiver (IntentRecord Seed replay)
open Minidregg.Kernel.DurableCheckpoint (State)
open Minidregg.Kernel.DurableView (Keys AgreesOnKeys)
open Minidregg.Compiler.DurableReceiverIO (Loaded)
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (StateAt VerifiedFootprint TxAnswer ByTx Spent)
open Minidregg.Compiler.DurableCheckpointCodec (systemLeaf)

set_option autoImplicit false

variable {rootBytes : List UInt8 → Digest}

/-- The state of a snapshot with its history removed. -/
def bare (snapshot : DataSnapshot rootBytes) : DataSnapshot rootBytes where
  model := { snapshot.model with consumed := fun _ => false, history := [], journal := [] }
  canonicalBytes := snapshot.canonicalBytes
  coherent := snapshot.coherent

/-- The cells a state enumerates after `records`: the base's, then each newly
written id in record order (`Image.cellIds`'s order when the base is the seed). -/
def extendIds (ids : List CellId) (records : List IntentRecord) : List CellId :=
  (ids ++ records.flatMap fun record => record.writes.map DataWrite.cellId).eraseDups

theorem not_mem_extendIds {ids : List CellId} {records : List IntentRecord} {cellId : CellId}
    (missing : cellId ∉ extendIds ids records) :
    cellId ∉ ids ∧ cellId ∉ records.flatMap fun record => record.writes.map DataWrite.cellId := by
  unfold extendIds at missing
  rw [List.mem_eraseDups, List.mem_append, not_or] at missing
  exact missing

structure Served (rootBytes : List UInt8 → Digest) (store : StoreIdentity) where
  private mk ::
  private state : DataSnapshot rootBytes
  seed : Seed
  /-- Every enumerable cell id at `height` (seeded or written), in enumeration order. -/
  cellIds : List CellId
  absentBytes : List UInt8
  height : Nat
  chain : Digest
  worldRoot : Digest
  private outsideAbsent : ∀ cellId, cellId ∉ cellIds → state.canonicalBytes cellId = absentBytes
  private cellIdsNodup : cellIds.Nodup

namespace Served

variable {store : StoreIdentity}

def logStart (_served : Served rootBytes store) : Digest := store.logStart

def roots (served : Served rootBytes store) : CellId → Digest := served.state.model.roots
def canonicalBytes (served : Served rootBytes store) : CellId → List UInt8 := served.state.canonicalBytes
def available (served : Served rootBytes store) : Charge := served.state.model.available

theorem coherent (served : Served rootBytes store) (cellId : CellId) :
    rootBytes (served.canonicalBytes cellId) = served.roots cellId :=
  served.state.coherent cellId

/-- Outside the enumeration every cell holds the fresh-cell bytes. -/
theorem canonicalBytes_outside (served : Served rootBytes store) (cellId : CellId)
    (missing : cellId ∉ served.cellIds) : served.canonicalBytes cellId = served.absentBytes :=
  served.outsideAbsent cellId missing

theorem cellIds_nodup (served : Served rootBytes store) : served.cellIds.Nodup := served.cellIdsNodup

/-- The cells a directory loads, in enumeration order. -/
def cells (served : Served rootBytes store) : List (CellId × List UInt8) :=
  served.cellIds.map fun cellId => (cellId, served.canonicalBytes cellId)

/-- The world-root entries of a state (C1's `worldEntries`). -/
def entriesOf (roots : CellId → Digest) (cellIds : List CellId) (height : Nat) (chain : Digest) :
    List (WorldRoot.Key × Digest) :=
  (.system, systemLeaf height chain) :: cellIds.map fun cellId => (.cell cellId.value, roots cellId)

/-! ## Footprint answers at the served height -/

/-- The recorded intents a footprint contributes at `height`: a present answer
whose record was accepted at or below `height`. -/
def recordedAt {head : Head store} {keys : Keys} (footprint : VerifiedFootprint head keys) (height : Nat) :
    List (TransactionId × Intent TransactionId CellId StableNullifier ReplayEnvelope) :=
  footprint.transactions.filterMap fun answer =>
    match answer.2 with
    | .present found =>
        if found.height ≤ height then some (answer.1, DurableCheckpoint.IntentRecord.erase found.read.record)
        else none
    | .absent _ => none

/-- A nullifier's consumed bit at `height`: its first answer names an inserting
height at or below `height`. -/
def spentAt {head : Head store} {keys : Keys} (footprint : VerifiedFootprint head keys) (height : Nat)
    (nullifier : StableNullifier) : Bool :=
  (footprint.nullifiers.find? (·.1 = nullifier)).any fun answer => answer.2.value.any (· ≤ height)

/-- The served state with the footprint's answers at the served height: the
only `DataSnapshot` with a journal or consumed bits a `Served` yields. -/
def viewAt (served : Served rootBytes store) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) : DataSnapshot rootBytes where
  model := { served.state.model with
    journal := recordedAt footprint served.height
    consumed := spentAt footprint served.height }
  canonicalBytes := served.state.canonicalBytes
  coherent := served.state.coherent

@[simp] theorem viewAt_roots (served : Served rootBytes store) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) : (served.viewAt footprint).model.roots = served.roots := rfl
@[simp] theorem viewAt_canonicalBytes (served : Served rootBytes store) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) :
    (served.viewAt footprint).canonicalBytes = served.canonicalBytes := rfl
@[simp] theorem viewAt_available (served : Served rootBytes store) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) :
    (served.viewAt footprint).model.available = served.available := rfl

theorem recordedAt_lookup_some_list {head : Head store} (height : Nat) (transactionId : TransactionId)
    {intent : Intent TransactionId CellId StableNullifier ReplayEnvelope} :
    ∀ (answers : List ((id : TransactionId) × TxAnswer head id)),
      Snapshot.lookupRecorded transactionId (answers.filterMap fun answer =>
        match answer.2 with
        | .present found =>
            if found.height ≤ height then
              some (answer.1, DurableCheckpoint.IntentRecord.erase found.read.record)
            else none
        | .absent _ => none) = some intent →
      ∃ found : ByTx head transactionId, found.height ≤ height ∧
        intent = DurableCheckpoint.IntentRecord.erase found.read.record
  | [], hit => by simp [Snapshot.lookupRecorded] at hit
  | ⟨id, .absent _⟩ :: rest, hit => recordedAt_lookup_some_list height transactionId rest (by
      simpa [List.filterMap_cons] using hit)
  | ⟨id, .present found⟩ :: rest, hit => by
      by_cases below : found.height ≤ height
      · simp only [List.filterMap_cons, below, ↓reduceIte, Snapshot.lookupRecorded] at hit
        split at hit
        · rename_i same
          subst same
          exact ⟨found, below, (Option.some.inj hit).symm⟩
        · exact recordedAt_lookup_some_list height transactionId rest hit
      · simp only [List.filterMap_cons, below, ↓reduceIte] at hit
        exact recordedAt_lookup_some_list height transactionId rest hit

/-- **Every journal answer of a view is a record verified at use, accepted at
or below the served height.** -/
theorem recordedAt_some {head : Head store} {keys : Keys} (footprint : VerifiedFootprint head keys)
    (height : Nat) (transactionId : TransactionId)
    {intent : Intent TransactionId CellId StableNullifier ReplayEnvelope}
    (hit : Snapshot.lookupRecorded transactionId (recordedAt footprint height) = some intent) :
    ∃ found : ByTx head transactionId, found.height ≤ height ∧
      intent = DurableCheckpoint.IntentRecord.erase found.read.record :=
  recordedAt_lookup_some_list height transactionId footprint.transactions hit

theorem recordedAt_lookup_none_list {head : Head store} (height : Nat) (transactionId : TransactionId) :
    ∀ (answers : List ((id : TransactionId) × TxAnswer head id)),
      Snapshot.lookupRecorded transactionId (answers.filterMap fun answer =>
        match answer.2 with
        | .present found =>
            if found.height ≤ height then
              some (answer.1, DurableCheckpoint.IntentRecord.erase found.read.record)
            else none
        | .absent _ => none) = none →
      ∀ answer ∈ answers, answer.1 = transactionId →
        (∃ opens : DurableSpent.Opens head.spentRoot (DurableSpent.transactionKey answer.1) none,
            answer.2 = .absent opens) ∨
          ∃ found : ByTx head answer.1, answer.2 = .present found ∧ height < found.height
  | [], _, _, member, _ => by cases member
  | ⟨id, reply⟩ :: rest, miss, answer, member, same => by
      rcases List.mem_cons.mp member with rfl | inRest
      · cases reply with
        | absent opens => exact Or.inl ⟨opens, rfl⟩
        | present found =>
            by_cases below : found.height ≤ height
            · simp only at same
              subst same
              simp [below, Snapshot.lookupRecorded] at miss
            · exact Or.inr ⟨found, rfl, Nat.lt_of_not_le below⟩
      · have missRest : Snapshot.lookupRecorded transactionId (rest.filterMap fun answer =>
            match answer.2 with
            | .present found =>
                if found.height ≤ height then
                  some (answer.1, DurableCheckpoint.IntentRecord.erase found.read.record)
                else none
            | .absent _ => none) = none := by
          cases reply with
          | absent _ => simpa [List.filterMap_cons] using miss
          | present found =>
              by_cases below : found.height ≤ height
              · simp only [List.filterMap_cons, below, ↓reduceIte, Snapshot.lookupRecorded] at miss
                split at miss
                · cases miss
                · exact miss
              · simpa [List.filterMap_cons, below] using miss
        exact recordedAt_lookup_none_list height transactionId rest missRest answer inRest same

/-- **A miss on a declared key is a verified absence, or a record accepted
above the served height** (it did not exist at that height). -/
theorem recordedAt_none {head : Head store} {keys : Keys} (footprint : VerifiedFootprint head keys)
    (height : Nat) (transactionId : TransactionId)
    (miss : Snapshot.lookupRecorded transactionId (recordedAt footprint height) = none)
    (answer : (id : TransactionId) × TxAnswer head id) (member : answer ∈ footprint.transactions)
    (same : answer.1 = transactionId) :
    (∃ opens : DurableSpent.Opens head.spentRoot (DurableSpent.transactionKey answer.1) none,
        answer.2 = .absent opens) ∨
      ∃ found : ByTx head answer.1, answer.2 = .present found ∧ height < found.height :=
  recordedAt_lookup_none_list height transactionId footprint.transactions miss answer member same

/-- **A consumed bit of a view is the spent map's verified answer at the served
height**: true exactly when the nullifier's answer opens an inserting height at
or below it. -/
theorem spentAt_true {head : Head store} {keys : Keys} (footprint : VerifiedFootprint head keys)
    (height : Nat) (nullifier : StableNullifier) (consumed : spentAt footprint height nullifier = true) :
    ∃ answer ∈ footprint.nullifiers, answer.1 = nullifier ∧
      ∃ inserted, answer.2.value = some inserted ∧ inserted ≤ height := by
  unfold spentAt at consumed
  cases found : footprint.nullifiers.find? (·.1 = nullifier) with
  | none => simp [found] at consumed
  | some answer =>
      rw [found] at consumed
      have member := List.mem_of_find?_eq_some found
      have key := List.find?_some found
      simp only [decide_eq_true_eq] at key
      simp only [Option.any_some] at consumed
      cases value : answer.2.value with
      | none => simp [value] at consumed
      | some inserted =>
          simp only [value, Option.any_some, decide_eq_true_eq] at consumed
          exact ⟨answer, member, key, inserted, value, consumed⟩

/-- Every declared nullifier has an answer, so a false bit is that answer's
verified absence or an insertion above the served height. -/
theorem spentAt_false {head : Head store} {keys : Keys} (footprint : VerifiedFootprint head keys)
    (height : Nat) (nullifier : StableNullifier) (declared : nullifier ∈ keys.nullifiers)
    (fresh : spentAt footprint height nullifier = false) :
    ∃ answer ∈ footprint.nullifiers, answer.1 = nullifier ∧
      (answer.2.value = none ∨ ∃ inserted, answer.2.value = some inserted ∧ height < inserted) := by
  have present : ∃ answer ∈ footprint.nullifiers, answer.1 = nullifier := by
    rw [← footprint.nullifiersExact] at declared
    obtain ⟨answer, member, key⟩ := List.mem_map.mp declared
    exact ⟨answer, member, key⟩
  unfold spentAt at fresh
  cases found : footprint.nullifiers.find? (·.1 = nullifier) with
  | none =>
      obtain ⟨answer, member, key⟩ := present
      have := List.find?_eq_none.mp found answer member
      simp [key] at this
  | some answer =>
      rw [found] at fresh
      have member := List.mem_of_find?_eq_some found
      have key := List.find?_some found
      simp only [decide_eq_true_eq] at key
      refine ⟨answer, member, key, ?_⟩
      cases value : answer.2.value with
      | none => exact Or.inl rfl
      | some inserted =>
          simp only [Option.any_some, value, decide_eq_false_iff_not, Nat.not_le] at fresh
          exact Or.inr ⟨inserted, rfl, fresh⟩

/-- **A view agrees on the declared keys with any snapshot that holds the
served state and gives the authenticated history's answers at the served
height**: the premise `Family.covers` consumes (`DurableView.run_view`). -/
theorem viewAt_agrees (served : Served rootBytes store) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) (full : DataSnapshot rootBytes)
    (roots : full.model.roots = served.roots) (bytes : full.canonicalBytes = served.canonicalBytes)
    (available : full.model.available = served.available)
    (journal : ∀ transactionId ∈ keys.transactions,
      Snapshot.lookupRecorded transactionId full.model.journal =
        Snapshot.lookupRecorded transactionId (recordedAt footprint served.height))
    (consumed : ∀ nullifier ∈ keys.nullifiers,
      full.model.consumed nullifier = spentAt footprint served.height nullifier) :
    AgreesOnKeys keys (served.viewAt footprint) full :=
  ⟨roots.symm, bytes.symm, available.symm,
    fun transactionId member => (journal transactionId member).symm,
    fun nullifier member => (consumed nullifier member).symm⟩

/-! ## Producers -/

/-- From the full verified materialization of the same Store. -/
def ofLoaded (loaded : Loaded rootBytes) (_sameStart : store.logStart = loaded.logStart) :
    Served rootBytes store :=
  ⟨bare loaded.snapshot, loaded.image.seed, loaded.cellIds, loaded.image.seed.absentBytes, loaded.height,
    loaded.chain, loaded.worldRoot, fun cellId missing => by
      rw [Loaded.cellIds_eq] at missing
      exact DurableCheckpoint.resume_outside_support rootBytes loaded.image loaded.baseHeight loaded.base
        loaded.snapshot loaded.resumed cellId missing,
    by rw [Loaded.cellIds_eq]; exact DurableCheckpoint.nodup_eraseDups _⟩

@[simp] theorem ofLoaded_canonicalBytes (loaded : Loaded rootBytes) (sameStart : store.logStart = loaded.logStart) :
    (ofLoaded loaded sameStart).canonicalBytes = loaded.snapshot.canonicalBytes := rfl
@[simp] theorem ofLoaded_roots (loaded : Loaded rootBytes) (sameStart : store.logStart = loaded.logStart) :
    (ofLoaded loaded sameStart).roots = loaded.snapshot.model.roots := rfl

/-- The full materialization serves exactly what its image enumerates. -/
theorem ofLoaded_cellIds (loaded : Loaded rootBytes) (sameStart : store.logStart = loaded.logStart) :
    (ofLoaded loaded sameStart).cellIds = loaded.image.cellIds :=
  Loaded.cellIds_eq loaded

theorem replay_history_length :
    ∀ (records : List IntentRecord) (before after : DataSnapshot rootBytes),
      replay rootBytes before records = some after →
        after.model.history.length = before.model.history.length + records.length
  | [], before, after, replayed => by cases Option.some.inj replayed; rfl
  | record :: records, before, after, replayed => by
      unfold replay at replayed
      cases bound : record.bind? rootBytes with
      | none => simp [bound] at replayed
      | some intent =>
          simp only [bound, bind, Option.bind] at replayed
          cases executed : DurableDataIntent.execute .complete before intent with
          | accepted next =>
              simp only [executed] at replayed
              have installed := DurableReceiver.execute_accepted_install before intent next executed
              rw [replay_history_length records next after replayed, installed]
              simp [DataSnapshot.install_model, List.length_append]
              omega
          | replayed recorded => simp [executed] at replayed
          | rejected reason => simp [executed] at replayed
          | crashed point next => simp [executed] at replayed

/-- **The full shape's authority clock is its height**: its history has one
event per accepted record (`CredentialAuthorityDomainReceiver.clockOf`). -/
theorem history_length_eq_height (loaded : Loaded rootBytes) :
    loaded.snapshot.model.history.length = loaded.height := by
  have resumed := loaded.resumed
  unfold DurableCheckpoint.resume at resumed
  split at resumed
  next =>
    rw [replay_history_length _ _ _ resumed]
    simp only [State.snapshot, List.length_map, Loaded.height]
    rw [← List.length_append, List.take_append_drop]
  next => simp at resumed

/-- A served state from a base state and the records replayed after it: the
base's cells plus every cell the records wrote, the bytes of the replay. Private:
only the producers below call it, each from a base and records it verified. -/
private def ofBase (seed : Seed) (base : State) (records : List IntentRecord)
    (snapshot : DataSnapshot rootBytes)
    (replayed : replay rootBytes (base.snapshot rootBytes []) records = some snapshot)
    (height : Nat) (chain worldRoot : Digest) : Served rootBytes store :=
  ⟨bare snapshot, seed, extendIds (base.cells.map Prod.fst) records, base.absentBytes, height, chain,
    worldRoot, fun cellId missing => by
      obtain ⟨notBase, notWritten⟩ := not_mem_extendIds missing
      show snapshot.canonicalBytes cellId = _
      rw [DurableReceiver.replay_outside_support rootBytes _ _ cellId notWritten snapshot replayed]
      simp [State.snapshot, DurableReceiver.Seed.lookup_missing base.cells cellId notBase],
    DurableCheckpoint.nodup_eraseDups _⟩

/-- A past height from `Reader.stateAt`: the base's cells plus every cell its
verified records wrote, the chain after its last verified record (or the
base's), and the world root over that state. -/
def ofStateAt {seed : Seed} {head : Head store} {height : Nat}
    (state : StateAt rootBytes seed head height) : Served rootBytes store :=
  let records := state.reads.map (·.2.record)
  let cellIds := extendIds (state.baseState.cells.map Prod.fst) records
  let chain := (state.reads.getLast?.map (·.2.verified.chain)).getD state.baseChain
  ofBase seed state.baseState records state.snapshot state.replayed height chain
    (WorldRoot.deployedRoot (entriesOf state.snapshot.model.roots cellIds height chain))

/-- **A past state's chain is the chain after its verified records** from the
base (the reads are chained, `StateAt.chained`). -/
theorem ofStateAt_chain {seed : Seed} {head : Head store} {height : Nat}
    (state : StateAt rootBytes seed head height) :
    (ofStateAt state).chain =
      DurableCheckpointCodec.chainAfter state.baseChain (state.reads.map (·.2.record)) := by
  have chained := state.chained
  show (state.reads.getLast?.map (·.2.verified.chain)).getD state.baseChain = _
  cases hreads : state.reads.getLast? with
  | none =>
      have : state.reads = [] := List.getLast?_eq_none_iff.mp hreads
      simp [this, DurableCheckpointCodec.chainAfter]
  | some last =>
      have nonempty : state.reads ≠ [] := by
        intro empty; rw [empty] at hreads; cases hreads
      have position : state.reads.length - 1 < state.reads.length := by
        have := List.length_pos_of_ne_nil nonempty; omega
      have lastEq : last = state.reads[state.reads.length - 1] := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem position] at hreads
        exact (Option.some.inj hreads).symm
      have at_ := congrArg (fun l => l[state.reads.length - 1]?) chained
      simp only [List.getElem?_map, List.getElem?_eq_getElem position, List.getElem?_range position,
        Option.map_some] at at_
      have taken : (state.reads.map (·.2.record)).take (state.reads.length - 1 + 1) =
          state.reads.map (·.2.record) := by
        rw [Nat.sub_add_cancel (List.length_pos_of_ne_nil nonempty)]; simp
      rw [taken] at at_
      simp only [Option.map_some, Option.getD_some]
      rw [lastEq]
      exact Option.some.inj at_

/-- A past state's bytes are the replay of its verified records from its base. -/
theorem ofStateAt_canonicalBytes {seed : Seed} {head : Head store} {height : Nat}
    (state : StateAt rootBytes seed head height) :
    (ofStateAt state).canonicalBytes = state.snapshot.canonicalBytes := rfl

/-! ## One accepted record -/

open Minidregg.Compiler.DurableReceiverIO (recordSlots lastVal_cellIds lastVal_writes lastVal_cells_system
  lookupPost_member lookupPost_isSome)
open Minidregg.Kernel.WorldRootCache (lastVal lastVal_cons)

/-- The state after one record the executor accepted on a view of this state. -/
def advance (served : Served rootBytes store) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) (intent : DurableDataIntent.DataIntent rootBytes)
    (next : DataSnapshot rootBytes)
    (executed : DurableDataIntent.execute .complete (served.viewAt footprint) intent = .accepted next)
    (chain worldRoot : Digest) : Served rootBytes store :=
  ⟨bare next, served.seed, extendIds served.cellIds [IntentRecord.ofIntent intent], served.absentBytes,
    served.height + 1, chain, worldRoot, fun cellId missing => by
      obtain ⟨notOld, notWritten⟩ := not_mem_extendIds missing
      have installed := DurableReceiver.execute_accepted_install _ intent next executed
      subst installed
      show (DurableDataIntent.DataSnapshot.lookupPostBytes cellId intent.writes).getD
        ((served.viewAt footprint).canonicalBytes cellId) = _
      rw [DurableReceiver.lookupPostBytes_missing intent.writes cellId
        (by simpa [IntentRecord.ofIntent] using notWritten)]
      exact served.outsideAbsent cellId notOld,
    DurableCheckpoint.nodup_eraseDups _⟩

@[simp] theorem advance_height (served : Served rootBytes store) {head : Head store} {keys : Keys}
    (footprint : VerifiedFootprint head keys) (intent : DurableDataIntent.DataIntent rootBytes)
    (next : DataSnapshot rootBytes)
    (executed : DurableDataIntent.execute .complete (served.viewAt footprint) intent = .accepted next)
    (chain worldRoot : Digest) :
    (served.advance footprint intent next executed chain worldRoot).height = served.height + 1 := rfl

/-- **The served entries after an accepted intent** are the entries before it
overwritten by the record's slot writes (`recordSlots`): what lets the root
cache advance by one path per written cell. -/
theorem entries_step (ids : List CellId) (nodup : ids.Nodup) (before next : DataSnapshot rootBytes)
    (intent : DurableDataIntent.DataIntent rootBytes) (height : Nat) (chain chain' : Digest)
    (executed : DurableDataIntent.execute .complete before intent = .accepted next) (k : WorldRoot.Key) :
    lastVal (entriesOf next.model.roots (extendIds ids [IntentRecord.ofIntent intent]) (height + 1) chain') k =
      (lastVal (recordSlots (height + 1) chain' (IntentRecord.ofIntent intent)) k).or
        (lastVal (entriesOf before.model.roots ids height chain) k) := by
  have accepted : next = DurableDataIntent.DataSnapshot.install before intent ∧
      (intent.writes.map DataWrite.cellId).Nodup := by
    unfold DurableDataIntent.execute at executed
    split at executed
    · split at executed <;> cases executed
    · split at executed
      · cases executed
      · rename_i passed
        cases executed
        refine ⟨rfl, ?_⟩
        unfold DurableDataIntent.DataIntent.preflight at passed
        split at passed
        · cases passed
        split at passed
        · cases passed
        split at passed
        · cases passed
        rename_i lower
        unfold DurableCommitProtocol.Intent.preflight at lower
        by_contra repeated
        have mapped : ¬ (intent.erase.rootWrites.map DurableCommitProtocol.RootWrite.cellId).Nodup := by
          simpa [DurableDataIntent.DataIntent.erase, List.map_map, Function.comp_def] using repeated
        simp only [mapped, decide_false, Bool.not_false, if_true] at lower
        split at lower <;> cases lower
  obtain ⟨installed, writesNodup⟩ := accepted
  subst installed
  cases k with
  | system =>
      simp only [entriesOf, recordSlots, lastVal_cons, lastVal_cells_system, IntentRecord.ofIntent]
      simp
  | cell n =>
      have newIds : ∀ id : CellId, id ∈ extendIds ids [IntentRecord.ofIntent intent] ↔
          id ∈ ids ∨ id ∈ intent.writes.map DataWrite.cellId := by
        intro id
        simp only [extendIds, List.mem_eraseDups, List.mem_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, IntentRecord.ofIntent]
      have extended : (extendIds ids [IntentRecord.ofIntent intent]).Nodup :=
        DurableCheckpoint.nodup_eraseDups _
      simp only [entriesOf, recordSlots, lastVal_cons, reduceCtorEq, if_false, Option.or_none]
      rw [lastVal_cellIds _ extended, lastVal_cellIds _ nodup]
      simp only [IntentRecord.ofIntent] at newIds ⊢
      rw [lastVal_writes _ writesNodup]
      have roots : (DurableDataIntent.DataSnapshot.install before intent).model.roots ⟨n⟩ =
          (DurableCommitProtocol.Snapshot.lookupPost ⟨n⟩ intent.erase.rootWrites).getD
            (before.model.roots ⟨n⟩) := rfl
      rw [roots]
      simp only [DurableDataIntent.DataIntent.erase]
      cases found : DurableCommitProtocol.Snapshot.lookupPost (⟨n⟩ : CellId)
          (intent.writes.map fun write =>
        ({ cellId := write.cellId, expectedPre := write.expectedPre, exactPost := write.exactPost } :
          DurableCommitProtocol.RootWrite CellId)) with
      | some post =>
          have member := lookupPost_member _ _ found
          simp [(newIds ⟨n⟩).mpr (Or.inr member)]
      | none =>
          have unwritten : (⟨n⟩ : CellId) ∉ intent.writes.map DataWrite.cellId := by
            intro member
            have := lookupPost_isSome _ _ member
            rw [found] at this
            cases this
          by_cases old : (⟨n⟩ : CellId) ∈ ids
          · simp [(newIds ⟨n⟩).mpr (Or.inl old), old]
          · have absent : ¬ ((⟨n⟩ : CellId) ∈ ids ∨ (⟨n⟩ : CellId) ∈ intent.writes.map DataWrite.cellId) := by
              tauto
            rw [← newIds] at absent
            simp [absent, old]

end Served

/-! ## The light opening of the head (KN2 2b-1, step 3)

The open reads the seed, the latest checkpoint and the entries from it to the
head (`Transport.readFromCheckpoint`, one call, under the head anchor), and
nothing older. What it establishes, each refused by name:

* the Store's epoch (the seed label), before anything else;
* the checkpoint: its MAC (`openSealed`), and the MAC of the entry at its height
  for the checkpoint's chain, accumulator frontier and spent root
  (`verifyTagged`): the checkpoint sits on the log the head anchor fixes;
* every entry after it: canonical record bytes (named by height), the chain over
  the stored bytes, its tag's MAC (`verifyTags`), the frontier its tag carries
  (`walkFrontier`), and the spent root its tag carries, re-derived by inserting
  the record's transaction id and nullifiers into the spent map at the
  checkpoint's version (`DurableSpent.insertAll` refuses a key already present:
  a transaction or nullifier accepted before the checkpoint);
* the replay of those records from the checkpoint state through the executor;
* the head: its tag's MAC under the Store's key (`Head.verify`) and the root it
  carries equal to the replayed world root.

Records at or below the checkpoint are verified at use (`Reader`) and by
`store audit`; the full shape's open (the ratchet-listed full materialization) still
verifies every one, for its ratchet-listed callers. -/

structure Opening (rootBytes : List UInt8 → Digest) where
  store : StoreIdentity
  head : Head store
  served : Served rootBytes store
  heightExact : served.height = head.height
  chainExact : served.chain = head.chain
  /-- The world root, cached; advanced by one path per written cell. -/
  roots : DurableReceiverIO.RootCache
  rootsExact : DurableReceiverIO.RootsExact roots
    (Served.entriesOf served.roots served.cellIds served.height served.chain)
  /-- The height of the checkpoint the opening resumed from (the cadence). -/
  baseHeight : Nat

private def decodeRecordsAt : Nat → List DurableReceiverIO.Entry → Except String (List IntentRecord)
  | _, [] => .ok []
  | height, entry :: rest => do
      let some record := DurableCheckpointCodec.recordFrame.decode entry.record
        | throw s!"noncanonical durable log record at height {height}"
      return record :: (← decodeRecordsAt (height + 1) rest)

/-- The spent root after each record, re-derived from the map at the base's
version: each record's keys inserted at its height; the root after each must be
the one its (MAC-verified) tag carries. The rows each record writes are kept in a
map (newest wins) laid over the Store's rows. -/
private def checkSpent (rows : List Bool → Option DurableSpent.Row) :
    Std.HashMap (List Bool) DurableSpent.Row → Digest → Nat → List (IntentRecord × Digest) →
      Except String Unit
  | _, _, _, [] => .ok ()
  | written, root, height, (record, carried) :: rest => do
      let keys := DurableSpent.recordKeys record.transactionId record.nullifiers
      let current := fun path => (written.get? path).or (rows path)
      let (next, writes) ← match DurableSpent.insertAll current root height keys with
        | .ok result => pure result
        | .error message => throw s!"durable log record at height {height}: {message}"
      if next ≠ carried then
        throw s!"the tag at height {height} carries a spent root the log does not reach"
      checkSpent rows (writes.foldl (fun map row => map.insert row.1 row.2) written) next (height + 1) rest

/-- The light opening of an opened Store's head. -/
def openHead (transport : DurableReceiverIO.Transport) (rootBytes : List UInt8 → Digest) :
    IO (Except String (Opening rootBytes)) := do
  -- Operator measurement control: MINI_OPEN_TIMING=1 prints each stage's elapsed time to stderr.
  let timing := (← IO.getEnv "MINI_OPEN_TIMING") == some "1"
  let started ← IO.monoMsNow
  let lap := fun (label : String) => do
    if timing then IO.eprintln s!"light open {label}: {(← IO.monoMsNow) - started} ms"
  if let .ok (some seedBytes) := ← transport.peekSeed then
    if let some refusal := (DurableCheckpointCodec.SeedEpoch.ofBytes seedBytes).refusal then
      return .error s!"durable store refused: {refusal}"
  let key ← match ← transport.key with
    | .error message => return .error message
    | .ok key => pure key
  let stored ← match ← transport.readFromCheckpoint with
    | .error message => return .error message
    | .ok none => return .error "durable store is not initialized"
    | .ok (some stored) => pure stored
  lap "read"
  let some seedBytes := stored.seed | return .error "durable seed missing"
  if let some refusal := (DurableCheckpointCodec.SeedEpoch.ofBytes seedBytes).refusal then
    return .error s!"durable store refused: {refusal}"
  let some seed := DurableCheckpointCodec.seedFrame.decode seedBytes
    | return .error "noncanonical durable seed"
  let logStart := transport.logStart seed
  let store := StoreIdentity.ofOpen key logStart
  let headHeight := stored.head
  -- The base: the seed at height 0, or the checkpoint sitting on the log.
  let ((baseHeight, base, baseChain, baseFrontier, baseSpent, suffix) :
      Nat × State × Digest × List (Nat × Digest) × Digest × List DurableReceiverIO.Entry) ←
    match stored.checkpoint with
    | none =>
        if stored.entries.length ≠ headHeight then
          return .error "durable log head does not match its entries"
        pure (0, State.ofSeed seed, logStart, ([] : List (Nat × Digest)), DurableSpent.emptyDigest,
          stored.entries)
    | some checkpoint =>
        match DurableCheckpointCodec.openSealed key rootBytes checkpoint.bytes with
        | .error reason => return .error s!"checkpoint refused: {repr reason}"
        | .ok body =>
            if body.height ≠ checkpoint.height ∨ body.height = 0 ∨ body.height > headHeight then
              return .error "checkpoint height does not match the log"
            if stored.entries.length ≠ headHeight - body.height + 1 then
              return .error "durable log head does not match its entries"
            let some atCheckpoint := stored.entries.head? | return .error "checkpoint height has no log entry"
            match DurableHistory.verifyTagged key body.height atCheckpoint.tag body.chain
                (DurableHistory.frontierDigest body.height body.frontier) body.spentRoot with
            | .error refusal => return .error s!"checkpoint does not sit on the log: {refusal.message}"
            | .ok _ =>
                pure (body.height, body.state, body.chain, body.frontier, body.spentRoot,
                  stored.entries.drop 1)
  lap "checkpoint"
  if !((base.cells.map Prod.fst).Nodup ∧ base.absentBytes = seed.absentBytes) then
    return .error "checkpoint state is not admissible for this Store's seed"
  let records ← match decodeRecordsAt (baseHeight + 1) suffix with
    | .error message => return .error message
    | .ok records => pure records
  let chains := DurableLogTags.chainPrefixesStored baseChain (suffix.map (·.record))
  if let .error message := DurableLogTags.verifyTags key baseHeight chains (suffix.map (·.tag)) then
    return .error message
  let frontier ← match DurableReceiverIO.walkFrontier baseHeight baseFrontier (suffix.zip (chains.drop 1)) with
    | .error message => return .error message
    | .ok frontier => pure frontier
  lap "records, chain, tags, frontier"
  let carriedSpent ← match suffix.mapM fun entry => DurableHistory.trailerCarried entry.tag with
    | none => return .error "durable log tag malformed"
    | some carried => pure (carried.map (·.spentRoot))
  let keys := records.flatMap fun record => DurableSpent.recordKeys record.transactionId record.nullifiers
  -- Rows down to 32 bits first; every prefix when what they open does not verify.
  let shallow ← match ← DurableReceiverIO.spentRows transport baseHeight keys 32 with
    | .error message => return .error message
    | .ok rows => pure rows
  lap "spent rows read"
  if let .error _ := checkSpent shallow {} baseSpent (baseHeight + 1) (records.zip carriedSpent) then
    let deep ← match ← DurableReceiverIO.spentRows transport baseHeight keys with
      | .error message => return .error message
      | .ok rows => pure rows
    if let .error message := checkSpent deep {} baseSpent (baseHeight + 1) (records.zip carriedSpent) then
      return .error message
  lap "spent map"
  let headChain := chains.getLast?.getD baseChain
  match replayed : replay rootBytes (base.snapshot rootBytes []) records with
  | none => return .error "durable log suffix does not replay through the canonical executor"
  | some snapshot =>
      let cellIds := extendIds (base.cells.map Prod.fst) records
      let entries := Served.entriesOf snapshot.model.roots cellIds headHeight headChain
      let roots := DurableReceiverIO.RootCache.ofEntries entries
      let rootsExact := DurableReceiverIO.RootsExact.ofEntries entries
      let worldRoot := if rootsExact.injective then roots.root else WorldRoot.deployedRoot entries
      let served : Served rootBytes store :=
        Served.ofBase seed base records snapshot replayed headHeight headChain worldRoot
      lap "replay and root"
      if zero : headHeight = 0 then
        if genesisChain : headChain = store.logStart then
          let head := Head.genesis store worldRoot
          return .ok ⟨store, head, served, zero.trans (Head.genesis_fields store worldRoot).1.symm,
            genesisChain.trans (Head.genesis_fields store worldRoot).2.1.symm, roots, rootsExact, baseHeight⟩
        else return .error "an empty durable log's chain is not its genesis log start"
      else
        let some last := suffix.getLast? | return .error "durable head entry missing"
        match verified : Head.verify store headHeight last.tag headChain frontier with
        | .error refusal => return .error refusal.message
        | .ok head =>
            if head.root ≠ worldRoot then
              return .error "durable log head root differs from the replayed root"
            have fields := Head.verify_fields verified
            return .ok ⟨store, head, served, fields.1.symm, fields.2.1.symm, roots, rootsExact, baseHeight⟩


/-! ## The light receive (KN2 2b-1, step 4)

One record on a light opening: the request's footprint (its transaction id and
nullifiers) read from the authenticated history, the executor run on the view
(`DurableView.execute_view`: it cannot tell the view from the full snapshot),
the same gates the full receive applies, the spent map extended from the head's
MAC-verified spent root, the accumulator and the root cache advanced by one
path each, and one append of the entry with its node rows. -/

/-- The Reader of a light opening at its head. -/
def Opening.reader (transport : DurableReceiverIO.Transport) (rootBytes : List UInt8 → Digest)
    (opening : Opening rootBytes) : DurableHistoryReader.Reader rootBytes opening.store :=
  { head := opening.head, seed := opening.served.seed
    atHeight := DurableHistoryStore.atHeight transport opening.head
    byTx := DurableHistoryStore.byTx transport opening.head
    spent := DurableHistoryStore.spent transport opening.head
    range := DurableHistoryStore.range transport opening.head
    stateAt := DurableHistoryStore.stateAt transport rootBytes opening.served.seed opening.head }

/-- The keys the shared executor consults for an intent (`DurableView.executeFamily`). -/
def intentKeys (intent : DurableDataIntent.DataIntent rootBytes) : Keys :=
  ⟨[intent.transactionId], intent.nullifiers⟩

/-- **The light receive executes what the full receive executes**: on any full
snapshot that holds the served state and answers the intent's transaction id
and nullifiers as the authenticated history does at the served height, the
executor's observable outcome (rejection, replayed record, or accepted roots,
bytes and allowance) is the one `receiveServed` acts on
(`DurableView.executeFamily`, `Served.viewAt_agrees`). -/
theorem receive_executes_as_full {store : StoreIdentity} (served : Served rootBytes store) {head : Head store}
    (intent : DurableDataIntent.DataIntent rootBytes) (footprint : VerifiedFootprint head (intentKeys intent))
    (full : DataSnapshot rootBytes)
    (roots : full.model.roots = served.roots) (bytes : full.canonicalBytes = served.canonicalBytes)
    (available : full.model.available = served.available)
    (journal : Snapshot.lookupRecorded intent.transactionId full.model.journal =
      Snapshot.lookupRecorded intent.transactionId (Served.recordedAt footprint served.height))
    (consumed : ∀ nullifier ∈ intent.nullifiers,
      full.model.consumed nullifier = Served.spentAt footprint served.height nullifier) :
    DurableView.observe (DurableDataIntent.execute .complete (served.viewAt footprint) intent) =
      DurableView.observe (DurableDataIntent.execute .complete full intent) :=
  DurableView.run_view DurableView.executeFamily intent _ _
    (served.viewAt_agrees footprint full roots bytes available
      (fun transactionId member => by
        simp only [intentKeys, List.mem_singleton] at member
        subst member
        exact journal)
      consumed)

inductive Received (rootBytes : List UInt8 → Digest) (opening : Opening rootBytes)
    (intent : DurableDataIntent.DataIntent rootBytes) where
  /-- Appended (or found appended) and read back byte for byte; `next` is the
  opening after exactly this record. -/
  | appended (kind : DurableReceiverIO.Confirmation) (next : Opening rootBytes)
      (height : next.head.height = opening.head.height + 1) (entry : DurableReceiverIO.Entry)
      (entryExact : entry.record = DurableCheckpointCodec.recordFrame.encode (IntentRecord.ofIntent intent))
  /-- The transaction was already accepted: its verified record. -/
  | replayed (recorded : Intent TransactionId CellId StableNullifier ReplayEnvelope)
  | rejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- The checkpoint state of a served state (`DurableCheckpoint.State.ofSnapshot`'s shape). -/
def Served.checkpointState {store : StoreIdentity} (served : Served rootBytes store) : State :=
  ⟨served.absentBytes, served.cells, served.available⟩

def receiveServed (transport : DurableReceiverIO.Transport) (rootBytes : List UInt8 → Digest)
    (opening : Opening rootBytes) (intent : DurableDataIntent.DataIntent rootBytes) :
    IO (Received rootBytes opening intent) := do
  let served := opening.served
  let head := opening.head
  let reader := opening.reader transport rootBytes
  let footprint ← match ← reader.footprint (intentKeys intent) with
    | .error refusal => return .unavailable refusal.message
    | .ok footprint => pure footprint
  let view := served.viewAt footprint
  match executed : DurableDataIntent.execute .complete view intent with
  | .replayed recorded => return .replayed recorded
  | .rejected reason => return .rejected reason
  | .crashed _ _ => return .unavailable "unexpected complete-schedule outcome"
  | .accepted next =>
      if let .error reason := transport.sourceGate view intent then return .rejected reason
      if let some systemId := transport.systemCell then
        if let .error reason := Kernel.TailBound.gate systemId (served.height + 1) served.chain view intent then
          return .rejected reason
      let key := opening.store.key
      let height := served.height + 1
      let record := IntentRecord.ofIntent intent
      let recordBytes := DurableCheckpointCodec.recordFrame.encode record
      let chain := DurableCheckpointCodec.chainStep served.chain record
      -- The spent map after the head (MAC-verified, carried by the head's tag), this record's keys inserted.
      let keys := DurableSpent.recordKeys intent.transactionId intent.nullifiers
      let (spentAfter, spentWrites) ← match ← DurableReceiverIO.withSpentRows transport served.height keys
          (fun rows => DurableSpent.insertAll rows head.spentRoot height keys) with
        | .ok result => pure result
        | .error message => return .unavailable message
      -- The root cache advanced by the record's slot writes.
      let roots := opening.rootsExact.advance (DurableReceiverIO.recordSlots height chain record)
        (Served.entries_step served.cellIds served.cellIds_nodup view next intent served.height
          served.chain chain executed)
      let entries := Served.entriesOf next.model.roots (extendIds served.cellIds [record]) height chain
      let worldRoot := if roots.2.injective then roots.1.root else WorldRoot.deployedRoot entries
      let leaf := DurableHistory.leafDigest height recordBytes chain worldRoot
      let frontierAfter := DurableHistory.Frontier.push head.frontier leaf
      let nodes := DurableReceiverIO.appendNodes
        (DurableHistory.completedNodes head.frontier height leaf) spentWrites
      let entry : DurableReceiverIO.Entry := ⟨recordBytes, DurableHistory.trailer key height
        ⟨worldRoot, chain, DurableHistory.frontierDigest height frontierAfter, spentAfter⟩⟩
      let confirm := fun (kind : DurableReceiverIO.Confirmation) => do
        match ← transport.read height false with
        | .error message => return Received.uncertain s!"append attempted; readback unavailable: {message}"
        | .ok none => return .uncertain "append attempted; the Store is not initialized"
        | .ok (some stored) =>
            match stored.entries.head? with
            | none => return .uncertain "append attempted; entry absent on readback"
            | some readBack =>
                if readBack ≠ entry then return .contention
                match verified : Head.verify opening.store height entry.tag chain frontierAfter with
                | .error refusal => return .unavailable refusal.message
                | .ok head' =>
                    have fields := Head.verify_fields verified
                    let served' := served.advance footprint intent next executed chain worldRoot
                    -- A due checkpoint (a function of the height alone); a failed seal loses nothing.
                    let sealedAt ←
                      if transport.checkpointEvery > 0 && height % transport.checkpointEvery == 0 then do
                        let sealed := DurableCheckpointCodec.sealAt key height chain frontierAfter spentAfter
                          served'.checkpointState worldRoot
                        match ← transport.putCheckpoint height
                            (DurableCheckpointCodec.checkpointFrame.encode sealed) with
                        | .ok () => pure height
                        | .error _ => pure opening.baseHeight
                      else pure opening.baseHeight
                    return .appended kind
                      ⟨opening.store, head', served', fields.1.symm, fields.2.1.symm, roots.1, roots.2, sealedAt⟩
                      (by rw [fields.1, ← opening.heightExact]) entry rfl
      match ← transport.append height entry nodes with
      | .installed => confirm .installed
      | .alreadyPresent => confirm .installed
      | .conflict => return .contention
      | .uncertain _ => confirm .recoveredAfterUncertainResponse

#assert_axioms Served.recordedAt_some
#assert_axioms Served.recordedAt_none
#assert_axioms Served.spentAt_true
#assert_axioms Served.spentAt_false
#assert_axioms Served.viewAt_agrees
#assert_axioms Served.ofLoaded_cellIds
#assert_axioms Served.history_length_eq_height
#assert_axioms Served.ofStateAt_chain
#assert_axioms Served.entries_step
#assert_axioms receive_executes_as_full

end Minidregg.Compiler.DurableServed
