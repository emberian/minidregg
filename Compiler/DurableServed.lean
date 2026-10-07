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
        loaded.snapshot loaded.resumed cellId missing⟩

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

/-- A past height from `Reader.stateAt`: the base's cells plus every cell its
verified records wrote, the chain after its last verified record (or the
base's), and the world root over that state. -/
def ofStateAt {seed : Seed} {head : Head store} {height : Nat}
    (state : StateAt rootBytes seed head height) : Served rootBytes store :=
  let records := state.reads.map (·.2.record)
  let cellIds := extendIds (state.baseState.cells.map Prod.fst) records
  let chain := (state.reads.getLast?.map (·.2.verified.chain)).getD state.baseChain
  ⟨bare state.snapshot, seed, cellIds, state.baseState.absentBytes, height, chain,
    WorldRoot.deployedRoot (entriesOf state.snapshot.model.roots cellIds height chain),
    fun cellId missing => by
      obtain ⟨notBase, notWritten⟩ := not_mem_extendIds missing
      show state.snapshot.canonicalBytes cellId = _
      rw [DurableReceiver.replay_outside_support rootBytes _ _ cellId notWritten state.snapshot
        state.replayed]
      simp [State.snapshot, DurableReceiver.Seed.lookup_missing state.baseState.cells cellId notBase]⟩

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

end Served

#assert_axioms Served.recordedAt_some
#assert_axioms Served.recordedAt_none
#assert_axioms Served.spentAt_true
#assert_axioms Served.spentAt_false
#assert_axioms Served.viewAt_agrees
#assert_axioms Served.ofLoaded_cellIds
#assert_axioms Served.history_length_eq_height
#assert_axioms Served.ofStateAt_chain

end Minidregg.Compiler.DurableServed
