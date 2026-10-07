/-
# Compiler.DurableServed — the light state a request is served from (KN2 stage 2b-1, PINNED)

Requests are served from a `Served`: the state at a height (every cell's root
and canonical bytes, the allowance), the cell enumeration, the fresh-cell bytes,
the height, the log chain there, the genesis log start and the world root. It
carries NO history prefix: the journal / consumed / history inside its
snapshot are only what its producer verified — the records since its base, and
(for a request) the footprint answers laid over them (`DurableView.view`).

Producers:
* `Loaded.served` — from the full verified materialization (today's callers;
  the ratchet list `scripts/ports/full-loaded-callers.txt` only shrinks);
* `StateAt.served` — a past height from `Reader.stateAt` (checkpoint at or below
  it, MAC-verified, plus verified records): what history-selection consumers
  (PORT-B's `Candidate.prior`) are built from, instead of a genesis replay of
  the prefix;
* the head's light opening (2b-1, next): checkpoint + suffix + frontier + head
  tag + spent root, built by the open.

Consumers re-indexed onto `Served` (2b-1, in order): LoadedDirectory /
Opened / validateLoaded (`validateServed`), PreparedInvocation (invoke), then the
other write-path families. A consumer that needs a journal or consumed answer
beyond the producer's records declares it as a `DurableView.Family` key; it
never reads an "absent" it did not ask for.
-/
import Compiler.DurableHistoryStore

namespace Minidregg.Compiler.DurableServed

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent (DataSnapshot CellId DataWrite)
open Minidregg.Kernel.DurableReceiver (IntentRecord Seed)
open Minidregg.Kernel.DurableCheckpoint (State)
open Minidregg.Compiler.DurableReceiverIO (Loaded)
open Minidregg.Compiler.DurableHistory (Head StoreIdentity)
open Minidregg.Compiler.DurableHistoryReader (StateAt)
open Minidregg.Compiler.DurableCheckpointCodec (systemLeaf)

set_option autoImplicit false

structure Served (rootBytes : List UInt8 → Digest) where
  /-- The state at `height`; its journal/consumed/history hold only verified records. -/
  snapshot : DataSnapshot rootBytes
  /-- Every enumerable cell id at `height` (seeded or written), in enumeration order. -/
  cellIds : List CellId
  absentBytes : List UInt8
  height : Nat
  chain : Digest
  logStart : Digest
  worldRoot : Digest

/-- The cells a directory loads, in enumeration order. -/
def Served.cells {rootBytes : List UInt8 → Digest} (served : Served rootBytes) :
    List (CellId × List UInt8) :=
  served.cellIds.map fun cellId => (cellId, served.snapshot.canonicalBytes cellId)

/-- The world-root entries of a served state (C1's `worldEntries`). -/
def Served.entries {rootBytes : List UInt8 → Digest} (snapshot : DataSnapshot rootBytes)
    (cellIds : List CellId) (height : Nat) (chain : Digest) :
    List (WorldRoot.Key × Digest) :=
  (.system, systemLeaf height chain) ::
    cellIds.map fun cellId => (.cell cellId.value, snapshot.model.roots cellId)

/-- From the full verified materialization. -/
def ofLoaded {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) : Served rootBytes :=
  ⟨loaded.snapshot, loaded.cellIds, loaded.image.seed.absentBytes, loaded.height, loaded.chain,
    loaded.logStart, loaded.worldRoot⟩

/-- The full materialization serves exactly what its image enumerates. -/
theorem ofLoaded_cellIds {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    (ofLoaded loaded).cellIds = loaded.image.cellIds :=
  Loaded.cellIds_eq loaded

/-- Enumeration after records: the base's ids, then each record's newly written ids. -/
def extendIds (ids : List CellId) : List IntentRecord → List CellId
  | [] => ids
  | record :: rest =>
      extendIds (ids ++ (record.writes.map DataWrite.cellId).filter (· ∉ ids)).eraseDups rest

/-- A past height from `Reader.stateAt`: the snapshot it replayed, the base's
cells plus every cell its verified records wrote, the chain after its last
verified record (or the base's), and the world root over that state. -/
def ofStateAt {rootBytes : List UInt8 → Digest} {seed : Seed} {store : StoreIdentity}
    {head : Head store} {height : Nat} (state : StateAt rootBytes seed head height) :
    Served rootBytes :=
  let records := state.reads.map (·.2.record)
  let cellIds := extendIds (state.baseState.cells.map Prod.fst) records
  let chain := (state.reads.getLast?.map (·.2.verified.chain)).getD state.baseChain
  ⟨state.snapshot, cellIds, state.baseState.absentBytes, height, chain, store.logStart,
    WorldRoot.deployedRoot (Served.entries state.snapshot cellIds height chain)⟩

/-- **A past state's chain is the chain after its verified records** from the
base (the reads are chained, `StateAt.chained`). -/
theorem ofStateAt_chain {rootBytes : List UInt8 → Digest} {seed : Seed} {store : StoreIdentity}
    {head : Head store} {height : Nat} (state : StateAt rootBytes seed head height) :
    (ofStateAt state).chain =
      DurableCheckpointCodec.chainAfter state.baseChain (state.reads.map (·.2.record)) := by
  have chained := state.chained
  unfold ofStateAt
  simp only
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

#assert_axioms ofLoaded_cellIds
#assert_axioms ofStateAt_chain

end Minidregg.Compiler.DurableServed
