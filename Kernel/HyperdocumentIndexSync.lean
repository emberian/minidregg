/-
# Kernel.HyperdocumentIndexSync -- bounded backlink/range indexing and causal sync

This module defines one deliberately bounded index over canonical
`Hyperdocument.LinkRecord`s.  The source corpus and the derived rows are both
retained, so an index can be checked for freshness instead of being trusted as
an opaque host search result.

Queries are target keyed or stable-source-range keyed and inspect every slot in
the finite domain.  The completeness theorems are consequently exact for that
domain only.  They say nothing about links outside the page, crawler coverage,
network availability, external finality, or collision resistance.

A delta names its exact before/after causal checkpoints and exact before/after
slot values.  Applying it updates both source and derived row at the same slot;
retry is accepted only when the after checkpoint and after row are already
present.  The small device model distinguishes volatile staging from durable
sync so crash-before-sync, crash-after-sync, reopen, and retry have explicit
semantics.  Refinement to a physical filesystem or database is not asserted.
-/
import Theory.Hyperdocument

namespace Minidregg.Kernel.HyperdocumentIndexSync

open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Canonical bounded source and derived rows -/

/-- The source datum indexed by one finite slot.  `linkId` is retained rather
than reconstructed from the record. -/
structure SourceEntry where
  linkId : LinkId
  record : LinkRecord
  deriving DecidableEq

/-- A live derived row contains every key needed by the two query surfaces. -/
structure IndexedRow where
  linkId : LinkId
  sourceDocument : DocumentId
  sourceRange : Option StableRange
  target : LinkTarget
  relation : Digest
  operation : OperationId
  deriving DecidableEq

/-- Tombstones are canonical source data but have no live index row. -/
def SourceEntry.row? (entry : SourceEntry) : Option IndexedRow :=
  if entry.record.tombstonedAt = none then
    some
      { linkId := entry.linkId
        sourceDocument := entry.record.sourceDocument
        sourceRange := entry.record.source
        target := entry.record.target
        relation := entry.record.relation
        operation := entry.record.operation }
  else
    none

abbrev Corpus (capacity : Nat) := Fin capacity -> Option SourceEntry
abbrev Index (capacity : Nat) := Fin capacity -> Option IndexedRow

/-- The only canonical index derivation: one live row at the same finite slot
as its source entry. -/
def rebuild {capacity : Nat} (corpus : Corpus capacity) : Index capacity :=
  fun slot => (corpus slot).bind SourceEntry.row?

/-- One causal checkpoint for this bounded history slice.  The optional head is
the exact content-addressed event known at `sequence`; absence is permitted for
an empty slice. -/
structure CausalCheckpoint where
  historyDomain : Digest
  document : DocumentId
  head : Option VersionEventId
  sequence : Nat
  deriving DecidableEq

/-- An index step stays in one history/document stream and advances exactly one
sequence number.  This is a local causal condition, not a finality judgment. -/
def CausalCheckpoint.Follows
    (before after : CausalCheckpoint) : Prop :=
  after.historyDomain = before.historyDomain ∧
    after.document = before.document ∧
    after.sequence = before.sequence + 1

instance (before after : CausalCheckpoint) :
    Decidable (CausalCheckpoint.Follows before after) := by
  unfold CausalCheckpoint.Follows
  infer_instance

/-- A cursor is meaningful only together with its causal checkpoint.  `nextSlot`
is first-order wire data; `Valid` below bounds it by the finite page capacity. -/
structure SyncCursor where
  checkpoint : CausalCheckpoint
  nextSlot : Nat
  deriving DecidableEq

def SyncCursor.Valid (capacity : Nat) (cursor : SyncCursor) : Prop :=
  cursor.nextSlot <= capacity

def SyncCursor.Complete (capacity : Nat) (cursor : SyncCursor) : Prop :=
  cursor.nextSlot = capacity

/-- Both checkpoints are stored.  Advancing the source without the index is
therefore observable as `staleCheckpoint`, and modifying derived rows without
changing the source is observable as `staleRows`. -/
structure Snapshot (capacity : Nat) where
  sourceCheckpoint : CausalCheckpoint
  indexCheckpoint : CausalCheckpoint
  corpus : Corpus capacity
  index : Index capacity
  cursor : SyncCursor

def Snapshot.Fresh {capacity : Nat} (snapshot : Snapshot capacity) : Prop :=
  snapshot.indexCheckpoint = snapshot.sourceCheckpoint ∧
    snapshot.cursor.checkpoint = snapshot.sourceCheckpoint ∧
    snapshot.cursor.Complete capacity ∧
    snapshot.index = rebuild snapshot.corpus

inductive Status
  | current
  | staleCheckpoint
  | staleCursor
  | incompleteCursor
  | staleRows
  deriving DecidableEq, Repr

/-- Executable freshness classification.  Checkpoint drift is reported before
row drift so callers cannot mistake an old complete index for a current one. -/
def status {capacity : Nat} (snapshot : Snapshot capacity) : Status :=
  if snapshot.indexCheckpoint != snapshot.sourceCheckpoint then
    .staleCheckpoint
  else if snapshot.cursor.checkpoint != snapshot.sourceCheckpoint then
    .staleCursor
  else if snapshot.cursor.nextSlot != capacity then
    .incompleteCursor
  else if snapshot.index != rebuild snapshot.corpus then
    .staleRows
  else
    .current

theorem status_current_iff {capacity : Nat} (snapshot : Snapshot capacity) :
    status snapshot = .current ↔ snapshot.Fresh := by
  by_cases checkpoint :
      snapshot.indexCheckpoint = snapshot.sourceCheckpoint
  · by_cases cursor :
        snapshot.cursor.checkpoint = snapshot.sourceCheckpoint
    · by_cases complete : snapshot.cursor.nextSlot = capacity
      · by_cases rows : snapshot.index = rebuild snapshot.corpus
        · simp [status, Snapshot.Fresh, SyncCursor.Complete, checkpoint, cursor,
            complete, rows]
        · simp [status, Snapshot.Fresh, SyncCursor.Complete, checkpoint, cursor,
            complete, rows]
      · simp [status, Snapshot.Fresh, SyncCursor.Complete, checkpoint, cursor,
          complete]
    · simp [status, Snapshot.Fresh, SyncCursor.Complete, checkpoint, cursor]
  · simp [status, Snapshot.Fresh, SyncCursor.Complete, checkpoint]

theorem stale_checkpoint_detected {capacity : Nat}
    (snapshot : Snapshot capacity)
    (stale : snapshot.indexCheckpoint ≠ snapshot.sourceCheckpoint) :
    status snapshot = .staleCheckpoint := by
  simp [status, stale]

/-! ## Exact finite-domain query surfaces -/

/-- Target-keyed backlink lookup at one finite slot.  Enumerating all
`Fin capacity` slots is the complete bounded query. -/
def backlinkAt {capacity : Nat} (index : Index capacity)
    (target : LinkTarget) (slot : Fin capacity) : Option IndexedRow :=
  match index slot with
  | none => none
  | some row => if row.target = target then some row else none

/-- Stable-range lookup at one finite slot.  Both source document and exact
stored range are keys; there is no byte-offset or renderer-derived overlap. -/
def stableRangeAt {capacity : Nat} (index : Index capacity)
    (document : DocumentId) (range : StableRange)
    (slot : Fin capacity) : Option IndexedRow :=
  match index slot with
  | none => none
  | some row =>
      if row.sourceDocument = document ∧ row.sourceRange = some range then
        some row
      else
        none

theorem backlinkAt_sound {capacity : Nat} (index : Index capacity)
    (target : LinkTarget) (slot : Fin capacity) (row : IndexedRow)
    (found : backlinkAt index target slot = some row) :
    index slot = some row ∧ row.target = target := by
  unfold backlinkAt at found
  split at found
  · contradiction
  · rename_i stored equal
    split at found
    · have rowExact : stored = row := Option.some.inj found
      subst row
      exact ⟨equal, by assumption⟩
    · contradiction

theorem stableRangeAt_sound {capacity : Nat} (index : Index capacity)
    (document : DocumentId) (range : StableRange) (slot : Fin capacity)
    (row : IndexedRow)
    (found : stableRangeAt index document range slot = some row) :
    index slot = some row ∧ row.sourceDocument = document ∧
      row.sourceRange = some range := by
  unfold stableRangeAt at found
  split at found
  · contradiction
  · rename_i stored equal
    split at found
    · have rowExact : stored = row := Option.some.inj found
      subst row
      exact ⟨equal, by assumption⟩
    · contradiction

/-- Exact target-query completeness for every slot in the bounded domain. -/
theorem backlinkAt_complete {capacity : Nat} (snapshot : Snapshot capacity)
    (fresh : snapshot.Fresh) (slot : Fin capacity) (entry : SourceEntry)
    (source : snapshot.corpus slot = some entry)
    (live : entry.record.tombstonedAt = none) :
    backlinkAt snapshot.index entry.record.target slot =
      some
        { linkId := entry.linkId
          sourceDocument := entry.record.sourceDocument
          sourceRange := entry.record.source
          target := entry.record.target
          relation := entry.record.relation
          operation := entry.record.operation } := by
  rcases fresh with ⟨_, _, _, exactRows⟩
  rw [exactRows]
  simp [backlinkAt, rebuild, source, SourceEntry.row?, live]

/-- Exact stable-range-query completeness for every live source carrying that
range inside the bounded domain. -/
theorem stableRangeAt_complete {capacity : Nat} (snapshot : Snapshot capacity)
    (fresh : snapshot.Fresh) (slot : Fin capacity) (entry : SourceEntry)
    (range : StableRange) (source : snapshot.corpus slot = some entry)
    (live : entry.record.tombstonedAt = none)
    (hasRange : entry.record.source = some range) :
    stableRangeAt snapshot.index entry.record.sourceDocument range slot =
      some
        { linkId := entry.linkId
          sourceDocument := entry.record.sourceDocument
          sourceRange := entry.record.source
          target := entry.record.target
          relation := entry.record.relation
          operation := entry.record.operation } := by
  rcases fresh with ⟨_, _, _, exactRows⟩
  rw [exactRows]
  simp [stableRangeAt, rebuild, source, SourceEntry.row?, live, hasRange]

/-! ## Exact one-slot delta maintenance -/

structure Delta (capacity : Nat) where
  beforeCheckpoint : CausalCheckpoint
  afterCheckpoint : CausalCheckpoint
  slot : Fin capacity
  before : Option SourceEntry
  after : Option SourceEntry
  deriving DecidableEq

def Snapshot.MatchesDelta {capacity : Nat} (snapshot : Snapshot capacity)
    (delta : Delta capacity) : Prop :=
  snapshot.sourceCheckpoint = delta.beforeCheckpoint ∧
    snapshot.corpus delta.slot = delta.before ∧
    delta.beforeCheckpoint.Follows delta.afterCheckpoint

instance {capacity : Nat} (snapshot : Snapshot capacity)
    (delta : Delta capacity) : Decidable (snapshot.MatchesDelta delta) := by
  unfold Snapshot.MatchesDelta
  infer_instance

/-- The unique exact post-state of a matched delta. -/
def Snapshot.advance {capacity : Nat} (snapshot : Snapshot capacity)
    (delta : Delta capacity) : Snapshot capacity where
  sourceCheckpoint := delta.afterCheckpoint
  indexCheckpoint := delta.afterCheckpoint
  corpus := Function.update snapshot.corpus delta.slot delta.after
  index := Function.update snapshot.index delta.slot
    (delta.after.bind SourceEntry.row?)
  cursor := ⟨delta.afterCheckpoint, capacity⟩

theorem rebuild_update {capacity : Nat} (corpus : Corpus capacity)
    (slot : Fin capacity) (entry : Option SourceEntry) :
    rebuild (Function.update corpus slot entry) =
      Function.update (rebuild corpus) slot (entry.bind SourceEntry.row?) := by
  funext current
  by_cases equal : current = slot
  · subst current
    simp [rebuild]
  · simp [rebuild, Function.update, equal]

/-- Updating the exact source and derived slot preserves freshness. -/
theorem Snapshot.advance_fresh {capacity : Nat}
    (snapshot : Snapshot capacity) (delta : Delta capacity)
    (fresh : snapshot.Fresh) :
    (snapshot.advance delta).Fresh := by
  rcases fresh with ⟨_, _, _, exactRows⟩
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp only [Snapshot.advance]
  rw [rebuild_update, exactRows]

inductive RejectReason
  | staleCheckpoint
  | staleRow
  | nonCausal
  deriving DecidableEq, Repr

inductive ApplyResult (capacity : Nat)
  | applied (snapshot : Snapshot capacity)
  | replayed (snapshot : Snapshot capacity)
  | rejected (reason : RejectReason)

/-- Apply one exact causal delta, recognize an exact retry, or fail closed.  A
checkpoint match alone never authorizes a row overwrite. -/
def applyDelta {capacity : Nat} (snapshot : Snapshot capacity)
    (delta : Delta capacity) : ApplyResult capacity :=
  if snapshot.sourceCheckpoint = delta.beforeCheckpoint then
    if snapshot.corpus delta.slot = delta.before then
      if delta.beforeCheckpoint.Follows delta.afterCheckpoint then
        .applied (snapshot.advance delta)
      else
        .rejected .nonCausal
    else
      .rejected .staleRow
  else if snapshot.sourceCheckpoint = delta.afterCheckpoint ∧
      snapshot.corpus delta.slot = delta.after then
    .replayed snapshot
  else
    .rejected .staleCheckpoint

theorem applyDelta_matched {capacity : Nat} (snapshot : Snapshot capacity)
    (delta : Delta capacity) (matched : snapshot.MatchesDelta delta) :
    applyDelta snapshot delta = .applied (snapshot.advance delta) := by
  rcases matched with ⟨checkpoint, row, causal⟩
  simp [applyDelta, checkpoint, row, causal]

theorem applyDelta_retry {capacity : Nat} (snapshot : Snapshot capacity)
    (delta : Delta capacity)
    (causal : delta.beforeCheckpoint.Follows delta.afterCheckpoint) :
    applyDelta (snapshot.advance delta) delta =
      .replayed (snapshot.advance delta) := by
  have different : delta.afterCheckpoint ≠ delta.beforeCheckpoint := by
    intro equal
    have sequence := causal.2.2
    rw [equal] at sequence
    omega
  simp [applyDelta, Snapshot.advance, different]

/-! ## Logical durable staging and reopen -/

/-- `staged` is volatile; only `durable` is returned by `reopen`. -/
structure Device (capacity : Nat) where
  durable : Snapshot capacity
  staged : Option (Snapshot capacity)

def Device.stage {capacity : Nat} (device : Device capacity)
    (next : Snapshot capacity) : Device capacity :=
  { device with staged := some next }

def Device.sync {capacity : Nat} (device : Device capacity) : Device capacity :=
  match device.staged with
  | none => device
  | some next => ⟨next, none⟩

def Device.crash {capacity : Nat} (device : Device capacity) : Device capacity :=
  ⟨device.durable, none⟩

def Device.reopen {capacity : Nat} (device : Device capacity) : Snapshot capacity :=
  device.durable

@[simp] theorem crash_before_sync_reopens_durable {capacity : Nat}
    (device : Device capacity) (next : Snapshot capacity) :
    (device.stage next).crash.reopen = device.durable :=
  rfl

@[simp] theorem crash_after_sync_reopens_next {capacity : Nat}
    (device : Device capacity) (next : Snapshot capacity) :
    ((device.stage next).sync.crash).reopen = next :=
  rfl

/-- Sync, crash, reopen, then retry recognizes precisely the already-installed
after checkpoint and row. -/
theorem sync_crash_reopen_retry {capacity : Nat}
    (device : Device capacity) (delta : Delta capacity)
    (causal : delta.beforeCheckpoint.Follows delta.afterCheckpoint) :
    applyDelta (((device.stage (device.durable.advance delta)).sync.crash).reopen)
      delta = .replayed (device.durable.advance delta) := by
  exact applyDelta_retry device.durable delta causal

/-! ## Axiom audit -/

/-- info: 'Minidregg.Kernel.HyperdocumentIndexSync.Snapshot.advance_fresh' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Snapshot.advance_fresh
/-- info: 'Minidregg.Kernel.HyperdocumentIndexSync.backlinkAt_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms backlinkAt_complete
/-- info: 'Minidregg.Kernel.HyperdocumentIndexSync.sync_crash_reopen_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sync_crash_reopen_retry

end Minidregg.Kernel.HyperdocumentIndexSync
