/-
# Kernel.DurableDataIntent -- payload-bearing guarded durable settlement

`DurableCommitProtocol.Intent` is intentionally generic: it durably installs
roots and appends an opaque event.  A data-bearing deployment needs a narrower
adapter.  Its replay identity must retain the exact canonical post bytes and
every read-only root guard, rather than remembering only their digests.

This module supplies that adapter with deployment-stable digest identifiers:

* transaction and cell identifiers are `TypedAuthorization.Digest`;
* nullifiers and events are versioned, domain-separated byte envelopes;
* every written post image carries canonical bytes and an exact root binding;
* read-only cells are guarded against the same snapshot used for installation;
* erasure places writes, bytes, guards, and the event inside the journaled
  replay envelope, so same-id retry cannot silently change any of them;
* a data snapshot stores canonical bytes beside the existing atomic snapshot,
  with root/byte coherence preserved by installation.

No injectivity property is requested of `rootBytes`.  The executable teeth use
an intentionally non-injective length digest and still reject a same-root byte
tamper because replay equality compares the bytes themselves.

As in `DurableCommitProtocol`, this is a model boundary.  The last section
states the proof-relevant simulation a database, filesystem, or replicated
service must discharge; it does not manufacture physical durability.
-/
import Kernel.DurableCommitProtocol

namespace Minidregg.Kernel.DurableDataIntent

open Minidregg.Theory
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableCommitProtocol

set_option autoImplicit false

universe u v

/-! ## Stable wire carriers -/

/-- Durable transaction identifiers cross deployments as digests, not host
object identities or process-local counters. -/
abbrev TransactionId := TypedAuthorization.Digest

/-- Durable cell identifiers use the same deployment-stable digest carrier. -/
abbrev CellId := TypedAuthorization.Digest

/-- A stable nullifier retains its codec version, semantic domain, stable id,
and exact canonical bytes.  The bytes remain part of replay identity even if a
deployment's digest function has collisions. -/
structure StableNullifier where
  codecVersion : Nat
  domain : TypedAuthorization.Digest
  nullifierId : TypedAuthorization.Digest
  canonicalBytes : List UInt8
  deriving DecidableEq, Repr

/-- The semantic event stored with a transaction.  This is an envelope rather
than an executor-owned string: version, domain, stable event id, and canonical
payload all survive retry and recovery. -/
structure StableEvent where
  codecVersion : Nat
  domain : TypedAuthorization.Digest
  eventId : TypedAuthorization.Digest
  canonicalBytes : List UInt8
  deriving DecidableEq, Repr

/-- A canonical post image.  `exactPost` is not trusted independently: a
`DataIntent` below proves that `rootBytes canonicalPostBytes = exactPost`. -/
structure DataWrite where
  cellId : CellId
  expectedPre : TypedAuthorization.Digest
  exactPost : TypedAuthorization.Digest
  canonicalPostBytes : List UInt8
  deriving DecidableEq, Repr

/-- A root guard for a cell that is observed but not written. -/
structure ReadGuard where
  cellId : CellId
  expectedRoot : TypedAuthorization.Digest
  deriving DecidableEq, Repr

/-- Exact payload journaled as the existing protocol's opaque `Event`.

Keeping `writes` here is deliberate even though their roots are also erased to
`RootWrite`: this copy is the canonical byte payload.  Keeping `readGuards`
here makes guard changes transaction conflicts on same-id replay. -/
structure ReplayEnvelope where
  writes : List DataWrite
  readGuards : List ReadGuard
  event : StableEvent
  deriving DecidableEq, Repr

/-! ## The bound data intent and faithful erasure -/

/-- A payload-bearing durable intent.  Root binding and read/write disjointness
are construction obligations, not flags asserted by the executor. -/
structure DataIntent (rootBytes : List UInt8 -> TypedAuthorization.Digest) where
  transactionId : TransactionId
  writes : List DataWrite
  readGuards : List ReadGuard
  nullifiers : List StableNullifier
  exactCharge : Charge
  event : StableEvent
  postRootsBound : forall write, write ∈ writes ->
    rootBytes write.canonicalPostBytes = write.exactPost
  guardsReadOnly : forall guard, guard ∈ readGuards ->
    guard.cellId ∉ writes.map DataWrite.cellId

namespace DataIntent

variable {rootBytes : List UInt8 -> TypedAuthorization.Digest}

/-- Erase data semantics into the already verified durable protocol.  The
opaque event is the complete replay envelope, so erasure loses neither bytes
nor guards. -/
def erase (intent : DataIntent rootBytes) :
    Intent TransactionId CellId StableNullifier ReplayEnvelope where
  transactionId := intent.transactionId
  rootWrites := intent.writes.map fun write =>
    { cellId := write.cellId
      expectedPre := write.expectedPre
      exactPost := write.exactPost }
  nullifiers := intent.nullifiers
  exactCharge := intent.exactCharge
  event :=
    { writes := intent.writes
      readGuards := intent.readGuards
      event := intent.event }

@[simp] theorem erase_transactionId (intent : DataIntent rootBytes) :
    intent.erase.transactionId = intent.transactionId := rfl

@[simp] theorem erase_rootWrites (intent : DataIntent rootBytes) :
    intent.erase.rootWrites = intent.writes.map fun write =>
      { cellId := write.cellId
        expectedPre := write.expectedPre
        exactPost := write.exactPost } := rfl

@[simp] theorem erase_nullifiers (intent : DataIntent rootBytes) :
    intent.erase.nullifiers = intent.nullifiers := rfl

@[simp] theorem erase_event (intent : DataIntent rootBytes) :
    intent.erase.event =
      { writes := intent.writes
        readGuards := intent.readGuards
        event := intent.event } := rfl

/-- Exact characterization of erased replay identity.  In particular, bytes
and guards are not quotiented by their roots. -/
theorem erase_samePayload_iff (left right : DataIntent rootBytes) :
    left.erase.SamePayload right.erase <->
      left.writes = right.writes /\
      left.readGuards = right.readGuards /\
      left.nullifiers = right.nullifiers /\
      left.exactCharge = right.exactCharge /\
      left.event = right.event := by
  simp only [Intent.SamePayload, erase]
  constructor
  · rintro ⟨_, nullifiers, charge, envelope⟩
    have writes : left.writes = right.writes :=
      congrArg ReplayEnvelope.writes envelope
    have guards : left.readGuards = right.readGuards :=
      congrArg ReplayEnvelope.readGuards envelope
    have event : left.event = right.event :=
      congrArg ReplayEnvelope.event envelope
    exact ⟨writes, guards, nullifiers, charge, event⟩
  · rintro ⟨writes, guards, nullifiers, charge, event⟩
    simp [writes, guards, nullifiers, charge, event]

@[simp] theorem erase_sameCheck_eq_true_iff
    (left right : DataIntent rootBytes) :
    left.erase.sameCheck right.erase = true <->
      left.writes = right.writes /\
      left.readGuards = right.readGuards /\
      left.nullifiers = right.nullifiers /\
      left.exactCharge = right.exactCharge /\
      left.event = right.event := by
  rw [Intent.sameCheck_eq_true_iff, erase_samePayload_iff]

end DataIntent

/-! ## Canonical data snapshot and coherent installation -/

/-- The atomic protocol snapshot paired with the canonical bytes from which
each current root is derived.  There is no independent, unbound data cache. -/
structure DataSnapshot (rootBytes : List UInt8 -> TypedAuthorization.Digest) where
  model : Snapshot TransactionId CellId StableNullifier ReplayEnvelope
  canonicalBytes : CellId -> List UInt8
  coherent : forall cellId, rootBytes (canonicalBytes cellId) = model.roots cellId

namespace DataSnapshot

variable {rootBytes : List UInt8 -> TypedAuthorization.Digest}

/-- Find canonical post bytes using exactly the same first-match discipline as
`DurableCommitProtocol.Snapshot.lookupPost`. -/
def lookupPostBytes (cellId : CellId) : List DataWrite -> Option (List UInt8)
  | [] => none
  | write :: rest =>
      if write.cellId = cellId then some write.canonicalPostBytes
      else lookupPostBytes cellId rest

private theorem lookupPost_bound_list
    (cellId : CellId) (writes : List DataWrite)
    (bound : forall write, write ∈ writes ->
      rootBytes write.canonicalPostBytes = write.exactPost) :
    Option.map rootBytes (lookupPostBytes cellId writes) =
      Snapshot.lookupPost cellId
        (writes.map fun write =>
          { cellId := write.cellId
            expectedPre := write.expectedPre
            exactPost := write.exactPost }) := by
  induction writes with
  | nil => rfl
  | cons write rest ih =>
      simp only [lookupPostBytes, List.map_cons, Snapshot.lookupPost]
      split
      · simp only [Option.map_some, Option.some.injEq]
        exact bound write (by simp)
      · apply ih
        intro member memberRest
        exact bound member (by simp [memberRest])

private theorem lookupPost_bound
    (intent : DataIntent rootBytes) (cellId : CellId) :
    Option.map rootBytes (lookupPostBytes cellId intent.writes) =
      Snapshot.lookupPost cellId intent.erase.rootWrites := by
  exact lookupPost_bound_list cellId intent.writes intent.postRootsBound

/-- Install canonical bytes and the existing durable model in one constructor.
Coherence follows from every post image's root binding; no injectivity of
`rootBytes` is used. -/
def install (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    DataSnapshot rootBytes where
  model := Snapshot.install before.model intent.erase
  canonicalBytes := fun cellId =>
    (lookupPostBytes cellId intent.writes).getD (before.canonicalBytes cellId)
  coherent := by
    intro cellId
    rw [Snapshot.install_roots]
    change rootBytes
        ((lookupPostBytes cellId intent.writes).getD
          (before.canonicalBytes cellId)) =
      (Snapshot.lookupPost cellId intent.erase.rootWrites).getD
        (before.model.roots cellId)
    have bound := lookupPost_bound intent cellId
    cases bytesResult : lookupPostBytes cellId intent.writes with
    | none =>
        have rootNone : Snapshot.lookupPost cellId intent.erase.rootWrites = none := by
          simpa [bytesResult] using bound.symm
        simp only [Option.getD_none]
        rw [rootNone]
        simp only [Option.getD_none]
        exact before.coherent cellId
    | some bytes =>
        have rootSome :
            Snapshot.lookupPost cellId intent.erase.rootWrites =
              some (rootBytes bytes) := by
          simpa [bytesResult] using bound.symm
        simp only [Option.getD_some]
        rw [rootSome]
        simp only [Option.getD_some]

@[simp] theorem install_model (before : DataSnapshot rootBytes)
    (intent : DataIntent rootBytes) :
    (install before intent).model = Snapshot.install before.model intent.erase := rfl

@[simp] theorem install_canonicalBytes (before : DataSnapshot rootBytes)
    (intent : DataIntent rootBytes) (cellId : CellId) :
    (install before intent).canonicalBytes cellId =
      (lookupPostBytes cellId intent.writes).getD
        (before.canonicalBytes cellId) := rfl

@[simp] theorem install_coherent (before : DataSnapshot rootBytes)
    (intent : DataIntent rootBytes) (cellId : CellId) :
    rootBytes ((install before intent).canonicalBytes cellId) =
      (install before intent).model.roots cellId :=
  (install before intent).coherent cellId

end DataSnapshot

/-! ## Read-guarded fail-closed execution -/

inductive RejectReason
  | durable (reason : DurableCommitProtocol.RejectReason)
  | staleReadGuard
  deriving DecidableEq, Repr

namespace DataIntent

variable {rootBytes : List UInt8 -> TypedAuthorization.Digest}

def readGuardsMatchCheck (before : DataSnapshot rootBytes)
    (intent : DataIntent rootBytes) : Bool :=
  intent.readGuards.all fun guard =>
    decide (before.model.roots guard.cellId = guard.expectedRoot)

@[simp] theorem readGuardsMatchCheck_eq_true_iff
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    intent.readGuardsMatchCheck before = true <->
      forall guard, guard ∈ intent.readGuards ->
        before.model.roots guard.cellId = guard.expectedRoot := by
  simp [readGuardsMatchCheck]

/-- Guard checking and ordinary durable preflight read one immutable model
snapshot.  An implementation may not validate against one snapshot and install
against another without violating the refinement premise below. -/
def preflight (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    Except RejectReason Unit :=
  if !intent.readGuardsMatchCheck before then
    .error .staleReadGuard
  else
    match intent.erase.preflight before.model with
    | .error reason => .error (.durable reason)
    | .ok () => .ok ()

end DataIntent

inductive Outcome (rootBytes : List UInt8 -> TypedAuthorization.Digest)
  | accepted (next : DataSnapshot rootBytes)
  | replayed (recorded :
      Intent TransactionId CellId StableNullifier ReplayEnvelope)
  | rejected (reason : RejectReason)
  | crashed (point : CrashPoint) (next : DataSnapshot rootBytes)

namespace Outcome

variable {rootBytes : List UInt8 -> TypedAuthorization.Digest}

def storeAfter (before : DataSnapshot rootBytes) : Outcome rootBytes -> DataSnapshot rootBytes
  | .accepted next => next
  | .replayed _ => before
  | .rejected _ => before
  | .crashed _ next => next

end Outcome

/-- Retry-safe, guarded, payload-bearing execution.  Journal lookup remains
first so a lost successful response replays after roots have changed. -/
def execute {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (schedule : Schedule) (before : DataSnapshot rootBytes)
    (intent : DataIntent rootBytes) : Outcome rootBytes :=
  match Snapshot.lookupRecorded intent.transactionId before.model.journal with
  | some recorded =>
      if recorded.sameCheck intent.erase then .replayed recorded
      else .rejected (.durable .transactionConflict)
  | none =>
      match intent.preflight before with
      | .error reason => .rejected reason
      | .ok () =>
          match schedule with
          | .complete => .accepted (DataSnapshot.install before intent)
          | .crash .beforeAtomicInstall => .crashed .beforeAtomicInstall before
          | .crash .afterAtomicInstall =>
              .crashed .afterAtomicInstall (DataSnapshot.install before intent)

/-- Atomicity lifts from root state to root-bound canonical data: every outcome
exposes either the complete old data snapshot or the complete installation. -/
theorem execute_no_partial_data_commit
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (schedule : Schedule) (before : DataSnapshot rootBytes)
    (intent : DataIntent rootBytes) :
    (execute schedule before intent).storeAfter before = before \/
      (execute schedule before intent).storeAfter before =
        DataSnapshot.install before intent := by
  simp only [execute]
  split
  · split <;> simp [Outcome.storeAfter]
  · split
    · simp [Outcome.storeAfter]
    · split <;> simp [Outcome.storeAfter]

/-- Positive non-vacuity: a fresh, guarded intent passing preflight installs
its exact data-bearing snapshot. -/
theorem execute_complete_ready
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (unrecorded : Snapshot.lookupRecorded intent.transactionId
      before.model.journal = none)
    (ready : intent.preflight before = .ok ()) :
    execute .complete before intent =
      .accepted (DataSnapshot.install before intent) := by
  simp [execute, unrecorded, ready]

/-- A stale observed root rejects before any post data is exposed. -/
theorem stale_read_guard_rejected
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (stale : exists guard, guard ∈ intent.readGuards /\
      before.model.roots guard.cellId != guard.expectedRoot) :
    intent.preflight before = .error .staleReadGuard := by
  rcases stale with ⟨guard, member, stale⟩
  have failed : intent.readGuardsMatchCheck before = false := by
    simp only [DataIntent.readGuardsMatchCheck, List.all_eq_false]
    exact ⟨guard, member, by simpa using stale⟩
  simp [DataIntent.preflight, failed]

/-! ## Explicit physical refinement ceiling -/

/-- A physical data handler refines this layer only by simulating an actual
guarded execution over root-bound data snapshots.  `PhysicalStep` is evidence,
not an `atomic` or `fsyncSucceeded` Boolean. -/
structure ImplementationRefinement
    (rootBytes : List UInt8 -> TypedAuthorization.Digest)
    (PhysicalState : Type u)
    (PhysicalStep : PhysicalState -> DataIntent rootBytes -> PhysicalState -> Type v)
    (Represents : PhysicalState -> DataSnapshot rootBytes -> Prop) : Prop where
  simulates : forall {physicalBefore physicalAfter modelBefore intent},
    Represents physicalBefore modelBefore ->
    PhysicalStep physicalBefore intent physicalAfter ->
    exists schedule,
      Represents physicalAfter
        ((execute schedule modelBefore intent).storeAfter modelBefore)

/-- Conditional physical atomicity and data coherence.  No concrete storage
engine is claimed to satisfy the premise in this module. -/
theorem physical_step_no_partial_data_commit
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    {PhysicalState : Type u}
    {PhysicalStep : PhysicalState -> DataIntent rootBytes -> PhysicalState -> Type v}
    {Represents : PhysicalState -> DataSnapshot rootBytes -> Prop}
    (refinement : ImplementationRefinement rootBytes PhysicalState PhysicalStep Represents)
    {physicalBefore physicalAfter : PhysicalState}
    {modelBefore : DataSnapshot rootBytes}
    {intent : DataIntent rootBytes}
    (represented : Represents physicalBefore modelBefore)
    (stepped : PhysicalStep physicalBefore intent physicalAfter) :
    exists modelAfter,
      Represents physicalAfter modelAfter /\
      (modelAfter = modelBefore \/
        modelAfter = DataSnapshot.install modelBefore intent) /\
      (forall cellId,
        rootBytes (modelAfter.canonicalBytes cellId) =
          modelAfter.model.roots cellId) := by
  rcases refinement.simulates represented stepped with ⟨schedule, simulated⟩
  let modelAfter := (execute schedule modelBefore intent).storeAfter modelBefore
  refine ⟨modelAfter, simulated, execute_no_partial_data_commit schedule modelBefore intent, ?_⟩
  exact modelAfter.coherent

/-! ## Executable collision, TOCTOU, and tamper teeth -/

namespace Witness

/-- Intentionally collision-prone: this witness makes clear that no theorem
below smuggles in hash injectivity. -/
def lengthRoot (bytes : List UInt8) : TypedAuthorization.Digest :=
  ⟨bytes.length⟩

def readCell : CellId := ⟨11⟩
def writeCell : CellId := ⟨22⟩

def beforeBytes (cellId : CellId) : List UInt8 :=
  if cellId = readCell then [1, 2, 3]
  else if cellId = writeCell then [4, 5]
  else []

def beforeModel : Snapshot TransactionId CellId StableNullifier ReplayEnvelope where
  roots := fun cellId => lengthRoot (beforeBytes cellId)
  consumed := fun _ => false
  available := fun _ => 10
  history := []
  journal := []

def before : DataSnapshot lengthRoot where
  model := beforeModel
  canonicalBytes := beforeBytes
  coherent := fun _ => rfl

def nullifier : StableNullifier where
  codecVersion := 1
  domain := ⟨71⟩
  nullifierId := ⟨72⟩
  canonicalBytes := [110, 117, 108]

def event : StableEvent where
  codecVersion := 1
  domain := ⟨81⟩
  eventId := ⟨82⟩
  canonicalBytes := [101, 118, 116]

def write : DataWrite where
  cellId := writeCell
  expectedPre := ⟨2⟩
  exactPost := ⟨4⟩
  canonicalPostBytes := [6, 7, 8, 9]

def guard : ReadGuard where
  cellId := readCell
  expectedRoot := ⟨3⟩

def intent : DataIntent lengthRoot where
  transactionId := ⟨91⟩
  writes := [write]
  readGuards := [guard]
  nullifiers := [nullifier]
  exactCharge := fun _ => 1
  event := event
  postRootsBound := by simp [write, lengthRoot]
  guardsReadOnly := by simp [guard, write, readCell, writeCell]

@[simp] theorem ready : intent.preflight before = .ok () := by decide

@[simp] theorem positive_install :
    execute .complete before intent =
      .accepted (DataSnapshot.install before intent) := by
  apply execute_complete_ready
  · rfl
  · exact ready

@[simp] theorem installed_post_bytes :
    (DataSnapshot.install before intent).canonicalBytes writeCell =
      [6, 7, 8, 9] := by decide

@[simp] theorem installed_post_root :
    (DataSnapshot.install before intent).model.roots writeCell = ⟨4⟩ := by decide

/-- A concurrent move changes only the read-only cell, producing another
coherent snapshot.  The write cell remains at its original pre-state. -/
def afterConcurrentReadMoveBytes (cellId : CellId) : List UInt8 :=
  if cellId = readCell then [1, 2, 3, 4, 5]
  else beforeBytes cellId

def afterConcurrentReadMoveModel :
    Snapshot TransactionId CellId StableNullifier ReplayEnvelope :=
  { beforeModel with
    roots := fun cellId => lengthRoot (afterConcurrentReadMoveBytes cellId) }

def afterConcurrentReadMove : DataSnapshot lengthRoot where
  model := afterConcurrentReadMoveModel
  canonicalBytes := afterConcurrentReadMoveBytes
  coherent := fun _ => rfl

@[simp] theorem stale_after_concurrent_read_move :
    intent.preflight afterConcurrentReadMove = .error .staleReadGuard := by decide

/-- **TOCTOU tooth.**  The same intent is ready at the snapshot it observed and
rejected at a coherent snapshot in which only its read guard moved. -/
theorem no_toctou_reuse :
    intent.preflight before = .ok () /\
      intent.preflight afterConcurrentReadMove = .error .staleReadGuard :=
  ⟨ready, stale_after_concurrent_read_move⟩

/-- A different four-byte post image has the same intentionally weak root. -/
def tamperedWrite : DataWrite :=
  { write with canonicalPostBytes := [9, 9, 9, 9] }

theorem collision_without_injectivity :
    lengthRoot write.canonicalPostBytes =
      lengthRoot tamperedWrite.canonicalPostBytes /\
    write.canonicalPostBytes ≠ tamperedWrite.canonicalPostBytes := by decide

def tamperedIntent : DataIntent lengthRoot where
  transactionId := intent.transactionId
  writes := [tamperedWrite]
  readGuards := intent.readGuards
  nullifiers := intent.nullifiers
  exactCharge := intent.exactCharge
  event := intent.event
  postRootsBound := by simp [tamperedWrite, write, lengthRoot]
  guardsReadOnly := by simp [intent, guard, tamperedWrite, write, readCell, writeCell]

/-- Exact roots, charge, ids, nullifiers, guards, and event may agree while
canonical post bytes differ.  Erased replay identity still rejects it. -/
@[simp] theorem byte_tamper_changes_replay_identity :
    intent.erase.sameCheck tamperedIntent.erase = false := by decide

/-- **Tamper tooth.**  After the honest transaction is journaled, submitting
the same transaction id with colliding post bytes is a conflict, not a replay. -/
@[simp] theorem byte_tamper_rejected_after_install :
    execute .complete (DataSnapshot.install before intent) tamperedIntent =
      .rejected (.durable .transactionConflict) := by rfl

end Witness

end Minidregg.Kernel.DurableDataIntent

/-! Kernel-facing theorem audit. -/

/-- info: 'Minidregg.Kernel.DurableDataIntent.execute_no_partial_data_commit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableDataIntent.execute_no_partial_data_commit
/-- info: 'Minidregg.Kernel.DurableDataIntent.physical_step_no_partial_data_commit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableDataIntent.physical_step_no_partial_data_commit
/-- info: 'Minidregg.Kernel.DurableDataIntent.Witness.no_toctou_reuse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableDataIntent.Witness.no_toctou_reuse
/-- info: 'Minidregg.Kernel.DurableDataIntent.Witness.byte_tamper_rejected_after_install' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.DurableDataIntent.Witness.byte_tamper_rejected_after_install
