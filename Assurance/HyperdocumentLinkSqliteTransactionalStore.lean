/-
# Assurance.HyperdocumentLinkSqliteTransactionalStore

This module is the Lean authority for the isolated SQLite-backed forward-link
store.  It models the transaction boundary explicitly: an open transaction
and an inserted row are not cold-start visible, while a completed commit is.
It then joins the exact committed bytes to the existing guarded WAL witness,
Lean recovery controller, and human/agent client receipt.

The companion native crate treats the value as an opaque bounded BLOB and may
return only bytes, a publication status, or an error.  Its process-exit tests
exercise SQLite rollback-journal recovery around `COMMIT`; they do not prove
this model refines SQLite, SQLite refines its C implementation, Rust FFI is
correct, host locks are sound, sync requests reach stable media, or any
particular power-loss behavior.  Those premises remain explicit below.
-/
import Assurance.HyperdocumentLinkClientLocalFileCutover

namespace Minidregg.Assurance.HyperdocumentLinkSqliteTransactionalStore

open Minidregg.Assurance.HyperdocumentLinkLocalFileStore
open Minidregg.Assurance.HyperdocumentLinkClientCutover
open Minidregg.Assurance.HyperdocumentLinkClientCutover.LocalFile

set_option autoImplicit false

noncomputable section

/-! ## Lean-owned single-row transaction model -/

namespace TransactionModel

inductive Failure where
  | missing
  | tooLarge
  | conflict
  | busy
  | corruptOrTorn
  | native
  deriving DecidableEq, Repr

inductive PublishStatus where
  | installed
  | alreadyPresent
  deriving DecidableEq, Repr

inductive ImageHealth where
  | healthy
  | corrupt
  | torn
  deriving DecidableEq, Repr

/-- The transaction phase is proof-visible in Lean but never decoded by the
native adapter.  `inserted` is still rollback-journal state, not a publication.
-/
inductive TransactionPhase where
  | idle
  | begun
  | inserted (record : StoreModel.BoundedRecord)
  | exactRetry

structure State where
  committed : Option StoreModel.BoundedRecord
  transaction : TransactionPhase
  health : ImageHealth

def empty : State := ⟨none, .idle, .healthy⟩

def read (state : State) : Except Failure (List UInt8) :=
  match state.health with
  | .corrupt | .torn => .error .corruptOrTorn
  | .healthy =>
      match state.committed with
      | none => .error .missing
      | some record => .ok record.bytes

/-- `BEGIN IMMEDIATE` obtains the sole abstract write transaction. -/
def beginImmediate (state : State) : Except Failure State :=
  match state.health with
  | .corrupt | .torn => .error .corruptOrTorn
  | .healthy =>
      match state.transaction with
      | .idle => .ok { state with transaction := .begun }
      | _ => .error .busy

/-- Bind the opaque BLOB into the open transaction.  Byte equality is the only
native comparison: no link, intent, checksum, or authority meaning appears.
-/
def insert (state : State) (bytes : List UInt8) : Except Failure State :=
  if oversized : maxRecordBytes < bytes.length then
    .error .tooLarge
  else
    match state.health, state.transaction with
    | .healthy, .begun =>
        match state.committed with
        | none =>
            let record : StoreModel.BoundedRecord :=
              ⟨bytes, Nat.le_of_not_gt oversized⟩
            .ok { state with transaction := .inserted record }
        | some live =>
            if live.bytes = bytes then
              .ok { state with transaction := .exactRetry }
            else
              .error .conflict
    | .corrupt, _ | .torn, _ => .error .corruptOrTorn
    | .healthy, _ => .error .busy

/-- `COMMIT` is the only transition making an inserted row cold-start visible.
-/
def commit (state : State) : Except Failure (PublishStatus × State) :=
  match state.health, state.transaction with
  | .healthy, .inserted record =>
      .ok (.installed,
        { committed := some record, transaction := .idle, health := .healthy })
  | .healthy, .exactRetry =>
      .ok (.alreadyPresent, { state with transaction := .idle })
  | .corrupt, _ | .torn, _ => .error .corruptOrTorn
  | .healthy, _ => .error .missing

def publish (state : State) (bytes : List UInt8) :
    Except Failure (PublishStatus × State) :=
  match beginImmediate state with
  | .error failure => .error failure
  | .ok opened =>
      match insert opened bytes with
      | .error failure => .error failure
      | .ok inserted => commit inserted

/-- Abrupt process exit rolls an unfinished transaction back.  A completed
commit has already returned the state to `idle` and remains visible.
-/
def crash (state : State) : State :=
  { state with transaction := .idle }

def boundedFixture : StoreModel.BoundedRecord :=
  ⟨recoveryFixture, recoveryFixture_bounded⟩

def begunHonest : State :=
  { empty with transaction := .begun }

def insertedHonest : State :=
  { empty with transaction := .inserted boundedFixture }

def committedHonest : State :=
  { committed := some boundedFixture,
    transaction := .idle,
    health := .healthy }

@[simp] theorem honest_begin_exact :
    beginImmediate empty = .ok begunHonest := by
  rfl

@[simp] theorem honest_insert_exact :
    insert begunHonest recoveryFixture = .ok insertedHonest := by
  simp [insert, begunHonest, insertedHonest, boundedFixture, empty,
    recoveryFixture, maxRecordBytes]

@[simp] theorem honest_commit_exact :
    commit insertedHonest = .ok (.installed, committedHonest) := by
  rfl

@[simp] theorem honest_publish_exact :
    publish empty recoveryFixture = .ok (.installed, committedHonest) := by
  simp [publish]

/-- A process exit immediately after `BEGIN IMMEDIATE` cannot expose a row. -/
@[simp] theorem crash_after_begin_recovers_absent :
    read (crash begunHonest) = .error .missing := by
  rfl

/-- A process exit after `INSERT` but before `COMMIT` cannot expose a row. -/
@[simp] theorem crash_after_insert_recovers_absent :
    read (crash insertedHonest) = .error .missing := by
  rfl

/-- Losing the response after `COMMIT` and reopening returns the exact
Lean-authored recovery byte stream. -/
@[simp] theorem crash_after_commit_recovers_exact :
    read (crash committedHonest) = .ok recoveryFixture := by
  rfl

/-- Retrying the same BLOB starts a new transaction but commits no second row.
-/
@[simp] theorem exact_retry_is_idempotent :
    publish (crash committedHonest) recoveryFixture =
      .ok (.alreadyPresent, crash committedHonest) := by
  have withinBound : ¬ maxRecordBytes < recoveryFixture.length :=
    Nat.not_lt_of_ge recoveryFixture_bounded
  simp [publish, beginImmediate, insert, commit, crash, committedHonest,
    boundedFixture, withinBound]

/-- A conflicting transaction cannot replace the already committed row. -/
@[simp] theorem different_retry_conflicts :
    publish (crash committedHonest) StoreModel.conflictingFixture =
      .error .conflict := by
  simp [publish, beginImmediate, insert, crash, committedHonest,
    boundedFixture, StoreModel.conflictingFixture, recoveryFixture,
    maxRecordBytes]

@[simp] theorem conflict_preserves_exact_committed_read :
    read (crash committedHonest) = .ok recoveryFixture := by
  rfl

/-- Database corruption and a torn database image are both opaque native
failures.  Neither can manufacture payload bytes at the Lean boundary. -/
def corruptImage : State := { committedHonest with health := .corrupt }
def tornImage : State := { committedHonest with health := .torn }

@[simp] theorem corrupt_image_returns_no_bytes :
    read corruptImage = .error .corruptOrTorn := by
  rfl

@[simp] theorem torn_image_returns_no_bytes :
    read tornImage = .error .corruptOrTorn := by
  rfl

@[simp] theorem oversize_rejected_before_transaction :
    publish empty StoreModel.oversizedFixture = .error .tooLarge := by
  have oversized :
      maxRecordBytes < StoreModel.oversizedFixture.length := by
    rw [show StoreModel.oversizedFixture.length = maxRecordBytes + 1 by
      simp only [StoreModel.oversizedFixture, List.length_replicate]]
    exact Nat.lt_succ_self maxRecordBytes
  have insertOversized :
      insert begunHonest StoreModel.oversizedFixture = .error .tooLarge := by
    unfold insert
    simp only [oversized, ↓reduceDIte]
  simp [publish, insertOversized]

end TransactionModel

/-! ## Exact WAL, transaction, recovery, and client join -/

/-- The exact BLOB committed by the transaction contains the same encoded
frame as the authority-guarded abstract WAL transition. -/
theorem fixture_contains_exact_guarded_wal_frame :
    recoveryFixture =
      Minidregg.Assurance.HyperdocumentLinkFramedRecovery.wireHeader ++
        Minidregg.Assurance.HyperdocumentLinkFramedRecovery.walFrameCodec.encodeFrame
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent.erase := by
  rw [recoveryFixture_exact]
  rfl

/-- A cold SQLite reader remains opaque and fallible.  This closed boundary is
constructed only from the Lean transaction model's post-commit read theorem.
-/
def committedBoundary : RestartedBoundary TransactionModel.Failure where
  reader := fun _ =>
    TransactionModel.read
      (TransactionModel.crash TransactionModel.committedHonest)
  observed := TransactionModel.crash_after_commit_recovers_exact

@[simp] theorem committed_transaction_human_client_reopens
    (sessionId interactionId : Nat) :
    (submitLink (loseFirstStoreResponse committedBoundary)
      (humanCommand sessionId interactionId)).record? =
        some Endpoint.record :=
  file_lost_response_restart_reopens _ _

@[simp] theorem committed_transaction_agent_client_reopens
    (runId toolCallId : Nat) :
    (submitLink (loseFirstStoreResponse committedBoundary)
      (agentCommand runId toolCallId)).record? =
        some Endpoint.record :=
  file_lost_response_restart_reopens _ _

/-- The closed load-bearing carrier: one guarded WAL-ready intent, its exact
transactional BLOB, the pre/post-commit crash classification, and the exact
Lean recovery result are all the same publication. -/
structure TransactionalRecoveryJoin : Prop where
  guarded :
    Minidregg.Assurance.HyperdocumentLinkFramedRecovery.GuardedSyncReady
      Minidregg.Assurance.HyperdocumentLinkFramedRecovery.checkpoint
      Minidregg.Assurance.HyperdocumentLinkFramedRecovery.stagedDevice
  exactFrame : recoveryFixture =
    Minidregg.Assurance.HyperdocumentLinkFramedRecovery.wireHeader ++
      Minidregg.Assurance.HyperdocumentLinkFramedRecovery.walFrameCodec.encodeFrame
        Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent.erase
  published : TransactionModel.publish TransactionModel.empty recoveryFixture =
    .ok (.installed, TransactionModel.committedHonest)
  preCommitAbsent :
    TransactionModel.read
      (TransactionModel.crash TransactionModel.insertedHonest) =
        .error .missing
  postCommitExact :
    TransactionModel.read
      (TransactionModel.crash TransactionModel.committedHonest) =
        .ok recoveryFixture
  controllerAccepted :
    Minidregg.Compiler.FramedWalRecoveryController.run
        Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller
        Minidregg.Assurance.HyperdocumentLinkFramedRecovery.checkpoint
        (fun _ : Unit =>
          (Except.ok recoveryFixture :
            Except TransactionModel.Failure (List UInt8))) () =
      .ok Minidregg.Assurance.HyperdocumentLinkFramedRecovery.verifiedRecovery

def transactionalRecoveryWitness : TransactionalRecoveryJoin where
  guarded :=
    Minidregg.Assurance.HyperdocumentLinkFramedRecovery.guardedSyncReady
  exactFrame := fixture_contains_exact_guarded_wal_frame
  published := TransactionModel.honest_publish_exact
  preCommitAbsent := TransactionModel.crash_after_insert_recovers_absent
  postCommitExact := TransactionModel.crash_after_commit_recovers_exact
  controllerAccepted := exact_fixture_recovery_run

/-! ## Fail-closed corrupt/torn observations -/

@[simp] theorem corrupt_database_cannot_mint_client_receipt
    (command : LinkCommand) :
    submitLink
        (nativeFileErrorSubmit TransactionModel.Failure.corruptOrTorn)
        command =
      .native (.native TransactionModel.Failure.corruptOrTorn) :=
  native_file_error_cannot_mint_client_receipt _ _

@[simp] theorem torn_database_cannot_mint_client_receipt
    (command : LinkCommand) :
    submitLink
        (nativeFileErrorSubmit TransactionModel.Failure.corruptOrTorn)
        command =
      .native (.native TransactionModel.Failure.corruptOrTorn) :=
  native_file_error_cannot_mint_client_receipt _ _

/-! ## Explicit physical trust ceiling -/

/-- Premises still required to turn the isolated native conformance tests into
a physical durability theorem.  No inhabitant is constructed here.

`SQLiteAtomicCommit` includes rollback-journal correctness; `HostLocking`
includes cross-process lock semantics; `SyncOrdering` includes SQLite's
`synchronous=EXTRA` requests and directory-entry ordering.  `StableMedia` and
`PowerLossSurvival` remain distinct because successful calls alone prove
neither. -/
structure PhysicalSqliteDurabilityCeiling
    (RustFfiRefinesModel SQLiteAtomicCommit HostLocking SyncOrdering
      StableMedia PowerLossSurvival AdversarialDirectoryMutationExcluded
      SqliteLibraryIntegrity : Prop) : Prop where
  rustFfiRefinesModel : RustFfiRefinesModel
  sqliteAtomicCommit : SQLiteAtomicCommit
  hostLocking : HostLocking
  syncOrdering : SyncOrdering
  stableMedia : StableMedia
  powerLossSurvival : PowerLossSurvival
  adversarialDirectoryMutationExcluded : AdversarialDirectoryMutationExcluded
  sqliteLibraryIntegrity : SqliteLibraryIntegrity

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentLinkSqliteTransactionalStore.fixture_contains_exact_guarded_wal_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms fixture_contains_exact_guarded_wal_frame
/-- info: 'Minidregg.Assurance.HyperdocumentLinkSqliteTransactionalStore.transactionalRecoveryWitness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms transactionalRecoveryWitness
/-- info: 'Minidregg.Assurance.HyperdocumentLinkSqliteTransactionalStore.committed_transaction_human_client_reopens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms committed_transaction_human_client_reopens

end

end Minidregg.Assurance.HyperdocumentLinkSqliteTransactionalStore
