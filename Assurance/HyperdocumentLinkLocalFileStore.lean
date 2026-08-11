/-
# Assurance.HyperdocumentLinkLocalFileStore -- bounded file bytes, Lean acceptance

This is the first deployment-shaped local-storage boundary for the concrete
Hyperdocument forward link.  It deliberately separates three claims:

* `StoreModel` specifies a bounded, single-record stage/install/read protocol
  with crash-before-install, lost-response, idempotent-retry, conflict, and
  oversize teeth;
* the companion Rust program performs real fallible local filesystem calls but
  returns only bytes or an opaque error;
* this module gives semantic meaning to a successful restart read only after
  the existing Lean endpoint decodes the exact bytes and replays the guarded
  durable intent.

The checked-in fixture is a literal Lean value and is definitionally equal to
`HyperdocumentLinkFramedRecovery.recoveryBytes`.  A Lean emitter authors the
binary fixture used by the Rust lifecycle tests.

There is intentionally no theorem about Rust, POSIX `fsync`, `hard_link`,
directory sync, atomic visibility, stable media, power loss, or an adversarial
filesystem.  Executable tests are conformance evidence for the calls observed
on tested hosts, not a formal refinement of their implementations.
-/
import Assurance.HyperdocumentLinkEndpointController

namespace Minidregg.Assurance.HyperdocumentLinkLocalFileStore

open Minidregg.Assurance.HyperdocumentLinkEndpointController
open Minidregg.Compiler.FramedWalRecoveryController
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

noncomputable section

/-! ## Lean-authored physical fixture -/

/-- The complete controller/domain/codec header and one checksummed link frame.
This literal, rather than native code, authors the bytes installed by the
filesystem conformance test. -/
def recoveryFixture : List UInt8 :=
  [162, 74, 30, 216, 1, 72, 89, 80, 69, 82, 76, 78, 75, 110]

/-- The physical fixture is exactly the already accepted logical recovery
stream; there is no second wire format at the filesystem boundary. -/
theorem recoveryFixture_exact :
    recoveryFixture =
      Minidregg.Assurance.HyperdocumentLinkFramedRecovery.recoveryBytes := by
  rfl

def maxRecordBytes : Nat := 4096

@[simp] theorem recoveryFixture_bounded :
    recoveryFixture.length <= maxRecordBytes := by
  decide

/-! ## Bounded single-record store control model -/

namespace StoreModel

inductive Failure where
  | missing
  | tooLarge
  | conflict
  | io
  deriving DecidableEq, Repr

inductive StageStatus where
  | staged
  | alreadyPresent
  deriving DecidableEq, Repr

inductive PublishStatus where
  | installed
  | alreadyPresent
  deriving DecidableEq, Repr

/-- A record carries the admission bound.  Native storage never obtains a
semantic payload type: its only retained value is this byte list. -/
structure BoundedRecord where
  bytes : List UInt8
  bounded : bytes.length <= maxRecordBytes

structure State where
  published : Option BoundedRecord
  staged : Option BoundedRecord

def empty : State := ⟨none, none⟩

def read (state : State) : Except Failure (List UInt8) :=
  match state.published with
  | none => .error .missing
  | some record => .ok record.bytes

/-- Stage bytes without making them visible.  A same-byte live record is an
idempotent success; a different live/staged byte string is never overwritten. -/
def stage (state : State) (bytes : List UInt8) :
    Except Failure (StageStatus × State) :=
  if oversized : maxRecordBytes < bytes.length then
    .error .tooLarge
  else
    let record : BoundedRecord := ⟨bytes, Nat.le_of_not_gt oversized⟩
    match state.published with
    | some live =>
        if live.bytes = bytes then .ok (.alreadyPresent, state)
        else .error .conflict
    | none =>
        match state.staged with
        | none => .ok (.staged, { state with staged := some record })
        | some candidate =>
            if candidate.bytes = bytes then .ok (.staged, state)
            else .error .conflict

/-- Install the staged byte string without replacing a different published
record.  This is the control model of the native hard-link install, not a
theorem that a host filesystem realizes it. -/
def install (state : State) : Except Failure (PublishStatus × State) :=
  match state.staged with
  | none => .error .missing
  | some candidate =>
      match state.published with
      | none =>
          .ok (.installed,
            { published := some candidate, staged := none })
      | some live =>
          if live.bytes = candidate.bytes then
            .ok (.alreadyPresent,
              { published := state.published, staged := none })
          else
            .error .conflict

/-- One ordinary publish attempt stages and installs. -/
def publish (state : State) (bytes : List UInt8) :
    Except Failure (PublishStatus × State) := do
  let (stageStatus, stagedState) <- stage state bytes
  match stageStatus with
  | .alreadyPresent => .ok (.alreadyPresent, stagedState)
  | .staged => install stagedState

/-- Process death discards an uninstalled staging file but preserves the
published slot in the model. -/
def crash (state : State) : State :=
  { published := state.published, staged := none }

def stagedHonest : State :=
  match stage empty recoveryFixture with
  | .ok (.staged, next) => next
  | _ => empty

def publishedHonest : State :=
  match publish empty recoveryFixture with
  | .ok (.installed, next) => next
  | _ => empty

@[simp] theorem stage_honest_not_visible :
    read stagedHonest = .error .missing := by
  rfl

/-- A restart before the install point cannot expose volatile/staged bytes. -/
@[simp] theorem crash_before_install_not_visible :
    read (crash stagedHonest) = .error .missing := by
  rfl

/-- Once installed, losing the response and restarting leaves the exact byte
stream visible. -/
@[simp] theorem install_lost_response_restart_reads_exact :
    read (crash publishedHonest) = .ok recoveryFixture := by
  rfl

/-- Retrying the identical publication is byte-idempotent. -/
@[simp] theorem exact_retry_is_idempotent :
    publish (crash publishedHonest) recoveryFixture =
      .ok (.alreadyPresent, crash publishedHonest) := by
  rfl

def conflictingFixture : List UInt8 := recoveryFixture.dropLast ++ [0]

theorem conflictingFixture_ne : conflictingFixture != recoveryFixture := by
  decide

/-- A different retry cannot overwrite the already published bytes. -/
@[simp] theorem different_retry_conflicts :
    publish (crash publishedHonest) conflictingFixture =
      .error .conflict := by
  rfl

def oversizedFixture : List UInt8 :=
  List.replicate (maxRecordBytes + 1) 0

@[simp] theorem oversized_stage_rejected :
    stage empty oversizedFixture = .error .tooLarge := by
  have oversized : maxRecordBytes < oversizedFixture.length := by
    rw [show oversizedFixture.length = maxRecordBytes + 1 by
      simp only [oversizedFixture, List.length_replicate]]
    exact Nat.lt_succ_self maxRecordBytes
  simp only [stage, oversized, ↓reduceDIte]

end StoreModel

/-! ## Opaque file reader to Lean-owned endpoint acceptance -/

/-- This is the entire callable native storage boundary used by a client:
one request may fail opaquely or return a byte list. -/
abbrev OpaqueFileRead (Error : Type) := Unit → Except Error (List UInt8)

private theorem unit_reader_eq_ok {Error : Type}
    (reader : OpaqueFileRead Error) (bytes : List UInt8)
    (observed : reader () = .ok bytes) :
    reader = fun _ : Unit => .ok bytes := by
  funext request
  cases request
  exact observed

private theorem unit_reader_eq_error {Error : Type}
    (reader : OpaqueFileRead Error) (error : Error)
    (observed : reader () = .error error) :
    reader = fun _ : Unit => .error error := by
  funext request
  cases request
  exact observed

@[simp] theorem exact_fixture_recovery_run {Error : Type} :
    run Recovery.controller Recovery.checkpoint
        (fun _ : Unit => (Except.ok recoveryFixture :
          Except Error (List UInt8))) () =
      .ok Minidregg.Assurance.HyperdocumentLinkFramedRecovery.verifiedRecovery := by
  rw [recoveryFixture_exact]
  unfold run
  simp only
  split
  next reason failed =>
    rw [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller_decodes_exact_intent]
      at failed
    contradiction
  next intents decoded =>
    have intentsExact : intents =
        [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent] := by
      rw [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller_decodes_exact_intent]
        at decoded
      exact (Except.ok.inj decoded).symm
    subst intents
    split
    next reason failed =>
      rw [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller_replays_install]
        at failed
      contradiction
    next snapshot replayed =>
      have snapshotExact : snapshot = DataSnapshot.install Recovery.checkpoint
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent := by
        rw [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.controller_replays_install]
          at replayed
        exact (Except.ok.inj replayed).symm
      subst snapshot
      rfl

/-- Narrow read-result refinement: if a restarted local reader observably
returns the exact Lean-authored fixture, the existing Lean endpoint accepts
and returns only the canonical link response bytes.  No proposition about why
the filesystem returned those bytes is needed or inferred. -/
theorem endpoint_accepts_exact_restarted_read {Error : Type}
    (origin : Origin) (reader : OpaqueFileRead Error)
    (observed : reader () = .ok recoveryFixture) :
    runAt Recovery.checkpoint origin honestRequestBytes reader =
      .ok resultBytes := by
  have readerExact := unit_reader_eq_ok reader recoveryFixture observed
  rw [readerExact]
  simp only [runAt, honest_request_decodes]
  simp [runRequest, honestRequest, endpointVersion, exact_fixture_recovery_run,
    Minidregg.Assurance.HyperdocumentLinkFramedRecovery.recovered_link_post_bytes,
    resultBytes]

/-- Lost response plus process restart remains semantically idempotent: the
same observed bytes reopen the exact link and the already journaled intent
does not append a second event. -/
theorem installed_restart_retry_reopens_exact {Error : Type}
    (origin : Origin) (reader : OpaqueFileRead Error)
    (observed : reader () = .ok recoveryFixture) :
    runAt Recovery.checkpoint origin honestRequestBytes reader =
        .ok resultBytes ∧
      replayAll
          (DataSnapshot.install Recovery.checkpoint
            Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent)
          [Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent] =
        .ok (DataSnapshot.install Recovery.checkpoint
          Minidregg.Assurance.HyperdocumentLinkFramedRecovery.intent) ∧
      linkRecordCodec.decode resultBytes = some Reopen.record :=
  ⟨endpoint_accepts_exact_restarted_read origin reader observed,
    Minidregg.Assurance.HyperdocumentLinkFramedRecovery.idempotent_retry,
    result_decodes_exact_link⟩

def corruptChecksumFixture : List UInt8 :=
  recoveryFixture.dropLast ++ [0]

@[simp] theorem corruptChecksumFixture_rejected_by_Lean :
    Recovery.controller.decodeWire corruptChecksumFixture =
      .error .invalidFrame := by
  rfl

@[simp] theorem corrupt_fixture_recovery_run {Error : Type} :
    run Recovery.controller Recovery.checkpoint
        (fun _ : Unit => (Except.ok corruptChecksumFixture :
          Except Error (List UInt8))) () =
      .error (.wire .invalidFrame) := by
  unfold run
  simp only
  split
  next reason failed =>
    rw [corruptChecksumFixture_rejected_by_Lean] at failed
    have reasonExact := Except.error.inj failed
    subst reason
    rfl
  next intents decoded =>
    rw [corruptChecksumFixture_rejected_by_Lean] at decoded
    contradiction

/-- A local file may be corrupted and still be read successfully by the OS.
Those bytes do not cross the Lean acceptance boundary. -/
theorem corrupt_file_bytes_fail_closed {Error : Type}
    (origin : Origin) (reader : OpaqueFileRead Error)
    (observed : reader () = .ok corruptChecksumFixture) :
    runAt Recovery.checkpoint origin honestRequestBytes reader =
      .error .malformedStorage := by
  have readerExact := unit_reader_eq_ok reader corruptChecksumFixture observed
  rw [readerExact]
  simp only [runAt, honest_request_decodes]
  simp [runRequest, honestRequest, endpointVersion,
    corrupt_fixture_recovery_run]

/-- An I/O error is never converted into a semantic response. -/
theorem native_file_error_blocks {Error : Type}
    (origin : Origin) (reader : OpaqueFileRead Error) (error : Error)
    (observed : reader () = .error error) :
    runAt Recovery.checkpoint origin honestRequestBytes reader =
      .error (.native error) := by
  have readerExact := unit_reader_eq_error reader error observed
  rw [readerExact]
  simp only [runAt, honest_request_decodes]
  simp [runRequest, honestRequest, endpointVersion,
    Minidregg.Compiler.FramedWalRecoveryController.run]

/-! ## Explicit trust ceiling -/

/-- Evidence still required before the tested local-store lifecycle can be
advertised as a physical durability theorem.  This module constructs no such
value.  In particular, successful `sync_all` return and a passing restart test
do not prove any of these propositions. -/
structure PhysicalDurabilityCeiling
    (FileSyncRefined DirectorySyncRefined NoOverwriteInstallRefined
      StableMedia PowerLossSurvival AdversarialRaceSafety : Prop) : Prop where
  fileSyncRefined : FileSyncRefined
  directorySyncRefined : DirectorySyncRefined
  noOverwriteInstallRefined : NoOverwriteInstallRefined
  stableMedia : StableMedia
  powerLossSurvival : PowerLossSurvival
  adversarialRaceSafety : AdversarialRaceSafety

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentLinkLocalFileStore.endpoint_accepts_exact_restarted_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms endpoint_accepts_exact_restarted_read
/-- info: 'Minidregg.Assurance.HyperdocumentLinkLocalFileStore.installed_restart_retry_reopens_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms installed_restart_retry_reopens_exact
/-- info: 'Minidregg.Assurance.HyperdocumentLinkLocalFileStore.corrupt_file_bytes_fail_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms corrupt_file_bytes_fail_closed

end

end Minidregg.Assurance.HyperdocumentLinkLocalFileStore
