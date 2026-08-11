/-
# Kernel.AdmissionPrologue -- fee-first replay-safe admission

Some operations must charge admission and advance replay protection even when
their semantic body is rejected.  Treating that behavior as one ordinary
all-or-nothing turn loses the fee and nonce on body failure; charging in a
native pre-handler instead creates a second, unaudited state machine.

This module gives the two stages one Lean-owned protocol:

* an exact grant authorizes the principal, nonce domain, time window, and fee;
* a payload-bearing durable prologue consumes exactly that nonce and charges a
  positive fee before the body is examined;
* the body may install its exact durable data or reject, while a rejection
  exposes precisely the post-prologue snapshot;
* one dependent receipt is indexed by both exact stage payloads;
* the outer admission journal makes retries identity operations, while the
  inner stage journals recover a prologue or body installed before the outer
  receipt was recorded.

The model is deliberately logical.  It reuses `DurableDataIntent` for exact
bytes, read guards, nullifiers, charges, and replay identity, but makes no
claim that a filesystem, database, or remote service physically persisted
anything.  Such a claim still requires that module's implementation-refinement
premise.
-/
import Kernel.DurableDataIntent

namespace Minidregg.Kernel.AdmissionPrologue

open Minidregg.Theory
open Minidregg.Theory.ResourceCost
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

/-! ## Exact authorization and two-stage request -/

/-- A finite admission capability.  The grant does not authorize the body by
itself; it authorizes only the fee/replay prologue for an already constructed
body intent. -/
structure Grant where
  principal : TypedAuthorization.Digest
  nonceDomain : TypedAuthorization.Digest
  notBefore : Nat
  notAfter : Nat
  maxFeeDebit : Nat
  deriving DecidableEq, Repr

/-- The two exact durable stages.  The admission identifier is also the
prologue transaction identifier; the body has its own identifier so the two
inner journal records cannot alias. -/
structure Request (rootBytes : List UInt8 -> TypedAuthorization.Digest) where
  admissionId : TransactionId
  principal : TypedAuthorization.Digest
  height : Nat
  nonce : StableNullifier
  prologue : DataIntent rootBytes
  body : DataIntent rootBytes

namespace Request

variable {rootBytes : List UInt8 -> TypedAuthorization.Digest}

/-- Structural conditions which prevent the body from silently reinterpreting
the admission fee or nonce.  Other prologue lanes may honestly account for
storage and proof work; only the `feeDebit` lane is reserved here. -/
structure WellFormed (request : Request rootBytes) : Prop where
  prologueTransaction : request.prologue.transactionId = request.admissionId
  distinctBodyTransaction : request.body.transactionId ≠ request.admissionId
  exactAdmissionNonce : request.prologue.nullifiers = [request.nonce]
  positiveFee : 0 < request.prologue.exactCharge .feeDebit
  bodyChargesNoAdmissionFee : request.body.exactCharge .feeDebit = 0
  bodyDoesNotConsumeAdmissionNonce : request.nonce ∉ request.body.nullifiers

/-- Authorization is indexed by the exact request and exact grant. -/
structure Authorized (grant : Grant) (request : Request rootBytes) : Prop where
  principal : request.principal = grant.principal
  nonceDomain : request.nonce.domain = grant.nonceDomain
  validFrom : grant.notBefore <= request.height
  validUntil : request.height <= grant.notAfter
  feeWithinGrant : request.prologue.exactCharge .feeDebit <= grant.maxFeeDebit

/-- The value admitted by `execute`: construction must provide both the exact
grant relation and the structural separation of the two stages. -/
structure Admitted (rootBytes : List UInt8 -> TypedAuthorization.Digest) where
  grant : Grant
  request : Request rootBytes
  wellFormed : request.WellFormed
  authorized : request.Authorized grant

/-- Exact replay equality.  `DataIntent.erase` retains canonical post bytes,
read guards, all charge lanes, nullifiers, and the semantic event inside its
replay envelope. -/
def sameCheck (left right : Request rootBytes) : Bool :=
  decide (left.principal = right.principal) &&
    decide (left.height = right.height) &&
    decide (left.nonce = right.nonce) &&
    left.prologue.erase.sameCheck right.prologue.erase &&
    left.body.erase.sameCheck right.body.erase

def SamePayload (left right : Request rootBytes) : Prop :=
  left.principal = right.principal /\
    left.height = right.height /\
    left.nonce = right.nonce /\
    left.prologue.erase.SamePayload right.prologue.erase /\
    left.body.erase.SamePayload right.body.erase

@[simp] theorem sameCheck_eq_true_iff (left right : Request rootBytes) :
    left.sameCheck right = true <-> left.SamePayload right := by
  simp only [sameCheck, Bool.and_eq_true, decide_eq_true_eq,
    DurableCommitProtocol.Intent.sameCheck_eq_true_iff, SamePayload]
  tauto

@[simp] theorem sameCheck_self (request : Request rootBytes) :
    request.sameCheck request = true := by
  rw [sameCheck_eq_true_iff]
  exact ⟨rfl, rfl, rfl,
    ⟨rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl⟩⟩

end Request

/-! ## One receipt indexed by both stages -/

/-- The body result is the only open branch after the prologue settles. -/
inductive BodyStatus
  | committed
  | rejected (reason : DurableDataIntent.RejectReason)
  deriving DecidableEq, Repr

/-- A receipt is indexed by the exact request.  Consequently its projections
below are definitionally the prologue and body payloads that were admitted;
an executor cannot substitute alternate roots, bytes, guards, charges, or
events while retaining this receipt type. -/
structure Receipt {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (request : Request rootBytes) where
  bodyStatus : BodyStatus

namespace Receipt

variable {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    {request : Request rootBytes}

def prologuePayload (_receipt : Receipt request) := request.prologue.erase

def bodyPayload (_receipt : Receipt request) := request.body.erase

@[simp] theorem prologuePayload_exact (receipt : Receipt request) :
    receipt.prologuePayload = request.prologue.erase := rfl

@[simp] theorem bodyPayload_exact (receipt : Receipt request) :
    receipt.bodyPayload = request.body.erase := rfl

end Receipt

/-! ## Logical admission snapshot and outer replay journal -/

/-- One recorded terminal admission.  The dependent receipt remains attached
to the exact request it describes. -/
structure Recorded (rootBytes : List UInt8 -> TypedAuthorization.Digest) where
  request : Request rootBytes
  receipt : Receipt request

structure AdmissionSnapshot (rootBytes : List UInt8 -> TypedAuthorization.Digest) where
  data : DataSnapshot rootBytes
  records : List (Recorded rootBytes)

namespace AdmissionSnapshot

variable {rootBytes : List UInt8 -> TypedAuthorization.Digest}

private def lookupList (admissionId : TransactionId) :
    List (Recorded rootBytes) -> Option (Recorded rootBytes)
  | [] => none
  | recorded :: rest =>
      if recorded.request.admissionId = admissionId then some recorded
      else lookupList admissionId rest

def lookup (snapshot : AdmissionSnapshot rootBytes) (admissionId : TransactionId) :
    Option (Recorded rootBytes) :=
  lookupList admissionId snapshot.records

def record (before : AdmissionSnapshot rootBytes)
    (request : Request rootBytes) (receipt : Receipt request)
    (data : DataSnapshot rootBytes) : AdmissionSnapshot rootBytes where
  data := data
  records := { request := request, receipt := receipt } :: before.records

@[simp] theorem lookup_record (before : AdmissionSnapshot rootBytes)
    (request : Request rootBytes) (receipt : Receipt request)
    (data : DataSnapshot rootBytes) :
    (record before request receipt data).lookup request.admissionId =
      some { request := request, receipt := receipt } := by
  simp [record, lookup, lookupList]

end AdmissionSnapshot

/-! ## Complete logical stage execution -/

/-- The crash-free logical projection of `DurableDataIntent.execute`.  This
does not assert crash freedom of an implementation: it describes a completed
model step using the same journal-first replay check, preflight, and exact data
installation. -/
inductive StageOutcome (rootBytes : List UInt8 -> TypedAuthorization.Digest)
  | accepted (next : DataSnapshot rootBytes)
  | replayed (recorded :
      DurableCommitProtocol.Intent TransactionId CellId StableNullifier ReplayEnvelope)
  | rejected (reason : DurableDataIntent.RejectReason)

def executeStage {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    StageOutcome rootBytes :=
  match DurableCommitProtocol.Snapshot.lookupRecorded intent.transactionId
      before.model.journal with
  | some recorded =>
      if recorded.sameCheck intent.erase then .replayed recorded
      else .rejected (.durable .transactionConflict)
  | none =>
      match intent.preflight before with
      | .error reason => .rejected reason
      | .ok () => .accepted (DataSnapshot.install before intent)

theorem executeStage_ready
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (unrecorded : DurableCommitProtocol.Snapshot.lookupRecorded
      intent.transactionId before.model.journal = none)
    (ready : intent.preflight before = .ok ()) :
    executeStage before intent = .accepted (DataSnapshot.install before intent) := by
  simp [executeStage, unrecorded, ready]

theorem executeStage_rejected
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes)
    (unrecorded : DurableCommitProtocol.Snapshot.lookupRecorded
      intent.transactionId before.model.journal = none)
    (reason : DurableDataIntent.RejectReason)
    (rejected : intent.preflight before = .error reason) :
    executeStage before intent = .rejected reason := by
  simp [executeStage, unrecorded, rejected]

@[simp] theorem executeStage_after_install
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : DataSnapshot rootBytes) (intent : DataIntent rootBytes) :
    executeStage (DataSnapshot.install before intent) intent =
      .replayed intent.erase := by
  simp [executeStage, DataSnapshot.install, DurableCommitProtocol.Snapshot.install,
    DurableCommitProtocol.Snapshot.lookupRecorded]

/-! ## Total two-stage settlement -/

inductive RejectReason
  | admissionConflict
  | prologue (reason : DurableDataIntent.RejectReason)
  deriving DecidableEq, Repr

inductive Outcome (rootBytes : List UInt8 -> TypedAuthorization.Digest)
  | settled (next : AdmissionSnapshot rootBytes) (recorded : Recorded rootBytes)
  | replayed (recorded : Recorded rootBytes)
  | rejected (reason : RejectReason)

namespace Outcome

variable {rootBytes : List UInt8 -> TypedAuthorization.Digest}

def storeAfter (before : AdmissionSnapshot rootBytes) :
    Outcome rootBytes -> AdmissionSnapshot rootBytes
  | .settled next _ => next
  | .replayed _ => before
  | .rejected _ => before

end Outcome

private def settleBody {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : AdmissionSnapshot rootBytes) (request : Request rootBytes)
    (afterPrologue : DataSnapshot rootBytes) : Outcome rootBytes :=
  match executeStage afterPrologue request.body with
  | .accepted afterBody =>
      let receipt : Receipt request := { bodyStatus := .committed }
      let recorded : Recorded rootBytes := { request := request, receipt := receipt }
      .settled (before.record request receipt afterBody) recorded
  | .replayed _ =>
      let receipt : Receipt request := { bodyStatus := .committed }
      let recorded : Recorded rootBytes := { request := request, receipt := receipt }
      .settled (before.record request receipt afterPrologue) recorded
  | .rejected reason =>
      let receipt : Receipt request := { bodyStatus := .rejected reason }
      let recorded : Recorded rootBytes := { request := request, receipt := receipt }
      .settled (before.record request receipt afterPrologue) recorded

/-- Journal-first, fee-first admission.  A replayed prologue or body is a
recovery state, not a second charge: the existing data snapshot already
contains that stage's complete installation. -/
def execute {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : AdmissionSnapshot rootBytes) (admitted : Request.Admitted rootBytes) :
    Outcome rootBytes :=
  match before.lookup admitted.request.admissionId with
  | some recorded =>
      if recorded.request.sameCheck admitted.request then .replayed recorded
      else .rejected .admissionConflict
  | none =>
      match executeStage before.data admitted.request.prologue with
      | .accepted afterPrologue =>
          settleBody before admitted.request afterPrologue
      | .replayed _ =>
          settleBody before admitted.request before.data
      | .rejected reason => .rejected (.prologue reason)

/-! ## Safety teeth -/

/-- Once a body rejection is known, the only exposed data state is the exact
post-prologue state.  In particular, no candidate body root or post bytes are
installed. -/
theorem body_rejection_exposes_only_prologue
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : AdmissionSnapshot rootBytes) (admitted : Request.Admitted rootBytes)
    (fresh : before.lookup admitted.request.admissionId = none)
    (prologue : executeStage before.data admitted.request.prologue =
      .accepted (DataSnapshot.install before.data admitted.request.prologue))
    (reason : DurableDataIntent.RejectReason)
    (body : executeStage (DataSnapshot.install before.data admitted.request.prologue)
      admitted.request.body = .rejected reason) :
    (execute before admitted).storeAfter before =
      before.record admitted.request
        { bodyStatus := .rejected reason }
        (DataSnapshot.install before.data admitted.request.prologue) := by
  simp [execute, fresh, prologue, settleBody, body, Outcome.storeAfter]

theorem body_rejection_installs_no_body_root
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : AdmissionSnapshot rootBytes) (admitted : Request.Admitted rootBytes)
    (fresh : before.lookup admitted.request.admissionId = none)
    (prologue : executeStage before.data admitted.request.prologue =
      .accepted (DataSnapshot.install before.data admitted.request.prologue))
    (reason : DurableDataIntent.RejectReason)
    (body : executeStage (DataSnapshot.install before.data admitted.request.prologue)
      admitted.request.body = .rejected reason)
    (cellId : CellId) :
    ((execute before admitted).storeAfter before).data.model.roots cellId =
      (DataSnapshot.install before.data admitted.request.prologue).model.roots cellId /\
    ((execute before admitted).storeAfter before).data.canonicalBytes cellId =
      (DataSnapshot.install before.data admitted.request.prologue).canonicalBytes cellId := by
  rw [body_rejection_exposes_only_prologue before admitted fresh prologue reason body]
  exact ⟨rfl, rfl⟩

/-- Body failure retains both replay consumption and the exact prologue debit.
The theorem uses only logical installation plus the caller's successful
funding premise; it makes no physical persistence claim. -/
theorem fee_and_nonce_persist_on_body_failure
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : AdmissionSnapshot rootBytes) (admitted : Request.Admitted rootBytes)
    (fresh : before.lookup admitted.request.admissionId = none)
    (prologue : executeStage before.data admitted.request.prologue =
      .accepted (DataSnapshot.install before.data admitted.request.prologue))
    (reason : DurableDataIntent.RejectReason)
    (body : executeStage (DataSnapshot.install before.data admitted.request.prologue)
      admitted.request.body = .rejected reason)
    (funded : admitted.request.prologue.exactCharge <= before.data.model.available) :
    ((execute before admitted).storeAfter before).data.model.consumed
        admitted.request.nonce = true /\
      admitted.request.prologue.exactCharge +
        ((execute before admitted).storeAfter before).data.model.available =
          before.data.model.available := by
  rw [body_rejection_exposes_only_prologue before admitted fresh prologue reason body]
  constructor
  · change (DataSnapshot.install before.data admitted.request.prologue).model.consumed
      admitted.request.nonce = true
    rw [DataSnapshot.install_model]
    apply DurableCommitProtocol.Snapshot.install_consumes
    have present : admitted.request.nonce ∈ admitted.request.prologue.nullifiers := by
      rw [admitted.wellFormed.exactAdmissionNonce]
      simp
    simpa [DataIntent.erase] using present
  · change admitted.request.prologue.exactCharge +
      (DataSnapshot.install before.data admitted.request.prologue).model.available =
        before.data.model.available
    rw [DataSnapshot.install_model]
    exact DurableCommitProtocol.Snapshot.install_exact_debit
      before.data.model admitted.request.prologue.erase funded

/-- Recording a terminal receipt makes every exact retry an identity operation.
This is the outer half of no-double-charge; the inner stage journals provide
the same property across interruptions before this record exists. -/
@[simp] theorem retry_after_record
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : AdmissionSnapshot rootBytes) (admitted : Request.Admitted rootBytes)
    (receipt : Receipt admitted.request) (data : DataSnapshot rootBytes) :
    execute (before.record admitted.request receipt data) admitted =
      .replayed { request := admitted.request, receipt := receipt } := by
  simp [execute, AdmissionSnapshot.lookup_record, Request.sameCheck_self]

theorem retry_does_not_double_charge
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : AdmissionSnapshot rootBytes) (admitted : Request.Admitted rootBytes)
    (receipt : Receipt admitted.request) (data : DataSnapshot rootBytes) :
    (execute (before.record admitted.request receipt data) admitted).storeAfter
        (before.record admitted.request receipt data) =
      before.record admitted.request receipt data := by
  rw [retry_after_record]
  rfl

/-- Recovery between stages is also fee-idempotent.  When the durable
prologue is already installed but the outer receipt is absent, its inner
journal entry is replayed and the body continues against the existing
post-prologue snapshot.  A body rejection therefore leaves the already
debited availability unchanged rather than charging the prologue again. -/
theorem resume_after_prologue_install_does_not_recharge
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : AdmissionSnapshot rootBytes) (admitted : Request.Admitted rootBytes)
    (fresh : before.lookup admitted.request.admissionId = none)
    (reason : DurableDataIntent.RejectReason)
    (body : executeStage
      (DataSnapshot.install before.data admitted.request.prologue)
      admitted.request.body = .rejected reason) :
    let afterPrologue := DataSnapshot.install before.data admitted.request.prologue
    let resumed : AdmissionSnapshot rootBytes :=
      { data := afterPrologue, records := before.records }
    ((execute resumed admitted).storeAfter resumed).data.model.available =
      afterPrologue.model.available := by
  have freshList := fresh
  change AdmissionSnapshot.lookupList admitted.request.admissionId before.records = none
    at freshList
  dsimp only
  simp [execute, AdmissionSnapshot.lookup, freshList, executeStage_after_install,
    settleBody, body, Outcome.storeAfter, AdmissionSnapshot.record,
    DataSnapshot.install_model]

/-- A body may account for its own resource work, but it can never debit the
admission fee lane a second time. -/
theorem body_has_zero_admission_fee
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (admitted : Request.Admitted rootBytes) :
    admitted.request.body.exactCharge .feeDebit = 0 :=
  admitted.wellFormed.bodyChargesNoAdmissionFee

/-! ## Explicit stale/replayed nonce rejection -/

/-- If all earlier prologue checks pass but its exact nonce is already
consumed, ordinary durable preflight rejects at `alreadyConsumed`. -/
theorem prologue_preflight_rejects_consumed_nonce
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : DataSnapshot rootBytes) (request : Request rootBytes)
    (wellFormed : request.WellFormed)
    (guards : request.prologue.readGuardsMatchCheck before = true)
    (writes : request.prologue.writes ≠ [])
    (distinctWrites : (request.prologue.writes.map DataWrite.cellId).Nodup)
    (roots : request.prologue.erase.rootsMatchCheck before.model = true)
    (consumed : before.model.consumed request.nonce = true) :
    request.prologue.preflight before =
      .error (.durable .alreadyConsumed) := by
  have nullifiersNodup : request.prologue.nullifiers.Nodup := by
    rw [wellFormed.exactAdmissionNonce]
    simp
  have freshFailed : request.prologue.erase.nullifiersFreshCheck before.model = false := by
    simp [DurableCommitProtocol.Intent.nullifiersFreshCheck, DataIntent.erase,
      wellFormed.exactAdmissionNonce, consumed]
  simp [DurableDataIntent.DataIntent.preflight, guards,
    DurableCommitProtocol.Intent.preflight, roots, freshFailed]
  simp [Function.comp_def, writes, distinctWrites, nullifiersNodup]

theorem execute_rejects_replayed_nonce
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : AdmissionSnapshot rootBytes) (admitted : Request.Admitted rootBytes)
    (freshAdmission : before.lookup admitted.request.admissionId = none)
    (stageUnrecorded : DurableCommitProtocol.Snapshot.lookupRecorded
      admitted.request.prologue.transactionId before.data.model.journal = none)
    (guards : admitted.request.prologue.readGuardsMatchCheck before.data = true)
    (writes : admitted.request.prologue.writes ≠ [])
    (distinctWrites :
      (admitted.request.prologue.writes.map DataWrite.cellId).Nodup)
    (roots : admitted.request.prologue.erase.rootsMatchCheck before.data.model = true)
    (consumed : before.data.model.consumed admitted.request.nonce = true) :
    execute before admitted =
      .rejected (.prologue (.durable .alreadyConsumed)) := by
  have rejected := prologue_preflight_rejects_consumed_nonce before.data
    admitted.request admitted.wellFormed guards writes distinctWrites roots consumed
  simp [execute, freshAdmission, executeStage, stageUnrecorded, rejected]

/-- A stale prologue write is rejected before nonce consumption or fee debit.
The exact ordered failure is inherited from durable preflight. -/
theorem execute_rejects_stale_prologue
    {rootBytes : List UInt8 -> TypedAuthorization.Digest}
    (before : AdmissionSnapshot rootBytes) (admitted : Request.Admitted rootBytes)
    (freshAdmission : before.lookup admitted.request.admissionId = none)
    (stageUnrecorded : DurableCommitProtocol.Snapshot.lookupRecorded
      admitted.request.prologue.transactionId before.data.model.journal = none)
    (stale : admitted.request.prologue.preflight before.data =
      .error (.durable .stalePreRoot)) :
    execute before admitted =
      .rejected (.prologue (.durable .stalePreRoot)) := by
  simp [execute, freshAdmission, executeStage, stageUnrecorded, stale]

/-! ## Executable non-vacuity witness -/

namespace Witness

open Minidregg.Kernel.DurableDataIntent.Witness

def bodyNullifier : StableNullifier where
  codecVersion := 1
  domain := ⟨73⟩
  nullifierId := ⟨74⟩
  canonicalBytes := [98, 111, 100, 121]

def bodyEvent : StableEvent where
  codecVersion := 1
  domain := ⟨83⟩
  eventId := ⟨84⟩
  canonicalBytes := [98, 111, 100, 121]

/-- The body proposes valid root-bound bytes, but intentionally names a stale
pre-root.  Rejection is therefore a real durable preflight tooth rather than
an empty or malformed intent. -/
def staleBodyWrite : DataWrite where
  cellId := writeCell
  expectedPre := ⟨999⟩
  exactPost := ⟨2⟩
  canonicalPostBytes := [10, 11]

def bodyIntent : DataIntent lengthRoot where
  transactionId := ⟨92⟩
  writes := [staleBodyWrite]
  readGuards := []
  nullifiers := [bodyNullifier]
  exactCharge := 0
  event := bodyEvent
  postRootsBound := by simp [staleBodyWrite, lengthRoot]
  guardsReadOnly := by simp

def request : Request lengthRoot where
  admissionId := intent.transactionId
  principal := ⟨61⟩
  height := 5
  nonce := nullifier
  prologue := intent
  body := bodyIntent

def grant : Grant where
  principal := request.principal
  nonceDomain := request.nonce.domain
  notBefore := 0
  notAfter := 10
  maxFeeDebit := 1

def admitted : Request.Admitted lengthRoot where
  grant := grant
  request := request
  wellFormed := by
    constructor
    · rfl
    · decide
    · rfl
    · decide
    · rfl
    · decide
  authorized := by
    constructor <;> decide

def beforeAdmission : AdmissionSnapshot lengthRoot where
  data := before
  records := []

@[simp] theorem prologue_ready :
    executeStage beforeAdmission.data request.prologue =
      .accepted (DataSnapshot.install beforeAdmission.data request.prologue) := by
  apply executeStage_ready
  · rfl
  · exact Minidregg.Kernel.DurableDataIntent.Witness.ready

@[simp] theorem body_preflight_rejects :
    request.body.preflight
      (DataSnapshot.install beforeAdmission.data request.prologue) =
        .error (.durable .stalePreRoot) := by
  decide

@[simp] theorem body_stage_unrecorded :
    DurableCommitProtocol.Snapshot.lookupRecorded request.body.transactionId
      (DataSnapshot.install beforeAdmission.data request.prologue).model.journal = none := by
  simp [beforeAdmission, request, bodyIntent, DataSnapshot.install,
    DurableCommitProtocol.Snapshot.install,
    DurableCommitProtocol.Snapshot.lookupRecorded,
    Minidregg.Kernel.DurableDataIntent.Witness.intent,
    Minidregg.Kernel.DurableDataIntent.Witness.before,
    Minidregg.Kernel.DurableDataIntent.Witness.beforeModel]

@[simp] theorem body_really_rejects :
    executeStage (DataSnapshot.install beforeAdmission.data request.prologue)
      request.body = .rejected (.durable .stalePreRoot) := by
  apply executeStage_rejected
  · exact body_stage_unrecorded
  · exact body_preflight_rejects

/-- Positive end-to-end witness: the exact fee prologue settles, the stale
body rejects, and the terminal receipt is attached to the exact two-stage
request. -/
theorem settles_body_rejection :
    exists next recorded,
      execute beforeAdmission admitted = .settled next recorded /\
        recorded.receipt.bodyStatus =
          .rejected (.durable .stalePreRoot) := by
  refine ⟨beforeAdmission.record request
      { bodyStatus := .rejected (.durable .stalePreRoot) }
      (DataSnapshot.install beforeAdmission.data request.prologue),
    { request := request,
      receipt := { bodyStatus := .rejected (.durable .stalePreRoot) } }, ?_, rfl⟩
  have fresh : beforeAdmission.lookup admitted.request.admissionId = none := rfl
  have prologue := prologue_ready
  change executeStage beforeAdmission.data admitted.request.prologue =
    .accepted (DataSnapshot.install beforeAdmission.data admitted.request.prologue)
    at prologue
  have body := body_really_rejects
  change executeStage
    (DataSnapshot.install beforeAdmission.data admitted.request.prologue)
    admitted.request.body = .rejected (.durable .stalePreRoot) at body
  simp only [execute, fresh, prologue, settleBody, body]
  rfl

/-- The concrete witness exhibits the principal semantic tooth: a rejected
body still leaves the fee debit and admission nonce installed. -/
theorem concrete_fee_and_nonce_persist :
    ((execute beforeAdmission admitted).storeAfter beforeAdmission).data.model.consumed
        request.nonce = true /\
      request.prologue.exactCharge +
        ((execute beforeAdmission admitted).storeAfter beforeAdmission).data.model.available =
          beforeAdmission.data.model.available := by
  apply fee_and_nonce_persist_on_body_failure beforeAdmission admitted
    (by rfl) prologue_ready (.durable .stalePreRoot) body_really_rejects
  intro lane
  cases lane <;> decide

end Witness

end Minidregg.Kernel.AdmissionPrologue

/-! Kernel-facing theorem audit. -/

/-- info: 'Minidregg.Kernel.AdmissionPrologue.fee_and_nonce_persist_on_body_failure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Kernel.AdmissionPrologue.fee_and_nonce_persist_on_body_failure
/-- info: 'Minidregg.Kernel.AdmissionPrologue.Witness.concrete_fee_and_nonce_persist' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Kernel.AdmissionPrologue.Witness.concrete_fee_and_nonce_persist
