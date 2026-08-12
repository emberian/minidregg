/-
# Assurance.ReactiveDurableSettlement -- accepted effects become durable terminals

`ReactiveLifecycleHistory.Finalized` proves an accepted semantic effect, but
intentionally performs no durable installation.  `ReactiveTerminalCell` gives
four retry-safe terminal alternatives, but is independent of any particular
effect family.  This adapter joins those two exact carriers.

A successful finalization atomically installs:

* the accepted effect's canonical post bytes;
* the canonical terminal promise record; and
* the exact outbox message for that terminal record.

The finalization post root is the terminal evidence root, its pre-root is a
read guard, and settlement height is guarded by the canonical clock image.
Cancel, expire, and break use the same open cell, transaction id, and
nullifier; once any terminal intent is installed, every different alternative
is a journal payload conflict.  Exact retries replay.

The construction proves logical atomicity and exposes a physical simulation
ceiling.  It supplies no scheduler fairness, delivery acknowledgement,
filesystem persistence, replication, or eventual-progress claim.
-/
import Assurance.ReactiveLifecycleHistory
import Kernel.AdmissionPrologue
import Kernel.ReactiveTerminalCell

namespace Minidregg.Assurance.ReactiveDurableSettlement

open Minidregg.Assurance.AcceptedCellEffectHistory
open Minidregg.Assurance.ReactiveLifecycleHistory
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Kernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ReactiveTerminalCell
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe u v w x y z q r
  uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome
  uClauseEvidence uPhysical uStep

noncomputable section

section Lifecycle

variable
    {U : FirstOrderUniverse.{q, r}}
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {Condition Continuation BreakReason : Type}
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {entryFamily : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {C : Submodule F (BoundReceiptIx n → F)}

/-- Deployment identities for the one durable terminal cell.  The promise id
and deadline are equalities, not copied lookalike fields. -/
structure Binding
    (spec : PromiseSpec U family Nat Condition Continuation) where
  openCell : OpenCell
  promiseIdExact : openCell.promiseId = spec.promiseId
  deadlineExact : openCell.deadline = spec.deadline

namespace Binding

variable
    {rules : HistoryRules n F Nat Condition BreakReason}
    {spec : PromiseSpec U family Nat Condition Continuation}
    {portal : Portal} {authState : AuthState}

def finalizePlan
    (binding : Binding spec)
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec)
    (settledAt : Nat) (within : settledAt ≤ spec.deadline) :
    Plan M.rootBytes binding.openCell where
  settledAt := settledAt
  decision := .finalize (by simpa [binding.deadlineExact] using within)
  evidenceRoot := finalized.accepted.prepared.postRoot
  triggerRoot := finalized.accepted.prepared.preRoot

def expirePlan
    (binding : Binding spec)
    (expired : Expired (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec) :
    Plan M.rootBytes binding.openCell where
  settledAt := rules.observedHeight expired.entry.context
  decision := .expire (by
    simpa [binding.deadlineExact] using expired.afterDeadline)
  evidenceRoot := expired.entry.context.postStateRoot
  triggerRoot := expired.entry.context.postStateRoot

/-- A single Lean predicate classifies authenticated break reasons.  Its two
proof branches cannot both construct terminal alternatives for one reason. -/
structure BreakClassification where
  IsCancellation : BreakReason → Prop

def cancelPlan
    (binding : Binding spec) (classification : BreakClassification)
    (broken : Broken (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec)
    (_cancel : classification.IsCancellation broken.reason)
    (settledAt : Nat) (within : settledAt ≤ spec.deadline) :
    Plan M.rootBytes binding.openCell where
  settledAt := settledAt
  decision := .cancel (by simpa [binding.deadlineExact] using within)
  evidenceRoot := broken.entry.context.postStateRoot
  triggerRoot := broken.entry.context.postStateRoot

def breakPlan
    (binding : Binding spec) (classification : BreakClassification)
    (broken : Broken (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C) rules spec)
    (_notCancel : ¬ classification.IsCancellation broken.reason)
    (settledAt : Nat) (within : settledAt ≤ spec.deadline) :
    Plan M.rootBytes binding.openCell where
  settledAt := settledAt
  decision := .broken (by simpa [binding.deadlineExact] using within)
  evidenceRoot := broken.entry.context.postStateRoot
  triggerRoot := broken.entry.context.postStateRoot

end Binding

/-! ## Finalization installs the semantic post with its terminal and outbox -/

variable
    {rules : HistoryRules n F Nat Condition BreakReason}
    {spec : PromiseSpec U family Nat Condition Continuation}
    {portal : Portal} {authState : AuthState}

/-- The only additional deployment choice is the durable cell carrying the
already canonical semantic post.  Its four inequalities make it neither a
terminal/outbox write nor a read-only clock/trigger cell. -/
structure FinalizeSettlement
    (binding : Binding spec)
    (finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec) where
  settledAt : Nat
  withinDeadline : settledAt ≤ spec.deadline
  effectCell : CellId
  effectTerminalDistinct : effectCell ≠ binding.openCell.terminalCell
  effectOutboxDistinct : effectCell ≠ binding.openCell.outboxCell
  effectClockDistinct : effectCell ≠ binding.openCell.clockCell
  effectTriggerDistinct : effectCell ≠ binding.openCell.triggerCell

namespace FinalizeSettlement

variable
    {binding : Binding spec}
    {finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec}

def terminalPlan (settlement : FinalizeSettlement binding finalized) :
    Plan M.rootBytes binding.openCell :=
  binding.finalizePlan finalized settlement.settledAt settlement.withinDeadline

/-- The accepted semantic cell is written from its exact canonical pre-image to
the exact canonical post image produced by the validated patch. -/
def effectWrite (settlement : FinalizeSettlement binding finalized) : DataWrite where
  cellId := settlement.effectCell
  expectedPre := finalized.accepted.prepared.preRoot
  exactPost := finalized.accepted.prepared.postRoot
  canonicalPostBytes := finalized.accepted.prepared.post.bytes

/-- One data intent atomically carries the semantic post, terminal record, and
outbox.  The terminal event and replay nullifier are unchanged projections of
the kernel plan. -/
def intent (settlement : FinalizeSettlement binding finalized) :
    DataIntent M.rootBytes where
  transactionId := binding.openCell.transactionId
  writes := settlement.effectWrite :: settlement.terminalPlan.intent.writes
  readGuards := settlement.terminalPlan.intent.readGuards
  nullifiers := settlement.terminalPlan.intent.nullifiers
  exactCharge := binding.openCell.exactCharge
  event := settlement.terminalPlan.event
  postRootsBound := by
    intro write member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact finalized.accepted.prepared.post.root_encoding_coherent.symm
    · exact settlement.terminalPlan.intent.postRootsBound write member
  guardsReadOnly := by
    intro guard member
    simp at member
    rcases member with rfl | rfl
    · simp [effectWrite, Plan.clockGuard, Plan.intent_writes, Plan.terminalWrite,
        Plan.outboxWrite,
        binding.openCell.terminalClockDistinct.symm,
        binding.openCell.outboxClockDistinct.symm]
      exact settlement.effectClockDistinct.symm
    · simp [effectWrite, Plan.triggerGuard, Plan.intent_writes, Plan.terminalWrite,
        Plan.outboxWrite,
        binding.openCell.terminalTriggerDistinct.symm,
        binding.openCell.outboxTriggerDistinct.symm]
      exact settlement.effectTriggerDistinct.symm

@[simp] theorem intent_writes
    (settlement : FinalizeSettlement binding finalized) :
    settlement.intent.writes =
      [settlement.effectWrite, settlement.terminalPlan.terminalWrite,
        settlement.terminalPlan.outboxWrite] := rfl

@[simp] theorem effect_write_exact
    (settlement : FinalizeSettlement binding finalized) :
    settlement.effectWrite.expectedPre = finalized.accepted.prepared.preRoot ∧
      settlement.effectWrite.exactPost = finalized.accepted.prepared.postRoot ∧
      settlement.effectWrite.canonicalPostBytes =
        finalized.accepted.prepared.post.bytes :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem evidence_root_exact
    (settlement : FinalizeSettlement binding finalized) :
    settlement.terminalPlan.evidenceRoot =
      finalized.accepted.prepared.postRoot := by
  simp [terminalPlan, Binding.finalizePlan]

@[simp] theorem trigger_root_exact
    (settlement : FinalizeSettlement binding finalized) :
    settlement.terminalPlan.triggerRoot =
      finalized.accepted.prepared.preRoot := by
  simp [terminalPlan, Binding.finalizePlan]

theorem trigger_is_authenticated_observation
    (settlement : FinalizeSettlement binding finalized) :
    settlement.terminalPlan.triggerRoot =
      finalized.reaction.notification.entry.context.postStateRoot := by
  rw [trigger_root_exact]
  exact (finalizedObservedPreRootExact finalized).symm

theorem complete_ready
    (settlement : FinalizeSettlement binding finalized)
    (before : DataSnapshot M.rootBytes)
    (unrecorded : Snapshot.lookupRecorded binding.openCell.transactionId
      before.model.journal = none)
    (ready : settlement.intent.preflight before = .ok ()) :
    DurableDataIntent.execute .complete before settlement.intent =
      .accepted (DataSnapshot.install before settlement.intent) :=
  DurableDataIntent.execute_complete_ready before settlement.intent
    unrecorded ready

theorem semantic_terminal_outbox_atomic
    (settlement : FinalizeSettlement binding finalized)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    (DurableDataIntent.execute schedule before settlement.intent).storeAfter before =
        before ∨
      (DurableDataIntent.execute schedule before settlement.intent).storeAfter before =
        DataSnapshot.install before settlement.intent :=
  DurableDataIntent.execute_no_partial_data_commit schedule before settlement.intent

@[simp] theorem retry_after_install
    (settlement : FinalizeSettlement binding finalized)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before settlement.intent) settlement.intent =
      .replayed settlement.intent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install,
    Snapshot.install, Snapshot.lookupRecorded,
    Intent.sameCheck_self]

/-- Any cancel, expire, or break plan for the same binding loses after this
finalization.  The journal compares the full three-write payload with the
alternative's two-write payload before consulting now-stale roots. -/
theorem alternative_after_finalize_conflicts
    (settlement : FinalizeSettlement binding finalized)
    (alternative : Plan M.rootBytes binding.openCell)
    (_different : settlement.terminalPlan.kind ≠ alternative.kind)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before settlement.intent) alternative.intent =
      .rejected (.durable .transactionConflict) := by
  have writesNe : settlement.intent.writes ≠ alternative.intent.writes := by
    intro equal
    have lengths := congrArg List.length equal
    simp at lengths
  have checkFalse : settlement.intent.erase.sameCheck alternative.intent.erase = false := by
    apply Bool.eq_false_iff.mpr
    intro checkTrue
    have payload := (DataIntent.erase_sameCheck_eq_true_iff
      settlement.intent alternative.intent).mp checkTrue
    exact writesNe payload.1
  have recorded : Snapshot.lookupRecorded binding.openCell.transactionId
      (DataSnapshot.install before settlement.intent).model.journal =
        some settlement.intent.erase := by
    change Snapshot.lookupRecorded settlement.intent.transactionId
      (DataSnapshot.install before settlement.intent).model.journal =
        some settlement.intent.erase
    simpa only [DataSnapshot.install_model] using
      Snapshot.lookupRecorded_install before.model settlement.intent.erase
  unfold DurableDataIntent.execute
  have alternativeTransaction :
      alternative.intent.transactionId = binding.openCell.transactionId := rfl
  rw [alternativeTransaction, recorded]
  simp [checkFalse]

/-- The semantic post, terminal, and outbox are visible together after logical
installation, including exact canonical post bytes. -/
theorem installed_exact
    (settlement : FinalizeSettlement binding finalized)
    (before : DataSnapshot M.rootBytes) :
    (DataSnapshot.install before settlement.intent).canonicalBytes
        settlement.effectCell = finalized.accepted.prepared.post.bytes ∧
      (DataSnapshot.install before settlement.intent).canonicalBytes
        binding.openCell.terminalCell = settlement.terminalPlan.terminalBytes ∧
      (DataSnapshot.install before settlement.intent).canonicalBytes
        binding.openCell.outboxCell = settlement.terminalPlan.outboxBytes := by
  simp [DataSnapshot.install_canonicalBytes, DataSnapshot.lookupPostBytes,
    intent, effectWrite, Plan.terminalWrite, Plan.outboxWrite,
    settlement.effectTerminalDistinct, settlement.effectOutboxDistinct,
    binding.openCell.terminalOutboxDistinct]

/-! ## Fee-first admission of the exact combined settlement -/

/-- Bind a finalize settlement into the already verified two-stage admission
protocol.  The fee/replay prologue and terminal body retain distinct
transaction ids and nullifiers; the body cannot debit the admission fee lane. -/
structure FeeFirstBinding
    (settlement : FinalizeSettlement binding finalized) where
  admissionId : TransactionId
  principal : Digest
  height : Nat
  admissionNonce : StableNullifier
  prologue : DataIntent M.rootBytes
  grant : AdmissionPrologue.Grant
  prologueTransaction : prologue.transactionId = admissionId
  bodyTransaction : settlement.intent.transactionId ≠ admissionId
  exactAdmissionNonce : prologue.nullifiers = [admissionNonce]
  positiveFee : 0 < prologue.exactCharge .feeDebit
  bodyZeroAdmissionFee : settlement.intent.exactCharge .feeDebit = 0
  bodyDoesNotConsumeAdmissionNonce :
    admissionNonce ∉ settlement.intent.nullifiers
  principalExact : principal = grant.principal
  nonceDomainExact : admissionNonce.domain = grant.nonceDomain
  validFrom : grant.notBefore ≤ height
  validUntil : height ≤ grant.notAfter
  feeWithinGrant : prologue.exactCharge .feeDebit ≤ grant.maxFeeDebit

namespace FeeFirstBinding

def request
    {settlement : FinalizeSettlement binding finalized}
    (feeFirst : FeeFirstBinding settlement) :
    AdmissionPrologue.Request M.rootBytes where
  admissionId := feeFirst.admissionId
  principal := feeFirst.principal
  height := feeFirst.height
  nonce := feeFirst.admissionNonce
  prologue := feeFirst.prologue
  body := settlement.intent

def admitted
    {settlement : FinalizeSettlement binding finalized}
    (feeFirst : FeeFirstBinding settlement) :
    AdmissionPrologue.Request.Admitted M.rootBytes where
  grant := feeFirst.grant
  request := feeFirst.request
  wellFormed := {
    prologueTransaction := feeFirst.prologueTransaction
    distinctBodyTransaction := feeFirst.bodyTransaction
    exactAdmissionNonce := feeFirst.exactAdmissionNonce
    positiveFee := feeFirst.positiveFee
    bodyChargesNoAdmissionFee := feeFirst.bodyZeroAdmissionFee
    bodyDoesNotConsumeAdmissionNonce := feeFirst.bodyDoesNotConsumeAdmissionNonce }
  authorized := {
    principal := feeFirst.principalExact
    nonceDomain := feeFirst.nonceDomainExact
    validFrom := feeFirst.validFrom
    validUntil := feeFirst.validUntil
    feeWithinGrant := feeFirst.feeWithinGrant }

@[simp] theorem admitted_body_exact
    {settlement : FinalizeSettlement binding finalized}
    (feeFirst : FeeFirstBinding settlement) :
    feeFirst.admitted.request.body = settlement.intent := rfl

theorem admitted_body_has_zero_fee
    {settlement : FinalizeSettlement binding finalized}
    (feeFirst : FeeFirstBinding settlement) :
    feeFirst.admitted.request.body.exactCharge .feeDebit = 0 :=
  AdmissionPrologue.body_has_zero_admission_fee feeFirst.admitted

end FeeFirstBinding

/-! ## Explicit deployment ceiling -/

theorem physical_step_atomic
    (settlement : FinalizeSettlement binding finalized)
    {PhysicalState : Type uPhysical}
    {PhysicalStep : PhysicalState → DataIntent M.rootBytes → PhysicalState → Type uStep}
    {Represents : PhysicalState → DataSnapshot M.rootBytes → Prop}
    (refinement : DurableDataIntent.ImplementationRefinement
      M.rootBytes PhysicalState PhysicalStep Represents)
    {physicalBefore physicalAfter : PhysicalState}
    {modelBefore : DataSnapshot M.rootBytes}
    (represented : Represents physicalBefore modelBefore)
    (stepped : PhysicalStep physicalBefore settlement.intent physicalAfter) :
    ∃ modelAfter,
      Represents physicalAfter modelAfter ∧
      (modelAfter = modelBefore ∨
        modelAfter = DataSnapshot.install modelBefore settlement.intent) ∧
      (∀ cellId, M.rootBytes (modelAfter.canonicalBytes cellId) =
        modelAfter.model.roots cellId) :=
  DurableDataIntent.physical_step_no_partial_data_commit
    refinement represented stepped

/-- Eventual scheduling, persistence, and outbox delivery are separate from
atomic safety.  A deployment claiming liveness must inhabit all three
relations for every enabled finalization; no instance is manufactured here. -/
structure LivenessRefinement
    (Enabled : FinalizeSettlement binding finalized → Prop)
    (EventuallyPersisted : FinalizeSettlement binding finalized → Prop)
    (EventuallyDelivered : FinalizeSettlement binding finalized → Prop) : Prop where
  persists : ∀ settlement, Enabled settlement → EventuallyPersisted settlement
  delivers : ∀ settlement, Enabled settlement → EventuallyDelivered settlement

end FinalizeSettlement

end Lifecycle

/-! Assurance-facing theorem audit. -/

/-- info: 'Minidregg.Assurance.ReactiveDurableSettlement.FinalizeSettlement.trigger_is_authenticated_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FinalizeSettlement.trigger_is_authenticated_observation
/-- info: 'Minidregg.Assurance.ReactiveDurableSettlement.FinalizeSettlement.semantic_terminal_outbox_atomic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FinalizeSettlement.semantic_terminal_outbox_atomic
/-- info: 'Minidregg.Assurance.ReactiveDurableSettlement.FinalizeSettlement.retry_after_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FinalizeSettlement.retry_after_install
/-- info: 'Minidregg.Assurance.ReactiveDurableSettlement.FinalizeSettlement.alternative_after_finalize_conflicts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FinalizeSettlement.alternative_after_finalize_conflicts
/-- info: 'Minidregg.Assurance.ReactiveDurableSettlement.FinalizeSettlement.installed_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FinalizeSettlement.installed_exact
/-- info: 'Minidregg.Assurance.ReactiveDurableSettlement.FinalizeSettlement.FeeFirstBinding.admitted_body_has_zero_fee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FinalizeSettlement.FeeFirstBinding.admitted_body_has_zero_fee
/-- info: 'Minidregg.Assurance.ReactiveDurableSettlement.FinalizeSettlement.physical_step_atomic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FinalizeSettlement.physical_step_atomic

end

end Minidregg.Assurance.ReactiveDurableSettlement
