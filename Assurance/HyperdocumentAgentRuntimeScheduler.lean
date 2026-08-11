/-
# Assurance.HyperdocumentAgentRuntimeScheduler -- one leased reactive link job

This module is a deployment-shaped logical consumer of the proof-native
Hyperdocument surfaces.  It specializes `HyperdocumentAgentOperation` to the
already accepted forward-link publication, reuses the closed reactive/history
substrate from `HyperdocumentReactiveCarrierWitness`, and settles the exact
accepted link through `ReactiveDurableSettlement`.

One scheduler job therefore retains, at its type indices and equality fields:

* the eager promise and authenticated history notification;
* the reaction and exact accepted link effect;
* the provider execution lease and action grant that admit the job;
* the three-write atomic semantic-post/terminal/outbox intent; and
* the same first-order link request used by human and agent clients.

The scheduler below is an executable logical state machine over
`DurableDataIntent`.  Crash before installation leaves the job runnable; crash
after installation followed by retry is a journal replay.  Dependency
invalidation is represented by changing the guarded trigger root and therefore
fails closed before installation.  Exactly-once here means exactly one logical
terminal/outbox installation and history append.  It does not mean exactly-once
network delivery or exactly-once execution of an external tool.

No value in this module supplies scheduler fairness, actual provider/tool
execution, delivery acknowledgement, OS durability, external finality, or a
human/agent UI runtime.  Those ceilings remain explicit at the end.
-/
import Assurance.HyperdocumentLinkClientLocalFileCutover
import Assurance.HyperdocumentReactiveCarrierWitness
import Kernel.ProviderExecutionLease

namespace Minidregg.Assurance.HyperdocumentAgentRuntimeScheduler

open Minidregg.Assurance.HistoryHeadInhabitation
open Minidregg.Assurance.HyperdocumentAgentOperation
open Minidregg.Assurance.HyperdocumentLinkClientCutover
open Minidregg.Assurance.ReactiveDurableSettlement
open Minidregg.Assurance.ReactiveLifecycleHistory
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Kernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ReactiveTerminalCell
open Minidregg.Theory
open Minidregg.Theory.CanonicalReactiveView
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentInterface
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

namespace Link

noncomputable abbrev materializer :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.documentMaterializer
noncomputable abbrev pre :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.genesisPost
noncomputable abbrev config :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.config
noncomputable abbrev projection :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.projection
noncomputable abbrev authorityPre :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.authorityPre
noncomputable abbrev portal :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.permissivePortal
noncomputable abbrev declaration :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.linkDeclaration
noncomputable abbrev accepted :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.linkAccepted
noncomputable abbrev payload :=
  Minidregg.Assurance.HyperdocumentLinkPublicationWitness.linkPayload

end Link

namespace ReactiveWitness

abbrev firstOrder :=
  Minidregg.Assurance.HyperdocumentReactiveCarrierWitness.firstOrder

end ReactiveWitness

namespace ProviderWitness

noncomputable abbrev lease :=
  Minidregg.Kernel.ProviderExecutionLease.Witness.lease
noncomputable abbrev grant :=
  Minidregg.Kernel.ProviderExecutionLease.Witness.startGrant

end ProviderWitness

/-! ## The exact link promise and authenticated wake -/

def selected : SelectedAction := .link Link.payload

def selection : Selection Link.declaration where
  selected := selected
  actionExact := rfl

def wakeContext : HistoryAdmissionContext where
  manifestAddress := manifest.contentAddress
  historyDomain := ⟨210⟩
  sequence := 20
  previousReceiptRoot := some ⟨211⟩
  semanticObjectRoot := Link.declaration.intent.document.digest
  semanticRelationId := manifest.semanticRelationId
  outcome := .committed
  preStateRoot := ⟨212⟩
  postStateRoot := Link.pre.root
  effectRoot := Link.declaration.effectDigest Link.config
  authorizationRoot := Link.declaration.intent.author.authorId
  disclosureRoot := ⟨213⟩
  dialectClauseRoots := []

theorem wakeContext_wellFormed : wakeContext.WellFormed manifest where
  manifestExact := rfl
  semanticRelationExact := rfl
  historyLink := Or.inr ⟨by decide, ⟨⟨211⟩, rfl⟩⟩
  rejectedAtomic := trivial
  dialectClauseIdsUnique := List.nodup_nil
  dialectClausesClosed := fun _ absent => absurd absent (List.not_mem_nil)

def wakeEntry : VerifiedEntry (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := code) where
  context := wakeContext
  claim := claim
  semantics := PLift.up (fun _ rejected => by cases rejected)
  contextWellFormed := wakeContext_wellFormed
  dialectEvidence := ⟨fun index => index.elim0, fun index => index.elim0⟩
  bindingExact := by rfl
  codeword := Submodule.mem_top

def historyRules : HistoryRules 1 Fld Nat Digest Unit where
  observedHeight := fun context => context.sequence
  Matches := fun condition context _claim =>
    context.postStateRoot = condition
  AdviceAllowed := fun _condition _context _claim bytes => bytes = []
  Breaks := fun _request _reason _context _claim => False

def promiseId : Digest := ⟨214⟩

def continuationId : Digest := ⟨215⟩

theorem requestPreRootExact :
    (Link.declaration.toRequest Link.config).preStateRoot = Link.pre.root :=
  rfl

def promiseSpec : PromiseSpec ReactiveWitness.firstOrder
    (HyperdocumentOperations.family (M := Link.materializer) Link.config)
    Nat Digest Digest :=
  HyperdocumentAgentOperation.promiseSpec
    (U := ReactiveWitness.firstOrder) (MDoc := Link.materializer)
    (contentConfig := Link.config) (documentPre := Link.pre)
    (contentDeclaration := Link.declaration)
    requestPreRootExact promiseId () Link.pre.root 25 continuationId .object
      (Link.declaration.toRequest Link.config)

def promise : Promise promiseSpec := Promise.open promiseSpec

def notification : Notification
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := family)
    (headerCells := headerCells) (C := code) historyRules promiseSpec :=
  notify historyRules promise wakeEntry rfl (by decide) rfl rfl

def reaction : Reaction
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := family)
    (headerCells := headerCells) (C := code) historyRules promiseSpec :=
  react historyRules notification () rfl

def reactiveRequest : HyperdocumentAgentOperation.ReactiveRequest
    (U := ReactiveWitness.firstOrder)
    (MDoc := Link.materializer) (contentConfig := Link.config)
    (documentPre := Link.pre) (contentDeclaration := Link.declaration)
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := family)
    (headerCells := headerCells) (C := code) historyRules
    requestPreRootExact promiseId () Link.pre.root 25 continuationId .object
      (Link.declaration.toRequest Link.config) :=
  HyperdocumentAgentOperation.ReactiveRequest.build selection reaction

def acceptedOperation : HyperdocumentAgentOperation.AcceptedOperation
    (U := ReactiveWitness.firstOrder)
    (MDoc := Link.materializer) (MAuth :=
      Minidregg.Assurance.HyperdocumentLinkPublicationWitness.Genesis.authorityMaterializer)
    (contentConfig := Link.config) (projection := Link.projection)
    (authorityPre := Link.authorityPre) (documentPre := Link.pre)
    (contentPortal := Link.portal) (contentDeclaration := Link.declaration)
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := family)
    (headerCells := headerCells) (C := code) historyRules
    requestPreRootExact promiseId () Link.pre.root 25 continuationId .object
      (Link.declaration.toRequest Link.config) Link.accepted
      HyperdocumentInterface.contentMutationV1 :=
  HyperdocumentAgentOperation.AcceptedOperation.build reactiveRequest

def finalized : Finalized
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := family)
    (headerCells := headerCells) (C := code)
    (portal := Link.portal)
    (authState := CredentialAuthorityState.authState Link.projection
      Link.authorityPre)
    historyRules promiseSpec :=
  HyperdocumentAgentOperation.AcceptedOperation.finalized acceptedOperation

@[simp] theorem finalized_is_exact_link :
    finalized.accepted = Link.accepted.accepted := rfl

@[simp] theorem trigger_is_exact_link_pre_root :
    reaction.notification.entry.context.postStateRoot = Link.pre.root := rfl

theorem selected_link_view_is_invalidated :
    ObserverLens.Dirty ContentQuery.lens selected.query
      Link.accepted.accepted.prepared.delta :=
  selected_view_dirty Link.accepted selection

/-! ## Durable finalization and outbox creation -/

def openCell : OpenCell where
  codecVersion := 1
  domain := ⟨216⟩
  promiseId := promiseId
  deadline := 25
  transactionId := ⟨217⟩
  nullifierId := ⟨218⟩
  eventId := ⟨219⟩
  terminalCell := ⟨220⟩
  outboxCell := ⟨221⟩
  clockCell := ⟨222⟩
  triggerCell := ⟨223⟩
  openTerminalBytes := [224]
  openOutboxBytes := [225]
  exactCharge := fun _ => 0
  terminalOutboxDistinct := by decide
  terminalClockDistinct := by decide
  outboxClockDistinct := by decide
  terminalTriggerDistinct := by decide
  outboxTriggerDistinct := by decide

def durableBinding : ReactiveDurableSettlement.Binding promiseSpec where
  openCell := openCell
  promiseIdExact := rfl
  deadlineExact := rfl

def settlement : ReactiveDurableSettlement.FinalizeSettlement
    durableBinding finalized where
  settledAt := 20
  withinDeadline := by decide
  effectCell := ⟨226⟩
  effectTerminalDistinct := by decide
  effectOutboxDistinct := by decide
  effectClockDistinct := by decide
  effectTriggerDistinct := by decide

abbrev intent : DataIntent Link.materializer.rootBytes := settlement.intent

@[simp] theorem intent_has_exact_three_writes :
    intent.writes =
      [settlement.effectWrite, settlement.terminalPlan.terminalWrite,
        settlement.terminalPlan.outboxWrite] := rfl

@[simp] theorem terminal_is_finalized :
    settlement.terminalPlan.kind = .finalized := rfl

@[simp] theorem terminal_evidence_is_link_post :
    settlement.terminalPlan.evidenceRoot =
      Link.accepted.accepted.prepared.post.root := by
  exact settlement.evidence_root_exact

@[simp] theorem terminal_trigger_is_authenticated_link_pre :
    settlement.terminalPlan.triggerRoot = wakeEntry.context.postStateRoot :=
  by
    simpa [finalized, acceptedOperation, reactiveRequest] using
      settlement.trigger_is_authenticated_observation

/-! ## Provider-lease scheduler admission -/

/-- The lease is evidence carried into scheduling, not a claim that the
provider has executed.  The exact accepted prepay and exact start grant are
retained so the scheduler cannot synthesize a native authority bit. -/
structure LeaseAdmission where
  lease : Minidregg.Kernel.ProviderExecutionLease.OpenedLease
    Minidregg.Theory.CanonicalResourceKernel.materializer
    Minidregg.Theory.TypedAuthorization.demoPortal
    Minidregg.Theory.TypedAuthorization.demoState
    Minidregg.Theory.CanonicalResourceKernel.witnessCell
  leaseExact : lease = ProviderWitness.lease
  grant : Minidregg.Kernel.ProviderExecutionLease.StartGrant
  grantExact : grant = ProviderWitness.grant
  targetExact : grant.target = lease.runtime.providerEndpoint
  actionAllowed :
    Minidregg.Kernel.ProviderExecutionLease.startAction lease ∈ grant.actions

noncomputable def leaseAdmission : LeaseAdmission where
  lease := ProviderWitness.lease
  leaseExact := rfl
  grant := ProviderWitness.grant
  grantExact := rfl
  targetExact := rfl
  actionAllowed := by
    simp [ProviderWitness.grant,
      Minidregg.Kernel.ProviderExecutionLease.Witness.startGrant]

/-! ## Proof-relevant queue item -/

structure Job (command : LinkCommand) where
  lifecycle : finalized.accepted = Link.accepted.accepted
  authenticatedWake : notification.entry = wakeEntry
  leased : LeaseAdmission
  semanticRequest : List UInt8
  requestExact : semanticRequest = command.requestBytes
  settlementExact : settlement.intent = intent

noncomputable def enqueue (command : LinkCommand) : Job command where
  lifecycle := finalized_is_exact_link
  authenticatedWake := rfl
  leased := leaseAdmission
  semanticRequest := command.requestBytes
  requestExact := rfl
  settlementExact := rfl

theorem human_agent_jobs_have_same_semantic_request
    (sessionId interactionId runId toolCallId : Nat) :
    (enqueue (humanCommand sessionId interactionId)).semanticRequest =
      (enqueue (agentCommand runId toolCallId)).semanticRequest := by
  rfl

theorem human_agent_jobs_have_same_declaration
    (sessionId interactionId runId toolCallId : Nat) :
    (humanCommand sessionId interactionId).declarationBytes =
      (agentCommand runId toolCallId).declarationBytes :=
  LinkCommand.human_agent_declaration_bytes_identical _ _ _ _

/-! ## Scheduler state and crash/retry semantics -/

abbrev Store := DataSnapshot Link.materializer.rootBytes

def run (schedule : Schedule) (before : Store) : Outcome Link.materializer.rootBytes :=
  DurableDataIntent.execute schedule before intent

def after (before : Store) (outcome : Outcome Link.materializer.rootBytes) : Store :=
  outcome.storeAfter before

/-- Readiness is proof-relevant.  A queue item cannot turn a failed preflight
into a runnable Boolean: it must carry both absence from the journal and the
exact guarded preflight derivation. -/
structure Ready (before : Store) : Prop where
  unrecorded : Snapshot.lookupRecorded intent.transactionId
    before.model.journal = none
  preflight : intent.preflight before = .ok ()

/-- A closed agent-originated queue item.  Its request bytes are the same
first-order link request admitted for the human client below. -/
def agentJob : Job (agentCommand 300 301) :=
  enqueue (agentCommand 300 301)

theorem ready_run_accepts {command : LinkCommand} {before : Store}
    (_job : Job command)
    (ready : Ready before) :
    run .complete before = .accepted (DataSnapshot.install before intent) :=
  DurableDataIntent.execute_complete_ready before intent
    ready.unrecorded ready.preflight

theorem every_schedule_is_atomic (before : Store) (schedule : Schedule) :
    after before (run schedule before) = before ∨
      after before (run schedule before) = DataSnapshot.install before intent :=
  settlement.semantic_terminal_outbox_atomic schedule before

theorem installed_semantic_terminal_outbox_exact (before : Store) :
    (DataSnapshot.install before intent).canonicalBytes settlement.effectCell =
        Link.accepted.accepted.prepared.post.bytes ∧
      (DataSnapshot.install before intent).canonicalBytes openCell.terminalCell =
        settlement.terminalPlan.terminalBytes ∧
      (DataSnapshot.install before intent).canonicalBytes openCell.outboxCell =
        settlement.terminalPlan.outboxBytes :=
  settlement.installed_exact before

@[simp] theorem installed_appends_exactly_one_history (before : Store) :
    (DataSnapshot.install before intent).model.history =
      before.model.history ++ [intent.erase.event] := rfl

@[simp] theorem exact_retry_is_replay (before : Store) (schedule : Schedule) :
    run schedule (DataSnapshot.install before intent) =
      .replayed intent.erase :=
  settlement.retry_after_install schedule before

theorem exact_retry_does_not_append_second_history
    (before : Store) (schedule : Schedule) :
    (after (DataSnapshot.install before intent)
      (run schedule (DataSnapshot.install before intent))).model.history =
        before.model.history ++ [intent.erase.event] := by
  rw [exact_retry_is_replay]
  rfl

theorem exact_retry_does_not_change_outbox
    (before : Store) (schedule : Schedule) :
    (after (DataSnapshot.install before intent)
      (run schedule (DataSnapshot.install before intent))).canonicalBytes
        openCell.outboxCell = settlement.terminalPlan.outboxBytes := by
  rw [exact_retry_is_replay]
  exact (installed_semantic_terminal_outbox_exact before).2.2

theorem crash_before_then_retry_accepts {command : LinkCommand} {before : Store}
    (_job : Job command) (ready : Ready before) :
    run (.crash .beforeAtomicInstall) before =
        .crashed .beforeAtomicInstall before ∧
      run .complete
          (after before (run (.crash .beforeAtomicInstall) before)) =
        .accepted (DataSnapshot.install before intent) := by
  have crash : run (.crash .beforeAtomicInstall) before =
      .crashed .beforeAtomicInstall before := by
    unfold run DurableDataIntent.execute
    rw [ready.unrecorded, ready.preflight]
  refine ⟨crash, ?_⟩
  rw [crash]
  exact ready_run_accepts _job ready

theorem crash_after_then_retry_replays {command : LinkCommand} {before : Store}
    (_job : Job command) (ready : Ready before) :
    run (.crash .afterAtomicInstall) before =
        .crashed .afterAtomicInstall (DataSnapshot.install before intent) ∧
      run .complete
          (after before (run (.crash .afterAtomicInstall) before)) =
        .replayed intent.erase := by
  have crash : run (.crash .afterAtomicInstall) before =
      .crashed .afterAtomicInstall (DataSnapshot.install before intent) := by
    unfold run DurableDataIntent.execute
    rw [ready.unrecorded, ready.preflight]
  refine ⟨crash, ?_⟩
  rw [crash]
  exact exact_retry_is_replay before .complete

/-! ## Dependency invalidation is the trigger read guard -/

/-- A scheduler snapshot whose dependency cell no longer has the authenticated
trigger root fails closed.  The changed snapshot must itself come from the
store refinement boundary; this theorem does not fabricate a physical write. -/
theorem invalidated_dependency_preflight_rejects (before : Store)
    (changed : before.model.roots openCell.triggerCell ≠
      settlement.terminalPlan.triggerRoot) :
    intent.preflight before = .error .staleReadGuard := by
  apply DurableDataIntent.stale_read_guard_rejected
  refine ⟨settlement.terminalPlan.triggerGuard, ?_, ?_⟩
  · simp [intent, ReactiveDurableSettlement.FinalizeSettlement.intent]
  · simpa [ReactiveTerminalCell.Plan.triggerGuard] using changed

theorem invalidated_dependency_cannot_finalize (before : Store)
    (changed : before.model.roots openCell.triggerCell ≠
      settlement.terminalPlan.triggerRoot) :
    run .complete before = .rejected .staleReadGuard ∨
    Snapshot.lookupRecorded intent.transactionId
      before.model.journal ≠ none := by
  by_cases recorded : Snapshot.lookupRecorded intent.transactionId
      before.model.journal = none
  · left
    unfold run DurableDataIntent.execute
    rw [recorded, invalidated_dependency_preflight_rejects before changed]
  · exact Or.inr recorded

/-! ## Existing local-store client projection -/

theorem local_store_agent_receives_exact_link (runId toolCallId : Nat) :
    (submitLink
      (HyperdocumentLinkClientCutover.LocalFile.loseFirstStoreResponse
        HyperdocumentLinkClientCutover.LocalFile.modelBoundary)
      (agentCommand runId toolCallId)).record? =
        some Endpoint.record :=
  HyperdocumentLinkClientCutover.LocalFile.model_agent_client_reopens _ _

theorem local_store_human_and_agent_same_semantics
    (sessionId interactionId runId toolCallId : Nat) :
    (humanCommand sessionId interactionId).requestBytes =
        (agentCommand runId toolCallId).requestBytes ∧
      (submitLink
        (HyperdocumentLinkClientCutover.LocalFile.loseFirstStoreResponse
          HyperdocumentLinkClientCutover.LocalFile.modelBoundary)
        (humanCommand sessionId interactionId)).record? =
      (submitLink
        (HyperdocumentLinkClientCutover.LocalFile.loseFirstStoreResponse
          HyperdocumentLinkClientCutover.LocalFile.modelBoundary)
        (agentCommand runId toolCallId)).record? := by
  constructor
  · rfl
  · rw [HyperdocumentLinkClientCutover.LocalFile.model_human_client_reopens,
      HyperdocumentLinkClientCutover.LocalFile.model_agent_client_reopens]

/-! ## Explicit deployment and liveness ceiling -/

/-- These are relations/evidence a real DeOS runtime must provide.  None is
constructed here.  In particular, an installed outbox record is not a delivery
acknowledgement and an accepted provider lease is not evidence that a tool ran.
-/
structure RuntimeCompletion
    (SchedulerFair ToolExecutionRefined DeliveryAckAuthenticated
      EventuallyDelivered PhysicalStoreRefined OsDurability ExternalFinality
      HumanUiRuntime AgentRuntime : Prop) : Prop where
  schedulerFair : SchedulerFair
  toolExecutionRefined : ToolExecutionRefined
  deliveryAckAuthenticated : DeliveryAckAuthenticated
  eventuallyDelivered : EventuallyDelivered
  physicalStoreRefined : PhysicalStoreRefined
  osDurable : OsDurability
  externalFinality : ExternalFinality
  humanUiRuntime : HumanUiRuntime
  agentRuntime : AgentRuntime

/-! ## Axiom audit -/

#print axioms finalized_is_exact_link
#print axioms selected_link_view_is_invalidated
#print axioms ready_run_accepts
#print axioms crash_after_then_retry_replays
#print axioms invalidated_dependency_preflight_rejects
#print axioms local_store_human_and_agent_same_semantics

end

end Minidregg.Assurance.HyperdocumentAgentRuntimeScheduler
