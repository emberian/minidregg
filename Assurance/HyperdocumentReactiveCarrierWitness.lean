/-
# Assurance.HyperdocumentReactiveCarrierWitness -- a built reactive document turn

This module closes the abstract reactive-carrier cluster at one deployed
Hyperdocument operation.  It instantiates `ReactiveController.HostObservation`,
`ProofData`, `CellState.ControllerLayout`, and
`ReactiveCellTransition.Accepted` for the canonical create patch already
inhabited by `HyperdocumentCausalFamily.Witness`.

The second half consumes one exact verified history entry with concrete
`HistoryRules`, finalizes the same accepted Hyperdocument effect, and binds it
to `ReactiveDurableSettlement`.  The history entry is a logical verified-entry
witness, not a claim of deployed PCS openings or chain finality; those remain
explicitly outside this module.
-/
import Assurance.HistoryHeadInhabitation
import Assurance.HyperdocumentAgentOperation
import Assurance.ReactiveDurableSettlement
import Theory.HyperdocumentCausalFamily
import Theory.ReactiveCellTransition

namespace Minidregg.Assurance.HyperdocumentReactiveCarrierWitness

open Minidregg.Assurance.HistoryHeadInhabitation
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
open Minidregg.Theory.GuardedAdvice
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

namespace HW
noncomputable abbrev materializer :=
  Minidregg.Theory.DeployedMaterializerWitness.hyperdocumentMaterializer
noncomputable abbrev pre :=
  Minidregg.Theory.DeployedMaterializerWitness.hyperdocumentCell
noncomputable abbrev config :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.config
noncomputable abbrev declaration :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.declaration
noncomputable abbrev accepted :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.accepted
noncomputable abbrev projection :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.projection
noncomputable abbrev authorityPre :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.authorityPre
noncomputable abbrev portal :=
  Minidregg.Theory.TypedAuthorizationWitness.permissivePortal
end HW

set_option autoImplicit false

noncomputable section

/-! ## Closed first-order controller carriers -/

def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode := fun bytes => if bytes = [] then some () else none
  decode_encode := by intro; simp

abbrev firstOrder : FirstOrderUniverse where
  Code := Unit
  El := fun _ => Unit
  codec := fun _ => unitCodec

abbrev controllerTypes : ReactiveController.Types where
  Key := Address
  Value := Unit
  HoleId := Nat
  TurnId := Nat
  Root := Digest
  AuthorityDemand := Digest
  Commitment := Digest
  Height := Nat
  Continuation := Digest
  NullifierDomain := Digest

local instance : DecidableEq
    (ReactiveController.HoleSpec firstOrder controllerTypes) :=
  Classical.decEq _

local instance : DecidableEq controllerTypes.Key := by
  change DecidableEq Address
  infer_instance

local instance : LinearOrder controllerTypes.Height := by
  change LinearOrder Nat
  infer_instance

local instance : DecidableEq
    (GuardedAdvice.NullifierKey controllerTypes.vocabulary) :=
  Classical.decEq _

def layout : CellState.ControllerLayout cellSchema.{0, 0} controllerTypes where
  fieldKey := id
  resourceKey := Empty.elim

def patch : CellState.Patch cellSchema.{0, 0} Digest :=
  HW.declaration.patch HW.config

def controllerWrites : List (controllerTypes.Key × controllerTypes.Value) :=
  (patch.controllerFootprint layout).toList.map fun key => (key, ())

def hole : ReactiveController.HoleSpec firstOrder controllerTypes where
  holeId := 40
  code := ()
  turnId := 41
  preRoot := HW.pre.root
  authorityDemand := ⟨42⟩
  footprint := patch.controllerFootprint layout
  guardCommitment := ⟨43⟩
  effectCommitment := HW.declaration.effectDigest HW.config
  deadline := 25
  continuation := ⟨44⟩
  nullifierDomain := ⟨45⟩

def declaration : ReactiveController.Declaration firstOrder controllerTypes where
  hole := hole
  guard := .bytesEq []
  effect :=
    { writes := controllerWrites
      expectedPostRoot := HW.accepted.accepted.prepared.post.root }
  wakeAfter := some hole.turnId

def advice : ReactiveController.Advice declaration.hole := ⟨()⟩

def observation : ReactiveController.HostObservation controllerTypes where
  now := 20
  durableRoot := HW.pre.root
  backendAvailable := true
  finalizedTurns := {hole.turnId}
  consumed := ∅

def proofData : ReactiveController.ProofData controllerTypes where
  authority := hole.authorityDemand
  guardCommitment := hole.guardCommitment
  effectCommitment := hole.effectCommitment
  writes := controllerWrites
  postRoot := HW.accepted.accepted.prepared.post.root

def controllerPre : ReactiveReceipt.Store controllerTypes.Key controllerTypes.Value :=
  fun _ => ()

@[simp] theorem effect_touched_exact :
    declaration.effect.touched = declaration.hole.footprint := by
  simp [declaration, hole, controllerWrites,
    ReactiveController.EffectDecl.touched, Function.comp_def]

@[simp] theorem advice_bytes_exact :
    declaration.hole.codec.encode advice.value = [] := rfl

private theorem supports_exact :
    (declaration.verifier observation proofData).supports declaration.hole = true := by
  simp [ReactiveController.Declaration.verifier]

private theorem backend_exact :
    (declaration.verifier observation proofData).backendAvailable declaration.hole =
      true := rfl

private theorem ready_exact :
    (declaration.verifier observation proofData).ready declaration.hole advice =
      true := by
  simp [ReactiveController.Declaration.verifier,
    ReactiveController.Declaration.ready, declaration, observation, hole]

private theorem authority_exact :
    (declaration.verifier observation proofData).authorityAccepts
      declaration.hole advice = true := by
  simp [ReactiveController.Declaration.verifier, declaration, proofData, hole]

private theorem guard_exact :
    (declaration.verifier observation proofData).guardAccepts
      declaration.hole advice = true := by
  change ReactiveController.GuardTerm.eval
      (declaration.hole.codec.encode advice.value) declaration.guard = true
  change decide (([] : List UInt8) = []) = true
  rfl

private theorem effect_exact :
    (declaration.verifier observation proofData).effectAccepts
      declaration.hole advice = true := by
  change (decide (proofData.effectCommitment = declaration.hole.effectCommitment) &&
      decide (proofData.writes = declaration.effect.writes) &&
      decide (proofData.postRoot = declaration.effect.expectedPostRoot) &&
      decide (declaration.effect.touched = declaration.hole.footprint)) = true
  rw [effect_touched_exact]
  simp [proofData, declaration, hole]

theorem guarded_accepts :
    ∃ verified : GuardedAdvice.VerifiedFill
        (declaration.verifier observation proofData) observation.now
        declaration.hole advice,
      GuardedAdvice.verifyFill (declaration.verifier observation proofData)
          observation.now declaration.hole advice = .accepted verified := by
  unfold GuardedAdvice.verifyFill
  simp only [supports_exact, backend_exact, ready_exact, authority_exact,
    guard_exact, effect_exact]
  exact ⟨_, rfl⟩

private theorem control_commits_of_verified
    {decl : ReactiveController.Declaration firstOrder controllerTypes}
    {obs : ReactiveController.HostObservation controllerTypes}
    {lateAdvice : ReactiveController.Advice decl.hole}
    {lateProof : ReactiveController.ProofData controllerTypes}
    {preStore : ReactiveReceipt.Store controllerTypes.Key controllerTypes.Value}
    (verified : GuardedAdvice.VerifiedFill (decl.verifier obs lateProof) obs.now
      decl.hole lateAdvice)
    (verifyExact : GuardedAdvice.verifyFill (decl.verifier obs lateProof) obs.now
      decl.hole lateAdvice = .accepted verified)
    (rootExact : obs.durableRoot = decl.hole.preRoot)
    (fresh : decl.hole.nullifierKey ∉ obs.consumed) :
    ∃ intent : ReactiveController.CommitIntent decl obs lateAdvice lateProof preStore,
    ReactiveController.control decl obs lateAdvice lateProof preStore =
        .commitIntent intent := by
  unfold ReactiveController.control
  split <;> simp_all

private theorem control_stale_of_verified
    {decl : ReactiveController.Declaration firstOrder controllerTypes}
    {obs : ReactiveController.HostObservation controllerTypes}
    {lateAdvice : ReactiveController.Advice decl.hole}
    {lateProof : ReactiveController.ProofData controllerTypes}
    {preStore : ReactiveReceipt.Store controllerTypes.Key controllerTypes.Value}
    {verified : GuardedAdvice.VerifiedFill (decl.verifier obs lateProof) obs.now
      decl.hole lateAdvice}
    (verifyExact : GuardedAdvice.verifyFill (decl.verifier obs lateProof) obs.now
      decl.hole lateAdvice = .accepted verified)
    (rootWrong : obs.durableRoot ≠ decl.hole.preRoot) :
    ReactiveController.control decl obs lateAdvice lateProof preStore =
      .reject .stalePreRoot := by
  unfold ReactiveController.control
  split <;> simp_all

private theorem control_replay_of_verified
    {decl : ReactiveController.Declaration firstOrder controllerTypes}
    {obs : ReactiveController.HostObservation controllerTypes}
    {lateAdvice : ReactiveController.Advice decl.hole}
    {lateProof : ReactiveController.ProofData controllerTypes}
    {preStore : ReactiveReceipt.Store controllerTypes.Key controllerTypes.Value}
    {verified : GuardedAdvice.VerifiedFill (decl.verifier obs lateProof) obs.now
      decl.hole lateAdvice}
    (verifyExact : GuardedAdvice.verifyFill (decl.verifier obs lateProof) obs.now
      decl.hole lateAdvice = .accepted verified)
    (rootExact : obs.durableRoot = decl.hole.preRoot)
    (consumed : decl.hole.nullifierKey ∈ obs.consumed) :
    ReactiveController.control decl obs lateAdvice lateProof preStore =
      .reject .alreadyConsumed := by
  unfold ReactiveController.control
  split <;> simp_all

private theorem control_expired_of_verify
    {decl : ReactiveController.Declaration firstOrder controllerTypes}
    {obs : ReactiveController.HostObservation controllerTypes}
    {lateAdvice : ReactiveController.Advice decl.hole}
    {lateProof : ReactiveController.ProofData controllerTypes}
    {preStore : ReactiveReceipt.Store controllerTypes.Key controllerTypes.Value}
    (verifyExact : GuardedAdvice.verifyFill (decl.verifier obs lateProof) obs.now
      decl.hole lateAdvice = .expired) :
    ReactiveController.control decl obs lateAdvice lateProof preStore =
      .reject .expired := by
  unfold ReactiveController.control
  split <;> simp_all

theorem controller_accepts :
    ∃ intent : ReactiveController.CommitIntent declaration observation advice
        proofData controllerPre,
      ReactiveController.control declaration observation advice proofData
        controllerPre = ReactiveController.Outcome.commitIntent intent := by
  rcases guarded_accepts with ⟨verified, verifyExact⟩
  apply control_commits_of_verified verified verifyExact
  · rfl
  · simp [observation]

noncomputable def controllerIntent : ReactiveController.CommitIntent
    declaration observation advice proofData controllerPre :=
  Classical.choose controller_accepts

theorem controller_exact :
    ReactiveController.control declaration observation advice proofData
      controllerPre = ReactiveController.Outcome.commitIntent controllerIntent :=
  Classical.choose_spec controller_accepts

theorem controller_pre_root_exact :
    controllerIntent.request.preRoot = HW.pre.root := by
  rcases controllerIntent.request_binds_hole with
    ⟨_, _, _, preRootExact, _⟩
  exact preRootExact

theorem controller_post_root_exact :
    controllerIntent.verified.postRoot =
      HW.accepted.accepted.validated.apply.root := by
  calc
    controllerIntent.verified.postRoot = proofData.postRoot := by
      simpa [ReactiveController.Declaration.verifier] using
        controllerIntent.verified.postRoot_eq
    _ = HW.accepted.accepted.validated.apply.root := rfl

theorem controller_footprint_exact :
    patch.controllerFootprint layout = declaration.hole.footprint := rfl

set_option maxRecDepth 10000 in
theorem patch_validates :
    CellState.validate HW.materializer HW.pre patch =
      CellState.ValidationOutcome.accepted HW.accepted.accepted.validated := by
  have rootExact : (HW.declaration.patch HW.config).expectedPreRoot = HW.pre.root :=
    HW.accepted.accepted.validated.preRoot_bound
  have fieldsExact : (HW.declaration.patch HW.config).fieldFootprint =
      (HW.declaration.patch HW.config).namedFields :=
    HW.accepted.accepted.validated.fields_exact
  have resourcesExact : (HW.declaration.patch HW.config).resourceFootprint =
      (HW.declaration.patch HW.config).namedResources :=
    HW.accepted.accepted.validated.resources_exact
  change CellState.validate HW.materializer HW.pre
      (HW.declaration.patch HW.config) =
    CellState.ValidationOutcome.accepted HW.accepted.accepted.validated
  unfold CellState.validate
  simp only [rootExact, fieldsExact, resourcesExact]
  congr

set_option maxRecDepth 10000 in
theorem transition_accepts :
    ∃ accepted : ReactiveCellTransition.Accepted HW.materializer layout
        declaration observation advice proofData controllerPre HW.pre patch,
      ReactiveCellTransition.transition HW.materializer
      layout declaration observation advice proofData controllerPre
      HW.pre patch = ReactiveCellTransition.Outcome.accepted accepted := by
  unfold ReactiveCellTransition.transition
  simp only [controller_exact, patch_validates]
  split
  · split
    · split
      · exact ⟨_, rfl⟩
      · contradiction
    · rename_i _ postMismatch
      exact False.elim (postMismatch (by
        simpa using controller_post_root_exact))
  · contradiction

noncomputable def acceptedTransition : ReactiveCellTransition.Accepted
    HW.materializer layout declaration observation advice proofData
      controllerPre HW.pre patch :=
  Classical.choose transition_accepts

theorem transition_exact :
    ReactiveCellTransition.transition HW.materializer
      layout declaration observation advice proofData controllerPre
      HW.pre patch = ReactiveCellTransition.Outcome.accepted acceptedTransition :=
  Classical.choose_spec transition_accepts

theorem reactive_post_is_hyperdocument_post :
    acceptedTransition.validated.apply =
      HW.accepted.accepted.prepared.post := by
  rfl

/-! ## Controller rejection teeth -/

def wrongRoot : Digest := ⟨HW.pre.root.value + 1⟩

theorem wrongRoot_ne : wrongRoot ≠ HW.pre.root := by
  intro equal
  have values := congrArg Digest.value equal
  simp [wrongRoot] at values

def wrongRootObservation : ReactiveController.HostObservation controllerTypes :=
  { observation with durableRoot := wrongRoot }

@[simp] theorem wrong_root_rejected :
    ReactiveController.control declaration wrongRootObservation advice proofData
      controllerPre =
        (ReactiveController.Outcome.reject .stalePreRoot :
          ReactiveController.Outcome declaration wrongRootObservation advice
            proofData controllerPre) := by
  rcases guarded_accepts with ⟨verified, verifyExact⟩
  unfold ReactiveController.control
  have wrongVerify : GuardedAdvice.verifyFill
      (declaration.verifier wrongRootObservation proofData)
      wrongRootObservation.now declaration.hole advice = .accepted verified := by
    simpa [wrongRootObservation] using verifyExact
  apply control_stale_of_verified wrongVerify
  simpa [wrongRootObservation, observation, declaration, hole] using wrongRoot_ne

def expiredObservation : ReactiveController.HostObservation controllerTypes :=
  { observation with now := hole.deadline + 1 }

@[simp] theorem expired_rejected :
    ReactiveController.control declaration expiredObservation advice proofData
      controllerPre =
        (ReactiveController.Outcome.reject .expired :
          ReactiveController.Outcome declaration expiredObservation advice
            proofData controllerPre) := by
  unfold ReactiveController.control
  have expiredVerify : GuardedAdvice.verifyFill
      (declaration.verifier expiredObservation proofData)
      expiredObservation.now declaration.hole advice = .expired := by
    unfold GuardedAdvice.verifyFill
    simp only [show (declaration.verifier expiredObservation proofData).supports
        declaration.hole = true by
          simpa [expiredObservation] using supports_exact,
      show (declaration.verifier expiredObservation proofData).backendAvailable
        declaration.hole = true by
          simpa [expiredObservation] using backend_exact]
    simp [expiredObservation, observation, declaration, hole]
  exact control_expired_of_verify expiredVerify

def replayObservation : ReactiveController.HostObservation controllerTypes :=
  { observation with consumed := {declaration.hole.nullifierKey} }

@[simp] theorem consumed_replay_rejected :
    ReactiveController.control declaration replayObservation advice proofData
      controllerPre =
        (ReactiveController.Outcome.reject .alreadyConsumed :
          ReactiveController.Outcome declaration replayObservation advice
            proofData controllerPre) := by
  rcases guarded_accepts with ⟨verified, verifyExact⟩
  unfold ReactiveController.control
  have replayVerify : GuardedAdvice.verifyFill
      (declaration.verifier replayObservation proofData)
      replayObservation.now declaration.hole advice = .accepted verified := by
    simpa [replayObservation] using verifyExact
  apply control_replay_of_verified replayVerify
  · rfl
  · simp [replayObservation]

/-! ## One authenticated history wake at the exact document pre-root -/

def wakeContext : HistoryAdmissionContext where
  manifestAddress := manifest.contentAddress
  historyDomain := ⟨46⟩
  sequence := 20
  previousReceiptRoot := some ⟨47⟩
  semanticObjectRoot := HW.declaration.intent.document.digest
  semanticRelationId := manifest.semanticRelationId
  outcome := .committed
  preStateRoot := ⟨48⟩
  postStateRoot := HW.pre.root
  effectRoot := HW.declaration.effectDigest HW.config
  authorizationRoot := HW.declaration.intent.author.authorId
  disclosureRoot := ⟨49⟩
  dialectClauseRoots := []

theorem wakeContext_wellFormed : wakeContext.WellFormed manifest where
  manifestExact := rfl
  semanticRelationExact := rfl
  historyLink := Or.inr ⟨by decide, ⟨⟨47⟩, rfl⟩⟩
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

def promiseId : Digest := ⟨50⟩

def continuationId : Digest := ⟨51⟩

def promiseSpec : PromiseSpec firstOrder
    (HyperdocumentOperations.family (M := HW.materializer) HW.config)
    Nat Digest Digest :=
  HyperdocumentAgentOperation.promiseSpec
    (U := firstOrder) (MDoc := HW.materializer)
    (contentConfig := HW.config) (documentPre := HW.pre)
    (contentDeclaration := HW.declaration)
    rfl promiseId () HW.pre.root 25 continuationId .object
      (HW.declaration.toRequest HW.config)

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

def finalized : Finalized
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (entryFamily := family)
    (headerCells := headerCells) (C := code)
    (portal := HW.portal)
    (authState := CredentialAuthorityState.authState HW.projection HW.authorityPre)
    historyRules promiseSpec :=
  finalize historyRules reaction HW.accepted.accepted

@[simp] theorem history_wake_post_root_exact :
    notification.entry.context.postStateRoot = HW.pre.root := rfl

@[simp] theorem finalized_content_exact :
    finalized.accepted = HW.accepted.accepted := rfl

@[simp] theorem finalized_reactive_post_exact :
    finalized.accepted.prepared.post = acceptedTransition.validated.apply := rfl

theorem wake_not_after_deadline :
    ¬ (promiseSpec.deadline <
      historyRules.observedHeight notification.entry.context) :=
  notificationNotAfterDeadline notification

/-! ## Durable terminal settlement of that same authenticated wake -/

def openCell : OpenCell where
  codecVersion := 1
  domain := ⟨52⟩
  promiseId := promiseId
  deadline := 25
  transactionId := ⟨53⟩
  nullifierId := ⟨54⟩
  eventId := ⟨55⟩
  terminalCell := ⟨56⟩
  outboxCell := ⟨57⟩
  clockCell := ⟨58⟩
  triggerCell := ⟨59⟩
  openTerminalBytes := [60]
  openOutboxBytes := [61]
  exactCharge := fun _ => 0
  terminalOutboxDistinct := by decide
  terminalClockDistinct := by decide
  outboxClockDistinct := by decide
  terminalTriggerDistinct := by decide
  outboxTriggerDistinct := by decide

def durableBinding : Binding promiseSpec where
  openCell := openCell
  promiseIdExact := rfl
  deadlineExact := rfl

def settlement : FinalizeSettlement durableBinding finalized where
  settledAt := 20
  withinDeadline := by decide
  effectCell := ⟨62⟩
  effectTerminalDistinct := by decide
  effectOutboxDistinct := by decide
  effectClockDistinct := by decide
  effectTriggerDistinct := by decide

@[simp] theorem terminal_trigger_is_verified_history_root :
    settlement.terminalPlan.triggerRoot = wakeEntry.context.postStateRoot :=
  settlement.trigger_is_authenticated_observation

@[simp] theorem terminal_evidence_is_reactive_post_root :
    settlement.terminalPlan.evidenceRoot = acceptedTransition.validated.apply.root := by
  rw [settlement.evidence_root_exact]
  rfl

theorem exact_retry_replays
    (schedule : Schedule)
    (before : DataSnapshot HW.materializer.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before settlement.intent) settlement.intent =
      .replayed settlement.intent.erase :=
  settlement.retry_after_install schedule before

theorem different_terminal_after_finalize_conflicts
    (alternative : Plan HW.materializer.rootBytes durableBinding.openCell)
    (different : settlement.terminalPlan.kind ≠ alternative.kind)
    (schedule : Schedule)
    (before : DataSnapshot HW.materializer.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before settlement.intent) alternative.intent =
      .rejected (.durable .transactionConflict) :=
  settlement.alternative_after_finalize_conflicts alternative different
    schedule before

theorem terminal_race_has_no_partial_commit
    (schedule : Schedule)
    (before : DataSnapshot HW.materializer.rootBytes) :
    (DurableDataIntent.execute schedule before settlement.intent).storeAfter before =
        before ∨
      (DurableDataIntent.execute schedule before settlement.intent).storeAfter before =
        DataSnapshot.install before settlement.intent :=
  settlement.semantic_terminal_outbox_atomic schedule before

/-!
The witness above instantiates the logical carriers and exact durable payload.
It deliberately does not manufacture cryptographic openings, an external
finality oracle, durable-store refinement, scheduler fairness, or outbox
delivery.  A deployment has to supply those independently.
-/
structure DeploymentCeiling where
  commitmentOpeningSound : Prop
  authenticatedFinality : Prop
  durableRefinement : Prop
  schedulerFairness : Prop
  eventualOutboxDelivery : Prop

/-! ## Narrow assurance audit -/

#print axioms transition_exact
#print axioms wrong_root_rejected
#print axioms expired_rejected
#print axioms consumed_replay_rejected
#print axioms terminal_trigger_is_verified_history_root
#print axioms exact_retry_replays
#print axioms different_terminal_after_finalize_conflicts
#print axioms terminal_race_has_no_partial_commit

end

end Minidregg.Assurance.HyperdocumentReactiveCarrierWitness
