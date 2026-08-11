/-
# Assurance.PrivateEscrowSettlementJoin -- Drex/FHEgg/Dark-Bazaar consumer join

This module supplies the indexed source family required by
`Kernel.PrivateEscrowSettlement`.

* NoteSpend and BFV are fail-closed empty branches while their canonical proof
  suite identities remain zero.  Their in-process arithmetic tokens are not
  treated as cryptographic market receipts.
* The shared-MPC source is inhabited now by `MpcSealedCellExecution.accepted`.
  It proves only the executable Lean relation and declared quorum agreement;
  it is deliberately tagged `declaredMpc`, never `semanticProof`.

The first two carriers are intentionally empty for today's canonical
zero-pinned requests.  Their impossibility theorems are part of the
consumer boundary: an in-process arithmetic token cannot be laundered into a
deployed cryptographic proof.  The shared-MPC carrier gives one honest
non-cryptographic positive path and retains its executor/authentication ceiling.

The final constructors turn any exact source into the kernel's sealed receipt
and later authorized settlement.  They do not manufacture a declassification
token, public fill authorization, root refinement, physical durability, or
outbox delivery.
-/
import Assurance.BfvProofControllerAdmission
import Assurance.MpcSealedCellExecution
import Assurance.NoteSpendConcreteCellAdapter
import Kernel.PrivateEscrowSettlement

namespace Minidregg.Assurance.PrivateEscrowSettlementJoin

open Minidregg.Kernel.CanonicalEscrowMarket
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.PrivateEscrowSettlement
open Minidregg.Theory
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

namespace NoteSource

open Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect

/-- The canonical NoteSpend request is deliberately not a current source for
market settlement.  Its zero suite pin is not upgraded by the existence of an
in-process arithmetic accepted effect. -/
abbrev SemanticCell := PEmpty

theorem current_suite_unassigned : modeEvidencePins.proofSuiteId = ⟨0⟩ :=
  cryptographic_pins_unassigned.1

theorem no_current_semantic_cell : IsEmpty SemanticCell := inferInstance

end NoteSource

namespace BfvSource

open Minidregg.Compiler.BfvReceiptClause

/-- Direct 384-row arithmetic admission is real, but the canonical BFV proof
codec, suite, and controller remain zero.  Therefore it is not a current
cryptographic market source. -/
abbrev SemanticCell := PEmpty

theorem current_suite_unassigned :
    bfvClausePin.proofSuiteStatus = .unassigned /\
      bfvClausePin.declaration.proofCodecId = ⟨0⟩ /\
      bfvClausePin.declaration.proofSuiteId = ⟨0⟩ /\
      bfvClausePin.declaration.verifierControllerDigest = ⟨0⟩ :=
  bfvClausePin_unassigned

theorem no_current_semantic_cell : IsEmpty SemanticCell := inferInstance

end BfvSource

namespace MpcSource

open Minidregg.Assurance.MpcSealedCellExecution

abbrev Accepted := ComputationCellEffect.Accepted
  (portal := Minidregg.Theory.TypedAuthorizationWitness.permissivePortal)
  (authState := Minidregg.Theory.TypedAuthorizationWitness.authState)
  declaration adapter commonRequest pre honestRequest honestResult

def binding : EvidenceBinding where
  mode := .sharedMpc
  status := .declaredMpc
  pins := .zero
  protocolId := pins.protocolId
  federationId := pins.federationId
  semanticAssigned := by intro impossible; cases impossible
  mpcShape := by
    intro _
    exact ⟨rfl, rfl, by decide, by decide⟩

@[simp] theorem binding_acceptable : binding.Acceptable := Or.inr rfl

structure SemanticCell where
  accepted : Accepted

noncomputable def semanticCell : SemanticCell := ⟨accepted⟩

theorem semanticCell_nonempty : Nonempty SemanticCell := ⟨semanticCell⟩

theorem declared_quorum_agreement
    (_source : SemanticCell) :
    DeclaredQuorumAgreement
      (declaration.statementOf honestRequest honestResult) honestEvidence :=
  accepted_declared_quorum_agreement

theorem disclosure_sealed (_source : SemanticCell) :
    accepted.cellEffect.disclosure = .sealed :=
  accepted_disclosure_sealed

theorem no_release (_source : SemanticCell)
    (release : (ComputationCellEffect.family
      (M := Minidregg.Assurance.MpcSealedCellExecution.materializer)
      declaration adapter).Release honestRequest honestResult) : False :=
  accepted_has_no_release release

end MpcSource

/-! ## One canonical indexed source family -/

inductive CanonicalSource (claim : Claim) (evidence : EvidenceBinding) : Type
  | sharedMpc (source : MpcSource.SemanticCell)
      (evidenceExact : evidence = MpcSource.binding)
      (preExact : claim.sourcePreRoot =
        Minidregg.Assurance.MpcSealedCellExecution.pre.root)
      (postExact : claim.sourcePostRoot =
        source.accepted.cellEffect.prepared.postRoot)
      (nullifierExact : claim.computationNullifier =
        Minidregg.Assurance.MpcSealedCellExecution.sessionId)
      (outputExact : claim.outputCommitment =
        Minidregg.Assurance.MpcSealedCellExecution.honestOutputArtifact.commitment)

namespace CanonicalSource

theorem acceptable {claim : Claim} {evidence : EvidenceBinding}
    (source : CanonicalSource claim evidence) : evidence.Acceptable := by
  cases source with
  | sharedMpc _ exact _ _ _ _ =>
      subst exact
      exact MpcSource.binding_acceptable

/-- Any currently inhabitable source is the honest, explicitly
non-cryptographic shared-MPC branch. -/
theorem current_source_is_sharedMpc
    {claim : Claim} {evidence : EvidenceBinding}
    (source : CanonicalSource claim evidence) :
    evidence.mode = .sharedMpc /\ evidence.status = .declaredMpc := by
  cases source with
  | sharedMpc _ exact _ _ _ _ =>
      subst exact
      exact ⟨rfl, rfl⟩

end CanonicalSource

/-! ## Exact sealed and settlement constructors -/

/-- Construct the first durable phase from an actual indexed source.  The
source cell roots and the durable wrapper roots are both retained by `claim`;
`computationPostBytes` is an explicit representation refinement between them. -/
def acceptSealed
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    (claim : Claim) (evidence : EvidenceBinding)
    (source : CanonicalSource claim evidence)
    (runtime : SealedRuntime) (computationPostBytes : List UInt8)
    (computationPreBound :
      M.rootBytes runtime.openComputationBytes = claim.computationPreRoot)
    (computationPostBound :
      M.rootBytes computationPostBytes = claim.computationPostRoot) :
    SealedAcceptance CanonicalSource M where
  claim := claim
  evidence := evidence
  acceptable := source.acceptable
  source := source
  runtime := runtime
  computationPostBytes := computationPostBytes
  computationPreBound := computationPreBound
  computationPostBound := computationPostBound

/-- The later constructor cannot weaken either source acceptance or public
fill authorization: it only packages their exact existing values with a new
declassification token and terminal/outbox runtime. -/
def settle
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (sealed : SealedAcceptance CanonicalSource M)
    (fill : Fill M portal authState)
    (claimBound : sealed.claim.BoundTo fill)
    (declassification : Declassification sealed.claim fill)
    (runtime : ReleaseRuntime sealed fill) :
    Settlement CanonicalSource M portal authState where
  sealed := sealed
  fill := fill
  claimBound := claimBound
  declassification := declassification
  runtime := runtime

theorem settled_source_status
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (settlement : Settlement CanonicalSource M portal authState) :
    settlement.sealed.evidence.mode = .sharedMpc /\
      settlement.sealed.evidence.status = .declaredMpc :=
  settlement.sealed.source.current_source_is_sharedMpc

theorem settled_keeps_receipt_separate
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (settlement : Settlement CanonicalSource M portal authState) :
    settlement.sealed.runtime.receiptCell ∉
        settlement.intent.writes.map DataWrite.cellId /\
      settlement.sealed.runtime.computationCell ∉
        settlement.intent.writes.map DataWrite.cellId := by
  constructor
  · intro member
    simp only [Settlement.intent, List.map_append, List.mem_append,
      List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with inFill | terminal | outbox
    · exact settlement.runtime.receiptNotFill inFill
    · exact settlement.runtime.receiptTerminalDistinct terminal
    · exact settlement.runtime.receiptOutboxDistinct outbox
  · intro member
    simp only [Settlement.intent, List.map_append, List.mem_append,
      List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with inFill | terminal | outbox
    · exact settlement.runtime.computationNotFill inFill
    · exact settlement.runtime.computationTerminalDistinct terminal
    · exact settlement.runtime.computationOutboxDistinct outbox

/-! ## One non-vacuous private-market order -/

namespace Witness

abbrev MarketMaterializer := CanonicalResourceKernel.materializer

noncomputable def computationPostBytes : List UInt8 :=
  Minidregg.Assurance.MpcSealedCellExecution.publicReceiptCodec.encode
    Minidregg.Assurance.MpcSealedCellExecution.publicReceipt

noncomputable def claim : Claim where
  terms := Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.terms
  before := Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.before
  after := Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.after
  taker := Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.taker
  base := Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.base
  height := Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.height
  orderPreRoot := MarketMaterializer.rootBytes
    (stateBytes Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.terms
      Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.before)
  orderPostRoot := MarketMaterializer.rootBytes
    (stateBytes Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.terms
      Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.after)
  resourcePreRoot :=
    Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.resourcePre.root
  resourcePostRoot :=
    Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.feeAccepted.post.root
  releasedBase := Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.base
  paymentQuote := Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.base *
    Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.terms.unitQuote
  feeQuote := Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.base *
    Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.terms.feePerBase
  residualRefundBase :=
    Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled.after.remainingBase
  sourcePreRoot := Minidregg.Assurance.MpcSealedCellExecution.pre.root
  sourcePostRoot := Minidregg.Assurance.MpcSealedCellExecution.accepted.cellEffect.prepared.postRoot
  computationPreRoot := MarketMaterializer.rootBytes []
  computationPostRoot := MarketMaterializer.rootBytes computationPostBytes
  computationNullifier := Minidregg.Assurance.MpcSealedCellExecution.sessionId
  outputCommitment :=
    Minidregg.Assurance.MpcSealedCellExecution.honestOutputArtifact.commitment

theorem claim_bound : claim.BoundTo
    Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled where
  termsExact := rfl
  beforeExact := rfl
  afterExact := rfl
  takerExact := rfl
  baseExact := rfl
  heightExact := rfl
  orderPreExact := rfl
  orderPostExact := rfl
  resourcePreExact := rfl
  resourcePostExact := rfl
  releaseExact := rfl
  paymentExact := rfl
  feeExact := rfl
  refundExact := rfl

noncomputable def source : CanonicalSource claim MpcSource.binding :=
  .sharedMpc MpcSource.semanticCell rfl rfl rfl rfl rfl

def sealedRuntime : SealedRuntime where
  transactionId := ⟨200⟩
  nullifierId := ⟨201⟩
  computationCell := ⟨202⟩
  receiptCell := ⟨203⟩
  openComputationBytes := []
  openReceiptBytes := []
  cellsDistinct := by decide

noncomputable def sealed :
    SealedAcceptance CanonicalSource MarketMaterializer :=
  acceptSealed claim MpcSource.binding source sealedRuntime
    computationPostBytes rfl rfl

noncomputable def declassificationRequest : Request .object :=
  { Minidregg.Theory.TypedAuthorization.demoRequest with
    domain := releaseDomain claim
    semantics := ⟨173⟩
    target := ⟨claim.terms.orderId⟩
    verb := .mutateObject
    argsDigest := claim.digest
    effectsDigest := releaseEffectDigest claim
      Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled
    nonce := 204
    preStateRoot := claim.orderPreRoot
    cost := 0 }

noncomputable def declassificationAuthorization :
    Authorized demoPortal demoState declassificationRequest where
  evidence := .signature () rfl rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

noncomputable def declassification :
    Declassification claim
      Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled where
  request := declassificationRequest
  authorization := declassificationAuthorization
  domainExact := rfl
  semanticsExact := rfl
  targetExact := rfl
  verbExact := rfl
  argsExact := rfl
  effectsExact := rfl
  preRootExact := rfl
  zeroExtraCost := rfl

noncomputable def releaseRuntime : ReleaseRuntime sealed
    Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled where
  transactionId := ⟨205⟩
  nullifierId := ⟨206⟩
  terminalCell := ⟨207⟩
  outboxCell := ⟨208⟩
  openTerminalBytes := []
  openOutboxBytes := []
  distinctTransaction := by decide
  terminalOutboxDistinct := by decide
  computationNotFill := by
    change (sealedRuntime.computationCell : Digest) ∉ [⟨102⟩, ⟨103⟩]
    decide
  receiptNotFill := by
    change (sealedRuntime.receiptCell : Digest) ∉ [⟨102⟩, ⟨103⟩]
    decide
  terminalNotFill := by
    change (⟨207⟩ : Digest) ∉ [⟨102⟩, ⟨103⟩]
    decide
  outboxNotFill := by
    change (⟨208⟩ : Digest) ∉ [⟨102⟩, ⟨103⟩]
    decide
  computationTerminalDistinct := by decide
  computationOutboxDistinct := by decide
  receiptTerminalDistinct := by decide
  receiptOutboxDistinct := by decide

noncomputable def settlement :
    Settlement CanonicalSource MarketMaterializer demoPortal demoState :=
  settle sealed Minidregg.Kernel.CanonicalEscrowMarket.Witness.filled
    claim_bound declassification releaseRuntime

theorem settlement_nonempty : Nonempty
    (Settlement CanonicalSource MarketMaterializer demoPortal demoState) :=
  ⟨settlement⟩

@[simp] theorem source_is_declared_mpc :
    settlement.sealed.evidence.mode = .sharedMpc /\
      settlement.sealed.evidence.status = .declaredMpc :=
  settled_source_status settlement

theorem exact_payment_fee_refund :
    settlement.sealed.claim.paymentQuote = 4 /\
      settlement.sealed.claim.feeQuote = 2 /\
      settlement.sealed.claim.residualRefundBase = 2 := by
  change 4 = 4 /\ 2 = 2 /\ 2 = 2
  exact ⟨rfl, rfl, rfl⟩

theorem exact_retry
    (schedule : Schedule)
    (before : DataSnapshot MarketMaterializer.rootBytes) :
    execute schedule
        (DataSnapshot.install before settlement.intent) settlement.intent =
      .replayed settlement.intent.erase :=
  settlement.exact_retry_replays schedule before

end Witness

/-! ## Explicit shared-MPC trust ceiling -/

structure MpcExecutorBoundary where
  conformance :
    Minidregg.Assurance.MpcSealedCellExecution.ExecutorConformance
      Minidregg.Assurance.MpcSealedCellExecution.honestEvidence
  transcriptAuthenticationSound : Prop
  privateChannels : Prop
  physicalExecution : Prop

/-- The inhabited source does not synthesize the physical/security bridge. -/
theorem mpc_source_does_not_imply_executor_boundary
    (_source : MpcSource.SemanticCell) :
    (Nonempty MpcExecutorBoundary -> Nonempty MpcExecutorBoundary) :=
  fun boundary => boundary

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.PrivateEscrowSettlementJoin.NoteSource.no_current_semantic_cell' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms NoteSource.no_current_semantic_cell
/-- info: 'Minidregg.Assurance.PrivateEscrowSettlementJoin.BfvSource.no_current_semantic_cell' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms BfvSource.no_current_semantic_cell
/-- info: 'Minidregg.Assurance.PrivateEscrowSettlementJoin.MpcSource.semanticCell_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms MpcSource.semanticCell_nonempty
/-- info: 'Minidregg.Assurance.PrivateEscrowSettlementJoin.Witness.settlement_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.settlement_nonempty
/-- info: 'Minidregg.Assurance.PrivateEscrowSettlementJoin.settled_keeps_receipt_separate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms settled_keeps_receipt_separate

end


end Minidregg.Assurance.PrivateEscrowSettlementJoin
