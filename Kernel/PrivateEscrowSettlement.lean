/-
# Kernel.PrivateEscrowSettlement -- sealed private work before public escrow release

This module is the first-order kernel seam for a private market order.  It does
not verify a note proof, a BFV proof, or an MPC transcript.  Instead it is
parameterized by an indexed `Source` supplied by an assurance module.  The
kernel then makes two transitions impossible to confuse:

1. `SealedAcceptance.intent` installs only a sealed computation post and its
   exact proof/semantic receipt.  It cannot move an escrow balance or publish a
   private result.
2. `Settlement.intent` is a later, separately authorized mutation.  It reuses
   the exact `CanonicalEscrowMarket.Fill`, guards the retained sealed receipt
   and computation roots, and atomically adds a release terminal and outbox.

The public fill remains the sole source of the base release, quote payment,
collector fee, resource charge, order roots, and fill nullifier.  A residual
base refund is recorded exactly but is not performed by settlement: the
existing `CanonicalEscrowMarket.Refund` requires a close plus fresh resource
authorization.  Exact retry is free and transaction re-keying cannot bypass
the stable release nullifier.

Proof status is first-order data with a load-bearing law.  A semantic proof
status requires a nonzero suite identity (and, for BFV, nonzero codec and
controller identities).  The shared-MPC status is explicitly non-cryptographic
and requires zero proof pins plus nonzero protocol/federation names.  Thus the
current zero-pinned NoteSpend and BFV statements cannot be relabeled as
semantic proof receipts.

All durability below is logical `DurableDataIntent` atomicity.  Hash/root
collision resistance, proof security, MPC authentication/executor conformance,
physical storage, outbox delivery, external finality, and client cutover remain
explicit refinement boundaries.
-/
import Kernel.CanonicalEscrowMarket

namespace Minidregg.Kernel.PrivateEscrowSettlement

open Minidregg.Kernel.CanonicalEscrowMarket
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## Honest proof-status vocabulary -/

inductive PrivateMode
  | noteSpend
  | bfv
  | sharedMpc
  deriving DecidableEq, Repr

def PrivateMode.tag : PrivateMode -> Nat
  | .noteSpend => 1
  | .bfv => 2
  | .sharedMpc => 3

inductive ProofStatus
  | unassigned
  | semanticProof
  | declaredMpc
  deriving DecidableEq, Repr

def ProofStatus.tag : ProofStatus -> Nat
  | .unassigned => 0
  | .semanticProof => 1
  | .declaredMpc => 2

structure ProofPins where
  proofCodecId : Digest
  proofSuiteId : Digest
  controllerDigest : Digest
  deriving DecidableEq, Repr

def ProofPins.zero : ProofPins := ⟨⟨0⟩, ⟨0⟩, ⟨0⟩⟩

def ProofPins.SemanticallyAssigned (mode : PrivateMode)
    (pins : ProofPins) : Prop :=
  pins.proofSuiteId ≠ ⟨0⟩ /\
    (mode = .bfv ->
      pins.proofCodecId ≠ ⟨0⟩ /\ pins.controllerDigest ≠ ⟨0⟩)

/-- The status law is proof relevant.  It prevents a zero identifier from
being described as a deployed semantic proof suite.  Shared MPC is a separate
honest semantic path, not a proof-suite alias. -/
structure EvidenceBinding where
  mode : PrivateMode
  status : ProofStatus
  pins : ProofPins
  protocolId : Digest
  federationId : Digest
  semanticAssigned : status = .semanticProof ->
    pins.SemanticallyAssigned mode
  mpcShape : status = .declaredMpc ->
    mode = .sharedMpc /\ pins = .zero /\
      protocolId ≠ ⟨0⟩ /\ federationId ≠ ⟨0⟩

def EvidenceBinding.Acceptable (binding : EvidenceBinding) : Prop :=
  binding.status = .semanticProof \/ binding.status = .declaredMpc

theorem zero_suite_cannot_be_semantic
    (binding : EvidenceBinding)
    (zeroSuite : binding.pins.proofSuiteId = ⟨0⟩) :
    binding.status ≠ .semanticProof := by
  intro semantic
  exact (binding.semanticAssigned semantic).1 zeroSuite

theorem note_or_bfv_zero_suite_not_acceptable
    (binding : EvidenceBinding)
    (mode : binding.mode = .noteSpend \/ binding.mode = .bfv)
    (zeroPins : binding.pins = .zero) :
    Not binding.Acceptable := by
  intro acceptable
  rcases acceptable with semantic | mpc
  · exact (zero_suite_cannot_be_semantic binding (by
      simpa [zeroPins, ProofPins.zero])) semantic
  · have shared := (binding.mpcShape mpc).1
    rcases mode with note | bfv <;> simp_all

/-! ## Exact private fill statement -/

/-- The receipt commits both sides of the private computation and every public
economic quantity.  `BoundTo` below, rather than a caller-authored flag, joins
these fields to the canonical authorized fill. -/
structure Claim where
  terms : Terms
  before : State
  after : State
  taker : AccountId
  base : Nat
  height : Nat
  orderPreRoot : Digest
  orderPostRoot : Digest
  resourcePreRoot : Digest
  resourcePostRoot : Digest
  releasedBase : Nat
  paymentQuote : Nat
  feeQuote : Nat
  residualRefundBase : Nat
  sourcePreRoot : Digest
  sourcePostRoot : Digest
  computationPreRoot : Digest
  computationPostRoot : Digest
  computationNullifier : Digest
  outputCommitment : Digest
  deriving DecidableEq, Repr

def Claim.canonicalBytes (claim : Claim) : List UInt8 :=
  CanonicalEscrowMarket.encodeNat claim.terms.code ++
    CanonicalEscrowMarket.encodeNat claim.before.code ++
    CanonicalEscrowMarket.encodeNat claim.after.code ++
    CanonicalEscrowMarket.encodeNat claim.taker ++
    CanonicalEscrowMarket.encodeNat claim.base ++
    CanonicalEscrowMarket.encodeNat claim.height ++
    CanonicalEscrowMarket.encodeNat claim.orderPreRoot.value ++
    CanonicalEscrowMarket.encodeNat claim.orderPostRoot.value ++
    CanonicalEscrowMarket.encodeNat claim.resourcePreRoot.value ++
    CanonicalEscrowMarket.encodeNat claim.resourcePostRoot.value ++
    CanonicalEscrowMarket.encodeNat claim.releasedBase ++
    CanonicalEscrowMarket.encodeNat claim.paymentQuote ++
    CanonicalEscrowMarket.encodeNat claim.feeQuote ++
    CanonicalEscrowMarket.encodeNat claim.residualRefundBase ++
    CanonicalEscrowMarket.encodeNat claim.sourcePreRoot.value ++
    CanonicalEscrowMarket.encodeNat claim.sourcePostRoot.value ++
    CanonicalEscrowMarket.encodeNat claim.computationPreRoot.value ++
    CanonicalEscrowMarket.encodeNat claim.computationPostRoot.value ++
    CanonicalEscrowMarket.encodeNat claim.computationNullifier.value ++
    CanonicalEscrowMarket.encodeNat claim.outputCommitment.value

def Claim.digest (claim : Claim) : Digest :=
  ⟨Nat.pair claim.terms.code
    (Nat.pair claim.before.code
      (Nat.pair claim.after.code
        (Nat.pair claim.sourcePostRoot.value
          (Nat.pair claim.computationPostRoot.value
            (Nat.pair claim.computationNullifier.value
              claim.outputCommitment.value)))))⟩

/-- Load-bearing equality between private receipt data and the already
authorized public fill.  In particular, the post-resource root is after all
three public operations, not merely after escrow release. -/
structure Claim.BoundTo
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (claim : Claim) (fill : Fill M portal authState) : Prop where
  termsExact : claim.terms = fill.terms
  beforeExact : claim.before = fill.before
  afterExact : claim.after = fill.after
  takerExact : claim.taker = fill.taker
  baseExact : claim.base = fill.base
  heightExact : claim.height = fill.height
  orderPreExact : claim.orderPreRoot =
    M.rootBytes (stateBytes fill.terms fill.before)
  orderPostExact : claim.orderPostRoot =
    M.rootBytes (stateBytes fill.terms fill.after)
  resourcePreExact : claim.resourcePreRoot = fill.resourcePre.root
  resourcePostExact : claim.resourcePostRoot = fill.feeAccepted.post.root
  releaseExact : claim.releasedBase = fill.base
  paymentExact : claim.paymentQuote = fill.base * fill.terms.unitQuote
  feeExact : claim.feeQuote = fill.base * fill.terms.feePerBase
  refundExact : claim.residualRefundBase = fill.after.remainingBase

namespace Claim.BoundTo

variable {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    {claim : Claim} {fill : Fill M portal authState}

theorem exact_economics (bound : claim.BoundTo fill) :
    claim.releasedBase = fill.base /\
      claim.paymentQuote = fill.base * fill.terms.unitQuote /\
      claim.feeQuote = fill.base * fill.terms.feePerBase /\
      claim.residualRefundBase = fill.after.remainingBase :=
  ⟨bound.releaseExact, bound.paymentExact, bound.feeExact, bound.refundExact⟩

theorem complete_has_zero_refund
    (bound : claim.BoundTo fill) (complete : fill.after.phase = .filled) :
    claim.residualRefundBase = 0 := by
  rw [bound.refundExact]
  have valid := fill.after_valid
  have phaseValid := valid.2
  rw [complete] at phaseValid
  exact phaseValid.2

end Claim.BoundTo

/-! ## First transition: retain only a sealed computation and receipt -/

def EvidenceBinding.canonicalBytes (binding : EvidenceBinding) : List UInt8 :=
  CanonicalEscrowMarket.encodeNat binding.mode.tag ++
    CanonicalEscrowMarket.encodeNat binding.status.tag ++
    CanonicalEscrowMarket.encodeNat binding.pins.proofCodecId.value ++
    CanonicalEscrowMarket.encodeNat binding.pins.proofSuiteId.value ++
    CanonicalEscrowMarket.encodeNat binding.pins.controllerDigest.value ++
    CanonicalEscrowMarket.encodeNat binding.protocolId.value ++
    CanonicalEscrowMarket.encodeNat binding.federationId.value

structure SealedRuntime where
  transactionId : TransactionId
  nullifierId : Digest
  computationCell : CellId
  receiptCell : CellId
  openComputationBytes : List UInt8
  openReceiptBytes : List UInt8
  cellsDistinct : computationCell ≠ receiptCell

/-- `Source` is indexed by both the exact claim and exact evidence binding.
An assurance layer can therefore expose only constructors backed by a real
accepted NoteSpend/BFV/MPC effect. -/
structure SealedAcceptance
    (Source : Claim -> EvidenceBinding -> Type)
    (M : CellState.Materializer CanonicalResourceKernel.schema Digest) where
  claim : Claim
  evidence : EvidenceBinding
  acceptable : evidence.Acceptable
  source : Source claim evidence
  runtime : SealedRuntime
  computationPostBytes : List UInt8
  computationPreBound :
    M.rootBytes runtime.openComputationBytes = claim.computationPreRoot
  computationPostBound :
    M.rootBytes computationPostBytes = claim.computationPostRoot

namespace SealedAcceptance

variable {Source : Claim -> EvidenceBinding -> Type}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}

def receiptBytes (accepted : SealedAcceptance Source M) : List UInt8 :=
  [171] ++ accepted.claim.canonicalBytes ++
    accepted.evidence.canonicalBytes

def nullifier (accepted : SealedAcceptance Source M) : StableNullifier where
  codecVersion := 1
  domain := accepted.claim.digest
  nullifierId := accepted.runtime.nullifierId
  canonicalBytes := accepted.claim.canonicalBytes ++
    CanonicalEscrowMarket.encodeNat accepted.claim.computationNullifier.value

def event (accepted : SealedAcceptance Source M) : StableEvent where
  codecVersion := 1
  domain := accepted.claim.digest
  eventId := ⟨Nat.pair accepted.claim.computationPostRoot.value
    accepted.claim.outputCommitment.value⟩
  canonicalBytes := [172] ++ accepted.receiptBytes

def computationWrite (accepted : SealedAcceptance Source M) : DataWrite where
  cellId := accepted.runtime.computationCell
  expectedPre := accepted.claim.computationPreRoot
  exactPost := accepted.claim.computationPostRoot
  canonicalPostBytes := accepted.computationPostBytes

def receiptWrite (accepted : SealedAcceptance Source M) : DataWrite where
  cellId := accepted.runtime.receiptCell
  expectedPre := M.rootBytes accepted.runtime.openReceiptBytes
  exactPost := M.rootBytes accepted.receiptBytes
  canonicalPostBytes := accepted.receiptBytes

def intent (accepted : SealedAcceptance Source M) : DataIntent M.rootBytes where
  transactionId := accepted.runtime.transactionId
  writes := [accepted.computationWrite, accepted.receiptWrite]
  readGuards := []
  nullifiers := [accepted.nullifier]
  exactCharge := 0
  event := accepted.event
  postRootsBound := by
    intro write member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · exact accepted.computationPostBound
    · rfl
  guardsReadOnly := by simp

@[simp] theorem intent_writes (accepted : SealedAcceptance Source M) :
    accepted.intent.writes =
      [accepted.computationWrite, accepted.receiptWrite] := rfl

@[simp] theorem no_public_charge (accepted : SealedAcceptance Source M) :
    accepted.intent.exactCharge = 0 := rfl

@[simp] theorem exact_retry_replays (accepted : SealedAcceptance Source M)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before accepted.intent) accepted.intent =
      .replayed accepted.intent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install, Snapshot.install,
    Snapshot.lookupRecorded, Intent.sameCheck_self]

end SealedAcceptance

/-! ## Second transition: separately authorized release/declassification -/

def releaseDomain (claim : Claim) : Digest :=
  ⟨Nat.pair 173 claim.digest.value⟩

def releaseEffectDigest
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (claim : Claim) (fill : Fill M portal authState) : Digest :=
  ⟨Nat.pair claim.digest.value fill.event.eventId.value⟩

/-- This token is additional to the three resource authorizations inside
`Fill`.  Its zero cost prevents the disclosure gate from silently duplicating
the already exact public resource charge. -/
structure Declassification
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (claim : Claim) (fill : Fill M portal authState) where
  request : Request .object
  authorization : Authorized portal authState request
  domainExact : request.domain = releaseDomain claim
  semanticsExact : request.semantics = ⟨173⟩
  targetExact : request.target.value = claim.terms.orderId
  verbExact : request.verb = .mutateObject
  argsExact : request.argsDigest = claim.digest
  effectsExact : request.effectsDigest = releaseEffectDigest claim fill
  preRootExact : request.preStateRoot = claim.orderPreRoot
  zeroExtraCost : request.cost = 0

structure ReleaseRuntime
    {Source : Claim -> EvidenceBinding -> Type}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (sealed : SealedAcceptance Source M) (fill : Fill M portal authState) where
  transactionId : TransactionId
  nullifierId : Digest
  terminalCell : CellId
  outboxCell : CellId
  openTerminalBytes : List UInt8
  openOutboxBytes : List UInt8
  distinctTransaction : transactionId ≠ sealed.runtime.transactionId
  terminalOutboxDistinct : terminalCell ≠ outboxCell
  computationNotFill : sealed.runtime.computationCell ∉
    fill.intent.writes.map DataWrite.cellId
  receiptNotFill : sealed.runtime.receiptCell ∉
    fill.intent.writes.map DataWrite.cellId
  terminalNotFill : terminalCell ∉ fill.intent.writes.map DataWrite.cellId
  outboxNotFill : outboxCell ∉ fill.intent.writes.map DataWrite.cellId
  computationTerminalDistinct : sealed.runtime.computationCell ≠ terminalCell
  computationOutboxDistinct : sealed.runtime.computationCell ≠ outboxCell
  receiptTerminalDistinct : sealed.runtime.receiptCell ≠ terminalCell
  receiptOutboxDistinct : sealed.runtime.receiptCell ≠ outboxCell

structure Settlement
    (Source : Claim -> EvidenceBinding -> Type)
    (M : CellState.Materializer CanonicalResourceKernel.schema Digest)
    (portal : Portal) (authState : AuthState) where
  sealed : SealedAcceptance Source M
  fill : Fill M portal authState
  claimBound : sealed.claim.BoundTo fill
  declassification : Declassification sealed.claim fill
  runtime : ReleaseRuntime sealed fill

namespace Settlement

variable {Source : Claim -> EvidenceBinding -> Type}
    {M : CellState.Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}

def receiptGuard (settlement : Settlement Source M portal authState) : ReadGuard where
  cellId := settlement.sealed.runtime.receiptCell
  expectedRoot := M.rootBytes settlement.sealed.receiptBytes

def computationGuard
    (settlement : Settlement Source M portal authState) : ReadGuard where
  cellId := settlement.sealed.runtime.computationCell
  expectedRoot := settlement.sealed.claim.computationPostRoot

def outboxBytes (settlement : Settlement Source M portal authState) : List UInt8 :=
  [174] ++ settlement.sealed.claim.canonicalBytes ++
    settlement.sealed.evidence.canonicalBytes ++
    CanonicalEscrowMarket.encodeNat settlement.fill.event.eventId.value

def terminalBytes (settlement : Settlement Source M portal authState) : List UInt8 :=
  [175] ++ settlement.sealed.claim.canonicalBytes ++
    CanonicalEscrowMarket.encodeNat
      (M.rootBytes settlement.sealed.receiptBytes).value ++
    CanonicalEscrowMarket.encodeNat (M.rootBytes settlement.outboxBytes).value

def terminalWrite (settlement : Settlement Source M portal authState) : DataWrite where
  cellId := settlement.runtime.terminalCell
  expectedPre := M.rootBytes settlement.runtime.openTerminalBytes
  exactPost := M.rootBytes settlement.terminalBytes
  canonicalPostBytes := settlement.terminalBytes

def outboxWrite (settlement : Settlement Source M portal authState) : DataWrite where
  cellId := settlement.runtime.outboxCell
  expectedPre := M.rootBytes settlement.runtime.openOutboxBytes
  exactPost := M.rootBytes settlement.outboxBytes
  canonicalPostBytes := settlement.outboxBytes

def nullifier (settlement : Settlement Source M portal authState) : StableNullifier where
  codecVersion := settlement.fill.manifest.version
  domain := releaseDomain settlement.sealed.claim
  nullifierId := settlement.runtime.nullifierId
  canonicalBytes := settlement.sealed.claim.canonicalBytes ++
    CanonicalEscrowMarket.encodeNat
      settlement.declassification.request.nonce

def event (settlement : Settlement Source M portal authState) : StableEvent where
  codecVersion := settlement.fill.manifest.version
  domain := releaseDomain settlement.sealed.claim
  eventId := releaseEffectDigest settlement.sealed.claim settlement.fill
  canonicalBytes := [176] ++ settlement.terminalBytes ++ settlement.outboxBytes

/-- The canonical public fill is retained byte-for-byte, then the terminal and
outbox are appended.  The two private artifacts are read guards, never release
writes. -/
def intent (settlement : Settlement Source M portal authState) :
    DataIntent M.rootBytes where
  transactionId := settlement.runtime.transactionId
  writes := settlement.fill.intent.writes ++
    [settlement.terminalWrite, settlement.outboxWrite]
  readGuards := [settlement.receiptGuard, settlement.computationGuard]
  nullifiers := settlement.fill.intent.nullifiers ++ [settlement.nullifier]
  exactCharge := settlement.fill.intent.exactCharge
  event := settlement.event
  postRootsBound := by
    intro write member
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with inFill | rfl | rfl
    · exact settlement.fill.intent.postRootsBound write inFill
    · rfl
    · rfl
  guardsReadOnly := by
    intro guard member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    · simp only [receiptGuard, List.map_append, List.mem_append, not_or]
      constructor
      · exact settlement.runtime.receiptNotFill
      · simp [terminalWrite, outboxWrite,
          settlement.runtime.receiptTerminalDistinct,
          settlement.runtime.receiptOutboxDistinct]
    · simp only [computationGuard, List.map_append, List.mem_append, not_or]
      constructor
      · exact settlement.runtime.computationNotFill
      · simp [terminalWrite, outboxWrite,
          settlement.runtime.computationTerminalDistinct,
          settlement.runtime.computationOutboxDistinct]

@[simp] theorem intent_writes
    (settlement : Settlement Source M portal authState) :
    settlement.intent.writes = settlement.fill.intent.writes ++
      [settlement.terminalWrite, settlement.outboxWrite] := rfl

@[simp] theorem intent_read_guards
    (settlement : Settlement Source M portal authState) :
    settlement.intent.readGuards =
      [settlement.receiptGuard, settlement.computationGuard] := rfl

@[simp] theorem exact_public_charge
    (settlement : Settlement Source M portal authState) :
    settlement.intent.exactCharge = settlement.fill.charge :=
  settlement.fill.exact_charge

theorem exact_economics
    (settlement : Settlement Source M portal authState) :
    settlement.sealed.claim.releasedBase = settlement.fill.base /\
      settlement.sealed.claim.paymentQuote =
        settlement.fill.base * settlement.fill.terms.unitQuote /\
      settlement.sealed.claim.feeQuote =
        settlement.fill.base * settlement.fill.terms.feePerBase /\
      settlement.sealed.claim.residualRefundBase =
        settlement.fill.after.remainingBase :=
  settlement.claimBound.exact_economics

/-- Settlement never performs the residual refund.  It remains the exact
amount that a later `Close`/`Refund` path may move under fresh authorization. -/
theorem residual_refund_is_deferred
    (settlement : Settlement Source M portal authState) :
    settlement.sealed.claim.residualRefundBase =
      settlement.fill.after.remainingBase /\
      CanonicalEscrowMarket.Terms.refundOperation settlement.fill.terms
          settlement.sealed.claim.residualRefundBase =
        .transfer settlement.fill.terms.escrow settlement.fill.terms.maker
          settlement.fill.terms.baseAsset settlement.fill.after.remainingBase := by
  constructor
  · exact settlement.claimBound.refundExact
  · simp [Terms.refundOperation, settlement.claimBound.refundExact]

theorem public_order_roots_exact
    (settlement : Settlement Source M portal authState) :
    settlement.sealed.claim.orderPreRoot =
        M.rootBytes (stateBytes settlement.fill.terms settlement.fill.before) /\
      settlement.sealed.claim.orderPostRoot =
        M.rootBytes (stateBytes settlement.fill.terms settlement.fill.after) :=
  ⟨settlement.claimBound.orderPreExact,
    settlement.claimBound.orderPostExact⟩

theorem declassification_is_separate_authority
    (settlement : Settlement Source M portal authState) :
    Nonempty (Authorized portal authState settlement.declassification.request) /\
      settlement.declassification.request.cost = 0 /\
      settlement.declassification.request.effectsDigest =
        releaseEffectDigest settlement.sealed.claim settlement.fill :=
  ⟨⟨settlement.declassification.authorization⟩,
    settlement.declassification.zeroExtraCost,
    settlement.declassification.effectsExact⟩

@[simp] theorem exact_retry_replays
    (settlement : Settlement Source M portal authState)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before settlement.intent) settlement.intent =
      .replayed settlement.intent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install, Snapshot.install,
    Snapshot.lookupRecorded, Intent.sameCheck_self]

def rekey (settlement : Settlement Source M portal authState)
    (transactionId : TransactionId) : DataIntent M.rootBytes :=
  { settlement.intent with transactionId := transactionId }

@[simp] theorem installed_rekey_nullifier_not_fresh
    (settlement : Settlement Source M portal authState)
    (transactionId : TransactionId) (before : DataSnapshot M.rootBytes) :
    (settlement.rekey transactionId).erase.nullifiersFreshCheck
      (DataSnapshot.install before settlement.intent).model = false := by
  simp [rekey, intent, nullifier,
    DurableCommitProtocol.Intent.nullifiersFreshCheck,
    DataSnapshot.install, Snapshot.install]

theorem atomic_public_terminal_outbox
    (settlement : Settlement Source M portal authState)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    (DurableDataIntent.execute schedule before settlement.intent).storeAfter before = before \/
      (DurableDataIntent.execute schedule before settlement.intent).storeAfter before =
        DataSnapshot.install before settlement.intent :=
  DurableDataIntent.execute_no_partial_data_commit schedule before settlement.intent

/-- Physical durability and transport enter only through an implementation
refinement.  The logical settlement itself supplies no such witness. -/
theorem physical_step_atomic
    (settlement : Settlement Source M portal authState)
    {PhysicalState : Type} {PhysicalStep :
      PhysicalState -> DataIntent M.rootBytes -> PhysicalState -> Type}
    {Represents : PhysicalState -> DataSnapshot M.rootBytes -> Prop}
    (refinement : ImplementationRefinement
      M.rootBytes PhysicalState PhysicalStep Represents)
    {physicalBefore physicalAfter : PhysicalState}
    {modelBefore : DataSnapshot M.rootBytes}
    (represented : Represents physicalBefore modelBefore)
    (stepped : PhysicalStep physicalBefore settlement.intent physicalAfter) :
    exists modelAfter,
      Represents physicalAfter modelAfter /\
      (modelAfter = modelBefore \/
        modelAfter = DataSnapshot.install modelBefore settlement.intent) /\
      (forall cellId, M.rootBytes (modelAfter.canonicalBytes cellId) =
        modelAfter.model.roots cellId) :=
  DurableDataIntent.physical_step_no_partial_data_commit
    refinement represented stepped

end Settlement

/-! ## Axiom audit -/

/-- info: 'Minidregg.Kernel.PrivateEscrowSettlement.zero_suite_cannot_be_semantic' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms zero_suite_cannot_be_semantic
/-- info: 'Minidregg.Kernel.PrivateEscrowSettlement.note_or_bfv_zero_suite_not_acceptable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms note_or_bfv_zero_suite_not_acceptable
/-- info: 'Minidregg.Kernel.PrivateEscrowSettlement.Settlement.exact_economics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Settlement.exact_economics
/-- info: 'Minidregg.Kernel.PrivateEscrowSettlement.Settlement.installed_rekey_nullifier_not_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Settlement.installed_rekey_nullifier_not_fresh

end

end Minidregg.Kernel.PrivateEscrowSettlement
