/-
# Kernel.CanonicalEscrowMarket -- authorized public order settlement

This module joins a public maker order to the canonical resource kernel without
inventing a second balance algebra.  A deposit is one accepted transfer into an
escrow account.  A fill is the exact atomic sequence

* escrow releases base asset to the taker;
* taker pays the maker in quote asset;
* taker pays the declared collector fee.

Every leg is independently indexed by `AuthorizedResourceCharge`: the signed
request contains the exact canonical operation, tariff-derived ten-lane charge,
and a market domain committing the complete order, prior state, and action.
The durable fill installs the final canonical book and order state together,
charges exactly the pointwise sum of those authorized legs, and consumes one
stable fill nullifier.  Exact retry is free; changing the transaction id cannot
bypass that nullifier.

Cancellation and expiry settle only the order state.  Residual escrow is never
released by a terminal tag: it requires a fresh accepted transfer and fresh
resource authorization.  Private-note validity, an external price/oracle,
provider finality, wall-clock truth, root collision resistance, and native
codec correctness remain explicit refinement boundaries.  This public kernel
does not depend on any unfinished private-note suite.
-/
import Kernel.AuthorizedResourceCharge

namespace Minidregg.Kernel.CanonicalEscrowMarket

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

local instance schemaFieldDecidableEq :
    DecidableEq CanonicalResourceKernel.schema.Field := by
  change DecidableEq CanonicalResourceKernel.Field
  infer_instance

local instance schemaResourceDecidableEq :
    DecidableEq CanonicalResourceKernel.schema.Resource := by
  change DecidableEq Empty
  infer_instance

/-! ## Canonical order terms and state -/

structure Terms where
  orderId : Nat
  maker : AccountId
  escrow : AccountId
  baseAsset : AssetId
  quoteAsset : AssetId
  baseQuantity : Nat
  unitQuote : Nat
  feeCollector : AccountId
  feePerBase : Nat
  opensAt : Nat
  expiresAt : Nat
  deriving DecidableEq, Repr

structure Terms.WellFormed (terms : Terms) : Prop where
  positiveQuantity : 0 < terms.baseQuantity
  positiveQuote : 0 < terms.unitQuote
  marketWindow : terms.opensAt < terms.expiresAt
  makerEscrowDistinct : terms.maker ≠ terms.escrow
  baseQuoteDistinct : terms.baseAsset ≠ terms.quoteAsset

def Terms.depositOperation (terms : Terms) : Operation :=
  .transfer terms.maker terms.escrow terms.baseAsset terms.baseQuantity

def Terms.releaseOperation (terms : Terms) (taker : AccountId) (base : Nat) : Operation :=
  .transfer terms.escrow taker terms.baseAsset base

def Terms.paymentOperation (terms : Terms) (taker : AccountId) (base : Nat) : Operation :=
  .transfer taker terms.maker terms.quoteAsset (base * terms.unitQuote)

def Terms.feeOperation (terms : Terms) (taker : AccountId) (base : Nat) : Operation :=
  .fee taker terms.feeCollector terms.quoteAsset (base * terms.feePerBase)

def Terms.refundOperation (terms : Terms) (remaining : Nat) : Operation :=
  .transfer terms.escrow terms.maker terms.baseAsset remaining

inductive Phase
  | liveOpen
  | livePartial
  | filled
  | cancelled
  | expired
  deriving DecidableEq, Repr

def Phase.tag : Phase -> Nat
  | .liveOpen => 0
  | .livePartial => 1
  | .filled => 2
  | .cancelled => 3
  | .expired => 4

structure State where
  filledBase : Nat
  remainingBase : Nat
  phase : Phase
  deriving DecidableEq, Repr

def State.Valid (terms : Terms) (state : State) : Prop :=
  state.filledBase + state.remainingBase = terms.baseQuantity /\
    match state.phase with
    | .liveOpen => state.filledBase = 0 /\ state.remainingBase = terms.baseQuantity
    | .livePartial => 0 < state.filledBase /\ 0 < state.remainingBase
    | .filled => state.filledBase = terms.baseQuantity /\ state.remainingBase = 0
    | .cancelled => 0 < state.remainingBase
    | .expired => 0 < state.remainingBase

def State.opened (terms : Terms) : State where
  filledBase := 0
  remainingBase := terms.baseQuantity
  phase := .liveOpen

@[simp] theorem State.opened_valid (terms : Terms) :
    (State.opened terms).Valid terms := by
  simp [State.opened, State.Valid]

def State.Live (state : State) : Prop :=
  state.phase = .liveOpen \/ state.phase = .livePartial

structure FillAllowed (terms : Terms) (before : State)
    (base height : Nat) : Prop where
  live : before.Live
  positive : 0 < base
  withinEscrow : base <= before.remainingBase
  opened : terms.opensAt <= height
  beforeExpiry : height <= terms.expiresAt

def State.afterFill (before : State) (base : Nat) : State where
  filledBase := before.filledBase + base
  remainingBase := before.remainingBase - base
  phase := if base = before.remainingBase then .filled else .livePartial

theorem State.afterFill_valid
    {terms : Terms} {before : State} {base height : Nat}
    (valid : before.Valid terms) (allowed : FillAllowed terms before base height) :
    (before.afterFill base).Valid terms := by
  rcases valid with ⟨total, _phaseValid⟩
  have within := allowed.withinEscrow
  have positive := allowed.positive
  simp only [State.afterFill, State.Valid]
  constructor
  · omega
  · by_cases complete : base = before.remainingBase
    · simp [complete]
      omega
    · simp [complete]
      omega

@[simp] theorem State.afterFill_complete_iff
    (before : State) (base : Nat) :
    (before.afterFill base).phase = .filled <-> base = before.remainingBase := by
  simp [State.afterFill]

theorem State.afterFill_partial_of_strict
    {before : State} {base : Nat} (strict : base < before.remainingBase) :
    (before.afterFill base).phase = .livePartial := by
  simp [State.afterFill, Nat.ne_of_lt strict]

theorem overfill_has_no_admission
    {terms : Terms} {before : State} {base height : Nat}
    (tooMuch : before.remainingBase < base) :
    Not (FillAllowed terms before base height) := by
  intro allowed
  exact (Nat.not_le_of_gt tooMuch) allowed.withinEscrow

def State.cancelled (before : State) : State := { before with phase := .cancelled }
def State.expired (before : State) : State := { before with phase := .expired }

def State.ReleaseDue (state : State) : Prop :=
  (state.phase = .cancelled \/ state.phase = .expired) /\ 0 < state.remainingBase

@[simp] theorem complete_has_no_release_due
    {state : State} (complete : state.phase = .filled) :
    Not state.ReleaseDue := by
  simp [State.ReleaseDue, complete]

/-! ## First-order commitments -/

def encodeNat (value : Nat) : List UInt8 :=
  List.replicate value 0 ++ [1]

def stateBytes (terms : Terms) (state : State) : List UInt8 :=
  encodeNat terms.orderId ++ encodeNat state.filledBase ++
    encodeNat state.remainingBase ++ encodeNat state.phase.tag

def Terms.code (terms : Terms) : Nat :=
  Nat.pair terms.orderId
    (Nat.pair terms.maker
      (Nat.pair terms.escrow
        (Nat.pair terms.baseAsset
          (Nat.pair terms.quoteAsset
            (Nat.pair terms.baseQuantity
              (Nat.pair terms.unitQuote
                (Nat.pair terms.feeCollector
                  (Nat.pair terms.feePerBase
                    (Nat.pair terms.opensAt terms.expiresAt)))))))))

def State.code (state : State) : Nat :=
  Nat.pair state.filledBase (Nat.pair state.remainingBase state.phase.tag)

inductive Action
  | deposit
  | fill (taker base height : Nat)
  | cancel (height : Nat)
  | expire (height : Nat)
  | refund (remaining : Nat)
  deriving DecidableEq, Repr

def Action.code : Action -> Nat
  | .deposit => Nat.pair 0 0
  | .fill taker base height => Nat.pair 1 (Nat.pair taker (Nat.pair base height))
  | .cancel height => Nat.pair 2 height
  | .expire height => Nat.pair 3 height
  | .refund remaining => Nat.pair 4 remaining

def actionDomain (manifest : AuthorizedResourceCharge.DeploymentManifest)
    (terms : Terms) (before : State) (action : Action) : Digest :=
  ⟨Nat.pair manifest.semanticDigest.value
    (Nat.pair terms.code (Nat.pair before.code action.code))⟩

def ContextBound
    (context : AuthorizedResourceCharge.RequestContext)
    (manifest : AuthorizedResourceCharge.DeploymentManifest)
    (terms : Terms) (before : State) (action : Action) : Prop :=
  context.domain = actionDomain manifest terms before action

/-! ## Maker escrow deposit -/

structure DepositRuntime where
  transactionId : TransactionId
  nullifierId : Digest
  resourceCell : CellId
  orderCell : CellId
  emptyOrderBytes : List UInt8
  cellsDistinct : resourceCell ≠ orderCell

structure Deposit
    (M : Materializer CanonicalResourceKernel.schema Digest)
    (portal : Portal) (authState : AuthState) (pre : Materialized M) where
  terms : Terms
  wellFormed : terms.WellFormed
  runtime : DepositRuntime
  manifest : AuthorizedResourceCharge.DeploymentManifest
  context : AuthorizedResourceCharge.RequestContext
  accepted : Accepted pre terms.depositOperation
  contextBound : ContextBound context manifest terms (State.opened terms) .deposit
  authorization : Authorized portal authState
    (context.request manifest accepted)

namespace Deposit

variable {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}

noncomputable def acceptedEffect (deposit : Deposit M portal authState pre) :=
  AuthorizedResourceCharge.toCellEffect deposit.manifest deposit.accepted
    deposit.context deposit.authorization

def nullifier (deposit : Deposit M portal authState pre) : StableNullifier where
  codecVersion := deposit.manifest.version
  domain := actionDomain deposit.manifest deposit.terms (State.opened deposit.terms) .deposit
  nullifierId := deposit.runtime.nullifierId
  canonicalBytes := encodeNat deposit.terms.orderId ++ encodeNat deposit.context.nonce

def event (deposit : Deposit M portal authState pre) : StableEvent where
  codecVersion := deposit.manifest.version
  domain := actionDomain deposit.manifest deposit.terms (State.opened deposit.terms) .deposit
  eventId :=
    ⟨Nat.pair (AuthorizedResourceCharge.chargedEffectDigest deposit.manifest pre
      deposit.terms.depositOperation).value deposit.terms.code⟩
  canonicalBytes :=
    CanonicalResourceEffect.operationCodec.encode deposit.terms.depositOperation ++
      stateBytes deposit.terms (State.opened deposit.terms)

def intent (deposit : Deposit M portal authState pre) : DataIntent M.rootBytes where
  transactionId := deposit.runtime.transactionId
  writes :=
    [{ cellId := deposit.runtime.resourceCell
       expectedPre := pre.root
       exactPost := deposit.accepted.post.root
       canonicalPostBytes := deposit.accepted.post.bytes },
     { cellId := deposit.runtime.orderCell
       expectedPre := M.rootBytes deposit.runtime.emptyOrderBytes
       exactPost := M.rootBytes (stateBytes deposit.terms (State.opened deposit.terms))
       canonicalPostBytes := stateBytes deposit.terms (State.opened deposit.terms) }]
  readGuards := []
  nullifiers := [deposit.nullifier]
  exactCharge := AuthorizedResourceCharge.exactCharge deposit.manifest deposit.accepted
  event := deposit.event
  postRootsBound := by
    intro write present
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at present
    rcases present with rfl | rfl <;> rfl
  guardsReadOnly := by simp

@[simp] theorem intent_exact_charge (deposit : Deposit M portal authState pre) :
    deposit.intent.exactCharge =
      AuthorizedResourceCharge.exactCharge deposit.manifest deposit.accepted := rfl

@[simp] theorem authorized_cost_is_durable_fee
    (deposit : Deposit M portal authState pre) :
    (deposit.context.request deposit.manifest deposit.accepted).cost =
      deposit.intent.exactCharge .feeDebit := rfl

theorem conserves (deposit : Deposit M portal authState pre) (asset : AssetId) :
    (logicalBook deposit.accepted.post.logical).totalAsset asset =
      (logicalBook pre.logical).totalAsset asset :=
  deposit.accepted.conserves asset

@[simp] theorem retry_replays (deposit : Deposit M portal authState pre)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before deposit.intent)
        deposit.intent = .replayed deposit.intent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install, Snapshot.install,
    Snapshot.lookupRecorded, Intent.sameCheck_self]

def rekey (deposit : Deposit M portal authState pre)
    (transactionId : TransactionId) : DataIntent M.rootBytes :=
  { deposit.intent with transactionId := transactionId }

@[simp] theorem rekey_transactionId (deposit : Deposit M portal authState pre)
    (transactionId : TransactionId) :
    (deposit.rekey transactionId).transactionId = transactionId := rfl

@[simp] theorem installed_rekey_nullifier_not_fresh
    (deposit : Deposit M portal authState pre) (transactionId : TransactionId)
    (before : DataSnapshot M.rootBytes) :
    (deposit.rekey transactionId).erase.nullifiersFreshCheck
      (DataSnapshot.install before deposit.intent).model = false := by
  simp [rekey, intent, nullifier, DurableCommitProtocol.Intent.nullifiersFreshCheck,
    DataSnapshot.install, Snapshot.install]

theorem installed_rekey_preflight_rejects
    (deposit : Deposit M portal authState pre) (transactionId : TransactionId)
    (before : DataSnapshot M.rootBytes) :
    (deposit.rekey transactionId).preflight
      (DataSnapshot.install before deposit.intent) ≠ .ok () := by
  simp [DataIntent.preflight, DurableCommitProtocol.Intent.preflight,
    rekey, intent, nullifier, DurableCommitProtocol.Intent.rootsMatchCheck,
    DurableCommitProtocol.Intent.nullifiersFreshCheck,
    DataSnapshot.install, Snapshot.install]
  split <;> simp_all
  all_goals aesop

theorem rekey_cannot_charge_twice
    (deposit : Deposit M portal authState pre) (transactionId : TransactionId)
    (different : transactionId ≠ deposit.runtime.transactionId)
    (before : DataSnapshot M.rootBytes)
    (newUnrecorded : Snapshot.lookupRecorded transactionId before.model.journal = none)
    (schedule : Schedule) (next : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before deposit.intent)
        (deposit.rekey transactionId) ≠ .accepted next := by
  have lookup : Snapshot.lookupRecorded transactionId
      (DataSnapshot.install before deposit.intent).model.journal = none := by
    have oldNe : deposit.intent.transactionId ≠ transactionId := by
      simpa [intent] using different.symm
    simp [DataSnapshot.install, Snapshot.install, Snapshot.lookupRecorded,
      oldNe, newUnrecorded]
  unfold DurableDataIntent.execute
  simp only [rekey_transactionId]
  rw [lookup]
  cases preflightEq : (deposit.rekey transactionId).preflight
      (DataSnapshot.install before deposit.intent) with
  | error reason => simp
  | ok _ => exact (deposit.installed_rekey_preflight_rejects transactionId before preflightEq).elim

end Deposit

/-! ## One atomic authorized fill -/

structure FillRuntime where
  transactionId : TransactionId
  nullifierId : Digest
  resourceCell : CellId
  orderCell : CellId
  cellsDistinct : resourceCell ≠ orderCell

structure Fill
    (M : Materializer CanonicalResourceKernel.schema Digest)
    (portal : Portal) (authState : AuthState) where
  terms : Terms
  wellFormed : terms.WellFormed
  manifest : AuthorizedResourceCharge.DeploymentManifest
  runtime : FillRuntime
  resourcePre : Materialized M
  before : State
  beforeValid : before.Valid terms
  taker : AccountId
  base : Nat
  height : Nat
  allowed : FillAllowed terms before base height
  escrowCover : Int.ofNat before.remainingBase <=
    (logicalBook resourcePre.logical).balance terms.escrow terms.baseAsset
  releaseAccepted : Accepted resourcePre (terms.releaseOperation taker base)
  paymentAccepted : Accepted releaseAccepted.post (terms.paymentOperation taker base)
  feeAccepted : Accepted paymentAccepted.post (terms.feeOperation taker base)
  releaseContext : AuthorizedResourceCharge.RequestContext
  paymentContext : AuthorizedResourceCharge.RequestContext
  feeContext : AuthorizedResourceCharge.RequestContext
  releaseContextBound : ContextBound releaseContext manifest terms before (.fill taker base height)
  paymentContextBound : ContextBound paymentContext manifest terms before (.fill taker base height)
  feeContextBound : ContextBound feeContext manifest terms before (.fill taker base height)
  releaseAuthorization : Authorized portal authState
    (releaseContext.request manifest releaseAccepted)
  paymentAuthorization : Authorized portal authState
    (paymentContext.request manifest paymentAccepted)
  feeAuthorization : Authorized portal authState
    (feeContext.request manifest feeAccepted)

namespace Fill

variable {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}

def after (fill : Fill M portal authState) : State :=
  fill.before.afterFill fill.base

@[simp] theorem after_valid (fill : Fill M portal authState) :
    fill.after.Valid fill.terms :=
  State.afterFill_valid fill.beforeValid fill.allowed

noncomputable def releaseEffect (fill : Fill M portal authState) :=
  AuthorizedResourceCharge.toCellEffect fill.manifest fill.releaseAccepted
    fill.releaseContext fill.releaseAuthorization

noncomputable def paymentEffect (fill : Fill M portal authState) :=
  AuthorizedResourceCharge.toCellEffect fill.manifest fill.paymentAccepted
    fill.paymentContext fill.paymentAuthorization

noncomputable def feeEffect (fill : Fill M portal authState) :=
  AuthorizedResourceCharge.toCellEffect fill.manifest fill.feeAccepted
    fill.feeContext fill.feeAuthorization

def charge (fill : Fill M portal authState) : Charge :=
  AuthorizedResourceCharge.exactCharge fill.manifest fill.releaseAccepted +
    AuthorizedResourceCharge.exactCharge fill.manifest fill.paymentAccepted +
    AuthorizedResourceCharge.exactCharge fill.manifest fill.feeAccepted

def nullifier (fill : Fill M portal authState) : StableNullifier where
  codecVersion := fill.manifest.version
  domain := actionDomain fill.manifest fill.terms fill.before
    (.fill fill.taker fill.base fill.height)
  nullifierId := fill.runtime.nullifierId
  canonicalBytes := encodeNat fill.terms.orderId ++ encodeNat fill.before.filledBase ++
    encodeNat fill.base ++ encodeNat fill.height

def event (fill : Fill M portal authState) : StableEvent where
  codecVersion := fill.manifest.version
  domain := actionDomain fill.manifest fill.terms fill.before
    (.fill fill.taker fill.base fill.height)
  eventId := ⟨Nat.pair
    (AuthorizedResourceCharge.chargedEffectDigest fill.manifest fill.resourcePre
      (fill.terms.releaseOperation fill.taker fill.base)).value
    (Nat.pair
      (AuthorizedResourceCharge.chargedEffectDigest fill.manifest fill.releaseAccepted.post
        (fill.terms.paymentOperation fill.taker fill.base)).value
      (AuthorizedResourceCharge.chargedEffectDigest fill.manifest fill.paymentAccepted.post
        (fill.terms.feeOperation fill.taker fill.base)).value)⟩
  canonicalBytes :=
    CanonicalResourceEffect.operationCodec.encode
        (fill.terms.releaseOperation fill.taker fill.base) ++
      CanonicalResourceEffect.operationCodec.encode
        (fill.terms.paymentOperation fill.taker fill.base) ++
      CanonicalResourceEffect.operationCodec.encode
        (fill.terms.feeOperation fill.taker fill.base) ++
      stateBytes fill.terms fill.after

def intent (fill : Fill M portal authState) : DataIntent M.rootBytes where
  transactionId := fill.runtime.transactionId
  writes :=
    [{ cellId := fill.runtime.resourceCell
       expectedPre := fill.resourcePre.root
       exactPost := fill.feeAccepted.post.root
       canonicalPostBytes := fill.feeAccepted.post.bytes },
     { cellId := fill.runtime.orderCell
       expectedPre := M.rootBytes (stateBytes fill.terms fill.before)
       exactPost := M.rootBytes (stateBytes fill.terms fill.after)
       canonicalPostBytes := stateBytes fill.terms fill.after }]
  readGuards := []
  nullifiers := [fill.nullifier]
  exactCharge := fill.charge
  event := fill.event
  postRootsBound := by
    intro write present
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at present
    rcases present with rfl | rfl <;> rfl
  guardsReadOnly := by simp

@[simp] theorem exact_charge (fill : Fill M portal authState) :
    fill.intent.exactCharge = fill.charge := rfl

theorem authorized_fees_sum_exactly (fill : Fill M portal authState) :
    (fill.releaseContext.request fill.manifest fill.releaseAccepted).cost +
      (fill.paymentContext.request fill.manifest fill.paymentAccepted).cost +
      (fill.feeContext.request fill.manifest fill.feeAccepted).cost =
        fill.intent.exactCharge .feeDebit := rfl

theorem conserves (fill : Fill M portal authState) (asset : AssetId) :
    (logicalBook fill.feeAccepted.post.logical).totalAsset asset =
      (logicalBook fill.resourcePre.logical).totalAsset asset := by
  calc
    (logicalBook fill.feeAccepted.post.logical).totalAsset asset =
        (logicalBook fill.paymentAccepted.post.logical).totalAsset asset :=
      fill.feeAccepted.conserves asset
    _ = (logicalBook fill.releaseAccepted.post.logical).totalAsset asset :=
      fill.paymentAccepted.conserves asset
    _ = (logicalBook fill.resourcePre.logical).totalAsset asset :=
      fill.releaseAccepted.conserves asset

theorem cannot_overfill (fill : Fill M portal authState) :
    fill.base <= fill.before.remainingBase :=
  fill.allowed.withinEscrow

@[simp] theorem retry_replays (fill : Fill M portal authState)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before fill.intent)
        fill.intent = .replayed fill.intent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install, Snapshot.install,
    Snapshot.lookupRecorded, Intent.sameCheck_self]

theorem atomic_resource_and_order
    (fill : Fill M portal authState) (schedule : Schedule)
    (before : DataSnapshot M.rootBytes) :
    (DurableDataIntent.execute schedule before fill.intent).storeAfter before = before \/
      (DurableDataIntent.execute schedule before fill.intent).storeAfter before =
        DataSnapshot.install before fill.intent :=
  DurableDataIntent.execute_no_partial_data_commit schedule before fill.intent

def rekey (fill : Fill M portal authState)
    (transactionId : TransactionId) : DataIntent M.rootBytes :=
  { fill.intent with transactionId := transactionId }

@[simp] theorem rekey_transactionId (fill : Fill M portal authState)
    (transactionId : TransactionId) :
    (fill.rekey transactionId).transactionId = transactionId := rfl

@[simp] theorem installed_rekey_nullifier_not_fresh
    (fill : Fill M portal authState) (transactionId : TransactionId)
    (before : DataSnapshot M.rootBytes) :
    (fill.rekey transactionId).erase.nullifiersFreshCheck
      (DataSnapshot.install before fill.intent).model = false := by
  simp [rekey, intent, nullifier, DurableCommitProtocol.Intent.nullifiersFreshCheck,
    DataSnapshot.install, Snapshot.install]

theorem installed_rekey_preflight_rejects
    (fill : Fill M portal authState) (transactionId : TransactionId)
    (before : DataSnapshot M.rootBytes) :
    (fill.rekey transactionId).preflight
      (DataSnapshot.install before fill.intent) ≠ .ok () := by
  simp [DataIntent.preflight, DurableCommitProtocol.Intent.preflight,
    rekey, intent, nullifier, DurableCommitProtocol.Intent.rootsMatchCheck,
    DurableCommitProtocol.Intent.nullifiersFreshCheck,
    DataSnapshot.install, Snapshot.install]
  split <;> simp_all
  all_goals aesop

theorem rekey_cannot_fill_twice
    (fill : Fill M portal authState) (transactionId : TransactionId)
    (different : transactionId ≠ fill.runtime.transactionId)
    (before : DataSnapshot M.rootBytes)
    (newUnrecorded : Snapshot.lookupRecorded transactionId before.model.journal = none)
    (schedule : Schedule) (next : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before fill.intent)
        (fill.rekey transactionId) ≠ .accepted next := by
  have lookup : Snapshot.lookupRecorded transactionId
      (DataSnapshot.install before fill.intent).model.journal = none := by
    have oldNe : fill.intent.transactionId ≠ transactionId := by
      simpa [intent] using different.symm
    simp [DataSnapshot.install, Snapshot.install, Snapshot.lookupRecorded,
      oldNe, newUnrecorded]
  unfold DurableDataIntent.execute
  simp only [rekey_transactionId]
  rw [lookup]
  cases preflightEq : (fill.rekey transactionId).preflight
      (DataSnapshot.install before fill.intent) with
  | error reason => simp
  | ok _ => exact (fill.installed_rekey_preflight_rejects transactionId before preflightEq).elim

def admissionCharge (fill : Fill M portal authState) : Charge :=
  fun lane => if lane = .feeDebit then fill.charge lane else 0

def bodyCharge (fill : Fill M portal authState) : Charge :=
  fun lane => if lane = .feeDebit then 0 else fill.charge lane

theorem admission_add_body_exact (fill : Fill M portal authState) :
    fill.admissionCharge + fill.bodyCharge = fill.charge := by
  funext lane
  by_cases fee : lane = .feeDebit
  · subst fee
    simp [admissionCharge, bodyCharge]
  · simp [admissionCharge, bodyCharge, fee]

def admissionBodyIntent (fill : Fill M portal authState) : DataIntent M.rootBytes :=
  { fill.intent with exactCharge := fill.bodyCharge }

structure FeeFirstEnvelope (fill : Fill M portal authState) where
  request : AdmissionPrologue.Request M.rootBytes
  wellFormed : request.WellFormed
  prologueExact : request.prologue.exactCharge = fill.admissionCharge
  bodyExact : request.body = fill.admissionBodyIntent

theorem FeeFirstEnvelope.exact_split
    {fill : Fill M portal authState} (envelope : FeeFirstEnvelope fill) :
    envelope.request.prologue.exactCharge + envelope.request.body.exactCharge =
        fill.charge /\
      envelope.request.body.exactCharge .feeDebit = 0 := by
  constructor
  · rw [envelope.prologueExact, envelope.bodyExact]
    exact fill.admission_add_body_exact
  · exact envelope.wellFormed.bodyChargesNoAdmissionFee

end Fill

/-! ## Terminal order state, without implicit asset release -/

structure CancelCapability (terms : Terms) where
  principal : AccountId
  orderId : Nat
  notBefore : Nat
  notAfter : Nat
  exactMaker : principal = terms.maker
  exactOrder : orderId = terms.orderId

inductive CloseDecision (terms : Terms) (height : Nat)
  | cancel (capability : CancelCapability terms)
      (validFrom : capability.notBefore <= height)
      (validUntil : height <= capability.notAfter)
  | expire (afterDeadline : terms.expiresAt < height)

def CloseDecision.phase {terms : Terms} {height : Nat} :
    CloseDecision terms height -> Phase
  | .cancel .. => .cancelled
  | .expire .. => .expired

structure CloseRuntime where
  transactionId : TransactionId
  nullifierId : Digest
  orderCell : CellId

structure Close
    (M : Materializer CanonicalResourceKernel.schema Digest) where
  terms : Terms
  wellFormed : terms.WellFormed
  manifest : AuthorizedResourceCharge.DeploymentManifest
  runtime : CloseRuntime
  resourcePre : Materialized M
  before : State
  beforeValid : before.Valid terms
  live : before.Live
  height : Nat
  decision : CloseDecision terms height

namespace Close

variable {M : Materializer CanonicalResourceKernel.schema Digest}

def after (close : Close M) : State :=
  { close.before with phase := close.decision.phase }

@[simp] theorem after_release_due (close : Close M) : close.after.ReleaseDue := by
  constructor
  · unfold after
    cases close.decision <;> simp [CloseDecision.phase]
  · rcases close.beforeValid with ⟨_, phaseValid⟩
    have remaining : 0 < close.before.remainingBase := by
      rcases close.live with openedProof | partialProof
      · rw [openedProof] at phaseValid
        rw [phaseValid.2]
        exact close.wellFormed.positiveQuantity
      · rw [partialProof] at phaseValid
        exact phaseValid.2
    simpa [after] using remaining

def nullifier (close : Close M) : StableNullifier where
  codecVersion := close.manifest.version
  domain := actionDomain close.manifest close.terms close.before
    (match close.decision with
     | .cancel .. => .cancel close.height
     | .expire .. => .expire close.height)
  nullifierId := close.runtime.nullifierId
  canonicalBytes := encodeNat close.terms.orderId ++ encodeNat close.height

def intent (close : Close M) : DataIntent M.rootBytes where
  transactionId := close.runtime.transactionId
  writes :=
    [{ cellId := close.runtime.orderCell
       expectedPre := M.rootBytes (stateBytes close.terms close.before)
       exactPost := M.rootBytes (stateBytes close.terms close.after)
       canonicalPostBytes := stateBytes close.terms close.after }]
  readGuards := []
  nullifiers := [close.nullifier]
  exactCharge := 0
  event :=
    { codecVersion := close.manifest.version
      domain := close.nullifier.domain
      eventId := ⟨Nat.pair close.terms.orderId close.after.phase.tag⟩
      canonicalBytes := stateBytes close.terms close.after }
  postRootsBound := by simp
  guardsReadOnly := by simp

@[simp] theorem no_asset_write (close : Close M) :
    close.intent.writes.map DataWrite.cellId = [close.runtime.orderCell] := rfl

@[simp] theorem no_resource_charge (close : Close M) :
    close.intent.exactCharge = 0 := rfl

@[simp] theorem retry_replays (close : Close M)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before close.intent)
        close.intent = .replayed close.intent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install, Snapshot.install,
    Snapshot.lookupRecorded, Intent.sameCheck_self]

end Close

/-! ## Freshly authorized residual refund -/

structure RefundRuntime where
  transactionId : TransactionId
  nullifierId : Digest
  resourceCell : CellId

structure Refund
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {close : Close M} (_due : close.after.ReleaseDue)
    (portal : Portal) (authState : AuthState) where
  runtime : RefundRuntime
  context : AuthorizedResourceCharge.RequestContext
  accepted : Accepted close.resourcePre
    (close.terms.refundOperation close.before.remainingBase)
  contextBound : ContextBound context close.manifest close.terms close.after
    (.refund close.before.remainingBase)
  authorization : Authorized portal authState
    (context.request close.manifest accepted)

namespace Refund

variable {M : Materializer CanonicalResourceKernel.schema Digest}
    {close : Close M} {due : close.after.ReleaseDue}
    {portal : Portal} {authState : AuthState}

def nullifier (refund : Refund due portal authState) : StableNullifier where
  codecVersion := close.manifest.version
  domain := actionDomain close.manifest close.terms close.after
    (.refund close.before.remainingBase)
  nullifierId := refund.runtime.nullifierId
  canonicalBytes := encodeNat close.terms.orderId ++
    encodeNat close.before.remainingBase ++ encodeNat refund.context.nonce

def intent (refund : Refund due portal authState) : DataIntent M.rootBytes :=
  { AuthorizedResourceCharge.durableIntent refund.runtime.transactionId
      refund.runtime.resourceCell close.manifest refund.accepted with
      nullifiers := [refund.nullifier]
      event :=
        { codecVersion := close.manifest.version
          domain := refund.nullifier.domain
          eventId := AuthorizedResourceCharge.chargedEffectDigest close.manifest
            close.resourcePre (close.terms.refundOperation close.before.remainingBase)
          canonicalBytes := CanonicalResourceEffect.operationCodec.encode
            (close.terms.refundOperation close.before.remainingBase) } }

@[simp] theorem separately_authorized_cost
    (refund : Refund due portal authState) :
    (refund.context.request close.manifest refund.accepted).cost =
      refund.intent.exactCharge .feeDebit := rfl

theorem conserves (refund : Refund due portal authState) (asset : AssetId) :
    (logicalBook refund.accepted.post.logical).totalAsset asset =
      (logicalBook close.resourcePre.logical).totalAsset asset :=
  refund.accepted.conserves asset

theorem refund_operation_ne_deposit
    (_refund : Refund due portal authState) :
    close.terms.refundOperation close.before.remainingBase ≠
      close.terms.depositOperation := by
  intro same
  simp [Terms.refundOperation, Terms.depositOperation] at same
  exact close.wellFormed.makerEscrowDistinct same.1.symm

@[simp] theorem retry_replays (refund : Refund due portal authState)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before refund.intent)
        refund.intent = .replayed refund.intent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install, Snapshot.install,
    Snapshot.lookupRecorded, Intent.sameCheck_self]

def rekey (refund : Refund due portal authState)
    (transactionId : TransactionId) : DataIntent M.rootBytes :=
  { refund.intent with transactionId := transactionId }

@[simp] theorem rekey_transactionId (refund : Refund due portal authState)
    (transactionId : TransactionId) :
    (refund.rekey transactionId).transactionId = transactionId := rfl

@[simp] theorem installed_rekey_nullifier_not_fresh
    (refund : Refund due portal authState) (transactionId : TransactionId)
    (before : DataSnapshot M.rootBytes) :
    (refund.rekey transactionId).erase.nullifiersFreshCheck
      (DataSnapshot.install before refund.intent).model = false := by
  simp [rekey, intent, nullifier, DurableCommitProtocol.Intent.nullifiersFreshCheck,
    DataSnapshot.install, Snapshot.install]

theorem installed_rekey_preflight_rejects
    (refund : Refund due portal authState) (transactionId : TransactionId)
    (before : DataSnapshot M.rootBytes) :
    (refund.rekey transactionId).preflight
      (DataSnapshot.install before refund.intent) ≠ .ok () := by
  simp [DataIntent.preflight, DurableCommitProtocol.Intent.preflight,
    rekey, intent, nullifier, DurableCommitProtocol.Intent.rootsMatchCheck,
    DurableCommitProtocol.Intent.nullifiersFreshCheck,
    DataSnapshot.install, Snapshot.install]
  split <;> simp_all
  all_goals aesop

theorem rekey_cannot_release_twice
    (refund : Refund due portal authState) (transactionId : TransactionId)
    (different : transactionId ≠ refund.runtime.transactionId)
    (before : DataSnapshot M.rootBytes)
    (newUnrecorded : Snapshot.lookupRecorded transactionId before.model.journal = none)
    (schedule : Schedule) (next : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before refund.intent)
        (refund.rekey transactionId) ≠ .accepted next := by
  have lookup : Snapshot.lookupRecorded transactionId
      (DataSnapshot.install before refund.intent).model.journal = none := by
    have oldNe : refund.intent.transactionId ≠ transactionId := by
      simpa [intent] using different.symm
    simp [DataSnapshot.install, Snapshot.install, Snapshot.lookupRecorded,
      oldNe, newUnrecorded]
  unfold DurableDataIntent.execute
  simp only [rekey_transactionId]
  rw [lookup]
  cases preflightEq : (refund.rekey transactionId).preflight
      (DataSnapshot.install before refund.intent) with
  | error reason => simp
  | ok _ => exact (refund.installed_rekey_preflight_rejects transactionId before preflightEq).elim

end Refund

/-! ## Fill/close race and explicit trust boundaries -/

theorem fill_after_close_has_stale_order_root
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (fill : Fill M portal authState) (close : Close M)
    (sameTerms : fill.terms = close.terms)
    (sameState : fill.before = close.before)
    (sameOrderCell : fill.runtime.orderCell = close.runtime.orderCell)
    (rootMoves : M.rootBytes (stateBytes close.terms close.after) ≠
      M.rootBytes (stateBytes close.terms close.before))
    (before : DataSnapshot M.rootBytes) :
    (DataSnapshot.install before close.intent).model.roots fill.runtime.orderCell ≠
      M.rootBytes (stateBytes fill.terms fill.before) := by
  intro equal
  apply rootMoves
  simpa [DataSnapshot.install, Snapshot.install, Snapshot.lookupPost, Close.intent,
    sameTerms, sameState, sameOrderCell] using equal

theorem fill_after_close_roots_check_fails
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (fill : Fill M portal authState) (close : Close M)
    (sameTerms : fill.terms = close.terms)
    (sameState : fill.before = close.before)
    (sameOrderCell : fill.runtime.orderCell = close.runtime.orderCell)
    (rootMoves : M.rootBytes (stateBytes close.terms close.after) ≠
      M.rootBytes (stateBytes close.terms close.before))
    (before : DataSnapshot M.rootBytes) :
    fill.intent.erase.rootsMatchCheck
      (DataSnapshot.install before close.intent).model = false := by
  cases checked : fill.intent.erase.rootsMatchCheck
      (DataSnapshot.install before close.intent).model with
  | false => rfl
  | true =>
      have every := (DurableCommitProtocol.Intent.rootsMatchCheck_eq_true_iff
        (DataSnapshot.install before close.intent).model fill.intent.erase).mp checked
      have orderMatch := every
        { cellId := fill.runtime.orderCell
          expectedPre := M.rootBytes (stateBytes fill.terms fill.before)
          exactPost := M.rootBytes (stateBytes fill.terms fill.after) }
        (by simp [Fill.intent, DataIntent.erase])
      exact (fill_after_close_has_stale_order_root fill close sameTerms sameState
        sameOrderCell rootMoves before orderMatch).elim

theorem fill_after_close_preflight_rejects
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (fill : Fill M portal authState) (close : Close M)
    (sameTerms : fill.terms = close.terms)
    (sameState : fill.before = close.before)
    (sameOrderCell : fill.runtime.orderCell = close.runtime.orderCell)
    (rootMoves : M.rootBytes (stateBytes close.terms close.after) ≠
      M.rootBytes (stateBytes close.terms close.before))
    (before : DataSnapshot M.rootBytes) :
    fill.intent.preflight (DataSnapshot.install before close.intent) ≠ .ok () := by
  have failed := fill_after_close_roots_check_fails fill close sameTerms sameState
    sameOrderCell rootMoves before
  have failed' : fill.intent.erase.rootsMatchCheck
      (Snapshot.install before.model close.intent.erase) = false := by
    simpa [DataSnapshot.install] using failed
  have modelReject : fill.intent.erase.preflight
      (Snapshot.install before.model close.intent.erase) ≠ .ok () := by
    unfold DurableCommitProtocol.Intent.preflight
    rw [failed']
    split
    · simp
    · split
      · simp
      · split <;> simp
  unfold DataIntent.preflight
  have guards : fill.intent.readGuardsMatchCheck
      (DataSnapshot.install before close.intent) = true := by rfl
  rw [guards]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  cases checked : fill.intent.erase.preflight
      (Snapshot.install before.model close.intent.erase) with
  | error reason => simp [checked]
  | ok unit => exact (modelReject checked).elim

/-- A private proof is outside this public settlement kernel.  The only sound
join is a refinement showing that a verified private statement denotes the
already explicit public fill and its three exact accepted legs. -/
structure PrivateFillRefinement
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (fill : Fill M portal authState)
    (Statement Proof : Type) (verify : Statement -> Proof -> Bool)
    (statement : Statement) : Prop where
  denotesExactPublicFill : forall proof, verify statement proof = true ->
    FillAllowed fill.terms fill.before fill.base fill.height /\
      ContextBound fill.releaseContext fill.manifest fill.terms fill.before
        (.fill fill.taker fill.base fill.height) /\
      ContextBound fill.paymentContext fill.manifest fill.terms fill.before
        (.fill fill.taker fill.base fill.height) /\
      ContextBound fill.feeContext fill.manifest fill.terms fill.before
        (.fill fill.taker fill.base fill.height)

/-- Price discovery and oracle truth are not inferred from the declared quote.
This boundary must relate external evidence to the exact immutable terms. -/
structure PriceOracleRefinement (terms : Terms) (Evidence : Type)
    (ValidMarketPrice : Nat -> Prop) where
  verifies : Evidence -> Prop
  sound : forall evidence, verifies evidence -> ValidMarketPrice terms.unitQuote

/-- Durable logical atomicity becomes a provider/storage claim only through
the common data-intent implementation refinement. -/
theorem physical_fill_atomic
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState}
    (fill : Fill M portal authState)
    {PhysicalState : Type} {PhysicalStep : PhysicalState -> DataIntent M.rootBytes -> PhysicalState -> Type}
    {Represents : PhysicalState -> DataSnapshot M.rootBytes -> Prop}
    (refinement : ImplementationRefinement M.rootBytes PhysicalState PhysicalStep Represents)
    {physicalBefore physicalAfter : PhysicalState}
    {modelBefore : DataSnapshot M.rootBytes}
    (represented : Represents physicalBefore modelBefore)
    (stepped : PhysicalStep physicalBefore fill.intent physicalAfter) :
    exists modelAfter,
      (modelAfter = modelBefore \/ modelAfter = DataSnapshot.install modelBefore fill.intent) /\
        Represents physicalAfter modelAfter :=
  by
    rcases DurableDataIntent.physical_step_no_partial_data_commit refinement represented stepped with
      ⟨modelAfter, representedAfter, oldOrNew, _coherent⟩
    exact ⟨modelAfter, oldOrNew, representedAfter⟩

/-! ## Closed public witnesses -/

namespace Witness

def terms : Terms where
  orderId := 7
  maker := 1
  escrow := 2
  baseAsset := 0
  quoteAsset := 4
  baseQuantity := 4
  unitQuote := 2
  feeCollector := 0
  feePerBase := 1
  opensAt := 10
  expiresAt := 20

def termsWellFormed : terms.WellFormed where
  positiveQuantity := by decide
  positiveQuote := by decide
  marketWindow := by decide
  makerEscrowDistinct := by decide
  baseQuoteDistinct := by decide

def openState : State := State.opened terms

def partialState : State := openState.afterFill 2

def partialAllowed : FillAllowed terms openState 2 12 where
  live := Or.inl rfl
  positive := by decide
  withinEscrow := by decide
  opened := by decide
  beforeExpiry := by decide

@[simp] theorem partial_is_partial : partialState.phase = .livePartial := by decide

@[simp] theorem partial_remaining : partialState.remainingBase = 2 := by decide

def completeState : State := openState.afterFill 4

@[simp] theorem complete_is_complete : completeState.phase = .filled := by decide

@[simp] theorem complete_not_refundable : Not completeState.ReleaseDue :=
  complete_has_no_release_due complete_is_complete

theorem five_unit_overfill_rejected :
    Not (FillAllowed terms openState 5 12) :=
  overfill_has_no_admission (by decide)

/-- The public arithmetic witness: the three fill legs preserve both asset
totals even though base and quote balances move in opposite directions. -/
def book : Book where
  accounts := {0, 1, 2, 3, 4}
  balances :=
    DFinsupp.single (0, 0) (-10) +
      DFinsupp.single (1, 0) 4 +
      DFinsupp.single (3, 0) 6 +
      DFinsupp.single (4, 4) (-20) +
      DFinsupp.single (3, 4) 20
  leaseRecords := 0

example : book.totalAsset 0 = 0 := by decide
example : book.totalAsset 4 = 0 := by decide

example :
    ((terms.depositOperation.apply book).totalAsset 0) = book.totalAsset 0 := by
  exact Operation.apply_conserves _ _ (by decide) (by decide) 0

example :
    (((terms.feeOperation 3 2).apply
      ((terms.paymentOperation 3 2).apply
        ((terms.releaseOperation 3 2).apply
          (terms.depositOperation.apply book)))).totalAsset 4) = book.totalAsset 4 := by
  rw [Operation.apply_conserves _ _ (by decide) (by decide) 4]
  rw [Operation.apply_conserves _ _ (by decide) (by decide) 4]
  rw [Operation.apply_conserves _ _ (by decide) (by decide) 4]
  exact Operation.apply_conserves _ _ (by decide) (by decide) 4

def logical : LogicalState CanonicalResourceKernel.schema where
  fields := (0 : FieldStore CanonicalResourceKernel.schema).write .book book
  resources := fun resource => nomatch resource

noncomputable def cell : Materialized CanonicalResourceKernel.materializer :=
  materialize CanonicalResourceKernel.materializer logical

@[simp] theorem cell_book : logicalBook cell.logical = book := by
  simp [cell, logical, logicalBook, materialize, FieldStore.read]

def depositAdmission : Admission book terms.depositOperation where
  sourcePresent := by decide
  destinationPresent := by decide
  sourceSolvent := Or.inr (by decide)
  leaseWellFormed := trivial

noncomputable def depositAccepted : Accepted cell terms.depositOperation :=
  Accepted.ofAdmission (by simpa using depositAdmission)

def context (domain : Digest) (nonce : Nat) :
    AuthorizedResourceCharge.RequestContext where
  domain := domain
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 2
  nonce := nonce
  height := 12
  policyId := ⟨9⟩
  policyEpoch := 5

noncomputable def authorize
    {pre : Materialized CanonicalResourceKernel.materializer}
    {operation : Operation} (domain : Digest) (nonce : Nat)
    (accepted : Accepted pre operation) :
    Authorized demoPortal demoState
      ((context domain nonce).request AuthorizedResourceCharge.witnessManifest accepted) where
  evidence := .signature () rfl rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def depositContext := context
  (actionDomain AuthorizedResourceCharge.witnessManifest terms openState .deposit) 1

def depositRuntime : DepositRuntime where
  transactionId := ⟨100⟩
  nullifierId := ⟨101⟩
  resourceCell := ⟨102⟩
  orderCell := ⟨103⟩
  emptyOrderBytes := []
  cellsDistinct := by decide

noncomputable def deposited :
    Deposit CanonicalResourceKernel.materializer demoPortal demoState cell where
  terms := terms
  wellFormed := termsWellFormed
  runtime := depositRuntime
  manifest := AuthorizedResourceCharge.witnessManifest
  context := depositContext
  accepted := depositAccepted
  contextBound := rfl
  authorization := by
    exact authorize
      (actionDomain AuthorizedResourceCharge.witnessManifest terms openState .deposit)
      1 depositAccepted

@[simp] theorem deposited_cost_exact :
    (depositContext.request AuthorizedResourceCharge.witnessManifest depositAccepted).cost =
      deposited.intent.exactCharge .feeDebit := rfl

theorem deposited_retry_is_free
    (schedule : Schedule)
    (before : DataSnapshot CanonicalResourceKernel.materializer.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before deposited.intent)
        deposited.intent = .replayed deposited.intent.erase :=
  deposited.retry_replays schedule before

def releaseAdmission :
    Admission (logicalBook depositAccepted.post.logical)
      (terms.releaseOperation 3 2) where
  sourcePresent := by
    rw [depositAccepted.post_logicalBook, Operation.apply_accounts]
    decide
  destinationPresent := by
    rw [depositAccepted.post_logicalBook, Operation.apply_accounts]
    decide
  sourceSolvent := Or.inr (by
    rw [depositAccepted.post_logicalBook]
    decide)
  leaseWellFormed := trivial

noncomputable def releaseAccepted :
    Accepted depositAccepted.post (terms.releaseOperation 3 2) :=
  Accepted.ofAdmission releaseAdmission

def paymentAdmission :
    Admission (logicalBook releaseAccepted.post.logical)
      (terms.paymentOperation 3 2) where
  sourcePresent := by
    rw [releaseAccepted.post_logicalBook, depositAccepted.post_logicalBook,
      Operation.apply_accounts, Operation.apply_accounts]
    decide
  destinationPresent := by
    rw [releaseAccepted.post_logicalBook, depositAccepted.post_logicalBook,
      Operation.apply_accounts, Operation.apply_accounts]
    decide
  sourceSolvent := Or.inr (by
    rw [releaseAccepted.post_logicalBook, depositAccepted.post_logicalBook]
    decide)
  leaseWellFormed := trivial

noncomputable def paymentAccepted :
    Accepted releaseAccepted.post (terms.paymentOperation 3 2) :=
  Accepted.ofAdmission paymentAdmission

def feeAdmission :
    Admission (logicalBook paymentAccepted.post.logical)
      (terms.feeOperation 3 2) where
  sourcePresent := by
    rw [paymentAccepted.post_logicalBook, releaseAccepted.post_logicalBook,
      depositAccepted.post_logicalBook, Operation.apply_accounts,
      Operation.apply_accounts, Operation.apply_accounts]
    decide
  destinationPresent := by
    rw [paymentAccepted.post_logicalBook, releaseAccepted.post_logicalBook,
      depositAccepted.post_logicalBook, Operation.apply_accounts,
      Operation.apply_accounts, Operation.apply_accounts]
    decide
  sourceSolvent := Or.inr (by
    rw [paymentAccepted.post_logicalBook, releaseAccepted.post_logicalBook,
      depositAccepted.post_logicalBook]
    decide)
  leaseWellFormed := trivial

noncomputable def feeAccepted :
    Accepted paymentAccepted.post (terms.feeOperation 3 2) :=
  Accepted.ofAdmission feeAdmission

def fillDomain := actionDomain AuthorizedResourceCharge.witnessManifest
  terms openState (.fill 3 2 12)

def releaseContext := context fillDomain 2
def paymentContext := context fillDomain 3
def feeContext := context fillDomain 4

def fillRuntime : FillRuntime where
  transactionId := ⟨110⟩
  nullifierId := ⟨111⟩
  resourceCell := depositRuntime.resourceCell
  orderCell := depositRuntime.orderCell
  cellsDistinct := depositRuntime.cellsDistinct

noncomputable def filled :
    Fill CanonicalResourceKernel.materializer demoPortal demoState where
  terms := terms
  wellFormed := termsWellFormed
  manifest := AuthorizedResourceCharge.witnessManifest
  runtime := fillRuntime
  resourcePre := depositAccepted.post
  before := openState
  beforeValid := State.opened_valid terms
  taker := 3
  base := 2
  height := 12
  allowed := partialAllowed
  escrowCover := by
    rw [depositAccepted.post_logicalBook]
    decide
  releaseAccepted := releaseAccepted
  paymentAccepted := paymentAccepted
  feeAccepted := feeAccepted
  releaseContext := releaseContext
  paymentContext := paymentContext
  feeContext := feeContext
  releaseContextBound := rfl
  paymentContextBound := rfl
  feeContextBound := rfl
  releaseAuthorization := authorize fillDomain 2 releaseAccepted
  paymentAuthorization := authorize fillDomain 3 paymentAccepted
  feeAuthorization := authorize fillDomain 4 feeAccepted

@[simp] theorem filled_is_partial : filled.after.phase = .livePartial := by decide

theorem filled_conserves_base :
    (logicalBook filled.feeAccepted.post.logical).totalAsset terms.baseAsset =
      (logicalBook filled.resourcePre.logical).totalAsset terms.baseAsset :=
  filled.conserves terms.baseAsset

theorem filled_conserves_quote :
    (logicalBook filled.feeAccepted.post.logical).totalAsset terms.quoteAsset =
      (logicalBook filled.resourcePre.logical).totalAsset terms.quoteAsset :=
  filled.conserves terms.quoteAsset

theorem filled_retry_is_free
    (schedule : Schedule)
    (before : DataSnapshot CanonicalResourceKernel.materializer.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before filled.intent)
        filled.intent = .replayed filled.intent.erase :=
  filled.retry_replays schedule before

def cancelCapability : CancelCapability terms where
  principal := terms.maker
  orderId := terms.orderId
  notBefore := 10
  notAfter := 20
  exactMaker := rfl
  exactOrder := rfl

def closeRuntime : CloseRuntime where
  transactionId := ⟨120⟩
  nullifierId := ⟨121⟩
  orderCell := fillRuntime.orderCell

noncomputable def closed : Close CanonicalResourceKernel.materializer where
  terms := terms
  wellFormed := termsWellFormed
  manifest := AuthorizedResourceCharge.witnessManifest
  runtime := closeRuntime
  resourcePre := feeAccepted.post
  before := filled.after
  beforeValid := filled.after_valid
  live := Or.inr filled_is_partial
  height := 13
  decision := .cancel cancelCapability (by decide) (by decide)

@[simp] theorem closed_is_cancelled : closed.after.phase = .cancelled := rfl

@[simp] theorem closed_has_residual_release : closed.after.ReleaseDue :=
  closed.after_release_due

def refundAdmission :
    Admission (logicalBook feeAccepted.post.logical)
      (terms.refundOperation filled.after.remainingBase) where
  sourcePresent := by
    rw [feeAccepted.post_logicalBook, paymentAccepted.post_logicalBook,
      releaseAccepted.post_logicalBook, depositAccepted.post_logicalBook,
      Operation.apply_accounts, Operation.apply_accounts,
      Operation.apply_accounts, Operation.apply_accounts]
    decide
  destinationPresent := by
    rw [feeAccepted.post_logicalBook, paymentAccepted.post_logicalBook,
      releaseAccepted.post_logicalBook, depositAccepted.post_logicalBook,
      Operation.apply_accounts, Operation.apply_accounts,
      Operation.apply_accounts, Operation.apply_accounts]
    decide
  sourceSolvent := Or.inr (by
    rw [feeAccepted.post_logicalBook, paymentAccepted.post_logicalBook,
      releaseAccepted.post_logicalBook, depositAccepted.post_logicalBook]
    decide)
  leaseWellFormed := trivial

noncomputable def refundAccepted :
    Accepted feeAccepted.post
      (terms.refundOperation filled.after.remainingBase) :=
  Accepted.ofAdmission refundAdmission

noncomputable def refundDomain := actionDomain AuthorizedResourceCharge.witnessManifest
  terms closed.after (.refund closed.before.remainingBase)

noncomputable def refundContext := context refundDomain 5

def refundRuntime : RefundRuntime where
  transactionId := ⟨130⟩
  nullifierId := ⟨131⟩
  resourceCell := fillRuntime.resourceCell

noncomputable def refunded :
    Refund closed_has_residual_release demoPortal demoState where
  runtime := refundRuntime
  context := refundContext
  accepted := refundAccepted
  contextBound := rfl
  authorization := authorize refundDomain 5 refundAccepted

@[simp] theorem refund_is_separately_authorized :
    (refundContext.request AuthorizedResourceCharge.witnessManifest refundAccepted).cost =
      refunded.intent.exactCharge .feeDebit :=
  refunded.separately_authorized_cost

theorem refund_preserves_base :
    (logicalBook refunded.accepted.post.logical).totalAsset terms.baseAsset =
      (logicalBook closed.resourcePre.logical).totalAsset terms.baseAsset :=
  refunded.conserves terms.baseAsset

theorem refund_retry_is_free
    (schedule : Schedule)
    (before : DataSnapshot CanonicalResourceKernel.materializer.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before refunded.intent)
        refunded.intent = .replayed refunded.intent.erase :=
  refunded.retry_replays schedule before

theorem refund_cannot_be_rekeyed_and_released_again
    (before : DataSnapshot CanonicalResourceKernel.materializer.rootBytes)
    (unrecorded : Snapshot.lookupRecorded (⟨132⟩ : Digest) before.model.journal = none)
    (schedule : Schedule) (next : DataSnapshot CanonicalResourceKernel.materializer.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before refunded.intent)
        (refunded.rekey ⟨132⟩) ≠ .accepted next :=
  refunded.rekey_cannot_release_twice ⟨132⟩ (by decide) before unrecorded schedule next

end Witness

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.CanonicalEscrowMarket.Fill.conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fill.conserves
/-- info: 'Minidregg.Kernel.CanonicalEscrowMarket.Fill.atomic_resource_and_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fill.atomic_resource_and_order
/-- info: 'Minidregg.Kernel.CanonicalEscrowMarket.Fill.installed_rekey_nullifier_not_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Fill.installed_rekey_nullifier_not_fresh
/-- info: 'Minidregg.Kernel.CanonicalEscrowMarket.Refund.refund_operation_ne_deposit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Refund.refund_operation_ne_deposit
/-- info: 'Minidregg.Kernel.CanonicalEscrowMarket.Refund.installed_rekey_nullifier_not_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Refund.installed_rekey_nullifier_not_fresh

end Minidregg.Kernel.CanonicalEscrowMarket
