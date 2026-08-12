/-
# Assurance.DreggNetProviderConsumer -- one exact purchased provider job

This module is the application-level weld for a DreggNet/cloud-provider job.
It does not introduce another balance, authorization, terminal, or consensus
machine.  Instead one closed job crosses the existing joints:

* `CanonicalEscrowMarket.Fill` buys an exact quantity at an exact public quote;
* `ProviderExecutionLease.OpenedLease` prepays that same quantity and price;
* `AdmissionPrologue` charges the manifest-derived fee first and installs the
  zero-fee canonical lease body under one replay identity;
* the provider start key commits the complete lease terms, image/input roots,
  endpoint, and deployment manifest, so stale tariffs and stale leases cannot
  alias an already authorized provider invocation;
* opaque provider completion evidence selects one `ReactiveTerminalCell`
  terminal/outbox write, and an intersecting quorum finalizes its exact erased
  durable payload;
* retry, cancellation, expiry, and separately authorized refund remain the
  existing kernel transitions rather than native side doors.

The provider boundary is still opaque.  This file does not prove that a cloud
API executed the image correctly, that its evidence is truthful, that an OS or
database persisted bytes, or that a real network reaches consensus or makes
progress.  Those are explicit refinements at the end of the module.
-/
import Kernel.CanonicalEscrowMarket
import Kernel.ProviderExecutionLease
import Kernel.ReplicatedSettlementFinality

namespace Minidregg.Assurance.DreggNetProviderConsumer

open Minidregg.Kernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel

set_option autoImplicit false

/-! ## Market-to-provider commercial binding -/

/-- The market fill is not decorative metadata: its taker, maker, quote asset,
filled capacity, and unit quote are definitionally the lease's holder,
provider, prepaid asset, epochs, and rate. -/
structure CommercialBinding
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (fill : CanonicalEscrowMarket.Fill M portal authState)
    (lease : ProviderExecutionLease.OpenedLease M portal authState pre) : Prop where
  holder : lease.terms.holder = fill.taker
  provider : lease.terms.provider = fill.terms.maker
  asset : lease.terms.asset = fill.terms.quoteAsset
  capacity : lease.terms.epochs = fill.base
  unitPrice : lease.terms.rate = fill.terms.unitQuote

theorem CommercialBinding.exact_quote
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {fill : CanonicalEscrowMarket.Fill M portal authState}
    {lease : ProviderExecutionLease.OpenedLease M portal authState pre}
    (binding : CommercialBinding fill lease) :
    lease.prepaid = fill.base * fill.terms.unitQuote := by
  simp [ProviderExecutionLease.OpenedLease.prepaid, ProviderExecutionLease.Terms.prepaid,
    binding.capacity, binding.unitPrice]
  exact Nat.mul_comm _ _

/-! ## Exact provider invocation identity -/

/-- First-order encoding of every immutable lease coordinate. -/
def leaseCode (terms : ProviderExecutionLease.Terms) : Nat :=
  Nat.pair terms.leaseId
    (Nat.pair terms.holder
      (Nat.pair terms.provider
        (Nat.pair terms.asset
          (Nat.pair terms.rate
            (Nat.pair terms.epochs terms.startsAt)))))

theorem leaseCode_injective : Function.Injective leaseCode := by
  rintro ⟨leftLease, leftHolder, leftProvider, leftAsset, leftRate, leftEpochs, leftStart⟩
    ⟨rightLease, rightHolder, rightProvider, rightAsset, rightRate, rightEpochs, rightStart⟩ same
  simp only [leaseCode, Nat.pair_eq_pair] at same
  simp_all

/-- Stable provider idempotency key.  It binds more than the provider's
`StartAction.prepaid` scalar: different rate/epoch decompositions, codecs, or
tariffs cannot retain the same key merely because their product is equal. -/
def providerInvocationKey
    (terms : ProviderExecutionLease.Terms) (manifest : AuthorizedResourceCharge.DeploymentManifest)
    (endpoint imageRoot inputRoot : Digest) : Digest :=
  ⟨Nat.pair 431
    (Nat.pair (leaseCode terms)
      (Nat.pair manifest.code
        (Nat.pair endpoint.value
          (Nat.pair imageRoot.value inputRoot.value))))⟩

theorem different_lease_changes_provider_key
    (left right : ProviderExecutionLease.Terms) (different : left ≠ right)
    (manifest : AuthorizedResourceCharge.DeploymentManifest)
    (endpoint imageRoot inputRoot : Digest) :
    providerInvocationKey left manifest endpoint imageRoot inputRoot ≠
      providerInvocationKey right manifest endpoint imageRoot inputRoot := by
  intro same
  apply different
  apply leaseCode_injective
  have values := congrArg Digest.value same
  simp only [providerInvocationKey, Nat.pair_eq_pair] at values
  exact values.2.1

theorem different_manifest_changes_provider_key
    (terms : ProviderExecutionLease.Terms)
    (left right : AuthorizedResourceCharge.DeploymentManifest) (different : left ≠ right)
    (endpoint imageRoot inputRoot : Digest) :
    providerInvocationKey terms left endpoint imageRoot inputRoot ≠
      providerInvocationKey terms right endpoint imageRoot inputRoot := by
  intro same
  apply different
  apply AuthorizedResourceCharge.DeploymentManifest.code_injective
  have values := congrArg Digest.value same
  simp only [providerInvocationKey, Nat.pair_eq_pair] at values
  exact values.2.2.1

/-- A consumer lease may enter the provider boundary only when its external
transaction id is the key derived above. -/
structure BoundLease
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M} where
  lease : ProviderExecutionLease.OpenedLease M portal authState pre
  exactProviderKey : lease.runtime.startTransaction =
    providerInvocationKey lease.terms lease.manifest
      lease.runtime.providerEndpoint lease.runtime.imageRoot lease.runtime.inputRoot

namespace BoundLease

variable {M : Materializer CanonicalResourceKernel.schema Digest}
  {portal : Portal} {authState : AuthState} {pre : Materialized M}

@[simp] theorem start_uses_exact_provider_key
    (job : BoundLease (M := M) (portal := portal) (authState := authState)
      (pre := pre)) (height attempt : Nat) :
    (ProviderExecutionLease.startIntent job.lease height attempt).transactionId =
      providerInvocationKey job.lease.terms job.lease.manifest
        job.lease.runtime.providerEndpoint job.lease.runtime.imageRoot
        job.lease.runtime.inputRoot :=
  job.exactProviderKey

/-- A stale tariff/codec manifest cannot be replayed under the live provider
transaction identity. -/
theorem stale_manifest_key_rejected
    (job : BoundLease (M := M) (portal := portal) (authState := authState)
      (pre := pre))
    (stale : AuthorizedResourceCharge.DeploymentManifest) (different : stale ≠ job.lease.manifest) :
    job.lease.runtime.startTransaction ≠
      providerInvocationKey job.lease.terms stale
        job.lease.runtime.providerEndpoint job.lease.runtime.imageRoot
        job.lease.runtime.inputRoot := by
  rw [job.exactProviderKey]
  exact different_manifest_changes_provider_key job.lease.terms
    job.lease.manifest stale different.symm _ _ _

/-- Likewise a stale lease (including an equal-product rate/epoch mutation)
cannot alias the live provider transaction identity. -/
theorem stale_lease_key_rejected
    (job : BoundLease (M := M) (portal := portal) (authState := authState)
      (pre := pre))
    (stale : ProviderExecutionLease.Terms) (different : stale ≠ job.lease.terms) :
    job.lease.runtime.startTransaction ≠
      providerInvocationKey stale job.lease.manifest
        job.lease.runtime.providerEndpoint job.lease.runtime.imageRoot
        job.lease.runtime.inputRoot := by
  rw [job.exactProviderKey]
  exact different_lease_changes_provider_key job.lease.terms stale
    different.symm _ _ _ _

end BoundLease

/-- Two calls carrying the exact provider transaction key must denote one
provider observation.  This is the semantic idempotency contract expected of
the cloud adapter; its physical refinement remains explicit below. -/
structure IdempotentProviderStart
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (job : BoundLease (M := M) (portal := portal) (authState := authState)
      (pre := pre))
    (boundary : ProviderExecutionLease.StartBoundary)
    (height attempt : Nat) where
  first : ProviderExecutionLease.StartObserved boundary
    (ProviderExecutionLease.startIntent job.lease height attempt)
  retry : ProviderExecutionLease.StartObserved boundary
    (ProviderExecutionLease.startIntent job.lease height attempt)
  sameObservation : retry.observation = first.observation

namespace IdempotentProviderStart

variable {M : Materializer CanonicalResourceKernel.schema Digest}
  {portal : Portal} {authState : AuthState} {pre : Materialized M}
  {job : BoundLease (M := M) (portal := portal) (authState := authState)
    (pre := pre)}
  {boundary : ProviderExecutionLease.StartBoundary} {height attempt : Nat}

@[simp] theorem exact_transaction_key
    (_replay : IdempotentProviderStart job boundary height attempt) :
    (ProviderExecutionLease.startIntent job.lease height attempt).transactionId =
      providerInvocationKey job.lease.terms job.lease.manifest
        job.lease.runtime.providerEndpoint job.lease.runtime.imageRoot
        job.lease.runtime.inputRoot :=
  job.start_uses_exact_provider_key height attempt

end IdempotentProviderStart

/-! ## Concrete fee-first prepay adapter -/

/-- The admission fee has its own cell and transaction.  The canonical lease
body retains the provider prepay transaction id and resource cell; this
dependent carrier supplies their separation without admitting an impossible
or vacuous runtime value. -/
structure FeeFirstJob
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (lease : ProviderExecutionLease.OpenedLease M portal authState pre) where
  admissionId : TransactionId
  feeCell : CellId
  feeNullifier : Digest
  feeEvent : Digest
  openFeeBytes : List UInt8
  paidFeeBytes : List UInt8
  admissionPrepayDistinct : admissionId ≠ lease.runtime.prepayTransaction
  feeResourceDistinct : feeCell ≠ lease.runtime.resourceCell
  positiveFee : 0 < AuthorizedResourceCharge.exactCharge lease.manifest lease.accepted .feeDebit

namespace FeeFirstJob

variable {M : Materializer CanonicalResourceKernel.schema Digest}
  {portal : Portal} {authState : AuthState} {pre : Materialized M}
  {lease : ProviderExecutionLease.OpenedLease M portal authState pre}

def nonce (job : FeeFirstJob lease) : StableNullifier where
  codecVersion := lease.manifest.version
  domain := lease.manifest.semanticDigest
  nullifierId := job.feeNullifier
  canonicalBytes := ReactiveTerminalCell.frame 190
    [ReactiveTerminalCell.encodeNat lease.requestContext.nonce,
      ReactiveTerminalCell.encodeDigest job.admissionId]

def prologue (job : FeeFirstJob lease) : DataIntent M.rootBytes where
  transactionId := job.admissionId
  writes :=
    [{ cellId := job.feeCell
       expectedPre := M.rootBytes job.openFeeBytes
       exactPost := M.rootBytes job.paidFeeBytes
       canonicalPostBytes := job.paidFeeBytes }]
  readGuards := []
  nullifiers := [job.nonce]
  exactCharge := AuthorizedResourceCharge.admissionCharge lease.manifest lease.accepted
  event :=
    { codecVersion := lease.manifest.version
      domain := lease.manifest.semanticDigest
      eventId := job.feeEvent
      canonicalBytes := ReactiveTerminalCell.frame 191
        [ReactiveTerminalCell.encodeDigest job.admissionId,
          ReactiveTerminalCell.encodeNat lease.requestContext.nonce] }
  postRootsBound := by simp
  guardsReadOnly := by simp

def body (_job : FeeFirstJob lease) : DataIntent M.rootBytes :=
  AuthorizedResourceCharge.admissionBodyIntent lease.runtime.prepayTransaction
    lease.runtime.resourceCell lease.manifest lease.accepted

def request (job : FeeFirstJob lease) : AdmissionPrologue.Request M.rootBytes where
  admissionId := job.admissionId
  principal := ⟨lease.requestContext.subject.value⟩
  height := lease.requestContext.height
  nonce := job.nonce
  prologue := job.prologue
  body := job.body

def grant (_job : FeeFirstJob lease) : AdmissionPrologue.Grant where
  principal := ⟨lease.requestContext.subject.value⟩
  nonceDomain := lease.manifest.semanticDigest
  notBefore := lease.requestContext.height
  notAfter := lease.requestContext.height
  maxFeeDebit := AuthorizedResourceCharge.exactCharge lease.manifest lease.accepted .feeDebit

theorem wellFormed (job : FeeFirstJob lease) : job.request.WellFormed where
  prologueTransaction := rfl
  distinctBodyTransaction := job.admissionPrepayDistinct.symm
  exactAdmissionNonce := rfl
  positiveFee := by
    simpa [prologue, AuthorizedResourceCharge.admissionCharge] using job.positiveFee
  bodyChargesNoAdmissionFee := AuthorizedResourceCharge.admissionBodyIntent_no_second_fee
    lease.runtime.prepayTransaction lease.runtime.resourceCell
      lease.manifest lease.accepted
  bodyDoesNotConsumeAdmissionNonce := by
    change job.nonce ∉ ([] : List StableNullifier)
    simp

def admitted (job : FeeFirstJob lease) : AdmissionPrologue.Request.Admitted M.rootBytes where
  grant := job.grant
  request := job.request
  wellFormed := job.wellFormed
  authorized :=
    { principal := rfl
      nonceDomain := rfl
      validFrom := Nat.le_refl _
      validUntil := Nat.le_refl _
      feeWithinGrant := Nat.le_refl _ }

def envelope (job : FeeFirstJob lease) : ProviderExecutionLease.OpenedLease.FeeFirstEnvelope lease where
  request := job.request
  wellFormed := job.wellFormed
  prologueExact := rfl
  bodyExact := rfl

/-- The scalar signed by resource authority is the exact prologue fee, the
body cannot debit that lane again, and all ten lanes recombine exactly. -/
theorem authorized_exact_split (job : FeeFirstJob lease) :
    (lease.requestContext.request lease.manifest lease.accepted).cost =
        job.request.prologue.exactCharge .feeDebit /\
      job.request.body.exactCharge .feeDebit = 0 /\
      job.request.prologue.exactCharge + job.request.body.exactCharge =
        AuthorizedResourceCharge.exactCharge lease.manifest lease.accepted :=
  job.envelope.exact_split

/-- Once the outer receipt is recorded, retry is an identity operation. -/
theorem recorded_retry_preserves_every_lane
    (job : FeeFirstJob lease) (before : AdmissionPrologue.AdmissionSnapshot M.rootBytes)
    (receipt : AdmissionPrologue.Receipt job.request) (data : DataSnapshot M.rootBytes) :
    (AdmissionPrologue.execute (before.record job.request receipt data) job.admitted).storeAfter
        (before.record job.request receipt data) =
      before.record job.request receipt data :=
  AdmissionPrologue.retry_does_not_double_charge before job.admitted receipt data

end FeeFirstJob

/-- A positive per-incidence tariff makes every canonical accepted operation
costed, independently of the sizes of its other nine lanes. -/
theorem exactFee_positive_of_incidence_price
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation}
    (manifest : AuthorizedResourceCharge.DeploymentManifest)
    (accepted : Accepted pre operation)
    (positive : 0 < manifest.tariff.unitFee .incidences) :
    0 < AuthorizedResourceCharge.exactCharge manifest accepted .feeDebit := by
  rw [AuthorizedResourceCharge.exactCharge_feeDebit]
  unfold AuthorizedResourceCharge.Tariff.billable
  have incidence :
      AuthorizedResourceCharge.operationalCharge manifest accepted .incidences = 1 := rfl
  rw [incidence, one_mul]
  omega

/-! ## Closed DreggNet purchase and lease -/

namespace Witness

noncomputable def marketFill :
    CanonicalEscrowMarket.Fill CanonicalResourceKernel.materializer demoPortal demoState :=
  CanonicalEscrowMarket.Witness.filled

/-- The public market fill buys two provider epochs at two quote units each.
The lease consumes precisely that quote asset and total. -/
def terms : ProviderExecutionLease.Terms where
  leaseId := 30
  holder := 3
  provider := 1
  asset := CanonicalEscrowMarket.Witness.terms.quoteAsset
  rate := CanonicalEscrowMarket.Witness.terms.unitQuote
  epochs := 2
  startsAt := 12

def leaseAdmission :
    Admission (logicalBook marketFill.feeAccepted.post.logical) terms.operation where
  sourcePresent := by
    change terms.operation.posting.source ∈
      (logicalBook CanonicalEscrowMarket.Witness.feeAccepted.post.logical).accounts
    rw [CanonicalEscrowMarket.Witness.feeAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.paymentAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.releaseAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.depositAccepted.post_logicalBook,
      Operation.apply_accounts, Operation.apply_accounts, Operation.apply_accounts,
      Operation.apply_accounts]
    decide
  destinationPresent := by
    change terms.operation.posting.destination ∈
      (logicalBook CanonicalEscrowMarket.Witness.feeAccepted.post.logical).accounts
    rw [CanonicalEscrowMarket.Witness.feeAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.paymentAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.releaseAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.depositAccepted.post_logicalBook,
      Operation.apply_accounts, Operation.apply_accounts, Operation.apply_accounts,
      Operation.apply_accounts]
    decide
  sourceSolvent := Or.inr (by
    change Int.ofNat terms.operation.posting.amount ≤
      (logicalBook CanonicalEscrowMarket.Witness.feeAccepted.post.logical).balance
        terms.operation.posting.source terms.operation.posting.asset
    rw [CanonicalEscrowMarket.Witness.feeAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.paymentAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.releaseAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.depositAccepted.post_logicalBook]
    decide)
  leaseWellFormed := by
    change 0 < terms.epochs /\
      (logicalBook marketFill.feeAccepted.post.logical).leases terms.leaseId = none
    constructor
    · decide
    · change
        (logicalBook CanonicalEscrowMarket.Witness.feeAccepted.post.logical).leases
          terms.leaseId = none
      rw [CanonicalEscrowMarket.Witness.feeAccepted.post_logicalBook,
        CanonicalEscrowMarket.Witness.paymentAccepted.post_logicalBook,
        CanonicalEscrowMarket.Witness.releaseAccepted.post_logicalBook,
        CanonicalEscrowMarket.Witness.depositAccepted.post_logicalBook]
      decide

noncomputable def accepted :
    Accepted marketFill.feeAccepted.post terms.operation :=
  Accepted.ofAdmission leaseAdmission

def endpoint : Digest := ⟨430⟩
def imageRoot : Digest := ⟨431⟩
def inputRoot : Digest := ⟨432⟩

def runtime : ProviderExecutionLease.Runtime where
  providerEndpoint := endpoint
  imageRoot := imageRoot
  inputRoot := inputRoot
  prepayTransaction := ⟨433⟩
  resourceCell := ⟨434⟩
  startTransaction := providerInvocationKey terms
    AuthorizedResourceCharge.witnessManifest endpoint imageRoot inputRoot
  startCell := ⟨435⟩
  terminalTransaction := ⟨436⟩
  terminalNullifier := ⟨437⟩
  terminalEvent := ⟨438⟩
  terminalCell := ⟨439⟩
  outboxCell := ⟨440⟩
  clockCell := ⟨441⟩
  openStartBytes := [4, 3, 0]
  openTerminalBytes := [4, 3, 1]
  openOutboxBytes := [4, 3, 2]
  prepayTerminalDistinct := by decide
  terminalOutboxDistinct := by decide
  terminalClockDistinct := by decide
  outboxClockDistinct := by decide
  terminalStartDistinct := by decide
  outboxStartDistinct := by decide

def requestContext : AuthorizedResourceCharge.RequestContext where
  domain := ⟨providerInvocationKey terms AuthorizedResourceCharge.witnessManifest
    endpoint imageRoot inputRoot |>.value⟩
  federation := ⟨3⟩
  subject := ⟨3⟩
  subjectKeyEpoch := 2
  nonce := 443
  height := 12
  policyId := ⟨9⟩
  policyEpoch := 5

noncomputable def authorization :
    Authorized demoPortal demoState
      (requestContext.request AuthorizedResourceCharge.witnessManifest accepted) where
  evidence := .signature () rfl rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

noncomputable def lease : ProviderExecutionLease.OpenedLease
    CanonicalResourceKernel.materializer demoPortal demoState
      marketFill.feeAccepted.post where
  terms := terms
  runtime := runtime
  manifest := AuthorizedResourceCharge.witnessManifest
  requestContext := requestContext
  accepted := accepted
  authorization := authorization

noncomputable def boundLease : BoundLease
    (M := CanonicalResourceKernel.materializer)
    (portal := demoPortal) (authState := demoState)
    (pre := marketFill.feeAccepted.post) where
  lease := lease
  exactProviderKey := rfl

def commercialBinding : CommercialBinding marketFill lease where
  holder := rfl
  provider := rfl
  asset := rfl
  capacity := rfl
  unitPrice := rfl

@[simp] theorem market_quote_is_exact_prepay :
    lease.prepaid = marketFill.base * marketFill.terms.unitQuote :=
  commercialBinding.exact_quote

@[simp] theorem purchased_capacity_and_prepay :
    lease.terms.epochs = 2 /\ lease.prepaid = 4 := by decide

set_option maxRecDepth 100000 in
def feeFirst : FeeFirstJob lease where
  admissionId := ⟨444⟩
  feeCell := ⟨445⟩
  feeNullifier := ⟨446⟩
  feeEvent := ⟨447⟩
  openFeeBytes := [0]
  paidFeeBytes := [1]
  admissionPrepayDistinct := by decide
  feeResourceDistinct := by decide
  positiveFee := exactFee_positive_of_incidence_price _ _ (by decide)

@[simp] theorem fee_first_exact_charge :
    (lease.requestContext.request lease.manifest lease.accepted).cost =
        feeFirst.request.prologue.exactCharge .feeDebit /\
      feeFirst.request.body.exactCharge .feeDebit = 0 /\
      feeFirst.request.prologue.exactCharge + feeFirst.request.body.exactCharge =
        AuthorizedResourceCharge.exactCharge lease.manifest lease.accepted :=
  feeFirst.authorized_exact_split

def admittedReceipt : AdmissionPrologue.Receipt feeFirst.request where
  bodyStatus := .committed

@[simp] theorem admitted_retry_is_identity
    (before : AdmissionPrologue.AdmissionSnapshot
      CanonicalResourceKernel.materializer.rootBytes)
    (data : DataSnapshot CanonicalResourceKernel.materializer.rootBytes) :
    (AdmissionPrologue.execute
      (before.record feeFirst.request admittedReceipt data)
      feeFirst.admitted).storeAfter
        (before.record feeFirst.request admittedReceipt data) =
      before.record feeFirst.request admittedReceipt data :=
  feeFirst.recorded_retry_preserves_every_lane before admittedReceipt data

@[simp] theorem prepay_exact_retry_is_free
    (schedule : Schedule)
    (before : DataSnapshot CanonicalResourceKernel.materializer.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before lease.prepayIntent) lease.prepayIntent =
      .replayed lease.prepayIntent.erase :=
  lease.prepay_retry_replays schedule before

@[simp] theorem provider_start_key_is_exact (height attempt : Nat) :
    (ProviderExecutionLease.startIntent lease height attempt).transactionId =
      providerInvocationKey terms AuthorizedResourceCharge.witnessManifest
        endpoint imageRoot inputRoot :=
  boundLease.start_uses_exact_provider_key height attempt

/-! ### Exact start and opaque completion -/

def startBoundary : ProviderExecutionLease.StartBoundary where
  Evidence := fun _ _ => Unit

noncomputable def startGrant : ProviderExecutionLease.StartGrant where
  grantId := ⟨450⟩
  principal := ⟨terms.holder⟩
  effectClass := .providerExecution
  target := endpoint
  actions := {ProviderExecutionLease.startAction lease}
  compensations := {ProviderExecutionLease.compensation lease}
  notBefore := 12
  notAfter := 20
  maxAttempt := 2

noncomputable def startAuthorized :
    startGrant.Authorizes (ProviderExecutionLease.startIntent lease 12 1) where
  principal := rfl
  effectClass := rfl
  target := rfl
  action := by
    change ProviderExecutionLease.startAction lease ∈
      ({ProviderExecutionLease.startAction lease} :
        Finset ProviderExecutionLease.StartAction)
    simp
  validFrom := by decide
  validUntil := by decide
  attempt := by decide
  compensation := by
    intro requested exact
    simp [ProviderExecutionLease.startIntent] at exact
    subst requested
    simp [startGrant]

def startReceipt : ProviderExecutionLease.StartReceipt where
  runId := ⟨451⟩
  providerEvidenceRoot := ⟨452⟩

def forwardPerformed : ProviderExecutionLease.StartObserved startBoundary
    (ProviderExecutionLease.startIntent lease 12 1) :=
  ⟨.performed startReceipt, ()⟩

noncomputable def idempotentStart :
    IdempotentProviderStart boundLease startBoundary 12 1 where
  first := forwardPerformed
  retry := forwardPerformed
  sameObservation := rfl

@[simp] theorem provider_retry_returns_same_observation :
    idempotentStart.retry.observation = idempotentStart.first.observation :=
  idempotentStart.sameObservation

noncomputable def completedAttempt :
    ProviderExecutionLease.StartAttempt lease startBoundary where
  height := 12
  attempt := 1
  grant := startGrant
  authorized := startAuthorized
  currentRoot := (ProviderExecutionLease.startIntent lease 12 1).expectedPreRoot
  forward := forwardPerformed
  plan := .commit

/-- The kernel sees only a claim and a root-binding predicate.  In particular,
the `outputRoot` is not interpreted as proof of correct execution here. -/
def completionBoundary : ProviderExecutionLease.CompletionBoundary completedAttempt where
  Evidence := fun claim => claim.providerEvidenceRoot =
    ⟨Nat.pair claim.runId.value
      (Nat.pair claim.outputRoot.value claim.usageRoot.value)⟩
  rootBound := fun _ evidence => evidence

def completionClaim : ProviderExecutionLease.CompletionClaim where
  runId := ⟨451⟩
  outputRoot := ⟨453⟩
  usageRoot := ⟨454⟩
  providerEvidenceRoot := ⟨Nat.pair 451 (Nat.pair 453 454)⟩

noncomputable def completedOutcome :
    ProviderExecutionLease.Outcome completedAttempt completionBoundary 20 19 :=
  .completed completionClaim rfl rfl (by decide)

noncomputable def completedPlan :=
  ProviderExecutionLease.terminalPlan completedOutcome

@[simp] theorem opaque_completion_is_finalized :
    completedPlan.kind = .finalized := rfl

@[simp] theorem completion_has_no_second_charge :
    completedPlan.intent.exactCharge = 0 :=
  ProviderExecutionLease.terminal_settlement_has_no_second_charge completedOutcome

noncomputable def terminalBeforeBytes (cellId : CellId) : List UInt8 :=
  if cellId = runtime.terminalCell then runtime.openTerminalBytes
  else if cellId = runtime.outboxCell then runtime.openOutboxBytes
  else if cellId = runtime.clockCell then completedPlan.clockBytes
  else if cellId = runtime.startCell then
    List.replicate completedPlan.triggerRoot.value 0
  else []

noncomputable def terminalBeforeModel :
    Snapshot TransactionId CellId StableNullifier ReplayEnvelope where
  roots := fun cellId => CanonicalResourceKernel.materializer.rootBytes
    (terminalBeforeBytes cellId)
  consumed := fun _ => false
  available := 0
  history := []
  journal := []

noncomputable def terminalBefore :
    DataSnapshot CanonicalResourceKernel.materializer.rootBytes where
  model := terminalBeforeModel
  canonicalBytes := terminalBeforeBytes
  coherent := fun _ => rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
@[simp] theorem completedReady :
    completedPlan.intent.preflight terminalBefore = .ok () := by
  decide

@[simp] theorem completion_commits_terminal_and_outbox :
    DurableDataIntent.execute .complete terminalBefore completedPlan.intent =
      .accepted (DataSnapshot.install terminalBefore completedPlan.intent) :=
  ReactiveTerminalCell.Plan.complete_ready completedPlan terminalBefore
    (by decide) completedReady

@[simp] theorem completion_retry_is_exact_replay :
    DurableDataIntent.execute .complete
        (DataSnapshot.install terminalBefore completedPlan.intent)
        completedPlan.intent = .replayed completedPlan.intent.erase :=
  ProviderExecutionLease.terminal_retry_replays completedOutcome .complete terminalBefore

/-! ### Cancel, expiry, and separately authorized refund -/

def forwardRefused : ProviderExecutionLease.StartObserved startBoundary
    (ProviderExecutionLease.startIntent lease 12 1) :=
  ⟨.notPerformed .refused, ()⟩

noncomputable def refusedAttempt :
    ProviderExecutionLease.StartAttempt lease startBoundary where
  height := 12
  attempt := 1
  grant := startGrant
  authorized := startAuthorized
  currentRoot := (ProviderExecutionLease.startIntent lease 12 1).expectedPreRoot
  forward := forwardRefused
  plan := .commit

def refusedCompletionBoundary :
    ProviderExecutionLease.CompletionBoundary refusedAttempt where
  Evidence := fun claim => claim.providerEvidenceRoot =
    ⟨Nat.pair claim.runId.value
      (Nat.pair claim.outputRoot.value claim.usageRoot.value)⟩
  rootBound := fun _ evidence => evidence

noncomputable def cancelledOutcome :
    ProviderExecutionLease.Outcome refusedAttempt refusedCompletionBoundary 20 13 :=
  .cancelled rfl (by decide)

noncomputable def expiredOutcome :
    ProviderExecutionLease.Outcome completedAttempt completionBoundary 20 21 :=
  .expired (by decide)

@[simp] theorem refused_start_cancels_and_refunds :
    (ProviderExecutionLease.terminalPlan cancelledOutcome).kind = .cancelled /\
      cancelledOutcome.RefundDue := by
  constructor
  · rfl
  · unfold cancelledOutcome ProviderExecutionLease.Outcome.RefundDue
    trivial

@[simp] theorem expiry_expires_and_refunds :
    (ProviderExecutionLease.terminalPlan expiredOutcome).kind = .expired /\
      expiredOutcome.RefundDue := by
  constructor
  · rfl
  · unfold expiredOutcome ProviderExecutionLease.Outcome.RefundDue
    trivial

@[simp] theorem expiry_cannot_overwrite_completion :
    DurableDataIntent.execute .complete
        (DataSnapshot.install terminalBefore completedPlan.intent)
        (ProviderExecutionLease.terminalPlan expiredOutcome).intent =
      .rejected (.durable .transactionConflict) := by
  exact ProviderExecutionLease.distinct_provider_terminals_conflict
    completedOutcome expiredOutcome (by decide) .complete terminalBefore

def refundAdmission :
    Admission (logicalBook accepted.post.logical) terms.refundOperation where
  sourcePresent := by
    change terms.refundOperation.posting.source ∈
      (terms.operation.apply
        (logicalBook CanonicalEscrowMarket.Witness.feeAccepted.post.logical)).accounts
    rw [Operation.apply_accounts,
      CanonicalEscrowMarket.Witness.feeAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.paymentAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.releaseAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.depositAccepted.post_logicalBook,
      Operation.apply_accounts, Operation.apply_accounts, Operation.apply_accounts,
      Operation.apply_accounts]
    decide
  destinationPresent := by
    change terms.refundOperation.posting.destination ∈
      (terms.operation.apply
        (logicalBook CanonicalEscrowMarket.Witness.feeAccepted.post.logical)).accounts
    rw [Operation.apply_accounts,
      CanonicalEscrowMarket.Witness.feeAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.paymentAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.releaseAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.depositAccepted.post_logicalBook,
      Operation.apply_accounts, Operation.apply_accounts, Operation.apply_accounts,
      Operation.apply_accounts]
    decide
  sourceSolvent := Or.inr (by
    change Int.ofNat terms.refundOperation.posting.amount ≤
      (terms.operation.apply
        (logicalBook CanonicalEscrowMarket.Witness.feeAccepted.post.logical)).balance
          terms.refundOperation.posting.source terms.refundOperation.posting.asset
    rw [CanonicalEscrowMarket.Witness.feeAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.paymentAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.releaseAccepted.post_logicalBook,
      CanonicalEscrowMarket.Witness.depositAccepted.post_logicalBook]
    decide)
  leaseWellFormed := trivial

noncomputable def refundAccepted :
    Accepted accepted.post terms.refundOperation :=
  Accepted.ofAdmission refundAdmission

def refundContext : AuthorizedResourceCharge.RequestContext where
  domain := ⟨460⟩
  federation := ⟨3⟩
  subject := ⟨3⟩
  subjectKeyEpoch := 2
  nonce := 461
  height := 21
  policyId := ⟨9⟩
  policyEpoch := 5

noncomputable def refundAuthorization :
    Authorized demoPortal demoState
      (refundContext.request AuthorizedResourceCharge.witnessManifest
        refundAccepted) where
  evidence := .signature () rfl rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

theorem expiredRefundDue : expiredOutcome.RefundDue := by
  unfold expiredOutcome ProviderExecutionLease.Outcome.RefundDue
  trivial

noncomputable def refundPlan :
    ProviderExecutionLease.RefundPlan expiredOutcome expiredRefundDue where
  transactionId := ⟨462⟩
  resourceCell := runtime.resourceCell
  requestContext := refundContext
  accepted := refundAccepted
  authorization := refundAuthorization

@[simp] theorem refund_is_fresh_authority :
    refundPlan.requestContext.request lease.manifest refundPlan.accepted ≠
      lease.requestContext.request lease.manifest lease.accepted :=
  refundPlan.request_ne_prepay

@[simp] theorem refund_retry_is_exact_replay
    (schedule : Schedule)
    (before : DataSnapshot CanonicalResourceKernel.materializer.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before refundPlan.intent) refundPlan.intent =
      .replayed refundPlan.intent.erase :=
  refundPlan.exact_retry_replays schedule before

/-! ### Closed stale-tariff and stale-lease teeth -/

def staleTariff : AuthorizedResourceCharge.Tariff :=
  { AuthorizedResourceCharge.witnessManifest.tariff with networkCopies := 2 }

def staleManifest : AuthorizedResourceCharge.DeploymentManifest :=
  { AuthorizedResourceCharge.witnessManifest with tariff := staleTariff }

def equalProductStaleTerms : ProviderExecutionLease.Terms :=
  { terms with rate := 1, epochs := 4 }

@[simp] theorem stale_tariff_cannot_reuse_provider_key :
    runtime.startTransaction ≠
      providerInvocationKey terms staleManifest endpoint imageRoot inputRoot :=
  boundLease.stale_manifest_key_rejected staleManifest (by
    change staleManifest ≠ AuthorizedResourceCharge.witnessManifest
    intro same
    have copies := congrArg
      (fun manifest : AuthorizedResourceCharge.DeploymentManifest =>
        manifest.tariff.networkCopies) same
    norm_num [staleManifest, staleTariff,
      AuthorizedResourceCharge.witnessManifest] at copies)

@[simp] theorem stale_equal_product_lease_cannot_reuse_provider_key :
    terms.prepaid = equalProductStaleTerms.prepaid /\
      runtime.startTransaction ≠
        providerInvocationKey equalProductStaleTerms
          AuthorizedResourceCharge.witnessManifest endpoint imageRoot inputRoot := by
  constructor
  · decide
  · exact boundLease.stale_lease_key_rejected equalProductStaleTerms (by decide)

/-! ### Exact replicated finality for the durable terminal payload -/

abbrev ReplicaNode := Fin 3

def quorumCore : Finset ReplicaNode := {0, 1}

def quorums : QuorumSystem ReplicaNode where
  isQuorum voters := quorumCore ⊆ voters
  intersects := by
    intro left right leftQ rightQ
    refine ⟨0, leftQ ?_, rightQ ?_⟩ <;> simp [quorumCore]

noncomputable def terminalCandidate :
    Candidate TransactionId CellId StableNullifier ReplayEnvelope :=
  Candidate.ofData 9 [] completedPlan.intent

noncomputable def voteBook : VoteBook
    (Node := ReplicaNode) (TxId := TransactionId) (CellId := CellId)
    (Nullifier := StableNullifier) (Event := ReplayEnvelope) :=
  fun _ => [terminalCandidate]

noncomputable def prefixDiscipline : PrefixDiscipline voteBook where
  compatible := by
    intro node left right leftVote rightVote
    simp only [voteBook, List.mem_singleton] at leftVote rightVote
    subst left
    subst right
    exact Or.inl List.prefix_rfl

noncomputable def finalityCertificate :
    Finalized quorums voteBook terminalCandidate where
  voters := quorumCore
  quorum := fun _ member => member
  voted := by simp [voteBook]

@[simp] theorem finalized_exact_terminal_payload :
    terminalCandidate.intent = completedPlan.intent.erase := rfl

theorem no_other_finalized_payload_at_terminal_slot
    {other : Candidate TransactionId CellId StableNullifier ReplayEnvelope}
    (otherFinal : Finalized quorums voteBook other)
    (sameSlot : terminalCandidate.slot = other.slot) :
    other.intent = completedPlan.intent.erase := by
  have exact := finalized_transaction_unique_at_slot prefixDiscipline
    finalityCertificate otherFinal sameSlot
  simpa using exact.symm

end Witness

/-! ## Explicit deployment ceilings -/

/-- Supplying this record is what turns the closed logical witness into a
claim about a particular cloud and storage deployment.  None of its fields is
constructed above. -/
structure DeploymentRefinement
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : ProviderExecutionLease.OpenedLease M portal authState pre}
    {boundary : ProviderExecutionLease.StartBoundary}
    (attempt : ProviderExecutionLease.StartAttempt lease boundary)
    (completion : ProviderExecutionLease.CompletionBoundary attempt)
    (terminalIntent : DataIntent M.rootBytes) where
  PhysicalRun : Type
  RepresentsClaim : PhysicalRun → ProviderExecutionLease.CompletionClaim → Prop
  completionSound : ProviderExecutionLease.CompletionRefinement completion
    PhysicalRun RepresentsClaim
  ExecutionCorrect : PhysicalRun → Prop
  evidenceImpliesCorrect : ∀ claim, completion.Evidence claim →
    ∀ run, RepresentsClaim run claim → ExecutionCorrect run
  PhysicalState : Type
  PhysicalStep : PhysicalState → DataIntent M.rootBytes → PhysicalState → Type
  RepresentsStore : PhysicalState → DataSnapshot M.rootBytes → Prop
  durableRefinement : ImplementationRefinement M.rootBytes
    PhysicalState PhysicalStep RepresentsStore
  CloudApiRefinesStart : Prop
  CloudApiRefinesIdempotency : Prop
  AuthenticatedVotesRefineBook : Prop
  NetworkConsensusSafety : Prop
  NetworkEventuallyDelivers : Prop
  ProviderEventuallyTerminates : Prop

/-! ## Axiom audit for the new load-bearing joints -/

/-- info: 'Minidregg.Assurance.DreggNetProviderConsumer.different_manifest_changes_provider_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms different_manifest_changes_provider_key
/-- info: 'Minidregg.Assurance.DreggNetProviderConsumer.FeeFirstJob.authorized_exact_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FeeFirstJob.authorized_exact_split
/-- info: 'Minidregg.Assurance.DreggNetProviderConsumer.Witness.completion_retry_is_exact_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.completion_retry_is_exact_replay
/-- info: 'Minidregg.Assurance.DreggNetProviderConsumer.Witness.no_other_finalized_payload_at_terminal_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.no_other_finalized_payload_at_terminal_slot

end Minidregg.Assurance.DreggNetProviderConsumer
