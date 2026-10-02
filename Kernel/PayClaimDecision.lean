/-
Closed claim recovery decision, awaiting the integrator's authorized Lean pass.

The receiver supplies authenticated pay, authority and Clock snapshots and checks
both expected physical roots before calling this leaf. Checked possession binds
the whole closed command, domain and current semantics. The receiver commits the
returned pay patch together with the prepared V2 legs and operation nonce in one
intent. No original deposit is rewritten or observed a second time.
-/
import Kernel.PayEnrolV2Legs
import Kernel.PayPendingRotation
import Kernel.PayChainTip

namespace Minidregg.Kernel.PayClaimDecision

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Theory.Store (Store Patch)
open Minidregg.Theory.CredentialAuthorityState (currentSigningKey signingKeyRevocation keyStanding)
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff (Tariff)

set_option autoImplicit false

abbrev Pricing := PayEnrolV2Decision.Pricing
abbrev Authority := CredentialAuthorityDomain.Snapshot
abbrev Request := PayEnrolClaim.AcceptRequest
abbrev Origin := PayEnrolClaim.Claim
abbrev Consumption := PayEnrolClaim.Consumption

inductive Reject where
  | invalidSignature | authorityDomainMismatch | missingClaim | malformedClaim
  | malformedMemo | deploymentMismatch | recipientMismatch | tariffInvalid
  | selfEnrolOff | floatUnavailable | invalidEconomics | invalidOwner
  | authorityUnavailable | subjectTaken | pendingOwnerMissing | pendingHistoryMismatch
  | sshKeyTaken | sshKeyMismatch
  | freshness (reason : PayChainTip.FreshnessReject)
  | quote (reason : PayEnrolClaim.QuoteReject)
  | acceptance (reason : PayEnrolClaim.Reject)
  | rotation (reason : PayPendingRotation.Reject)
  deriving DecidableEq, Repr

/-- A pending owner has a real NEXT. Acceptance needs only the current registry
identity/key/epoch; it never synthesizes pending custody for an admitted member. -/
inductive Owner where
  | pending (owner : PayEnrolClaim.PendingOwner)
  | admitted (owner : PayEnrolClaim.CurrentOwner) (before : EnrolRecord)
  deriving DecidableEq, Repr

def Owner.current : Owner → PayEnrolClaim.CurrentOwner
  | .pending owner => owner.toCurrentOwner
  | .admitted owner _ => owner

def Owner.mode : Owner → PayEnrolClaim.Mode
  | .pending _ => .enroll
  | .admitted _ _ => .renew

def Owner.birthFee (pricing : Pricing) : Owner → Nat
  | .pending _ => pricing.birthFee
  | .admitted _ _ => 0

/-- No historical signing key or retained pending row is current authority after
admission. History is checked only as provenance of exact current pending custody. -/
def resolveOwner (pay : PayStore) (authority : Authority) (identity : List UInt8) :
    Except Reject Owner :=
  let subject : SubjectId := ⟨PayEnrolMemo.subjectOf identity⟩
  match enrolmentAt pay identity with
  | some before =>
    match currentSigningKey authority.logical subject with
    | none => .error .authorityUnavailable
    | some key =>
      let owner : PayEnrolClaim.CurrentOwner := ⟨identity, key.publicKey, key.keyEpoch⟩
      if owner.valid ∧ key.subject = subject.value ∧
          key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
          keyStanding authority.cell (signingKeyRevocation key) = .live ∧
          key.activeFrom ≤ authority.revision ∧ authority.revision ≤ key.activeUntil then
        .ok (.admitted owner before)
      else .error .authorityUnavailable
  | none =>
    if (authority.logical ⟨.subjectKeyEpoch, subject⟩).isSome then .error .subjectTaken
    else
      match pendingOwnerAt pay identity with
      | none => .error .pendingOwnerMissing
      | some owner =>
        if ¬owner.valid ∨ owner.identityKey ≠ identity then .error .invalidOwner
        else if pendingOwnerHistoryAt pay identity owner.epoch ≠ some owner then
          .error .pendingHistoryMismatch
        else .ok (.pending owner)

structure EnrolPlan where
  input : PayEnrolV2Legs.EnrolInput
  tip : ChainTip
  sshBlob : List UInt8
  index : Option Nat
  leaseUntil : Nat
  deriving DecidableEq, Repr

structure RenewPlan where
  input : PayEnrolV2Legs.RenewInput
  tip : ChainTip
  leaseFrom : Nat
  leaseUntil : Nat
  deriving DecidableEq, Repr

inductive AcceptancePlan where
  | enrol (plan : EnrolPlan)
  | renew (plan : RenewPlan)
  deriving DecidableEq, Repr

def AcceptancePlan.economic : AcceptancePlan → PayEnrolV2Legs.EconomicInput
  | .enrol plan => plan.input.economic
  | .renew plan => plan.input.economic

def AcceptancePlan.origin (plan : AcceptancePlan) : Origin := plan.economic.origin

def AcceptancePlan.consumption (plan : AcceptancePlan) : Consumption := plan.economic.consumption

def AcceptancePlan.tip : AcceptancePlan → ChainTip
  | .enrol plan => plan.tip
  | .renew plan => plan.tip

def AcceptancePlan.input : AcceptancePlan → PayEnrolV2Legs.Input
  | .enrol plan => .enrol plan.input
  | .renew plan => .renew plan.input

/-- Reading the exact retained origin and allocating its first consumption is
common to both admission variants. Origin bytes, reason and original quote stay. -/
def consumptionPatch (origin : Origin) (consumed : Consumption) : Patch PayCell.layout :=
  [.read .claim origin.id (some origin),
   .allocate .claimConsumption origin.id consumed]

/-- account is the actual prepared birth account. enrolledSlot is acceptance's
fresh finalized tip, rather than reviving the old deposit's slot as admission time. -/
def EnrolPlan.patch (plan : EnrolPlan) (account : Nat) : Patch PayCell.layout :=
  consumptionPatch plan.input.economic.origin plan.input.economic.consumption ++
  [.allocate .enrolment plan.input.economic.identityKey
      ⟨plan.sshBlob, account, plan.index, plan.leaseUntil, plan.tip.slot⟩,
   .allocate .sshIndex plan.sshBlob plan.input.economic.identityKey] ++
  match plan.index with | none => [] | some index => [.allocate .assignment index account]

def RenewPlan.patch (plan : RenewPlan) : Patch PayCell.layout :=
  consumptionPatch plan.input.economic.origin plan.input.economic.consumption ++
  [.write .enrolment plan.input.economic.identityKey plan.input.before
    { plan.input.before with leaseUntil := plan.leaseUntil }]

def AcceptancePlan.payPatch (plan : AcceptancePlan) (account : Nat) : Patch PayCell.layout :=
  match plan with
  | .enrol plan => plan.patch account
  | .renew plan => plan.patch

inductive Decision where
  | accept (plan : AcceptancePlan)
  | rotate (patch : Patch PayCell.layout)

def Decision.input : Decision → PayEnrolV2Legs.Input
  | .accept plan => plan.input
  | .rotate _ => .noCredit

def Decision.payPatch (value : Decision) (account : Nat) : Patch PayCell.layout :=
  match value with
  | .accept plan => plan.payPatch account
  | .rotate patch => patch

def Decision.mintedCredit : Decision → Nat
  | .accept plan => plan.consumption.mintedCredit
  | .rotate _ => 0

/-- Current mode comes from source ownership, not the original memo's mode. A
second initial payment can explicitly be accepted as renewal after admission. -/
def makePlan (pay : PayStore) (tip : ChainTip) (origin : Origin) (consumed : Consumption)
    (memo : PayEnrolMemoV2.Memo) (float : Nat) (owner : Owner) : AcceptancePlan :=
  match owner with
  | .pending pending => .enrol {
      input := PayEnrolV2Legs.ofAcceptedEnrol origin consumed float pending
      tip := tip
      sshBlob := PayEnrolMemo.sshBlobOf memo.unsigned.sshKey
      index := if nextFree pay < bookSize pay then some (nextFree pay) else none
      leaseUntil := tip.hour + 168 * consumed.terms.requestedWeeks }
  | .admitted _ before =>
      let start := max before.leaseUntil tip.hour
      .renew {
        input := PayEnrolV2Legs.ofAcceptedRenew origin consumed float before
        tip := tip
        leaseFrom := start
        leaseUntil := start + 168 * consumed.terms.requestedWeeks }

/-- Low-level pure preparation, called only beneath Checked possession in decide.
Source leg preconditions are checked here too, so acceptance returns executable
physical input rather than merely plausible economic data. -/
private def acceptRequest (pay : PayStore) (authority : Authority) (clock : ClockCell.Clock)
    (pricing : Pricing) (request : Request) : Except Reject AcceptancePlan := do
  let tip ← (PayChainTip.fresh clock (chainTipOf pay)).mapError Reject.freshness
  let origin ← match claimAt pay request.claimId with
    | none => .error .missingClaim | some origin => .ok origin
  if ¬origin.valid ∨ claimMemoCoherent origin ≠ true then throw .malformedClaim
  if origin.reason.isNone then throw (.acceptance .notPending)
  if (claimConsumptionAt pay origin.id).isSome then throw (.acceptance .alreadyConsumed)
  let memo ← match PayEnrolMemoV2.parse origin.rawMemo with
    | .error _ => .error .malformedMemo | .ok memo => .ok memo
  let tariff ← match tariffOf pay with
    | none => .error .tariffInvalid | some tariff => .ok tariff
  if ¬tariff.valid then throw .tariffInvalid
  let enrolIndex ← match tariff.enrolIndex with
    | none => .error .selfEnrolOff | some index => .ok index
  if bookAt pay enrolIndex ≠ some origin.original.recipient then throw .recipientMismatch
  if memo.unsigned.deploymentCommitment ≠ PayEnrolPricing.deploymentCommitment
      pricing.domain pricing.expectedSeed tariff origin.original.recipient then
    throw .deploymentMismatch
  let float ← match assignmentAt pay enrolIndex with
    | none => .error .floatUnavailable | some account => .ok account
  let owner ← resolveOwner pay authority origin.ownerIdentityKey
  let birthFee := owner.birthFee pricing
  let quote ← (PayEnrolClaim.quoteFixed origin.original.amountAtomic tariff birthFee
    request.requestedWeeks request.minimumStarterCredit).mapError Reject.quote
  let commitment := PayEnrolPricing.pricingCommitment pricing.semantics tariff
    pricing.creation pricing.template owner.mode quote
  let consumed ← (PayEnrolClaim.accept origin (claimConsumptionAt pay origin.id)
    owner.current tariff birthFee owner.mode commitment tip.hour request).mapError Reject.acceptance
  let plan := makePlan pay tip origin consumed memo float owner
  if ¬PayEnrolV2Legs.EconomicReady pay tariff plan.economic then throw .invalidEconomics
  match plan with
  | .enrol enrol =>
    if ¬PayEnrolV2Legs.OwnerReady pay enrol.input then throw .invalidOwner
    if (sshIndexAt pay enrol.sshBlob).isSome then throw .sshKeyTaken
    return plan
  | .renew renew =>
    if renew.input.before.sshBlob ≠ PayEnrolMemo.sshBlobOf memo.unsigned.sshKey then
      throw .sshKeyMismatch
    return plan

/-- The only closed decision entry point. Rotation does not consult chain time;
its proof is successor possession plus the source NEXT precommitment gate.
Physical roots and replay nonce remain the enclosing receiver's responsibility. -/
def decide (pay : PayStore) (authority : Authority) (clock : ClockCell.Clock)
    (pricing : Pricing) (ingress : PayClaimCommand.DecodedIngress)
    (checked : PayClaimCommand.Checked pricing.domain pricing.semantics ingress) :
    Except Reject Decision :=
  if !checked.valid then .error .invalidSignature
  else if authority.domain ≠ pricing.domain then .error .authorityDomainMismatch
  else
    match ingress.command.action with
    | .inl request => (acceptRequest pay authority clock pricing request).map Decision.accept
    | .inr _ => (PayPendingRotation.decidedPatch pay authority.logical ingress checked)
        |>.mapError Reject.rotation |>.map Decision.rotate

/-! Source obligations for the receiver's composition. -/

theorem invalid_signature_refuses (pay : PayStore) (authority : Authority)
    (clock : ClockCell.Clock) (pricing : Pricing) (ingress : PayClaimCommand.DecodedIngress)
    (checked : PayClaimCommand.Checked pricing.domain pricing.semantics ingress)
    (invalid : checked.valid = false) :
    decide pay authority clock pricing ingress checked = .error .invalidSignature := by
  simp [decide, invalid]

theorem success_requires_signature (pay : PayStore) (authority : Authority)
    (clock : ClockCell.Clock) (pricing : Pricing) (ingress : PayClaimCommand.DecodedIngress)
    (checked : PayClaimCommand.Checked pricing.domain pricing.semantics ingress)
    (result : Decision) (accepted : decide pay authority clock pricing ingress checked = .ok result) :
    checked.valid = true := by
  cases valid : checked.valid with
  | false => simp [decide, valid] at accepted
  | true => rfl

theorem admitted_missing_registry_refuses (pay : PayStore) (authority : Authority)
    (identity : List UInt8) (before : EnrolRecord)
    (admitted : enrolmentAt pay identity = some before)
    (missing : currentSigningKey authority.logical ⟨PayEnrolMemo.subjectOf identity⟩ = none) :
    resolveOwner pay authority identity = .error .authorityUnavailable := by
  simp [resolveOwner, admitted, missing]

theorem rotation_independent_of_clock (pay : PayStore) (authority : Authority)
    (left right : ClockCell.Clock) (pricing : Pricing) (ingress : PayClaimCommand.DecodedIngress)
    (checked : PayClaimCommand.Checked pricing.domain pricing.semantics ingress)
    (rotation : PayClaimCommand.RotatePendingOwner)
    (action : ingress.command.action = .inr rotation) :
    decide pay authority left pricing ingress checked =
      decide pay authority right pricing ingress checked := by
  simp [decide, action]

theorem rotation_no_credit (patch : Patch PayCell.layout) :
    (Decision.rotate patch).input = .noCredit ∧
    (Decision.rotate patch).mintedCredit = 0 := ⟨rfl, rfl⟩

theorem makePlan_retains_origin (pay : PayStore) (tip : ChainTip) (origin : Origin)
    (consumed : Consumption) (memo : PayEnrolMemoV2.Memo) (float : Nat) (owner : Owner) :
    (makePlan pay tip origin consumed memo float owner).origin = origin ∧
    (makePlan pay tip origin consumed memo float owner).consumption = consumed := by
  cases owner <;> exact ⟨rfl, rfl⟩

theorem pending_plan_keeps_current_owner (pay : PayStore) (tip : ChainTip)
    (origin : Origin) (consumed : Consumption) (memo : PayEnrolMemoV2.Memo)
    (float : Nat) (owner : PayEnrolClaim.PendingOwner) :
    (makePlan pay tip origin consumed memo float (.pending owner)).input =
      .enrol (PayEnrolV2Legs.ofAcceptedEnrol origin consumed float owner) := rfl

theorem consumption_patch_preserves_origin (pay : PayStore) (origin : Origin)
    (consumed : Consumption) (id : List UInt8) :
    claimAt (Patch.run pay (consumptionPatch origin consumed)) id = claimAt pay id := by
  apply Patch.run_frame
  simp [consumptionPatch, Patch.writeFootprint, Store.Op.writeAddress?, Store.Op.address,
    claimAddress]

theorem consumption_patch_consumes (pay : PayStore) (origin : Origin)
    (consumed : Consumption) :
    claimConsumptionAt (Patch.run pay (consumptionPatch origin consumed)) origin.id =
      some consumed := Minidregg.Theory.Store.Store.set_eq _ _ _

theorem enrol_patch_preserves_origin (pay : PayStore) (plan : EnrolPlan)
    (account : Nat) (id : List UInt8) :
    claimAt (Patch.run pay (plan.patch account)) id = claimAt pay id := by
  apply Patch.run_frame
  cases indexed : plan.index <;>
    simp [EnrolPlan.patch, indexed, consumptionPatch, Patch.writeFootprint,
      Store.Op.writeAddress?, Store.Op.address, claimAddress]

theorem renew_patch_preserves_origin (pay : PayStore) (plan : RenewPlan) (id : List UInt8) :
    claimAt (Patch.run pay plan.patch) id = claimAt pay id := by
  apply Patch.run_frame
  simp [RenewPlan.patch, consumptionPatch, Patch.writeFootprint,
    Store.Op.writeAddress?, Store.Op.address, claimAddress]

theorem renew_patch_preserves_pending_owner (pay : PayStore) (plan : RenewPlan)
    (identity : List UInt8) :
    pendingOwnerAt (Patch.run pay plan.patch) identity = pendingOwnerAt pay identity := by
  apply Patch.run_frame
  simp [RenewPlan.patch, consumptionPatch, Patch.writeFootprint,
    Store.Op.writeAddress?, Store.Op.address, pendingOwnerAddress]

#assert_axioms invalid_signature_refuses
#assert_axioms success_requires_signature
#assert_axioms admitted_missing_registry_refuses
#assert_axioms rotation_independent_of_clock
#assert_axioms rotation_no_credit
#assert_axioms makePlan_retains_origin
#assert_axioms pending_plan_keeps_current_owner
#assert_axioms consumption_patch_preserves_origin
#assert_axioms consumption_patch_consumes
#assert_axioms enrol_patch_preserves_origin
#assert_axioms renew_patch_preserves_origin
#assert_axioms renew_patch_preserves_pending_owner

end Minidregg.Kernel.PayClaimDecision
