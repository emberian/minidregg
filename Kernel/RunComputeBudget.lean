/-!
# RunComputeBudget — admitted execution quota and existing Book consumption

Preparation component for the after-core PayCell v5 profile. The receiver
loads the deployment's actual PayCell, clock and Book, authorizes the signed
funding account leg, and commits usage, credit burn and invocation effects in
ONE durable intent. Exact replay is resolved before pricing again.

Usage is keyed by the authenticated execution subject, independently of the
optional funding account. Missing usage means zero only AFTER the source-
authenticated append-only computeActivation record permits the clock day.
A neutral v4→v5 codec lift leaves activation absent and cannot reset history.

No new monetary ledger: paid steps burn the existing PayTariff credit asset
in CanonicalResourceKernel.Book. Transaction9 has an explicit compute-funding payload. Its signed account
leg supplies exact consent; syntactic funding is not capability/signature authority.
Unauthenticated dry-run requests cannot debit a caller-supplied subject.
-/
import Compiler.WorldExecutionContract
import Kernel.ClockCell
import Kernel.PayCell
import Compiler.CanonicalResourcePageMaterializer

namespace Minidregg.Kernel.RunComputeBudget

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Store (Patch)

set_option autoImplicit false

def freeStepsPerDay : Nat := WorldExecutionContract.freeStepsPerDay

/-- Exact marginal paid steps, including a call straddling the free threshold. -/
def paidSteps (used steps : Nat) : Nat :=
  steps - (freeStepsPerDay - used)

theorem paidSteps_le_steps (used steps : Nat) : paidSteps used steps ≤ steps :=
  Nat.sub_le _ _

theorem paidSteps_cumulative (used steps : Nat) :
    paidSteps used steps =
      (used + steps - freeStepsPerDay) - (used - freeStepsPerDay) := by
  unfold paidSteps
  omega

/-- Splitting a day's execution cannot create another free allowance. -/
theorem paidSteps_split (used first second : Nat) :
    paidSteps used first + paidSteps (used + first) second =
      paidSteps used (first + second) := by
  simp only [paidSteps_cumulative]
  omega

structure Quote where
  subject : SubjectId
  day : Nat
  usedBefore : Nat
  steps : Nat
  credits : Nat
  deriving DecidableEq, Repr

inductive Reject where
  | computeInactive
  | activationInvalid
  | beforeActivation
  | usageBeforeActivation
  | clockBeforeUsage
  | stalePayRoot
  | usagePatch (reason : CellState.RejectReason)
  | missingFunding
  | malformedFunding
  | tariffInvalid
  | fundingAmount
  | payerIsIssuer
  | stalePayerBalance
  | staleWellBalance
  | bookRefused
  | checkedStepsChanged
  deriving DecidableEq, Repr

/-- Pure quote over source-loaded activation, clock and that subject's usage.
A future stored day or a row predating the activated era fails closed. -/
def quote (subject : SubjectId) (clock : ClockCell.Clock)
    (activation : PayCell.ComputeActivation) (before : Option PayCell.ComputeUsage)
    (steps : Nat) : Except Reject Quote := do
  if !decide activation.valid then throw .activationInvalid
  let day := clock.now / ClockCell.secondsPerDay
  if day < activation.day then throw .beforeActivation
  let used ← match before with
    | none => pure 0
    | some usage => do
      if usage.day < activation.day then throw .usageBeforeActivation
      if day < usage.day then throw .clockBeforeUsage
      pure (if usage.day = day then usage.admittedSteps else 0)
  pure ⟨subject, day, used, steps, paidSteps used steps⟩

def Quote.after (quoted : Quote) : PayCell.ComputeUsage :=
  ⟨quoted.day, quoted.usedBefore + quoted.steps⟩

/-- The typed usage row alone changes. Every other PayCell namespace, including
activation, paid claims and pending custody, is preserved by this patch. -/
def usagePatch (subject : SubjectId) (before : Option PayCell.ComputeUsage)
    (after : PayCell.ComputeUsage) : Patch PayCell.layout :=
  match before with
  | none => [.allocate .computeUsage subject.value after]
  | some old => [.write .computeUsage subject.value old after]

/-- Existing payment/custody rows and other subjects are outside this update. -/
theorem usagePatch_frame (store : PayCell.PayStore) (subject : SubjectId)
    (before : Option PayCell.ComputeUsage) (after : PayCell.ComputeUsage)
    (address : Minidregg.Theory.Store.Address PayCell.layout)
    (outside : address ≠ PayCell.computeUsageAddress subject.value) :
    Patch.run store (usagePatch subject before after) address = store address := by
  apply Patch.run_frame
  cases before <;>
    simpa [usagePatch, Patch.writeFootprint, Minidregg.Theory.Store.Op.writeAddress?,
      PayCell.computeUsageAddress] using outside

structure PreparedQuota (subject : SubjectId) (pre : PayCell.Cell)
    (expectedRoot : Digest) where
  private mk ::
  activation : PayCell.ComputeActivation
  before : Option PayCell.ComputeUsage
  quoted : Quote
  validated : ValidatedPatch PayCell.materializer pre expectedRoot
    (usagePatch subject before quoted.after)

def prepareQuota (subject : SubjectId) (clock : ClockCell.Clock)
    (pre : PayCell.Cell) (expectedRoot : Digest) (steps : Nat) :
    Except Reject (PreparedQuota subject pre expectedRoot) := do
  let some activation := PayCell.computeActivationOf pre.logical | throw .computeInactive
  let before := PayCell.computeUsageAt pre.logical subject.value
  let quoted ← quote subject clock activation before steps
  if expectedRoot != pre.root then throw .stalePayRoot
  match validate PayCell.materializer pre expectedRoot
      (usagePatch subject before quoted.after) with
  | .rejected reason => throw (.usagePatch reason)
  | .accepted validated => pure ⟨activation, before, quoted, validated⟩

def PreparedQuota.post {subject : SubjectId} {pre : PayCell.Cell}
    {expectedRoot : Digest} (prepared : PreparedQuota subject pre expectedRoot) : PayCell.Cell :=
  prepared.validated.apply

/-- Consent extracted from one SIGNED account target, not proof of authority.
The parent receiver must additionally admit its actual transfer capability and
current account law against the exact compute charge, under the same signature. -/
structure Funding where
  payer : Nat
  capability : CapabilityId
  asset : Nat
  credits : Nat
  expectedPayerBalance : Int
  expectedWellBalance : Int
  deriving DecidableEq, Repr

abbrev BookCell := Materialized CanonicalResourcePageMaterializer.materializer

/-- An empty batch for a free run; otherwise exactly one existing Book burn.
No account registrations and no alternate monetary carrier. -/
def burnBatch (funding : Option Funding) : CanonicalResourceKernel.Batch :=
  ⟨[], funding.toList.map fun supplied =>
    .burn supplied.payer supplied.asset supplied.credits⟩

structure PreparedBook (pre : BookCell) where
  private mk ::
  funding : Option Funding
  credits : Nat
  fundingExact : (funding.map Funding.credits).getD 0 = credits
  accepted : CanonicalResourceKernel.AcceptedBatch pre (burnBatch funding)

def prepareBook (pre : BookCell) (tariff : Option PayTariff.Tariff)
    (credits : Nat) (funding : Option Funding) : Except Reject (PreparedBook pre) := do
  if credits = 0 then
    -- A supplied zero-price leg is still consent, but not needed: require its
    -- debit to be exactly zero and use no Book operation.
    if let some supplied := funding then
      if supplied.credits != 0 then throw .fundingAmount
      -- Even an unnecessary zero-price leg projects actual source values to
      -- participant laws. It cannot fabricate a balance or tariff asset.
      let some tariff := tariff | throw .tariffInvalid
      if !decide tariff.valid || supplied.asset != tariff.asset then throw .tariffInvalid
      if supplied.payer = supplied.asset then throw .payerIsIssuer
      let book := CanonicalResourceKernel.logicalBook pre.logical
      if book.balance supplied.payer supplied.asset != supplied.expectedPayerBalance then
        throw .stalePayerBalance
      if book.balance supplied.asset supplied.asset != supplied.expectedWellBalance then
        throw .staleWellBalance
    let batch := burnBatch none
    if admitted : batch.Admission (CanonicalResourceKernel.logicalBook pre.logical) then
      pure ⟨none, 0, rfl, CanonicalResourceKernel.AcceptedBatch.ofAdmission admitted⟩
    else throw .bookRefused
  else
    let some supplied := funding | throw .missingFunding
    let some tariff := tariff | throw .tariffInvalid
    if !decide tariff.valid || supplied.asset != tariff.asset then throw .tariffInvalid
    if exact : supplied.credits = credits then
      if supplied.payer = supplied.asset then throw .payerIsIssuer
      let book := CanonicalResourceKernel.logicalBook pre.logical
      if book.balance supplied.payer supplied.asset != supplied.expectedPayerBalance then
        throw .stalePayerBalance
      if book.balance supplied.asset supplied.asset != supplied.expectedWellBalance then
        throw .staleWellBalance
      let batch := burnBatch (some supplied)
      if admitted : batch.Admission book then
        pure ⟨some supplied, credits, exact, CanonicalResourceKernel.AcceptedBatch.ofAdmission admitted⟩
      else throw .bookRefused
    else throw .fundingAmount

/-- Any paid plan burns exactly the quoted count, not a separate client fee. -/
theorem PreparedBook.funding_credits {pre : BookCell} (prepared : PreparedBook pre)
    (supplied : Funding) (funded : prepared.funding = some supplied) :
    supplied.credits = prepared.credits := by
  simpa [funded] using prepared.fundingExact

def PreparedBook.post {pre : BookCell} (prepared : PreparedBook pre) : BookCell :=
  prepared.accepted.post

theorem PreparedBook.conserves {pre : BookCell} (prepared : PreparedBook pre)
    (asset : CanonicalResourceKernel.AssetId) :
    (CanonicalResourceKernel.logicalBook prepared.post.logical).totalAsset asset =
      (CanonicalResourceKernel.logicalBook pre.logical).totalAsset asset :=
  prepared.accepted.conserves asset


/-- Plans must settle together with the invocation. Refused execution consumes
neither daily quota nor credits; exact replay must return before repricing. -/
structure Prepared (subject : SubjectId) (payPre : PayCell.Cell)
    (payRoot : Digest) (bookPre : BookCell) where
  private mk ::
  quota : PreparedQuota subject payPre payRoot
  book : PreparedBook bookPre
  sameCharge : book.credits = quota.quoted.credits

/-- The tariff is read from the SAME pay pre-state as activation and usage. -/
def prepare (subject : SubjectId) (clock : ClockCell.Clock)
    (payPre : PayCell.Cell) (payRoot : Digest) (bookPre : BookCell)
    (steps : Nat) (funding : Option Funding) :
    Except Reject (Prepared subject payPre payRoot bookPre) := do
  let quota ← prepareQuota subject clock payPre payRoot steps
  let book ← prepareBook bookPre (PayCell.tariffOf payPre.logical) quota.quoted.credits funding
  if exact : book.credits = quota.quoted.credits then pure ⟨quota, book, exact⟩
  else throw .fundingAmount

/-- Pre-oracle solvency checking may use signed claim.steps. The receiver must
obtain this evidence from the actual checked evaluator count before settlement. -/
structure CheckedSteps {subject : SubjectId} {payPre : PayCell.Cell}
    {payRoot : Digest} {bookPre : BookCell}
    (prepared : Prepared subject payPre payRoot bookPre) (checkedSteps : Nat) where
  private mk ::
  exact : prepared.quota.quoted.steps = checkedSteps

def confirmCheckedSteps {subject : SubjectId} {payPre : PayCell.Cell}
    {payRoot : Digest} {bookPre : BookCell}
    (prepared : Prepared subject payPre payRoot bookPre) (checkedSteps : Nat) :
    Except Reject (CheckedSteps prepared checkedSteps) :=
  if exact : prepared.quota.quoted.steps = checkedSteps then .ok ⟨exact⟩
  else .error .checkedStepsChanged

-- Small source poles, not native qualification.
example : paidSteps 0 1000000 = 0 := by decide
example : paidSteps 999999 3 = 2 := by decide
example : paidSteps 1000007 3 = 3 := by decide
example : paidSteps 500000 0 = 0 := by decide
example : quote ⟨7⟩ ⟨172800, 0⟩ ⟨1, some 0, ⟨9⟩⟩ (some ⟨1, 1000010⟩) 3 =
    .ok ⟨⟨7⟩, 2, 0, 3, 0⟩ := by decide
example : quote ⟨7⟩ ⟨172800, 0⟩ ⟨3, some 2, ⟨9⟩⟩ none 3 =
    .error .beforeActivation := by decide
example : quote ⟨7⟩ ⟨172800, 0⟩ ⟨2, some 2, ⟨9⟩⟩ none 3 =
    .error .activationInvalid := by decide
example : quote ⟨7⟩ ⟨172800, 0⟩ ⟨1, some 0, ⟨9⟩⟩ (some ⟨3, 0⟩) 3 =
    .error .clockBeforeUsage := by decide
example : quote ⟨7⟩ ⟨172800, 0⟩ ⟨2, some 1, ⟨9⟩⟩ (some ⟨1, 0⟩) 3 =
    .error .usageBeforeActivation := by decide

end Minidregg.Kernel.RunComputeBudget
