/-
# V2 paid-entry economic and resource-birth legs

This is executable preparation source, awaiting the integrator's authorized Lean
pass. It does not verify observer/member signatures or submit a transaction.
The receiver authenticates the exact input and commits these writes, the pay-cell
source index/membership patch, and its nullifiers in ONE durable intent.

Direct admission and later acceptance share the same economic input. Stable
identity derives the account, subject and grants. Current pending custody supplies
the installed key/epoch/NEXT, including after pre-admission rotation. No v1 memo
or possession signature is synthesized. Shared birth/authority constructors come
from PayEnrolReceiver; only the v2 economics and owner binding differ.
-/
import Kernel.PayEnrolReceiver
import Kernel.PayEnrolV2Decision

namespace Minidregg.Kernel.PayEnrolV2Legs

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff (Tariff)
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.Store (Store Patch Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer
abbrev Ambient := PayEnrolReceiver.Ambient
abbrev BookCell (deployment : Deployment) (directory : Directory Nat Registry) :=
  PayEnrolReceiver.BookCell deployment directory
abbrev FactoryCell (deployment : Deployment) (directory : Directory Nat Registry) :=
  PayEnrolReceiver.FactoryCell deployment directory

/-- The retained source index and exact normalized economic outcome. The
receiver obtains consumption from the authenticated original decision or accept
command; no second quote or transfer is invented here. -/
structure EconomicInput where
  origin : PayEnrolClaim.Claim
  consumption : PayEnrolClaim.Consumption
  float : Nat
  deriving DecidableEq, Repr

def EconomicInput.identityKey (input : EconomicInput) : List UInt8 := input.origin.ownerIdentityKey

structure EnrolInput where
  economic : EconomicInput
  owner : PayEnrolClaim.PendingOwner
  deriving DecidableEq, Repr

structure RenewInput where
  economic : EconomicInput
  before : EnrolRecord
  deriving DecidableEq, Repr

inductive Input where
  | enrol (input : EnrolInput)
  | renew (input : RenewInput)
  | noCredit
  deriving DecidableEq, Repr

def ofDirectEnrol (plan : PayEnrolV2Decision.EnrolPlan)
    (owner : PayEnrolClaim.PendingOwner) : EnrolInput :=
  ⟨⟨plan.origin, plan.consumption, plan.float⟩, owner⟩

def ofDirectRenew (plan : PayEnrolV2Decision.RenewPlan) : RenewInput :=
  ⟨⟨plan.origin, plan.consumption, plan.float⟩, plan.before⟩

/-- Same constructor for a Checked, current-owner acceptance: the retained
origin and the successful accept gate's consumption are the economic source. -/
def ofAcceptedEnrol (origin : PayEnrolClaim.Claim) (consumption : PayEnrolClaim.Consumption)
    (float : Nat) (owner : PayEnrolClaim.PendingOwner) : EnrolInput :=
  ⟨⟨origin, consumption, float⟩, owner⟩

def ofAcceptedRenew (origin : PayEnrolClaim.Claim) (consumption : PayEnrolClaim.Consumption)
    (float : Nat) (record : EnrolRecord) : RenewInput :=
  ⟨⟨origin, consumption, float⟩, record⟩

/-- Immediate origin is absent before its atomic admission; pending origin is
already retained exactly. In neither case may a prior consumption be spent again. -/
def IndexReady (pay : PayStore) (input : EconomicInput) : Prop :=
  claimConsumptionAt pay input.origin.id = none ∧
    match input.consumption.authorization with
    | .originalMemo => claimAt pay input.origin.id = none
    | .acceptCurrentQuote _ => claimAt pay input.origin.id = some input.origin

instance (pay : PayStore) (input : EconomicInput) : Decidable (IndexReady pay input) := by
  unfold IndexReady
  cases input.consumption.authorization <;> infer_instance

/-- The same source-index coherence used by the pay-cell law, plus the exact
currently loaded tariff and enrollment float. Conservation follows from valid
consumption; physical preparation additionally checks its actual birth fee. -/
def EconomicReady (pay : PayStore) (tariff : Tariff) (input : EconomicInput) : Prop :=
  tariffOf pay = some tariff ∧
  input.origin.valid ∧ claimMemoCoherent input.origin = true ∧
  input.consumption.valid ∧ input.consumption.matchesClaim input.origin ∧
  consumptionAuthorizationCoherent input.origin input.consumption = true ∧
  input.consumption.tariff = tariff ∧
  tariff.enrolIndex.bind (assignmentAt pay) = some input.float ∧
  input.float ≠ tariff.asset ∧ IndexReady pay input

instance (pay : PayStore) (tariff : Tariff) (input : EconomicInput) :
    Decidable (EconomicReady pay tariff input) := by
  unfold EconomicReady
  infer_instance

/-- With no pending row, the actual original enrollment memo supplies the key,
epoch and NEXT. A current-quote acceptance cannot create missing custody. -/
def originalOwnerMatches (input : EnrolInput) : Bool :=
  match input.economic.consumption.authorization with
  | .acceptCurrentQuote _ => false
  | .originalMemo =>
      match PayEnrolMemoV2.parse input.economic.origin.rawMemo with
      | .error _ => false
      | .ok memo => decide (
          memo.unsigned.mode = .enroll ∧
          input.owner.identityKey = memo.unsigned.enrollmentIdentityKey ∧
          input.owner.currentKey = memo.unsigned.authorizingKey ∧
          input.owner.epoch = memo.unsigned.authorityEpoch ∧
          input.owner.nextKeyDigest = memo.unsigned.nextKeyDigest)

/-- Existing pending custody is matched exactly; its current key may differ
from the immutable deposit's original key after a deliberate pre-rotation. -/
def OwnerReady (pay : PayStore) (input : EnrolInput) : Prop :=
  input.owner.valid ∧ input.owner.identityKey = input.economic.identityKey ∧
    match pendingOwnerAt pay input.economic.identityKey with
    | none => originalOwnerMatches input = true
    | some current => input.owner = current

instance (pay : PayStore) (input : EnrolInput) : Decidable (OwnerReady pay input) := by
  unfold OwnerReady
  cases pendingOwnerAt pay input.economic.identityKey <;> infer_instance

inductive Reject where
  | economics | owner | membership | birthFee
  | grantBatch | birthShape | keyTaken | observeGrantTaken | authorityEntries
  | validation | allocation | bookAdmission
  deriving DecidableEq, Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason | some value => .ok value

def require (condition : Prop) [Decidable condition] (reason : Reject) :
    Except Reject (PLift condition) :=
  if holds : condition then .ok ⟨holds⟩ else .error reason

/-- Stable identity derives all resource identifiers, even after pending rotation. -/
def enrolIds (deployment : Deployment) (input : EnrolInput) : PayEnrolReceiver.Ids :=
  PayEnrolReceiver.ids deployment.domain input.economic.identityKey

/-- The installed key is CURRENT custody, never a revived original memo key. -/
def enrolKey (deployment : Deployment) (revision : Nat) (input : EnrolInput) : KeyRecord :=
  let identities := enrolIds deployment input
  ⟨identities.keyId, input.owner.epoch, CredentialSignatureAdmission.ed25519Algorithm,
    identities.subject, input.owner.currentKey, revision,
    revision + PayEnrolReceiver.keyLifetime, some input.owner.nextKeyDigest⟩

/-- One mint, requested membership fee, then the ordinary birth's exact funding
and birth fee. The resource-birth descriptor supplies registrations and order. -/
def enrolBatch (tariff : Tariff) (collector : Nat) (input : EnrolInput)
    (descriptor : Descriptor Registry) : CanonicalResourceKernel.Batch :=
  ⟨descriptor.resourceBatch.registrations,
    .mint tariff.asset input.economic.float input.economic.consumption.mintedCredit ::
      .fee input.economic.float collector tariff.asset input.economic.consumption.membershipCredit ::
        descriptor.resourceBatch.operations⟩

def renewBatch (tariff : Tariff) (collector : Nat) (input : RenewInput) :
    CanonicalResourceKernel.Batch :=
  ⟨[], [.mint tariff.asset input.economic.float input.economic.consumption.mintedCredit,
    .fee input.economic.float collector tariff.asset input.economic.consumption.membershipCredit,
    .transfer input.economic.float input.before.account tariff.asset
      input.economic.consumption.creditedRemainder]⟩

section Legs

variable {F : Type} [Field F] (deployment : Deployment)
  (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) {durable : Durable}

def enrolObserve (authority : Loaded deployment durable.snapshot) (input : EnrolInput) :
    AuthorityGrant :=
  PayEnrolReceiver.observeGrant deployment profile.template authority.snapshot.cell ambient.height
    (enrolIds deployment input)

def enrolDraft (authority : Loaded deployment durable.snapshot) (input : EnrolInput) :
    Descriptor Registry :=
  PayEnrolReceiver.draft deployment profile.semantics profile.template ambient.tariff
    authority.snapshot.cell ambient.height (enrolIds deployment input) input.economic.float
    input.economic.consumption.creditedRemainder

structure EnrolLegs (directory : LoadedDirectory durable)
    (authority : Loaded deployment durable.snapshot)
    (pay : PayCellDomain.Loaded deployment durable.snapshot)
    (book : BookCell deployment directory.directory) (tariff : Tariff) (input : EnrolInput) where
  private mk ::
  economics : EconomicReady pay.cell.logical tariff input.economic
  owner : OwnerReady pay.cell.logical input
  mode : input.economic.consumption.terms.mode = .enroll
  absent : enrolmentAt pay.cell.logical input.economic.identityKey = none
  assetExact : ambient.tariff.asset = tariff.asset
  feeExact : input.economic.consumption.birthFee =
    (enrolDraft deployment profile ambient authority input).fee.amount
  descriptor : Descriptor Registry
  descriptorExact : descriptor =
    { enrolDraft deployment profile ambient authority input with
      auxiliaryCreates := descriptor.auxiliaryCreates }
  grants : PreparedGrantBatch profile.compilerProfile deployment authority descriptor
  auxiliaryExact : descriptor.auxiliaryCreates = grants.auxiliaryCreates
  initials : CanonicalCellRegistry.BirthsAdmissible deployment descriptor
  templateBound : ResourceBirthPolicyController.Concrete.TemplateBound profile.template
    authority.snapshot.authState ambient.height descriptor
  keyFresh : PayEnrolReceiver.KeyFresh authority.snapshot
    (enrolKey deployment authority.snapshot.revision input)
  observeReady : GrantReady authority.snapshot (enrolObserve deployment profile ambient authority input)
  entriesDistinct : ((PayEnrolReceiver.authorityEntries descriptor
    (enrolKey deployment authority.snapshot.revision input)
    (enrolObserve deployment profile ambient authority input)).map Sigma.fst).Nodup
  authorityValidated : ValidatedPatch AuthorityMaterializer authority.snapshot.cell
    authority.snapshot.cell.root
    (assignAll authority.snapshot.logical (PayEnrolReceiver.authorityEntries descriptor
      (enrolKey deployment authority.snapshot.revision input)
      (enrolObserve deployment profile ambient authority input)))
  allocated : ResourceBirthController.Allocated Registry directory.directory descriptor
  resources : CanonicalResourceKernel.AcceptedBatch book.payload
    (enrolBatch tariff ambient.tariff.collector input descriptor)

def prepareEnrolLegs (directory : LoadedDirectory durable)
    (authority : Loaded deployment durable.snapshot)
    (pay : PayCellDomain.Loaded deployment durable.snapshot)
    (book : BookCell deployment directory.directory) (tariff : Tariff) (input : EnrolInput) :
    Except Reject (EnrolLegs deployment profile ambient directory authority pay book tariff input) := do
  let economic ← require (EconomicReady pay.cell.logical tariff input.economic) .economics
  let owner ← require (OwnerReady pay.cell.logical input) .owner
  let mode ← require (input.economic.consumption.terms.mode = .enroll) .membership
  let absent ← require (enrolmentAt pay.cell.logical input.economic.identityKey = none) .membership
  let asset ← require (ambient.tariff.asset = tariff.asset) .economics
  let base := enrolDraft deployment profile ambient authority input
  let fee ← require (input.economic.consumption.birthFee = base.fee.amount) .birthFee
  let first ← requireSome .grantBatch
    (prepareGrantBatch profile.compilerProfile deployment authority base)
  let descriptor : Descriptor Registry := { base with auxiliaryCreates := first.auxiliaryCreates }
  let grants ← requireSome .grantBatch
    (prepareGrantBatch profile.compilerProfile deployment authority descriptor)
  let aux ← require (ResourceBirthController.Concrete.sameCreates descriptor.auxiliaryCreates
    grants.auxiliaryCreates = true) .grantBatch
  let initials ← require (CanonicalCellRegistry.BirthsAdmissible deployment descriptor) .birthShape
  let template ← require (ResourceBirthPolicyController.Concrete.TemplateBound profile.template
    authority.snapshot.authState ambient.height descriptor) .birthShape
  let key ← require (PayEnrolReceiver.KeyFresh authority.snapshot
    (enrolKey deployment authority.snapshot.revision input)) .keyTaken
  let observe ← require (GrantReady authority.snapshot
    (enrolObserve deployment profile ambient authority input)) .observeGrantTaken
  let distinct ← require (((PayEnrolReceiver.authorityEntries descriptor
    (enrolKey deployment authority.snapshot.revision input)
    (enrolObserve deployment profile ambient authority input)).map Sigma.fst).Nodup) .authorityEntries
  match validate AuthorityMaterializer authority.snapshot.cell authority.snapshot.cell.root
      (assignAll authority.snapshot.logical (PayEnrolReceiver.authorityEntries descriptor
        (enrolKey deployment authority.snapshot.revision input)
        (enrolObserve deployment profile ambient authority input))) with
  | .rejected _ => throw .validation
  | .accepted validated =>
    let allocated ← match ResourceBirthController.allocate? Registry directory.directory descriptor with
      | .error _ => throw .allocation
      | .ok allocated => pure allocated
    let admission ← require ((enrolBatch tariff ambient.tariff.collector input descriptor).Admission
      (CanonicalResourceKernel.logicalBook book.payload.logical)) .bookAdmission
    pure ⟨economic.down, owner.down, mode.down, absent.down, asset.down, fee.down,
      descriptor, rfl, grants, (ResourceBirthController.Concrete.sameCreates_iff _ _).mp aux.down,
      initials.down, template.down, key.down, observe.down, distinct.down, validated, allocated,
      CanonicalResourceKernel.AcceptedBatch.ofAdmission admission.down⟩

def EnrolLegs.authorityPost {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot}
    {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff} {input : EnrolInput}
    (legs : EnrolLegs deployment profile ambient directory authority pay book tariff input) :
    CredentialAuthorityDomain.Cell := legs.authorityValidated.apply

structure RenewLegs (directory : LoadedDirectory durable)
    (pay : PayCellDomain.Loaded deployment durable.snapshot)
    (book : BookCell deployment directory.directory) (tariff : Tariff) (input : RenewInput) : Type where
  private mk ::
  economics : EconomicReady pay.cell.logical tariff input.economic
  mode : input.economic.consumption.terms.mode = .renew
  recordExact : enrolmentAt pay.cell.logical input.economic.identityKey = some input.before
  noBirth : input.economic.consumption.birthFee = 0
  resources : CanonicalResourceKernel.AcceptedBatch book.payload
    (renewBatch tariff ambient.tariff.collector input)

def prepareRenewLegs (directory : LoadedDirectory durable)
    (pay : PayCellDomain.Loaded deployment durable.snapshot)
    (book : BookCell deployment directory.directory) (tariff : Tariff) (input : RenewInput) :
    Except Reject (RenewLegs deployment ambient directory pay book tariff input) := do
  let economic ← require (EconomicReady pay.cell.logical tariff input.economic) .economics
  let mode ← require (input.economic.consumption.terms.mode = .renew) .membership
  let record ← require (enrolmentAt pay.cell.logical input.economic.identityKey = some input.before) .membership
  let fee ← require (input.economic.consumption.birthFee = 0) .birthFee
  let admission ← require ((renewBatch tariff ambient.tariff.collector input).Admission
    (CanonicalResourceKernel.logicalBook book.payload.logical)) .bookAdmission
  pure ⟨economic.down, mode.down, record.down, fee.down,
    CanonicalResourceKernel.AcceptedBatch.ofAdmission admission.down⟩

inductive Legs (directory : LoadedDirectory durable)
    (authority : Loaded deployment durable.snapshot)
    (pay : PayCellDomain.Loaded deployment durable.snapshot)
    (book : BookCell deployment directory.directory) (tariff : Tariff) : Input → Type
  | enrol (input : EnrolInput)
      (legs : EnrolLegs deployment profile ambient directory authority pay book tariff input) :
      Legs directory authority pay book tariff (.enrol input)
  | renew (input : RenewInput)
      (legs : RenewLegs deployment ambient directory pay book tariff input) :
      Legs directory authority pay book tariff (.renew input)
  | noCredit : Legs directory authority pay book tariff .noCredit

def prepare (directory : LoadedDirectory durable)
    (authority : Loaded deployment durable.snapshot)
    (pay : PayCellDomain.Loaded deployment durable.snapshot)
    (book : BookCell deployment directory.directory) (tariff : Tariff) :
    (input : Input) → Except Reject (Legs deployment profile ambient directory authority pay book tariff input)
  | .enrol input => do
      let legs ← prepareEnrolLegs deployment profile ambient directory authority pay book tariff input
      pure (.enrol input legs)
  | .renew input => do
      let legs ← prepareRenewLegs deployment ambient directory pay book tariff input
      pure (.renew input legs)
  | .noCredit => .ok .noCredit

variable {deployment profile ambient}
variable {directory : LoadedDirectory durable} {authority : Loaded deployment durable.snapshot}
  {pay : PayCellDomain.Loaded deployment durable.snapshot}
  {book : BookCell deployment directory.directory} {tariff : Tariff}

/-- Resource writes only: pay membership/index/lease/tip remains the receiver's
separate validated patch in the SAME intent. -/
def Legs.writes (factory : FactoryCell deployment directory.directory) : {input : Input} →
    Legs deployment profile ambient directory authority pay book tariff input → List DataWrite
  | _, .enrol _ legs =>
      ResourceBirthController.Concrete.planWrites deployment legs.descriptor factory.payload
        book.payload legs.resources.post (authority.writes legs.authorityPost)
  | _, .renew _ legs =>
      [ResourceBirthController.Concrete.packedWrite deployment.resourceBookId
        ⟨.resourceBook, book.payload⟩ ⟨.resourceBook, legs.resources.post⟩]
  | _, .noCredit => []

def Legs.account : {input : Input} →
    Legs deployment profile ambient directory authority pay book tariff input → Nat
  | _, .enrol input _ => (enrolIds deployment input).account
  | _, .renew input _ => input.before.account
  | _, .noCredit => 0

def Legs.birthBytes : {input : Input} →
    Legs deployment profile ambient directory authority pay book tariff input → List UInt8
  | _, .enrol _ legs => CanonicalCellRegistry.sourceEncoding.codec.encode legs.descriptor
  | _, _ => []

def Legs.nullifiers : {input : Input} →
    Legs deployment profile ambient directory authority pay book tariff input → List StableNullifier
  | _, .enrol _ legs =>
      [CredentialAuthorityReplay.nullifier deployment.domain legs.descriptor.authorityNullifier]
  | _, _ => []

/-- The renewal leg emits exactly one Book write, so no authority-cell write is
hidden in this branch. The receiver separately patches the paid lease/index. -/
theorem renewal_writes_only_book (factory : FactoryCell deployment directory.directory)
    (input : RenewInput) (legs : RenewLegs deployment ambient directory pay book tariff input) :
    (Legs.renew input legs : Legs deployment profile ambient directory authority pay book tariff (.renew input)).writes factory =
      [ResourceBirthController.Concrete.packedWrite deployment.resourceBookId
        ⟨.resourceBook, book.payload⟩ ⟨.resourceBook, legs.resources.post⟩] := rfl

end Legs

/-! ## The stable identity/current custody boundary -/

theorem enrol_key_current (deployment : Deployment) (revision : Nat) (input : EnrolInput) :
    (enrolKey deployment revision input).publicKey = input.owner.currentKey ∧
    (enrolKey deployment revision input).keyEpoch = input.owner.epoch ∧
    (enrolKey deployment revision input).nextKeyDigest = some input.owner.nextKeyDigest ∧
    (enrolKey deployment revision input).subject =
      (PayEnrolReceiver.ids deployment.domain input.economic.identityKey).subject :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem existing_pending_owner_required (pay : PayStore) (input : EnrolInput)
    (current : PayEnrolClaim.PendingOwner)
    (present : pendingOwnerAt pay input.economic.identityKey = some current)
    (ready : OwnerReady pay input) : input.owner = current := by
  simpa [OwnerReady, present] using ready.2.2

/-- Preparation checks the actual source index's conservation partition, not a
parallel arithmetic result detached from the proposed Book/birth operation. -/
theorem economic_partition (pay : PayStore) (tariff : Tariff) (input : EconomicInput)
    (ready : EconomicReady pay tariff input) :
    input.consumption.birthFee + input.consumption.membershipCredit +
      input.consumption.creditedRemainder = input.consumption.mintedCredit := by
  rcases ready with ⟨_, _, _, valid, _, _, _, _, _, _⟩
  rcases valid with ⟨_, _, _, _, _, _, _, _, partition, _, _⟩
  exact partition

theorem direct_origin_preserved (plan : PayEnrolV2Decision.EnrolPlan)
    (owner : PayEnrolClaim.PendingOwner) :
    (ofDirectEnrol plan owner).economic.origin = plan.origin ∧
    (ofDirectEnrol plan owner).economic.consumption = plan.consumption := ⟨rfl, rfl⟩

theorem acceptance_origin_preserved (origin : PayEnrolClaim.Claim)
    (consumption : PayEnrolClaim.Consumption) (float : Nat) (owner : PayEnrolClaim.PendingOwner) :
    (ofAcceptedEnrol origin consumption float owner).economic.origin = origin ∧
    (ofAcceptedEnrol origin consumption float owner).owner = owner := ⟨rfl, rfl⟩

#assert_axioms economic_partition
#assert_axioms enrol_key_current
#assert_axioms existing_pending_owner_required
#assert_axioms direct_origin_preserved
#assert_axioms acceptance_origin_preserved
#assert_axioms renewal_writes_only_book

end Minidregg.Kernel.PayEnrolV2Legs
