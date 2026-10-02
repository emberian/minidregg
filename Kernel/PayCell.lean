/-
# Kernel.PayCell — the pay cell: tariff, deposit address book, assignment, enrolment

One store cell per deployment, at an identifier derived from the deployment
domain (`physicalId`), with thirteen namespaces on `Theory.Store`:

| namespace    | key              | value                     | discipline  |
|--------------|------------------|---------------------------|-------------|
| `tariff`     | `Unit`           | `PayTariff.Tariff`        | RAM         |
| `book`       | index `Nat`      | 32-byte deposit address   | append-only |
| `assignment` | index `Nat`      | Book `AccountId`          | append-only |
| `enrolment`  | Mini key (32 B)  | `EnrolRecord`             | RAM         |
| `sshIndex`   | ssh blob (51 B)  | Mini key                  | append-only |
| `journal`    | nullifier bytes  | `Unattributed`            | append-only |
| `claim`      | nullifier bytes  | original paid claim       | append-only |
| `claimConsumption` | claim id   | exact authorized split    | append-only |
| `pendingOwner` | identity key   | current unadmitted custody| RAM         |
| `chainTip`   | `Unit`           | finalized slot/block time | RAM         |
| `pendingOwnerHistory` | identity/epoch | retained custody     | append-only |
| `computeUsage` | subject `Nat`   | day/admitted steps        | RAM         |
| `computeActivation` | `Unit`     | activation/history anchor | append-only |

The last three are PAY §11's self-enrollment state (layout v2).  An
`enrolment` row is written once by an enrollment and rewritten only by a
renewal of the same key (its lease grows, `PayEnrolDecision`); `sshIndex`
makes an ssh key belong to at most one Mini key, and the law ties the two
namespaces together in both directions; `journal` holds every
enrollment-index payment that was not accepted, with its named reason.

`book` is written by the operator's control capability (`PayBookReceiver`);
`assignment` binds book index `i` to the account a subject owns
(`PayAssignmentReceiver`); `tariff` is the operator's versioned rate. Verified
observer ingress retains its finalized chain tip here and also advances the
deployment clock. The deployment clock may advance independently; it is not
chain evidence. Quote expiry uses this chain tip, with an explicit lag bound
against the deployment clock. Empty verified observation reports refresh it.

Both indexed namespaces are append-only, so an index is written once
(`Store.Op.allocate_enabled_fresh`).  The index an observation names resolves
to both its address (`bookAt`) and its account (`assignmentAt`); a payment
nullifier covering signature ‖ address (PAY §10 erratum 1) reads the address
from `bookAt`.

Wire: the store codec with layout name `DREGG/PAY/CELL/v5` (its frame commits
to the name and every namespace's codec identifier); the tariff value is
`DREGG/PAY/TARIFF/v3`.  v3 = P3b-1's enrolment namespaces without P2's in-cell
clock: namespace tag 3 (the clock) is retired and decodes to nothing.  v4 = v3
with the tariff at `DREGG/PAY/TARIFF/v3` (C3's `slashCallerPermille`). v5 adds
claim/custody/tip tags 7–11 and compute usage/activation tags 12–13, without
reusing retired tag 3. Old versions refuse
this decoder. `PayCellLegacyV4` and `PayCellUpgrade` provide an explicit neutral
v4 lift preserving every old row and leaving every new namespace empty. In particular, a neutral codec lift does
not activate compute or assert that historical execution used no allowance.
Compute requires a separately authenticated fresh-genesis or closed-legacy
history activation. Its append-only record prevents resetting the free epoch.
-/
import Kernel.PayEnrolClaim
import Kernel.PayEnrolMemoV2
import Compiler.StoreCodec
import Kernel.PayTariff
import Kernel.PayEnrolMemo

namespace Minidregg.Kernel.PayCell

open Minidregg.Compiler
open Minidregg.Compiler.StoreCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Store
open Minidregg.Theory.CellState (Materializer Materialized materialize)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayEnrolMemo (JournalReason MemoField isEd25519Blob)

set_option autoImplicit false

inductive Namespace
  | tariff
  | book
  | assignment
  | enrolment
  | sshIndex
  | journal
  | claim
  | claimConsumption
  | pendingOwner
  | chainTip
  | pendingOwnerHistory
  | computeUsage
  | computeActivation
  deriving DecidableEq, Repr

/-- The finalized chain tip a pay observer reports at: the slot and its block
time (unix s). It is the observer's claim about the chain, carried in its
command. The dedicated row preserves chain evidence independently of wall ticks. -/
structure ChainTip where
  slot : Nat
  blockTime : Nat
  deriving DecidableEq, Repr

/-- The chain hour of a tip: the unit of enrollment leases. -/
def ChainTip.hour (tip : ChainTip) : Nat := tip.blockTime / 3600

/-- The hour of a unix time: the public enrollment view's `clock.hour` (read
from the clock cell's `now`). -/
def hourOf (now : Nat) : Nat := now / 3600

def chainTipStream : StreamCodec ChainTip :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat StreamCodec.nat)
    (fun tip => (tip.slot, tip.blockTime))
    (fun (slot, blockTime) => ⟨slot, blockTime⟩)
    (by intro tip; cases tip; rfl)

/-- A self-enrolled Mini key's record (PAY §11.4), keyed by the 32-byte Mini
key.  `leaseUntil` is a chain hour (`blockTime / 3600`): the node membership
the key has paid for runs while `clock hour < leaseUntil`. -/
structure EnrolRecord where
  /-- The 51-byte `ssh-ed25519` wire blob the enrollment bought a login for. -/
  sshBlob : List UInt8
  /-- The Book account born for the key. -/
  account : Nat
  /-- The book index assigned to that account, if one was free. -/
  index : Option Nat
  leaseUntil : Nat
  /-- The chain slot of the enrolling payment. -/
  enrolledSlot : Nat
  deriving DecidableEq, Repr

/-- An enrollment-index payment that was not accepted: consumed (its
nullifier is spent), credited nowhere, and kept here with its reason. -/
structure Unattributed where
  index : Nat
  amount : Nat
  slot : Nat
  reason : JournalReason
  memo : MemoField
  deriving DecidableEq, Repr

/-- Nonmonetary execution accounting, indexed by the actual signing subject. -/
structure ComputeUsage where
  day : Nat
  admittedSteps : Nat
  deriving DecidableEq, Repr

/-- Installed only by authenticated boot/carry. `history` binds the actual
closed legacy history, or the genesis identity for a genuinely new deployment.
`legacyThroughDay = none` means fresh genesis, never "history unavailable".
A legacy activation starts after its final old-profile execution day. -/
structure ComputeActivation where
  day : Nat
  legacyThroughDay : Option Nat
  history : Digest
  deriving DecidableEq, Repr

def ComputeActivation.valid (activation : ComputeActivation) : Prop :=
  match activation.legacyThroughDay with
  | none => True
  | some priorDay => priorDay < activation.day

instance (activation : ComputeActivation) : Decidable activation.valid := by
  unfold ComputeActivation.valid
  cases activation.legacyThroughDay <;> infer_instance

def Namespace.Key : Namespace → Type
  | .tariff => Unit
  | .book => Nat
  | .assignment => Nat
  | .enrolment => List UInt8
  | .sshIndex => List UInt8
  | .journal => List UInt8
  | .claim => List UInt8
  | .claimConsumption => List UInt8
  | .pendingOwner => List UInt8
  | .pendingOwnerHistory => List UInt8 × Nat
  | .chainTip => Unit
  | .computeUsage => Nat
  | .computeActivation => Unit

def Namespace.Value : Namespace → Type
  | .tariff => Tariff
  | .book => Address32
  | .assignment => Nat
  | .enrolment => EnrolRecord
  | .sshIndex => List UInt8
  | .journal => Unattributed
  | .claim => PayEnrolClaim.Claim
  | .claimConsumption => PayEnrolClaim.Consumption
  | .pendingOwner => PayEnrolClaim.PendingOwner
  | .pendingOwnerHistory => PayEnrolClaim.PendingOwner
  | .chainTip => ChainTip
  | .computeUsage => ComputeUsage
  | .computeActivation => ComputeActivation

instance Namespace.keyDecEq : (space : Namespace) → DecidableEq (Namespace.Key space)
  | .tariff => inferInstanceAs (DecidableEq Unit)
  | .book => inferInstanceAs (DecidableEq Nat)
  | .assignment => inferInstanceAs (DecidableEq Nat)
  | .enrolment => inferInstanceAs (DecidableEq (List UInt8))
  | .sshIndex => inferInstanceAs (DecidableEq (List UInt8))
  | .journal => inferInstanceAs (DecidableEq (List UInt8))
  | .claim => inferInstanceAs (DecidableEq (List UInt8))
  | .claimConsumption => inferInstanceAs (DecidableEq (List UInt8))
  | .pendingOwner => inferInstanceAs (DecidableEq (List UInt8))
  | .pendingOwnerHistory => inferInstanceAs (DecidableEq (List UInt8 × Nat))
  | .chainTip => inferInstanceAs (DecidableEq Unit)
  | .computeUsage => inferInstanceAs (DecidableEq Nat)
  | .computeActivation => inferInstanceAs (DecidableEq Unit)

instance Namespace.valueDecEq : (space : Namespace) → DecidableEq (Namespace.Value space)
  | .tariff => inferInstanceAs (DecidableEq Tariff)
  | .book => inferInstanceAs (DecidableEq (List UInt8))
  | .assignment => inferInstanceAs (DecidableEq Nat)
  | .enrolment => inferInstanceAs (DecidableEq EnrolRecord)
  | .sshIndex => inferInstanceAs (DecidableEq (List UInt8))
  | .journal => inferInstanceAs (DecidableEq Unattributed)
  | .claim => inferInstanceAs (DecidableEq PayEnrolClaim.Claim)
  | .claimConsumption => inferInstanceAs (DecidableEq PayEnrolClaim.Consumption)
  | .pendingOwner => inferInstanceAs (DecidableEq PayEnrolClaim.PendingOwner)
  | .pendingOwnerHistory => inferInstanceAs (DecidableEq PayEnrolClaim.PendingOwner)
  | .chainTip => inferInstanceAs (DecidableEq ChainTip)
  | .computeUsage => inferInstanceAs (DecidableEq ComputeUsage)
  | .computeActivation => inferInstanceAs (DecidableEq ComputeActivation)

def Namespace.discipline : Namespace → Discipline
  | .tariff => .ram
  | .book => .appendOnly
  | .assignment => .appendOnly
  | .enrolment => .ram
  | .sshIndex => .appendOnly
  | .journal => .appendOnly
  | .claim => .appendOnly
  | .claimConsumption => .appendOnly
  | .pendingOwner => .ram
  | .pendingOwnerHistory => .appendOnly
  | .chainTip => .ram
  | .computeUsage => .ram
  | .computeActivation => .appendOnly

abbrev layout : Layout.{0, 0, 0} where
  Namespace := Namespace
  Key := Namespace.Key
  Value := Namespace.Value
  discipline := Namespace.discipline

abbrev PayStore := Store layout

/-! ## Addresses and typed reads -/

def tariffAddress : Address layout := ⟨.tariff, ()⟩
def bookAddress (index : Nat) : Address layout := ⟨.book, index⟩
def assignmentAddress (index : Nat) : Address layout := ⟨.assignment, index⟩
def enrolmentAddress (miniKey : List UInt8) : Address layout := ⟨.enrolment, miniKey⟩
def sshIndexAddress (sshBlob : List UInt8) : Address layout := ⟨.sshIndex, sshBlob⟩
def journalAddress (nullifier : List UInt8) : Address layout := ⟨.journal, nullifier⟩

def claimAddress (id : List UInt8) : Address layout := ⟨.claim, id⟩
def claimConsumptionAddress (id : List UInt8) : Address layout := ⟨.claimConsumption, id⟩
def pendingOwnerAddress (identityKey : List UInt8) : Address layout := ⟨.pendingOwner, identityKey⟩
/-- Immutable provenance of pre-admission custody, never a current-authority
fallback after the identity has entered the registry. -/
def pendingOwnerHistoryAddress (identityKey : List UInt8) (epoch : Nat) : Address layout :=
  ⟨.pendingOwnerHistory, (identityKey, epoch)⟩
def chainTipAddress : Address layout := ⟨.chainTip, ()⟩
def claimAt (store : PayStore) (id : List UInt8) : Option PayEnrolClaim.Claim := store (claimAddress id)
def claimConsumptionAt (store : PayStore) (id : List UInt8) : Option PayEnrolClaim.Consumption :=
  store (claimConsumptionAddress id)
def pendingOwnerAt (store : PayStore) (identityKey : List UInt8) : Option PayEnrolClaim.PendingOwner :=
  store (pendingOwnerAddress identityKey)
def pendingOwnerHistoryAt (store : PayStore) (identityKey : List UInt8) (epoch : Nat) :
    Option PayEnrolClaim.PendingOwner :=
  store (pendingOwnerHistoryAddress identityKey epoch)
def chainTipOf (store : PayStore) : Option ChainTip := store chainTipAddress

def computeUsageAddress (subject : Nat) : Address layout := ⟨.computeUsage, subject⟩
def computeActivationAddress : Address layout := ⟨.computeActivation, ()⟩
def computeUsageAt (store : PayStore) (subject : Nat) : Option ComputeUsage :=
  store (computeUsageAddress subject)
def computeActivationOf (store : PayStore) : Option ComputeActivation :=
  store computeActivationAddress

def tariffOf (store : PayStore) : Option Tariff := store tariffAddress
/-- The deposit address at book index `index`. -/
def bookAt (store : PayStore) (index : Nat) : Option Address32 := store (bookAddress index)
/-- The account book index `index` is assigned to. -/
def assignmentAt (store : PayStore) (index : Nat) : Option Nat := store (assignmentAddress index)
/-- The self-enrollment record of a Mini key. -/
def enrolmentAt (store : PayStore) (miniKey : List UInt8) : Option EnrolRecord :=
  store (enrolmentAddress miniKey)
/-- The Mini key an ssh blob is enrolled under. -/
def sshIndexAt (store : PayStore) (sshBlob : List UInt8) : Option (List UInt8) :=
  store (sshIndexAddress sshBlob)
def journalAt (store : PayStore) (nullifier : List UInt8) : Option Unattributed :=
  store (journalAddress nullifier)

/-- Present rows of one namespace. -/
def countIn (store : PayStore) (space : Namespace) : Nat :=
  (store.support.filter fun address => address.1 = space).card

/-- The next unassigned index: the number of assignments made.  History
independent — the assignment namespace grows with payers, not turns. -/
def nextFree (store : PayStore) : Nat := countIn store .assignment

/-- The next free book index: the number of installed deposit addresses. -/
def bookSize (store : PayStore) : Nat := countIn store .book

/-- Whether some index is already bound to `account`: a scan of the support. -/
def accountAssigned (store : PayStore) (account : Nat) : Bool :=
  decide (∃ address ∈ store.support, assignedTo store account address = true)
where
  assignedTo (store : PayStore) (account : Nat) : Address layout → Bool
    | ⟨.assignment, index⟩ => decide (assignmentAt store index = some account)
    | _ => false

/-! ## The cell law -/

/-- Original claim bytes remain bound to the signed v2 identity, amount and pricing.
Signature verification is the receiver's Checked boundary, not a cell-law oracle. -/
def claimMemoCoherent (claim : PayEnrolClaim.Claim) : Bool :=
  match PayEnrolMemoV2.parse claim.rawMemo with
  | .ok memo => decide (memo.unsigned.enrollmentIdentityKey = claim.ownerIdentityKey ∧
      memo.unsigned.amountAtomic = claim.original.amountAtomic ∧
      memo.unsigned.pricingCommitment = claim.originalPricingCommitment)
  | .error _ => false

/-- Original-memo consumption derives its normalized economic terms from the
immutable signed bytes, never from a fabricated detached acceptance request. -/
def originalConsumptionTerms (claim : PayEnrolClaim.Claim) : Option PayEnrolClaim.Terms :=
  match PayEnrolMemoV2.parse claim.rawMemo with
  | .error _ => none
  | .ok memo =>
    let mode : PayEnrolClaim.Mode := match memo.unsigned.mode with
      | .enroll => .enroll
      | .renew | .renewWithoutCommitment => .renew
    some ⟨mode, claim.id, memo.unsigned.enrollmentIdentityKey,
      memo.unsigned.pricingCommitment, memo.unsigned.weeks,
      memo.unsigned.minimumStarterCredit, memo.unsigned.expiresAtProcessingChainHour⟩

def consumptionAuthorizationCoherent (claim : PayEnrolClaim.Claim)
    (consumed : PayEnrolClaim.Consumption) : Bool :=
  match consumed.authorization with
  | .originalMemo => claim.reason.isNone &&
      decide (originalConsumptionTerms claim = some consumed.terms)
  | .acceptCurrentQuote request => claim.reason.isSome &&
      decide (request.terms = consumed.terms)

/-- Every book entry is a 32-byte key; every enrolment row is a 32-byte Mini
key holding one ssh-ed25519 blob that the ssh index maps back to it; every
ssh index row points at an enrolment row holding that blob.  A scan of the
support. -/
def rowShaped (store : PayStore) : Address layout → Bool
  | ⟨.book, index⟩ =>
      match bookAt store index with
      | some address => address.length == 32
      | none => true
  | ⟨.enrolment, miniKey⟩ =>
      match enrolmentAt store miniKey with
      | some record => miniKey.length == 32 && isEd25519Blob record.sshBlob &&
          decide (sshIndexAt store record.sshBlob = some miniKey)
      | none => true
  | ⟨.sshIndex, blob⟩ =>
      match sshIndexAt store blob with
      | some miniKey =>
          match enrolmentAt store miniKey with
          | some record => decide (record.sshBlob = blob)
          | none => false
      | none => true
  | ⟨.claim, claimIdentifier⟩ =>
      match claimAt store claimIdentifier with
      | some claim => decide (claim.valid ∧ claim.id = claimIdentifier) && claimMemoCoherent claim &&
          (claim.reason.isSome || (claimConsumptionAt store claimIdentifier).isSome)
      | none => true
  | ⟨.claimConsumption, claimIdentifier⟩ =>
      match claimConsumptionAt store claimIdentifier with
      | some consumed =>
          match claimAt store claimIdentifier with
          | some claim => decide (consumed.valid ∧ consumed.claimId = claimIdentifier ∧ consumed.matchesClaim claim) &&
              consumptionAuthorizationCoherent claim consumed
          | none => false
      | none => true
  | ⟨.pendingOwner, identity⟩ =>
      match pendingOwnerAt store identity with
      | some owner => decide (owner.valid ∧ owner.identityKey = identity ∧
          pendingOwnerHistoryAt store identity owner.epoch = some owner)
      | none => true
  | ⟨.pendingOwnerHistory, (identity, epoch)⟩ =>
      match pendingOwnerHistoryAt store identity epoch with
      | some owner => decide (owner.valid ∧ owner.identityKey = identity ∧ owner.epoch = epoch)
      | none => true
  | ⟨.chainTip, ()⟩ =>
      match chainTipOf store with
      | some tip => decide (0 < tip.slot ∧ tip.slot < 2 ^ 64 ∧
          0 < tip.blockTime ∧ tip.blockTime < 2 ^ 64)
      | none => true
  | ⟨.computeUsage, subject⟩ =>
      match computeUsageAt store subject with
      | none => true
      | some usage => match computeActivationOf store with
        | none => false
        | some activation => decide (activation.valid ∧ activation.day ≤ usage.day)
  | ⟨.computeActivation, ()⟩ =>
      match computeActivationOf store with
      | none => true
      | some activation => decide activation.valid
  | _ => true

/-- A pay cell always holds a tariff, every deposit address is
32 bytes, and the enrolment and ssh index rows agree.  The identity half of the law is the registry's
(`CanonicalCellRegistry.LogicalLaw`). -/
def Law (store : PayStore) : Prop :=
  (tariffOf store).isSome = true ∧
    ∀ address ∈ store.support, rowShaped store address = true

instance (store : PayStore) : Decidable (Law store) := by
  unfold Law
  infer_instance

/-! ## Wire `DREGG/PAY/CELL/v5` -/

def namespaceStream : StreamCodec Namespace where
  encode
    | .tariff => [0]
    | .book => [1]
    | .assignment => [2]
    | .enrolment => [4]
    | .sshIndex => [5]
    | .journal => [6]
    | .claim => [7]
    | .claimConsumption => [8]
    | .pendingOwner => [9]
    | .pendingOwnerHistory => [11]
    | .chainTip => [10]
    | .computeUsage => [12]
    | .computeActivation => [13]
  decodePrefix
    | 0 :: suffix => some (.tariff, suffix)
    | 1 :: suffix => some (.book, suffix)
    | 2 :: suffix => some (.assignment, suffix)
    | 4 :: suffix => some (.enrolment, suffix)
    | 5 :: suffix => some (.sshIndex, suffix)
    | 6 :: suffix => some (.journal, suffix)
    | 7 :: suffix => some (.claim, suffix)
    | 8 :: suffix => some (.claimConsumption, suffix)
    | 9 :: suffix => some (.pendingOwner, suffix)
    | 10 :: suffix => some (.chainTip, suffix)
    | 11 :: suffix => some (.pendingOwnerHistory, suffix)
    | 12 :: suffix => some (.computeUsage, suffix)
    | 13 :: suffix => some (.computeActivation, suffix)
    | _ => none
  decodePrefix_encode := by intro space suffix; cases space <;> rfl

def enrolRecordStream : StreamCodec EnrolRecord :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (StreamCodec.option StreamCodec.nat)
          (StreamCodec.product StreamCodec.nat StreamCodec.nat))))
    (fun record => (record.sshBlob, record.account, record.index, record.leaseUntil,
      record.enrolledSlot))
    (fun (blob, account, index, lease, slot) => ⟨blob, account, index, lease, slot⟩)
    (by intro record; cases record; rfl)

def unattributedStream : StreamCodec Unattributed :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product PayEnrolMemo.journalReasonStream PayEnrolMemo.memoFieldStream))))
    (fun row => (row.index, row.amount, row.slot, row.reason, row.memo))
    (fun (index, amount, slot, reason, memo) => ⟨index, amount, slot, reason, memo⟩)
    (by intro row; cases row; rfl)

def computeUsageStream : StreamCodec ComputeUsage :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat StreamCodec.nat)
    (fun usage => (usage.day, usage.admittedSteps))
    (fun (day, steps) => ⟨day, steps⟩)
    (by intro usage; cases usage; rfl)

def computeActivationStream : StreamCodec ComputeActivation :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (StreamCodec.option StreamCodec.nat) digestStream))
    (fun activation => (activation.day, activation.legacyThroughDay, activation.history))
    (fun (day, prior, history) => ⟨day, prior, history⟩)
    (by intro activation; cases activation; rfl)

def keyStream : (space : Namespace) → StreamCodec (Namespace.Key space)
  | .tariff => unitStream
  | .book => StreamCodec.nat
  | .assignment => StreamCodec.nat
  | .enrolment => bytesStream
  | .sshIndex => bytesStream
  | .journal => bytesStream
  | .claim => bytesStream
  | .claimConsumption => bytesStream
  | .pendingOwner => bytesStream
  | .pendingOwnerHistory => StreamCodec.product bytesStream StreamCodec.nat
  | .chainTip => unitStream
  | .computeUsage => StreamCodec.nat
  | .computeActivation => unitStream

def valueStream : (space : Namespace) → StreamCodec (Namespace.Value space)
  | .tariff => tariffStream
  | .book => bytesStream
  | .assignment => StreamCodec.nat
  | .enrolment => enrolRecordStream
  | .sshIndex => bytesStream
  | .journal => unattributedStream
  | .claim => PayEnrolClaim.claimStream
  | .claimConsumption => PayEnrolClaim.consumptionStream
  | .pendingOwner => PayEnrolClaim.pendingOwnerStream
  | .pendingOwnerHistory => PayEnrolClaim.pendingOwnerStream
  | .chainTip => chainTipStream
  | .computeUsage => computeUsageStream
  | .computeActivation => computeActivationStream

def wireName : String := "DREGG/PAY/CELL/v5"

def wire : Wire layout where
  name := wireName
  namespaces := [.tariff, .book, .assignment, .enrolment, .sshIndex, .journal,
    .claim, .claimConsumption, .pendingOwner, .chainTip, .pendingOwnerHistory,
    .computeUsage, .computeActivation]
  namespaces_complete := by intro space; cases space <;> simp
  namespaceStream := namespaceStream
  keyStream := keyStream
  valueStream := valueStream
  keyCodecId
    | .tariff => "unit"
    | .book => "book-index/nat"
    | .assignment => "book-index/nat"
    | .enrolment => "mini-key32/bytes"
    | .sshIndex => "ssh-ed25519-blob/bytes"
    | .journal => "soltx-nullifier/bytes"
    | .claim => "soltx-nullifier/bytes"
    | .claimConsumption => "soltx-nullifier/bytes"
    | .pendingOwner => "mini-key32/bytes"
    | .pendingOwnerHistory => "mini-key32/bytes+epoch/nat"
    | .chainTip => "unit"
    | .computeUsage => "subject-id/nat"
    | .computeActivation => "unit"
  valueCodecId
    | .tariff => "DREGG/PAY/TARIFF/v3"
    | .book => "address32/bytes"
    | .assignment => "account-id/nat"
    | .enrolment => "DREGG/PAY/ENROLMENT/v1"
    | .sshIndex => "mini-key32/bytes"
    | .journal => "DREGG/PAY/UNATTRIBUTED/v1"
    | .claim => "DREGG/PAY/CLAIM/v2"
    | .claimConsumption => "DREGG/PAY/CLAIM/CONSUMPTION/v2"
    | .pendingOwner => "DREGG/PAY/PENDING-OWNER/v1"
    | .pendingOwnerHistory => "DREGG/PAY/PENDING-OWNER/v1"
    | .chainTip => "DREGG/PAY/CHAIN-TIP/v1"
    | .computeUsage => "DREGG/RUN/COMPUTE-USAGE/v1"
    | .computeActivation => "DREGG/RUN/COMPUTE-ACTIVATION/v1"

def materializer : Materializer layout Digest := StoreCodec.materializer wire

abbrev Cell := Materialized materializer

theorem cell_roundtrip (store : PayStore) :
    StoreCodec.decode wire (StoreCodec.encode wire store) = some store :=
  StoreCodec.decode_encode wire store

theorem cell_canonical {bytes : List UInt8} {store : PayStore}
    (accepted : StoreCodec.decode wire bytes = some store) : StoreCodec.encode wire store = bytes :=
  StoreCodec.decode_reencodes wire accepted

/-! ## Identity and genesis -/

def idCustomization : List UInt8 := "DREGG.PAY.CELL.ID/v1".toUTF8.toList

/-- The pay cell's physical identifier in deployment `domain`. -/
def physicalId (domain : Digest) : Nat :=
  (Sp800185Cshake256.hash idCustomization (digestStream.encode domain)).digest.value

/-- The genesis pay cell: the placeholder tariff, an empty book and no
assignment. -/
def genesisStore : PayStore :=
  (0 : PayStore).set tariffAddress (some genesisDefault)

theorem genesis_law : Law genesisStore := by decide +kernel

theorem genesis_tariff : tariffOf genesisStore = some genesisDefault := by decide +kernel

theorem genesis_nextFree : nextFree genesisStore = 0 := by decide +kernel

/-- Refuting pole of the law: a pay cell without a tariff is not lawful. -/
theorem tariffless_unlawful : ¬ Law (0 : PayStore) := by
  decide +kernel

/-- A lawful enrolled key: its record and its ssh index row. -/
def enrolledFixture : PayStore :=
  (genesisStore.set (enrolmentAddress PayEnrolMemo.fixtureMemo.miniKey)
    (some ⟨PayEnrolMemo.fixtureMemo.sshBlob, 108, some 1, 500168, 900⟩)).set
    (sshIndexAddress PayEnrolMemo.fixtureMemo.sshBlob) (some PayEnrolMemo.fixtureMemo.miniKey)

/-- Satisfiable pole of the enrolment shape. -/
theorem enrolled_fixture_law : Law enrolledFixture := by decide +kernel

/-- Refuting pole: an enrolment row whose ssh key is not indexed is not lawful. -/
theorem unindexed_enrolment_unlawful :
    ¬ Law (genesisStore.set (enrolmentAddress PayEnrolMemo.fixtureMemo.miniKey)
      (some ⟨PayEnrolMemo.fixtureMemo.sshBlob, 108, some 1, 500168, 900⟩)) := by decide +kernel

/-- Refuting pole: an ssh index row naming a key with no enrolment is not lawful. -/
theorem dangling_ssh_index_unlawful :
    ¬ Law (genesisStore.set (sshIndexAddress PayEnrolMemo.fixtureMemo.sshBlob)
      (some PayEnrolMemo.fixtureMemo.miniKey)) := by decide +kernel

/-- Refuting pole of the row shape: a 31-byte deposit address is not lawful. -/
theorem short_address_unlawful :
    ¬ Law (genesisStore.set (bookAddress 0) (some (List.replicate 31 1))) := by
  decide +kernel

theorem pendingOwnerHistory_appendOnly :
    Namespace.discipline .pendingOwnerHistory = .appendOnly := rfl

/-- No enabled rewrite can replace an already recorded pending epoch. -/
theorem pendingOwnerHistory_no_rewrite (store : PayStore) (identity : List UInt8) (epoch : Nat)
    (before after : PayEnrolClaim.PendingOwner)
    (enabled : (Op.write (L := layout) .pendingOwnerHistory (identity, epoch) before after).Enabled store) : False := by
  have wrong := enabled.1
  change Minidregg.Theory.Store.Discipline.appendOnly = .ram at wrong
  cases wrong

private def historyFixtureOwner : PayEnrolClaim.PendingOwner :=
  ⟨List.replicate 32 1, List.replicate 32 2, 1, ⟨3⟩⟩

/-- Current custody and its immutable epoch are installed together. -/
theorem pending_owner_with_history_law :
    Law ((genesisStore.set
      (pendingOwnerHistoryAddress historyFixtureOwner.identityKey historyFixtureOwner.epoch)
      (some historyFixtureOwner)).set (pendingOwnerAddress historyFixtureOwner.identityKey)
      (some historyFixtureOwner)) := by decide +kernel

theorem current_owner_without_history_unlawful :
    ¬Law (genesisStore.set (pendingOwnerAddress historyFixtureOwner.identityKey)
      (some historyFixtureOwner)) := by decide +kernel

theorem history_epoch_mismatch_unlawful :
    ¬Law (genesisStore.set (pendingOwnerHistoryAddress historyFixtureOwner.identityKey 2)
      (some historyFixtureOwner)) := by decide +kernel

theorem computeActivation_appendOnly :
    Namespace.discipline .computeActivation = .appendOnly := rfl

/-- Activation cannot be replaced to mint another free allowance. -/
theorem computeActivation_no_rewrite (store : PayStore) (before after : ComputeActivation)
    (enabled : (Op.write (L := layout) .computeActivation () before after).Enabled store) : False := by
  have wrong := enabled.1
  change Minidregg.Theory.Store.Discipline.appendOnly = .ram at wrong
  cases wrong

/-- Neutral genesis is deliberately inactive until its authenticated boot edge. -/
theorem genesis_compute_inactive : computeActivationOf genesisStore = none := by decide

#assert_axioms computeActivation_appendOnly
#assert_axioms computeActivation_no_rewrite
#assert_axioms genesis_compute_inactive
#assert_axioms pending_owner_with_history_law
#assert_axioms current_owner_without_history_unlawful
#assert_axioms history_epoch_mismatch_unlawful
#assert_axioms pendingOwnerHistory_appendOnly
#assert_axioms pendingOwnerHistory_no_rewrite
#assert_axioms cell_roundtrip
#assert_axioms cell_canonical
#assert_axioms genesis_law
#assert_axioms genesis_tariff
#assert_axioms genesis_nextFree
#assert_axioms tariffless_unlawful
#assert_axioms short_address_unlawful
#assert_axioms enrolled_fixture_law
#assert_axioms unindexed_enrolment_unlawful
#assert_axioms dangling_ssh_index_unlawful

end Minidregg.Kernel.PayCell
