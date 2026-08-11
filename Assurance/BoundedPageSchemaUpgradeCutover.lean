/-
# Assurance.BoundedPageSchemaUpgradeCutover -- durable replicated page upgrade

`Compiler.BoundedPageSchemaUpgrade` supplies the exact V1/V2 codecs, semantic
migration, catalog bytes, and fail-closed admission decision.  This module
binds that decision into one durable cutover payload and composes it with the
existing replicated-settlement safety theorem.

Recovery has one explicit linearization bit.  A prepared record (including a
fully written V2 catalog) still recovers V1; a committed record recovers V2
only when the old bytes, new bytes, and complete admitted payload are exact.
Corruption fails closed.  Page recovery accepts either canonical generation,
while the compiler theorem proves that corresponding V1/V2 pages have equal
canonical semantics and unequal bytes.

At the replicated layer, the complete cutover payload is the event of a
`DurableCommitProtocol.Intent`.  Quorum intersection plus prefix discipline
therefore makes two finalized cutovers at one slot payload-identical, even
across epochs.  This is safety, not a consensus implementation.

**Trust ceiling.**  The operator authorization token remains externally
governed.  `commitMarker = true` is a logical durability boundary, not a proof
about POSIX `fsync`, filesystems, disks, or controllers.  Quorum intersection
and prefix discipline are safety premises; finality progress still requires an
online quorum, eventual network delivery, and responsive replicas.  Digest
separation remains the pair-scoped cryptographic premise in the compiler
module.  None of these boundaries is inferred from successful recovery.
-/
import Compiler.BoundedPageSchemaUpgrade
import Kernel.ReplicatedSettlementFinality

namespace Minidregg.Assurance.BoundedPageSchemaUpgradeCutover

open Minidregg.Compiler.BoundedPageExtensionCatalog
open Minidregg.Compiler.BoundedPageSchemaUpgrade
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ReplicatedSettlementFinality
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## The exact admitted cutover payload -/

/-- Every byte and governance pin needed to distinguish one cutover is in the
replicated/durable event.  Catalog bytes bind all three dependent controller
rows, including schema, codec, root-domain, version, and capacity pins. -/
structure CutoverPayload where
  transitionId : Digest
  fromVersion : Nat
  toVersion : Nat
  oldCatalogBytes : List UInt8
  newCatalogBytes : List UInt8
  oldCatalogDigest : Digest
  newCatalogDigest : Digest
  operatorSetRoot : Digest
  operatorEpoch : Nat
  authorizationToken : Digest
  deriving DecidableEq, Repr

def payloadOfRequest (request : UpgradeRequest) : CutoverPayload where
  transitionId := request.policy.policyId
  fromVersion := request.fromVersion
  toVersion := request.toVersion
  oldCatalogBytes := catalogCodec.encode request.fromCatalog
  newCatalogBytes := catalogCodec.encode request.toCatalog
  oldCatalogDigest := request.fromCatalog.contentAddress.digest
  newCatalogDigest := request.toCatalog.contentAddress.digest
  operatorSetRoot := request.policy.operatorSetRoot
  operatorEpoch := request.policy.operatorEpoch
  authorizationToken := request.presentedAuthorization

def approvedPayload : CutoverPayload := payloadOfRequest approvedRequest

@[simp] theorem approved_payload_versions :
    approvedPayload.fromVersion = 1 ∧ approvedPayload.toVersion = 2 := by
  decide

@[simp] theorem approved_payload_catalog_bytes :
    approvedPayload.oldCatalogBytes = catalogCodec.encode deployedCatalog ∧
      approvedPayload.newCatalogBytes = catalogCodec.encode upgradedCatalog := by
  exact ⟨rfl, rfl⟩

theorem approved_payload_bytes_distinct :
    approvedPayload.oldCatalogBytes ≠ approvedPayload.newCatalogBytes :=
  catalog_migration_changes_canonical_bytes.symm

/-! ## Fail-closed durable preparation and recovery -/

/-- The abstract durable image.  `stagedNewCatalog` may have reached storage
before the commit marker; that does not make it active. -/
structure DurableCutoverRecord where
  payload : CutoverPayload
  oldCatalog : List UInt8
  stagedNewCatalog : Option (List UInt8)
  commitMarker : Bool
  deriving DecidableEq, Repr

inductive RecoveryResult where
  | activeV1
  | activeV2
  | corrupt
  deriving DecidableEq, Repr

/-- Exact recovery order matters.  The old image and full payload are checked
even before a non-committed preparation may recover V1.  V2 additionally
requires the marker and exact staged V2 bytes. -/
def recover (expected : CutoverPayload)
    (record : DurableCutoverRecord) : RecoveryResult :=
  if record.payload != expected then .corrupt
  else if record.oldCatalog != expected.oldCatalogBytes then .corrupt
  else if !record.commitMarker then .activeV1
  else if record.stagedNewCatalog != some expected.newCatalogBytes then .corrupt
  else .activeV2

def preparedRecord (payload : CutoverPayload) : DurableCutoverRecord where
  payload := payload
  oldCatalog := payload.oldCatalogBytes
  stagedNewCatalog := some payload.newCatalogBytes
  commitMarker := false

def committedRecord (payload : CutoverPayload) : DurableCutoverRecord where
  payload := payload
  oldCatalog := payload.oldCatalogBytes
  stagedNewCatalog := some payload.newCatalogBytes
  commitMarker := true

@[simp] theorem recover_prepared (payload : CutoverPayload) :
    recover payload (preparedRecord payload) = .activeV1 := by
  simp [recover, preparedRecord]

@[simp] theorem recover_committed (payload : CutoverPayload) :
    recover payload (committedRecord payload) = .activeV2 := by
  simp [recover, committedRecord]

/-- A crash after V2 bytes reach the durable image but before the commit marker
has the exact old-generation recovery meaning. -/
theorem crash_before_marker_keeps_v1 (payload : CutoverPayload)
    (staged : Option (List UInt8)) :
    recover payload
      { payload := payload
        oldCatalog := payload.oldCatalogBytes
        stagedNewCatalog := staged
        commitMarker := false } = .activeV1 := by
  simp [recover]

/-- A commit marker cannot bless wrong V2 bytes. -/
theorem committed_corrupt_new_bytes_rejected (payload : CutoverPayload)
    (bytes : List UInt8) (wrong : bytes ≠ payload.newCatalogBytes) :
    recover payload
      { payload := payload
        oldCatalog := payload.oldCatalogBytes
        stagedNewCatalog := some bytes
        commitMarker := true } = .corrupt := by
  simp [recover, wrong]

/-- A marker for another admitted-looking payload is not replay-compatible. -/
theorem mismatched_payload_rejected (expected actual : CutoverPayload)
    (different : actual ≠ expected) (oldBytes : List UInt8)
    (newBytes : Option (List UInt8)) (marker : Bool) :
    recover expected
      { payload := actual
        oldCatalog := oldBytes
        stagedNewCatalog := newBytes
        commitMarker := marker } = .corrupt := by
  simp [recover, different]

def EligibleAfterFinality (payload : CutoverPayload)
    (record : DurableCutoverRecord) : Prop :=
  recover payload record = .activeV2

theorem prepared_replica_not_eligible_after_finality (payload : CutoverPayload) :
    ¬ EligibleAfterFinality payload (preparedRecord payload) := by
  simp [EligibleAfterFinality]

theorem committed_replica_eligible_after_finality (payload : CutoverPayload) :
    EligibleAfterFinality payload (committedRecord payload) := by
  simp [EligibleAfterFinality]

/-! ## Canonical mixed-version page decoding -/

inductive MixedDecodeError where
  | unrecognized
  | noncanonicalV1
  | noncanonicalV2
  deriving DecidableEq, Repr

inductive DecodedPage (kind : PageKind) where
  | v1 (state : kind.State)
  | v2 (state : kind.State)

def DecodedPage.semantics {kind : PageKind} :
    DecodedPage kind -> Semantic kind
  | .v1 state => semanticProjection kind state
  | .v2 state => semanticProjection kind state

/-- Prefer V1 only after exact re-encoding; otherwise try V2 and impose the
same canonicality check.  A permissive decoder cannot smuggle alternate bytes
into a recovered page. -/
def decodeMixed (kind : PageKind) (bytes : List UInt8) :
    Except MixedDecodeError (DecodedPage kind) :=
  match (controller kind).codec.decode bytes with
  | some state =>
      if oldCanonicalBytes kind state = bytes then .ok (.v1 state)
      else .error .noncanonicalV1
  | none =>
      match (controllerV2 kind).codec.decode bytes with
      | some state =>
          if newCanonicalBytes kind state = bytes then .ok (.v2 state)
          else .error .noncanonicalV2
      | none => .error .unrecognized

@[simp] theorem decode_mixed_old (kind : PageKind) (state : kind.State) :
    decodeMixed kind (oldCanonicalBytes kind state) = .ok (.v1 state) := by
  simp [decodeMixed, oldCanonicalBytes, (controller kind).codec.decode_encode]

@[simp] theorem decode_mixed_new (kind : PageKind) (state : kind.State) :
    decodeMixed kind (newCanonicalBytes kind state) = .ok (.v2 state) := by
  simp [decodeMixed, old_decoder_rejects_new, decode_new_migration]

theorem mixed_decoded_semantics_agree (kind : PageKind) (state : kind.State) :
    (DecodedPage.v1 state).semantics =
      (DecodedPage.v2 (migrate kind state)).semantics :=
  migration_preserves_semantic_projection kind state

/-! ## Replicated finality binds the complete payload -/

abbrev CutoverIntent := Intent Nat Unit Unit CutoverPayload
abbrev CutoverCandidate := Candidate Nat Unit Unit CutoverPayload

def cutoverIntent (transactionId : Nat)
    (payload : CutoverPayload) : CutoverIntent where
  transactionId := transactionId
  rootWrites := []
  nullifiers := []
  exactCharge := 0
  event := payload

def cutoverCandidate (epoch transactionId : Nat)
    (priorLog : List CutoverIntent) (payload : CutoverPayload) :
    CutoverCandidate where
  epoch := epoch
  priorLog := priorLog
  intent := cutoverIntent transactionId payload

theorem finalized_cutover_payload_unique_at_slot
    {Node : Type} [DecidableEq Node]
    {quorums : QuorumSystem Node}
    {book : VoteBook (Node := Node) (TxId := Nat) (CellId := Unit)
      (Nullifier := Unit) (Event := CutoverPayload)}
    (discipline : PrefixDiscipline book)
    {left right : CutoverCandidate}
    (leftFinal : Finalized quorums book left)
    (rightFinal : Finalized quorums book right)
    (sameSlot : left.slot = right.slot) :
    left.intent.event = right.intent.event := by
  exact congrArg Intent.event
    (finalized_transaction_unique_at_slot discipline leftFinal rightFinal sameSlot)

def ConflictingCutoversAtSlot (left right : CutoverCandidate) : Prop :=
  left.slot = right.slot ∧ left.intent.event ≠ right.intent.event

theorem no_conflicting_finalized_cutovers
    {Node : Type} [DecidableEq Node]
    {quorums : QuorumSystem Node}
    {book : VoteBook (Node := Node) (TxId := Nat) (CellId := Unit)
      (Nullifier := Unit) (Event := CutoverPayload)}
    (discipline : PrefixDiscipline book)
    {left right : CutoverCandidate}
    (leftFinal : Finalized quorums book left)
    (rightFinal : Finalized quorums book right) :
    ¬ ConflictingCutoversAtSlot left right := by
  rintro ⟨sameSlot, different⟩
  exact different
    (finalized_cutover_payload_unique_at_slot discipline leftFinal rightFinal
      sameSlot)

/-! ## Closed non-vacuous finality and durable cutover witness -/

namespace ClosedInstance

inductive Node where
  | only
  deriving DecidableEq, Repr

def candidate : CutoverCandidate :=
  cutoverCandidate 7 700 [] approvedPayload

def book : VoteBook (Node := Node) (TxId := Nat) (CellId := Unit)
    (Nullifier := Unit) (Event := CutoverPayload) :=
  fun _ => [candidate]

def quorums : QuorumSystem Node where
  isQuorum voters := .only ∈ voters
  intersects := by
    intro left right leftQuorum rightQuorum
    exact ⟨.only, leftQuorum, rightQuorum⟩

theorem discipline : PrefixDiscipline book := by
  constructor
  intro node left right leftMember rightMember
  have leftExact : left = candidate := by
    simpa [book] using leftMember
  have rightExact : right = candidate := by
    simpa [book] using rightMember
  subst left
  subst right
  exact Or.inl ⟨[], by simp⟩

def finalized : Finalized quorums book candidate where
  voters := {.only}
  quorum := by simp [quorums]
  voted := by
    intro node member
    have nodeExact : node = .only := by simpa using member
    subst node
    simp [book]

theorem finalized_nonempty : Nonempty (Finalized quorums book candidate) :=
  ⟨finalized⟩

theorem finalized_payload_exact :
    candidate.intent.event = approvedPayload := rfl

theorem finalized_committed_record_recovers_v2 :
    recover candidate.intent.event (committedRecord approvedPayload) =
      .activeV2 := by
  simpa only [candidate, cutoverCandidate, cutoverIntent] using
    (recover_committed approvedPayload)

theorem finalized_prepared_record_recovers_v1 :
    recover candidate.intent.event (preparedRecord approvedPayload) =
      .activeV1 := by
  simpa only [candidate, cutoverCandidate, cutoverIntent] using
    (recover_prepared approvedPayload)

end ClosedInstance

/-! ## Explicit deployment ceilings -/

/-- External operator/signature governance must refine issuance of the exact
token checked by `admit`; this model does not verify signatures itself. -/
structure OperatorGovernanceRefinement
    (IssuedApprovedToken : Prop) : Prop where
  issuedApprovedToken : IssuedApprovedToken

/-- A physical implementation must prove that its sync/storage transition
refines the logical change from `preparedRecord` to `committedRecord`. -/
structure PhysicalDurabilityRefinement
    (SyncedMarkerSurvivesDeclaredFaultDomain : Prop) : Prop where
  syncedMarkerSurvivesDeclaredFaultDomain :
    SyncedMarkerSurvivesDeclaredFaultDomain

/-- Safety does not manufacture progress.  Availability, fair delivery, and
responsive voting remain deployment premises exactly as in
`ReplicatedSettlementFinality`. -/
structure NetworkLivenessRefinement
    (OnlineQuorumExists FairDelivery ResponsiveReplicas : Prop) : Prop where
  onlineQuorumExists : OnlineQuorumExists
  fairDelivery : FairDelivery
  responsiveReplicas : ResponsiveReplicas

/-! ## Axiom pins -/

/-- info: 'Minidregg.Assurance.BoundedPageSchemaUpgradeCutover.no_conflicting_finalized_cutovers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms no_conflicting_finalized_cutovers
/-- info: 'Minidregg.Assurance.BoundedPageSchemaUpgradeCutover.mixed_decoded_semantics_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixed_decoded_semantics_agree
/-- info: 'Minidregg.Assurance.BoundedPageSchemaUpgradeCutover.ClosedInstance.finalized_committed_record_recovers_v2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClosedInstance.finalized_committed_record_recovers_v2

end Minidregg.Assurance.BoundedPageSchemaUpgradeCutover
