/-
# Kernel.QuotaGcSettlement -- quota admission and reachability-safe reclamation

Bounded pages and canonical resource leases need a common abuse-control and
reclamation law.  A page being finite does not by itself prevent byte or proof
work exhaustion, and an expired lease does not by itself authorize deleting a
live reference or finalized history.

This module gives the missing logical joint:

* every command is checked against an exact finite slot, byte, ten-lane work,
  side-effect, and fee budget;
* lease-backed insertion and lease rotation use the canonical resource book;
* tombstone and compaction require an expired lease and prove that the target
  is outside the root/reachability/finalized protection closure;
* one scoped authority names the exact page epoch, command digest, limits, and
  tariff-derived resource fee;
* the page image and canonical resource book settle in one replay-safe durable
  intent with authority, clock, and protection-index read guards.

The protection graph here is the authoritative logical graph.  Discovering it
with a production crawler, interpreting wall clock as a logical height,
physically reclaiming bytes, and guaranteeing eventual collection remain
explicit implementation/liveness obligations at the end of the module.
-/
import Kernel.AuthorizedResourceCharge

namespace Minidregg.Kernel.QuotaGcSettlement

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

abbrev ContentId := Nat

/-! ## A finite page and its semantic protection graph -/

inductive Status
  | live
  | tombstoned (epoch : Nat)
  deriving DecidableEq, Repr

structure Object where
  contentId : ContentId
  owner : AccountId
  leaseId : LeaseId
  payload : List UInt8
  status : Status
  deriving DecidableEq, Repr

/-- Capacity is in the type: no command can address a fifth slot of a four-slot
page.  Byte and work ceilings remain independently configurable below. -/
structure Page (capacity : Nat) where
  epoch : Nat
  slots : Fin capacity -> Option Object

namespace Page

variable {capacity : Nat}

def occupied (page : Page capacity) : Finset (Fin capacity) :=
  Finset.univ.filter fun slot => (page.slots slot).isSome

def occupiedCount (page : Page capacity) : Nat := page.occupied.card

def usedBytes (page : Page capacity) : Nat :=
  ∑ slot, match page.slots slot with
    | some object => object.payload.length
    | none => 0

def liveIds (page : Page capacity) : Finset ContentId :=
  Finset.univ.biUnion fun slot =>
    match page.slots slot with
    | some object =>
        match object.status with
        | .live => {object.contentId}
        | .tombstoned _ => ∅
    | none => ∅

/-- Content identities are unique among occupied slots. -/
def Valid (page : Page capacity) : Prop :=
  forall left right leftObject rightObject,
    page.slots left = some leftObject ->
    page.slots right = some rightObject ->
    leftObject.contentId = rightObject.contentId -> left = right

theorem occupiedCount_le_capacity (page : Page capacity) :
    page.occupiedCount <= capacity := by
  rw [occupiedCount]
  exact le_trans (Finset.card_le_card (Finset.filter_subset _ _))
    (by simp)

noncomputable def lookup (page : Page capacity) (contentId : ContentId) : Option Object :=
  (Finset.univ.toList.filterMap fun slot =>
    match page.slots slot with
    | some object => if object.contentId = contentId then some object else none
    | none => none).head?

end Page

/-- Logical roots, outgoing edges, and history-finality marks.  This is not a
crawler result: a physical indexer must prove that its discovered view equals
this semantic value before using the kernel admission theorem. -/
structure Protection where
  roots : List ContentId
  edges : List (ContentId × ContentId)
  historyFinalized : List ContentId

def Protection.outgoing (protection : Protection)
    (source : ContentId) : List ContentId :=
  protection.edges.filterMap fun edge =>
    if edge.1 = source then some edge.2 else none

inductive Reachable (protection : Protection) : ContentId -> ContentId -> Prop
  | refl (contentId) : Reachable protection contentId contentId
  | step {source next target} :
      next ∈ protection.outgoing source ->
      Reachable protection next target ->
      Reachable protection source target

/-- A target is protected by an explicit root, finalized history, or the
transitive outgoing closure of a *different* live object.  Excluding the target
as its own source lets an otherwise unreachable live object be tombstoned. -/
def Protected {capacity : Nat} (page : Page capacity)
    (protection : Protection) (target : ContentId) : Prop :=
  target ∈ protection.roots \/
    target ∈ protection.historyFinalized \/
    exists slot object,
      page.slots slot = some object /\
      object.status = .live /\
      object.contentId ≠ target /\
      Reachable protection object.contentId target

theorem protected_of_live_direct_reference
    {capacity : Nat} {page : Page capacity} {protection : Protection}
    {slot : Fin capacity} {source : Object} {target : ContentId}
    (stored : page.slots slot = some source)
    (live : source.status = .live)
    (different : source.contentId ≠ target)
    (edge : target ∈ protection.outgoing source.contentId) :
    Protected page protection target := by
  exact Or.inr (Or.inr ⟨slot, source, stored, live, different,
    .step edge (.refl target)⟩)

theorem protected_of_finalized
    {capacity : Nat} {page : Page capacity} {protection : Protection}
    {target : ContentId}
    (finalized : target ∈ protection.historyFinalized) :
    Protected page protection target :=
  Or.inr (Or.inl finalized)

/-! ## Epoch-indexed page commands -/

inductive Command (capacity : Nat)
  | put (expectedEpoch height : Nat) (slot : Fin capacity) (object : Object)
  | renew (expectedEpoch height : Nat) (slot : Fin capacity) (before : Object)
      (newLeaseId : LeaseId) (rate epochs : Nat)
  | tombstone (expectedEpoch height : Nat) (slot : Fin capacity) (before : Object)
  | compact (expectedEpoch height : Nat) (slot : Fin capacity) (before : Object)
  deriving Repr

namespace Command

variable {capacity : Nat}

def expectedEpoch : Command capacity -> Nat
  | .put epoch _ _ _ => epoch
  | .renew epoch _ _ _ _ _ _ => epoch
  | .tombstone epoch _ _ _ => epoch
  | .compact epoch _ _ _ => epoch

def height : Command capacity -> Nat
  | .put _ height _ _ => height
  | .renew _ height _ _ _ _ _ => height
  | .tombstone _ height _ _ => height
  | .compact _ height _ _ => height

def target : Command capacity -> Object
  | .put _ _ _ object => object
  | .renew _ _ _ before _ _ _ => before
  | .tombstone _ _ _ before => before
  | .compact _ _ _ before => before

def slot : Command capacity -> Fin capacity
  | .put _ _ slot _ => slot
  | .renew _ _ slot _ _ _ _ => slot
  | .tombstone _ _ slot _ => slot
  | .compact _ _ slot _ => slot

def postObject? : Command capacity -> Option Object
  | .put _ _ _ object => some object
  | .renew _ _ _ before newLeaseId _ _ =>
      some { before with leaseId := newLeaseId }
  | .tombstone _ height _ before =>
      some { before with status := .tombstoned height }
  | .compact _ _ _ _ => none

def apply (page : Page capacity) (command : Command capacity) : Page capacity where
  epoch := page.epoch + 1
  slots := Function.update page.slots command.slot command.postObject?

@[simp] theorem apply_epoch (page : Page capacity) (command : Command capacity) :
    (command.apply page).epoch = page.epoch + 1 := rfl

@[simp] theorem apply_target_slot
    (page : Page capacity) (command : Command capacity) :
    (command.apply page).slots command.slot = command.postObject? := by
  simp [apply]

def tag : Command capacity -> Nat
  | .put .. => 0
  | .renew .. => 1
  | .tombstone .. => 2
  | .compact .. => 3

end Command

/-! ## Canonical page and graph bytes -/

def encodeNat (value : Nat) : List UInt8 := List.replicate value 0 ++ [1]

def encodeStatus : Status -> List UInt8
  | .live => [0]
  | .tombstoned epoch => 1 :: encodeNat epoch

def Object.canonicalBytes (object : Object) : List UInt8 :=
  encodeNat object.contentId ++ encodeNat object.owner ++ encodeNat object.leaseId ++
    encodeNat object.payload.length ++ object.payload ++ encodeStatus object.status

def Page.canonicalBytes {capacity : Nat} (page : Page capacity) : List UInt8 :=
  211 :: encodeNat capacity ++ encodeNat page.epoch ++
    (List.ofFn page.slots).flatMap fun
      | none => [0]
      | some object =>
          1 :: encodeNat object.canonicalBytes.length ++ object.canonicalBytes

def Protection.canonicalBytes (protection : Protection) : List UInt8 :=
  215 ::
    protection.roots.flatMap encodeNat ++ [216] ++
    protection.edges.flatMap
      (fun edge => encodeNat edge.1 ++ encodeNat edge.2) ++ [217] ++
    protection.historyFinalized.flatMap encodeNat

/-! ## Canonical leases and exact quota accounting -/

def LeaseMatches (book : Book) (object : Object) (record : LeaseRecord) : Prop :=
  book.leases object.leaseId = some record /\
    record.holder = object.owner

def ActiveLease (book : Book) (object : Object) (height : Nat) : Prop :=
  exists record, LeaseMatches book object record /\ height <= record.expiresAt

def ExpiredLease (book : Book) (object : Object) (height : Nat) : Prop :=
  exists record, LeaseMatches book object record /\ record.expiresAt < height

/-- Non-renewal operations settle a canonical fee posting.  Renewal rotates to
a fresh canonical prepaid lease id; its resource debit is the prepaid amount. -/
structure Config where
  collector : AccountId
  lessor : AccountId
  asset : AssetId
  baseFee : Nat
  feePerPayloadByte : Nat

def Command.semanticFee {capacity : Nat} (config : Config)
    (command : Command capacity) : Nat :=
  config.baseFee + config.feePerPayloadByte * command.target.payload.length

def Command.resourceOperation {capacity : Nat} (config : Config) :
    Command capacity -> Operation
  | command@(.put _ _ _ object) =>
      .fee object.owner config.collector config.asset (command.semanticFee config)
  | .renew _ height _ before newLeaseId rate epochs =>
      .lease newLeaseId before.owner config.lessor config.asset rate epochs height
  | command@(.tombstone _ _ _ before) =>
      .fee before.owner config.collector config.asset (command.semanticFee config)
  | command@(.compact _ _ _ before) =>
      .fee before.owner config.collector config.asset (command.semanticFee config)

/-- Hostile work cannot be hidden in the resource posting: page scan and every
outgoing edge of an occupied object are charged by the logical model. -/
def protectionWork {capacity : Nat} (page : Page capacity)
    (protection : Protection) : Nat :=
  capacity + ∑ slot, match page.slots slot with
    | some object => (protection.outgoing object.contentId).length
    | none => 0

/-- The page component of the exact charge.  The canonical resource component
is added below, so this vector deliberately contributes zero fee/lease debit. -/
def pageCharge {capacity : Nat} (page : Page capacity)
    (protection : Protection) (command : Command capacity) : Charge
  | .incidences => 1
  | .turnBytes => page.canonicalBytes.length +
      (command.apply page).canonicalBytes.length
  | .memoryTouches => capacity
  | .witnessBytes => 0
  | .proofWork => protectionWork page protection
  | .storageBytes => (command.apply page).canonicalBytes.length
  | .networkBytes => 0
  | .sideEffectCount => 3 -- page write, resource write, receipt append
  | .feeDebit => 0
  | .leaseByteBlocks => 0

structure Limits where
  maxOccupied : Nat
  maxPageBytes : Nat
  available : Charge

/-- Shape-specific admission.  All constructors name the exact object observed
in the exact slot.  Tombstone and compaction both carry negative protection
evidence; expiry alone is never sufficient. -/
inductive Allowed {capacity : Nat} (page : Page capacity)
    (protection : Protection) (book : Book) : Command capacity -> Prop
  | put {expectedEpoch height slot object} :
      page.slots slot = none ->
      object.status = .live ->
      (forall occupied existing, page.slots occupied = some existing ->
        existing.contentId ≠ object.contentId) ->
      ActiveLease book object height ->
      Allowed page protection book (.put expectedEpoch height slot object)
  | renew {expectedEpoch height slot before newLeaseId rate epochs} :
      page.slots slot = some before ->
      before.status = .live ->
      0 < epochs ->
      Allowed page protection book
        (.renew expectedEpoch height slot before newLeaseId rate epochs)
  | tombstone {expectedEpoch height slot before} :
      page.slots slot = some before ->
      before.status = .live ->
      ExpiredLease book before height ->
      Not (Protected page protection before.contentId) ->
      Allowed page protection book (.tombstone expectedEpoch height slot before)
  | compact {expectedEpoch height slot before tombstonedAt} :
      page.slots slot = some before ->
      before.status = .tombstoned tombstonedAt ->
      ExpiredLease book before height ->
      Not (Protected page protection before.contentId) ->
      Allowed page protection book (.compact expectedEpoch height slot before)

/-! ## One authority-bounded admitted plan -/

structure Grant where
  subject : SubjectId
  domain : Digest
  pageCell : CellId
  commandDigest : Digest
  notBefore : Nat
  notAfter : Nat
  maxEpoch : Nat
  maxOccupied : Nat
  maxPageBytes : Nat
  maxCharge : Charge

def Grant.canonicalBytes (grant : Grant) : List UInt8 :=
  218 :: encodeNat grant.subject.value ++ encodeNat grant.domain.value ++
    encodeNat grant.pageCell.value ++ encodeNat grant.commandDigest.value ++
    encodeNat grant.notBefore ++ encodeNat grant.notAfter ++
    encodeNat grant.maxEpoch ++ encodeNat grant.maxOccupied ++
    encodeNat grant.maxPageBytes ++
    encodeNat (AuthorizedResourceCharge.chargeCode grant.maxCharge)

def Command.canonicalBytes {capacity : Nat} (command : Command capacity) : List UInt8 :=
  212 :: encodeNat command.tag ++ encodeNat command.expectedEpoch ++
    encodeNat command.height ++ encodeNat command.slot.val ++
    command.target.canonicalBytes ++
    match command with
    | .renew _ _ _ _ newLeaseId rate epochs =>
        encodeNat newLeaseId ++ encodeNat rate ++ encodeNat epochs
    | _ => []

def commandDigest {capacity : Nat} (rootBytes : List UInt8 -> Digest)
    (page : Page capacity) (command : Command capacity) : Digest :=
  rootBytes (page.canonicalBytes ++ command.canonicalBytes)

structure ScopedAuthority {capacity : Nat}
    (rootBytes : List UInt8 -> Digest) (grant : Grant) (limits : Limits)
    (page : Page capacity) (command : Command capacity)
    (context : AuthorizedResourceCharge.RequestContext)
    (resourceFee : Nat) : Prop where
  subject : context.subject = grant.subject
  domain : context.domain = grant.domain
  commandBound : commandDigest rootBytes page command = grant.commandDigest
  heightFrom : grant.notBefore <= command.height
  heightUntil : command.height <= grant.notAfter
  contextHeight : context.height = command.height
  epochCeiling : command.expectedEpoch <= grant.maxEpoch
  occupiedCeiling : limits.maxOccupied <= grant.maxOccupied
  byteCeiling : limits.maxPageBytes <= grant.maxPageBytes
  chargeCeiling : limits.available <= grant.maxCharge
  feeCeiling : resourceFee <= grant.maxCharge .feeDebit

def totalCharge
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation} {capacity : Nat}
    (manifest : AuthorizedResourceCharge.DeploymentManifest)
    (accepted : Accepted pre operation) (page : Page capacity)
    (protection : Protection) (command : Command capacity) : Charge :=
  AuthorizedResourceCharge.exactCharge manifest accepted +
    pageCharge page protection command

@[simp] theorem totalCharge_feeDebit
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {operation : Operation} {capacity : Nat}
    (manifest : AuthorizedResourceCharge.DeploymentManifest)
    (accepted : Accepted pre operation) (page : Page capacity)
    (protection : Protection) (command : Command capacity) :
    totalCharge manifest accepted page protection command .feeDebit =
      AuthorizedResourceCharge.exactCharge manifest accepted .feeDebit := by
  rfl

/-- A shallow algebraic projection used by deployments whose tariff prices
only incidence admission.  It deliberately avoids normalizing any of the
unpriced byte/proof coordinates, which may contain noncomputable codecs. -/
theorem incidenceOnlyBillable
    (tariff : AuthorizedResourceCharge.Tariff) (charge : Charge) (fee : Nat)
    (incidenceCharge : charge .incidences = 1)
    (incidencePrice : tariff.unitFee .incidences = fee)
    (zeroOther : forall lane, lane ≠ .incidences -> tariff.unitFee lane = 0) :
    tariff.billable charge = fee := by
  unfold AuthorizedResourceCharge.Tariff.billable
  rw [incidenceCharge, incidencePrice,
    zeroOther .turnBytes (by decide),
    zeroOther .memoryTouches (by decide),
    zeroOther .witnessBytes (by decide),
    zeroOther .proofWork (by decide),
    zeroOther .storageBytes (by decide),
    zeroOther .networkBytes (by decide),
    zeroOther .sideEffectCount (by decide)]
  omega

structure Admission
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {capacity : Nat}
    (manifest : AuthorizedResourceCharge.DeploymentManifest)
    (config : Config) (limits : Limits) (page : Page capacity)
    (protection : Protection) (command : Command capacity)
    (accepted : Accepted pre (command.resourceOperation config)) : Prop where
  currentEpoch : command.expectedEpoch = page.epoch
  preValid : page.Valid
  allowed : Allowed page protection (logicalBook pre.logical) command
  postValid : (command.apply page).Valid
  occupiedBound : (command.apply page).occupiedCount <= limits.maxOccupied
  byteBound : (command.apply page).canonicalBytes.length <= limits.maxPageBytes
  exactFunded : totalCharge manifest accepted page protection command <= limits.available
  operationFeeExact :
    (command.resourceOperation config).feeDebit =
      AuthorizedResourceCharge.exactCharge manifest accepted .feeDebit

/-! ## Safety and rejection teeth -/

theorem compact_not_protected
    {capacity : Nat} {page : Page capacity} {protection : Protection}
    {book : Book} {expectedEpoch height : Nat} {slot : Fin capacity}
    {before : Object}
    (allowed : Allowed page protection book
      (.compact expectedEpoch height slot before)) :
    Not (Protected page protection before.contentId) := by
  cases allowed with
  | compact _ _ _ safe => exact safe

theorem tombstone_not_protected
    {capacity : Nat} {page : Page capacity} {protection : Protection}
    {book : Book} {expectedEpoch height : Nat} {slot : Fin capacity}
    {before : Object}
    (allowed : Allowed page protection book
      (.tombstone expectedEpoch height slot before)) :
    Not (Protected page protection before.contentId) := by
  cases allowed with
  | tombstone _ _ _ safe => exact safe

theorem finalized_content_cannot_compact
    {capacity : Nat} {page : Page capacity} {protection : Protection}
    {book : Book} {expectedEpoch height : Nat} {slot : Fin capacity}
    {before : Object}
    (finalized : before.contentId ∈ protection.historyFinalized) :
    Not (Allowed page protection book
      (.compact expectedEpoch height slot before)) := by
  intro allowed
  exact compact_not_protected allowed (protected_of_finalized finalized)

theorem finalized_content_cannot_tombstone
    {capacity : Nat} {page : Page capacity} {protection : Protection}
    {book : Book} {expectedEpoch height : Nat} {slot : Fin capacity}
    {before : Object}
    (finalized : before.contentId ∈ protection.historyFinalized) :
    Not (Allowed page protection book
      (.tombstone expectedEpoch height slot before)) := by
  intro allowed
  exact tombstone_not_protected allowed (protected_of_finalized finalized)

theorem live_reachable_content_cannot_compact
    {capacity : Nat} {page : Page capacity} {protection : Protection}
    {book : Book} {expectedEpoch height : Nat} {slot sourceSlot : Fin capacity}
    {before source : Object}
    (sourceStored : page.slots sourceSlot = some source)
    (sourceLive : source.status = .live)
    (different : source.contentId ≠ before.contentId)
    (reachable : Reachable protection source.contentId before.contentId) :
    Not (Allowed page protection book
      (.compact expectedEpoch height slot before)) := by
  intro allowed
  exact compact_not_protected allowed
    (Or.inr (Or.inr ⟨sourceSlot, source, sourceStored, sourceLive,
      different, reachable⟩))

theorem live_reachable_content_cannot_tombstone
    {capacity : Nat} {page : Page capacity} {protection : Protection}
    {book : Book} {expectedEpoch height : Nat} {slot sourceSlot : Fin capacity}
    {before source : Object}
    (sourceStored : page.slots sourceSlot = some source)
    (sourceLive : source.status = .live)
    (different : source.contentId ≠ before.contentId)
    (reachable : Reachable protection source.contentId before.contentId) :
    Not (Allowed page protection book
      (.tombstone expectedEpoch height slot before)) := by
  intro allowed
  exact tombstone_not_protected allowed
    (Or.inr (Or.inr ⟨sourceSlot, source, sourceStored, sourceLive,
      different, reachable⟩))

theorem no_admission_if_byte_quota_exceeded
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {capacity : Nat}
    {manifest : AuthorizedResourceCharge.DeploymentManifest}
    {config : Config} {limits : Limits} {page : Page capacity}
    {protection : Protection} {command : Command capacity}
    {accepted : Accepted pre (command.resourceOperation config)}
    (exceeded : limits.maxPageBytes <
      (command.apply page).canonicalBytes.length) :
    Not (Admission manifest config limits page protection command accepted) := by
  intro admitted
  exact (Nat.not_le_of_gt exceeded) admitted.byteBound

theorem no_admission_if_capacity_quota_exceeded
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {capacity : Nat}
    {manifest : AuthorizedResourceCharge.DeploymentManifest}
    {config : Config} {limits : Limits} {page : Page capacity}
    {protection : Protection} {command : Command capacity}
    {accepted : Accepted pre (command.resourceOperation config)}
    (exceeded : limits.maxOccupied < (command.apply page).occupiedCount) :
    Not (Admission manifest config limits page protection command accepted) := by
  intro admitted
  exact (Nat.not_le_of_gt exceeded) admitted.occupiedBound

theorem no_admission_if_work_quota_exceeded
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {capacity : Nat}
    {manifest : AuthorizedResourceCharge.DeploymentManifest}
    {config : Config} {limits : Limits} {page : Page capacity}
    {protection : Protection} {command : Command capacity}
    {accepted : Accepted pre (command.resourceOperation config)}
    (exceeded : limits.available .proofWork <
      totalCharge manifest accepted page protection command .proofWork) :
    Not (Admission manifest config limits page protection command accepted) := by
  intro admitted
  exact (Nat.not_le_of_gt exceeded) (admitted.exactFunded .proofWork)

theorem no_admission_if_side_effect_quota_exceeded
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {capacity : Nat}
    {manifest : AuthorizedResourceCharge.DeploymentManifest}
    {config : Config} {limits : Limits} {page : Page capacity}
    {protection : Protection} {command : Command capacity}
    {accepted : Accepted pre (command.resourceOperation config)}
    (exceeded : limits.available .sideEffectCount <
      totalCharge manifest accepted page protection command .sideEffectCount) :
    Not (Admission manifest config limits page protection command accepted) := by
  intro admitted
  exact (Nat.not_le_of_gt exceeded) (admitted.exactFunded .sideEffectCount)

theorem no_admission_if_resource_fee_mismatched
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {capacity : Nat}
    {manifest : AuthorizedResourceCharge.DeploymentManifest}
    {config : Config} {limits : Limits} {page : Page capacity}
    {protection : Protection} {command : Command capacity}
    {accepted : Accepted pre (command.resourceOperation config)}
    (mismatch : (command.resourceOperation config).feeDebit ≠
      AuthorizedResourceCharge.exactCharge manifest accepted .feeDebit) :
    Not (Admission manifest config limits page protection command accepted) := by
  intro admitted
  exact mismatch admitted.operationFeeExact

theorem stale_epoch_has_no_admission
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {capacity : Nat}
    {manifest : AuthorizedResourceCharge.DeploymentManifest}
    {config : Config} {limits : Limits} {page : Page capacity}
    {protection : Protection} {command : Command capacity}
    {accepted : Accepted pre (command.resourceOperation config)}
    (admitted : Admission manifest config limits page protection command accepted) :
    Not (Admission manifest config limits (command.apply page)
      protection command accepted) := by
  intro stale
  have old := admitted.currentEpoch
  have new := stale.currentEpoch
  rw [Command.apply_epoch] at new
  omega

theorem activeLease_not_expired
    {book : Book} {object : Object} {height : Nat}
    (active : ActiveLease book object height) :
    Not (ExpiredLease book object height) := by
  rintro ⟨expiredRecord, ⟨expiredLookup, _⟩, expiredAt⟩
  rcases active with ⟨activeRecord, ⟨activeLookup, _⟩, activeAt⟩
  have sameRecord : activeRecord = expiredRecord := by
    exact Option.some.inj (activeLookup.symm.trans expiredLookup)
  rw [← sameRecord] at expiredAt
  exact (Nat.not_lt_of_ge activeAt) expiredAt

theorem active_lease_cannot_tombstone
    {capacity : Nat} {page : Page capacity} {protection : Protection}
    {book : Book} {expectedEpoch height : Nat} {slot : Fin capacity}
    {before : Object}
    (active : ActiveLease book before height) :
    Not (Allowed page protection book
      (.tombstone expectedEpoch height slot before)) := by
  intro allowed
  cases allowed with
  | tombstone _ _ expired _ => exact activeLease_not_expired active expired

theorem active_lease_cannot_compact
    {capacity : Nat} {page : Page capacity} {protection : Protection}
    {book : Book} {expectedEpoch height : Nat} {slot : Fin capacity}
    {before : Object}
    (active : ActiveLease book before height) :
    Not (Allowed page protection book
      (.compact expectedEpoch height slot before)) := by
  intro allowed
  cases allowed with
  | compact _ _ expired _ => exact activeLease_not_expired active expired

theorem renewal_installs_exact_successor_lease
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {pre : Materialized M} {capacity : Nat}
    {expectedEpoch height : Nat} {slot : Fin capacity} {before : Object}
    {newLeaseId rate epochs : Nat} {config : Config}
    (accepted : Accepted pre
      (Command.resourceOperation config
        (Command.renew expectedEpoch height slot before newLeaseId rate epochs))) :
    (logicalBook accepted.post.logical).leases newLeaseId = some
      { holder := before.owner
        lessor := config.lessor
        asset := config.asset
        prepaid := rate * epochs
        startsAt := height
        expiresAt := height + epochs } := by
  rw [Accepted.post_logicalBook]
  exact lease_installs_exact_record _ _ _ _ _ _ _ _

/-! ## Durable settlement under exact scoped authority -/

structure Runtime where
  transactionId : TransactionId
  nullifierId : Digest
  pageCell : CellId
  resourceCell : CellId
  authorityCell : CellId
  protectionCell : CellId
  clockCell : CellId
  authorityRoot : Digest
  protectionRoot : Digest
  clockRoot : Digest
  pageResourceDistinct : pageCell ≠ resourceCell
  authorityPageDistinct : authorityCell ≠ pageCell
  authorityResourceDistinct : authorityCell ≠ resourceCell
  protectionPageDistinct : protectionCell ≠ pageCell
  protectionResourceDistinct : protectionCell ≠ resourceCell
  clockPageDistinct : clockCell ≠ pageCell
  clockResourceDistinct : clockCell ≠ resourceCell

structure Plan
    (M : Materializer CanonicalResourceKernel.schema Digest)
    (portal : Portal) (authState : AuthState) (pre : Materialized M)
    (capacity : Nat) where
  config : Config
  limits : Limits
  page : Page capacity
  protection : Protection
  command : Command capacity
  manifest : AuthorizedResourceCharge.DeploymentManifest
  context : AuthorizedResourceCharge.RequestContext
  accepted : Accepted pre (command.resourceOperation config)
  authorization : Authorized portal authState (context.request manifest accepted)
  admission : Admission manifest config limits page protection command accepted
  runtime : Runtime
  grant : Grant
  scopeEvidence : ScopedAuthority M.rootBytes grant limits page command context
    (AuthorizedResourceCharge.exactCharge manifest accepted .feeDebit)
  grantPage : grant.pageCell = runtime.pageCell
  grantRootBound : M.rootBytes grant.canonicalBytes = runtime.authorityRoot
  protectionRootBound :
    M.rootBytes protection.canonicalBytes = runtime.protectionRoot
  clockRootBound : M.rootBytes (encodeNat command.height) = runtime.clockRoot

namespace Plan

variable
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {capacity : Nat}

def exactCharge (plan : Plan M portal authState pre capacity) : Charge :=
  totalCharge plan.manifest plan.accepted plan.page plan.protection plan.command

def nullifier (plan : Plan M portal authState pre capacity) : StableNullifier where
  codecVersion := plan.manifest.version
  domain := plan.grant.domain
  nullifierId := plan.runtime.nullifierId
  canonicalBytes := 213 :: encodeNat plan.command.expectedEpoch ++
    encodeNat plan.context.nonce ++ plan.command.canonicalBytes

def event (plan : Plan M portal authState pre capacity) : StableEvent where
  codecVersion := plan.manifest.version
  domain := plan.grant.domain
  eventId := commandDigest M.rootBytes plan.page plan.command
  canonicalBytes := 214 :: plan.page.canonicalBytes ++
    (plan.command.apply plan.page).canonicalBytes ++ plan.command.canonicalBytes

def intent (plan : Plan M portal authState pre capacity) : DataIntent M.rootBytes where
  transactionId := plan.runtime.transactionId
  writes :=
    [{ cellId := plan.runtime.pageCell
       expectedPre := M.rootBytes plan.page.canonicalBytes
       exactPost := M.rootBytes (plan.command.apply plan.page).canonicalBytes
       canonicalPostBytes := (plan.command.apply plan.page).canonicalBytes },
     { cellId := plan.runtime.resourceCell
       expectedPre := pre.root
       exactPost := plan.accepted.post.root
       canonicalPostBytes := plan.accepted.post.bytes }]
  readGuards :=
    [{ cellId := plan.runtime.authorityCell, expectedRoot := plan.runtime.authorityRoot },
     { cellId := plan.runtime.protectionCell, expectedRoot := plan.runtime.protectionRoot },
     { cellId := plan.runtime.clockCell, expectedRoot := plan.runtime.clockRoot }]
  nullifiers := [plan.nullifier]
  exactCharge := plan.exactCharge
  event := plan.event
  postRootsBound := by
    intro write member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl <;> rfl
  guardsReadOnly := by
    intro guard member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [plan.runtime.authorityPageDistinct,
        plan.runtime.authorityResourceDistinct]
    · simp [plan.runtime.protectionPageDistinct,
        plan.runtime.protectionResourceDistinct]
    · simp [plan.runtime.clockPageDistinct,
        plan.runtime.clockResourceDistinct]

@[simp] theorem intent_exactCharge (plan : Plan M portal authState pre capacity) :
    plan.intent.exactCharge = plan.exactCharge := rfl

@[simp] theorem intent_fee_exact (plan : Plan M portal authState pre capacity) :
    plan.intent.exactCharge .feeDebit =
      (plan.command.resourceOperation plan.config).feeDebit := by
  change AuthorizedResourceCharge.exactCharge plan.manifest plan.accepted
      .feeDebit + 0 = (plan.command.resourceOperation plan.config).feeDebit
  rw [Nat.add_zero]
  exact plan.admission.operationFeeExact.symm

@[simp] theorem exact_retry_replays (plan : Plan M portal authState pre capacity)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule (DataSnapshot.install before plan.intent)
      plan.intent = .replayed plan.intent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install, Snapshot.install,
    Snapshot.lookupRecorded, Intent.sameCheck_self]

theorem stale_authority_rejected
    (plan : Plan M portal authState pre capacity)
    (snapshot : DataSnapshot M.rootBytes)
    (stale : snapshot.model.roots plan.runtime.authorityCell ≠
      plan.runtime.authorityRoot) :
    plan.intent.preflight snapshot = .error .staleReadGuard := by
  apply DurableDataIntent.stale_read_guard_rejected
  let guard : ReadGuard :=
    { cellId := plan.runtime.authorityCell
      expectedRoot := plan.runtime.authorityRoot }
  exact ⟨guard, by simp [guard, intent], by simpa [guard] using stale⟩

theorem stale_protection_index_rejected
    (plan : Plan M portal authState pre capacity)
    (snapshot : DataSnapshot M.rootBytes)
    (stale : snapshot.model.roots plan.runtime.protectionCell ≠
      plan.runtime.protectionRoot) :
    plan.intent.preflight snapshot = .error .staleReadGuard := by
  apply DurableDataIntent.stale_read_guard_rejected
  let guard : ReadGuard :=
    { cellId := plan.runtime.protectionCell
      expectedRoot := plan.runtime.protectionRoot }
  exact ⟨guard, by simp [guard, intent], by simpa [guard] using stale⟩

end Plan

/-! ## Explicit trust and liveness ceilings -/

/-- A native collector refines the logical kernel only if its crawl is exactly
the authoritative protection graph, its clock reading is the guarded height,
its atomic write/refund behavior refines `DurableDataIntent`, and physical
reclamation occurs only after an accepted compact command. -/
structure ImplementationRefinement
    (NativeRequest NativeStore NativeResult : Type)
    (run : NativeStore -> NativeRequest -> NativeResult)
    (logicalProtection : NativeRequest -> Protection)
    (logicalHeight : NativeRequest -> Nat)
    (physicallyReclaimed : NativeResult -> ContentId -> Prop)
    (CrawlerComplete GuardedClockRefined AtomicSettlementRefined
      PhysicalReclamationSound : Prop) : Prop where
  crawlerComplete : CrawlerComplete
  guardedClockRefined : GuardedClockRefined
  atomicSettlementRefined : AtomicSettlementRefined
  physicalReclamationSound : PhysicalReclamationSound

/-- Eventual expiry detection, eventual compaction, storage availability, and
provider honesty are temporal/environment properties, not consequences of a
single accepted logical transition. -/
structure LivenessBoundary
    (WallClockProgress CrawlerEventuallyRuns
      AcceptedCompactionEventuallyReclaims StorageRemainsAvailable : Prop) : Prop where
  wallClockProgress : WallClockProgress
  crawlerEventuallyRuns : CrawlerEventuallyRuns
  acceptedCompactionEventuallyReclaims : AcceptedCompactionEventuallyReclaims
  storageRemainsAvailable : StorageRemainsAvailable

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.QuotaGcSettlement.finalized_content_cannot_compact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalized_content_cannot_compact
/-- info: 'Minidregg.Kernel.QuotaGcSettlement.live_reachable_content_cannot_compact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms live_reachable_content_cannot_compact
/-- info: 'Minidregg.Kernel.QuotaGcSettlement.Plan.exact_retry_replays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Plan.exact_retry_replays

end Minidregg.Kernel.QuotaGcSettlement
