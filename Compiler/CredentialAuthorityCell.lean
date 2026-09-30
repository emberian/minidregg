/-
# Compiler.CredentialAuthorityCell -- the authority domain as one store cell

The authority domain is one cell: a `Store` over
`CredentialAuthorityState.layout`, one typed namespace ("plane") per kind of
authority record.  Its wire representation is the generic `StoreCodec` at the
declared `wire` below, and its materializer is `StoreCodec.materializer wire`;
round trip, canonicity and injectivity are the general theorems of
`Compiler.StoreCodec`.

The `revoked`, `nullifier` and `registered` planes are presence-only
(`Unit` values) and append-only.  A present revocation cannot be removed or
overwritten by any accepted patch (`CredentialAuthorityState.revocation_permanent`);
at this cell, a patch that tries is rejected at its first operation
(`unrevoke_rejected_at_cell`), and revoking a fresh key is accepted
(`revoke_accepted_at_cell`).

This replaces two representations of the same store:
`Compiler.CredentialAuthorityStateCodec` (frame `LOOM/AUTH/STATE`, a
`FiniteDependentMapCodec` over the deleted `AuthorityField`, with an explicit
`false` distinct from absence in the revocation plane) and
`Compiler.CredentialAuthorityPageMaterializer` (frame `LOOM/AUTH/PAGE`, a
four-slot shard whose entries projected into that store).  Both are deleted,
so cells written with either frame refuse to decode here
(`retired_state_frame_refused`, `retired_page_frame_refused`).
-/
import Compiler.StoreCodec
import Compiler.CredentialAuthorityEntryCodec

namespace Minidregg.Compiler.CredentialAuthorityCell

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.TypedAuthorizationRequestCodec
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.StoreCodec
open Minidregg.Theory
open Minidregg.Theory.CellState (Materializer Materialized materialize)
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## The declared wire of the authority layout -/

def revocationKeyStream : StreamCodec RevocationKey where
  encode
    | .capability capability => 0 :: capabilityIdStream.encode capability
    | .channel channel => 1 :: channelIdStream.encode channel
    | .signingKey subject epoch =>
        2 :: (StreamCodec.product subjectIdStream StreamCodec.nat).encode (subject, epoch)
  decodePrefix
    | 0 :: bytes => do
        let (capability, suffix) <- capabilityIdStream.decodePrefix bytes
        some (.capability capability, suffix)
    | 1 :: bytes => do
        let (channel, suffix) <- channelIdStream.decodePrefix bytes
        some (.channel channel, suffix)
    | 2 :: bytes => do
        let ((subject, epoch), suffix) <-
          (StreamCodec.product subjectIdStream StreamCodec.nat).decodePrefix bytes
        some (.signingKey subject epoch, suffix)
    | _ => none
  decodePrefix_encode := by
    intro key suffix
    cases key with
    | capability capability => simp [capabilityIdStream.decodePrefix_encode]
    | channel channel => simp [channelIdStream.decodePrefix_encode]
    | signingKey subject epoch =>
        simp [(StreamCodec.product subjectIdStream StreamCodec.nat).decodePrefix_encode]

/-- One tag byte per plane. -/
def planeTag : AuthorityPlane → UInt8
  | .capability .object => 0
  | .capability .account => 1
  | .capability .program => 2
  | .issuerEpoch => 3
  | .policyEpoch => 4
  | .policyAddress => 5
  | .subjectKeyEpoch => 6
  | .revoked => 7
  | .nullifier => 9
  | .subjectKey => 10
  | .policyRevision => 11
  | .registered => 12

def planeOfTag : UInt8 → Option AuthorityPlane
  | 0 => some (.capability .object)
  | 1 => some (.capability .account)
  | 2 => some (.capability .program)
  | 3 => some .issuerEpoch
  | 4 => some .policyEpoch
  | 5 => some .policyAddress
  | 6 => some .subjectKeyEpoch
  | 7 => some .revoked
  | 9 => some .nullifier
  | 10 => some .subjectKey
  | 11 => some .policyRevision
  | 12 => some .registered
  | _ => none

theorem planeOfTag_tag (plane : AuthorityPlane) : planeOfTag (planeTag plane) = some plane := by
  cases plane with
  | capability kind => cases kind <;> rfl
  | _ => rfl

def planeStream : StreamCodec AuthorityPlane where
  encode plane := [planeTag plane]
  decodePrefix
    | tag :: suffix => (planeOfTag tag).map fun plane => (plane, suffix)
    | [] => none
  decodePrefix_encode := by
    intro plane suffix
    simp [planeOfTag_tag]

def keyStream : (plane : AuthorityPlane) → StreamCodec plane.Key
  | .capability _ => capabilityIdStream
  | .issuerEpoch => issuerIdStream
  | .policyEpoch => policyIdStream
  | .policyRevision => policyIdStream
  | .policyAddress => StreamCodec.product policyIdStream StreamCodec.nat
  | .subjectKeyEpoch => subjectIdStream
  | .subjectKey => StreamCodec.product subjectIdStream StreamCodec.nat
  | .revoked => revocationKeyStream
  | .nullifier => StreamCodec.nat
  | .registered => revocationKeyStream

def valueStream : (plane : AuthorityPlane) → StreamCodec plane.Value
  | .capability kind => storedCapabilityStream kind
  | .issuerEpoch => StreamCodec.nat
  | .policyEpoch => StreamCodec.nat
  | .policyRevision => StreamCodec.nat
  | .policyAddress => digestStream
  | .subjectKeyEpoch => StreamCodec.nat
  | .subjectKey => CredentialSigningKeyCodec.keyRecordStream
  | .revoked => unitStream
  | .nullifier => unitStream
  | .registered => unitStream

def keyCodecId : AuthorityPlane → String
  | .capability _ => "capability-id/nat"
  | .issuerEpoch => "issuer-id/nat"
  | .policyEpoch => "policy-id/nat"
  | .policyRevision => "policy-id/nat"
  | .policyAddress => "policy-id/nat x nat"
  | .subjectKeyEpoch => "subject-id/nat"
  | .subjectKey => "subject-id/nat x nat"
  | .revoked => "revocation-key/tagged-v2"
  | .nullifier => "nat/base255"
  | .registered => "revocation-key/tagged-v2"

def valueCodecId : AuthorityPlane → String
  | .capability _ => "stored-capability/v1"
  | .issuerEpoch => "nat/base255"
  | .policyEpoch => "nat/base255"
  | .policyRevision => "nat/base255"
  | .policyAddress => "digest/nat"
  | .subjectKeyEpoch => "nat/base255"
  | .subjectKey => "signing-key-record/v2"
  | .revoked => "unit/presence"
  | .nullifier => "unit/presence"
  | .registered => "unit/presence"

def planes : List AuthorityPlane :=
  [.capability .object, .capability .account, .capability .program,
    .issuerEpoch, .policyEpoch, .policyRevision, .policyAddress,
    .subjectKeyEpoch, .subjectKey, .revoked, .nullifier, .registered]

/-- The authority layout on the wire. -/
def wire : Wire layout where
  name := "minidregg/credential-authority/v2"
  namespaces := planes
  namespaces_complete := by
    intro plane
    cases plane with
    | capability kind => cases kind <;> simp [planes]
    | _ => simp [planes]
  namespaceStream := planeStream
  keyStream := keyStream
  valueStream := valueStream
  keyCodecId := keyCodecId
  valueCodecId := valueCodecId

/-- The authority cell materializer. -/
def materializer : CredentialAuthorityState.Materializer := StoreCodec.materializer wire

abbrev Cell := Materialized materializer

theorem cell_decode (cell : Cell) :
    materializer.codec.decode cell.bytes = some cell.logical :=
  decode_encode wire cell.logical

theorem decode_canonical {bytes : List UInt8} {store : Store layout}
    (accepted : materializer.codec.decode bytes = some store) :
    materializer.codec.encode store = bytes :=
  decode_reencodes wire accepted

/-! ## Append-only planes at this cell (both poles) -/

theorem unrevoke_rejected_at_cell (pre : Cell) (key : RevocationKey) :
    CellState.validate materializer pre pre.root [Op.free (L := layout) .revoked key ()] =
      .rejected (.disabledOperation 0) :=
  unrevoke_rejected materializer pre key

theorem revoke_accepted_at_cell (pre : Cell) (key : RevocationKey)
    (fresh : pre.logical ⟨.revoked, key⟩ = none) :
    ∃ validated : CellState.ValidatedPatch materializer pre pre.root
        [Op.allocate (L := layout) .revoked key ()],
      CellState.validate materializer pre pre.root
          [Op.allocate (L := layout) .revoked key ()] = .accepted validated ∧
        validated.apply.logical ⟨.revoked, key⟩ = some () :=
  revoke_accepted materializer pre key fresh

theorem deregister_rejected_at_cell (pre : Cell) (key : RevocationKey) :
    CellState.validate materializer pre pre.root [Op.free (L := layout) .registered key ()] =
      .rejected (.disabledOperation 0) :=
  deregister_rejected materializer pre key

theorem register_accepted_at_cell (pre : Cell) (key : RevocationKey)
    (fresh : pre.logical ⟨.registered, key⟩ = none) :
    ∃ validated : CellState.ValidatedPatch materializer pre pre.root
        [Op.allocate (L := layout) .registered key ()],
      CellState.validate materializer pre pre.root
          [Op.allocate (L := layout) .registered key ()] = .accepted validated ∧
        validated.apply.logical ⟨.registered, key⟩ = some () :=
  register_accepted materializer pre key fresh

/-! ## Pair-scoped root binding

The cell root is the cSHAKE256 digest of the canonical bytes.  No global
injectivity into 256 bits is claimed: a root equality between two specific
stores is turned into store equality only under the premise that this pair is
not a collision. -/

/-- A collision between two authority stores: different stores, hence different
canonical bytes (`encode_injective`), with the same root. -/
structure Collision (left right : Store layout) : Prop where
  statesDifferent : left ≠ right
  bytesDifferent : materializer.codec.encode left ≠ materializer.codec.encode right
  rootsEqual : materializer.rootOf left = materializer.rootOf right

theorem collision_of_root_eq_of_ne {left right : Store layout} (different : left ≠ right)
    (same : materializer.rootOf left = materializer.rootOf right) : Collision left right :=
  ⟨different, fun bytes => different (encode_injective wire bytes), same⟩

/-- The pair-scoped collision-resistance premise. -/
def PairBindingPremise (left right : Store layout) : Prop :=
  ¬ Collision left right

/-- Under the pair premise, equal roots mean equal stores. -/
theorem logical_eq_of_root_eq {left right : Cell}
    (binding : PairBindingPremise left.logical right.logical)
    (same : left.root = right.root) : left.logical = right.logical := by
  by_contra different
  exact binding (collision_of_root_eq_of_ne different same)

/-- Under the pair premise, two cells with different stores have different
roots: every accepted authority change moves the root a durable read guard
observes. -/
theorem root_ne_of_logical_ne {left right : Cell}
    (binding : PairBindingPremise left.logical right.logical)
    (different : left.logical ≠ right.logical) : left.root ≠ right.root :=
  fun same => different (logical_eq_of_root_eq binding same)

/-! ## A worked authority cell -/

namespace Witness

def examplePolicy : PolicyId := ⟨17⟩
def exampleRevocation : RevocationKey := .channel ⟨9⟩

/-- A policy at revision 3 with its address, and one revoked channel. -/
def store : Store layout :=
  fromEntries
    ([⟨⟨.policyRevision, examplePolicy⟩, (3 : Nat)⟩,
      ⟨⟨.policyAddress, (examplePolicy, 3)⟩, (⟨3300⟩ : Digest)⟩,
      ⟨⟨.revoked, exampleRevocation⟩, ()⟩] : List (Entry layout))

def cell : Cell := materialize materializer store

theorem cell_roundtrip : materializer.codec.decode cell.bytes = some cell.logical :=
  cell_decode cell

theorem cell_revoked : isRevoked cell exampleRevocation = true := by
  decide

theorem cell_policyRevision : policyRevisionAt cell examplePolicy = 3 := by
  decide

/-- The revocation cannot be undone at this cell. -/
theorem cell_unrevoke_rejected :
    CellState.validate materializer cell cell.root
        [Op.free (L := layout) .revoked exampleRevocation ()] =
      .rejected (.disabledOperation 0) :=
  unrevoke_rejected_at_cell cell exampleRevocation

/-- A policy revision, on the RAM plane, can advance under its guard. -/
theorem cell_policy_advance_valid :
    Patch.ValidFrom cell.logical
      [Op.write (L := layout) .policyRevision examplePolicy (3 : Nat) (4 : Nat)] := by
  decide

/-! ### Capability admission reads the one cell (both poles)

Restated from the deleted page probe: the same teeth, over the authority
cell's `authState` rather than a page projection.  The owner's capability
key is registered, and revoking it is what refuses the grant. -/

def ownerEntries : List (Entry layout) :=
  [⟨⟨.capability .object, demoCapability.id⟩,
      (⟨demoCapability, []⟩ : StoredCapability .object)⟩,
   ⟨⟨.policyEpoch, demoCapability.policyId⟩, demoCapability.policyEpoch⟩,
   ⟨⟨.issuerEpoch, demoCapability.issuer⟩, demoCapability.issuerEpoch⟩,
   ⟨⟨.subjectKeyEpoch, demoRequest.subject⟩, demoRequest.subjectKeyEpoch⟩,
   ⟨⟨.registered, .capability demoCapability.id⟩, ()⟩]

def ownerCell : Cell := materialize materializer (fromEntries ownerEntries)

theorem owner_capability_exact :
    readCapability ownerCell .object demoCapability.id = some ⟨demoCapability, []⟩ := by
  decide

theorem owner_policy_exact :
    policyEpochAt ownerCell demoCapability.policyId = demoCapability.policyEpoch := by
  decide

theorem owner_issuer_exact :
    issuerEpochAt ownerCell demoCapability.issuer = demoCapability.issuerEpoch := by
  decide

theorem owner_registered_not_revoked :
    isRegistered ownerCell (.capability demoCapability.id) = true ∧
      isRevoked ownerCell (.capability demoCapability.id) = false := by
  decide

theorem owner_revoked_empty : (authState ownerCell).revoked = ∅ := by
  decide

/-- Satisfiable pole: the committed owner capability is admissible. -/
theorem owner_admissible :
    demoCapability.Admissible (authState ownerCell) demoRequest := by
  refine
    { holder := demoCapability_admissible.holder
      scope := demoCapability_admissible.scope
      validFrom := demoCapability_admissible.validFrom
      validUntil := demoCapability_admissible.validUntil
      policyId := demoCapability_admissible.policyId
      policyEpoch := demoCapability_admissible.policyEpoch
      policyCurrent := owner_policy_exact.symm
      issuerCurrent := owner_issuer_exact.symm
      selfNotRevoked := ?_
      ancestorNotRevoked := ?_
      channelNotRevoked := ?_ }
  · rw [owner_revoked_empty]; simp
  · intro ancestor _; rw [owner_revoked_empty]; simp
  · intro channel _; rw [owner_revoked_empty]; simp

/-- Refuting pole: a different subject is refused by the same cell. -/
theorem other_subject_refused :
    ¬ demoCapability.Admissible (authState ownerCell)
      { demoRequest with subject := ⟨99⟩ } := by
  intro admitted
  have holder := admitted.holder
  simp [demoCapability, Holder.Covers] at holder

theorem other_target_refused :
    ¬ demoCapability.Admissible (authState ownerCell)
      (demoRequest.retarget demoOtherTarget) :=
  target_substitution_rejected demoCapability _ _ _ (by decide)

/-- The same cell after an issuer-epoch rotation. -/
def rotatedCell : Cell :=
  materialize materializer
    (fromEntries (⟨⟨.issuerEpoch, demoCapability.issuer⟩, (4 : Nat)⟩ :: ownerEntries))

theorem rotated_issuer_refused :
    ¬ demoCapability.Admissible (authState rotatedCell) demoRequest := by
  intro admitted
  have current : demoCapability.issuerEpoch = issuerEpochAt rotatedCell demoCapability.issuer :=
    admitted.issuerCurrent
  have rotated : issuerEpochAt rotatedCell demoCapability.issuer = 4 := by decide
  rw [rotated] at current
  exact absurd current (by decide)

/-- The same cell after the owner's capability key is revoked (one fresh
allocation in the append-only plane). -/
def revokedCell : Cell :=
  materialize materializer
    (fromEntries (⟨⟨.revoked, .capability demoCapability.id⟩, ()⟩ :: ownerEntries))

theorem revocation_refuses_owner :
    ¬ demoCapability.Admissible (authState revokedCell) demoRequest := by
  intro admitted
  exact admitted.selfNotRevoked (by decide)

/-- The revoked owner key is registered present AND revoked present. -/
theorem revoked_owner_registered_and_revoked :
    isRegistered revokedCell (.capability demoCapability.id) = true ∧
      isRevoked revokedCell (.capability demoCapability.id) = true := by
  decide

/-- Refuting pole: the owner's registration cannot be erased. -/
theorem cell_deregister_rejected :
    CellState.validate materializer ownerCell ownerCell.root
        [Op.free (L := layout) .registered (.capability demoCapability.id) ()] =
      .rejected (.disabledOperation 0) :=
  deregister_rejected_at_cell ownerCell _

/-- Satisfiable pole: a key the cell has not registered can be registered. -/
theorem cell_register_fresh_accepted :
    ∃ validated : CellState.ValidatedPatch materializer ownerCell ownerCell.root
        [Op.allocate (L := layout) .registered exampleRevocation ()],
      CellState.validate materializer ownerCell ownerCell.root
          [Op.allocate (L := layout) .registered exampleRevocation ()] =
        .accepted validated ∧
        validated.apply.logical ⟨.registered, exampleRevocation⟩ = some () :=
  register_accepted_at_cell ownerCell _ (by decide)

end Witness

/-! ## Retired frames refuse to load -/

/-- `LOOM/AUTH/STATE` version 3: the deleted whole-state codec's frame. -/
def retiredStateFrame : List UInt8 := "LOOM/AUTH/STATE".toUTF8.toList ++ [3]

/-- `LOOM/AUTH/POLICYPAGE`, wire version 4, capacity 4: the deleted four-slot
shard's frame. -/
def retiredPageFrame : List UInt8 :=
  [76, 79, 79, 77, 47, 65, 85, 84, 72, 47, 80, 79, 76, 73, 67, 89, 80, 65,
    71, 69, 4, 4]

theorem retired_state_frame_refused (payload : List UInt8) :
    materializer.codec.decode (retiredStateFrame ++ payload) = none := by
  have head : retiredStateFrame = 76 :: retiredStateFrame.drop 1 := by decide +kernel
  rw [head, List.cons_append]
  exact decode_other_first_byte wire 76 (retiredStateFrame.drop 1 ++ payload) (by decide)

theorem retired_page_frame_refused (payload : List UInt8) :
    materializer.codec.decode (retiredPageFrame ++ payload) = none := by
  exact decode_other_first_byte wire 76 (retiredPageFrame.drop 1 ++ payload) (by decide)

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.unrevoke_rejected_at_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unrevoke_rejected_at_cell
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.revoke_accepted_at_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoke_accepted_at_cell
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.Witness.cell_revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.cell_revoked
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.Witness.cell_unrevoke_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.cell_unrevoke_rejected
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.Witness.cell_policy_advance_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.cell_policy_advance_valid
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.Witness.owner_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.owner_admissible
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.Witness.revocation_refuses_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.revocation_refuses_owner
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.Witness.rotated_issuer_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.rotated_issuer_refused
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.deregister_rejected_at_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deregister_rejected_at_cell
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.register_accepted_at_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms register_accepted_at_cell
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.root_ne_of_logical_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms root_ne_of_logical_ne
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.Witness.revoked_owner_registered_and_revoked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.revoked_owner_registered_and_revoked
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.Witness.cell_deregister_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.cell_deregister_rejected
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.Witness.cell_register_fresh_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Witness.cell_register_fresh_accepted
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.retired_state_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retired_state_frame_refused
/-- info: 'Minidregg.Compiler.CredentialAuthorityCell.retired_page_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retired_page_frame_refused

end Minidregg.Compiler.CredentialAuthorityCell
