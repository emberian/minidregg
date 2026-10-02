/-
# Explicit neutral paid-cell v4 → v5 payload carry

This is a codec migration, not a payment or an authority transition. Every old
row survives field-for-field. Claim, claim consumption, pending-owner custody
history, authenticated chain-tip, compute-usage and compute-activation namespaces
start empty. An empty usage map is not activation or a claim about historical work. The durable caller must
check the old anchor and atomically replace payload/root/registry commitments;
this leaf never interprets old bytes through the new decoder.
-/
import Kernel.PayCellLegacyV4
import Kernel.PayCell

namespace Minidregg.Kernel.PayCellUpgrade

open Minidregg.Compiler
open Minidregg.Compiler.StoreCodec
open Minidregg.Theory.Store

set_option autoImplicit false

abbrev OldStore := PayCellLegacyV4.PayStore
abbrev NewStore := PayCell.PayStore
abbrev OldAddress := Address PayCellLegacyV4.layout
abbrev NewAddress := Address PayCell.layout
abbrev OldEntry := Entry PayCellLegacyV4.layout
abbrev NewEntry := Entry PayCell.layout

def liftEnrolRecord (row : PayCellLegacyV4.EnrolRecord) : PayCell.EnrolRecord :=
  ⟨row.sshBlob, row.account, row.index, row.leaseUntil, row.enrolledSlot⟩

def liftUnattributed (row : PayCellLegacyV4.Unattributed) : PayCell.Unattributed :=
  ⟨row.index, row.amount, row.slot, row.reason, row.memo⟩

def addressMap : OldAddress → NewAddress
  | ⟨.tariff, key⟩ => ⟨.tariff, key⟩
  | ⟨.book, key⟩ => ⟨.book, key⟩
  | ⟨.assignment, key⟩ => ⟨.assignment, key⟩
  | ⟨.enrolment, key⟩ => ⟨.enrolment, key⟩
  | ⟨.sshIndex, key⟩ => ⟨.sshIndex, key⟩
  | ⟨.journal, key⟩ => ⟨.journal, key⟩

def valueMap : (address : OldAddress) →
    PayCellLegacyV4.layout.Value address.1 → PayCell.layout.Value (addressMap address).1
  | ⟨.tariff, _⟩, value => value
  | ⟨.book, _⟩, value => value
  | ⟨.assignment, _⟩, value => value
  | ⟨.enrolment, _⟩, value => liftEnrolRecord value
  | ⟨.sshIndex, _⟩, value => value
  | ⟨.journal, _⟩, value => liftUnattributed value

def liftEntry (entry : OldEntry) : NewEntry :=
  ⟨addressMap entry.1, valueMap entry.1 entry.2⟩

/-- Uses the existing executable canonical enumeration, never Finset.toList. -/
def lift (store : OldStore) : NewStore :=
  fromEntries ((entries PayCellLegacyV4.wire store).map liftEntry)

theorem addressMap_injective : Function.Injective addressMap := by
  intro left right same
  rcases left with ⟨ls, lk⟩
  rcases right with ⟨rs, rk⟩
  cases ls <;> cases rs <;> simp_all [addressMap]

private theorem old_entries_distinct (store : OldStore) :
    ((entries PayCellLegacyV4.wire store).map Sigma.fst).Nodup := by
  rw [entries_keys]
  exact Finset.sort_nodup _ _

private theorem mapped_entries_distinct (store : OldStore) :
    (((entries PayCellLegacyV4.wire store).map liftEntry).map Sigma.fst).Nodup := by
  have keys : (((entries PayCellLegacyV4.wire store).map liftEntry).map Sigma.fst) =
      ((entries PayCellLegacyV4.wire store).map Sigma.fst).map addressMap := by
    simp [List.map_map, Function.comp_def, liftEntry]
  rw [keys]
  exact (old_entries_distinct store).map addressMap_injective

private theorem entry_mem_of_read (store : OldStore) (address : OldAddress)
    (value : PayCellLegacyV4.layout.Value address.1) (found : store address = some value) :
    (⟨address, value⟩ : OldEntry) ∈ entries PayCellLegacyV4.wire store := by
  unfold entries
  apply List.mem_filterMap.mpr
  refine ⟨address, (mem_sortedSupport PayCellLegacyV4.wire store address).mpr ?_, ?_⟩
  · simp [found]
  · simp [found]

/-- Every old typed read is preserved, including absence. The two renamed
record carriers are mapped by their exact fields, with no defaulting. -/
theorem lift_apply (store : OldStore) (address : OldAddress) :
    lift store (addressMap address) = (store address).map (valueMap address) := by
  cases found : store address with
  | none =>
      simp only [Option.map_none]
      apply (fromEntries_apply_eq_none_iff _ _).mpr
      intro member
      simp only [List.map_map, Function.comp_def] at member
      obtain ⟨entry, member, same⟩ := List.mem_map.mp member
      change addressMap entry.1 = addressMap address at same
      have oldMember : address ∈ (entries PayCellLegacyV4.wire store).map Sigma.fst :=
        List.mem_map.mpr ⟨entry, member, addressMap_injective same⟩
      have absent : address ∉ (entries PayCellLegacyV4.wire store).map Sigma.fst := by
        apply (fromEntries_apply_eq_none_iff _ _).mp
        rw [fromEntries_entries]
        exact found
      exact absent oldMember
  | some value =>
      change fromEntries ((entries PayCellLegacyV4.wire store).map liftEntry)
        (liftEntry (⟨address, value⟩ : OldEntry)).1 =
          some (liftEntry (⟨address, value⟩ : OldEntry)).2
      apply fromEntries_apply_of_mem _ (mapped_entries_distinct store)
      exact List.mem_map_of_mem (entry_mem_of_read store address value found)

@[simp] theorem tariff_preserved (store : OldStore) :
    PayCell.tariffOf (lift store) = PayCellLegacyV4.tariffOf store := by
  have identity : valueMap (PayCellLegacyV4.tariffAddress) = _root_.id := by
    funext value
    rfl
  change lift store (addressMap (PayCellLegacyV4.tariffAddress)) = store (PayCellLegacyV4.tariffAddress)
  rw [lift_apply, identity]
  cases store (PayCellLegacyV4.tariffAddress) <;> rfl

@[simp] theorem book_preserved (store : OldStore) (index : Nat) :
    PayCell.bookAt (lift store) index = PayCellLegacyV4.bookAt store index := by
  have identity : valueMap (PayCellLegacyV4.bookAddress index) = _root_.id := by
    funext value
    rfl
  change lift store (addressMap (PayCellLegacyV4.bookAddress index)) = store (PayCellLegacyV4.bookAddress index)
  rw [lift_apply, identity]
  cases store (PayCellLegacyV4.bookAddress index) <;> rfl

@[simp] theorem assignment_preserved (store : OldStore) (index : Nat) :
    PayCell.assignmentAt (lift store) index = PayCellLegacyV4.assignmentAt store index := by
  have identity : valueMap (PayCellLegacyV4.assignmentAddress index) = _root_.id := by
    funext value
    rfl
  change lift store (addressMap (PayCellLegacyV4.assignmentAddress index)) = store (PayCellLegacyV4.assignmentAddress index)
  rw [lift_apply, identity]
  cases store (PayCellLegacyV4.assignmentAddress index) <;> rfl

@[simp] theorem enrolment_preserved (store : OldStore) (key : List UInt8) :
    PayCell.enrolmentAt (lift store) key =
      (PayCellLegacyV4.enrolmentAt store key).map liftEnrolRecord := by
  simpa [PayCell.enrolmentAt, PayCellLegacyV4.enrolmentAt,
    PayCell.enrolmentAddress, PayCellLegacyV4.enrolmentAddress, addressMap, valueMap]
    using lift_apply store (PayCellLegacyV4.enrolmentAddress key)

@[simp] theorem sshIndex_preserved (store : OldStore) (blob : List UInt8) :
    PayCell.sshIndexAt (lift store) blob = PayCellLegacyV4.sshIndexAt store blob := by
  have identity : valueMap (PayCellLegacyV4.sshIndexAddress blob) = _root_.id := by
    funext value
    rfl
  change lift store (addressMap (PayCellLegacyV4.sshIndexAddress blob)) = store (PayCellLegacyV4.sshIndexAddress blob)
  rw [lift_apply, identity]
  cases store (PayCellLegacyV4.sshIndexAddress blob) <;> rfl

@[simp] theorem journal_preserved (store : OldStore) (nullifier : List UInt8) :
    PayCell.journalAt (lift store) nullifier =
      (PayCellLegacyV4.journalAt store nullifier).map liftUnattributed := by
  simpa [PayCell.journalAt, PayCellLegacyV4.journalAt,
    PayCell.journalAddress, PayCellLegacyV4.journalAddress, addressMap, valueMap]
    using lift_apply store (PayCellLegacyV4.journalAddress nullifier)

private theorem new_address_absent (store : OldStore) (address : NewAddress)
    (fresh : ∀ old, addressMap old ≠ address) : lift store address = none := by
  apply (fromEntries_apply_eq_none_iff _ _).mpr
  intro member
  simp only [List.map_map, Function.comp_def] at member
  obtain ⟨entry, _, same⟩ := List.mem_map.mp member
  exact fresh entry.1 same

@[simp] theorem claim_absent (store : OldStore) (id : List UInt8) :
    PayCell.claimAt (lift store) id = none := by
  apply new_address_absent
  rintro ⟨space, key⟩
  cases space <;> simp [addressMap, PayCell.claimAddress]

@[simp] theorem consumption_absent (store : OldStore) (id : List UInt8) :
    PayCell.claimConsumptionAt (lift store) id = none := by
  apply new_address_absent
  rintro ⟨space, key⟩
  cases space <;> simp [addressMap, PayCell.claimConsumptionAddress]

@[simp] theorem pendingOwner_absent (store : OldStore) (identity : List UInt8) :
    PayCell.pendingOwnerAt (lift store) identity = none := by
  apply new_address_absent
  rintro ⟨space, key⟩
  cases space <;> simp [addressMap, PayCell.pendingOwnerAddress]

@[simp] theorem pendingOwnerHistory_absent (store : OldStore) (identity : List UInt8) (epoch : Nat) :
    PayCell.pendingOwnerHistoryAt (lift store) identity epoch = none := by
  apply new_address_absent
  rintro ⟨space, key⟩
  cases space <;> simp [addressMap, PayCell.pendingOwnerHistoryAddress]

@[simp] theorem chainTip_absent (store : OldStore) :
    PayCell.chainTipOf (lift store) = none := by
  apply new_address_absent
  rintro ⟨space, key⟩
  cases space <;> simp [addressMap, PayCell.chainTipAddress]

@[simp] theorem computeUsage_absent (store : OldStore) (subject : Nat) :
    PayCell.computeUsageAt (lift store) subject = none := by
  apply new_address_absent
  rintro ⟨space, key⟩
  cases space <;> simp [addressMap, PayCell.computeUsageAddress]

@[simp] theorem computeActivation_absent (store : OldStore) :
    PayCell.computeActivationOf (lift store) = none := by
  apply new_address_absent
  rintro ⟨space, key⟩
  cases space <;> simp [addressMap, PayCell.computeActivationAddress]

/-- The law's row predicate is unchanged on every old address, not merely on
its support; mutual enrollment/SSH-index relationships are preserved together. -/
theorem old_row_preserved (store : OldStore) (address : OldAddress) :
    PayCell.rowShaped (lift store) (addressMap address) =
      PayCellLegacyV4.rowShaped store address := by
  rcases address with ⟨space, key⟩
  cases space with
  | tariff => rfl
  | assignment => rfl
  | journal => rfl
  | book =>
      simp [addressMap, PayCell.rowShaped, PayCellLegacyV4.rowShaped] <;> rfl
  | enrolment =>
      simp only [addressMap, PayCell.rowShaped, PayCellLegacyV4.rowShaped, enrolment_preserved]
      cases found : PayCellLegacyV4.enrolmentAt store key <;>
        simp [liftEnrolRecord, sshIndex_preserved] <;> rfl
  | sshIndex =>
      simp only [addressMap, PayCell.rowShaped, PayCellLegacyV4.rowShaped, sshIndex_preserved]
      cases found : PayCellLegacyV4.sshIndexAt store key with
      | none => rfl
      | some identity =>
          dsimp only
          rw [enrolment_preserved]
          cases PayCellLegacyV4.enrolmentAt store identity <;> rfl

private theorem legacy_row_everywhere (store : OldStore) (law : PayCellLegacyV4.Law store)
    (address : OldAddress) : PayCellLegacyV4.rowShaped store address = true := by
  by_cases member : address ∈ store.support
  · exact law.2 address member
  · have absent : store address = none := by
      simpa only [DFinsupp.mem_support_toFun, not_not] using member
    rcases address with ⟨space, key⟩
    cases space <;>
      simp [PayCellLegacyV4.rowShaped, PayCellLegacyV4.bookAt,
        PayCellLegacyV4.bookAddress, PayCellLegacyV4.enrolmentAt,
        PayCellLegacyV4.enrolmentAddress, PayCellLegacyV4.sshIndexAt,
        PayCellLegacyV4.sshIndexAddress, absent]

/-- No new law premise is assumed: the empty new namespaces satisfy their row
conditions, while all old cross-row relationships remain exactly unchanged. -/
theorem lift_law (store : OldStore) (law : PayCellLegacyV4.Law store) :
    PayCell.Law (lift store) := by
  refine ⟨?_, ?_⟩
  · simpa using law.1
  · rintro ⟨space, key⟩ _
    cases space with
    | tariff => rfl
    | assignment => rfl
    | journal => rfl
    | book =>
        exact (old_row_preserved store ⟨.book, key⟩).trans
          (legacy_row_everywhere store law ⟨.book, key⟩)
    | enrolment =>
        exact (old_row_preserved store ⟨.enrolment, key⟩).trans
          (legacy_row_everywhere store law ⟨.enrolment, key⟩)
    | sshIndex =>
        exact (old_row_preserved store ⟨.sshIndex, key⟩).trans
          (legacy_row_everywhere store law ⟨.sshIndex, key⟩)
    | claim => simp [PayCell.rowShaped]
    | claimConsumption => simp [PayCell.rowShaped]
    | pendingOwner => simp [PayCell.rowShaped]
    | pendingOwnerHistory => rcases key with ⟨identity, epoch⟩; simp [PayCell.rowShaped]
    | chainTip => cases key; simp [PayCell.rowShaped]
    | computeUsage => simp [PayCell.rowShaped]
    | computeActivation => cases key; simp [PayCell.rowShaped]

/-- The actual executable codec lift. Invalid or noncanonical v4 input refuses;
canonical v5 bytes are produced only from the frozen v4 decoder's result. The
caller retains the exact old bytes/root as its durable compare-and-swap guard. -/
def upgradeBytes (bytes : List UInt8) : Option (List UInt8) :=
  (StoreCodec.decode PayCellLegacyV4.wire bytes).map fun store =>
    StoreCodec.encode PayCell.wire (lift store)

theorem upgradeBytes_encode (store : OldStore) :
    upgradeBytes (StoreCodec.encode PayCellLegacyV4.wire store) =
      some (StoreCodec.encode PayCell.wire (lift store)) := by
  simp [upgradeBytes, StoreCodec.decode_encode]

theorem upgraded_payload_decodes (store : OldStore) :
    StoreCodec.decode PayCell.wire (StoreCodec.encode PayCell.wire (lift store)) =
      some (lift store) := StoreCodec.decode_encode _ _

/-- Successful migration always has one exact old canonical payload and one
exact new canonical payload; there is no fallback permissive decode path. -/
theorem upgradeBytes_exact {oldBytes newBytes : List UInt8}
    (upgraded : upgradeBytes oldBytes = some newBytes) :
    ∃ store : OldStore,
      StoreCodec.decode PayCellLegacyV4.wire oldBytes = some store ∧
      StoreCodec.encode PayCellLegacyV4.wire store = oldBytes ∧
      StoreCodec.encode PayCell.wire (lift store) = newBytes ∧
      StoreCodec.decode PayCell.wire newBytes = some (lift store) := by
  unfold upgradeBytes at upgraded
  cases decoded : StoreCodec.decode PayCellLegacyV4.wire oldBytes with
  | none => simp [decoded] at upgraded
  | some store =>
      simp only [decoded, Option.map_some, Option.some.injEq] at upgraded
      refine ⟨store, rfl, StoreCodec.decode_reencodes _ decoded, upgraded, ?_⟩
      rw [← upgraded]
      exact upgraded_payload_decodes store

/-- The physical pay-cell identity is not changed by its payload version. -/
theorem physicalId_preserved (domain : Minidregg.Theory.TypedAuthorization.Digest) :
    PayCell.physicalId domain = PayCellLegacyV4.physicalId domain := rfl

/-! ## Satisfiable carry poles, without evaluating the canonical merge sort -/

theorem carried_genesis_law : PayCell.Law (lift PayCellLegacyV4.genesisStore) :=
  lift_law _ PayCellLegacyV4.genesis_law

theorem carried_enrollment_law : PayCell.Law (lift PayCellLegacyV4.enrolledFixture) :=
  lift_law _ PayCellLegacyV4.enrolled_fixture_law

/-- Existing paid membership survives without resetting its account or lease. -/
theorem carried_enrollment_exact :
    PayCell.enrolmentAt (lift PayCellLegacyV4.enrolledFixture)
      PayEnrolMemo.fixtureMemo.miniKey =
        some ⟨PayEnrolMemo.fixtureMemo.sshBlob, 108, some 1, 500168, 900⟩ := by
  rw [enrolment_preserved]
  have old : PayCellLegacyV4.enrolmentAt PayCellLegacyV4.enrolledFixture
      PayEnrolMemo.fixtureMemo.miniKey =
        some ⟨PayEnrolMemo.fixtureMemo.sshBlob, 108, some 1, 500168, 900⟩ := by decide
  rw [old]
  rfl

#assert_axioms carried_genesis_law
#assert_axioms carried_enrollment_law
#assert_axioms carried_enrollment_exact
#assert_axioms lift_apply
#assert_axioms tariff_preserved
#assert_axioms book_preserved
#assert_axioms assignment_preserved
#assert_axioms enrolment_preserved
#assert_axioms sshIndex_preserved
#assert_axioms journal_preserved
#assert_axioms claim_absent
#assert_axioms consumption_absent
#assert_axioms pendingOwner_absent
#assert_axioms pendingOwnerHistory_absent
#assert_axioms chainTip_absent
#assert_axioms computeUsage_absent
#assert_axioms computeActivation_absent
#assert_axioms old_row_preserved
#assert_axioms lift_law
#assert_axioms upgradeBytes_encode
#assert_axioms upgraded_payload_decodes
#assert_axioms upgradeBytes_exact
#assert_axioms physicalId_preserved

end Minidregg.Kernel.PayCellUpgrade
