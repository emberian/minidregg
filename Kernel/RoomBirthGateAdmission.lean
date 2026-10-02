/-
# Kernel.RoomBirthGateAdmission — the room birth gate runs at the admission height

`ResourceBirthController.preparePreAuthority` decides the room birth gate
(`Kernel.RoomBirthGate`) at the height it is given and records it as
`gateHeight`. This module pins that the recorded height is exactly the given one
through every preparation, so a native admission at height `h` (which passes
`h` to `prepareBirth`) decided every room placement at `h`.
-/
import Kernel.ResourceBirthPolicyController

namespace Minidregg.Kernel.RoomBirthGateAdmission

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Kernel.ResourceBirthController.Concrete

set_option autoImplicit false

variable {F : Type} [Field F]

theorem preparePreAuthority_gateHeight {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : Deployment} {pins : FactoryPins} {durable : Durable}
    {disabled : List Digest} {descriptor : Descriptor Registry} {height : Height}
    {pre : PreparedPreAuthority profile deployment pins durable descriptor}
    (prepared : preparePreAuthority profile disabled deployment pins durable descriptor height = .ok pre) :
    pre.gateHeight = height := by
  unfold preparePreAuthority at prepared
  simp only [bind, Except.bind] at prepared
  repeat' split at prepared
  all_goals first
    | (cases prepared; rfl)
    | (simp_all)

theorem prepareBirth_gateHeight {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : Deployment} {pins : FactoryPins} {durable : Durable}
    {disabled : List Digest} {descriptor : Descriptor Registry} {height : Height}
    {birth : PreparedBirth profile deployment pins durable descriptor}
    (prepared : prepareBirth profile disabled deployment pins durable descriptor height = .ok birth) :
    birth.gateHeight = height := by
  unfold prepareBirth at prepared
  simp only [bind, Except.bind] at prepared
  split at prepared
  · cases prepared
  · rename_i pre gate
    have exact := preparePreAuthority_gateHeight gate
    repeat' split at prepared
    all_goals first
      | (cases prepared; exact exact)
      | (simp_all)

theorem prepareGrainBirth_gateHeight {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : Deployment} {pins : FactoryPins} {durable : Durable}
    {disabled : List Digest} {descriptor : Descriptor Registry} {operationMarker : Nat} {height : Height}
    {birth : PreparedGrainBirth profile deployment pins durable descriptor operationMarker}
    (prepared : prepareGrainBirth profile disabled deployment pins durable descriptor operationMarker height =
      .ok birth) :
    birth.pre.gateHeight = height := by
  unfold prepareGrainBirth at prepared
  simp only [bind, Except.bind] at prepared
  split at prepared
  · cases prepared
  · rename_i pre gate
    have exact := preparePreAuthority_gateHeight gate
    repeat' split at prepared
    all_goals first
      | (cases prepared; exact exact)
      | (simp_all)

/-- **`birth_under_room_requires_grant` at the admission height.** A birth
prepared at height `h` — `ResourceBirthPolicyController.admitDecodedNative`
prepares at its admission height and its `AcceptedBirth.prepared` is that very
value — bears an item into room `R` only under a placing capability admissible
at `h` for the creator's `placeObject` request on `R`, and `R`'s law accepts it. -/
theorem birth_under_room_requires_grant_at {profile : CanonicalPolicyAdmission.PolicyCompilerProfile F}
    {deployment : Deployment} {pins : FactoryPins} {durable : Durable}
    {disabled : List Digest} {descriptor : Descriptor Registry} {height : Height}
    {birth : PreparedBirth profile deployment pins durable descriptor}
    (prepared : prepareBirth profile disabled deployment pins durable descriptor height = .ok birth)
    {item : BirthItem Registry} (member : item ∈ descriptor.births)
    {room : Nat} (inRoom : item.parent = some room) :
    ∃ placement cap, item.placement = some placement ∧
      RoomBirthGate.storedAt birth.authority placement = some cap ∧
      cap.holder.Covers descriptor.creator ∧
      cap.Admissible birth.authority.snapshot.authState
        (RoomBirthGate.placeRequest pins birth.authority.snapshot.authState
          (RoomBirthGate.roomRoot birth.directory.directory room) height descriptor room) ∧
      ∃ clock : ClockCellDomain.Loaded deployment durable.snapshot,
        ClockCellDomain.load deployment durable.snapshot = some clock ∧
      ∃ observed : ResourceTargetAdmission.Observed deployment birth.directory.directory
          .object room (RoomBirthGate.roomRoot birth.directory.directory room),
        ∃ law, RoomBirthGate.lawOf birth.directory birth.authority room = some law ∧
          Minidregg.Pred.eval law
            (RoomBirthGate.viewOf clock.clock (RoomBirthGate.placeRequest pins
              birth.authority.snapshot.authState (RoomBirthGate.roomRoot birth.directory.directory room)
              height descriptor room) observed)
            (RoomBirthGate.viewOf clock.clock (RoomBirthGate.placeRequest pins
              birth.authority.snapshot.authState (RoomBirthGate.roomRoot birth.directory.directory room)
              height descriptor room) observed) = true := by
  have exact := prepareBirth_gateHeight prepared
  have granted := birth.birth_under_room_requires_grant member inRoom
  rw [exact] at granted
  exact granted


/-! ## Axiom pins: every K-ROOM 3c theorem (verb, J7 pole, codec, gate, poles) -/

/-- info: 'Minidregg.Theory.TypedAuthorization.Verb.place_allowedBy_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Verb.place_allowedBy_iff
/-- info: 'Minidregg.Theory.TypedAuthorization.Verb.place_grant_cannot_mutate' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Verb.place_grant_cannot_mutate
/-- info: 'Minidregg.Theory.TypedAuthorization.Verb.observe_grant_cannot_place' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.TypedAuthorization.Verb.observe_grant_cannot_place
/-- info: 'Minidregg.Theory.RoomAuthorization.room_cap_survives_law_change' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.RoomAuthorization.room_cap_survives_law_change
/-- info: 'Minidregg.Theory.RoomAuthorization.generationPreserved_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.RoomAuthorization.generationPreserved_of_rows
/-- info: 'Minidregg.Theory.RoomAuthorization.room_cap_revoked_by_generation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.RoomAuthorization.room_cap_revoked_by_generation
/-- info: 'Minidregg.Theory.RoomAuthorization.room_grant_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.RoomAuthorization.room_grant_reads
/-- info: 'Minidregg.Theory.RoomAuthorization.room_grant_reads_after_law_change' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.RoomAuthorization.room_grant_reads_after_law_change
/-- info: 'Minidregg.Theory.RoomAuthorization.room_grant_reads_after_law_change_by_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.RoomAuthorization.room_grant_reads_after_law_change_by_check
/-- info: 'Minidregg.Theory.RoomAuthorization.room_grant_refused_after_rotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.RoomAuthorization.room_grant_refused_after_rotation
/-- info: 'Minidregg.Theory.RoomAuthorization.room_cap_survives_member_rotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.RoomAuthorization.room_cap_survives_member_rotation
/-- info: 'Minidregg.Compiler.ResourceBirthCodec.v4_descriptor_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.ResourceBirthCodec.v4_descriptor_refused
/-- info: 'Minidregg.Kernel.RoomBirthGate.decideRoom_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.decideRoom_ok_iff
/-- info: 'Minidregg.Kernel.RoomBirthGate.decideRoom_absent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.decideRoom_absent
/-- info: 'Minidregg.Kernel.RoomBirthGate.checkAll_ok_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.checkAll_ok_iff
/-- info: 'Minidregg.Kernel.RoomBirthGate.birth_under_room_requires_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.birth_under_room_requires_grant
/-- info: 'Minidregg.Kernel.RoomBirthGate.root_birth_names_no_placement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.root_birth_names_no_placement
/-- info: 'Minidregg.Kernel.RoomBirthGate.member_birth_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.member_birth_admitted
/-- info: 'Minidregg.Kernel.RoomBirthGate.stranger_birth_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.stranger_birth_refused
/-- info: 'Minidregg.Kernel.RoomBirthGate.stranger_with_members_grant_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.stranger_with_members_grant_refused
/-- info: 'Minidregg.Kernel.RoomBirthGate.guest_birth_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.guest_birth_refused
/-- info: 'Minidregg.Kernel.RoomBirthGate.revoked_member_birth_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.revoked_member_birth_refused
/-- info: 'Minidregg.Kernel.RoomBirthGate.lawless_room_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.lawless_room_refused
/-- info: 'Minidregg.Kernel.RoomBirthGate.realm_founder_birth_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.realm_founder_birth_admitted
/-- info: 'Minidregg.Kernel.RoomBirthGate.nonmember_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.nonmember_refused
/-- info: 'Minidregg.Kernel.RoomBirthGate.law_refusal_named' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.law_refusal_named
/-- info: 'Minidregg.Kernel.RoomBirthGate.fake_realm_asset_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGate.fake_realm_asset_refused
/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.birth_under_room_requires_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedBirth.birth_under_room_requires_grant
/-- info: 'Minidregg.Kernel.ResourceBirthController.Concrete.PreparedPreAuthority.birth_under_room_requires_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthController.Concrete.PreparedPreAuthority.birth_under_room_requires_grant
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.AcceptedBirth.birth_under_room_requires_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.ResourceBirthPolicyController.Concrete.AcceptedBirth.birth_under_room_requires_grant
/-- info: 'Minidregg.Kernel.RoomBirthGateAdmission.preparePreAuthority_gateHeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGateAdmission.preparePreAuthority_gateHeight
/-- info: 'Minidregg.Kernel.RoomBirthGateAdmission.prepareBirth_gateHeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGateAdmission.prepareBirth_gateHeight
/-- info: 'Minidregg.Kernel.RoomBirthGateAdmission.prepareGrainBirth_gateHeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGateAdmission.prepareGrainBirth_gateHeight
/-- info: 'Minidregg.Kernel.RoomBirthGateAdmission.birth_under_room_requires_grant_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Kernel.RoomBirthGateAdmission.birth_under_room_requires_grant_at

end Minidregg.Kernel.RoomBirthGateAdmission
