/-
# Kernel.RoomKick — a kick ends a member's authority in the room (PLACE §2.2)

PLACE J10: "A kicks B; B's read of the note is refused `revoked`; B's cap on a
doc B created under `lab` is also refused (it was an attenuation of B's room
cap — the tooth for `ancestors`)."

A cell born under a room is owned by its creator
(`RoomBirthGate.room_birth_owner_is_creator`), and its owner and control grants
carry the creator's placing capability and that capability's ancestors
(`ResourceBirthPolicyController.Concrete.BornLineage`). A kick revokes the
creator's room grant, so `Admissible.ancestorNotRevoked` refuses the born
grants and everything attenuated or delegated from them (each child copies its
parent's ancestors: `Capability.LineageBounds.ancestors`).

Before this, the born grants were roots with `ancestors = ∅`
(`RootGrantShape`), so nothing a kick revoked was in their lineage:
`old_root_shape_survives_kick` is that defect, as a theorem.

The founder's own room grant is outside the kicked lineage and keeps every
cell under the room, the kicked member's included (`founder_keeps_room_after_kick`).
-/
import Kernel.ResourceBirthPolicyController
import Kernel.RoomBirthGate
import Theory.Renounce

namespace Minidregg.Kernel.RoomKick

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.Renounce (RevokedOne InLineage renounce_preserves_others)
open Minidregg.Kernel.ResourceBirthPolicyController.Concrete
  (BornLineage placementLineage placement_mem_born_ancestors)

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry

/-! ## The tooth -/

/-- **`kick_revokes_room_born_authority`.** A grant born for a cell under a room
names the creator's placing capability among its ancestors. Once that capability
is revoked (a kick), no capability whose ancestors include the born grant's —
the born owner or control grant itself, and every attenuation or delegation
descending from it — is admissible for any request. -/
theorem kick_revokes_room_born_authority
    {lineage : CapabilityId → Option (Finset CapabilityId)} {descriptor : Descriptor Registry}
    (bound : BornLineage lineage descriptor)
    {item : BirthItem Registry} (member : item ∈ descriptor.births)
    {placement : CapabilityId} (placed : item.placement = some placement)
    {grant : AuthorityGrant} (grantMember : grant ∈ descriptor.grants)
    (forBirth : grant.ForBirth item)
    {state : AuthState} (kicked : RevocationKey.capability placement ∈ state.revoked)
    {kind : ResourceKind} (cap : Capability kind)
    (descends : grant.capability.head.ancestors ⊆ cap.ancestors) (request : Request kind) :
    ¬ cap.Admissible state request := fun admitted =>
  admitted.ancestorNotRevoked placement
    (descends (placement_mem_born_ancestors bound member placed grantMember forBirth)) kicked

/-- The born grant itself is refused after the kick. -/
theorem kick_revokes_born_grant
    {lineage : CapabilityId → Option (Finset CapabilityId)} {descriptor : Descriptor Registry}
    (bound : BornLineage lineage descriptor)
    {item : BirthItem Registry} (member : item ∈ descriptor.births)
    {placement : CapabilityId} (placed : item.placement = some placement)
    {grant : AuthorityGrant} (grantMember : grant ∈ descriptor.grants)
    (forBirth : grant.ForBirth item)
    {state : AuthState} (kicked : RevocationKey.capability placement ∈ state.revoked)
    (request : Request grant.kind) :
    ¬ grant.capability.head.Admissible state request :=
  kick_revokes_room_born_authority bound member placed grantMember forBirth kicked
    grant.capability.head (fun _ held => held) request

/-- Every descendant of the born grant (any chain of attenuations and
delegations, `Capability.LineageBounds`) is refused after the kick: bob's
delegation of his doc to eve falls with bob. -/
theorem kick_revokes_born_descendants
    {lineage : CapabilityId → Option (Finset CapabilityId)} {descriptor : Descriptor Registry}
    (bound : BornLineage lineage descriptor)
    {item : BirthItem Registry} (member : item ∈ descriptor.births)
    {placement : CapabilityId} (placed : item.placement = some placement)
    {grant : AuthorityGrant} (grantMember : grant ∈ descriptor.grants)
    (forBirth : grant.ForBirth item)
    {state : AuthState} (kicked : RevocationKey.capability placement ∈ state.revoked)
    {parentage : Parentage} (cap : Capability grant.kind)
    (descends : Capability.LineageBounds cap grant.capability.head parentage)
    (request : Request grant.kind) :
    ¬ cap.Admissible state request :=
  kick_revokes_room_born_authority bound member placed grantMember forBirth kicked cap
    descends.ancestors request

/-- **At the native admission.** Every admitted birth of an item into room `R`
names a placing capability held by the creator, is owned by the creator, and
once that placing capability is revoked no capability descending from any grant
born for the item is admissible. -/
theorem accepted_kick_revokes_room_born_authority {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F}
    {deployment : CanonicalCellRegistry.Deployment} {pins : FactoryPins}
    {durable : ResourceBirthController.Concrete.Durable} {height : Height}
    (accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth profile deployment pins durable height)
    {item : BirthItem Registry} (member : item ∈ accepted.descriptor.births)
    {room : Nat} (inRoom : item.parent = some room) :
    ∃ placement cap, item.placement = some placement ∧
      RoomBirthGate.storedAt accepted.prepared.authority placement = some cap ∧
      cap.holder.Covers accepted.descriptor.creator ∧
      item.owner = accepted.descriptor.creator ∧
      ∀ grant ∈ accepted.descriptor.grants, grant.ForBirth item →
        ∀ state : AuthState, RevocationKey.capability placement ∈ state.revoked →
          ∀ (kind : ResourceKind) (held : Capability kind),
            grant.capability.head.ancestors ⊆ held.ancestors →
            ∀ request, ¬ held.Admissible state request := by
  obtain ⟨placement, cap, placed, stored, holder, _⟩ :=
    accepted.birth_under_room_requires_grant member inRoom
  exact ⟨placement, cap, placed, stored, holder,
    RoomBirthGate.room_birth_owner_is_creator accepted.prepared.rooms member inRoom,
    fun grant grantMember forBirth state kicked kind held descends request =>
      kick_revokes_room_born_authority accepted.pending.bornLineage member placed grantMember
        forBirth kicked held descends request⟩

/-! ## The old shape, and the founder -/

/-- **`old_root_shape_survives_kick`** (the defect, on the old shape). The
born grants used to satisfy `parent = none ∧ ancestors = ∅`. Such a grant is
outside the lineage of any other capability, so revoking the creator's room
grant leaves it exactly as admissible as before, for every request. -/
theorem old_root_shape_survives_kick {pre post : AuthState} {placement : CapabilityId}
    (kick : RevokedOne pre post (.capability placement)) {kind : ResourceKind}
    (born : Capability kind) (ancestorsEmpty : born.ancestors = ∅) (other : born.id ≠ placement)
    (request : Request kind) :
    born.Admissible post request ↔ born.Admissible pre request :=
  renounce_preserves_others kick born
    (fun inLineage => inLineage.elim other (fun held => by simp [ancestorsEmpty] at held)) request

/-- **`founder_keeps_room_after_kick`.** A capability outside the kicked
lineage — the founder's own room grant, `under R` — is admissible after the kick
exactly when it was before, on every cell under the room, the kicked member's
docs included. -/
theorem founder_keeps_room_after_kick {pre post : AuthState} {placement : CapabilityId}
    (kick : RevokedOne pre post (.capability placement)) {kind : ResourceKind}
    (founder : Capability kind) (outside : ¬ InLineage placement founder)
    (request : Request kind) :
    founder.Admissible post request ↔ founder.Admissible pre request :=
  renounce_preserves_others kick founder outside request

/-! ## Poles, by the refusal classifier

Room 7 holds bob's doc 50 (`RoomBirthGate.Sample`): founder alice (4) holds the
room's root grant 20 `under 7`; bob (5) held member grant 22 and bore doc 50
with it; bob delegated doc 50 to eve (6). The kick revokes 22. Bob is
re-invited with grant 24 and bears doc 51. -/

namespace Sample

open RoomBirthGate.Sample

def eve : SubjectId := ⟨6⟩

/-- Bob's owner grant on doc 50, born under room 7 with his grant 22. -/
def bobDoc : Capability .object :=
  { demoCapability with
    id := ⟨30⟩, root := ⟨30⟩
    holder := .subject memberB
    scope := ⟨.under 50, ResourceBirthPolicyController.Concrete.ownerVerbs .object, 8, none, ∅⟩
    policyId := ⟨50⟩
    ancestors := {⟨22⟩}
    channels := ∅ }

/-- The same grant on the old shape: a root with no ancestors. -/
def oldBobDoc : Capability .object := { bobDoc with ancestors := ∅ }

/-- Bob's delegation of doc 50 to eve. -/
def eveDoc : Capability .object :=
  { bobDoc with
    id := ⟨31⟩, parent := some ⟨30⟩
    holder := .subject eve
    scope := ⟨.under 50, {.observeObject}, 8, none, ∅⟩
    ancestors := insert ⟨30⟩ {⟨22⟩} }

/-- Bob's owner grant on doc 51, born after the re-invite with grant 24. -/
def bobDocAgain : Capability .object :=
  { bobDoc with id := ⟨32⟩, root := ⟨32⟩, scope := ⟨.under 51, ResourceBirthPolicyController.Concrete.ownerVerbs .object, 8, none, ∅⟩,
    policyId := ⟨51⟩, ancestors := {⟨24⟩} }

def read (subject : SubjectId) (cell : Nat) : Request .object :=
  { demoRequest with subject := subject, target := ⟨cell⟩, verb := .observeObject,
    policyId := ⟨cell⟩, cost := 0 }

/-- After the kick: 22 is revoked; doc 51 is in room 7 too. -/
def kicked : AuthState :=
  { roomState {.capability ⟨22⟩} with parent := Parentage.ofList [(50, 7), (51, 7)] }

/-- Refuting pole: bob's own doc, after the kick, is refused `revoked`. -/
theorem bob_doc_refused_after_kick :
    RefusalReason.capabilityRefusal bobDoc kicked (read memberB 50) = some .revoked := by
  decide

/-- Refuting pole: bob's delegation to eve falls with him. -/
theorem eve_delegation_refused_after_kick :
    RefusalReason.capabilityRefusal eveDoc kicked (read eve 50) = some .revoked := by
  decide

/-- The defect, concretely: on the old shape bob still reads his doc. -/
theorem old_shape_bob_doc_admitted_after_kick :
    RefusalReason.capabilityRefusal oldBobDoc kicked (read memberB 50) = none := by
  decide

/-- Accepting pole: re-invited with a fresh grant, bob's new doc is admitted. -/
theorem reinvited_member_doc_admitted :
    RefusalReason.capabilityRefusal bobDocAgain kicked (read memberB 51) = none := by
  decide

/-- The founder still reads bob's doc through her room grant. -/
theorem founder_reads_bob_doc_after_kick :
    RefusalReason.capabilityRefusal founderGrant kicked (read founder 50) = none := by
  decide

end Sample

/-- info: 'Minidregg.Kernel.RoomKick.kick_revokes_room_born_authority' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kick_revokes_room_born_authority
/-- info: 'Minidregg.Kernel.RoomKick.kick_revokes_born_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kick_revokes_born_grant
/-- info: 'Minidregg.Kernel.RoomKick.kick_revokes_born_descendants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kick_revokes_born_descendants
/-- info: 'Minidregg.Kernel.RoomKick.accepted_kick_revokes_room_born_authority' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_kick_revokes_room_born_authority
/-- info: 'Minidregg.Kernel.RoomKick.old_root_shape_survives_kick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms old_root_shape_survives_kick
/-- info: 'Minidregg.Kernel.RoomKick.founder_keeps_room_after_kick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms founder_keeps_room_after_kick
/-- info: 'Minidregg.Kernel.RoomKick.Sample.bob_doc_refused_after_kick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Sample.bob_doc_refused_after_kick
/-- info: 'Minidregg.Kernel.RoomKick.Sample.eve_delegation_refused_after_kick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Sample.eve_delegation_refused_after_kick
/-- info: 'Minidregg.Kernel.RoomKick.Sample.old_shape_bob_doc_admitted_after_kick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Sample.old_shape_bob_doc_admitted_after_kick
/-- info: 'Minidregg.Kernel.RoomKick.Sample.reinvited_member_doc_admitted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Sample.reinvited_member_doc_admitted
/-- info: 'Minidregg.Kernel.RoomKick.Sample.founder_reads_bob_doc_after_kick' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Sample.founder_reads_bob_doc_after_kick

end Minidregg.Kernel.RoomKick
