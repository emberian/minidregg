/-
# Kernel.RoomBirthGate — who may bear a cell into a room

A birth that names a room `R` (`create --in R`) is admitted only when

1. the creator names a **placing capability** (`BirthItem.placement`) that is a
   stored capability of the authority cell, admissible for the creator's
   `placeObject` request on `R` (`placeRequest`): its holder covers the creator,
   its scope covers `R` with `placeObject` (or `mutateObject`), and it is
   current and unrevoked with all its ancestors — a **member** of `R`; and
2. `R`'s own committed law accepts that request, read through the same
   projection observation admission reads a cell's law through
   (`ResourceObservationAdmission.projectWith`), including the committed clock
   loaded from the same durable snapshot. Missing clocks fail closed.

So a room's law decides who may birth into it, over its members. The stock
templates: a workroom or social room's law admits every member; a realm's law
admits only its founder and referee (`placeObject` from anyone else fails the
law), so a stranger — or an ordinary player — cannot birth an account into a
realm, i.e. cannot issue a "realm asset" the realm's ledger would list
(`Kernel.RealmWellReceiver`: a realm well is any account with a parent row).

Refusals are named: `notRoomMember R reason` (the capability component that
decided it: `noGrant`, `revoked`, `staleGrant`, `outsideValidity`),
`clockUnavailable` when the committed clock cannot be loaded,
`birthRefused R leaf` (the failing clause of `R`'s law) and `ownerNotCreator R`.

A birth into a room is owned by its creator. Authority over a cell born in a
room is an attenuation of the creator's room grant: the born grants carry that
grant's lineage as their `ancestors`
(`ResourceBirthPolicyController.Concrete.BornLineage`), so a kick of the
creator takes them down. A cell born for another owner would carry the
creator's lineage, not the owner's, and survive the owner's kick; it is
refused. A founder who wants a member to hold a cell births it and delegates. The gate runs in
`ResourceBirthController.preparePreAuthority`, the one preparation every birth
route (bare, grain, draft) passes through, at the admission height.
-/
import Kernel.ResourceObservationAdmission
import Compiler.RefusalReason
import Compiler.ResourceBirthCodec

namespace Minidregg.Kernel.RoomBirthGate

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState (readCapability)

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Registry := CanonicalCellRegistry.registry

/-- Why a birth into a room is refused, by name. -/
inductive Refusal where
  /-- The deployment's committed clock cannot be loaded from this snapshot.
  A room law is never evaluated with a fabricated/default clock. -/
  | clockUnavailable
  /-- The named room is not an object resource of the directory: rooms are
  object cells. -/
  | notARoom (room : Nat)
  /-- A room birth named no placing capability, or a root birth named one. -/
  | placementShape
  /-- The creator holds no admissible capability placing cells in the room; the
  reason is the capability component that decided it. -/
  | notRoomMember (room : Nat) (reason : RefusalReason)
  /-- The creator is a member and the room's own law refuses the placement:
  its failing clause (`none`: the room has no committed law). -/
  | birthRefused (room : Nat) (leaf : Option LawLeaf)
  /-- The creator is a member and the room's law refuses the placement by a clause over
  fields outside the creator's grant: no clause and no value is named (FIX-DISCLOSE). -/
  | birthRefusedOutsideGrant (room : Nat)
  /-- A birth into the room names an owner other than its creator. -/
  | ownerNotCreator (room : Nat)
  deriving DecidableEq, Repr

/-! ## The pure decision -/

/-- Placement is explicit authority, or the existing full-room mutation
alias. A title-only, annotation-only, or bounded mutation grant must not acquire
room placement authority when the place verb is introduced by an upgrade. -/
def PlacementScope (scope : Scope .object) : Prop :=
  Verb.placeObject ∈ scope.verbs ∨
    (Verb.mutateObject ∈ scope.verbs ∧ scope.fields = none ∧ scope.maxDelta = ∅)

instance (scope : Scope .object) : Decidable (PlacementScope scope) := by
  unfold PlacementScope
  infer_instance

/-- One room: the stored capability at the named id (if any), the authority
projection, the creator's placement request, the room's committed law (if any)
and the law's view of the room. -/
def decideRoom (room : Nat) (stored : Option (Capability .object)) (state : AuthState)
    (request : Request .object) (law : Option Minidregg.Pred.Pred)
    (view : Minidregg.Pred.State) : Except Refusal Unit :=
  match stored with
  | none => .error (.notRoomMember room .noGrant)
  | some cap =>
      match RefusalReason.capabilityRefusal cap state request with
      | some reason => .error (.notRoomMember room reason)
      | none =>
          if !decide (PlacementScope cap.scope) then .error (.notRoomMember room .noGrant)
          else match law with
          | none => .error (.birthRefused room none)
          | some law =>
              match LawLeaf.of law view view with
              | none => .ok ()
              | some _ =>
                  -- The clause told is narrowed to the creator's grant (`LawLeaf.narrowed`).
                  match LawLeaf.narrowed cap.scope.fields law view view with
                  | some leaf => .error (.birthRefused room (some leaf))
                  | none => .error (.birthRefusedOutsideGrant room)

/-- The decision admits exactly a member whose capability is admissible and
whose placement the room's law accepts. -/
theorem decideRoom_ok_iff (room : Nat) (stored : Option (Capability .object))
    (state : AuthState) (request : Request .object) (law : Option Minidregg.Pred.Pred)
    (view : Minidregg.Pred.State) :
    decideRoom room stored state request law view = .ok () ↔
      ∃ cap, stored = some cap ∧ cap.Admissible state request ∧
        PlacementScope cap.scope ∧ ∃ pred, law = some pred ∧ Minidregg.Pred.eval pred view view = true := by
  unfold decideRoom
  cases stored with
  | none => simp
  | some cap =>
      cases refusal : RefusalReason.capabilityRefusal cap state request with
      | some reason =>
          have inadmissible : ¬ cap.Admissible state request := by
            rw [← RefusalReason.capabilityRefusal_eq_none_iff_admissible, refusal]
            simp
          simp [refusal, inadmissible]
      | none =>
          have admissible : cap.Admissible state request :=
            (RefusalReason.capabilityRefusal_eq_none_iff_admissible cap state request).mp refusal
          by_cases placing : PlacementScope cap.scope
          · simp only [placing, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            cases law with
            | none => simp [refusal]
            | some pred =>
                cases leaf : LawLeaf.of pred view view with
                | none =>
                    have accepts := (LawLeaf.of_none_iff pred view view).mp leaf
                    simp [refusal, leaf, admissible, accepts, placing]
                | some named =>
                    have rejects : Minidregg.Pred.eval pred view view = false := by
                      cases evaluated : Minidregg.Pred.eval pred view view with
                      | false => rfl
                      | true =>
                          have := (LawLeaf.of_none_iff pred view view).mpr evaluated
                          rw [leaf] at this
                          cases this
                    simp only [refusal, leaf]
                    constructor
                    · intro decided
                      split at decided <;> cases decided
                    · rintro ⟨_, stored, _, _, _, found, accepts⟩
                      cases stored
                      cases found
                      rw [rejects] at accepts
                      cases accepts
          · simp [placing, refusal]

/-- Actual successful placement carries the same scope condition checked by
this receiver, independently of the broader global verb alias. -/
theorem decideRoom_ok_has_placement (room : Nat) (stored : Option (Capability .object))
    (state : AuthState) (request : Request .object) (law : Option Minidregg.Pred.Pred)
    (view : Minidregg.Pred.State) (accepted : decideRoom room stored state request law view = .ok ()) :
    ∃ cap, stored = some cap ∧ PlacementScope cap.scope := by
  obtain ⟨cap, present, _, placing, _⟩ :=
    (decideRoom_ok_iff room stored state request law view).mp accepted
  exact ⟨cap, present, placing⟩

/-- A creator naming no stored capability is refused as a non-member. -/
theorem decideRoom_absent (room : Nat) (state : AuthState) (request : Request .object)
    (law : Option Minidregg.Pred.Pred) (view : Minidregg.Pred.State) :
    decideRoom room none state request law view = .error (.notRoomMember room .noGrant) := rfl

/-! ## The deployed gate -/

/-- The creator's placement request on `room`: the birth's own factory request
(creator, key epoch, nonce, the descriptor's digests, the height) retargeted at
the room with verb `placeObject`, under the room's own current law. -/
def placeRequest (pins : FactoryPins) (state : AuthState) (roomRoot : Digest) (height : Height)
    (descriptor : Descriptor Registry) (room : Nat) : Request .object :=
  { factoryRequest pins CanonicalCellRegistry.sourceEncoding state roomRoot height descriptor with
    target := ⟨room⟩
    verb := .placeObject
    policyId := ⟨room⟩
    policyEpoch := state.policyEpoch ⟨room⟩
    policyRevision := state.policyRevision ⟨room⟩
    cost := 0 }

@[simp] theorem placeRequest_subject (pins : FactoryPins) (state : AuthState) (roomRoot : Digest)
    (height : Height) (descriptor : Descriptor Registry) (room : Nat) :
    (placeRequest pins state roomRoot height descriptor room).subject = descriptor.creator := rfl

variable {deployment : Deployment} {durable : Durable}

/-- The stored capability at `placement`, as a capability. -/
def storedAt (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (placement : CapabilityId) : Option (Capability .object) :=
  (readCapability authority.snapshot.cell .object placement).map (·.head)

/-- The room's committed law at its current revision, read from the same policy
registry and source store observation admission resolves laws from. -/
def lawOf (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (room : Nat) : Option Minidregg.Pred.Pred :=
  ((CredentialAuthorityPolicyRegistry.policyRegistry authority.snapshot
      (ResourceObservationAdmission.sourceStore ⟨directory, authority⟩)).resolve ⟨room⟩
      (authority.snapshot.authState.policyRevision ⟨room⟩)).map (·.record.predicate)

/-- The room cell's current root, as the loaded directory holds it (the zero
digest when the slot is absent; `checkRoom` then refuses `notARoom`). -/
def roomRoot (directory : Directory Nat Registry) (room : Nat) : Digest :=
  match directory.slots room with
  | .present cell => cell.payload.root
  | .absent => ⟨0⟩

/-- The law's view of the room for the placement request, with the receiving
snapshot's committed clock. The caller must load the clock before evaluating a law. -/
def viewOf (clock : Kernel.ClockCell.Clock) {room : Nat} {root : Digest}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    (request : Request .object)
    (observed : ResourceTargetAdmission.Observed deployment directory.directory .object room root) :
    Minidregg.Pred.State :=
  ResourceObservationAdmission.projectWith clock request [] observed.before.kind [] observed.before.payload.logical

/-- One room birth: the room is an object cell of the directory, and the
creator's placing capability and the room's law admit the placement. -/
def checkRoom (pins : FactoryPins)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (height : Height) (descriptor : Descriptor Registry) (room : Nat) (placement : CapabilityId) :
    Except Refusal Unit :=
  match Kernel.ClockCellDomain.load deployment durable.snapshot with
  | none => .error .clockUnavailable
  | some clock =>
      match ResourceTargetAdmission.observe deployment directory.directory .object room
          (roomRoot directory.directory room) with
      | none => .error (.notARoom room)
      | some observed =>
          let request := placeRequest pins authority.snapshot.authState (roomRoot directory.directory room)
            height descriptor room
          decideRoom room (storedAt authority placement) authority.snapshot.authState request
            (lawOf directory authority room) (viewOf clock.clock request observed)

/-- A missing or invalid committed clock refuses room placement before a room law
can be evaluated. Root births do not evaluate a room law and remain unaffected. -/
theorem checkRoom_clock_unavailable (pins : FactoryPins)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (height : Height) (descriptor : Descriptor Registry) (room : Nat) (placement : CapabilityId)
    (missing : Kernel.ClockCellDomain.load deployment durable.snapshot = none) :
    checkRoom pins directory authority height descriptor room placement = .error .clockUnavailable := by
  simp [checkRoom, missing]

/-- Room placement laws read the clock before request/resource slots, exactly as
observations do. A resource field with a colliding name cannot shadow these slots. -/
theorem viewOf_clock_exact (clock : Kernel.ClockCell.Clock) {room : Nat} {root : Digest}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    (request : Request .object)
    (observed : ResourceTargetAdmission.Observed deployment directory.directory .object room root) :
    (viewOf clock request observed).get "clock/now" = some (Int.ofNat clock.now) ∧
      (viewOf clock request observed).get "clock/day" =
        some (Int.ofNat (clock.now / Kernel.ClockCell.secondsPerDay)) ∧
      (viewOf clock request observed).get "clock/slot" = some (Int.ofNat clock.slot) := by
  simp [viewOf, ResourceObservationAdmission.projectWith, Kernel.ClockCell.slots, Minidregg.Pred.State.get]

/-- One birth item: a root birth names no placing capability; a room birth
names one, is owned by its creator, and passes `checkRoom`. -/
def checkItem (pins : FactoryPins)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (height : Height) (descriptor : Descriptor Registry) (item : BirthItem Registry) :
    Except Refusal Unit :=
  match item.parent, item.placement with
  | none, none => .ok ()
  | some room, some placement =>
      if item.owner = descriptor.creator then
        checkRoom pins directory authority height descriptor room placement
      else .error (.ownerNotCreator room)
  | _, _ => .error .placementShape

/-- First refusal over a list, in order. -/
def checkAll {α : Type} (check : α → Except Refusal Unit) : List α → Except Refusal Unit
  | [] => .ok ()
  | item :: rest =>
      match check item with
      | .error reason => .error reason
      | .ok () => checkAll check rest

theorem checkAll_ok_iff {α : Type} (check : α → Except Refusal Unit) (items : List α) :
    checkAll check items = .ok () ↔ ∀ item ∈ items, check item = .ok () := by
  induction items with
  | nil => simp [checkAll]
  | cons item rest ih =>
      unfold checkAll
      cases checked : check item with
      | error reason => simp [checked]
      | ok value => cases value; simp [checked, ih]

/-- Every birth item of the descriptor passes the gate. -/
def Admitted (pins : FactoryPins)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (height : Height) (descriptor : Descriptor Registry) : Prop :=
  ∀ item ∈ descriptor.births, checkItem pins directory authority height descriptor item = .ok ()

/-- The gate: the first refusal, by name, or the admission. -/
def check (pins : FactoryPins)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (height : Height) (descriptor : Descriptor Registry) :
    Except Refusal (PLift (Admitted pins directory authority height descriptor)) :=
  match decided : checkAll (checkItem pins directory authority height descriptor) descriptor.births with
  | .error reason => .error reason
  | .ok () => .ok ⟨(checkAll_ok_iff _ _).mp decided⟩

/-- **`birth_under_room_requires_grant`.** Every admitted birth of an item into
room `R` names a placing capability stored in the authority cell, held by the
creator, admissible for the creator's `placeObject` request on `R`, and `R`'s
committed law accepts that request on `R`'s current state. -/
theorem birth_under_room_requires_grant {pins : FactoryPins}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {height : Height} {descriptor : Descriptor Registry}
    (admitted : Admitted pins directory authority height descriptor)
    {item : BirthItem Registry} (member : item ∈ descriptor.births)
    {room : Nat} (inRoom : item.parent = some room) :
    ∃ placement cap, item.placement = some placement ∧ storedAt authority placement = some cap ∧
      cap.holder.Covers descriptor.creator ∧
      cap.Admissible authority.snapshot.authState
        (placeRequest pins authority.snapshot.authState (roomRoot directory.directory room) height descriptor room) ∧
      ∃ clock : Kernel.ClockCellDomain.Loaded deployment durable.snapshot,
        Kernel.ClockCellDomain.load deployment durable.snapshot = some clock ∧
        ∃ observed : ResourceTargetAdmission.Observed deployment directory.directory .object room
          (roomRoot directory.directory room),
        ∃ law, lawOf directory authority room = some law ∧
          Minidregg.Pred.eval law
            (viewOf clock.clock (placeRequest pins authority.snapshot.authState (roomRoot directory.directory room)
              height descriptor room) observed)
            (viewOf clock.clock (placeRequest pins authority.snapshot.authState (roomRoot directory.directory room)
              height descriptor room) observed) = true := by
  have passed := admitted item member
  cases placed : item.placement with
  | none => simp [checkItem, inRoom, placed] at passed
  | some placement =>
      have step : checkRoom pins directory authority height descriptor room placement = .ok () := by
        by_cases owner : item.owner = descriptor.creator
        · simpa [checkItem, inRoom, placed, owner] using passed
        · simp [checkItem, inRoom, placed, owner] at passed
      cases loaded : Kernel.ClockCellDomain.load deployment durable.snapshot with
      | none => simp [checkRoom, loaded] at step
      | some clock =>
          simp only [checkRoom, loaded] at step
          split at step
          · cases step
          · rename_i observed _
            obtain ⟨cap, stored, admissible, _placing, law, resolved, accepts⟩ :=
              (decideRoom_ok_iff _ _ _ _ _ _).mp step
            exact ⟨placement, cap, rfl, stored, admissible.holder, admissible, clock, rfl,
              observed, law, resolved, accepts⟩

/-- **`room_birth_owner_is_creator`.** Every admitted birth into a room is
owned by its creator, so its grants are held by the subject whose placing
capability they descend from. -/
theorem room_birth_owner_is_creator {pins : FactoryPins}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {height : Height} {descriptor : Descriptor Registry}
    (admitted : Admitted pins directory authority height descriptor)
    {item : BirthItem Registry} (member : item ∈ descriptor.births)
    {room : Nat} (inRoom : item.parent = some room) : item.owner = descriptor.creator := by
  have passed := admitted item member
  cases placed : item.placement with
  | none => simp [checkItem, inRoom, placed] at passed
  | some placement =>
      by_cases owner : item.owner = descriptor.creator
      · exact owner
      · simp [checkItem, inRoom, placed, owner] at passed

/-- A root birth names no placing capability. -/
theorem root_birth_names_no_placement {pins : FactoryPins}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {height : Height} {descriptor : Descriptor Registry}
    (admitted : Admitted pins directory authority height descriptor)
    {item : BirthItem Registry} (member : item ∈ descriptor.births)
    (root : item.parent = none) : item.placement = none := by
  have passed := admitted item member
  cases placed : item.placement with
  | none => rfl
  | some _ => simp [checkItem, root, placed] at passed

/-! ## Poles, on the pure decision

Room 7. The founder (subject 4) holds the room's root grant; member B (subject 5)
holds an invite `{observe, place}` under 7; guest G (subject 6) holds
`{observe}`; stranger C (subject 9) holds nothing, or presents B's grant. -/

namespace Sample

open Minidregg.Pred

def founder : SubjectId := ⟨4⟩
def memberB : SubjectId := ⟨5⟩
def guest : SubjectId := ⟨6⟩
def stranger : SubjectId := ⟨9⟩

def roomState (revoked : Finset RevocationKey) : AuthState :=
  { demoState with revoked := revoked, parent := Parentage.ofList [(50, 7)] }

def grant (id : Nat) (holder : SubjectId) (verbs : Finset (Verb .object)) : Capability .object :=
  { demoCapability with
    id := ⟨id⟩
    holder := .subject holder
    scope := ⟨.under 7, verbs, 8, none, ∅⟩
    policyId := ⟨7⟩ }

def founderGrant : Capability .object :=
  grant 20 founder {.observeObject, .mutateObject, .delegateObject, .placeObject}
def memberGrant : Capability .object := grant 22 memberB {.observeObject, .placeObject}
def guestGrant : Capability .object := grant 23 guest {.observeObject}

/-- `subject` places a cell in room 7 at height `demoRequest.height`. -/
def place (subject : SubjectId) : Request .object :=
  { demoRequest with
    subject := subject
    target := ⟨7⟩
    verb := .placeObject
    policyId := ⟨7⟩
    cost := 0 }

/-- The view the room's law reads: here, the request's own slots. -/
def view (subject : SubjectId) : State := ⟨CanonicalRuntimeProfile.requestSlots (place subject)⟩

/-- The workroom template: every member may place. -/
def openLaw : Pred := .allL .nil

/-- The realm template: a placement (`request/verb` = place, tag 10) only by the
founder. Every other verb is unconstrained by this clause. -/
def realmLaw : Pred :=
  .anyL (.cons (.not (.eq "request/verb" 10)) (.cons (.memberOf "request/subject" [4]) .nil))

end Sample

open Sample

/-- Honest pole: member B places a cell in the workroom. -/
theorem member_birth_admitted :
    decideRoom 7 (some memberGrant) (roomState ∅) (place memberB) (some openLaw) (view memberB) =
      .ok () := by decide

/-- **Stranger, no grant**: refused `notRoomMember … noGrant`. -/
theorem stranger_birth_refused :
    decideRoom 7 none (roomState ∅) (place stranger) (some openLaw) (view stranger) =
      .error (.notRoomMember 7 .noGrant) := rfl

/-- **Stranger presenting B's grant**: refused `notRoomMember … noGrant` (the
holder does not cover the stranger). -/
theorem stranger_with_members_grant_refused :
    decideRoom 7 (some memberGrant) (roomState ∅) (place stranger) (some openLaw) (view stranger) =
      .error (.notRoomMember 7 .noGrant) := by decide

/-- A guest (`{observe}`) may read the room and may not bear cells into it. -/
theorem guest_birth_refused :
    decideRoom 7 (some guestGrant) (roomState ∅) (place guest) (some openLaw) (view guest) =
      .error (.notRoomMember 7 .noGrant) := by decide

/-- A kicked member (grant revoked) is refused `revoked`. -/
theorem revoked_member_birth_refused :
    decideRoom 7 (some memberGrant) (roomState {.capability ⟨22⟩}) (place memberB)
        (some openLaw) (view memberB) =
      .error (.notRoomMember 7 .revoked) := by decide

/-- A room whose law is missing refuses every placement (fail closed). -/
theorem lawless_room_refused :
    decideRoom 7 (some memberGrant) (roomState ∅) (place memberB) none (view memberB) =
      .error (.birthRefused 7 none) := rfl

/-- The realm's founder births a well. -/
theorem realm_founder_birth_admitted :
    decideRoom 7 (some founderGrant) (roomState ∅) (place founder) (some realmLaw)
      (view founder) = .ok () := by decide

/-- Exact scope poles use the actual admission decision, not a separate model. -/
def titleOnlyGrant : Capability .object :=
  { founderGrant with scope := { founderGrant.scope with
      verbs := {.mutateObject}, fields := some {.slot 0} } }
def boundedMutationGrant : Capability .object :=
  { founderGrant with scope := { founderGrant.scope with
      verbs := {.mutateObject}, maxDelta := {(.slot 0, 1)} } }
def fullMutationGrant : Capability .object :=
  { founderGrant with scope := { founderGrant.scope with verbs := {.mutateObject} } }

theorem title_only_cannot_place :
    decideRoom 7 (some titleOnlyGrant) (roomState ∅) (place founder) (some openLaw)
      (view founder) = .error (.notRoomMember 7 .noGrant) := by decide

theorem bounded_mutation_cannot_place :
    decideRoom 7 (some boundedMutationGrant) (roomState ∅) (place founder) (some openLaw)
      (view founder) = .error (.notRoomMember 7 .noGrant) := by decide

theorem unrestricted_mutation_can_place :
    decideRoom 7 (some fullMutationGrant) (roomState ∅) (place founder) (some openLaw)
      (view founder) = .ok () := by decide

/-! ## The general refusal forms -/

/-- A creator whose named capability is inadmissible for its placement is
refused as a non-member, with the deciding component's reason. -/
theorem nonmember_refused (room : Nat) (cap : Capability .object) (state : AuthState)
    (request : Request .object) (law : Option Minidregg.Pred.Pred) (view : Minidregg.Pred.State)
    (inadmissible : ¬ cap.Admissible state request) :
    ∃ reason, decideRoom room (some cap) state request law view =
      .error (.notRoomMember room reason) := by
  cases refusal : RefusalReason.capabilityRefusal cap state request with
  | none =>
      exact absurd ((RefusalReason.capabilityRefusal_eq_none_iff_admissible _ _ _).mp refusal)
        inadmissible
  | some reason => exact ⟨reason, by simp [decideRoom, refusal]⟩

/-- A member whose placement the room's law refuses is refused `birthRefused`, naming
the clause narrowed to the member's grant (`LawLeaf.narrowed`), or
`birthRefusedOutsideGrant` when every failing clause reads outside it. -/
theorem law_refusal_named (room : Nat) (cap : Capability .object) (state : AuthState)
    (request : Request .object) (law : Minidregg.Pred.Pred) (view : Minidregg.Pred.State)
    (admissible : cap.Admissible state request)
    (placing : PlacementScope cap.scope)
    (refuses : Minidregg.Pred.eval law view view = false) :
    decideRoom room (some cap) state request (some law) view =
      match LawLeaf.narrowed cap.scope.fields law view view with
      | some leaf => .error (.birthRefused room (some leaf))
      | none => .error (.birthRefusedOutsideGrant room) := by
  have none_ : RefusalReason.capabilityRefusal cap state request = none :=
    (RefusalReason.capabilityRefusal_eq_none_iff_admissible _ _ _).mpr admissible
  cases named : LawLeaf.of law view view with
  | none =>
      have := (LawLeaf.of_none_iff law view view).mp named
      rw [refuses] at this; cases this
  | some leaf => simp [decideRoom, none_, named, placing]

/-- An unnarrowed member (`fields = none`) is told the failing clause, as before. -/
theorem law_refusal_named_unnarrowed (room : Nat) (cap : Capability .object) (state : AuthState)
    (request : Request .object) (law : Minidregg.Pred.Pred) (view : Minidregg.Pred.State)
    (admissible : cap.Admissible state request) (placing : PlacementScope cap.scope)
    (whole : cap.scope.fields = none)
    (refuses : Minidregg.Pred.eval law view view = false) :
    ∃ leaf, decideRoom room (some cap) state request (some law) view =
      .error (.birthRefused room (some leaf)) := by
  rw [law_refusal_named room cap state request law view admissible placing refuses, whole,
    LawLeaf.narrowed_none]
  cases named : LawLeaf.of law view view with
  | none =>
      have := (LawLeaf.of_none_iff law view view).mp named
      rw [refuses] at this; cases this
  | some leaf => exact ⟨leaf, rfl⟩

/-- **`fake_realm_asset_refused`.** No one but the realm's founder can bear an
account (a would-be realm asset) into the realm: a stranger is refused as a
non-member, and even a member holding `placeObject` under the realm is refused by
the realm's law, naming its clause. -/
theorem fake_realm_asset_refused :
    decideRoom 7 none (roomState ∅) (place stranger) (some realmLaw) (view stranger) =
        .error (.notRoomMember 7 .noGrant) ∧
      ∃ leaf, decideRoom 7 (some memberGrant) (roomState ∅) (place memberB) (some realmLaw)
        (view memberB) = .error (.birthRefused 7 (some leaf)) :=
  ⟨rfl, law_refusal_named_unnarrowed 7 memberGrant (roomState ∅) (place memberB) realmLaw
    (view memberB) ((RefusalReason.capabilityRefusal_eq_none_iff_admissible _ _ _).mp (by decide))
    (by decide) rfl (by decide)⟩

end Minidregg.Kernel.RoomBirthGate
