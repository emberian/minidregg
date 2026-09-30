/-
# Theory.RoomAuthorization — `under R` scopes and room confidentiality

A room is a cell `R`; `under R` is the room cell itself and every cell whose
parent chain, in the parent projection, reaches `R`. A room under an area under
a realm is under the realm. Parent chains are decided within the projection's
finite support (`Parentage.descends_iff_bounded`), so coverage is decidable
without a depth constant.

A scope reaches a cell in exactly two ways: its target set is `under X` for an
`X` on the cell's parent chain, or it is an explicit set naming that cell.
`room_confidentiality` is the refusal form; `room_admission_traces_to_root` is
the lineage form: every admitted capability with a valid stored lineage
descends from a root whose own target set reaches the cell the same way.
-/
import Theory.CredentialLineageAdmission

namespace Minidregg.Theory.RoomAuthorization

open TypedAuthorization
open CredentialAuthorityFamily
open CredentialAuthorityState
open AuthorizationDeclaration
open CredentialLineageAdmission

set_option autoImplicit false

/-- `under room` covers exactly the cells whose parent chain reaches `room`
(the room itself at length zero), and every such chain has a witness no longer
than the parent projection's support. -/
theorem covers_under_chain {kind : ResourceKind} (parentage : Parentage) (room : Nat)
    (target : ResourceId kind) :
    (TargetSet.under room : TargetSet kind).Covers parentage target ↔
      ∃ n, n ≤ parentage.support.card ∧ parentage.ancestor n target.value = some room := by
  show parentage.Descends target.value room ↔ _
  rw [Parentage.descends_iff_bounded]
  exact ⟨fun ⟨n, lt, hn⟩ => ⟨n, by omega, hn⟩, fun ⟨n, le, hn⟩ => ⟨n, by omega, hn⟩⟩

/-- A cell is covered only by an `under X` whose `X` is on its parent chain, or
by an explicit set naming it. -/
theorem covers_cases {kind : ResourceKind} {targets : TargetSet kind}
    {parentage : Parentage} {target : ResourceId kind}
    (covers : targets.Covers parentage target) :
    (∃ room, targets = .under room ∧ parentage.Descends target.value room) ∨
      ∃ ts, targets = .explicit ts ∧ target ∈ ts := by
  cases targets with
  | explicit ts => exact .inr ⟨ts, rfl, covers⟩
  | under room => exact .inl ⟨room, rfl, covers⟩

/-- Room confidentiality. A capability whose target set is neither `under X`
for an `X` on the requested cell's parent chain nor an explicit set naming the
cell is not admissible for any request on that cell, observation included,
whoever presents it. -/
theorem room_confidentiality {kind : ResourceKind} {state : AuthState}
    {request : Request kind} (cap : Capability kind)
    (offChain : ∀ room, cap.scope.targets = .under room →
      ¬ state.parent.Descends request.target.value room)
    (notNamed : ∀ ts, cap.scope.targets = .explicit ts → request.target ∉ ts) :
    ¬ cap.Admissible state request := by
  intro admitted
  rcases covers_cases admitted.scope.target with ⟨room, same, chain⟩ | ⟨ts, named, member⟩
  · exact offChain room same chain
  · exact notNamed ts named member

/-- Every admitted capability with a valid lineage at the current parent
projection descends from a root (`parent = none`, `root = id`, same root id
and issuer) whose own target set is `under X` for an `X` on the cell's parent
chain, or explicitly names the cell. -/
theorem room_admission_traces_to_root {kind : ResourceKind} {state : AuthState}
    {request : Request kind} {stored : StoredCapability kind}
    (valid : LineageValid state.parent stored)
    (admitted : stored.head.Admissible state request) :
    ∃ root : Capability kind, root.parent = none ∧ root.root = root.id ∧
      stored.head.root = root.root ∧ stored.head.issuer = root.issuer ∧
      ((∃ room, root.scope.targets = .under room ∧
          state.parent.Descends request.target.value room) ∨
        ∃ ts, root.scope.targets = .explicit ts ∧ request.target ∈ ts) := by
  obtain ⟨root, parentNone, rootSelf, bounds⟩ := valid.root_bounds
  have covers := TargetSet.covers_of_narrows bounds.scope.targets admitted.scope.target
  exact ⟨root, parentNone, rootSelf, bounds.root, bounds.issuer, covers_cases covers⟩

/-! ## Concrete poles

Area 3 holds room 7; cell 50 is in room 7; cell 51 is created in room 7
later; room 8 is another room. -/

def roomParents : Parentage := Parentage.ofList [(50, 7), (7, 3)]

def grownParents : Parentage := Parentage.ofList ([(50, 7), (7, 3)] ++ [(51, 7)])

/-- A projection that rewrites cell 50's parent: not an append-only successor. -/
def rewrittenParents : Parentage := Parentage.ofList [(50, 8), (7, 3)]

def roomState : AuthState := { demoState with parent := roomParents }
def grownState : AuthState := { demoState with parent := grownParents }
def rewrittenState : AuthState := { demoState with parent := rewrittenParents }

def roomScope (room : Nat) : Scope .object where
  targets := .under room
  verbs := {.observeObject}
  maxCost := 8

def explicitScope (cell : Nat) : Scope .object where
  targets := .explicit {⟨cell⟩}
  verbs := {.observeObject}
  maxCost := 8

/-- An observation of cell `cell` by subject 4. -/
def observe (cell : Nat) : Request .object :=
  { demoRequest with target := ⟨cell⟩, verb := .observeObject }

def observeNote : Request .object := observe 50

def memberCapability : Capability .object :=
  { demoCapability with scope := roomScope 7 }

def areaCapability : Capability .object :=
  { demoCapability with scope := roomScope 3 }

def otherRoomCapability : Capability .object :=
  { demoCapability with scope := roomScope 8 }

def outsiderCapability : Capability .object :=
  { demoCapability with scope := explicitScope 60 }

theorem grownState_extends_roomState :
    ∀ c p, roomState.parent c = some p → grownState.parent c = some p :=
  Parentage.ofList_append_extends _ _

/-- Honest pole: a holder of `under 7` reads cell 50. -/
theorem member_reads : memberCapability.Admissible roomState observeNote :=
  (capabilityAdmissibleCheck_eq_true_iff _ _ _).mp (by decide)

/-- `under 7` covers the room cell itself: a member reads the roster. -/
theorem member_reads_room : memberCapability.Admissible roomState (observe 7) :=
  (capabilityAdmissibleCheck_eq_true_iff _ _ _).mp (by decide)

/-- Chains are transitive: a holder of `under 3` (the area) reads cell 50,
whose parent is room 7, whose parent is area 3. -/
theorem area_member_reads : areaCapability.Admissible roomState observeNote :=
  (capabilityAdmissibleCheck_eq_true_iff _ _ _).mp (by decide)

/-- A room grant does not reach up the chain: `under 7` is refused on area 3. -/
theorem member_refused_on_area :
    capabilityAdmissibleCheck memberCapability roomState (observe 3) = false := by
  decide

/-- The lineage form at the honest pole: the member's grant is itself a root
whose target set is `under 7`, and 7 is on cell 50's chain. -/
theorem member_traces_to_root :
    ∃ root : Capability .object, root.parent = none ∧ root.root = root.id ∧
      memberCapability.root = root.root ∧ memberCapability.issuer = root.issuer ∧
      ((∃ room, root.scope.targets = .under room ∧
          roomState.parent.Descends observeNote.target.value room) ∨
        ∃ ts, root.scope.targets = .explicit ts ∧ observeNote.target ∈ ts) :=
  room_admission_traces_to_root (stored := ⟨memberCapability, []⟩)
    (.root memberCapability rfl rfl rfl) member_reads

/-- Dishonest pole: an explicit grant on another cell is refused. -/
theorem outsider_refused : ¬ outsiderCapability.Admissible roomState observeNote :=
  room_confidentiality outsiderCapability
    (by intro room named; simp [outsiderCapability, explicitScope] at named)
    (by
      intro ts named
      simp only [outsiderCapability, explicitScope, TargetSet.explicit.injEq] at named
      subst named
      decide)

/-- Dishonest pole: a holder of `under 8` is refused on a cell of room 7. -/
theorem other_room_refused : ¬ otherRoomCapability.Admissible roomState observeNote :=
  room_confidentiality otherRoomCapability
    (by
      intro room named
      simp only [otherRoomCapability, roomScope, TargetSet.under.injEq] at named
      subst named
      decide)
    (by intro ts named; simp [otherRoomCapability, roomScope] at named)

/-- The same refusal, by evaluation. -/
theorem other_room_refused_by_check :
    capabilityAdmissibleCheck otherRoomCapability roomState observeNote = false := by
  decide

/-- The tooth of `narrows_stable`: an explicit grant on cell 51, checked
before 51 is recorded under room 7, is refused... -/
theorem explicit_new_cell_refused_before_birth :
    ¬ (explicitScope 51).Narrows (roomScope 7) roomState.parent := by
  decide

/-- ...and the same delegation is a narrowing once 51 is recorded. -/
theorem explicit_new_cell_narrows_after_birth :
    (explicitScope 51).Narrows (roomScope 7) grownState.parent := by
  decide

/-- A narrowing checked in `roomState` survives into the grown state. -/
theorem explicit_room_cell_narrowing_stable :
    (explicitScope 50).Narrows (roomScope 7) grownState.parent :=
  Scope.narrows_stable grownState_extends_roomState (by decide)

/-- The append-only premise is load-bearing: rewriting cell 50's parent breaks
a narrowing that held before. -/
theorem rewritten_parent_breaks_narrowing :
    (explicitScope 50).Narrows (roomScope 7) roomState.parent ∧
      ¬ (explicitScope 50).Narrows (roomScope 7) rewrittenState.parent := by
  decide

/-- Nested rooms attenuate: `under 7` narrows `under 3` (room 7 is in area 3);
the converse is refused. -/
theorem room_narrows_area :
    (roomScope 7).Narrows (roomScope 3) roomState.parent ∧
      ¬ (roomScope 3).Narrows (roomScope 7) roomState.parent := by
  decide

/-- `under` never narrows to an explicit set, even one naming every current
child of the room. -/
theorem under_never_narrows_to_explicit :
    ¬ (roomScope 7).Narrows (explicitScope 50) grownState.parent := by
  decide

/-! ## A room invite

The owner of room 7 holds `under 7` with the delegate verb; the invite is a
delegation request on the room cell 7 itself, whose child is `under 7` held by
subject 5. `under 7` covers the room cell, so the grantor's own capability is
admissible for the delegate request. -/

def ownerScope : Scope .object where
  targets := .under 7
  verbs := {.observeObject, .delegateObject}
  maxCost := 8

def ownerCapability : Capability .object := { demoCapability with scope := ownerScope }

def inviteRequest : Request .object :=
  { demoRequest with target := ⟨7⟩, verb := .delegateObject }

def inviteCapability : Capability .object :=
  { ownerCapability with
    id := ⟨22⟩
    parent := some ownerCapability.id
    holder := .subject ⟨5⟩
    scope := roomScope 7
    ancestors := insert ownerCapability.id ownerCapability.ancestors }

/-- Honest pole: a room invite is a well-shaped delegation. -/
theorem room_invite_shape :
    DelegationShape inviteRequest inviteCapability ownerCapability roomState.parent := by
  decide

/-- The invitee then reads cell 50 of the room. -/
theorem invitee_reads :
    { observeNote with subject := ⟨5⟩ } |> inviteCapability.Admissible roomState :=
  (capabilityAdmissibleCheck_eq_true_iff _ _ _).mp (by decide)

/-- Dishonest pole: an invite for room 7 cannot be minted from a grant on
room 8 — the grantor's scope does not cover the room cell. -/
theorem invite_from_other_room_refused :
    ¬ DelegationShape inviteRequest { inviteCapability with parent := some ⟨23⟩ }
      { ownerCapability with id := ⟨23⟩, scope := { ownerScope with targets := .under 8 } }
      roomState.parent := by
  decide

/-- Dishonest pole: an invite cannot widen to the enclosing area. -/
theorem invite_cannot_widen :
    ¬ DelegationShape inviteRequest { inviteCapability with scope := roomScope 3 }
      ownerCapability roomState.parent := by
  decide

/-! ## Axiom audit -/

/-- info: 'Minidregg.Theory.TypedAuthorization.Scope.narrows_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Scope.narrows_stable
/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.attenuation_admits_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Capability.attenuation_admits_subset
/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.strict_attenuation_admits_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Capability.strict_attenuation_admits_subset
/-- info: 'Minidregg.Theory.RoomAuthorization.covers_under_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms covers_under_chain
/-- info: 'Minidregg.Theory.RoomAuthorization.covers_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms covers_cases
/-- info: 'Minidregg.Theory.RoomAuthorization.room_confidentiality' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms room_confidentiality
/-- info: 'Minidregg.Theory.RoomAuthorization.room_admission_traces_to_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms room_admission_traces_to_root
/-- info: 'Minidregg.Theory.RoomAuthorization.member_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_reads
/-- info: 'Minidregg.Theory.RoomAuthorization.member_reads_room' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_reads_room
/-- info: 'Minidregg.Theory.RoomAuthorization.area_member_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms area_member_reads
/-- info: 'Minidregg.Theory.RoomAuthorization.member_refused_on_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_refused_on_area
/-- info: 'Minidregg.Theory.RoomAuthorization.member_traces_to_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_traces_to_root
/-- info: 'Minidregg.Theory.RoomAuthorization.outsider_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outsider_refused
/-- info: 'Minidregg.Theory.RoomAuthorization.other_room_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms other_room_refused
/-- info: 'Minidregg.Theory.RoomAuthorization.other_room_refused_by_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms other_room_refused_by_check
/-- info: 'Minidregg.Theory.RoomAuthorization.explicit_new_cell_refused_before_birth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms explicit_new_cell_refused_before_birth
/-- info: 'Minidregg.Theory.RoomAuthorization.explicit_new_cell_narrows_after_birth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms explicit_new_cell_narrows_after_birth
/-- info: 'Minidregg.Theory.RoomAuthorization.explicit_room_cell_narrowing_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms explicit_room_cell_narrowing_stable
/-- info: 'Minidregg.Theory.RoomAuthorization.rewritten_parent_breaks_narrowing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rewritten_parent_breaks_narrowing
/-- info: 'Minidregg.Theory.RoomAuthorization.room_narrows_area' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms room_narrows_area
/-- info: 'Minidregg.Theory.RoomAuthorization.under_never_narrows_to_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms under_never_narrows_to_explicit
/-- info: 'Minidregg.Theory.RoomAuthorization.room_invite_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms room_invite_shape
/-- info: 'Minidregg.Theory.RoomAuthorization.invitee_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invitee_reads
/-- info: 'Minidregg.Theory.RoomAuthorization.invite_from_other_room_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invite_from_other_room_refused
/-- info: 'Minidregg.Theory.RoomAuthorization.invite_cannot_widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invite_cannot_widen

end Minidregg.Theory.RoomAuthorization
