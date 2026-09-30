/-
# Theory.RoomAuthorization — `under R` scopes and room confidentiality

A room is a cell `R`; `under R` is every cell whose parent, in the system
cell's parent projection, is `R`. A scope reaches a cell under `R` in exactly
two ways: its target set is `under R`, or it is an explicit set naming that
cell. A scope over a different room never reaches it, because a cell has one
parent.

`room_confidentiality` is the refusal form: a capability that is neither an
`under R` grant nor an explicit grant naming the cell is not admissible for
any request on it. `room_admission_traces_to_root` is the lineage form: every
admitted capability with a valid stored lineage descends from a root whose own
target set is `under R` or names the cell.
-/
import Theory.CredentialAuthorityState

namespace Minidregg.Theory.RoomAuthorization

open TypedAuthorization
open CredentialAuthorityState
open AuthorizationDeclaration

set_option autoImplicit false

/-- A cell under `room` is covered only by `under room` or by an explicit set
naming it. -/
theorem covers_under_room {kind : ResourceKind} {targets : TargetSet kind}
    {parentage : Parentage} {room : Nat} {target : ResourceId kind}
    (underRoom : parentage target.value = some room)
    (covers : targets.Covers parentage target) :
    targets = .under room ∨ ∃ ts, targets = .explicit ts ∧ target ∈ ts := by
  cases targets with
  | explicit ts => exact .inr ⟨ts, rfl, covers⟩
  | under other =>
      have recorded : parentage target.value = some other := covers
      rw [underRoom] at recorded
      exact .inl (by rw [Option.some.inj recorded])

/-- Room confidentiality. For a cell under room `R`, a capability whose target
set is not `under R` and does not explicitly name the cell is not admissible
for any request on that cell, observation included, whoever presents it. -/
theorem room_confidentiality {kind : ResourceKind} {state : AuthState}
    {room : Nat} {request : Request kind}
    (underRoom : state.parent request.target.value = some room)
    (cap : Capability kind)
    (notRoomGrant : cap.scope.targets ≠ .under room)
    (notNamed : ∀ ts, cap.scope.targets = .explicit ts → request.target ∉ ts) :
    ¬ cap.Admissible state request := by
  intro admitted
  rcases covers_under_room underRoom admitted.scope.target with same | ⟨ts, named, member⟩
  · exact notRoomGrant same
  · exact notNamed ts named member

/-- Every admitted capability with a valid lineage at the current parent
projection descends from a root (`parent = none`, `root = id`, same root id
and issuer) whose own target set is `under R` or explicitly names the cell. -/
theorem room_admission_traces_to_root {kind : ResourceKind} {state : AuthState}
    {room : Nat} {request : Request kind} {stored : StoredCapability kind}
    (valid : LineageValid state.parent stored)
    (admitted : stored.head.Admissible state request)
    (underRoom : state.parent request.target.value = some room) :
    ∃ root : Capability kind, root.parent = none ∧ root.root = root.id ∧
      stored.head.root = root.root ∧ stored.head.issuer = root.issuer ∧
      (root.scope.targets = .under room ∨
        ∃ ts, root.scope.targets = .explicit ts ∧ request.target ∈ ts) := by
  obtain ⟨root, parentNone, rootSelf, bounds⟩ := valid.root_bounds
  have covers := TargetSet.covers_of_narrows bounds.scope.targets admitted.scope.target
  exact ⟨root, parentNone, rootSelf, bounds.root, bounds.issuer,
    covers_under_room underRoom covers⟩

/-! ## Concrete poles

Cell 50 is under room 7; cell 51 is created under room 7 later; room 8 is
another room. -/

def roomParents : Parentage := fun cell => if cell = 50 then some 7 else none

def grownParents : Parentage := fun cell =>
  if cell = 50 then some 7 else if cell = 51 then some 7 else none

/-- A projection that rewrites cell 50's parent: not an append-only successor. -/
def rewrittenParents : Parentage := fun cell => if cell = 50 then some 8 else none

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

/-- An observation of cell 50 by subject 4. -/
def observeNote : Request .object :=
  { demoRequest with target := ⟨50⟩, verb := .observeObject }

def memberCapability : Capability .object :=
  { demoCapability with scope := roomScope 7 }

def otherRoomCapability : Capability .object :=
  { demoCapability with scope := roomScope 8 }

def outsiderCapability : Capability .object :=
  { demoCapability with scope := explicitScope 60 }

theorem grownState_extends_roomState :
    ∀ c p, roomState.parent c = some p → grownState.parent c = some p := by
  intro c p recorded
  simp only [roomState, grownState, roomParents, grownParents] at recorded ⊢
  split at recorded
  · simp_all
  · simp at recorded

/-- Honest pole: a holder of `under 7` reads cell 50. -/
theorem member_reads : memberCapability.Admissible roomState observeNote :=
  (capabilityAdmissibleCheck_eq_true_iff _ _ _).mp (by decide)

/-- The lineage form at the honest pole: the member's grant is itself a root
whose target set is `under 7`. -/
theorem member_traces_to_root :
    ∃ root : Capability .object, root.parent = none ∧ root.root = root.id ∧
      memberCapability.root = root.root ∧ memberCapability.issuer = root.issuer ∧
      (root.scope.targets = .under 7 ∨
        ∃ ts, root.scope.targets = .explicit ts ∧ observeNote.target ∈ ts) :=
  room_admission_traces_to_root (stored := ⟨memberCapability, []⟩)
    (.root memberCapability rfl rfl rfl) member_reads (by decide)

/-- Dishonest pole: an explicit grant on another cell is refused. -/
theorem outsider_refused : ¬ outsiderCapability.Admissible roomState observeNote :=
  room_confidentiality (room := 7) (by decide) outsiderCapability (by decide)
    (by
      intro ts named
      simp only [outsiderCapability, explicitScope, TargetSet.explicit.injEq] at named
      subst named
      decide)

/-- Dishonest pole: a holder of `under 8` is refused on a cell of room 7. -/
theorem other_room_refused : ¬ otherRoomCapability.Admissible roomState observeNote :=
  room_confidentiality (room := 7) (by decide) otherRoomCapability (by decide)
    (by
      intro ts named
      simp [otherRoomCapability, roomScope] at named)

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

/-- `under` never narrows to an explicit set, even one naming every current
child of the room. -/
theorem under_never_narrows_to_explicit :
    ¬ (roomScope 7).Narrows (explicitScope 50) grownState.parent := by
  decide

/-! ## Axiom audit -/

/-- info: 'Minidregg.Theory.TypedAuthorization.Scope.narrows_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Scope.narrows_stable
/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.attenuation_admits_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Capability.attenuation_admits_subset
/-- info: 'Minidregg.Theory.TypedAuthorization.Capability.strict_attenuation_admits_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Capability.strict_attenuation_admits_subset
/-- info: 'Minidregg.Theory.RoomAuthorization.covers_under_room' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms covers_under_room
/-- info: 'Minidregg.Theory.RoomAuthorization.room_confidentiality' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms room_confidentiality
/-- info: 'Minidregg.Theory.RoomAuthorization.room_admission_traces_to_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms room_admission_traces_to_root
/-- info: 'Minidregg.Theory.RoomAuthorization.member_reads' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_reads
/-- info: 'Minidregg.Theory.RoomAuthorization.member_traces_to_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms member_traces_to_root
/-- info: 'Minidregg.Theory.RoomAuthorization.outsider_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms outsider_refused
/-- info: 'Minidregg.Theory.RoomAuthorization.other_room_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms other_room_refused
/-- info: 'Minidregg.Theory.RoomAuthorization.other_room_refused_by_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms other_room_refused_by_check
/-- info: 'Minidregg.Theory.RoomAuthorization.explicit_new_cell_refused_before_birth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms explicit_new_cell_refused_before_birth
/-- info: 'Minidregg.Theory.RoomAuthorization.explicit_new_cell_narrows_after_birth' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms explicit_new_cell_narrows_after_birth
/-- info: 'Minidregg.Theory.RoomAuthorization.explicit_room_cell_narrowing_stable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms explicit_room_cell_narrowing_stable
/-- info: 'Minidregg.Theory.RoomAuthorization.rewritten_parent_breaks_narrowing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rewritten_parent_breaks_narrowing
/-- info: 'Minidregg.Theory.RoomAuthorization.under_never_narrows_to_explicit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms under_never_narrows_to_explicit

end Minidregg.Theory.RoomAuthorization
