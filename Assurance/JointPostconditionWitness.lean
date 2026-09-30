/-
# JointPostconditionWitness — disjoint writes must preserve source predicates

Two source-admitted effects set independent flags from the same `(0,0)` pre.
Each local post satisfies "at least one flag is unset", but their joint `(1,1)`
post does not. The mandatory family postcondition makes that joint impossible.
The same disjoint writes compose under the source predicate "at least one flag
is set", demonstrating that the repair neither bans disjoint operations nor
requires the whole joint state to equal every local post.

The portal and the presence-bitmask witness layout are explicit existing
inhabitation witnesses. This checks semantic composition, not a
deployed signature verifier, cryptographic commitment or physical settlement.
-/
import Kernel.TypedCellHyperedge
import Theory.AcceptedCellEffectWitness
import Pred.Core

namespace Minidregg.Assurance.JointPostconditionWitness

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellStateWitness
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.TypedAuthorizationWitness
open Minidregg.Kernel.TypedCellHyperedge

set_option autoImplicit false

/-- The layout-owned scalar projection preserves address presence exactly. -/
def view (state : Store.Store layoutB) : Minidregg.Pred.State :=
  ⟨[("left", if (state (addressB false)).isSome then 1 else 0),
    ("right", if (state (addressB true)).isSome then 1 else 0)]⟩

inductive Rule where
  | someUnset
  | someSet
  deriving DecidableEq

/-- Both obligations are first-order source predicates, not host verdicts. -/
def Rule.predicate : Rule → Minidregg.Pred.Pred
  | .someUnset => .any [.eq "left" 0, .eq "right" 0]
  | .someSet => .any [.eq "left" 1, .eq "right" 1]

/-- Set one flag: allocate its (absent) address. -/
def patch (side : Bool) : Store.Patch layoutB := [@Store.Op.allocate layoutB () side ()]

def localPost (side : Bool) : Store.Store layoutB :=
  Store.Patch.run cellB.logical (patch side)

def sourceRequest (rule : Rule) (side : Bool) : Request .object :=
  { requestB with
    argsDigest := ⟨match rule with | .someUnset => 100 | .someSet => 101⟩
    nonce := if side then 29 else 28 }

/-- The source predicate and exact produced patch are both mandatory at the
actual post. Neither can be dropped by erasing an application wrapper. -/
def family (rule : Rule) (side : Bool) :
    SemanticEffectFamily.{0, 0, 0, 0, 0} layoutB materializerB Unit where
  Declaration := Unit
  declarationCodec := AcceptedCellEffectWitness.unitCodec
  pre := cellB
  request := fun _ => ⟨.object, sourceRequest rule side⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => AcceptedCellEffectWitness.unitCodec
  ModeEvidence := fun _ _ => Unit
  Postcondition := fun _ _ post =>
    (patch side).ResultAt cellB.logical post ∧
      Minidregg.Pred.eval rule.predicate (view cellB.logical) (view post) = true
  effectDigest := fun _ => requestB.effectsDigest
  patch := fun _ _ => patch side
  nullifier := fun _ _ => none
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => release.elim
  DisclosureAllowed := fun _ _ decision => decision = .sealed

def authorization (rule : Rule) (side : Bool) :
    Authorized permissivePortal authState (sourceRequest rule side) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyRevisionExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

theorem localPolicy (rule : Rule) (side : Bool) :
    Minidregg.Pred.eval rule.predicate
      (view cellB.logical) (view (localPost side)) = true := by
  cases rule <;> cases side <;> decide

theorem patchAccepted (rule : Rule) (side : Bool) :
    ValidatedPatch materializerB cellB (sourceRequest rule side).preStateRoot (patch side) := by
  obtain ⟨validated, _⟩ := validate_accepts materializerB cellB
    (sourceRequest rule side).preStateRoot (patch side)
    (show requestB.preStateRoot = cellB.root by decide)
    (by cases side <;> decide)
  exact validated

def accepted (rule : Rule) (side : Bool) :
    AcceptedCellEffect (portal := permissivePortal) (authState := authState)
      (family rule side) (sourceRequest rule side) cellB () () where
  authorization := authorization rule side
  preStateBound := rfl
  requestBound := rfl
  effectsDigestBound := rfl
  modeEvidence := ()
  validated := patchAccepted rule side
  postcondition := ⟨(patchAccepted rule side).resultAt, localPolicy rule side⟩
  disclosure := .sealed
  disclosureAllowed := rfl

def projection : AuthorizationProjection layoutB where
  project := fun _ => authState

def leg (rule : Rule) (side : Bool) : Leg permissivePortal authState cellB where
  Nullifier := Unit
  family := family rule side
  kind := .object
  request := sourceRequest rule side
  declaration := ()
  outcome := ()
  accepted := accepted rule side

def declaration (rule : Rule) :
    Declaration layoutB materializerB permissivePortal projection Bool where
  pre := cellB
  apex := ⟨3⟩
  legs := leg rule
  composition := { mode := .disjoint, order := [false, true] }

def law : ResourceLaw layoutB materializerB permissivePortal Unit Int where
  stateDelta := fun _ _ _ _ => 0

theorem jointPatch_eq (rule : Rule) :
    (declaration rule).jointPatch = patch false ++ patch true := rfl

theorem shapeValid (rule : Rule) : (declaration rule).ShapeValid where
  orderComplete := ⟨by cases rule <;> decide,
    fun i => by cases rule <;> cases i <;> decide⟩
  modeValid := by
    intro left right different
    cases left <;> cases right
    · exact absurd rfl different
    · cases rule <;> decide
    · cases rule <;> decide
    · exact absurd rfl different

/-- The joint patch (both allocations) validates at the common pre-root. -/
theorem jointValidated (rule : Rule) :
    ValidatedPatch materializerB cellB cellB.root (declaration rule).jointPatch := by
  obtain ⟨validated, _⟩ := validate_accepts materializerB cellB cellB.root
    (declaration rule).jointPatch rfl (by rw [jointPatch_eq]; decide)
  exact validated

/-- The joint post sets both flags. -/
theorem joint_post (rule : Rule) :
    Store.Patch.run cellB.logical (declaration rule).jointPatch = stateB (true, true) := by
  rw [jointPatch_eq]
  decide

/-- The old admission conditions, including exact preserved writes and joint
resource conservation, all hold even for the source-incompatible joint. -/
theorem oldConditionsHold (rule : Rule) :
    (declaration rule).ShapeValid ∧
      (declaration rule).OutcomesPreserved (jointValidated rule).apply ∧
      (declaration rule).jointDelta law (jointValidated rule).apply =
        (declaration rule).aggregateDelta law ∧
      (declaration rule).aggregateDelta law = 0 := by
  refine ⟨shapeValid rule, ?_, ?_, ?_⟩
  · intro side address present
    obtain ⟨op, member, writes⟩ := (Store.Patch.mem_writeFootprint_iff _ address).mp present
    change op ∈ patch side at member
    simp only [patch, List.mem_singleton] at member
    subst member
    simp only [Store.Op.writeAddress?, Store.Op.address, Option.some.injEq] at writes
    subst writes
    change Store.Patch.run cellB.logical (declaration rule).jointPatch ⟨(), side⟩ =
      Store.Patch.run cellB.logical (patch side) ⟨(), side⟩
    rw [jointPatch_eq]
    cases side <;> decide
  · funext coordinate
    simp [Declaration.jointDelta, Declaration.aggregateDelta, ResourceLaw.delta, law]
  · funext coordinate
    simp [Declaration.aggregateDelta, ResourceLaw.delta, law]

/-- Every local accepted token satisfies the very predicate that its bad
joint would violate. Refusal is not hidden in missing local evidence. -/
theorem everyLocalPolicyHeld (rule : Rule) (side : Bool) :
    Minidregg.Pred.eval rule.predicate (view cellB.logical)
      (view (((declaration rule).legs side).post.logical)) = true :=
  (accepted rule side).postcondition.2

/-- No generic accepted joint can erase the source's cross-field invariant. -/
theorem badJointRefused : ¬ Commit law (declaration .someUnset) := by
  intro commit
  have preserved := (commit.leg_postcondition false).2
  change Minidregg.Pred.eval Rule.someUnset.predicate (view cellB.logical)
    (view (Store.Patch.run cellB.logical (declaration .someUnset).jointPatch)) = true
    at preserved
  rw [joint_post] at preserved
  exact absurd preserved (by decide)

/-- The same nonempty disjoint writes compose under a compatible source
predicate, with every obligation checked at the actual joint post. -/
theorem goodCommit : Commit law (declaration .someSet) where
  shape := (oldConditionsHold .someSet).1
  validated := jointValidated .someSet
  apexExact := by decide
  outcomesPreserved := (oldConditionsHold .someSet).2.1
  jointDeltaExact := (oldConditionsHold .someSet).2.2.1
  aggregateBalanced := (oldConditionsHold .someSet).2.2.2
  postconditions := by
    intro side
    constructor
    · intro address present
      obtain ⟨op, member, writes⟩ := (Store.Patch.mem_writeFootprint_iff _ address).mp present
      change op ∈ patch side at member
      simp only [patch, List.mem_singleton] at member
      subst member
      simp only [Store.Op.writeAddress?, Store.Op.address, Option.some.injEq] at writes
      subst writes
      change Store.Patch.run cellB.logical (declaration .someSet).jointPatch ⟨(), side⟩ =
        Store.Patch.run cellB.logical (patch side) ⟨(), side⟩
      rw [jointPatch_eq]
      cases side <;> decide
    · change Minidregg.Pred.eval Rule.someSet.predicate (view cellB.logical)
        (view (Store.Patch.run cellB.logical (declaration .someSet).jointPatch)) = true
      rw [joint_post]
      decide

theorem goodJointPolicyHeld :
    Minidregg.Pred.eval Rule.someSet.predicate (view cellB.logical)
      (view (Store.Patch.run cellB.logical (declaration .someSet).jointPatch)) = true :=
  (goodCommit.leg_postcondition false).2

/-- Composition remains stronger than whole-state equality: another leg
changes an address outside this leg's output. -/
theorem goodJointDiffersFromLocal :
    Store.Patch.run cellB.logical (declaration .someSet).jointPatch ≠
      ((declaration .someSet).legs false).post.logical := by
  intro equal
  have impossible := congrArg (fun state : Store.Store layoutB => state (addressB true)) equal
  change Store.Patch.run cellB.logical (declaration .someSet).jointPatch (addressB true) =
    Store.Patch.run cellB.logical (patch false) (addressB true) at impossible
  rw [jointPatch_eq] at impossible
  exact absurd impossible (by decide)

/-- info: 'Minidregg.Assurance.JointPostconditionWitness.badJointRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms badJointRefused
/-- info: 'Minidregg.Assurance.JointPostconditionWitness.goodCommit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goodCommit
/-- info: 'Minidregg.Assurance.JointPostconditionWitness.goodJointDiffersFromLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goodJointDiffersFromLocal

end Minidregg.Assurance.JointPostconditionWitness
