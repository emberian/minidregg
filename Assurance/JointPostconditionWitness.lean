/-
# JointPostconditionWitness — disjoint writes must preserve source predicates

Two source-admitted effects set independent flags from the same `(0,0)` pre.
Each local post satisfies "at least one flag is unset", but their joint `(1,1)`
post does not. The mandatory family postcondition makes that joint impossible.
The same disjoint writes compose under the source predicate "at least one flag
is set", demonstrating that the repair neither bans disjoint operations nor
requires the whole joint state to equal every local post.

The portal, constant-root materializer and empty resource schema are explicit
existing inhabitation witnesses. This checks semantic composition, not a
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
noncomputable section

/-- The schema-owned scalar projection preserves field presence exactly. -/
def view (state : LogicalState schemaB) : Minidregg.Pred.State :=
  ⟨[("left", if (state.fields false).isSome then 1 else 0),
    ("right", if (state.fields true).isSome then 1 else 0)]⟩

inductive Rule where
  | someUnset
  | someSet
  deriving DecidableEq

/-- Both obligations are first-order source predicates, not host verdicts. -/
def Rule.predicate : Rule → Minidregg.Pred.Pred
  | .someUnset => .any [.eq "left" 0, .eq "right" 0]
  | .someSet => .any [.eq "left" 1, .eq "right" 1]

def patch (side : Bool) : Patch schemaB Digest where
  expectedPreRoot := cellB.root
  fieldFootprint := {side}
  resourceFootprint := ∅
  fieldWrites := [{ field := side, value := some () }]
  resourceWrites := []

def localPost (side : Bool) : LogicalState schemaB where
  fields := applyFieldWrites (patch side).fieldWrites cellB.logical.fields
  resources := cellB.logical.resources

def sourceRequest (rule : Rule) (side : Bool) : Request .object :=
  { requestB with
    argsDigest := ⟨match rule with | .someUnset => 100 | .someSet => 101⟩
    nonce := if side then 29 else 28 }

/-- The source predicate and exact produced patch are both mandatory at the
actual post. Neither can be dropped by erasing an application wrapper. -/
def family (rule : Rule) (side : Bool) :
    SemanticEffectFamily.{0, 0, 0, 0, 0, 0} schemaB materializerB Unit where
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
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

theorem localPolicy (rule : Rule) (side : Bool) :
    Minidregg.Pred.eval rule.predicate
      (view cellB.logical) (view (localPost side)) = true := by
  cases rule <;> cases side <;> decide

theorem patchAccepted (side : Bool) :
    Nonempty (ValidatedPatch materializerB cellB (patch side)) := by
  have witness : ∃ validated : ValidatedPatch materializerB cellB (patch side),
      validate materializerB cellB (patch side) =
        ValidationOutcome.accepted validated := by
    unfold validate
    rw [dif_pos (show (patch side).expectedPreRoot = cellB.root from rfl)]
    rw [dif_pos (show (patch side).fieldFootprint = (patch side).namedFields by
      cases side <;> decide)]
    rw [dif_pos (show (patch side).resourceFootprint = (patch side).namedResources by
      simp [patch, Patch.namedResources])]
    exact ⟨_, rfl⟩
  exact ⟨witness.choose⟩

def accepted (rule : Rule) (side : Bool) :
    AcceptedCellEffect (portal := permissivePortal) (authState := authState)
      (family rule side) (sourceRequest rule side) cellB () () where
  authorization := authorization rule side
  preStateBound := rfl
  requestBound := rfl
  effectsDigestBound := rfl
  preRootBound := rfl
  modeEvidence := ()
  validated := Classical.choice (patchAccepted side)
  postcondition := ⟨(Classical.choice (patchAccepted side)).resultAt, localPolicy rule side⟩
  disclosure := .sealed
  disclosureAllowed := rfl

def projection : AuthorizationProjection schemaB where
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
    Declaration schemaB materializerB permissivePortal projection Bool where
  pre := cellB
  apex := ⟨0⟩
  legs := leg rule
  composition := { fieldMode := .disjoint, order := [false, true] }

def law : ResourceLaw schemaB materializerB permissivePortal Unit Int where
  stateDelta := fun _ _ _ _ _ => 0

theorem shapeValid (rule : Rule) : (declaration rule).ShapeValid where
  orderComplete := ⟨by cases rule <;> decide,
    fun i => by cases rule <;> cases i <;> decide⟩
  resourcesDisjoint := by
    intro left right _
    simp [Declaration.legPatch, Leg.patch, declaration, leg, family, patch]
  fieldsValid := by
    intro left right different
    cases left <;> cases right
    · exact absurd rfl different
    · cases rule <;> decide
    · cases rule <;> decide
    · exact absurd rfl different

/-- The old admission conditions, including exact preserved writes and joint
resource conservation, all hold even for the source-incompatible joint. -/
theorem oldConditionsHold (rule : Rule) :
    (declaration rule).ShapeValid ∧
      (declaration rule).FieldOutcomesPreserved (declaration rule).jointValidated.apply ∧
      (declaration rule).jointDelta law (declaration rule).jointValidated.apply =
        (declaration rule).aggregateDelta law ∧
      (declaration rule).aggregateDelta law = 0 := by
  refine ⟨shapeValid rule, ?_, ?_, ?_⟩
  · intro side field present
    change field ∈ ({side} : Finset Bool) at present
    have same := Finset.mem_singleton.mp present
    subst field
    cases side <;> rfl
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
theorem badJointRefused : IsEmpty (Commit law (declaration .someUnset)) := by
  refine ⟨fun commit => ?_⟩
  have preserved := (commit.leg_postcondition false).2
  exact Bool.false_ne_true preserved

/-- The same nonempty disjoint writes compose under a compatible source
predicate, with every obligation checked at the actual joint post. -/
def goodCommit : Commit law (declaration .someSet) where
  shape := (oldConditionsHold .someSet).1
  validated := (declaration .someSet).jointValidated
  apexExact := rfl
  fieldsPreserved := (oldConditionsHold .someSet).2.1
  jointDeltaExact := (oldConditionsHold .someSet).2.2.1
  aggregateBalanced := (oldConditionsHold .someSet).2.2.2
  postconditions := by
    intro side
    constructor
    · constructor
      · intro field present
        change field ∈ ({side} : Finset Bool) at present
        have same := Finset.mem_singleton.mp present
        subst field
        cases side <;> rfl
      · intro resource
        exact resource.elim
    · decide

theorem goodJointInhabited : Nonempty (Commit law (declaration .someSet)) :=
  ⟨goodCommit⟩

theorem goodJointPolicyHeld :
    Minidregg.Pred.eval Rule.someSet.predicate (view cellB.logical)
      (view goodCommit.prepared.post.logical) = true :=
  (goodCommit.leg_postcondition false).2

/-- Composition remains stronger than whole-state equality: another leg
changes a field outside this leg's output. -/
theorem goodJointDiffersFromLocal :
    goodCommit.prepared.post.logical ≠
      ((declaration .someSet).legs false).post.logical := by
  intro equal
  have impossible := congrArg (fun state : LogicalState schemaB => state.fields true) equal
  exact (show (some () : Option Unit) ≠ none by decide) impossible

/-- info: 'Minidregg.Assurance.JointPostconditionWitness.badJointRefused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms badJointRefused
/-- info: 'Minidregg.Assurance.JointPostconditionWitness.goodJointInhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goodJointInhabited
/-- info: 'Minidregg.Assurance.JointPostconditionWitness.goodJointDiffersFromLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms goodJointDiffersFromLocal

end
end Minidregg.Assurance.JointPostconditionWitness
