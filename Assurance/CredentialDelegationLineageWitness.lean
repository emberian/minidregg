/-
# Mixed stored lineage: constructive shape and anchoring witnesses

These statements exercise the shared semantic checker. They do not claim an
IO signature or an authorized historical issuance from a serialized origin.
Actual issuance is the mandatory accepted delegation mode's obligation.
-/
import Theory.CredentialLineageAdmission

namespace Minidregg.Assurance.CredentialDelegationLineageWitness

open Minidregg.Theory
open CellState TypedAuthorization CredentialAuthorityFamily
open CredentialAuthorityState CredentialLineageAdmission

set_option autoImplicit false

def alice : SubjectId := ⟨1⟩
def bob : SubjectId := ⟨2⟩

def parent : Capability .object where
  id := ⟨100⟩
  root := ⟨100⟩
  parent := none
  issuer := ⟨70⟩
  holder := .subject alice
  scope := ⟨{⟨200⟩, ⟨201⟩}, {.observeObject, .mutateObject, .delegateObject}, 100⟩
  notBefore := 0
  notAfter := 100
  issuerEpoch := 0
  policyId := ⟨8⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def child : Capability .object :=
  { parent with
    id := ⟨101⟩
    parent := some parent.id
    holder := .subject bob
    scope := ⟨{⟨200⟩}, {.observeObject, .mutateObject}, 20⟩
    notBefore := 1
    notAfter := 80
    ancestors := {parent.id} }

def request : Request .object where
  domain := ⟨1⟩
  semantics := ⟨2⟩
  federation := ⟨3⟩
  subject := alice
  subjectKeyEpoch := 0
  target := ⟨200⟩
  verb := .delegateObject
  argsDigest := ⟨4⟩
  effectsDigest := ⟨5⟩
  nonce := 44
  height := 10
  preStateRoot := ⟨6⟩
  policyId := parent.policyId
  policyEpoch := 0
  policyRevision := 0
  cost := 3

def parentStored : StoredCapability .object := ⟨parent, []⟩
def delegatedStored : StoredCapability .object :=
  ⟨child, [⟨parent, .delegated request⟩]⟩
def unmarkedStored : StoredCapability .object :=
  ⟨child, [⟨parent, .strict⟩]⟩
def strictStored : StoredCapability .object :=
  ⟨{child with holder := .subject alice}, [⟨parent, .strict⟩]⟩

def logical : LogicalState schema where
  fields := ((0 : FieldStore schema).write (.capability .object parent.id) parentStored).write
    (.capability .object child.id) delegatedStored
  resources := fun resource => nomatch resource

def pre (M : Materializer) : Cell M := materialize M logical

theorem parent_present (M : Materializer) :
    readCapability (pre M) .object parent.id = some parentStored := by
  change (((0 : FieldStore schema).write (.capability .object parent.id) parentStored).write
    (.capability .object child.id) delegatedStored) (.capability .object parent.id) =
      some parentStored
  rw [FieldStore.write_other _
    (show AuthorityField.capability .object child.id ≠ .capability .object parent.id by decide)]
  exact FieldStore.write_self _ _ _

theorem explicit_transfer_shape : DelegationShape request child parent := by decide

theorem explicit_transfer_valid : LineageValid delegatedStored :=
  .delegate child parent [] request (.root parent rfl rfl rfl) explicit_transfer_shape

theorem explicit_transfer_anchored (M : Materializer) :
    LineageAnchored (pre M) delegatedStored :=
  LineageAnchored.cons child parent [] (.delegated request) (parent_present M) trivial

theorem explicit_transfer_accepted (M : Materializer) :
    storedLineageCheck (pre M) delegatedStored = true :=
  (storedLineageCheck_iff (pre M) delegatedStored).mpr
    ⟨explicit_transfer_valid, explicit_transfer_anchored M⟩

def rotatedPre (M : Materializer) : Cell M :=
  materialize M {logical with fields := logical.fields.write (.subjectKeyEpoch alice) (show Epoch from 1)}

theorem grantor_rotation_preserves_capability_reads (M : Materializer)
    (kind : ResourceKind) (identifier : CapabilityId) :
    readCapability (pre M) kind identifier =
      readCapability (rotatedPre M) kind identifier := by
  simp [pre, rotatedPre, readCapability, materialize]

theorem grantor_rotation_keeps_historical_lineage (M : Materializer) :
    storedLineageCheck (rotatedPre M) delegatedStored = true := by
  rw [← storedLineageCheck_congr (pre M) (rotatedPre M)
    (grantor_rotation_preserves_capability_reads M)]
  exact explicit_transfer_accepted M

theorem strict_same_holder_accepted (M : Materializer) :
    storedLineageCheck (pre M) strictStored = true := by
  apply (storedLineageCheck_iff (pre M) strictStored).mpr
  refine ⟨?_, ?_⟩
  · exact .attenuate _ parent [] (.root parent rfl rfl rfl) (by decide)
  · exact LineageAnchored.cons _ parent [] .strict (parent_present M) trivial

theorem unmarked_transfer_refused (M : Materializer) :
    storedLineageCheck (pre M) unmarkedStored = false := by
  change (false && _) = false
  rfl

def noDelegateParent : Capability .object :=
  {parent with scope := {parent.scope with verbs := {.observeObject, .mutateObject}}}

theorem absent_delegation_permission_refused :
    delegationShapeCheck request child noDelegateParent = false :=
  delegationShapeCheck_refuses_missing_delegate request child noDelegateParent (by decide)

theorem bearer_transfer_refused :
    delegationShapeCheck request {child with holder := .bearer} parent = false :=
  delegationShapeCheck_refuses_bearer request _ parent rfl

def substitutedParent : Capability .object := {parent with notAfter := 99}
def substitutedStored : StoredCapability .object :=
  ⟨child, [⟨substitutedParent, .delegated request⟩]⟩

theorem substituted_parent_still_well_shaped : LineageValid substitutedStored :=
  .delegate child substitutedParent [] request (.root substitutedParent rfl rfl rfl) (by decide)

theorem substituted_parent_refused (M : Materializer) :
    storedLineageCheck (pre M) substitutedStored = false := by
  apply storedLineageCheck_refuses_unanchored
  intro anchored
  have exactParent := anchored.parent_exact
  change readCapability (pre M) .object parent.id = some ⟨substitutedParent, []⟩ at exactParent
  rw [parent_present M] at exactParent
  have equal := congrArg (fun stored : StoredCapability .object => stored.head.notAfter)
    (Option.some.inj exactParent)
  change 100 = 99 at equal
  contradiction

def emptyPre (M : Materializer) : Cell M :=
  materialize M ⟨0, fun resource => nomatch resource⟩

theorem orphaned_transfer_refused (M : Materializer) :
    storedLineageCheck (emptyPre M) delegatedStored = false := by
  apply storedLineageCheck_refuses_unanchored
  intro anchored
  have exactParent := anchored.parent_exact
  change none = some parentStored at exactParent
  contradiction

def recipientRequest : Request .object :=
  {request with subject := bob, verb := .mutateObject}

def state : AuthState where
  capabilityRoot := ⟨10⟩
  revocationRoot := ⟨10⟩
  policyRoot := ⟨10⟩
  policyAddress := fun _ _ => ⟨11⟩
  revoked := ∅
  issuerEpoch := fun _ => 0
  policyEpoch := fun _ => 0
  policyRevision := fun _ => 0
  subjectKeyEpoch := fun _ => 0

theorem recipient_semantically_admitted : child.Admissible state recipientRequest :=
  (AuthorizationDeclaration.capabilityAdmissibleCheck_eq_true_iff _ _ _).mp (by decide)

/-- The old unconditional root-admission claim is false after an authorized
subject transfer. The strict-only theorem remains the correct statement. -/
theorem mixed_lineage_does_not_imply_root_admission :
    LineageValid delegatedStored ∧ child.Admissible state recipientRequest ∧
      ¬parent.Admissible state recipientRequest := by
  refine ⟨explicit_transfer_valid, recipient_semantically_admitted, ?_⟩
  intro admitted
  have holder := admitted.holder
  change alice = bob at holder
  cases holder

end Minidregg.Assurance.CredentialDelegationLineageWitness
