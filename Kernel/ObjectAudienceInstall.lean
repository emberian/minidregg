/- Source-owned audience phase and exact catalog preimage checks shared by the
policy installer. It proves no package handout: fresh disclosure remains the
all-holder exact-post admission's obligation. -/
import Kernel.ObjectAudienceController
import Kernel.AudienceRosterBinding
import Compiler.ResourceTargetAdmission
namespace Minidregg.Kernel.ObjectAudienceInstall
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
inductive Reject where
  | audienceTransition
  | audienceObjectUnavailable
  deriving DecidableEq, Repr
private def require (condition : Prop) [Decidable condition] (reason : Reject) :
    Except Reject (PLift condition) :=
  if accepted : condition then .ok ⟨accepted⟩ else .error reason
private def fromOption {A : Type} (value : Option A) (reason : Reject) : Except Reject A :=
  match value with | none => .error reason | some value => .ok value

/-- Added audience dependencies are derived from the same authenticated
physical image as the policy installer. The constructor stays inside this module. -/
def NeedsWitness (before after : Option Minidregg.Theory.ObjectAudience.State) : Prop :=
  match before, after with
  | none, some _ => True
  | some old, some next => old.mode = .frozen ∧ next.mode = .active
  | _, _ => False
instance (b a : Option Minidregg.Theory.ObjectAudience.State) : Decidable (NeedsWitness b a) := by
  cases b <;> cases a <;> unfold NeedsWitness <;> infer_instance

def SupportedObject {durable : Durable} (deployment : Deployment)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable) (object : Nat) : Prop :=
  match directory.directory.slots object with
  | .absent => False
  | .present cell => CanonicalCellRegistry.CellLaw deployment object cell ∧
      ResourceTargetAdmission.externalKind cell.kind = some .object
instance {durable : Durable} (deployment : Deployment) (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (object : Nat) : Decidable (SupportedObject deployment directory object) := by
  unfold SupportedObject; split <;> infer_instance

def objectMetadataRequired (before after : PolicyRecord) : Bool :=
  before.audience.isSome || after.audience.isSome ||
    before.objectDescriptor.isSome || after.objectDescriptor.isSome

structure Prepared (deployment : Deployment) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (object : Nat) (before after : Option Minidregg.Theory.ObjectAudience.State)
    (metadataRequired : Bool) where
  private mk ::
  deviceRoot : Nat
  bound : ObjectAudienceController.Bound object authority.snapshot.cell.root.value deviceRoot before after
  readGuards : List ReadGuard
  readGuardsExact : ∀ guard ∈ readGuards,
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId
  witness : NeedsWitness before after → ∃ next bytes,
    after = some next ∧ ∃ checked : AudienceRosterBinding.CheckedBytes (Minidregg.Compiler.ServedBasis.Ground.full _ directory authority) next bytes,
      checked.checked.deviceGuard ∈ readGuards ∧ deviceRoot = checked.checked.deviceRoot
  supported : metadataRequired = true → SupportedObject deployment directory object
  guarded : metadataRequired = true →
    (⟨⟨object⟩, durable.snapshot.model.roots ⟨object⟩⟩ : ReadGuard) ∈ readGuards

def prepare (deployment : Deployment) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (object : Nat) (before after : Option Minidregg.Theory.ObjectAudience.State)
    (rosterBytes : Option (List UInt8)) (metadataRequired : Bool) :
    Except Reject (Prepared deployment durable directory authority object before after metadataRequired) := do
  if ordinary : before = none ∧ after = none ∧ metadataRequired = false then
    if rosterBytes.isSome then throw .audienceTransition
    pure ⟨0, (by simp [ordinary.1, ordinary.2.1, ObjectAudienceController.Bound, ObjectAudienceController.Valid]),
      [], (by intro guard member; cases member),
      (by intro impossible; simp [NeedsWitness, ordinary.1, ordinary.2.1] at impossible),
      (by intro required; simp [ordinary.2.2] at required),
      (by intro required; simp [ordinary.2.2] at required)⟩
  else
    let supported ← require (SupportedObject deployment directory object) .audienceObjectUnavailable
    let objectGuard : ReadGuard := ⟨⟨object⟩, durable.snapshot.model.roots ⟨object⟩⟩
    if activation : NeedsWitness before after then
      match afterExact : after with
      | none => throw .audienceTransition
      | some next =>
        let bytes ← fromOption rosterBytes .audienceTransition
        let roster ← fromOption (AudienceRosterBinding.checkBytes (Minidregg.Compiler.ServedBasis.Ground.full _ directory authority) next bytes) .audienceTransition
        let checked ← require (ObjectAudienceController.Bound object
          authority.snapshot.cell.root.value roster.checked.deviceRoot before after) .audienceTransition
        pure ⟨roster.checked.deviceRoot, (by simpa only [afterExact] using checked.down),
          [objectGuard, roster.checked.deviceGuard], (by
            intro guard member
            simp only [List.mem_cons] at member
            rcases member with equal | equal
            · subst guard; rfl
            · rcases equal with equal | impossible
              · subst guard; exact roster.checked.deviceGuard_exact
              · cases impossible),
          (by intro _; exact ⟨next, bytes, rfl, roster, by simp, rfl⟩),
          (by intro _; exact supported.down),
          (by intro _; simp [objectGuard])⟩
    else
      if rosterBytes.isSome then throw .audienceTransition
      let deviceRoot := match after with | some state => state.deviceSnapshot | none => 0
      let checked ← require (ObjectAudienceController.Bound object
        authority.snapshot.cell.root.value deviceRoot before after) .audienceTransition
      pure ⟨deviceRoot, checked.down,
        [objectGuard], (by intro guard member; simp only [List.mem_singleton] at member; subst guard; rfl),
        (by intro needed; exact False.elim (activation needed)),
        (by intro _; exact supported.down),
        (by intro _; simp [objectGuard])⟩

end Minidregg.Kernel.ObjectAudienceInstall
