/- Explicit inherited export restrictions on the exact signed initial effect.
The old factory law remains the authorizer. A newborn's own local component is
not an export root and is never self-evaluated by this gate. -/
import Compiler.PhysicalLawResolution
import Compiler.WorldKindLawDependencies
import Compiler.CanonicalRuntimeProfile
import Kernel.WorldKindProjection
import Kernel.ContentResource
import Kernel.DeclaredResourceProjection
import Kernel.ClockCellDomain

namespace Minidregg.Kernel.BirthExportAdmission

open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.LawComposition
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes

/-- The receiving runtime must bind this projection contract in its v6 semantics. -/
def projectionContract : List UInt8 := Minidregg.Theory.LawComposition.birthProjectionContract

def roots (item : BirthItem Registry) (dependencies : WorldKindLawDependencies.Dependencies) :
    List PolicyRef :=
  (item.parent.toList.map fun parent => ⟨⟨parent⟩, .descendants, .head⟩) ++ dependencies.additional

/-- Only the exact signed BirthItem selects this view. World instances begin
with an empty inner store under the same immutable descriptor. -/
def initialEffect (subject : SubjectId) (target : Nat) : (kind : CanonicalCellRegistry.Kind) →
    Store (CanonicalCellRegistry.layout kind) → List (String × Int)
  | .worldInstance, initial => WorldKindProjection.birthProject subject initial
  | .worldKind, initial => WorldKindProjection.definitionProject 0 initial
  | .content, initial => ContentResource.project 0 initial ⟨[]⟩
  | .declaredObject, initial | .accountMetadata, initial | .declaredProgram, initial =>
      DeclaredResourceProjection.project target 0 initial
  | _, _ => []

/-- Factory request slots are unchanged. Newborn coordinates have their own
source-owned namespace; no fabricated newborn request replaces the signed one. -/
def view (pins : FactoryPins) (oldAuthority : AuthState) (factoryRoot : Digest)
    (height : Height) (descriptor : Descriptor Registry) (clock : ClockCell.Clock)
    (item : BirthItem Registry) (after : Bool) : Minidregg.Pred.State :=
  let request := factoryRequest pins CanonicalCellRegistry.sourceEncoding oldAuthority factoryRoot height descriptor
  ⟨ClockCell.slots clock ++
    [("target/storageKind", Int.ofNat item.create.cell.kind.tag.toNat),
     ("birth/target", Int.ofNat item.create.cellId),
     ("birth/owner", Int.ofNat item.owner.value),
     ("birth/resourceKind", Int.ofNat (CanonicalRuntimeProfile.requestKindTag item.resourceKind)),
     ("birth/parent-present", if item.parent.isSome then 1 else 0)] ++
    (item.parent.toList.map fun parent => ("birth/parent", Int.ofNat parent)) ++
    CanonicalRuntimeProfile.requestSlots request ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      (if after then item.create.cell.payload.bytes else []) ++
    initialEffect descriptor.creator item.create.cellId item.create.cell.kind
      item.create.cell.payload.logical⟩

variable {F : Type} [Field F]

structure ItemChecked (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (factoryRoot : Digest) (height : Height) (descriptor : Descriptor Registry)
    (clock : ClockCell.Clock) (item : BirthItem Registry) where
  private mk ::
  dependencies : WorldKindLawDependencies.Dependencies
  dependenciesExact : WorldKindLawDependencies.loadBirth deployment directory.directory item =
    some dependencies
  law : PhysicalLawResolution.GuardedRoots authority.snapshot directory.directory profile.semantics
    (roots item dependencies)
  witness : CompiledPolicyWitness F
  addressExact : witness.address = ComposedPolicyAdmission.closureDigest law.graph.resolved
  oldExact : witness.oldState = view pins authority.snapshot.authState factoryRoot height descriptor clock item false
  newExact : witness.newState = view pins authority.snapshot.authState factoryRoot height descriptor clock item true
  accepted : ∃ equality : DecidableEq F,
    @compiledLawAccepts F _ equality profile (ResolvedLawCompilation.predicate law.graph.resolved) witness = true

def checkItem [DecidableEq F] (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (factoryRoot : Digest) (height : Height) (descriptor : Descriptor Registry)
    (clock : ClockCell.Clock) (item : BirthItem Registry) :
    Option (ItemChecked profile deployment pins durable directory authority factoryRoot height descriptor clock item) := do
  match dependenciesExact : WorldKindLawDependencies.loadBirth deployment directory.directory item with
  | none => none
  | some dependencies => do
      let law ← PhysicalLawResolution.loadRoots authority.snapshot directory.directory profile.semantics
        (roots item dependencies) PhysicalLawResolution.resolutionBudget
      let witness := ResolvedLawCompilation.witness profile.compiler law.graph.resolved
        (ComposedPolicyAdmission.closureDigest law.graph.resolved)
        (view pins authority.snapshot.authState factoryRoot height descriptor clock item false)
        (view pins authority.snapshot.authState factoryRoot height descriptor clock item true)
      if accepted : compiledLawAccepts profile (ResolvedLawCompilation.predicate law.graph.resolved) witness = true then
        some ⟨dependencies, dependenciesExact, law, witness, rfl, rfl, rfl, inferInstance, accepted⟩
      else none

/-- A dependent list retains one checked graph and compiled witness for every
exact item in the signed descriptor, including duplicate entries later refused
by the existing allocator. -/
inductive ItemsChecked (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (factoryRoot : Digest) (height : Height) (descriptor : Descriptor Registry)
    (clock : ClockCell.Clock) : List (BirthItem Registry) → Type
  | nil : ItemsChecked profile deployment pins durable directory authority factoryRoot height descriptor clock []
  | cons {item rest} :
      ItemChecked profile deployment pins durable directory authority factoryRoot height descriptor clock item →
      ItemsChecked profile deployment pins durable directory authority factoryRoot height descriptor clock rest →
      ItemsChecked profile deployment pins durable directory authority factoryRoot height descriptor clock (item :: rest)

def checkItems [DecidableEq F] (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (factoryRoot : Digest) (height : Height) (descriptor : Descriptor Registry)
    (clock : ClockCell.Clock) : (items : List (BirthItem Registry)) →
    Option (ItemsChecked profile deployment pins durable directory authority factoryRoot height descriptor clock items)
  | [] => some .nil
  | item :: rest => do
      let head ← checkItem profile deployment pins durable directory authority factoryRoot height descriptor clock item
      let tail ← checkItems profile deployment pins durable directory authority factoryRoot height descriptor clock rest
      some (.cons head tail)

theorem ItemsChecked.item {profile : PolicyCompilerProfile F} {deployment : Deployment}
    {pins : FactoryPins} {durable : Durable}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {factoryRoot : Digest} {height : Height} {descriptor : Descriptor Registry}
    {clock : ClockCell.Clock} {items : List (BirthItem Registry)}
    (checked : ItemsChecked profile deployment pins durable directory authority factoryRoot height descriptor clock items)
    {item : BirthItem Registry} (member : item ∈ items) :
    Nonempty (ItemChecked profile deployment pins durable directory authority factoryRoot height descriptor clock item) := by
  induction checked with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | rest
      · subst item
        exact ⟨head⟩
      · exact ih rest

def ItemsChecked.guards {profile : PolicyCompilerProfile F} {deployment : Deployment}
    {pins : FactoryPins} {durable : Durable}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {factoryRoot : Digest} {height : Height} {descriptor : Descriptor Registry}
    {clock : ClockCell.Clock} {items : List (BirthItem Registry)} :
    ItemsChecked profile deployment pins durable directory authority factoryRoot height descriptor clock items → List ReadGuard
  | .nil => []
  | .cons head tail =>
      ((head.law.sourceGuards ++ head.dependencies.readGuards).map fun pair => ⟨⟨pair.1⟩, pair.2⟩) ++
      -- Source heads/parentage are guarded by the authority receiver. Keep
      -- lifecycle observations of every selected policy resource too.
      (head.law.graph.sources.map fun node =>
        let id := node.source.key.policyId.value
        ⟨⟨id⟩, durable.snapshot.model.roots ⟨id⟩⟩) ++ tail.guards

structure Evaluated (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (factoryRoot : Digest) (height : Height) (descriptor : Descriptor Registry) where
  private mk ::
  clock : ClockCellDomain.Loaded deployment durable.snapshot
  items : ItemsChecked profile deployment pins durable directory authority factoryRoot height descriptor clock.clock descriptor.births
  guardsExact : ∀ guard ∈ clock.readGuard :: items.guards,
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId

def Evaluated.readGuards {profile : PolicyCompilerProfile F} {deployment : Deployment}
    {pins : FactoryPins} {durable : Durable}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {factoryRoot : Digest} {height : Height} {descriptor : Descriptor Registry}
    (checked : Evaluated profile deployment pins durable directory authority factoryRoot height descriptor) : List ReadGuard :=
  checked.clock.readGuard :: checked.items.guards

def checkEvaluated [DecidableEq F] (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (factoryRoot : Digest) (height : Height) (descriptor : Descriptor Registry) :
    Option (Evaluated profile deployment pins durable directory authority factoryRoot height descriptor) := do
  let clock ← ClockCellDomain.load deployment durable.snapshot
  let items ← checkItems profile deployment pins durable directory authority factoryRoot height descriptor clock.clock descriptor.births
  if exact : ∀ guard ∈ clock.readGuard :: items.guards,
      guard.expectedRoot = durable.snapshot.model.roots guard.cellId then
    some ⟨clock, items, exact⟩
  else none

/-- A clockless neutral birth is justified by actual structural resolution,
not by guessing that a missing export body or inaccessible source means true. -/
structure NeutralItem (deployment : Deployment)
    (directory : CellRegistry.Directory Nat Registry) (item : BirthItem Registry) where
  private mk ::
  dependencies : WorldKindLawDependencies.Dependencies
  dependenciesExact : WorldKindLawDependencies.loadBirth deployment directory item = some dependencies
  rootsEmpty : roots item dependencies = []

inductive NeutralItems (deployment : Deployment)
    (directory : CellRegistry.Directory Nat Registry) : List (BirthItem Registry) → Type
  | nil : NeutralItems deployment directory []
  | cons {item rest} : NeutralItem deployment directory item →
      NeutralItems deployment directory rest → NeutralItems deployment directory (item :: rest)

def checkNeutralItems (deployment : Deployment) (directory : CellRegistry.Directory Nat Registry) :
    (items : List (BirthItem Registry)) → Option (NeutralItems deployment directory items)
  | [] => some .nil
  | item :: rest => do
      match exact : WorldKindLawDependencies.loadBirth deployment directory item with
      | none => none
      | some dependencies =>
          if empty : roots item dependencies = [] then do
            let tail ← checkNeutralItems deployment directory rest
            some (.cons ⟨dependencies, exact, empty⟩ tail)
          else none

def NeutralItems.guards {deployment : Deployment} {directory : CellRegistry.Directory Nat Registry}
    {items : List (BirthItem Registry)} : NeutralItems deployment directory items → List ReadGuard
  | .nil => []
  | .cons head tail =>
      (head.dependencies.readGuards.map fun pair => ⟨⟨pair.1⟩, pair.2⟩) ++ tail.guards

structure Neutral (deployment : Deployment) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (descriptor : Descriptor Registry) where
  private mk ::
  items : NeutralItems deployment directory.directory descriptor.births
  guardsExact : ∀ guard ∈ items.guards,
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId

def checkNeutral (deployment : Deployment) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (descriptor : Descriptor Registry) : Option (Neutral deployment durable directory descriptor) := do
  let items ← checkNeutralItems deployment directory.directory descriptor.births
  if exact : ∀ guard ∈ items.guards,
      guard.expectedRoot = durable.snapshot.model.roots guard.cellId then
    some ⟨items, exact⟩
  else none

/-- The empty-root branch preserves clockless bootstrap. Any actual root,
including a neutral local export whose ancestors still apply, takes the
fully evaluated branch and therefore observes the deployment's actual clock. -/
inductive Checked (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (factoryRoot : Digest) (height : Height) (descriptor : Descriptor Registry)
  | neutral : Neutral deployment durable directory descriptor →
      Checked profile deployment pins durable directory authority factoryRoot height descriptor
  | evaluated : Evaluated profile deployment pins durable directory authority factoryRoot height descriptor →
      Checked profile deployment pins durable directory authority factoryRoot height descriptor

def Checked.readGuards {profile : PolicyCompilerProfile F} {deployment : Deployment}
    {pins : FactoryPins} {durable : Durable}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {factoryRoot : Digest} {height : Height} {descriptor : Descriptor Registry} :
    Checked profile deployment pins durable directory authority factoryRoot height descriptor → List ReadGuard
  | .neutral checked => checked.items.guards
  | .evaluated checked => checked.readGuards

theorem Checked.guardsExact {profile : PolicyCompilerProfile F} {deployment : Deployment}
    {pins : FactoryPins} {durable : Durable}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {factoryRoot : Digest} {height : Height} {descriptor : Descriptor Registry}
    (checked : Checked profile deployment pins durable directory authority factoryRoot height descriptor)
    (guard : ReadGuard) (member : guard ∈ checked.readGuards) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId := by
  cases checked with
  | neutral checked => exact checked.guardsExact guard member
  | evaluated checked => exact checked.guardsExact guard member

def check [DecidableEq F] (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (factoryRoot : Digest) (height : Height) (descriptor : Descriptor Registry) :
    Option (Checked profile deployment pins durable directory authority factoryRoot height descriptor) :=
  match checkNeutral deployment durable directory descriptor with
  | some neutral => some (.neutral neutral)
  | none => (checkEvaluated profile deployment pins durable directory authority factoryRoot height descriptor).map
      Checked.evaluated

/-- No clock premise is needed when the exact source-derived roots are empty. -/
theorem check_of_neutral [DecidableEq F] (profile : PolicyCompilerProfile F) (deployment : Deployment)
    (pins : FactoryPins) (durable : Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (factoryRoot : Digest) (height : Height) (descriptor : Descriptor Registry)
    (neutral : Neutral deployment durable directory descriptor)
    (found : checkNeutral deployment durable directory descriptor = some neutral) :
    check profile deployment pins durable directory authority factoryRoot height descriptor =
      some (.neutral neutral) := by
  simp only [check, found]

/-- A containing room always supplies a root, even when its own export body
is omitted. Its authenticated ancestor chain still has to be resolved. -/
theorem room_root_not_empty (item : BirthItem Registry)
    (dependencies : WorldKindLawDependencies.Dependencies) (room : Nat)
    (parent : item.parent = some room) : roots item dependencies ≠ [] := by
  simp [roots, parent]

/-- Acceptance retains the actual conjunction's verdict, not merely a public
local diagnostic that could hide an inherited refusal. -/
theorem ItemChecked.effective_law {profile : PolicyCompilerProfile F} {deployment : Deployment}
    {pins : FactoryPins} {durable : Durable}
    {directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot}
    {factoryRoot : Digest} {height : Height} {descriptor : Descriptor Registry}
    {clock : ClockCell.Clock} {item : BirthItem Registry}
    (checked : ItemChecked profile deployment pins durable directory authority factoryRoot height descriptor clock item) :
    Minidregg.Pred.eval (ResolvedLawCompilation.predicate checked.law.graph.resolved)
      (view pins authority.snapshot.authState factoryRoot height descriptor clock item false)
      (view pins authority.snapshot.authState factoryRoot height descriptor clock item true) = true := by
  obtain ⟨equality, accepted⟩ := checked.accepted
  letI : DecidableEq F := equality
  have sound := compiledLawAccepts_sound profile _ checked.witness accepted
  simpa only [checked.oldExact, checked.newExact] using sound

end Minidregg.Kernel.BirthExportAdmission
