/- Objective-only native scalar/read binding. Exact native constructors and guards;
no old language AST, checked Book, source evaluator, or authority constructor. -/
import Compiler.BendWorldPlan
import Compiler.CredentialAuthorityDomainReceiver
import Kernel.PhysicalResourceReadGuard
namespace Minidregg.Compiler.ObjectiveNativeScalarBinding
open Minidregg.Compiler Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory Minidregg.Theory.TypedAuthorization Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.Store Minidregg.Theory.CellRegistry Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.IndexedProgram Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false
structure Ref where
  resourceID : Nat
  root : Digest
  deriving DecidableEq, Repr
structure Write where
  field : Nat
  before : Nat
  after : Nat
  deriving DecidableEq, Repr
structure Scalar where
  ref : Ref
  writes : List Write
  deriving DecidableEq, Repr
structure NativePlan where
  reads : List Ref
  effects : List Scalar
  deriving DecidableEq, Repr

def rootCodec : LawfulCodec Digest := ResourceBirthCodec.strictCodec digestStream.toLawful
def writeKey (ref : Ref) (write : Write) : StateKey :=
  .objectField ⟨ref.resourceID⟩ ⟨write.field⟩
def action (ref : Ref) (write : Write) : DeclaredActionLowering.Action :=
  .write (writeKey ref write) (some (Int.ofNat write.before)) (Int.ofNat write.after)
def sourcePatch (ref : Ref) (writes : List Write) : Patch effectLayout :=
  writes.map (fun write => DeclaredActionLowering.guardedSet (writeKey ref write)
    (some (Int.ofNat write.before)) (Int.ofNat write.after))

theorem sourcePatch_native (ref : Ref) (writes : List Write) :
    (writes.map (action ref)).flatMap DeclaredActionLowering.Action.ops = sourcePatch ref writes := by
  induction writes with
  | nil => rfl
  | cons write rest ih => simp [sourcePatch, action, DeclaredActionLowering.Action.ops, ih]

def effect (index : Nat) (scalar : Scalar) : BendWorldPlan.Effect :=
  ⟨index, .scalar (scalar.writes.map (action scalar.ref))⟩
/-- Actual command order determines indices. Identity is never the index. -/
def indexOf (command : Command) (resourceID : Nat) : Option (Fin command.targets.length) :=
  (List.finRange command.targets.length).find? fun i =>
    command.targets[i].target == resourceID

/-- A successful adapter retains a complete sampled preimage from the native
current directory. A client cannot provide the store or its own admission bit. -/
structure BoundScalar {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (scalar : Scalar) where
  private mk ::
  index : Fin command.targets.length
  indexExact : indexOf command scalar.ref.resourceID = some index
  kindExact : command.targets[index].kind = .object
  idExact : command.targets[index].target = scalar.ref.resourceID
  targetRoot : command.targets[index].expectedTargetRoot = scalar.ref.root
  packed : PackedCell CanonicalCellRegistry.registry
  present : loaded.directory.slots scalar.ref.resourceID = .present packed
  pre : DeclaredEffectCell.Cell
  selected : CanonicalCellRegistry.selectDeclared deployment scalar.ref.resourceID .object packed = some pre
  currentRoot : pre.root = scalar.ref.root
  /-- Native sequential guards: each expected value is checked at the
  exact store obtained from its preceding native source-derived writes. -/
  guardsExact : Patch.ValidFrom pre.logical (sourcePatch scalar.ref scalar.writes)

def bindScalar {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (scalar : Scalar) : Option (BoundScalar deployment loaded command scalar) := do
  match indexExact : indexOf command scalar.ref.resourceID with
  | none => none
  | some index =>
    if kindExact : command.targets[index].kind = .object then
      if idExact : command.targets[index].target = scalar.ref.resourceID then
        if targetRoot : command.targets[index].expectedTargetRoot = scalar.ref.root then
          match present : loaded.directory.slots scalar.ref.resourceID with
          | .absent => none
          | .present packed =>
            match selected : CanonicalCellRegistry.selectDeclared deployment scalar.ref.resourceID .object packed with
            | none => none
            | some pre =>
              if currentRoot : pre.root = scalar.ref.root then
                if guardsExact : Patch.ValidFrom pre.logical (sourcePatch scalar.ref scalar.writes) then
                  some ⟨index, indexExact, kindExact, idExact, targetRoot,
                    packed, present, pre, selected, currentRoot, guardsExact⟩
                else none
              else none
        else none
      else none
    else none

/-- Ordered correspondence, including the complete native payload of EVERY
source effect. Refusal cannot erase an effect and claim success on the rest. -/
inductive Ordered {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) : List Scalar → List BendWorldPlan.Effect → Type where
  | nil : Ordered deployment loaded command [] []
  | cons {scalar : Scalar} {rest : List Scalar} {effects : List BendWorldPlan.Effect}
      (bound : BoundScalar deployment loaded command scalar)
      (tail : Ordered deployment loaded command rest effects) :
      Ordered deployment loaded command (scalar :: rest) (effect bound.index.val scalar :: effects)

def bindOrdered {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (scalars : List Scalar) :
    Option (Sigma fun effects => Ordered deployment loaded command scalars effects) :=
  match scalars with
  | [] => some ⟨[], .nil⟩
  | scalar :: rest => do
      let bound ← bindScalar deployment loaded command scalar
      let tail ← bindOrdered deployment loaded command rest
      pure ⟨effect bound.index.val scalar :: tail.1, .cons bound tail.2⟩

/-- Source handles quote the logical schema root. Durable CAS read guards
quote the physical lifecycle envelope root. Both come from the SAME current
loaded cell; treating either digest as the other is a receiving bug. -/
structure BoundRead {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable) (ref : Ref) where
  private mk ::
  packed : PackedCell CanonicalCellRegistry.registry
  present : loaded.directory.slots ref.resourceID = .present packed
  logicalRoot : packed.payloadRoot = ref.root
  physicalCurrent : ResourceBirthCodec.physicalRoot (.live packed) =
    durable.snapshot.model.roots ⟨ref.resourceID⟩

def BoundRead.guard {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable} {ref : Ref}
    (bound : BoundRead loaded ref) : Minidregg.Kernel.DurableDataIntent.ReadGuard :=
  ⟨⟨ref.resourceID⟩, ResourceBirthCodec.physicalRoot (.live bound.packed)⟩

def bindRead {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable) (ref : Ref) :
    Option (BoundRead loaded ref) :=
  match present : loaded.directory.slots ref.resourceID with
  | .absent => none
  | .present packed =>
    if logicalRoot : packed.payloadRoot = ref.root then
      some ⟨packed, present, logicalRoot,
        Minidregg.Kernel.PhysicalResourceReadGuard.current loaded ref.resourceID packed present⟩
    else none

inductive OrderedReads {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable) :
    List Ref → List Minidregg.Kernel.DurableDataIntent.ReadGuard → Type where
  | nil : OrderedReads loaded [] []
  | cons {ref : Ref} {rest : List Ref}
      {guards : List Minidregg.Kernel.DurableDataIntent.ReadGuard}
      (bound : BoundRead loaded ref) (tail : OrderedReads loaded rest guards) :
      OrderedReads loaded (ref :: rest) (bound.guard :: guards)

def bindReads {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable) (refs : List Ref) :
    Option (Sigma fun guards => OrderedReads loaded refs guards) :=
  match refs with
  | [] => some ⟨[], .nil⟩
  | ref :: rest => do
    let bound ← bindRead loaded ref
    let tail ← bindReads loaded rest
    pure ⟨bound.guard :: tail.1, .cons bound tail.2⟩

theorem BoundRead.guard_current {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable} {ref : Ref}
    (bound : BoundRead loaded ref) :
    bound.guard.expectedRoot = durable.snapshot.model.roots bound.guard.cellId :=
  bound.physicalCurrent

theorem ordered_reads_complete {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable} {refs : List Ref}
    {guards : List Minidregg.Kernel.DurableDataIntent.ReadGuard}
    (ordered : OrderedReads loaded refs guards) :
    List.Forall₂ (fun ref guard => ∃ bound : BoundRead loaded ref, guard = bound.guard) refs guards := by
  induction ordered with
  | nil => exact .nil
  | cons bound tail ih => exact .cons ⟨bound, rfl⟩ ih

structure BoundPlan {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (source : NativePlan) where
  private mk ::
  plan : BendWorldPlan.Plan
  commandDistinct : (command.targets.map Target.target).Nodup
  effectsDistinct : (source.effects.map (fun s => s.ref.resourceID)).Nodup
  ordered : Ordered deployment loaded command source.effects plan.effects
  orderedReads : OrderedReads loaded source.reads plan.reads
  returnsExact : plan.returns = []
  nativeExact : BendWorldPlan.matchesCommand plan command = true

def bindPlan {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (source : NativePlan) : Option (BoundPlan deployment loaded command source) := do
  if commandDistinct : (command.targets.map Target.target).Nodup then
    if effectsDistinct : (source.effects.map (fun s => s.ref.resourceID)).Nodup then
      let effects ← bindOrdered deployment loaded command source.effects
      let reads ← bindReads loaded source.reads
      let plan : BendWorldPlan.Plan := ⟨effects.1, [], reads.1⟩
      if nativeExact : BendWorldPlan.matchesCommand plan command = true then
        pure ⟨plan, commandDistinct, effectsDistinct, effects.2, reads.2, rfl, nativeExact⟩
      else none
    else none
  else none

theorem ordered_length {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {scalars : List Scalar} {effects : List BendWorldPlan.Effect}
    (ordered : Ordered deployment loaded command scalars effects) : effects.length = scalars.length := by
  induction ordered with
  | nil => rfl
  | cons bound tail ih => exact congrArg Nat.succ ih

theorem no_missing_effects {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {source : NativePlan}
    (bound : BoundPlan deployment loaded command source) :
    bound.plan.effects.length = source.effects.length := ordered_length bound.ordered

theorem exact_native_effects {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {source : NativePlan}
    (bound : BoundPlan deployment loaded command source) :
    bound.plan.effects = BendWorldPlan.effectsOf command :=
  BendWorldPlan.ordered_payloads_exact bound.nativeExact

theorem write_admitted (ref : Ref) (write : Write) :
    (action ref write).admissionCheck (⟨ref.resourceID⟩ : ResourceId .object) = true := by
  simp [action, writeKey, DeclaredActionLowering.Action.admissionCheck,
    DeclaredActionLowering.writableKeyCheck]

/-- Every source before-value is the actual native value at its precise
ordered prior, including repeated writes to the same field. -/
theorem source_before_at_prefix {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {scalar : Scalar}
    (bound : BoundScalar deployment loaded command scalar)
    (prior suffix : List Write) (write : Write)
    (position : scalar.writes = prior ++ write :: suffix) :
    (Patch.run bound.pre.logical (sourcePatch scalar.ref prior))
      (writeKey scalar.ref write).address = some (Int.ofNat write.before) := by
  have valid := bound.guardsExact
  rw [position] at valid
  have patchExact : sourcePatch scalar.ref (prior ++ write :: suffix) =
      sourcePatch scalar.ref prior ++ sourcePatch scalar.ref (write :: suffix) := by
    simp [sourcePatch]
  rw [patchExact] at valid
  have tail := ((Patch.validFrom_append bound.pre.logical
    (sourcePatch scalar.ref prior) (sourcePatch scalar.ref (write :: suffix))).mp valid).2
  exact (DeclaredActionLowering.guardedSet_enabled_iff _ _ _ _).mp tail.1

theorem aliased_command_refused {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (source : NativePlan)
    (aliased : ¬ (command.targets.map Target.target).Nodup) :
    bindPlan deployment loaded command source = none := by
  simp [bindPlan, aliased]

theorem aliased_effect_refused {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (source : NativePlan)
    (aliased : ¬ (source.effects.map (fun s => s.ref.resourceID)).Nodup) :
    bindPlan deployment loaded command source = none := by
  simp [bindPlan, aliased]

theorem stale_root_impossible {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {scalar : Scalar}
    (bound : BoundScalar deployment loaded command scalar)
    (stale : bound.pre.root ≠ scalar.ref.root) : False := stale bound.currentRoot

theorem ordered_correspondence {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {scalars : List Scalar} {effects : List BendWorldPlan.Effect}
    (ordered : Ordered deployment loaded command scalars effects) :
    List.Forall₂ (fun scalar native => ∃ bound : BoundScalar deployment loaded command scalar,
      native = effect bound.index.val scalar) scalars effects := by
  induction ordered with
  | nil => exact .nil
  | cons bound tail ih => exact .cons ⟨bound, rfl⟩ ih


end Minidregg.Compiler.ObjectiveNativeScalarBinding
