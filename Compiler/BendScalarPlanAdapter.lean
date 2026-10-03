/- Generic structural source result ABI for guarded scalar object writes.
The source ABI identity must be pinned in the admitted execution profile.
Decoding is effect materialization, never domain policy or authority. Every
native field comes from the source constructor; target positions come from
one deterministic table over the actual command, and samples come from the
complete current native loaded directory. Native admission still checks current
source, authority, field closure, policy, funding, and complete replay binding.
-/
import Compiler.BendPlanLowering
import Compiler.BendSourceListTyped
import Compiler.CredentialAuthorityDomainReceiver
import Kernel.PhysicalResourceReadGuard

-- Exact emitted labels below captured from sealed-source Book
-- codex-station-world-20261003/evidence/sealed-bend-4JAMbl/book.bendtt
-- WorldPlanScalar source SHA256 1dfc1f4ae6f27268b291c03ffb7fe485fec49f8df18f0757a555fd618e489c30.
namespace Minidregg.Compiler.BendScalarPlanAdapter
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.BendSourceRepresentation
open Minidregg.Theory
open Minidregg.Theory.BendTT
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.Store
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.DeclaredResourceController
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

/-- Exact type declarations captured from the emitted sealed WorldPlanScalar
module. Constructor names alone are insufficient: the complete definitions and
whole checked Book must be retained by the profile binding. -/
def listType (element : String) : BTerm := .App .Q0 (.Ref "List.q2") (.Ref element)
def fieldsType : List BTerm → BTerm
  | [] => .Enu ["()"]
  | type :: rest => .Sig .Q1 type (fieldsType rest)
def singleArmsDef (name : String) (fields : List BTerm) : Def :=
  ⟨name ++ ".arms", .All .Q1 (.Enu [name]) (.Typ .Q2),
    .Mat name (fieldsType fields) .Efq, false⟩
def singleTypeDef (name : String) : Def :=
  ⟨name, .Typ .Q2, .Sig .Q1 (.Enu [name]) (.App .Q1 (.Ref (name ++ ".arms")) (.Var 0)), false⟩
def abiDefinitions : List Def :=
  [singleArmsDef "WorldPlanScalar.Ref" [.Ref "Nat", listType "Nat"],
   singleTypeDef "WorldPlanScalar.Ref",
   singleArmsDef "WorldPlanScalar.Write" [.Ref "Nat", .Ref "Nat", .Ref "Nat"],
   singleTypeDef "WorldPlanScalar.Write",
   singleArmsDef "WorldPlanScalar.ScalarEffect" [.Ref "WorldPlanScalar.Ref", listType "WorldPlanScalar.Write"],
   singleTypeDef "WorldPlanScalar.ScalarEffect",
   singleArmsDef "WorldPlanScalar.NativePlan" [listType "WorldPlanScalar.Ref", listType "WorldPlanScalar.ScalarEffect"],
   singleTypeDef "WorldPlanScalar.NativePlan",
   ⟨"WorldPlanScalar.PlanResult.arms",
     .All .Q1 (.Enu ["WorldPlanScalar.Refused", "WorldPlanScalar.Planned"]) (.Typ .Q2),
     .Mat "WorldPlanScalar.Refused" (fieldsType [.Ref "Nat"])
       (.Mat "WorldPlanScalar.Planned" (fieldsType [.Ref "WorldPlanScalar.NativePlan"]) .Efq), false⟩,
   ⟨"WorldPlanScalar.PlanResult", .Typ .Q2,
     .Sig .Q1 (.Enu ["WorldPlanScalar.Refused", "WorldPlanScalar.Planned"])
       (.App .Q1 (.Ref "WorldPlanScalar.PlanResult.arms") (.Var 0)), false⟩]

structure ABIBinding (book : Book) : Type where
  natBinding : NatBookBinding book
  listBinding : ListBookBinding book
  checked : Book.check book = .ok ()
  exactDefinitions : ∀ definition ∈ abiDefinitions, Book.get book definition.k = some definition

def bindABI (core : BendCoreAdmission.Checked) : Option (ABIBinding core.book) :=
  if prelude : Book.get core.book "Nat.arms" = some natArmsDef ∧
      Book.get core.book "Nat" = some natDef ∧
      Book.get core.book "List.q2.arms" = some listArmsDef ∧
      Book.get core.book "List.q2" = some listDef then
    if exactDefinitions : ∀ definition ∈ abiDefinitions,
        Book.get core.book definition.k = some definition then
      some ⟨⟨prelude.1, prelude.2.1, core.checked⟩,
        ⟨prelude.2.2.1, prelude.2.2.2, core.checked⟩, core.checked, exactDefinitions⟩
    else none
  else none

def rootCodec : LawfulCodec Digest := ResourceBirthCodec.strictCodec digestStream.toLawful

def refTerm (ref : Ref) : BTerm :=
  .Tup .Q1 (.Lab "WorldPlanScalar.Ref") (.Tup .Q1 (natTerm ref.resourceID)
    (.Tup .Q1 (bytesTerm (rootCodec.encode ref.root)) (.Lab "()")))
def decodeRef : BTerm → Option Ref
  | .Tup .Q1 (.Lab "WorldPlanScalar.Ref") (.Tup .Q1 resourceTerm (.Tup .Q1 root (.Lab "()"))) => do
      let resourceID ← decodeNat resourceTerm
      let bytes ← decodeBytes root
      let digest ← rootCodec.decode bytes
      pure ⟨resourceID, digest⟩
  | _ => none

def writeTerm (write : Write) : BTerm :=
  .Tup .Q1 (.Lab "WorldPlanScalar.Write") (.Tup .Q1 (natTerm write.field)
    (.Tup .Q1 (natTerm write.before) (.Tup .Q1 (natTerm write.after) (.Lab "()"))))
def decodeWrite : BTerm → Option Write
  | .Tup .Q1 (.Lab "WorldPlanScalar.Write") (.Tup .Q1 field
      (.Tup .Q1 before (.Tup .Q1 after (.Lab "()")))) => do
      let f ← decodeNat field
      let b ← decodeNat before
      let a ← decodeNat after
      pure ⟨f, b, a⟩
  | _ => none

def listTerm {α : Type} (item : α → BTerm) : List α → BTerm
  | [] => .Tup .Q1 (.Lab "Nil") (.Lab "()")
  | a :: rest => .Tup .Q1 (.Lab "Con")
      (.Tup .Q1 (item a) (.Tup .Q1 (listTerm item rest) (.Lab "()")))
def decodeList {α : Type} (item : BTerm → Option α) : BTerm → Option (List α)
  | .Tup .Q1 (.Lab "Nil") (.Lab "()") => some []
  | .Tup .Q1 (.Lab "Con") (.Tup .Q1 a (.Tup .Q1 rest (.Lab "()"))) => do
      let head ← item a
      let tail ← decodeList item rest
      pure (head :: tail)
  | _ => none

def scalarTerm (scalar : Scalar) : BTerm :=
  .Tup .Q1 (.Lab "WorldPlanScalar.ScalarEffect") (.Tup .Q1 (refTerm scalar.ref)
    (.Tup .Q1 (listTerm writeTerm scalar.writes) (.Lab "()")))
def decodeScalar : BTerm → Option Scalar
  | .Tup .Q1 (.Lab "WorldPlanScalar.ScalarEffect") (.Tup .Q1 ref (.Tup .Q1 writes (.Lab "()"))) => do
      let r ← decodeRef ref
      let ws ← decodeList decodeWrite writes
      pure ⟨r, ws⟩
  | _ => none

def planTerm (plan : NativePlan) : BTerm :=
  .Tup .Q1 (.Lab "WorldPlanScalar.NativePlan") (.Tup .Q1 (listTerm refTerm plan.reads)
    (.Tup .Q1 (listTerm scalarTerm plan.effects) (.Lab "()")))
def decodePlan : BTerm → Option NativePlan
  | .Tup .Q1 (.Lab "WorldPlanScalar.NativePlan") (.Tup .Q1 reads (.Tup .Q1 effects (.Lab "()"))) => do
      let rs ← decodeList decodeRef reads
      let es ← decodeList decodeScalar effects
      pure ⟨rs, es⟩
  | _ => none

@[simp] theorem decode_refTerm (ref : Ref) : decodeRef (refTerm ref) = some ref := by
  cases ref
  simp [refTerm, decodeRef, decode_natTerm, decode_bytesTerm, rootCodec.decode_encode]
@[simp] theorem decode_writeTerm (write : Write) : decodeWrite (writeTerm write) = some write := by
  cases write
  simp [writeTerm, decodeWrite, decode_natTerm]
@[simp] theorem decode_listTerm {α : Type} (item : α → BTerm) (decoder : BTerm → Option α)
    (roundtrip : ∀ a, decoder (item a) = some a) (items : List α) :
    decodeList decoder (listTerm item items) = some items := by
  induction items with
  | nil => rfl
  | cons a rest ih => simp [listTerm, decodeList, roundtrip, ih]
@[simp] theorem decode_scalarTerm (scalar : Scalar) : decodeScalar (scalarTerm scalar) = some scalar := by
  cases scalar
  simp [scalarTerm, decodeScalar, decode_listTerm writeTerm decodeWrite decode_writeTerm]
@[simp] theorem decode_planTerm (plan : NativePlan) : decodePlan (planTerm plan) = some plan := by
  cases plan
  simp [planTerm, decodePlan,
    decode_listTerm refTerm decodeRef decode_refTerm,
    decode_listTerm scalarTerm decodeScalar decode_scalarTerm]

/-- Refusal is inert and keeps its source reason. It is not an empty Plan. -/
inductive PlanResult where
  | refused (reason : Nat)
  | planned (plan : NativePlan)
  deriving DecidableEq, Repr

def resultTerm : PlanResult → BTerm
  | .refused reason => .Tup .Q1 (.Lab "WorldPlanScalar.Refused")
      (.Tup .Q1 (natTerm reason) (.Lab "()"))
  | .planned plan => .Tup .Q1 (.Lab "WorldPlanScalar.Planned")
      (.Tup .Q1 (planTerm plan) (.Lab "()"))
def decodeResult : BTerm → Option PlanResult
  | .Tup .Q1 (.Lab "WorldPlanScalar.Refused") (.Tup .Q1 reason (.Lab "()")) =>
      (decodeNat reason).map PlanResult.refused
  | .Tup .Q1 (.Lab "WorldPlanScalar.Planned") (.Tup .Q1 plan (.Lab "()")) =>
      (decodePlan plan).map PlanResult.planned
  | _ => none
@[simp] theorem decode_resultTerm (result : PlanResult) :
    decodeResult (resultTerm result) = some result := by
  cases result <;> simp [resultTerm, decodeResult, decode_natTerm]

theorem planTerm_injective : Function.Injective planTerm := by
  intro a b equal
  have decoded := congrArg decodePlan equal
  simpa only [decode_planTerm, Option.some.injEq] using decoded

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

/-- Execute only the Planned alternative. A decoded source refusal cannot
produce a Plan certificate; malformed constructor AST also fails closed. -/
def lowerResult {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (result : BTerm) :
    Option (Sigma fun source => BoundPlan deployment loaded command source) := do
  let decoded ← decodeResult result
  match decoded with
  | .refused _ => none
  | .planned source => do
      let bound ← bindPlan deployment loaded command source
      pure ⟨source, bound⟩

theorem refusal_no_plan {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (reason : Nat) :
    lowerResult deployment loaded command (resultTerm (.refused reason)) = none := by
  simp [lowerResult]

/-- Exact source bytes are one common canonical Plan result representation.
This equation does not claim the source method emitted those bytes: the
structural output codec and its immutable source Book/type must be bound. -/
theorem native_lower_roundtrip {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {source : NativePlan}
    (bound : BoundPlan deployment loaded command source) :
    BendPlanLowering.lower (BendPlanLowering.sourceTerm bound.plan) = some bound.plan :=
  BendPlanLowering.source_roundtrip bound.plan

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

/-- Source computation remains witnessed by the actual source machine. The
output decoder is this specific immutable structural codec; accepting arbitrary
client effect bytes is not an alternate execution route. -/
structure Evaluated (core : BendCoreAdmission.Checked) (initial : BTerm) where
  result : BTerm
  count : Nat
  trace : BendLiveMachine.Trace core.book count initial result
  value : Value core.book result
  output : PlanResult
  abi : ABIBinding core.book
  decoded : decodeResult result = some output

def execute (core : BendCoreAdmission.Checked) (abi : ABIBinding core.book) (classificationTicks steps : Nat)
    (initial : BTerm) : Option (Evaluated core initial) :=
  match BendLiveMachine.executeChecked core.book classificationTicks steps initial with
  | .refused _ _ _ _ => none
  | .complete result count trace value =>
      match decoded : decodeResult result with
      | none => none
      | some output => some ⟨result, count, trace, value, output, abi, decoded⟩

/-- The receiving join keeps the COMPLETED SOURCE TRACE together with the
native current-cell binding. Raw structural decoding is not a source execution
certificate. Current method/input/authority/funding admission is additional. -/
structure BoundResult {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (core : BendCoreAdmission.Checked) (initial : BTerm)
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) where
  evaluated : Evaluated core initial
  source : NativePlan
  outputExact : evaluated.output = .planned source
  bound : BoundPlan deployment loaded command source

def bindEvaluated {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {core : BendCoreAdmission.Checked} {initial : BTerm}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (evaluated : Evaluated core initial) :
    Option (BoundResult core initial deployment loaded command) :=
  match outputExact : evaluated.output with
  | .refused _ => none
  | .planned source => do
      let bound ← bindPlan deployment loaded command source
      pure ⟨evaluated, source, outputExact, bound⟩

theorem completed_refusal_inert {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {core : BendCoreAdmission.Checked} {initial : BTerm}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (evaluated : Evaluated core initial) (reason : Nat)
    (refusal : evaluated.output = .refused reason) :
    bindEvaluated deployment loaded command evaluated = none := by
  unfold bindEvaluated
  split <;> simp_all

theorem completed_source_exact_native {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {core : BendCoreAdmission.Checked} {initial : BTerm}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} (result : BoundResult core initial deployment loaded command) :
    result.bound.plan.effects = BendWorldPlan.effectsOf command := exact_native_effects result.bound

#assert_axioms BoundRead.guard_current
#assert_axioms ordered_reads_complete
#assert_axioms completed_refusal_inert
#assert_axioms completed_source_exact_native
#assert_axioms aliased_command_refused
#assert_axioms aliased_effect_refused
#assert_axioms stale_root_impossible
#assert_axioms ordered_correspondence
#assert_axioms exact_native_effects
#assert_axioms write_admitted
#assert_axioms sourcePatch_native
#assert_axioms source_before_at_prefix
#assert_axioms decode_refTerm
#assert_axioms decode_writeTerm
#assert_axioms decode_listTerm
#assert_axioms decode_scalarTerm
#assert_axioms decode_resultTerm
#assert_axioms refusal_no_plan
#assert_axioms decode_planTerm
#assert_axioms planTerm_injective
#assert_axioms native_lower_roundtrip
#assert_axioms no_missing_effects
end Minidregg.Compiler.BendScalarPlanAdapter
