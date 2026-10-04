/- Generic structural source result ABI for guarded scalar object writes.
The source ABI identity must be pinned in the admitted execution profile.
Decoding is effect materialization, never domain policy or authority. Every
native field comes from the source constructor; target positions come from
one deterministic table over the actual command, and samples come from the
complete current native loaded directory. Native admission still checks current
source, authority, field closure, policy, funding, and complete replay binding.
-/
import Compiler.BendPlanLowering
import Compiler.ObjectiveNativeScalarBinding
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

/-- The TT-free scalar binder lives in `Compiler.ObjectiveNativeScalarBinding`
(the Objective native route imports only that). This module keeps only the
BendTT term ABI over it; the names below are aliases, not a second copy. -/
export ObjectiveNativeScalarBinding (Ref Write Scalar NativePlan rootCodec writeKey action sourcePatch sourcePatch_native effect indexOf BoundScalar bindScalar Ordered bindOrdered BoundRead bindRead OrderedReads bindReads ordered_reads_complete BoundPlan bindPlan ordered_length no_missing_effects exact_native_effects write_admitted source_before_at_prefix aliased_command_refused aliased_effect_refused stale_root_impossible ordered_correspondence)

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
