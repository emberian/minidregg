/- Versioned scalar source ABI with canonical native identity bytes.
No native identity is materialized as a unary source Nat. The native logical
model and exact current-cell/prefix/order binding are the qualified v1 adapter. -/
import Compiler.BendScalarPlanCanonical
import Compiler.BendSourceCanonicalCodec

namespace Minidregg.Compiler.BendScalarPlanBytesAdapter
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.BendSourceRepresentation
open Minidregg.Theory.BendTT
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false
abbrev Ref := BendScalarPlanAdapter.Ref
abbrev Write := BendScalarPlanAdapter.Write
abbrev Scalar := BendScalarPlanAdapter.Scalar
abbrev NativePlan := BendScalarPlanAdapter.NativePlan
abbrev PlanResult := BendScalarPlanAdapter.PlanResult

def identityCodec : LawfulCodec Nat := ResourceBirthCodec.strictCodec StreamCodec.nat.toLawful
abbrev rootCodec := BendScalarPlanAdapter.rootCodec

def refTerm (ref : Ref) : BTerm :=
  .Tup .Q1 (.Lab "WorldPlanScalarBytes.Ref")
    (.Tup .Q1 (bytesTerm (identityCodec.encode ref.resourceID))
      (.Tup .Q1 (bytesTerm (rootCodec.encode ref.root)) (.Lab "()")))
def decodeRef : BTerm → Option Ref
  | .Tup .Q1 (.Lab "WorldPlanScalarBytes.Ref")
      (.Tup .Q1 resourceBytes (.Tup .Q1 rootBytes (.Lab "()"))) => do
      let idBytes ← decodeBytes resourceBytes
      let resourceID ← identityCodec.decode idBytes
      let bytes ← decodeBytes rootBytes
      let root ← rootCodec.decode bytes
      pure ⟨resourceID, root⟩
  | _ => none

def writeTerm (write : Write) : BTerm :=
  .Tup .Q1 (.Lab "WorldPlanScalarBytes.Write") (.Tup .Q1 (natTerm write.field)
    (.Tup .Q1 (natTerm write.before) (.Tup .Q1 (natTerm write.after) (.Lab "()"))))
def decodeWrite : BTerm → Option Write
  | .Tup .Q1 (.Lab "WorldPlanScalarBytes.Write") (.Tup .Q1 field
      (.Tup .Q1 before (.Tup .Q1 after (.Lab "()")))) => do
      let f ← decodeNat field
      let b ← decodeNat before
      let a ← decodeNat after
      pure ⟨f, b, a⟩
  | _ => none
abbrev listTerm := @BendScalarPlanAdapter.listTerm
abbrev decodeList := @BendScalarPlanAdapter.decodeList

def scalarTerm (scalar : Scalar) : BTerm :=
  .Tup .Q1 (.Lab "WorldPlanScalarBytes.ScalarEffect") (.Tup .Q1 (refTerm scalar.ref)
    (.Tup .Q1 (listTerm writeTerm scalar.writes) (.Lab "()")))
def decodeScalar : BTerm → Option Scalar
  | .Tup .Q1 (.Lab "WorldPlanScalarBytes.ScalarEffect")
      (.Tup .Q1 ref (.Tup .Q1 writes (.Lab "()"))) => do
      let r ← decodeRef ref
      let ws ← decodeList decodeWrite writes
      pure ⟨r, ws⟩
  | _ => none

def planTerm (plan : NativePlan) : BTerm :=
  .Tup .Q1 (.Lab "WorldPlanScalarBytes.NativePlan") (.Tup .Q1 (listTerm refTerm plan.reads)
    (.Tup .Q1 (listTerm scalarTerm plan.effects) (.Lab "()")))
def decodePlan : BTerm → Option NativePlan
  | .Tup .Q1 (.Lab "WorldPlanScalarBytes.NativePlan")
      (.Tup .Q1 reads (.Tup .Q1 effects (.Lab "()"))) => do
      let rs ← decodeList decodeRef reads
      let es ← decodeList decodeScalar effects
      pure ⟨rs, es⟩
  | _ => none
def resultTerm : PlanResult → BTerm
  | .refused reason => .Tup .Q1 (.Lab "WorldPlanScalarBytes.Refused")
      (.Tup .Q1 (natTerm reason) (.Lab "()"))
  | .planned plan => .Tup .Q1 (.Lab "WorldPlanScalarBytes.Planned")
      (.Tup .Q1 (planTerm plan) (.Lab "()"))
def decodeResult : BTerm → Option PlanResult
  | .Tup .Q1 (.Lab "WorldPlanScalarBytes.Refused") (.Tup .Q1 reason (.Lab "()")) =>
      (decodeNat reason).map BendScalarPlanAdapter.PlanResult.refused
  | .Tup .Q1 (.Lab "WorldPlanScalarBytes.Planned") (.Tup .Q1 plan (.Lab "()")) =>
      (decodePlan plan).map BendScalarPlanAdapter.PlanResult.planned
  | _ => none

@[simp] theorem decode_refTerm (ref : Ref) : decodeRef (refTerm ref) = some ref := by
  cases ref
  simp [refTerm, decodeRef, decode_bytesTerm, identityCodec.decode_encode, rootCodec.decode_encode]
@[simp] theorem decode_writeTerm (write : Write) : decodeWrite (writeTerm write) = some write := by
  cases write
  simp [writeTerm, decodeWrite, decode_natTerm]
@[simp] theorem decode_scalarTerm (scalar : Scalar) : decodeScalar (scalarTerm scalar) = some scalar := by
  cases scalar
  simp [scalarTerm, decodeScalar,
    BendScalarPlanAdapter.decode_listTerm writeTerm decodeWrite decode_writeTerm]
@[simp] theorem decode_planTerm (plan : NativePlan) : decodePlan (planTerm plan) = some plan := by
  cases plan
  simp [planTerm, decodePlan,
    BendScalarPlanAdapter.decode_listTerm refTerm decodeRef decode_refTerm,
    BendScalarPlanAdapter.decode_listTerm scalarTerm decodeScalar decode_scalarTerm]
@[simp] theorem decode_resultTerm (result : PlanResult) :
    decodeResult (resultTerm result) = some result := by
  cases result <;> simp [resultTerm, decodeResult, decode_natTerm]

abbrev listType := BendScalarPlanAdapter.listType
abbrev fieldsType := BendScalarPlanAdapter.fieldsType
abbrev singleArmsDef := BendScalarPlanAdapter.singleArmsDef
abbrev singleTypeDef := BendScalarPlanAdapter.singleTypeDef
def abiDefinitions : List Def :=
  [singleArmsDef "WorldPlanScalarBytes.Ref" [listType "Nat", listType "Nat"],
   singleTypeDef "WorldPlanScalarBytes.Ref",
   singleArmsDef "WorldPlanScalarBytes.Write" [.Ref "Nat", .Ref "Nat", .Ref "Nat"],
   singleTypeDef "WorldPlanScalarBytes.Write",
   singleArmsDef "WorldPlanScalarBytes.ScalarEffect" [.Ref "WorldPlanScalarBytes.Ref", listType "WorldPlanScalarBytes.Write"],
   singleTypeDef "WorldPlanScalarBytes.ScalarEffect",
   singleArmsDef "WorldPlanScalarBytes.NativePlan" [listType "WorldPlanScalarBytes.Ref", listType "WorldPlanScalarBytes.ScalarEffect"],
   singleTypeDef "WorldPlanScalarBytes.NativePlan",
   ⟨"WorldPlanScalarBytes.PlanResult.arms",
     .All .Q1 (.Enu ["WorldPlanScalarBytes.Refused", "WorldPlanScalarBytes.Planned"]) (.Typ .Q2),
     .Mat "WorldPlanScalarBytes.Refused" (fieldsType [.Ref "Nat"])
       (.Mat "WorldPlanScalarBytes.Planned" (fieldsType [.Ref "WorldPlanScalarBytes.NativePlan"]) .Efq), false⟩,
   ⟨"WorldPlanScalarBytes.PlanResult", .Typ .Q2,
     .Sig .Q1 (.Enu ["WorldPlanScalarBytes.Refused", "WorldPlanScalarBytes.Planned"])
       (.App .Q1 (.Ref "WorldPlanScalarBytes.PlanResult.arms") (.Var 0)), false⟩]

/-- Exact qualified declaration pinning is authored from the captured emitted
Book before this binder is qualified; aliases are not source type identity. -/
structure ABIBinding (book : Book) : Type where
  natBinding : NatBookBinding book
  listBinding : ListBookBinding book
  exactDefinitions : ∀ definition ∈ abiDefinitions, Book.get book definition.k = some definition

def bindABI (core : BendCoreAdmission.Checked) : Option (ABIBinding core.book) :=
  if prelude : Book.get core.book "Nat.arms" = some natArmsDef ∧
      Book.get core.book "Nat" = some natDef ∧
      Book.get core.book "List.q2.arms" = some listArmsDef ∧
      Book.get core.book "List.q2" = some listDef then
    if exactDefinitions : ∀ definition ∈ abiDefinitions,
        Book.get core.book definition.k = some definition then
      some ⟨⟨prelude.1, prelude.2.1, core.checked⟩,
        ⟨prelude.2.2.1, prelude.2.2.2, core.checked⟩, exactDefinitions⟩
    else none
  else none

abbrev bindPlan := @BendScalarPlanAdapter.bindPlan
abbrev bindOrdered := @BendScalarPlanAdapter.bindOrdered

/-- Source computation remains witnessed by the actual source machine. The
output decoder is this specific immutable structural codec; accepting arbitrary
client effect bytes is not an alternate execution route. -/
structure Evaluated (core : BendCoreAdmission.Checked) (initial : BTerm) where
  result : BTerm
  count : Nat
  trace : Minidregg.Theory.BendLiveMachine.Trace core.book count initial result
  value : Value core.book result
  output : PlanResult
  abi : ABIBinding core.book
  decoded : decodeResult result = some output

def execute (core : BendCoreAdmission.Checked) (abi : ABIBinding core.book) (classificationTicks steps : Nat)
    (initial : BTerm) : Option (Evaluated core initial) :=
  match Minidregg.Theory.BendLiveMachine.executeChecked core.book classificationTicks steps initial with
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
  bound : BendScalarPlanAdapter.BoundPlan deployment loaded command source

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
    result.bound.plan.effects = BendWorldPlan.effectsOf command := BendScalarPlanAdapter.exact_native_effects result.bound

theorem identityCodec_canonical {bytes : List UInt8} {resourceID : Nat}
    (decoded : identityCodec.decode bytes = some resourceID) :
    identityCodec.encode resourceID = bytes :=
  ResourceBirthCodec.strictCodec_canonical StreamCodec.nat.toLawful decoded

theorem decodeRef_sound (term : BTerm) (ref : Ref)
    (decoded : decodeRef term = some ref) : term = refTerm ref := by
  fun_cases decodeRef term <;>
    simp_all [decodeRef, refTerm, Option.bind_eq_some_iff] <;>
    aesop (add safe forward decodeBytes_sound)
      (add safe forward identityCodec_canonical)
      (add safe forward BendScalarPlanAdapter.rootCodec_canonical)

theorem decodeWrite_sound (term : BTerm) (write : Write)
    (decoded : decodeWrite term = some write) : term = writeTerm write := by
  fun_cases decodeWrite term <;>
    simp_all [decodeWrite, writeTerm, Option.bind_eq_some_iff] <;>
    aesop (add safe forward decodeNat_sound)

theorem decodeScalar_sound (term : BTerm) (scalar : Scalar)
    (decoded : decodeScalar term = some scalar) : term = scalarTerm scalar := by
  fun_cases decodeScalar term <;>
    simp_all [decodeScalar, scalarTerm, Option.bind_eq_some_iff] <;>
    aesop (add safe forward decodeRef_sound)
      (add safe forward (BendScalarPlanAdapter.decodeList_sound writeTerm decodeWrite decodeWrite_sound))

theorem decodePlan_sound (term : BTerm) (plan : NativePlan)
    (decoded : decodePlan term = some plan) : term = planTerm plan := by
  fun_cases decodePlan term <;>
    simp_all [decodePlan, planTerm, Option.bind_eq_some_iff] <;>
    aesop
      (add safe forward (BendScalarPlanAdapter.decodeList_sound refTerm decodeRef decodeRef_sound))
      (add safe forward (BendScalarPlanAdapter.decodeList_sound scalarTerm decodeScalar decodeScalar_sound))

theorem decodeResult_sound (term : BTerm) (result : PlanResult)
    (decoded : decodeResult term = some result) : term = resultTerm result := by
  fun_cases decodeResult term <;>
    simp_all [decodeResult, resultTerm, Option.map_eq_some_iff] <;>
    aesop (add safe forward [decodeNat_sound, decodePlan_sound])

theorem decodeResult_iff (term : BTerm) (result : PlanResult) :
    decodeResult term = some result ↔ term = resultTerm result :=
  ⟨decodeResult_sound term result, fun equal => equal ▸ decode_resultTerm result⟩

#assert_axioms identityCodec_canonical
#assert_axioms decodeRef_sound
#assert_axioms decodeWrite_sound
#assert_axioms decodeScalar_sound
#assert_axioms decodePlan_sound
#assert_axioms decodeResult_sound
#assert_axioms decodeResult_iff
#assert_axioms completed_refusal_inert
#assert_axioms completed_source_exact_native
#assert_axioms decode_refTerm
#assert_axioms decode_writeTerm
#assert_axioms decode_scalarTerm
#assert_axioms decode_planTerm
#assert_axioms decode_resultTerm
end Minidregg.Compiler.BendScalarPlanBytesAdapter
