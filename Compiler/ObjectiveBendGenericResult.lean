/- Same-source typed {plan,result} envelope. Current effect coverage is the
native content/durable-append constructor registry; return storage is appended without dropping original
ordered application effects or physical reads. Current authority/funding belong
to the native gate; this token cannot accept a caller-authored Plan. -/
import Compiler.ObjectiveBendResultAdapter
import Compiler.ObjectiveBendNativePlanData
namespace Minidregg.Compiler.ObjectiveBendGenericResult
open Minidregg.Theory Minidregg.Theory.TypedAuthorization
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendDemandMachine ObjectiveBendDemandData
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
open ObjectiveBendResultAdapter ObjectiveNativeScalarBinding
set_option autoImplicit false

def codecId : Digest := (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.NATIVE-RESULT-ENVELOPE/v1".toUTF8.toList
  (Minidregg.Compiler.Tower256ConcreteBackend.digestStream.encode ObjectiveBendNativePlanData.codecId ++
   Minidregg.Compiler.Tower256ConcreteBackend.digestStream.encode ObjectiveBendResultAdapter.codecId)).digest

/-- Merge the return atom into the selected content target's action order.
When that target has no source effect, add its content effect at the end.
This avoids duplicate resource targets and preserves every source action. -/
def augment (profile : ObjectiveBendResultAdapter.Profile) (command : Command)
    (slot : BendWorldPlan.ReturnSlot) (effects : List ObjectiveBendNativePlanData.Effect) :
    Option (List ObjectiveBendNativePlanData.Effect) := do
  let target ← command.targets[profile.target]?
  let .content returned := (returnEffect profile slot).payload | none
  match effects.find? (fun effect => effect.ref.resourceID == target.target) with
  | some found =>
    let .content content := found.payload | none
    let payload : Payload := .content ⟨content.actions++returned.actions⟩
    let merged : ObjectiveBendNativePlanData.Effect :=
      ⟨found.ref,payload,payloadStream.toLawful.decode_encode payload⟩
    pure (effects.map (fun effect => if effect.ref.resourceID == target.target then merged else effect))
  | none =>
    let payload := (returnEffect profile slot).payload
    let extra : ObjectiveBendNativePlanData.Effect :=
      ⟨⟨target.target,target.expectedTargetRoot⟩,payload,payloadStream.toLawful.decode_encode payload⟩
    pure (effects++[extra])

structure Prepared (deployment : CanonicalCellRegistry.Deployment)
    (loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (profile : ObjectiveBendResultAdapter.Profile) (command : Command) (source : AnnotatedTerm)
    (limits : Limits) (budget : Budget) (capacity : ObjectiveBendDemandCapacity.Profile) where
  private mk ::
  checked : Checked source []
  execution : ExecutionWith (ObjectiveBendDemandCapacity.allows capacity) limits budget source.term
  runExact : executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget source.term = .ok execution
  planType : Ty
  resultType : Ty
  typeShape : checked.type = .field "plan" planType (.field "result" resultType .emptyRow)
  planData : Data
  resultData : Data
  dataShape : execution.extraction.result.value = .record [("plan",planData),("result",resultData)]
  typeExact : dataMatches budget.nodes checked.type execution.extraction.result.value = true
  native : ObjectiveBendNativePlanData.NativePlan
  decodedPlan : ObjectiveBendNativePlanData.decode capacity planData = some native
  bytes : List UInt8
  bytesExact : encodeData budget.nodes resultData = some bytes
  slot : BendWorldPlan.ReturnSlot
  slotExact : slot = returnSlot profile resultType bytes
  augmented : List ObjectiveBendNativePlanData.Effect
  augmentationExact : augment profile command slot native.effects = some augmented
  effects : List BendWorldPlan.Effect
  ordered : ObjectiveBendNativePlanData.Ordered deployment loaded command augmented effects
  reads : List ReadGuard
  orderedReads : OrderedReads loaded native.reads reads
  plan : BendWorldPlan.Plan
  planExact : plan = ⟨effects,[slot],reads⟩
  nativeExact : BendWorldPlan.matchesCommand plan command = true
  returnsStored : plan.returns.all (storesReturn command) = true

def prepareChecked (deployment : CanonicalCellRegistry.Deployment)
    (loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (profile : ObjectiveBendResultAdapter.Profile) (command : Command) (source : AnnotatedTerm)
    (checked : Checked source []) (limits : Limits) (budget : Budget) (capacity : ObjectiveBendDemandCapacity.Profile) :
    Except ObjectiveBendResultAdapter.Failure (Prepared deployment loaded profile command source limits budget capacity) := do
  match runExact : executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget source.term with
  | .error error => throw (.execution error.1 error.2.1 error.2.2)
  | .ok execution =>
    match typeShape : checked.type with
    | .field "plan" planType (.field "result" resultType .emptyRow) =>
      match dataShape : execution.extraction.result.value with
      | .record [("plan",planData),("result",resultData)] =>
        if !ObjectiveBendNativePlanData.digestCapacity budget.nodes capacity planData then
          throw (.execution .suspended execution.extraction.result.state execution.extraction.result.remaining)
        if typeExact : dataMatches budget.nodes checked.type execution.extraction.result.value = true then
          match decodedPlan : ObjectiveBendNativePlanData.decode capacity planData with
          | none => throw .nativeBinding
          | some native =>
            if !(decide (command.targets.map Target.target).Nodup) ||
                !(decide (native.effects.map (fun effect=>effect.ref.resourceID)).Nodup) then throw .nativeBinding
            let some reads := bindReads loaded native.reads | throw .nativeBinding
            match bytesExact : encodeData budget.nodes resultData with
            | none => throw .bytes
            | some bytes =>
              let slot := returnSlot profile resultType bytes
              match augmentationExact : augment profile command slot native.effects with
              | none => throw .nativeBinding
              | some augmented =>
                let some effects := ObjectiveBendNativePlanData.bindOrdered deployment loaded command augmented | throw .nativeBinding
                let plan : BendWorldPlan.Plan := ⟨effects.1,[slot],reads.1⟩
                let producedBytes := (plan.effects.map (fun effect=>BendWorldPlan.effectStream.encode effect)).flatten.length + (BendWorldPlan.encodeReturn slot).length
                if producedBytes > budget.bytes then throw (.execution .budget execution.extraction.result.state execution.extraction.result.remaining)
                if nativeExact : BendWorldPlan.matchesCommand plan command = true then
                  if returnsStored : plan.returns.all (storesReturn command) = true then
                    pure ⟨checked,execution,runExact,planType,resultType,typeShape,planData,resultData,dataShape,typeExact,native,decodedPlan,bytes,bytesExact,slot,rfl,augmented,augmentationExact,effects.1,effects.2,reads.1,reads.2,plan,rfl,nativeExact,returnsStored⟩
                  else throw .nativeBinding
                else throw .nativeBinding
        else throw .groundType
      | _ => throw .groundType
    | _ => throw .groundType
def prepare (deployment : CanonicalCellRegistry.Deployment)
    (loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (profile : ObjectiveBendResultAdapter.Profile) (command : Command) (source : AnnotatedTerm)
    (typeFuel : Nat) (limits : Limits) (budget : Budget) (capacity : ObjectiveBendDemandCapacity.Profile) :
    Except ObjectiveBendResultAdapter.Failure (Prepared deployment loaded profile command source limits budget capacity) := do
  let some checked := check source [] typeFuel | throw .typing
  prepareChecked deployment loaded profile command source checked limits budget capacity

end Minidregg.Compiler.ObjectiveBendGenericResult
