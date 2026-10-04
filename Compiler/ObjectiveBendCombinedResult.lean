/- Same-source typed {plan,result} envelope. Current effect coverage is the
strict scalar-record ABI; return storage is appended without dropping original
ordered application effects or physical reads. Current authority/funding belong
to the native gate; this token cannot accept a caller-authored Plan. -/
import Compiler.ObjectiveBendResultAdapter
import Compiler.ObjectiveBendPlanAdapter
namespace Minidregg.Compiler.ObjectiveBendCombinedResult
open Minidregg.Theory Minidregg.Theory.TypedAuthorization
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendDemandMachine ObjectiveBendDemandData
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
open ObjectiveBendResultAdapter ObjectiveNativeScalarBinding
set_option autoImplicit false

structure Prepared {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
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
  native : NativePlan
  decodedPlan : ObjectiveBendPlanAdapter.decode planData = some native
  effects : List BendWorldPlan.Effect
  ordered : Ordered deployment loaded command native.effects effects
  reads : List ReadGuard
  orderedReads : OrderedReads loaded native.reads reads
  bytes : List UInt8
  bytesExact : encodeData budget.nodes resultData = some bytes
  slot : BendWorldPlan.ReturnSlot
  slotExact : slot = returnSlot profile resultType bytes
  plan : BendWorldPlan.Plan
  planExact : plan = ⟨effects++[returnEffect profile slot],[slot],reads⟩
  nativeExact : BendWorldPlan.matchesCommand plan command = true
  returnsStored : plan.returns.all (storesReturn command) = true

def prepare {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (profile : ObjectiveBendResultAdapter.Profile) (command : Command) (source : AnnotatedTerm)
    (typeFuel : Nat) (limits : Limits) (budget : Budget) (capacity : ObjectiveBendDemandCapacity.Profile) :
    Except ObjectiveBendResultAdapter.Failure (Prepared deployment loaded profile command source limits budget capacity) := do
  let some checked := check source [] typeFuel | throw .typing
  match runExact : executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget source.term with
  | .error error => throw (.execution error.1 error.2)
  | .ok execution =>
    match typeShape : checked.type with
    | .field "plan" planType (.field "result" resultType .emptyRow) =>
      match dataShape : execution.extraction.result.value with
      | .record [("plan",planData),("result",resultData)] =>
        if typeExact : dataMatches budget.nodes checked.type execution.extraction.result.value = true then
          match decodedPlan : ObjectiveBendPlanAdapter.decode planData with
          | none => throw .nativeBinding
          | some native =>
            if !(decide (command.targets.map Target.target).Nodup) ||
                !(decide (native.effects.map (fun effect=>effect.ref.resourceID)).Nodup) then throw .nativeBinding
            let some effects := bindOrdered deployment loaded command native.effects | throw .nativeBinding
            let some reads := bindReads loaded native.reads | throw .nativeBinding
            match bytesExact : encodeData budget.nodes resultData with
            | none => throw .bytes
            | some bytes =>
              let slot := returnSlot profile resultType bytes
              let plan : BendWorldPlan.Plan := ⟨effects.1++[returnEffect profile slot],[slot],reads.1⟩
              let producedBytes := (plan.effects.map (fun effect=>BendWorldPlan.effectStream.encode effect)).flatten.length + (BendWorldPlan.encodeReturn slot).length
              if producedBytes > budget.bytes then throw (.execution .budget execution.extraction.result.state)
              if nativeExact : BendWorldPlan.matchesCommand plan command = true then
                if returnsStored : plan.returns.all (storesReturn command) = true then
                  pure ⟨checked,execution,runExact,planType,resultType,typeShape,planData,resultData,dataShape,typeExact,native,decodedPlan,effects.1,effects.2,reads.1,reads.2,bytes,bytesExact,slot,rfl,plan,rfl,nativeExact,returnsStored⟩
                else throw .nativeBinding
              else throw .nativeBinding
        else throw .groundType
      | _ => throw .groundType
    | _ => throw .groundType
end Minidregg.Compiler.ObjectiveBendCombinedResult
