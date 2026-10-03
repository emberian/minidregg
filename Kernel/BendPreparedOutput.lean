/- Completed source result to the actual ordered native transaction. This gate
is below the controller, above ResourceTransaction, and owns no authority.
Current laws/signatures, whole physical writes, retained audience dependencies,
and fixed-capacity admission remain one controller acceptance. -/
import Compiler.BendPlanLowering
import Compiler.BendScalarPlanAdapter
import Compiler.BendSourceListTyped

namespace Minidregg.Kernel.BendPreparedOutput
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

def bytesCodec : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.OUTPUT-CODEC/v1".toUTF8.toList
    "exact-source-byte-list;canonical-complete-typed-Plan-frame/v1".toUTF8.toList).digest

def scalarCodec : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.OUTPUT-CODEC/v1".toUTF8.toList
    "WorldPlanScalar.PlanResult;exact-fourteen-source-definitions;native-prefix-guards/v1".toUTF8.toList).digest

/-- Full independent return records use a distinct ordinary content schema.
No assertion that clear bytes are encrypted is made by this carrier. -/
def returnSchema : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.RETURN-STORAGE/v1".toUTF8.toList []).digest

def storesReturn (command : Command) (slot : BendWorldPlan.ReturnSlot) : Bool :=
  command.targets.any fun target => match target.payload with
  | .content content => content.actions.any fun action => match action with
    | .createAtom atom (.inlineObject schema) bytes =>
      decide (atom.digest = BendWorldPlan.returnId slot ∧ schema = returnSchema ∧
        bytes = BendWorldPlan.encodeReturn slot)
    | _ => false
  | _ => false

structure ByteABI (core : BendCoreAdmission.Checked) where
  natBinding : BendSourceRepresentation.NatBookBinding core.book
  listBinding : BendSourceRepresentation.ListBookBinding core.book

def bindBytesABI (core : BendCoreAdmission.Checked) : Option (ByteABI core) :=
  if exact : BendTT.Book.get core.book "Nat.arms" = some BendSourceRepresentation.natArmsDef ∧
      BendTT.Book.get core.book "Nat" = some BendSourceRepresentation.natDef ∧
      BendTT.Book.get core.book "List.q2.arms" = some BendSourceRepresentation.listArmsDef ∧
      BendTT.Book.get core.book "List.q2" = some BendSourceRepresentation.listDef then
    some ⟨⟨exact.1,exact.2.1,core.checked⟩,
      ⟨exact.2.2.1,exact.2.2.2,core.checked⟩⟩
  else none

structure Checked {F : Type} [Field F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (source : PreparedBend command) where
  private mk ::
  plan : BendWorldPlan.Plan
  inputFamily : source.source.inputType = .Sig .Q1
    BendSourceRepresentation.listNatType BendSourceRepresentation.listNatType
  exactEffects : BendWorldPlan.matchesCommand plan command = true
  returnsStored : plan.returns.all (storesReturn command) = true
  decoded : (source.claim.outputCodec = bytesCodec ∧
      BendPlanLowering.lower source.source.source.result = some plan ∧
      Nonempty (ByteABI source.source.core) ∧
      BendTT.Term.inst source.source.outputBody source.source.input = BendSourceRepresentation.listNatType) ∨
    (source.claim.outputCodec = scalarCodec ∧
      Nonempty (BendScalarPlanAdapter.ABIBinding source.source.core.book) ∧
      BendTT.Term.inst source.source.outputBody source.source.input = .Ref "WorldPlanScalar.PlanResult" ∧
      ∃ bound : Sigma fun native => BendScalarPlanAdapter.BoundPlan deployment
          prepared.directory command native,
        BendScalarPlanAdapter.lowerResult deployment prepared.directory command
          source.source.source.result = some bound ∧ bound.2.plan = plan)

/-- Decoder selection comes from the signed claim and checked immutable profile;
there is no caller-selected fallback after a decoder refuses. -/
def check {F : Type} [Field F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (source : PreparedBend command) : Option (Checked prepared source) := do
  if family : source.source.inputType = .Sig .Q1
      BendSourceRepresentation.listNatType BendSourceRepresentation.listNatType then
    if codec : source.claim.outputCodec = bytesCodec then
      let some abi := bindBytesABI source.source.core | none
      if resultType : BendTT.Term.inst source.source.outputBody source.source.input =
          BendSourceRepresentation.listNatType then
        match decoded : BendPlanLowering.lower source.source.source.result with
        | none => none
        | some plan =>
          if exact : BendWorldPlan.matchesCommand plan command = true then
            if stored : plan.returns.all (storesReturn command) = true then
              pure ⟨plan,family,exact,stored,Or.inl ⟨codec,decoded,⟨abi⟩,resultType⟩⟩
            else none
          else none
      else none
    else if codec : source.claim.outputCodec = scalarCodec then
      let some abi := BendScalarPlanAdapter.bindABI source.source.core | none
      if resultType : BendTT.Term.inst source.source.outputBody source.source.input =
          .Ref "WorldPlanScalar.PlanResult" then
        match decoded : BendScalarPlanAdapter.lowerResult deployment prepared.directory command
          source.source.source.result with
        | none => none
        | some bound =>
          if exact : BendWorldPlan.matchesCommand bound.2.plan command = true then
            if stored : bound.2.plan.returns.all (storesReturn command) = true then
              pure ⟨bound.2.plan,family,exact,stored,
                Or.inr ⟨codec,⟨abi⟩,resultType,bound,decoded,rfl⟩⟩
            else none
          else none
      else none
    else none
  else none

/-- Native actual usage includes complete writes and all current dependencies.
Private reference source work is retained internally, never refunded publicly. -/
def usage {F : Type} [Field F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (source : PreparedBend command) (output : Checked prepared source)
    (ingress : List UInt8) (writes : List DataWrite) (guards : List ReadGuard) : ResourceCost.Charge
  | .incidences => command.targets.length + 1
  | .turnBytes => ingress.length
  | .memoryTouches => writes.length + guards.length
  | .witnessBytes => (BendTT.Term.show source.source.source.result 0).toUTF8.size +
      source.claim.arguments.length + (BendNativeInput.encodeContext ⟨command.subject,command.nonce⟩ source.observations).length
  | .proofWork => source.source.source.sourceCount
  | .storageBytes => (writes.map fun write => write.canonicalPostBytes.length).sum
  | .sideEffectCount => output.plan.effects.length
  | .feeDebit => (prepared.compute.map RunComputeBudgetDomain.Prepared.credits).getD 0
  | .networkBytes | .leaseByteBlocks => 0

structure Admitted {F : Type} [Field F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (ingress : List UInt8) (writes : List DataWrite) (guards : List ReadGuard) where
  private mk ::
  source : PreparedBend command
  sourceExact : prepared.bend = some source
  output : Checked prepared source
  readsCurrent : ∀ guard ∈ output.plan.reads, guard ∈ guards ∨
    ∃ write ∈ writes, guard.cellId = write.cellId ∧ guard.expectedRoot = write.expectedPre
  fits : usage prepared source output ingress writes guards ≤
    BendPrivateCapacity.charge source.claim.capacity

def admit {F : Type} [Field F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command}
    (prepared : PreparedInvocation deployment profile ambient durable command)
    (ingress : List UInt8) (writes : List DataWrite) (guards : List ReadGuard) :
    Except Reject (Option (Admitted prepared ingress writes guards)) :=
  match selected : prepared.bend with
  | none => .ok none
  | some source => do
    let some output := check prepared source | throw .bendExecution
    if reads : ∀ guard ∈ output.plan.reads, guard ∈ guards ∨
        ∃ write ∈ writes, guard.cellId = write.cellId ∧ guard.expectedRoot = write.expectedPre then
      if fits : usage prepared source output ingress writes guards ≤
          BendPrivateCapacity.charge source.claim.capacity then
        pure (some ⟨source,selected,output,reads,fits⟩)
      else throw .bendExecution
    else throw .bendExecution

theorem exact_effects {F : Type} [Field F]
    {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {command : Command}
    {prepared : PreparedInvocation deployment profile ambient durable command}
    {ingress : List UInt8} {writes : List DataWrite} {guards : List ReadGuard}
    (accepted : Admitted prepared ingress writes guards) :
    accepted.output.plan.effects = BendWorldPlan.effectsOf command :=
  BendWorldPlan.ordered_payloads_exact accepted.output.exactEffects

end Minidregg.Kernel.BendPreparedOutput
