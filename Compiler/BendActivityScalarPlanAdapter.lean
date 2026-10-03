/- Explicit scalar PlanResult variant of the affine Activity yield ABI. It is
selected independently of the byte-Plan ABI, never used as a fallback. Source
Book ABI binding and exact current native directory are still required by the
receiving profile. A generated Activity control leg must be checked by the
closed normalizer; this module never silently excludes a command target.
-/
import Compiler.BendActivityPlanAdapter
import Compiler.BendScalarPlanAdapter

namespace Minidregg.Compiler.BendActivityScalarPlanAdapter
open Minidregg.Theory
open BendTT TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

def activityScalarCodec : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.OUTPUT-CODEC/v1".toUTF8.toList
    "affine-Tup-Q1;WorldPlanScalar.PlanResult-first;retained-source-continuation-second/v1".toUTF8.toList).digest

structure Decoded {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (result : Term) where
  private mk ::
  planSource : Term
  continuation : Term
  exactResult : result = .Tup .Q1 planSource continuation
  native : BendScalarPlanAdapter.NativePlan
  bound : BendScalarPlanAdapter.BoundPlan deployment loaded command native
  decodedPlan : BendScalarPlanAdapter.lowerResult deployment loaded command planSource = some ⟨native,bound⟩

/-- Native scalar lowering keeps its own exact ordered command correspondence.
A command carrying an extra unchecked Activity write therefore refuses here;
the closed current-control normalization must account for that write explicitly. -/
def lower {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    (deployment : CanonicalCellRegistry.Deployment)
    (loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (command : Command) (result : Term) : Option (Decoded deployment loaded command result) :=
  match shape : result with
  | .Tup .Q1 planSource continuation =>
      match decoded : BendScalarPlanAdapter.lowerResult deployment loaded command planSource with
      | none => none
      | some bound => some ⟨planSource,continuation,shape,bound.1,bound.2,decoded⟩
  | _ => none

theorem full_result {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {result : Term} (decoded : Decoded deployment loaded command result) :
    result = .Tup .Q1 decoded.planSource decoded.continuation := decoded.exactResult

theorem ordered_effects {durable : DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes}
    {deployment : CanonicalCellRegistry.Deployment}
    {loaded : CredentialAuthorityDomainReceiver.LoadedDirectory durable}
    {command : Command} {result : Term} (decoded : Decoded deployment loaded command result) :
    decoded.bound.plan.effects = BendWorldPlan.effectsOf command :=
  BendScalarPlanAdapter.exact_native_effects decoded.bound

#assert_axioms lower
#assert_axioms full_result
#assert_axioms ordered_effects
end Minidregg.Compiler.BendActivityScalarPlanAdapter
