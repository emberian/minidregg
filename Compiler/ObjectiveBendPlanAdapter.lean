/- Core4 scalar-record ABI to the existing complete guarded native Plan binder.
This decoder confers no authority. Current source/family/law/capacity admission
remains the native receiver's responsibility. No returns in this explicit slice. -/
import Theory.ObjectiveBendDemandData
import Compiler.ObjectiveNativeScalarBinding
namespace Minidregg.Compiler.ObjectiveBendPlanAdapter
open Minidregg.Theory.ObjectiveBendDemandData
open ObjectiveNativeScalarBinding
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

/-- Exact public scalar-record output schema. Receiver registration must pin
this identity; a matching backend name cannot select a different decoder. -/
def codecId : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.SCALAR-RECORD/v1".toUTF8.toList
    "Core4:data;Plan=record[reads,effects];ordinal=contiguous-decimal-zero-based;Ref=record[resource:Nat,root:canonical-lowerhex-digestStream];Write=record[ref,field:Nat,before:Nat,after:Nat];same-resource-ordered-group;conflicting-root-refuse;no-extra-fields;no-returns;no-authority".toUTF8.toList).digest

def nibble (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat-'0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat-'a'.toNat+10)
  else none

def unhex : List Char → Option (List UInt8)
  | [] => some []
  | a::b::rest => do
    let hi ← nibble a
    let lo ← nibble b
    pure (UInt8.ofNat (hi*16+lo)::(← unhex rest))
  | _ => none

def natural : Data → Option Nat | .natural n => some n | _ => none

def reference : Data → Option Ref
  | .record [("resource",r),("root",.label root)] => do
    let resource ← natural r
    let bytes ← unhex root.toList
    let digest ← rootCodec.decode bytes
    pure ⟨resource,digest⟩
  | _ => none

def write : Data → Option Scalar
  | .record [("ref",r),("field",f),("before",b),("after",a)] => do
    let ref ← reference r
    pure ⟨ref,[⟨← natural f,← natural b,← natural a⟩]⟩
  | _ => none

def ordered {α : Type} (decode : Data → Option α) : Nat → List (String × Data) → Option (List α)
  | _,[] => some []
  | index,(name,value)::rest => do
    if name != toString index then none else
      pure ((← decode value)::(← ordered decode (index+1) rest))

def records {α : Type} (decode : Data → Option α) : Data → Option (List α)
  | .record fields => ordered decode 0 fields
  | _ => none

/-- Multiple writes to one resource are grouped in first-occurrence order;
conflicting roots refuse. The existing binder checks fields/preimages/roles. -/
def group (effects : List Scalar) : Option (List Scalar) :=
  effects.foldlM (fun prior next =>
    match prior.find? (fun p => p.ref.resourceID == next.ref.resourceID) with
    | none => some (prior ++ [next])
    | some found => if found.ref.root != next.ref.root then none else
      some (prior.map fun p => if p.ref.resourceID == next.ref.resourceID then
        {p with writes:=p.writes++next.writes} else p)) []

def decode : Data → Option NativePlan
  | .record [("reads",reads),("effects",effects)] => do
    pure ⟨← records reference reads,← group (← records write effects)⟩
  | _ => none

/-- Consume full data rather than a weak-head record. The caller must retain
the actual checked source execution/materialization evidence; this pure adapter
does not certify origin or current authority for a caller-constructed Result. -/
def lower (deployment : CanonicalCellRegistry.Deployment)
    (loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (command : Command)
    {limits : Minidregg.Theory.ObjectiveBendDemandMachine.Limits}
    {budget : Budget} {state : Minidregg.Theory.ObjectiveBendDemandMachine.State}
    {policy : Minidregg.Theory.ObjectiveBendDemandMachine.State → Bool}
    (extraction : ExtractionWith policy limits budget state) :
    Option (Sigma fun source => BoundPlan deployment loaded command source) := do
  let source ← decode extraction.result.value
  pure ⟨source,← bindPlan deployment loaded command source⟩
end Minidregg.Compiler.ObjectiveBendPlanAdapter
