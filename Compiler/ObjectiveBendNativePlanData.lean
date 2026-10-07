/- Typed source-data constructor decoding into EXISTING native payloads.
No effect evaluator lives here. Native current laws, execution, atomic physical
writes and funding remain the actual receiving transaction's obligations.
Current constructor registry: ordered content createDocument/createAtom and
room-stream append. Other constructors are unsupported, never scalar-coerced. -/
import Compiler.ObjectiveBendResultAdapter
import Compiler.ObjectiveBendPlanAdapter
namespace Minidregg.Compiler.ObjectiveBendNativePlanData
open Minidregg.Theory Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Compiler.Tower256ConcreteBackend
open ObjectiveNativeScalarBinding
set_option autoImplicit false

def codecId : Digest := (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.NATIVE-DATA-PLAN/v1".toUTF8.toList
  "Ref:resource,canonical-lowerhex-root;Plan:reads,effects;Effect:ref,payload;ordered-contiguous-ordinals;content:createDocument,createAtom-inlineObject;append:topic,payload,recipient,ref;byteNat<256;canonical-native-payloadStream;unsupported-constructor-refusal;no-authority".toUTF8.toList).digest

def natural (capacity : ObjectiveBendDemandCapacity.Profile) : Data → Option Nat
  | .natural value => if ObjectiveBendDemandCapacity.bits value ≤ capacity.scalarBits then some value else none
  | _ => none

def digest (capacity : ObjectiveBendDemandCapacity.Profile) : Data → Option Digest
  | .label text => do
      -- Digest wire is compact Nat plus terminator. Bound bytes BEFORE Nat parsing.
      if text.utf8ByteSize > 2*(capacity.scalarBits/8+1) then none else do
        let bytes ← ObjectiveBendPlanAdapter.unhex text.toList
        rootCodec.decode bytes
  | _ => none

/-- Conservative native Digest conversion capacity, checked before parsing.
The output graph has already been globally bounded/forced by the same source
execution. Oversized digest conversion is suspension, not invalid source. -/
def digestCapacity : Nat → ObjectiveBendDemandCapacity.Profile → Data → Bool
  | 0,_,_ => false
  | fuel+1,capacity,.record fields => fields.all (fun field =>
      let localFit := match field.2 with
        | .label text => if field.1 == "root" || field.1 == "atom" || field.1 == "schema" then
            text.utf8ByteSize ≤ 2*(capacity.scalarBits/8+1) else true
        | _ => true
      localFit && digestCapacity fuel capacity field.2)
  | _+1,_,_ => true

def reference (capacity : ObjectiveBendDemandCapacity.Profile) : Data → Option Ref
  | .record [("resource",resource),("root",root)] => do
      pure ⟨← natural capacity resource,← digest capacity root⟩
  | _ => none

def byte : Data → Option UInt8
  | .natural value => if value < 256 then some (UInt8.ofNat value) else none
  | _ => none

def bytes (value : Data) : Option (List UInt8) := ObjectiveBendPlanAdapter.records byte value

def contentAction (capacity : ObjectiveBendDemandCapacity.Profile) : Data → Option Minidregg.Kernel.ContentResource.Action
  | .record [("kind",.label "createDocument"),("root",root),("schema",schema)] => do
      pure (.createDocument ⟨← digest capacity root⟩ (← digest capacity schema))
  | .record [("kind",.label "createAtom"),("atom",atom),("schema",schema),("bytes",body)] => do
      pure (.createAtom ⟨← digest capacity atom⟩ (.inlineObject (← digest capacity schema)) (← bytes body))
  | _ => none

def recipient (capacity : ObjectiveBendDemandCapacity.Profile) : Data → Option (Option SubjectId)
  | .label "none" => some none
  | value => (natural capacity value).map (fun n => some ⟨n⟩)

def messageRef (capacity : ObjectiveBendDemandCapacity.Profile) : Data → Option (Option (Nat × Nat))
  | .label "none" => some none
  | .record [("resource",resource),("position",position)] => do
      pure (some (← natural capacity resource,← natural capacity position))
  | _ => none

def payload (capacity : ObjectiveBendDemandCapacity.Profile) : Data → Option Payload
  | .record [("kind",.label "content"),("actions",actions)] => do
      let actions ← ObjectiveBendPlanAdapter.records (contentAction capacity) actions
      pure (.content ⟨actions⟩)
  | .record [("kind",.label "append"),("topic",topic),("payload",body),("recipient",who),("ref",ref)] => do
      let topic ← bytes topic
      let body ← bytes body
      if topic.length > StreamCell.maxTopicBytes || body.length > StreamCell.maxPayloadBytes then none else
        pure (.append ⟨topic,body,← recipient capacity who,← messageRef capacity ref⟩)
  | _ => none

structure Effect where
  ref : Ref
  payload : Payload
  canonical : payloadStream.toLawful.decode (payloadStream.encode payload) = some payload

structure NativePlan where
  reads : List Ref
  effects : List Effect

def effect (capacity : ObjectiveBendDemandCapacity.Profile) : Data → Option Effect
  | .record [("ref",ref),("payload",body)] => do
      let ref ← reference capacity ref
      let body ← payload capacity body
      pure ⟨ref,body,payloadStream.toLawful.decode_encode body⟩
  | _ => none

def decode (capacity : ObjectiveBendDemandCapacity.Profile) : Data → Option NativePlan
  | .record [("reads",reads),("effects",effects)] => do
      pure ⟨← ObjectiveBendPlanAdapter.records (reference capacity) reads,
        ← ObjectiveBendPlanAdapter.records (effect capacity) effects⟩
  | _ => none

structure BoundEffect (deployment : CanonicalCellRegistry.Deployment)
    (loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (command : Command) (source : Effect) where
  private mk ::
  index : Fin command.targets.length
  indexExact : indexOf command source.ref.resourceID = some index
  read : BoundRead loaded source.ref
  roleExact : command.targets[index].kind = .object
  rootExact : command.targets[index].expectedTargetRoot = source.ref.root
  payloadExact : command.targets[index].payload = source.payload
  pre : TargetCell command.targets[index]
  selected : selectTarget deployment command.targets[index] read.packed = some pre

def BoundEffect.native {deployment : CanonicalCellRegistry.Deployment}
    {loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry}
    {command : Command} {source : Effect}
    (bound : BoundEffect deployment loaded command source) : BendWorldPlan.Effect :=
  ⟨bound.index.val,source.payload⟩

def bindEffect (deployment : CanonicalCellRegistry.Deployment)
    (loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (command : Command) (source : Effect) : Option (BoundEffect deployment loaded command source) := do
  match indexExact : indexOf command source.ref.resourceID with
  | none => none
  | some index =>
    let read ← bindRead loaded source.ref
    if roleExact : command.targets[index].kind = .object then
      if rootExact : command.targets[index].expectedTargetRoot = source.ref.root then
        if payloadExact : command.targets[index].payload = source.payload then
          let chosen : Option (TargetCell command.targets[index]) := selectTarget deployment command.targets[index] read.packed
          match selected : chosen with
          | none => none
          | some pre => some ⟨index,indexExact,read,roleExact,rootExact,payloadExact,pre,selected⟩
        else none
      else none
    else none

inductive Ordered (deployment : CanonicalCellRegistry.Deployment)
    (loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (command : Command) : List Effect → List BendWorldPlan.Effect → Type where
  | nil : Ordered deployment loaded command [] []
  | cons {source : Effect} {rest : List Effect} {effects : List BendWorldPlan.Effect}
      (bound : BoundEffect deployment loaded command source)
      (tail : Ordered deployment loaded command rest effects) :
      Ordered deployment loaded command (source::rest) (bound.native::effects)

def bindOrdered (deployment : CanonicalCellRegistry.Deployment)
    (loaded : Minidregg.Theory.CellRegistry.Directory Nat CanonicalCellRegistry.registry)
    (command : Command) : (effects : List Effect) →
    Option (Sigma fun native => Ordered deployment loaded command effects native)
  | [] => some ⟨[],.nil⟩
  | source::rest => do
      let bound ← bindEffect deployment loaded command source
      let tail ← bindOrdered deployment loaded command rest
      pure ⟨bound.native::tail.1,.cons bound tail.2⟩
end Minidregg.Compiler.ObjectiveBendNativePlanData
