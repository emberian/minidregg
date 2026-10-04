/- Objective closed ground returns. Profile metadata comes from the independently
accepted native method/profile, not a returned record or caller-selected mask.
This producer creates clear content effects, never encryption or authority. -/
import Theory.ObjectiveBendTyping
import Theory.ObjectiveBendDemandCapacity
import Compiler.BendWorldPlan
namespace Minidregg.Compiler.ObjectiveBendResultAdapter
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open ObjectiveBendTypes ObjectiveBendTyping ObjectiveBendDemandMachine ObjectiveBendDemandData
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

structure Profile where
  sourceArtifact : Digest
  selectedDeclaration : Digest
  sourceEntry : String
  name : String
  recipient : TypedAuthorization.SubjectId
  keyEpoch : Digest
  audience : Digest
  generation : Nat
  target : Nat
  deriving Repr

def codecId : Digest := (Sp800185Cshake256.hash
  "DREGG.OBJECTIVE-BEND.RESULT-CODEC/v1".toUTF8.toList
  "complete-checked-ground-data;ordered-record;canonical-DemandData/v1;clear-return-slot;profile-selected-metadata".toUTF8.toList).digest

def storageSchema : Digest := (Sp800185Cshake256.hash
  "DREGG.OBJECTIVE-BEND.RETURN-STORAGE/v1".toUTF8.toList []).digest

def valueSchema (profile : Profile) (type : Ty) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.RESULT-VALUE/v1".toUTF8.toList
    (digestStream.encode profile.sourceArtifact ++ digestStream.encode profile.selectedDeclaration ++ digestStream.encode codecId ++
      PolicyRecordCodec.stringStream.encode profile.sourceEntry ++
      (typeJson type).compress.toUTF8.toList)).digest

/-- Explicit ground type check supplements the annotated checker until general
preservation/demand adequacy is established. Executable/custody types refuse. -/
def dataMatches : Nat → Ty → Data → Bool
  | 0,_,_ => false
  | _+1,.natural,.natural _ => true
  | _+1,.boolean,.boolean _ => true
  | _+1,.label,.label _ => true
  | _+1,.emptyRow,.record [] => true
  | fuel+1,.field name member tail,.record ((key,value)::rest) =>
      name == key && dataMatches fuel member value && dataMatches fuel tail (.record rest)
  | _,_,_ => false

def dataFrame : List UInt8 := "DREGG/OBJECTIVE-BEND/CLEAR-DATA/v1".toUTF8.toList
def encodeData (depth : Nat) (value : Data) : Option (List UInt8) :=
  (encoded depth value).map (fun bytes => dataFrame ++ bytes)

/-- Read a canonical decimal prefix before constructing a Nat. -/
def readNatural (capacity : ObjectiveBendDemandCapacity.Profile) (bytes : List UInt8) :
    Option (Nat × List UInt8) := do
  let digits := bytes.takeWhile (fun byte => byte != 0)
  let 0 :: rest := bytes.drop digits.length | none
  let text ← String.fromUTF8? ⟨digits.toArray⟩
  let .ok value := ObjectiveBendDemandCapacity.decodeNatural capacity text | none
  pure (value,rest)

mutual
  def readData (capacity : ObjectiveBendDemandCapacity.Profile) :
      Nat → List UInt8 → Option (Data × List UInt8)
    | 0,_ => none
    | _+1,0::bytes => do
        let (value,rest) ← readNatural capacity bytes
        pure (.natural value,rest)
    | _+1,1::0::rest => some (.boolean false,rest)
    | _+1,1::1::rest => some (.boolean true,rest)
    | _+1,2::bytes => do
        let (size,rest) ← readNatural capacity bytes
        if size > rest.length then none else do
          let value ← String.fromUTF8? ⟨(rest.take size).toArray⟩
          pure (.label value,rest.drop size)
    | fuel+1,3::bytes => do
        let (count,rest) ← readNatural capacity bytes
        let (fields,tail) ← readFields capacity fuel count rest
        pure (.record fields,tail)
    | _,_ => none
  termination_by fuel _ => (fuel,0,0)
  def readFields (capacity : ObjectiveBendDemandCapacity.Profile) :
      Nat → Nat → List UInt8 → Option (List (String × Data) × List UInt8)
    | _,0,bytes => some ([],bytes)
    | fuel,count+1,bytes => do
        let (size,rest) ← readNatural capacity bytes
        if size > rest.length then none else do
          let name ← String.fromUTF8? ⟨(rest.take size).toArray⟩
          let (value,tail) ← readData capacity fuel (rest.drop size)
          let (fields,tail) ← readFields capacity fuel count tail
          if fields.any (fun field => field.1 == name) then none else
            pure ((name,value)::fields,tail)
  termination_by fuel count _ => (fuel,1,count)
end

def dataNodes : Nat → Data → Option Nat
  | 0,_ => none
  | _+1,.natural _ | _+1,.boolean _ | _+1,.label _ => some 1
  | fuel+1,.record fields => do
      let nodes ← fields.mapM (fun field => dataNodes fuel field.2)
      pure (1 + nodes.foldl (·+·) 0)

def decodeData (capacity : ObjectiveBendDemandCapacity.Profile) (budget : Budget)
    (bytes : List UInt8) : Option Data := do
  if bytes.length > budget.bytes || bytes.take dataFrame.length != dataFrame then none else do
    let (value,rest) ← readData capacity budget.nodes (bytes.drop dataFrame.length)
    let nodes ← dataNodes budget.nodes value
    if !rest.isEmpty || nodes > budget.nodes then none else
      if encodeData budget.nodes value == some bytes then some value else none

def returnSlot (profile : Profile) (type : Ty) (bytes : List UInt8) : BendWorldPlan.ReturnSlot :=
  ⟨profile.name,valueSchema profile type,codecId,profile.recipient,
    profile.keyEpoch,profile.audience,profile.generation,bytes⟩

/-- An independently selected expected profile/type is required at readback.
Stored bytes cannot select a codec, recipient, source identity or audience. -/
def decodeStoredReturn (profile : Profile) (type : Ty)
    (capacity : ObjectiveBendDemandCapacity.Profile) (budget : Budget)
    (atom : Digest) (schema : Digest) (bytes : List UInt8) : Option Data := do
  if schema != storageSchema || bytes.length > budget.bytes then none else do
    -- Compare independently expected metadata BEFORE decoding any wire Nat.
    let empty := BendWorldPlan.encodeReturn (returnSlot profile type [])
    let header := empty.take (empty.length - (bytesStream.encode []).length)
    if bytes.take header.length != header then none else do
      let afterHeader := bytes.drop header.length
      let digits := afterHeader.takeWhile (fun byte => byte != 255)
      if digits.length+1 > (StreamCodec.nat.encode budget.bytes).length then none else do
        let (count,payload) ← StreamCodec.nat.decodePrefix afterHeader
        if count > budget.bytes || count != payload.length then none else do
          let slot := returnSlot profile type payload
          if BendWorldPlan.encodeReturn slot != bytes || atom != BendWorldPlan.returnId slot then none else do
            let value ← decodeData capacity budget payload
            if dataMatches budget.nodes type value then some value else none

def returnEffect (profile : Profile) (slot : BendWorldPlan.ReturnSlot) : BendWorldPlan.Effect :=
  ⟨profile.target,.content ⟨[.createAtom ⟨BendWorldPlan.returnId slot⟩
    (.inlineObject storageSchema) (BendWorldPlan.encodeReturn slot)]⟩⟩

def storesReturn (command : Command) (slot : BendWorldPlan.ReturnSlot) : Bool :=
  command.targets.any fun target => match target.payload with
  | .content content => content.actions.any fun action => match action with
    | .createAtom atom (.inlineObject schema) bytes =>
      decide (atom.digest = BendWorldPlan.returnId slot ∧ schema = storageSchema ∧
        bytes = BendWorldPlan.encodeReturn slot)
    | _ => false
  | _ => false

structure PreparedResult (profile : Profile) (command : Command) (source : AnnotatedTerm)
    (limits : Limits) (budget : Budget) (capacity : ObjectiveBendDemandCapacity.Profile) where
  private mk ::
  checked : Checked source []
  execution : ExecutionWith (ObjectiveBendDemandCapacity.allows capacity) limits budget source.term
  runExact : executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget source.term = .ok execution
  bytes : List UInt8
  bytesExact : encodeData budget.nodes execution.extraction.result.value = some bytes
  decoded : Data
  decodedExact : decodeData capacity budget bytes = some decoded
  decodedBytesExact : encodeData budget.nodes decoded = some bytes
  typeExact : dataMatches budget.nodes checked.type execution.extraction.result.value = true
  slot : BendWorldPlan.ReturnSlot
  slotExact : slot = returnSlot profile checked.type bytes
  plan : BendWorldPlan.Plan
  planExact : plan = ⟨[returnEffect profile slot],[slot],[]⟩
  nativeExact : BendWorldPlan.matchesCommand plan command = true
  returnsStored : plan.returns.all (storesReturn command) = true

inductive Failure where
  | typing | execution (reason : ObjectiveBendDemandData.Failure) (state : State)
  | groundType | bytes | nativeBinding
  deriving Repr

def prepare (profile : Profile) (command : Command) (source : AnnotatedTerm)
    (typeFuel : Nat) (limits : Limits) (budget : Budget)
    (capacity : ObjectiveBendDemandCapacity.Profile) :
    Except Failure (PreparedResult profile command source limits budget capacity) := do
  let some checked := check source [] typeFuel | throw .typing
  match runExact : executeWith (ObjectiveBendDemandCapacity.allows capacity) limits budget source.term with
  | .error error => throw (.execution error.1 error.2)
  | .ok execution =>
    if typeExact : dataMatches budget.nodes checked.type execution.extraction.result.value = true then
      match bytesExact : encodeData budget.nodes execution.extraction.result.value with
      | none => throw .bytes
      | some bytes =>
        if bytes.length > budget.bytes then throw (.execution .budget execution.extraction.result.state)
        match decodedExact : decodeData capacity budget bytes with
        | none => throw .bytes
        | some decoded =>
          if decodedBytesExact : encodeData budget.nodes decoded = some bytes then
            let slot := returnSlot profile checked.type bytes
            let plan : BendWorldPlan.Plan := ⟨[returnEffect profile slot],[slot],[]⟩
            let producedBytes := (plan.effects.map (fun effect => BendWorldPlan.effectStream.encode effect)).flatten.length + (BendWorldPlan.encodeReturn slot).length
            if producedBytes > budget.bytes then throw (.execution .budget execution.extraction.result.state)
            if nativeExact : BendWorldPlan.matchesCommand plan command = true then
              if returnsStored : plan.returns.all (storesReturn command) = true then
                pure ⟨checked,execution,runExact,bytes,bytesExact,decoded,decodedExact,decodedBytesExact,typeExact,slot,rfl,plan,rfl,nativeExact,returnsStored⟩
              else throw .nativeBinding
            else throw .nativeBinding
          else throw .bytes
    else throw .groundType
end Minidregg.Compiler.ObjectiveBendResultAdapter
