/- Stack-safe circuit serialization with the SAME canonical wire identity.
Large source-compiled controllers exceed the recursive encodeMany interpreter
stack. FlatMap uses Lean's tail-recursive list implementation; these equations
prove exact byte equality, not merely successful roundtrip on a fixture. -/
import Compiler.PrivateCircuitAllocation

namespace Minidregg.Compiler.PrivateCircuitAllocationFast
open ObliviousNetwork PrivateCircuitAllocation PrivateSuccessorCustodyCodec
open Tower256ConcreteBackend
set_option autoImplicit false

theorem encodeMany_eq_flatMap {α : Type} (codec : StreamCodec α) (values : List α) :
    StreamCodec.encodeMany codec values = values.flatMap codec.encode := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [StreamCodec.encodeMany, ih]

def listBytes {α : Type} (codec : StreamCodec α) (values : List α) : List UInt8 :=
  StreamCodec.nat.encode values.length ++ values.flatMap codec.encode

theorem listBytes_exact {α : Type} (codec : StreamCodec α) (values : List α) :
    listBytes codec values = (StreamCodec.list codec).encode values := by
  simp [listBytes, StreamCodec.list, encodeMany_eq_flatMap]

def encodeNetwork (network : Network) : List UInt8 :=
  StreamCodec.nat.encode network.inputCount ++
    (listBytes opStream network.gates.toList ++ listBytes StreamCodec.nat network.outputs.toList)

theorem encodeNetwork_exact (network : Network) :
    encodeNetwork network = networkStream.encode network := by
  simp [encodeNetwork, networkStream, StreamCodec.xmap, StreamCodec.product, listBytes_exact]

def encodePlan (plan : Plan) : List UInt8 :=
  bytesStream.encode frame ++
    (generationStream.encode plan.generation ++
      (encodeNetwork plan.network ++
        (StreamCodec.nat.encode plan.publicTicks ++
          (bytesStream.encode plan.bindingBytes ++ listBytes correlationStream plan.rows))))

theorem encodePlan_exact (plan : Plan) : encodePlan plan = encode plan := by
  simp [encodePlan, encode, framedPlanStream, planStream, StreamCodec.xmap,
    StreamCodec.product, encodeNetwork_exact, listBytes_exact]

theorem decode_encodePlan (plan : Plan) : decode (encodePlan plan) = some plan := by
  rw [encodePlan_exact]
  exact decode_encode plan

/-- Tail recursion keeps the full decoded prefix in reverse order. No element
is skipped, and every underlying prefix decoder remains authoritative. -/
def decodeManyLoop {α : Type} (codec : StreamCodec α) :
    Nat → List UInt8 → List α → Option (List α × List UInt8)
  | 0, bytes, reversed => some (reversed.reverse,bytes)
  | count + 1, bytes, reversed =>
    match codec.decodePrefix bytes with
    | none => none
    | some (value,rest) => decodeManyLoop codec count rest (value :: reversed)

theorem decodeManyLoop_exact {α : Type} (codec : StreamCodec α) (count : Nat)
    (bytes : List UInt8) (reversed : List α) :
    decodeManyLoop codec count bytes reversed = (do
      let (values,suffix) ← StreamCodec.decodeMany codec count bytes
      pure (reversed.reverse ++ values,suffix)) := by
  induction count generalizing bytes reversed with
  | zero => simp [decodeManyLoop, StreamCodec.decodeMany]
  | succ count ih =>
    simp only [decodeManyLoop, StreamCodec.decodeMany]
    cases found : codec.decodePrefix bytes with
    | none => simp
    | some pair =>
      rcases pair with ⟨value,rest⟩
      change decodeManyLoop codec count rest (value :: reversed) = _
      rw [ih]
      cases tail : StreamCodec.decodeMany codec count rest with
      | none => simp [tail]
      | some pair =>
        rcases pair with ⟨values,suffix⟩
        simp [tail, List.reverse_cons, List.append_assoc]

def listDecode {α : Type} (codec : StreamCodec α) (bytes : List UInt8) :
    Option (List α × List UInt8) := do
  let (count,rest) ← StreamCodec.nat.decodePrefix bytes
  decodeManyLoop codec count rest []

theorem listDecode_exact {α : Type} (codec : StreamCodec α) (bytes : List UInt8) :
    listDecode codec bytes = (StreamCodec.list codec).decodePrefix bytes := by
  simp only [listDecode, StreamCodec.list]
  cases found : StreamCodec.nat.decodePrefix bytes with
  | none => rfl
  | some pair =>
    rcases pair with ⟨count,rest⟩
    simp [decodeManyLoop_exact]

def fastList {α : Type} (codec : StreamCodec α) : StreamCodec (List α) where
  encode := listBytes codec
  decodePrefix := listDecode codec
  decodePrefix_encode := by
    intro values suffix
    rw [listBytes_exact, listDecode_exact]
    exact (StreamCodec.list codec).decodePrefix_encode values suffix

theorem stream_ext {α : Type} {left right : StreamCodec α}
    (encoding : left.encode = right.encode) (decoding : left.decodePrefix = right.decodePrefix) :
    left = right := by
  cases left
  cases right
  cases encoding
  cases decoding
  rfl

theorem fastList_exact {α : Type} (codec : StreamCodec α) :
    fastList codec = StreamCodec.list codec := by
  have encoding : listBytes codec = (StreamCodec.list codec).encode := funext (listBytes_exact codec)
  have decoding : listDecode codec = (StreamCodec.list codec).decodePrefix := funext (listDecode_exact codec)
  exact stream_ext encoding decoding

def fastNetworkStream : StreamCodec Network :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product (fastList opStream) (fastList StreamCodec.nat)))
    (fun network => (network.inputCount, network.gates.toList, network.outputs.toList))
    (fun tuple => ⟨tuple.1, tuple.2.1.toArray, tuple.2.2.toArray⟩)
    (by intro network; cases network; simp)

theorem fastNetworkStream_exact : fastNetworkStream = networkStream := by
  simp [fastNetworkStream, networkStream, fastList_exact]

def fastPlanStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product generationStream (StreamCodec.product fastNetworkStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product bytesStream (fastList correlationStream)))))
    (fun plan => (plan.generation,plan.network,plan.publicTicks,plan.bindingBytes,plan.rows))
    (fun tuple => ⟨tuple.1,tuple.2.1,tuple.2.2.1,tuple.2.2.2.1,tuple.2.2.2.2⟩)
    (by intro plan; cases plan; rfl)

theorem fastPlanStream_exact : fastPlanStream = planStream := by
  simp [fastPlanStream, planStream, fastNetworkStream_exact, fastList_exact]

def fastFramedPlanStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product bytesStream fastPlanStream)
    (fun plan => (frame,plan)) Prod.snd (by intro plan; rfl)

theorem fastFramedPlanStream_exact : fastFramedPlanStream = framedPlanStream := by
  simp [fastFramedPlanStream, framedPlanStream, fastPlanStream_exact]

def decodePlan (bytes : List UInt8) : Option Plan := do
  let plan ← fastFramedPlanStream.toLawful.decode bytes
  if encodePlan plan == bytes then some plan else none

theorem decodePlan_exact (bytes : List UInt8) : decodePlan bytes = decode bytes := by
  simp [decodePlan, decode, fastFramedPlanStream_exact, encodePlan_exact]

theorem fast_roundtrip (plan : Plan) : decodePlan (encodePlan plan) = some plan := by
  rw [decodePlan_exact, decode_encodePlan]

#assert_axioms decodeManyLoop_exact
#assert_axioms listDecode_exact
#assert_axioms fastList_exact
#assert_axioms fastNetworkStream_exact
#assert_axioms fastPlanStream_exact
#assert_axioms fastFramedPlanStream_exact
#assert_axioms decodePlan_exact
#assert_axioms fast_roundtrip
#assert_axioms encodeMany_eq_flatMap
#assert_axioms listBytes_exact
#assert_axioms encodeNetwork_exact
#assert_axioms encodePlan_exact
#assert_axioms decode_encodePlan
end Minidregg.Compiler.PrivateCircuitAllocationFast
