/- The deployed D2 storage unit is the encoding of newly written values.
Transport frames, keys, old values, reads and frees are not value writes.
The complete turn encoding separately binds every guard and effect. -/
import Kernel.DeployedBridge
import Kernel.WorldRoot
import Compiler.DurableReceiverCodec

namespace Minidregg.Kernel.DeployedHistory

open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.World
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent (TransactionId StableEvent)

set_option autoImplicit false

/-- D2: only the new value of an allocation or write consumes storage bytes. -/
def opBytes (k : deployedR.Kind) : Op (deployedR.layout k) → Nat
  | .read _ _ _ => 0
  | .free _ _ _ => 0
  | .allocate ns _ value => ((wireOf k).valueStream ns |>.encode value).length
  | .write ns _ _ value => ((wireOf k).valueStream ns |>.encode value).length

/-- The deployed leg accounting, including non-OB kinds. -/
def legBytes (leg : Leg deployedR) : Nat := (leg.patch.map (opBytes leg.kind)).sum

/-- Birth images charge only present values; an empty RAM birth costs zero. -/
def imageBytes (cell : Cell deployedR) : Nat :=
  ((StoreCodec.entries (wireOf cell.kind) cell.store).map fun e =>
    ((wireOf cell.kind).valueStream e.1.1 |>.encode e.2).length).sum

/-- Framed op bytes for the journal digest, distinct from D2's value charge. -/
def encodeOp (k : deployedR.Kind) (op : Op (deployedR.layout k)) : List UInt8 :=
  let w := wireOf k
  match op with
  | .read ns key value => [0] ++ w.namespaceStream.encode ns ++ (w.keyStream ns).encode key ++
      (StreamCodec.option (w.valueStream ns)).encode value
  | .write ns key old value => [1] ++ w.namespaceStream.encode ns ++ (w.keyStream ns).encode key ++
      (w.valueStream ns).encode old ++ (w.valueStream ns).encode value
  | .allocate ns key value => [2] ++ w.namespaceStream.encode ns ++ (w.keyStream ns).encode key ++
      (w.valueStream ns).encode value
  | .free ns key old => [3] ++ w.namespaceStream.encode ns ++ (w.keyStream ns).encode key ++
      (w.valueStream ns).encode old

def encodeLeg (leg : Leg deployedR) : List UInt8 :=
  StreamCodec.nat.encode leg.cell ++ [CanonicalCellRegistry.Kind.tag leg.kind] ++
    (StreamCodec.list bytesStream).encode (leg.patch.map (encodeOp leg.kind))

/-- All fields other than absence pins, each in a length-delimited slot. -/
def turnFields (t : DTurn deployedR Digest) : List (List UInt8) :=
  [digestStream.encode t.txId,
   (StreamCodec.list bytesStream).encode (t.creates.map fun c =>
     StreamCodec.nat.encode c.1 ++ bytesStream.encode (encodeCell (some c.2.1)) ++
       (StreamCodec.option StreamCodec.nat).encode c.2.2),
   (StreamCodec.list bytesStream).encode (t.legs.map encodeLeg),
   (StreamCodec.list StreamCodec.nat).encode t.retires,
   DurableReceiverCodec.eventStream.encode t.event,
   (StreamCodec.list digestStream).encode t.nullifiers,
   DurableReceiverCodec.chargeStream.encode t.charge,
   (StreamCodec.option DurableReceiverCodec.subjectStream).encode t.subject,
   StreamCodec.nat.encode t.keyEpoch,
   (StreamCodec.option digestStream).encode t.capability,
   StreamCodec.nat.encode t.notBefore,
   (StreamCodec.option StreamCodec.nat).encode t.validUntil]

/-- Greenfield v2 turn shape: absence pins are in the digest preimage. -/
def encodeTurn (t : DTurn deployedR Digest) : List UInt8 :=
  (StreamCodec.product (StreamCodec.list StreamCodec.nat) (StreamCodec.list bytesStream)).encode
    (t.absent, turnFields t)

/-- Equal turn bytes imply equal absence pins: no field outside the digest. -/
theorem encodeTurn_absent {a b : DTurn deployedR Digest}
    (same : encodeTurn a = encodeTurn b) : a.absent = b.absent :=
  (Prod.mk.inj (StoreCodec.streamEncode_injective _ same)).1

/-- The pinned deployed history: cSHAKE turn digest/log chain and written-value bytes. -/
def history : History deployedR TransactionId StableEvent Digest :=
  WorldRoot.cshakeHistory encodeTurn ⟨0⟩ legBytes imageBytes

/-- A whole-blob allocation charges exactly its newly encoded payload. -/
theorem objective_allocate_bytes (c : CellId) (payload : ObjectiveActivityCell.Payload) :
    legBytes ⟨c, .objectiveActivity, [.allocate () () payload]⟩ =
      (ObjectiveActivityCell.payloadStream.encode payload).length := by
  simp [legBytes, opBytes, wireOf, objectiveActivityWire]

/-- Updating a whole blob never charges the old payload. -/
theorem objective_write_bytes (c : CellId) (old payload : ObjectiveActivityCell.Payload) :
    legBytes ⟨c, .objectiveActivity, [.write () () old payload]⟩ =
      (ObjectiveActivityCell.payloadStream.encode payload).length := by
  simp [legBytes, opBytes, wireOf, objectiveActivityWire]

/-- A free writes no values. -/
theorem objective_free_bytes (c : CellId) (old : ObjectiveActivityCell.Payload) :
    legBytes ⟨c, .objectiveActivity, [.free () () old]⟩ = 0 := rfl

/-- Guard-only legs charge no storage. -/
theorem read_bytes (c : CellId) (k : deployedR.Kind) (ns : (deployedR.layout k).Namespace)
    (key : (deployedR.layout k).Key ns) (value : Option ((deployedR.layout k).Value ns)) :
    legBytes ⟨c, k, [.read ns key value]⟩ = 0 := rfl

/-- The receiver's live post image has 40 bytes beyond the encoded payload:
4 lifecycle + 4 registry + 29 protected frame + 2 version + 1 presence tag. -/
theorem objective_post_bytes (payload : ObjectiveActivityCell.Payload) :
    (encodeCell (some ⟨.objectiveActivity,
      ProtectedCell.stateOfOption ObjectiveActivityCell.spec (some payload)⟩)).length =
      (ObjectiveActivityCell.payloadStream.encode payload).length + 40 := by
  change (List.append [68,82,2,1] (List.append [68,82,1,19]
    (ObjectiveActivityCell.spec.wireFrame ++
      (ProtectedCell.wirePayloadStream ObjectiveActivityCell.spec).encode
        (1, some payload)))).length = _
  have frameLength : "DREGG/OBJECTIVE/ACTIVITY-CELL".toByteArray.toList.length = 29 := by decide +kernel
  have versionLength : (StreamCodec.nat.encode 1).length = 2 := rfl
  simp [ProtectedCell.wirePayloadStream, StreamCodec.product, StreamCodec.option,
    ObjectiveActivityCell.spec, ObjectiveActivityCell.payloadStream, frameLength, versionLength,
    List.length_append, List.length_cons, List.length_nil]
  omega

/-- Allocation cannot exceed the receiver's full-image storage charge. -/
theorem objective_allocate_below_post (c : CellId) (payload : ObjectiveActivityCell.Payload) :
    legBytes ⟨c, .objectiveActivity, [.allocate () () payload]⟩ <
      (encodeCell (some ⟨.objectiveActivity,
        ProtectedCell.stateOfOption ObjectiveActivityCell.spec (some payload)⟩)).length := by
  rw [objective_allocate_bytes, objective_post_bytes]
  omega

/-- Every empty birth image charges zero, without a zero-history shortcut. -/
theorem imageBytes_empty (k : deployedR.Kind) : imageBytes ⟨k, 0⟩ = 0 := by
  simp [imageBytes, StoreCodec.entries, StoreCodec.sortedSupport_eq]

/-- RAM payloads have no ROM birth image: allocation is charged exactly once. -/
theorem objective_romPart_empty (s : Store ObjectiveActivityCell.layout) : romPart s = 0 := by
  apply DFinsupp.ext
  intro a
  rw [romPart_apply]
  rfl

theorem objective_birth_image_bytes (s : Store ObjectiveActivityCell.layout) :
    imageBytes ⟨.objectiveActivity, romPart s⟩ = 0 := by
  have empty : @romPart (deployedR.layout .objectiveActivity) s = 0 := objective_romPart_empty s
  simp only [empty, imageBytes_empty]

theorem objective_write_below_post (c : CellId) (old payload : ObjectiveActivityCell.Payload) :
    legBytes ⟨c, .objectiveActivity, [.write () () old payload]⟩ <
      (encodeCell (some ⟨.objectiveActivity,
        ProtectedCell.stateOfOption ObjectiveActivityCell.spec (some payload)⟩)).length := by
  rw [objective_write_bytes, objective_post_bytes]
  omega

/-- Retirement transports four tombstone bytes while a free writes zero value bytes. -/
theorem objective_free_below_retired (c : CellId) (old : ObjectiveActivityCell.Payload) :
    legBytes ⟨c, .objectiveActivity, [.free () () old]⟩ + 4 =
      (ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry .retired).length := rfl

#assert_axioms imageBytes_empty objective_romPart_empty objective_birth_image_bytes
#assert_axioms objective_write_below_post objective_free_below_retired

#assert_axioms encodeTurn_absent
#assert_axioms objective_allocate_bytes objective_write_bytes objective_free_bytes read_bytes
#assert_axioms objective_post_bytes objective_allocate_below_post

end Minidregg.Kernel.DeployedHistory
