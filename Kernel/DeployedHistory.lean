/- The deployed D2 storage unit is the encoding of newly written values, plus
the canonical bytes of the event the turn retains.
Transport frames, keys, old values, reads and frees are not value writes.
The complete turn encoding separately binds every guard and effect. -/
module

public import Kernel.DeployedBridge
public import Kernel.WorldRoot
public import Compiler.DurableReceiverCodec

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

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

/-- All fields other than absence pins, each in a length-delimited slot; the
last is the digest pins (`Turn.pins`, each a cell and its asserted digest), so
the journal digest binds what the turn asserts about the pre-state. -/
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
   (StreamCodec.option StreamCodec.nat).encode t.validUntil,
   (StreamCodec.list (StreamCodec.product StreamCodec.nat digestStream)).encode t.pins,
   DurableReceiverCodec.chargeStream.encode t.credit]

/-- Greenfield v2 turn shape: absence pins are in the digest preimage. -/
def encodeTurn (t : DTurn deployedR Digest) : List UInt8 :=
  (StreamCodec.product (StreamCodec.list StreamCodec.nat) (StreamCodec.list bytesStream)).encode
    (t.absent, turnFields t)

/-- Equal turn bytes imply equal absence pins: no field outside the digest. -/
theorem encodeTurn_absent {a b : DTurn deployedR Digest}
    (same : encodeTurn a = encodeTurn b) : a.absent = b.absent :=
  (Prod.mk.inj (StoreCodec.streamEncode_injective _ same)).1

/-- The bytes a turn's event retains: the event's canonical bytes, archived
with the turn (the admitted ingress they carry), charged like a written value. -/
def eventBytes (event : StableEvent) : Nat := event.canonicalBytes.length

/-- The pinned deployed history: cSHAKE turn digest/log chain, written-value
bytes, retained-event bytes, and the per-cell root a pin is compared with
(`DeployedBridge.cellRoot`). -/
def history : History deployedR TransactionId StableEvent Digest :=
  WorldRoot.cshakeHistory encodeTurn ⟨0⟩ legBytes imageBytes eventBytes cellRoot

/-- A pin is compared with the deployed per-cell root. -/
@[simp] theorem history_cellDigest : history.cellDigest = cellRoot := rfl

/-- **Pin coherence of the deployed bridge and history** at the deployed
per-cell root: bytes that decode to a slot and do not retire are that slot's
canonical encoding (`decodeCell_canonical`), so their root is the slot's
`cellRoot`, which is what a pin is compared with.  No deployed use of
`ofIntent_run`/`admit_of_accepted` carries coherence as a hypothesis. -/
theorem deployed_pinCoherent : PinCoherent bridge history ResourceBirthCodec.rootBytes :=
  fun _ _ h live => cellRoot_of_decode h live

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

/-- The receiver's live post image has 43 bytes beyond the encoded payload:
4 lifecycle + 4 registry + 32 protected frame + 2 version + 1 presence tag. -/
theorem objective_post_bytes (payload : ObjectiveActivityCell.Payload) :
    (encodeCell (some ⟨.objectiveActivity,
      ProtectedCell.stateOfOption ObjectiveActivityCell.spec (some payload)⟩)).length =
      (ObjectiveActivityCell.payloadStream.encode payload).length + 43 := by
  change (List.append [68,82,2,1] (List.append [68,82,1,19]
    (ObjectiveActivityCell.spec.wireFrame ++
      (ProtectedCell.wirePayloadStream ObjectiveActivityCell.spec).encode
        (1, some payload)))).length = _
  have frameLength : "DREGG/OBJECTIVE/ACTIVITY-CELL/v5".toByteArray.toList.length = 32 := by decide +kernel
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
  apply Minidregg.Theory.SparseMap.ext
  intro a
  rw [romPart_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
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
#assert_axioms deployed_pinCoherent
#assert_axioms objective_allocate_bytes objective_write_bytes objective_free_bytes read_bytes
#assert_axioms objective_post_bytes objective_allocate_below_post

/-! ## The pin guards a leg's untouched addresses

A derived leg carries one op per changed address (`TurnOfIntent.diff`); every other address
of the cell is guarded by the turn's pin on it, its pre-root.  An equal root fixes the whole
store, or names a collision of the root function: the collision is an explicit disjunct,
never an assumption. -/

/-- Two distinct byte strings with one deployed root. -/
def RootCollision : Prop :=
  ∃ a b : List UInt8, a ≠ b ∧ ResourceBirthCodec.rootBytes a = ResourceBirthCodec.rootBytes b

/-- **A pin fixes the store.**  Two stores of one kind with the same deployed root are
equal, or their encodings collide. -/
theorem pin_fixes_store {k : deployedR.Kind} {h s : Store (deployedR.layout k)}
    (pin : cellRoot (some ⟨k, h⟩) = cellRoot (some ⟨k, s⟩)) : h = s ∨ RootCollision := by
  by_cases same : encodeCell (some ⟨k, h⟩) = encodeCell (some ⟨k, s⟩)
  · have decoded := bridge_decode_total_on_registry (some ⟨k, h⟩)
    rw [same, bridge_decode_total_on_registry] at decoded
    have cell := (Option.some.inj (Option.some.inj decoded)).symm
    exact .inl (eq_of_heq (Cell.mk.inj cell).2)
  · exact .inr ⟨_, _, same, pin⟩

/-- **The pin implies the per-address guards** a leg used to carry: at a held store whose
root is the pin's, every read of an unchanged present address of the diffed pre-store holds,
or the root function collides. -/
theorem pin_implies_guards {k : deployedR.Kind} {h s s' : Store (deployedR.layout k)}
    (pin : cellRoot (some ⟨k, h⟩) = cellRoot (some ⟨k, s⟩)) :
    Patch.ValidFrom h (guardPatch (bridge.codec.cover k s s') s s') ∨ RootCollision := by
  rcases pin_fixes_store pin with rfl | collision
  · refine .inl (validFrom_of_distinct ?_ fun op m => ?_)
    · unfold guardPatch
      rw [map_address_filterMap _ (fun _ _ g => guardOp_address g)]
      exact (bridge.codec.cover_nodup k h s').filter _
    · obtain ⟨a, -, g⟩ := List.mem_filterMap.mp m
      obtain ⟨x, hx, -, rfl⟩ := guardOp_spec g
      exact hx
  · exact .inr collision

/-- **Teeth: a change at an address the leg does not touch is refused through the root.**
A held store that differs from the asserted pre-store anywhere fails the pin
(`World.pinCheck` refuses the turn `guardFailed`), or the root function collides. -/
theorem untouched_change_refused {w : World deployedR TransactionId Digest} {c : CellId} {k : deployedR.Kind}
    {h s s' : Store (deployedR.layout k)} {a : Address (deployedR.layout k)}
    (held : w.cells c = some ⟨k, h⟩) (moved : h a ≠ s a) (_untouched : changeOp s s' a = none) :
    Minidregg.Kernel.World.pinFails history w (c, cellRoot (some ⟨k, s⟩)) = true ∨ RootCollision := by
  cases fails : Minidregg.Kernel.World.pinFails history w (c, cellRoot (some ⟨k, s⟩)) with
  | true => exact .inl rfl
  | false =>
      have pin := ((Minidregg.Kernel.World.pinFails_eq_false_iff history).1 fails).2
      rw [history_cellDigest, held] at pin
      rcases pin_fixes_store pin with same | collision
      · subst same; exact absurd rfl moved
      · exact .inr collision

/-- Premise inhabitation for the teeth: a held store moved at an address the leg leaves
alone (the leg of `s` to itself touches nothing). -/
theorem untouched_change_inhabited {k : deployedR.Kind} {h s : Store (deployedR.layout k)}
    {a : Address (deployedR.layout k)} (moved : h a ≠ s a) :
    h a ≠ s a ∧ changeOp s s a = none := by
  refine ⟨moved, ?_⟩
  unfold changeOp
  cases s a <;> simp

#assert_axioms pin_fixes_store pin_implies_guards untouched_change_refused untouched_change_inhabited

end Minidregg.Kernel.DeployedHistory
