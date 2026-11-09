/-
# Compiler.DurableSealHeld -- the checkpoint body held encoded, sealed by concatenation

A due checkpoint (`DurableCheckpointCodec.sealedBytesAt`, every `checkpointEvery` appends)
encoded the whole served state and the World's system store, then MACed it. The state differs
from the previous seal's only in the cells and system rows the appends between them wrote, and
the system store's journal gains a row per record, so the encode grew with the height.

Here every part of the body that grows is held already encoded, moved at each append by what it
wrote:

* `HeldCells ids bytesOf`: each enumerable cell's checkpoint entry, `(id, bytes)` encoded once
  when the cell is written (`HeldCells.step`, over the cells a record wrote);
* `HeldWorld`: the fold's World beside its system store's entries, encoded once each and kept in
  the payload's order (`StoreCodec.HeldEntries`), moved by the system patch of each admitted turn
  (`HeldWorld.admitPinned`, `admitPinned_system`).

`sealArray` is then the small fields encoded, the held parts concatenated, the body hashed by the
cSHAKE kernel on the buffer and the MAC: `sealArray_eq` proves it is `sealedBytesAt`, byte for
byte.
-/
module

public import Compiler.DurableReceiverCore
public import Compiler.StoreCodecHeld

@[expose] public section

namespace Minidregg.Compiler.DurableReceiverIO

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Store
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableCheckpoint
open Minidregg.Compiler.DurableReceiverCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.DurableCheckpointCodec

set_option autoImplicit false

/-! ## The World's system store, held encoded -/

section World

open Minidregg.Kernel.World

variable {R : Registry} {TxId Ev D : Type} [DecidableEq TxId] [DecidableEq D]
  [Minidregg.Theory.StoreKey TxId] [Minidregg.Theory.StoreKey D]

/-- The system patch an admitted turn runs on the system store (`World.admit`'s last step), at
the World's head. -/
def sysPatchAt (H : History R TxId Ev D) (w : World R TxId D) (t : Turn R TxId Ev D) :
    Patch (sysLayout TxId D) :=
  match w.head with
  | some (height, logRoot) => sysPatch H t height logRoot w.meter
  | none => []

/-- **An admitted turn writes the system store by its system patch, nothing else.** -/
theorem admitPinned_system (H : History R TxId Ev D) {pins : Option Reject} {w w' : World R TxId D}
    {t : Turn R TxId Ev D} (admitted : World.admitPinned H pins w t = .ok w') :
    w'.system = Patch.run w.system (sysPatchAt H w t) := by
  unfold World.admitPinned at admitted
  unfold sysPatchAt
  split at admitted
  · cases admitted
  split at admitted
  · cases admitted
  split at admitted
  · cases admitted
  split at admitted
  · cases admitted
  split at admitted
  · cases admitted
  split at admitted
  · cases admitted
  · rename_i height logRoot head
    rw [head]
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    · cases admitted
      rfl

end World

/-- The fold's World with its system store's entries held encoded (`StoreCodec.HeldEntries`). -/
structure HeldWorld where
  world : HostRefinesWorld.DWorld
  system : StoreCodec.HeldEntries WorldSystemCodec.systemWire world.system

namespace HeldWorld

/-- A World's, built once (an open): every system entry encoded. -/
def ofWorld (world : HostRefinesWorld.DWorld) : HeldWorld :=
  ⟨world, StoreCodec.HeldEntries.ofStore (W := WorldSystemCodec.systemWire) world.system⟩

/-- `World.admitPinned`, the held entries moved by the turn's system patch. -/
def admitPinned (pins : Option Minidregg.Kernel.World.Reject) (held : HeldWorld)
    (t : Minidregg.Kernel.World.Turn DeployedBridge.deployedR TransactionId StableEvent Digest) :
    Except Minidregg.Kernel.World.Reject HeldWorld :=
  match admitted : Minidregg.Kernel.World.World.admitPinned DeployedHistory.history pins held.world t with
  | .error reason => .error reason
  | .ok w' => .ok ⟨w', (admitPinned_system DeployedHistory.history admitted).symm ▸
      held.system.run (sysPatchAt DeployedHistory.history held.world t)⟩

theorem admitPinned_world (pins : Option Minidregg.Kernel.World.Reject) (held : HeldWorld)
    (t : Minidregg.Kernel.World.Turn DeployedBridge.deployedR TransactionId StableEvent Digest) :
    (held.admitPinned pins t).map (·.world) =
      Minidregg.Kernel.World.World.admitPinned DeployedHistory.history pins held.world t := by
  unfold admitPinned
  split <;> rename_i admitted <;> simp only [Except.map] <;> exact admitted.symm

end HeldWorld

/-- `advanceWorldIntent` on a held World: the same turn, charge and admission, the system
entries moved by the turn's system patch (`advanceHeld_world`). -/
def advanceHeld {rootBytes : List UInt8 → Digest} (roots : CellId → Digest) (held : HeldWorld)
    (height : Nat) (intent : DataIntent rootBytes) : Except String HeldWorld :=
  match TurnOfIntent.Turn.ofIntent DeployedBridge.bridge DeployedHistory.history held.world intent with
  | .error refusal => .error s!"height {height + 1}: the record is not a turn: {repr refusal}"
  | .ok t =>
      match DeployedCharge.mismatch t.charge intent.exactCharge with
      | some lane =>
          .error s!"height {height + 1}: the record's charge is not its turn's: {repr lane}"
      | none =>
          match held.admitPinned
              (Minidregg.Kernel.World.pinCheckFromBy (rootPinFails roots held.world) 0 t.pins) t with
          | .error reason => .error s!"height {height + 1}: the World refuses the turn: {repr reason}"
          | .ok w' => .ok w'

theorem advanceHeld_world {rootBytes : List UInt8 → Digest} (roots : CellId → Digest) (held : HeldWorld)
    (height : Nat) (intent : DataIntent rootBytes) :
    (advanceHeld roots held height intent).map (·.world) =
      advanceWorldIntent roots held.world height intent := by
  unfold advanceHeld advanceWorldIntent
  cases TurnOfIntent.Turn.ofIntent DeployedBridge.bridge DeployedHistory.history held.world intent with
  | error refusal => rfl
  | ok t =>
      simp only
      cases DeployedCharge.mismatch t.charge intent.exactCharge with
      | some lane => rfl
      | none =>
          simp only
          rw [← HeldWorld.admitPinned_world]
          cases held.admitPinned _ t <;> rfl

/-- `foldRecords` on a held World (`foldHeld_world`): each turn admitted by `World.admit`, the
system entries moved by its system patch. -/
def foldHeld (rootBytes : List UInt8 → Digest) : HeldWorld → Nat → List IntentRecord → Except String HeldWorld
  | held, _, [] => .ok held
  | held, height, record :: rest =>
      match record.bind? rootBytes with
      | none => .error s!"height {height + 1}: the record does not bind its roots"
      | some intent =>
          match TurnOfIntent.Turn.ofIntent DeployedBridge.bridge DeployedHistory.history held.world intent with
          | .error refusal => .error s!"height {height + 1}: the record is not a turn: {repr refusal}"
          | .ok t =>
              match DeployedCharge.mismatch t.charge intent.exactCharge with
              | some lane =>
                  .error s!"height {height + 1}: the record's charge is not its turn's: {repr lane}"
              | none =>
              match held.admitPinned
                  (Minidregg.Kernel.World.pinCheck DeployedHistory.history held.world t) t with
              | .error reason => .error s!"height {height + 1}: the World refuses the turn: {repr reason}"
              | .ok w' => foldHeld rootBytes w' (height + 1) rest

theorem foldHeld_world (rootBytes : List UInt8 → Digest) (held : HeldWorld) (height : Nat)
    (records : List IntentRecord) :
    (foldHeld rootBytes held height records).map (·.world) = foldRecords rootBytes held.world height records := by
  induction records generalizing held height with
  | nil => rfl
  | cons record rest ih =>
      unfold foldHeld foldRecords
      cases record.bind? rootBytes with
      | none => rfl
      | some intent =>
          simp only
          cases TurnOfIntent.Turn.ofIntent DeployedBridge.bridge DeployedHistory.history held.world intent with
          | error refusal => rfl
          | ok t =>
              simp only
              cases DeployedCharge.mismatch t.charge intent.exactCharge with
              | some lane => rfl
              | none =>
                  simp only
                  rw [Minidregg.Kernel.World.admit_eq_admitPinned, ← HeldWorld.admitPinned_world]
                  cases held.admitPinned _ t with
                  | error reason => rfl
                  | ok w' => exact ih w' (height + 1)

/-! ## The served cells, held encoded -/

/-- A cell's checkpoint entry (`stateStream`'s element), encoded once. -/
def cellArray (cell : CellId × List UInt8) : ByteArray :=
  (StreamCodec.product digestStream bytesStream).encodeBytes cell

/-- Each enumerable cell's checkpoint entry, encoded when the cell was last written. -/
structure HeldCells (ids : List CellId) (bytesOf : CellId → List UInt8) where
  map : Minidregg.Theory.SparseMap CellId (fun _ => ByteArray)
  exact : ∀ cellId ∈ ids, map.get? cellId = some (cellArray (cellId, bytesOf cellId))

namespace HeldCells

/-- Encode the listed cells into `map`. -/
def encodeInto (bytesOf : CellId → List UInt8) (map : Minidregg.Theory.SparseMap CellId (fun _ => ByteArray))
    (cells : List CellId) : Minidregg.Theory.SparseMap CellId (fun _ => ByteArray) :=
  cells.foldl (fun map cellId => map.set cellId (some (cellArray (cellId, bytesOf cellId)))) map

theorem encodeInto_get (bytesOf : CellId → List UInt8) (map : Minidregg.Theory.SparseMap CellId (fun _ => ByteArray))
    (cells : List CellId) (cellId : CellId) :
    (encodeInto bytesOf map cells).get? cellId =
      if cellId ∈ cells then some (cellArray (cellId, bytesOf cellId)) else map.get? cellId := by
  induction cells generalizing map with
  | nil => simp [encodeInto]
  | cons head rest ih =>
      have step := ih (map.set head (some (cellArray (head, bytesOf head))))
      simp only [encodeInto, List.foldl_cons] at step ⊢
      rw [step]
      by_cases inRest : cellId ∈ rest
      · simp [inRest]
      · by_cases same : cellId = head
        · subst same; simp
        · simp [inRest, same, Minidregg.Theory.SparseMap.set_ne _ _ _ _ same]

/-- Every listed cell encoded (an open). -/
def build (ids : List CellId) (bytesOf : CellId → List UInt8) : HeldCells ids bytesOf where
  map := encodeInto bytesOf ∅ ids
  exact := by intro cellId member; rw [encodeInto_get]; simp [member]

/-- **One step**: the cells `written` re-encoded, every other one kept, given that outside
`written` the step keeps every cell's bytes and adds no cell. -/
def step {ids : List CellId} {bytesOf : CellId → List UInt8} (held : HeldCells ids bytesOf)
    (ids' : List CellId) (bytesOf' : CellId → List UInt8) (written : List CellId)
    (within : ∀ cellId ∈ ids', cellId ∉ written → cellId ∈ ids)
    (keeps : ∀ cellId, cellId ∉ written → bytesOf' cellId = bytesOf cellId) : HeldCells ids' bytesOf' where
  map := encodeInto bytesOf' held.map written
  exact := by
    intro cellId member
    rw [encodeInto_get]
    by_cases wrote : cellId ∈ written
    · simp [wrote]
    · simp only [wrote, ite_false]
      rw [held.exact cellId (within cellId member wrote), keeps cellId wrote]

/-- The cell list's encoding: its length, then each listed cell's held entry. -/
def payload {ids : List CellId} {bytesOf : CellId → List UInt8} (held : HeldCells ids bytesOf) : ByteArray :=
  ids.foldl (fun out cellId => out ++ (held.map.get? cellId).getD ByteArray.empty)
    (StreamCodec.nat.encodeBytes ids.length)

/-- **The held cells' payload is the checkpoint state's cell list, encoded.** -/
theorem payload_eq {ids : List CellId} {bytesOf : CellId → List UInt8} (held : HeldCells ids bytesOf) :
    held.payload.data.toList =
      (StreamCodec.list (StreamCodec.product digestStream bytesStream)).encode
        (ids.map fun cellId => (cellId, bytesOf cellId)) := by
  have walk : ∀ (rest : List CellId) (out : ByteArray), (∀ cellId ∈ rest, cellId ∈ ids) →
      (rest.foldl (fun out cellId => out ++ (held.map.get? cellId).getD ByteArray.empty) out).data.toList =
        out.data.toList ++ StreamCodec.encodeMany (StreamCodec.product digestStream bytesStream)
          (rest.map fun cellId => (cellId, bytesOf cellId)) := by
    intro rest
    induction rest with
    | nil => intro out _; simp [StreamCodec.encodeMany]
    | cons head tail ih =>
        intro out inside
        rw [List.foldl_cons, ih _ (fun cellId member => inside cellId (List.mem_cons_of_mem _ member)),
          held.exact head (inside head List.mem_cons_self)]
        simp only [Option.getD_some, ByteArray.data_append, Array.toList_append, List.map_cons,
          StreamCodec.encodeMany, cellArray, StreamCodec.encodeBytes_data, List.append_assoc]
  rw [payload, walk ids _ (fun _ member => member), StreamCodec.encodeBytes_data]
  simp [StreamCodec.list]

end HeldCells

/-! ## The seal -/

/-- `cshake256Bytes` on byte arrays, as the kernel computes it (`cshake256Array_data`). -/
def cshake256Array (customization input : ByteArray) : ByteArray :=
  Minidregg.Compiler.Sp800185Cshake256.Native.cshake256Kernel customization input

theorem cshake256Array_data (customization input : ByteArray) :
    (cshake256Array customization input).data.toList =
      Minidregg.Compiler.Sp800185Cshake256.cshake256Bytes customization.data.toList input.data.toList := by
  unfold cshake256Array Minidregg.Compiler.Sp800185Cshake256.Native.cshake256Kernel
  rw [Minidregg.Compiler.Sp800185Cshake256.Native.bytesOfList_toList,
    Minidregg.Compiler.Sp800185Cshake256.Fast.cshake256Fast_eq]

/-- The body of a checkpoint whose growing parts are held encoded: `cells` is the state's cell
list encoded (`HeldCells.payload`), `system` the system store's payload (`HeldEntries.payload`);
the rest is encoded here. Concatenation only. -/
def sealBody (key : MacKey) (height : Nat) (chain : Digest) (frontier : List (Nat × Digest))
    (indexRoot : Digest) (absentBytes : List UInt8) (cells : ByteArray) (available : Theory.ResourceCost.Charge)
    (system : Option ByteArray) : ByteArray :=
  let head := (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream (StreamCodec.product frontierStream
      (StreamCodec.product digestStream bytesStream))))).encodeBytes
    (key.id, height, chain, frontier, indexRoot, absentBytes)
  let systemPart := match system with
    | none => ByteArray.mk #[0]
    | some payload => ByteArray.mk #[1] ++ payload
  head ++ cells ++ chargeStream.encodeBytes available ++ systemPart ++
    digestStream.encodeBytes foldSemantics

/-- The checkpoint frame of an encoded body: the body hashed by the cSHAKE kernel on the buffer,
the MAC, the frame. Byte arrays in, a byte array out: it can run off the serving thread. -/
def sealFrame (key : MacKey) (height : Nat) (root : Digest) (body : ByteArray) : ByteArray :=
  let mac := Minidregg.Compiler.Sp800185Cshake256.kmac256Bytes key.bytes "DREGG/NATIVE-HOST/CHECKPOINT-MAC/v1".toUTF8.toList
    (macInputStream.encode (key.id, height, root,
      (cshake256Array (Minidregg.Compiler.Sp800185Cshake256.Native.bytesOfList
        "DREGG/NATIVE-HOST/CHECKPOINT-BODY/v1".toUTF8.toList) body).data.toList))
  bytesStream.encodeBytes checkpointFrame.frame ++ body ++
    (StreamCodec.product digestStream bytesStream).encodeBytes (root, mac)

/-- The checkpoint frame of a body whose growing parts are held encoded (`sealArray_eq`). -/
def sealArray (key : MacKey) (height : Nat) (chain : Digest) (frontier : List (Nat × Digest))
    (indexRoot : Digest) (absentBytes : List UInt8) (cells : ByteArray) (available : Theory.ResourceCost.Charge)
    (system : Option ByteArray) (root : Digest) : ByteArray :=
  sealFrame key height root (sealBody key height chain frontier indexRoot absentBytes cells available system)

/-- **The held seal is the seal**, byte for byte, given the held parts are the state's. -/
theorem sealArray_eq (key : MacKey) (height : Nat) (chain : Digest) (frontier : List (Nat × Digest))
    (indexRoot : Digest) (state : State) (cells : ByteArray)
    (cellsExact : cells.data.toList = (StreamCodec.list (StreamCodec.product digestStream bytesStream)).encode state.cells)
    (system : Option (Store WorldSystemCodec.DSys)) (payload : Option ByteArray)
    (systemExact : payload.map (·.data.toList) = system.map WorldSystemCodec.systemStream.encode)
    (root : Digest) :
    (sealArray key height chain frontier indexRoot state.absentBytes cells state.available payload root).data.toList =
      sealedBytesAt key height chain frontier indexRoot state system root := by
  have systemPart : (match payload with
      | none => ByteArray.mk #[0]
      | some payload => ByteArray.mk #[1] ++ payload).data.toList =
      (StreamCodec.option WorldSystemCodec.systemStream).encode system := by
    cases payload <;> cases system <;> simp_all [StreamCodec.option]
  have bodyBytes : (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream (StreamCodec.product frontierStream
        (StreamCodec.product digestStream bytesStream))))).encode
      (key.id, height, chain, frontier, indexRoot, state.absentBytes) ++ cells.data.toList ++
      chargeStream.encode state.available ++
      (StreamCodec.option WorldSystemCodec.systemStream).encode system ++ digestStream.encode foldSemantics =
      bodyStream.encode ⟨key.id, height, chain, frontier, indexRoot, state, system, foldSemantics⟩ := by
    rw [cellsExact]
    simp [bodyStream, stateStream, StreamCodec.xmap, StreamCodec.product, List.append_assoc]
  unfold sealArray sealFrame sealBody sealedBytesAt
  simp only [ByteArray.data_append, Array.toList_append, StreamCodec.encodeBytes_data, systemPart,
    cshake256Array_data, Minidregg.Compiler.Sp800185Cshake256.Native.bytesOfList_toList]
  rw [← bodyBytes]
  simp [StreamCodec.product, List.append_assoc]

end Minidregg.Compiler.DurableReceiverIO

#assert_axioms Minidregg.Compiler.DurableReceiverIO.admitPinned_system
#assert_axioms Minidregg.Compiler.DurableReceiverIO.advanceHeld_world
#assert_axioms Minidregg.Compiler.DurableReceiverIO.foldHeld_world
#assert_axioms Minidregg.Compiler.DurableReceiverIO.HeldCells.payload_eq
#assert_axioms Minidregg.Compiler.DurableReceiverIO.sealArray_eq
