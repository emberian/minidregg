/-
# Kernel.DeployedTurnCodec -- the deployed Turn's bytes decode to the Turn (FD-1, R4a)

`DeployedHistory.encodeTurn` is the turn's canonical bytes (the journal digest's
preimage).  This module is its inverse, so a log of `encodeTurn` entries is
something a follower can READ: `decodeTurn (encodeTurn t) = some t`
(`decodeTurn_encodeTurn`).  Each piece is a `StreamCodec` whose `encode` is the
piece `encodeTurn` already uses (`opStream_encode`, `legStream_encode`), so the
roundtrip is the codec law, not a second encoding.  No persisted byte changes.
-/
import Kernel.DeployedHistory
import Theory.AssertAxioms

namespace Minidregg.Kernel.DeployedTurnCodec

open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Kernel.World
open Minidregg.Kernel.DeployedBridge
open Minidregg.Kernel.DeployedHistory
open Minidregg.Kernel.TurnOfIntent
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent (TransactionId StableEvent)

set_option autoImplicit false

/-- Decode a whole byte string with a prefix codec: every byte consumed. -/
def full {α : Type} (c : StreamCodec α) (bytes : List UInt8) : Option α := do
  let (value, rest) ← c.decodePrefix bytes
  if rest = [] then some value else none

@[simp] theorem full_encode {α : Type} (c : StreamCodec α) (value : α) :
    full c (c.encode value) = some value := by
  have h := c.decodePrefix_encode value []
  simp only [List.append_nil] at h
  simp [full, h]

/-! ## Ops at a kind -/

/-- The op stream of a kind's layout; its `encode` is `encodeOp`. -/
def opStream (k : deployedR.Kind) : StreamCodec (Op (deployedR.layout k)) where
  encode := encodeOp k
  decodePrefix
    | 0 :: bytes => do
        let (ns, b1) ← (wireOf k).namespaceStream.decodePrefix bytes
        let (key, b2) ← ((wireOf k).keyStream ns).decodePrefix b1
        let (value, b3) ← (StreamCodec.option ((wireOf k).valueStream ns)).decodePrefix b2
        some (.read ns key value, b3)
    | 1 :: bytes => do
        let (ns, b1) ← (wireOf k).namespaceStream.decodePrefix bytes
        let (key, b2) ← ((wireOf k).keyStream ns).decodePrefix b1
        let (old, b3) ← ((wireOf k).valueStream ns).decodePrefix b2
        let (new, b4) ← ((wireOf k).valueStream ns).decodePrefix b3
        some (.write ns key old new, b4)
    | 2 :: bytes => do
        let (ns, b1) ← (wireOf k).namespaceStream.decodePrefix bytes
        let (key, b2) ← ((wireOf k).keyStream ns).decodePrefix b1
        let (value, b3) ← ((wireOf k).valueStream ns).decodePrefix b2
        some (.allocate ns key value, b3)
    | 3 :: bytes => do
        let (ns, b1) ← (wireOf k).namespaceStream.decodePrefix bytes
        let (key, b2) ← ((wireOf k).keyStream ns).decodePrefix b1
        let (old, b3) ← ((wireOf k).valueStream ns).decodePrefix b2
        some (.free ns key old, b3)
    | _ => none
  decodePrefix_encode := by
    intro op suffix
    cases op <;>
      simp [encodeOp, List.append_assoc, StreamCodec.decodePrefix_encode]

theorem opStream_encode (k : deployedR.Kind) (op : Op (deployedR.layout k)) :
    (opStream k).encode op = encodeOp k op := rfl

/-! ## Legs -/

/-- Decode a leg's op list at its kind: each element is one whole op. -/
def decodeOps (k : deployedR.Kind) (ops : List (List UInt8)) :
    Option (Patch (deployedR.layout k)) :=
  ops.mapM (full (opStream k))

theorem decodeOps_encode (k : deployedR.Kind) (patch : Patch (deployedR.layout k)) :
    decodeOps k (patch.map (encodeOp k)) = some patch := by
  induction patch with
  | nil => rfl
  | cons op rest ih =>
      have h := full_encode (opStream k) op
      rw [opStream_encode] at h
      simp only [decodeOps, List.map_cons, List.mapM_cons, h] at ih ⊢
      simp [ih]

/-- The leg stream; its `encode` is `encodeLeg`. -/
def legStream : StreamCodec (Leg deployedR) where
  encode := encodeLeg
  decodePrefix bytes := do
    let (cell, b1) ← StreamCodec.nat.decodePrefix bytes
    match b1 with
    | [] => none
    | tag :: b2 =>
      let k ← CanonicalCellRegistry.kindAtTag tag
      let (ops, b3) ← (StreamCodec.list bytesStream).decodePrefix b2
      let patch ← decodeOps k ops
      some (⟨cell, k, patch⟩, b3)
  decodePrefix_encode := by
    intro leg suffix
    obtain ⟨cell, k, patch⟩ := leg
    simp only [encodeLeg, List.append_assoc, StreamCodec.decodePrefix_encode,
      List.cons_append, List.nil_append]
    simp [StreamCodec.decodePrefix_encode, decodeOps_encode]

theorem legStream_encode (leg : Leg deployedR) : legStream.encode leg = encodeLeg leg := rfl

/-! ## Creates -/

/-- A create's bytes, as `turnFields` writes them. -/
def createBytes (c : CellId × Cell deployedR × Option CellId) : List UInt8 :=
  StreamCodec.nat.encode c.1 ++ bytesStream.encode (encodeCell (some c.2.1)) ++
    (StreamCodec.option StreamCodec.nat).encode c.2.2

/-- Decode one create: the id, a LIVE cell image, and the room. -/
def decodeCreate (bytes : List UInt8) : Option (CellId × Cell deployedR × Option CellId) := do
  let (c, b1) ← StreamCodec.nat.decodePrefix bytes
  let (image, b2) ← bytesStream.decodePrefix b1
  let room ← full (StreamCodec.option StreamCodec.nat) b2
  match decodeCell image with
  | some (some cell) => some (c, cell, room)
  | _ => none

theorem decodeCreate_createBytes (c : CellId × Cell deployedR × Option CellId) :
    decodeCreate (createBytes c) = some c := by
  obtain ⟨id, cell, room⟩ := c
  simp [decodeCreate, createBytes, List.append_assoc, StreamCodec.decodePrefix_encode,
    bridge_decode_total_on_registry]

/-! ## The turn -/

/-- **The inverse of `encodeTurn`.**  The absence pins, then exactly the twelve
`turnFields` slots, each consumed whole. -/
def decodeTurn (bytes : List UInt8) : Option (DTurn deployedR Digest) := do
  let (absent, fields) ← full (StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.list bytesStream)) bytes
  match fields with
  | [fTx, fCreates, fLegs, fRetires, fEvent, fNull, fCharge, fSubject, fEpoch, fCap,
      fBefore, fUntil] =>
    let txId ← full digestStream fTx
    let createsRaw ← full (StreamCodec.list bytesStream) fCreates
    let creates ← createsRaw.mapM decodeCreate
    let legsRaw ← full (StreamCodec.list bytesStream) fLegs
    let legs ← legsRaw.mapM (full legStream)
    let retires ← full (StreamCodec.list StreamCodec.nat) fRetires
    let event ← full DurableReceiverCodec.eventStream fEvent
    let nullifiers ← full (StreamCodec.list digestStream) fNull
    let charge ← full DurableReceiverCodec.chargeStream fCharge
    let subject ← full (StreamCodec.option DurableReceiverCodec.subjectStream) fSubject
    let keyEpoch ← full StreamCodec.nat fEpoch
    let capability ← full (StreamCodec.option digestStream) fCap
    let notBefore ← full StreamCodec.nat fBefore
    let validUntil ← full (StreamCodec.option StreamCodec.nat) fUntil
    some { txId, creates, legs, retires, event, nullifiers, charge, subject, keyEpoch,
           capability, notBefore, validUntil, absent }
  | _ => none

theorem mapM_decodeCreate (cs : List (CellId × Cell deployedR × Option CellId)) :
    (cs.map createBytes).mapM decodeCreate = some cs := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [List.mapM_cons, decodeCreate_createBytes, ih]

theorem mapM_decodeLeg (legs : List (Leg deployedR)) :
    (legs.map encodeLeg).mapM (full legStream) = some legs := by
  induction legs with
  | nil => rfl
  | cons leg rest ih =>
      have h := full_encode legStream leg
      rw [legStream_encode] at h
      simp [List.mapM_cons, h, ih]

/-- **`decodeTurn_encodeTurn`**: every deployed turn's canonical bytes decode to
exactly that turn. -/
theorem decodeTurn_encodeTurn (t : DTurn deployedR Digest) :
    decodeTurn (encodeTurn t) = some t := by
  have hc : (t.creates.map fun c => StreamCodec.nat.encode c.1 ++
      bytesStream.encode (encodeCell (some c.2.1)) ++
        (StreamCodec.option StreamCodec.nat).encode c.2.2).mapM decodeCreate = some t.creates :=
    mapM_decodeCreate t.creates
  have hp := full_encode (StreamCodec.product (StreamCodec.list StreamCodec.nat)
    (StreamCodec.list bytesStream)) (t.absent, turnFields t)
  unfold decodeTurn encodeTurn
  rw [hp]
  simp only [turnFields, bind, Option.bind, full_encode]
  rw [hc, mapM_decodeLeg]

#assert_axioms decodeOps_encode
#assert_axioms decodeCreate_createBytes
#assert_axioms decodeTurn_encodeTurn

end Minidregg.Kernel.DeployedTurnCodec
