/-
# Compiler.DurableReceiverCodec — canonical finite receiver bytes

Only generic `StreamCodec` products/lists are used. Full consumption and exact
re-encoding reject aliases and trailing bytes. All ten metering lanes, payload
bytes, read guards, nullifiers, and event envelopes survive persistence.
-/
import Kernel.DurableReceiver
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Compiler.DurableReceiverCodec

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

abbrev ChargeTuple := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

def chargeTuple (charge : Charge) : ChargeTuple :=
  (charge .incidences, charge .turnBytes, charge .memoryTouches, charge .witnessBytes,
    charge .proofWork, charge .storageBytes, charge .networkBytes,
    charge .sideEffectCount, charge .feeDebit, charge .leaseByteBlocks)

def chargeOfTuple (tuple : ChargeTuple) : Charge
  | .incidences => tuple.1
  | .turnBytes => tuple.2.1
  | .memoryTouches => tuple.2.2.1
  | .witnessBytes => tuple.2.2.2.1
  | .proofWork => tuple.2.2.2.2.1
  | .storageBytes => tuple.2.2.2.2.2.1
  | .networkBytes => tuple.2.2.2.2.2.2.1
  | .sideEffectCount => tuple.2.2.2.2.2.2.2.1
  | .feeDebit => tuple.2.2.2.2.2.2.2.2.1
  | .leaseByteBlocks => tuple.2.2.2.2.2.2.2.2.2

theorem chargeOfTuple_tuple (charge : Charge) : chargeOfTuple (chargeTuple charge) = charge := by
  funext lane
  cases lane <;> rfl

def chargeTupleStream : StreamCodec ChargeTuple :=
  StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
          (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))))

def chargeStream : StreamCodec Charge :=
  StreamCodec.xmap chargeTupleStream chargeTuple chargeOfTuple chargeOfTuple_tuple

def writeStream : StreamCodec DataWrite :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)))
    (fun write => (write.cellId, write.expectedPre, write.exactPost, write.canonicalPostBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; cases value; rfl)

def guardStream : StreamCodec ReadGuard :=
  StreamCodec.xmap (StreamCodec.product digestStream digestStream)
    (fun guard => (guard.cellId, guard.expectedRoot))
    (fun tuple => ⟨tuple.1, tuple.2⟩) (by intro value; cases value; rfl)

def nullifierStream : StreamCodec StableNullifier :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)))
    (fun value => (value.codecVersion, value.domain, value.nullifierId, value.canonicalBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; cases value; rfl)

def eventStream : StreamCodec StableEvent :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)))
    (fun value => (value.codecVersion, value.domain, value.eventId, value.canonicalBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; cases value; rfl)

def intentStream : StreamCodec IntentRecord :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product (StreamCodec.list writeStream)
        (StreamCodec.product (StreamCodec.list guardStream)
          (StreamCodec.product (StreamCodec.list nullifierStream)
            (StreamCodec.product chargeStream eventStream)))))
    (fun record => (record.transactionId, record.writes, record.readGuards,
      record.nullifiers, record.exactCharge, record.event))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1,
      tuple.2.2.2.2.1, tuple.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def seedStream : StreamCodec Seed :=
  StreamCodec.xmap
    (StreamCodec.product bytesStream
      (StreamCodec.product (StreamCodec.list (StreamCodec.product digestStream bytesStream)) chargeStream))
    (fun seed => (seed.absentBytes, seed.cells, seed.available))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro value; cases value; rfl)

def imageStream : StreamCodec Image :=
  StreamCodec.xmap (StreamCodec.product seedStream (StreamCodec.list intentStream))
    (fun image => (image.seed, image.accepted))
    (fun tuple => ⟨tuple.1, tuple.2⟩) (by intro value; cases value; rfl)

def wireFrame : List UInt8 := "DREGG.DURABLE.IMAGE".toUTF8.toList ++ [1]

/-- A fixed frame is recovered only if the final canonical check succeeds. -/
def framedStream : StreamCodec Image :=
  StreamCodec.xmap (StreamCodec.product bytesStream imageStream)
    (fun image => (wireFrame, image)) Prod.snd (by intro image; rfl)

def encode (image : Image) : List UInt8 := framedStream.encode image

def decode (bytes : List UInt8) : Option Image := do
  let image ← framedStream.toLawful.decode bytes
  if encode image = bytes then some image else none

@[simp] theorem decode_encode (image : Image) : decode (encode image) = some image := by
  have roundtrip := framedStream.toLawful.decode_encode image
  change framedStream.toLawful.decode (encode image) = some image at roundtrip
  simp [decode, roundtrip]

theorem decode_canonical {bytes : List UInt8} {image : Image}
    (accepted : decode bytes = some image) : encode image = bytes := by
  unfold decode at accepted
  cases raw : framedStream.toLawful.decode bytes with
  | none => simp [raw] at accepted
  | some selected =>
      simp only [raw, bind, Option.bind] at accepted
      split at accepted
      next canonical => cases Option.some.inj accepted; exact canonical
      next => contradiction

def codec : LawfulCodec Image where
  encode := encode
  decode := decode
  decode_encode := decode_encode

theorem encode_injective : Function.Injective encode := by
  intro left right equal
  have decoded := congrArg decode equal
  simpa using decoded

/-- Decoding a durable image and replaying its journal is the only recovery
path. Invalid bytes, stale recorded writes, duplicate commits, and bad bound
post roots all refuse. -/
def recover (rootBytes : List UInt8 → Digest) (bytes : List UInt8) :
    Option (DataSnapshot rootBytes) := do
  let image ← decode bytes
  image.restore rootBytes

theorem recover_encoded (rootBytes : List UInt8 → Digest) (image : Image) :
    recover rootBytes (encode image) = image.restore rootBytes := by
  simp [recover]

end Minidregg.Compiler.DurableReceiverCodec

/-- info: 'Minidregg.Compiler.DurableReceiverCodec.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DurableReceiverCodec.decode_encode
/-- info: 'Minidregg.Compiler.DurableReceiverCodec.decode_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DurableReceiverCodec.decode_canonical
