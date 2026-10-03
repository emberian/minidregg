/- Signed Bend execution request below native transaction types. The source
selector is a participant index, not an unguarded host filename. Native receiving
must resolve the source from that current observed participant, derive the
invocation input, and compare the entire decoded result to its native effects.
This claim is mutually exclusive with the historical Nock claim. -/
import Compiler.BendRunCore
import Compiler.BendPrivateCapacity

namespace Minidregg.Compiler.BendExecutionClaim
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

structure Claim where
  sourceIndex : Nat
  sourceAtom : Digest
  artifact : Digest
  method : Digest
  /-- Canonical authored argument bytes only; native observations are derived
  from the loaded image and never accepted from this vector. -/
  arguments : List UInt8
  argumentCodec : Digest
  outputCodec : Digest
  /-- The complete fixed public tariff envelope is signed before execution. -/
  capacity : BendPrivateCapacity.Capacity
  deriving DecidableEq, Repr

def capacityStream : StreamCodec BendPrivateCapacity.Capacity :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))))
    (fun c => (c.incidences,c.turnBytes,c.memoryTouches,c.witnessBytes,c.proofWork,
      c.storageBytes,c.networkBytes,c.sideEffectCount,c.feeDebit,c.leaseByteBlocks))
    (fun c => ⟨c.1,c.2.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2.1,c.2.2.2.2.2.1,
      c.2.2.2.2.2.2.1,c.2.2.2.2.2.2.2.1,c.2.2.2.2.2.2.2.2.1,c.2.2.2.2.2.2.2.2.2⟩)
    (by intro c; cases c; rfl)

def stream : StreamCodec Claim :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream capacityStream)))))))
    (fun c => (c.sourceIndex,c.sourceAtom,c.artifact,c.method,c.arguments,
      c.argumentCodec,c.outputCodec,c.capacity))
    (fun c => ⟨c.1,c.2.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2.1,c.2.2.2.2.2.1,
      c.2.2.2.2.2.2.1,c.2.2.2.2.2.2.2⟩) (by intro c; cases c; rfl)

def frame : List UInt8 := "DREGG/BEND/SIGNED-EXECUTION-CLAIM/v1".toUTF8.toList
def encode (claim : Claim) : List UInt8 := frame ++ stream.encode claim
def decode (bytes : List UInt8) : Option Claim :=
  NockProgramCodec.framedDecode frame stream bytes

theorem roundtrip (claim : Claim) : decode (encode claim) = some claim :=
  NockProgramCodec.framedDecode_encode frame stream claim

theorem canonical {bytes : List UInt8} {claim : Claim}
    (accepted : decode bytes = some claim) : encode claim = bytes :=
  NockProgramCodec.framedDecode_canonical accepted

end Minidregg.Compiler.BendExecutionClaim
