/-
# Compiler.PlanFootprintCodec — canonical bytes of a plan's read footprint

`Theory.PlanBinding.Footprint L` is a list of (address, observed value) reads.
A signed header carries it as bytes; this is the one codec, for any layout with
a `StoreCodec.Wire`: each read is the wire's canonical address followed by an
optional value in the wire's value codec for that address's namespace.
-/
import Compiler.StoreCodec
import Theory.PlanBinding

namespace Minidregg.Compiler.PlanFootprintCodec

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.Store
open Minidregg.Theory.PlanBinding

set_option autoImplicit false

variable {L : Layout.{0, 0, 0}} (W : StoreCodec.Wire L)

def readStream : StreamCodec (Read L) :=
  StreamCodec.xmap
    (FiniteDependentMapCodec.entryStream (StoreCodec.addressStream W)
      (fun address => StreamCodec.option (W.valueStream address.1)))
    (fun read => ⟨read.address, read.observed⟩)
    (fun entry => ⟨entry.1, entry.2⟩)
    (by intro read; cases read; rfl)

def footprintStream : StreamCodec (Footprint L) :=
  StreamCodec.list (readStream W)

def encode (footprint : Footprint L) : List UInt8 :=
  (footprintStream W).encode footprint

def decode (bytes : List UInt8) : Option (Footprint L) :=
  (footprintStream W).toLawful.decode bytes

theorem decode_encode (footprint : Footprint L) :
    decode W (encode W footprint) = some footprint :=
  (footprintStream W).toLawful.decode_encode footprint

/-- The canonical bytes of one address, for naming a stale read. -/
def addressBytes (address : Address L) : List UInt8 :=
  (StoreCodec.addressStream W).encode address

end Minidregg.Compiler.PlanFootprintCodec
