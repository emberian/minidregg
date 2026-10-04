/- The fixed public input layout of the Objective demand graph. The state region
(ObjectiveThunkNetwork.Shape) is followed by EVERY table the represented state
refers to: code rows, code field pairs (record/extend/case), names, environments
and runtime record fields. Sizes are public capacities; contents are inputs and
may be private. A decoder of a packed state reads all of these regions from the
bits it is given; no table is supplied beside them. -/
import Compiler.ObjectiveThunkNetwork
import Compiler.ObjectiveDemandPackedCode

namespace Minidregg.Compiler.ObjectiveDemandLayout
open ObjectiveThunkNetwork ObjectiveDemandPackedCode
set_option autoImplicit false

structure Layout where
  shape : Shape
  codeSlots : Nat
  codeFieldSlots : Nat
  nameSlots : Nat
  nameBytes : Nat
  environmentSlots : Nat
  environmentWidth : Nat
  recordSlots : Nat
  recordWidth : Nat
  /-- Public fuel for decoding source code from the code region. -/
  depth : Nat
  deriving Repr, DecidableEq

/-- One packed code row: opcode, primitive, then three words. -/
def rowBits (shape : Shape) : Nat := tagBits + primitiveBits + 3 * shape.wordBits

def Layout.word (layout : Layout) : Nat := layout.shape.wordBits

def Layout.codeBits (layout : Layout) : Nat := layout.codeSlots * rowBits layout.shape
def Layout.codeFieldBits (layout : Layout) : Nat :=
  layout.word + layout.codeFieldSlots * (2 * layout.word)
def Layout.nameEntryBits (layout : Layout) : Nat := layout.word + 8 * layout.nameBytes
def Layout.nameBits (layout : Layout) : Nat :=
  layout.word + layout.nameSlots * layout.nameEntryBits
def Layout.environmentEntryBits (layout : Layout) : Nat :=
  layout.word + layout.environmentWidth * layout.word
def Layout.environmentBits (layout : Layout) : Nat :=
  layout.word + layout.environmentSlots * layout.environmentEntryBits
def Layout.recordEntryBits (layout : Layout) : Nat :=
  layout.word + layout.recordWidth * (2 * layout.word)
def Layout.recordBits (layout : Layout) : Nat :=
  layout.word + layout.recordSlots * layout.recordEntryBits

/-- Every bit after the state region. The graph carries all of it from tick to tick. -/
def Layout.tableBits (layout : Layout) : Nat :=
  layout.codeBits + layout.codeFieldBits + layout.nameBits + layout.environmentBits +
    layout.recordBits

def Layout.inputCount (layout : Layout) : Nat := layout.shape.inputCount + layout.tableBits

def Layout.codeOffset (layout : Layout) : Nat := layout.shape.inputCount
def Layout.codeFieldOffset (layout : Layout) : Nat := layout.codeOffset + layout.codeBits
def Layout.nameOffset (layout : Layout) : Nat := layout.codeFieldOffset + layout.codeFieldBits
def Layout.environmentOffset (layout : Layout) : Nat := layout.nameOffset + layout.nameBits
def Layout.recordOffset (layout : Layout) : Nat := layout.environmentOffset + layout.environmentBits

/-- Every count and length fits its word. -/
def Layout.fits (layout : Layout) : Bool :=
  layout.shape.fits && layout.shape.payloadBits == 3 + 2 * layout.word &&
  [layout.codeSlots, layout.codeFieldSlots, layout.nameSlots, layout.nameBytes,
    layout.environmentSlots, layout.environmentWidth, layout.recordSlots,
    layout.recordWidth].all (· < 2^layout.word)

end Minidregg.Compiler.ObjectiveDemandLayout
