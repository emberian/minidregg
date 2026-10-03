/- Exact public-ROM projection for the fixed Bend controller.
Every Code constructor receives a fixed tag and three bounded payload words.
Name equality uses a publication-checked unique intern table; this module does
not permit a secret-dependent program or selected literal to become public.
ROM/source projection correctness is a separate refinement obligation. -/
import Compiler.BendObliviousAccess
import Compiler.BendClosurePacking

namespace Minidregg.Compiler.BendObliviousProgram
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
open ObliviousNetwork ObliviousWords BendObliviousState BendObliviousAccess
set_option autoImplicit false

structure CodeData where
  tag : Nat
  quantity : Quan := .Q0
  a : Nat := 0
  b : Nat := 0
  c : Nat := 0

def codeData : Code → CodeData
  | .var a => {tag:=0,a}
  | .ref a => {tag:=1,a}
  | .ann a b => {tag:=2,a,b}
  | .lett quantity a b => {tag:=3,quantity,a,b}
  | .typ quantity => {tag:=4,quantity}
  | .all quantity a b => {tag:=5,quantity,a,b}
  | .lam quantity a => {tag:=6,quantity,a}
  | .app quantity a b => {tag:=7,quantity,a,b}
  | .sig quantity a b => {tag:=8,quantity,a,b}
  | .tup quantity a b => {tag:=9,quantity,a,b}
  | .prj a => {tag:=10,a}
  | .enu a => {tag:=11,a}
  | .lab a => {tag:=12,a}
  | .mat a b c => {tag:=13,a,b,c}
  | .efq => {tag:=14}
  | .eql a b c => {tag:=15,a,b,c}
  | .rfl => {tag:=16}
  | .rwt a b c => {tag:=17,a,b,c}

def quantityCode : Quan → Nat
  | .Q0 => 0 | .Q1 => 1 | .Q2 => 2

def codeBits (shape : BendObliviousState.Shape) : Nat := 7 + 3 * shape.wordBits

structure CodeView (shape : BendObliviousState.Shape) where
  tag : Word 5
  quantity : Word 2
  a : Word shape.wordBits
  b : Word shape.wordBits
  c : Word shape.wordBits

def viewCode {shape : BendObliviousState.Shape} (zero : Nat) (row : Word (codeBits shape)) : CodeView shape :=
  ⟨slice zero row 0 5,slice zero row 5 2,
    slice zero row 7 shape.wordBits,
    slice zero row (7+shape.wordBits) shape.wordBits,
    slice zero row (7+2*shape.wordBits) shape.wordBits⟩

def codeConstant (shape : BendObliviousState.Shape) (data : CodeData) : Builder (Word (codeBits shape)) :=
  Vector.ofFnM fun bit =>
    emit (.constant (
      if bit.val < 5 then data.tag.testBit bit.val
      else if bit.val < 7 then (quantityCode data.quantity).testBit (bit.val-5)
      else if bit.val < 7+shape.wordBits then data.a.testBit (bit.val-7)
      else if bit.val < 7+2*shape.wordBits then data.b.testBit (bit.val-(7+shape.wordBits))
      else data.c.testBit (bit.val-(7+2*shape.wordBits))))

structure ROM (shape : BendObliviousState.Shape) (library : Library) where
  code : Vector (Word (codeBits shape)) library.program.code.size
  /-- First bit says that the named definition exists; rest is its code PC.
  Name-index validity is separately returned by the oblivious read. -/
  definitions : Vector (Word (1+shape.wordBits)) library.program.names.size

def build (shape : BendObliviousState.Shape) (library : Library) : Builder (ROM shape library) := do
  let code ← Vector.ofFnM fun index : Fin library.program.code.size =>
    codeConstant shape (codeData library.program.code[index])
  let definitions ← Vector.ofFnM fun index : Fin library.program.names.size => do
    let found := library.lookupName library.program.names[index]
    Vector.ofFnM fun bit =>
      emit (.constant (
        if bit.val = 0 then found.isSome
        else (found.getD 0).testBit (bit.val-1)))
  pure ⟨code,definitions⟩

def readCode {shape : BendObliviousState.Shape} {library : Library} (zero one : Nat)
    (rom : ROM shape library) (address : Word shape.wordBits) :
    Builder (Nat × CodeView shape) := do
  let (valid,row) ← readRows zero one address rom.code
  pure (valid,viewCode zero row)

def readDefinition {shape : BendObliviousState.Shape} {library : Library} (zero one : Nat)
    (rom : ROM shape library) (name : Word shape.wordBits) :
    Builder (Nat × Nat × Word shape.wordBits) := do
  let (nameValid,row) ← readRows zero one name rom.definitions
  pure (nameValid,row.toArray[0]?.getD zero,slice zero row 1 shape.wordBits)

end Minidregg.Compiler.BendObliviousProgram
