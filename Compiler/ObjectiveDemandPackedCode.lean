/- Fixed-width public ROM tables for every Objective constructor. This
translates the actual admitted Code, retains exact reconstruction evidence,
and refuses width/field capacity overflow. Runtime lookup can scan these
same tables; no source-dependent secret code publication is performed. -/
import Compiler.ObjectiveDemandCode

namespace Minidregg.Compiler.ObjectiveDemandPackedCode
open Minidregg.Theory.ObjectiveBendOpenRecursion
open ObjectiveDemandCode
set_option autoImplicit false

structure Row where
  tag : Nat
  a : Nat := 0
  b : Nat := 0
  c : Nat := 0
  primitive : Nat := 0
  deriving Repr, DecidableEq

structure Table where
  names : Array String
  rows : Array Row
  fields : Array (Nat × Nat)
  deriving Repr, DecidableEq

def primitiveTag : Primitive → Nat
  | .add => 0 | .multiply => 1 | .equal => 2 | .conjunction => 3 | .labelEqual => 4
  | .subtract => 5 | .divide => 6 | .less => 7 | .lessEqual => 8

def primitiveOf : Nat → Option Primitive
  | 0 => some .add | 1 => some .multiply | 2 => some .equal | 3 => some .conjunction
  | 4 => some .labelEqual | 5 => some .subtract | 6 => some .divide | 7 => some .less
  | 8 => some .lessEqual | _ => none

/-- Row layout widths: a 5-bit opcode, a 3-bit primitive, then three words. -/
def tagBits : Nat := 5
def primitiveBits : Nat := 4

def lowerRow (base : Nat) : Code → Row × List (Nat × Nat)
  | .bound a => (⟨0,a,0,0,0⟩,[])
  | .lam a => (⟨1,a,0,0,0⟩,[])
  | .app a b => (⟨2,a,b,0,0⟩,[])
  | .mix a b => (⟨3,a,b,0,0⟩,[])
  | .fix a b => (⟨4,a,b,0,0⟩,[])
  | .specification a b => (⟨5,a,b,0,0⟩,[])
  | .prototype a b => (⟨6,a,b,0,0⟩,[])
  | .reflect a => (⟨7,a,0,0,0⟩,[])
  | .metadata a => (⟨8,a,0,0,0⟩,[])
  | .project a => (⟨9,a,0,0,0⟩,[])
  | .natural a => (⟨10,a,0,0,0⟩,[])
  | .boolean a => (⟨11,if a then 1 else 0,0,0,0⟩,[])
  | .label a => (⟨12,a,0,0,0⟩,[])
  | .binary p a b => (⟨13,a,b,0,primitiveTag p⟩,[])
  | .extend a fields => (⟨14,a,base,fields.length,0⟩,fields)
  | .record fields => (⟨15,base,fields.length,0,0⟩,fields)
  | .get a b => (⟨16,a,b,0,0⟩,[])
  | .ifZero a b c => (⟨17,a,b,c,0⟩,[])
  | .inject name payload => (⟨18,name,payload,0,0⟩,[])
  | .case a arms => (⟨19,a,base,arms.length,0⟩,arms)
  | .ifBool a b c => (⟨20,a,b,c,0⟩,[])
  | .perform a => (⟨21,a,0,0,0⟩,[])
  | .done a => (⟨22,a,0,0,0⟩,[])

def lower (program : Program) : Table :=
  program.code.foldl (fun table code =>
    let (row,fields) := lowerRow table.fields.size code
    {table with rows:=table.rows.push row, fields:=table.fields ++ fields.toArray})
    ⟨program.names,#[],#[]⟩

def fieldSlice (fields : Array (Nat × Nat)) (offset count : Nat) : Option (List (Nat × Nat)) :=
  if offset+count ≤ fields.size then some ((fields.extract offset (offset+count)).toList) else none

def decodeRow (fields : Array (Nat × Nat)) (row : Row) : Option Code := do
  match row.tag with
  | 0 => pure (.bound row.a)
  | 1 => pure (.lam row.a)
  | 2 => pure (.app row.a row.b)
  | 3 => pure (.mix row.a row.b)
  | 4 => pure (.fix row.a row.b)
  | 5 => pure (.specification row.a row.b)
  | 6 => pure (.prototype row.a row.b)
  | 7 => pure (.reflect row.a)
  | 8 => pure (.metadata row.a)
  | 9 => pure (.project row.a)
  | 10 => pure (.natural row.a)
  | 11 => if row.a ≤ 1 then pure (.boolean (row.a == 1)) else none
  | 12 => pure (.label row.a)
  | 13 => pure (.binary (← primitiveOf row.primitive) row.a row.b)
  | 14 => pure (.extend row.a (← fieldSlice fields row.b row.c))
  | 15 => pure (.record (← fieldSlice fields row.a row.b))
  | 16 => pure (.get row.a row.b)
  | 17 => pure (.ifZero row.a row.b row.c)
  | 18 => pure (.inject row.a row.b)
  | 19 => pure (.case row.a (← fieldSlice fields row.b row.c))
  | 20 => pure (.ifBool row.a row.b row.c)
  | 21 => pure (.perform row.a)
  | 22 => pure (.done row.a)
  | _ => none

def decode (table : Table) : Option Program := do
  pure ⟨table.names,← table.rows.mapM (decodeRow table.fields)⟩

def Table.fits (width maxFields : Nat) (table : Table) : Bool :=
  table.names.size < 2^width && table.rows.size < 2^width &&
  table.fields.size < 2^width && table.fields.size ≤ maxFields &&
  table.rows.all (fun row => row.tag < 2^tagBits && row.primitive < 2^primitiveBits &&
    row.a < 2^width && row.b < 2^width && row.c < 2^width) &&
  table.fields.all (fun field => field.1 < 2^width && field.2 < 2^width)

structure Encoded (program : Program) (width maxFields : Nat) where
  table : Table
  fits : table.fits width maxFields = true
  exact : decode table = some program

/-- Translation validation uses actual complete tables, not a hash or a
caller-supplied decode premise. A successful value retains the proof. -/
def encode (program : Program) (width maxFields : Nat) : Option (Encoded program width maxFields) := do
  let table := lower program
  if fits : table.fits width maxFields = true then
    if exact : decode table = some program then some ⟨table,fits,exact⟩ else none
  else none

def natBits (width value : Nat) : Array Bool := (List.range width).toArray.map value.testBit
def Row.bits (width : Nat) (row : Row) : Array Bool :=
  natBits tagBits row.tag ++ natBits primitiveBits row.primitive ++ natBits width row.a ++ natBits width row.b ++ natBits width row.c
def Table.codeBits (width : Nat) (table : Table) : Array Bool :=
  table.rows.foldl (fun out row => out ++ row.bits width) #[]
def Table.fieldBits (width : Nat) (table : Table) : Array Bool :=
  table.fields.foldl (fun out field => out ++ natBits width field.1 ++ natBits width field.2) #[]

theorem encoded_source {source : Term} (compiled : Compiled source) {width maxFields : Nat}
    (encoded : Encoded compiled.program width maxFields) :
    (decode encoded.table).bind
      (fun program => ObjectiveDemandCode.decode program compiled.decodeDepth compiled.entry) = some source := by
  rw [encoded.exact]
  exact compiled.exact

#assert_axioms encoded_source
end Minidregg.Compiler.ObjectiveDemandPackedCode

