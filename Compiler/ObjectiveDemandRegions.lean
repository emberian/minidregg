/- The decoder of a packed Objective demand state: ONE function of the public
layout and the bits. It reads the state region AND every table region (code
rows, code field pairs, names, environments, record fields) from the same bits.
It takes no program, no tables and no caller-supplied table producer, so two
programs with different code can never be read through each other's tables.

The earlier tranche decoder read only the state region and interpreted its code
indices against tables supplied beside the bits. That relation is the
`represents` of no refinement of the graph:
Assurance.ObjectiveZkLiteralInstance.externalTables_not_refinement. -/
import Compiler.ObjectiveDemandLayout
import Compiler.ObjectiveDemandStateCodec

namespace Minidregg.Compiler.ObjectiveDemandRegions
open Minidregg.Theory.ObjectiveBendDemandMachine
open ObjectiveDemandLayout ObjectiveDemandPackedCode ObjectiveDemandStorage
set_option autoImplicit false

open ObjectiveDemandStateCodec (number bits)

/-- The opcode of an unused code row. No `Code` lowers to it. -/
def paddingTag : Nat := 31

/-! ### Reading -/

def readRow (layout : Layout) (input : Array Bool) (offset : Nat) : Row :=
  let body := offset + tagBits + primitiveBits
  ⟨number input offset tagBits, number input body layout.word,
    number input (body + layout.word) layout.word, number input (body + 2 * layout.word) layout.word,
    number input (offset + tagBits) primitiveBits⟩

/-- The rows before the first padding row. A live row after padding refuses. -/
def liveRows : List Row → Option (List Row)
  | [] => some []
  | row :: rest =>
    if row.tag == paddingTag then
      if rest.all (·.tag == paddingTag) then some [] else none
    else do pure (row :: (← liveRows rest))

def readRows (layout : Layout) (input : Array Bool) : Option (Array Row) := do
  let rows := (List.range layout.codeSlots).map fun index =>
    readRow layout input (layout.codeOffset + index * rowBits layout.shape)
  pure (← liveRows rows).toArray

def readPairs (layout : Layout) (input : Array Bool) (offset count : Nat) : List (Nat × Nat) :=
  (List.range count).map fun index =>
    (number input (offset + index * (2 * layout.word)) layout.word,
      number input (offset + index * (2 * layout.word) + layout.word) layout.word)

/-- A counted region: a count word, then `slots` fixed-size entries. -/
def readCounted {α : Type} (layout : Layout) (input : Array Bool) (offset slots entryBits : Nat)
    (entry : Nat → Option α) : Option (List α) :=
  let count := number input offset layout.word
  if count ≤ slots then
    (List.range count).mapM fun index => entry (offset + layout.word + index * entryBits)
  else none

def readCodeFields (layout : Layout) (input : Array Bool) : Option (Array (Nat × Nat)) :=
  let count := number input layout.codeFieldOffset layout.word
  if count ≤ layout.codeFieldSlots then
    some (readPairs layout input (layout.codeFieldOffset + layout.word) count).toArray
  else none

def readName (layout : Layout) (input : Array Bool) (offset : Nat) : Option String :=
  let length := number input offset layout.word
  if length ≤ layout.nameBytes then
    String.fromUTF8? ⟨((List.range length).map fun index =>
      (number input (offset + layout.word + 8 * index) 8).toUInt8).toArray⟩
  else none

def readEnvironment (layout : Layout) (input : Array Bool) (offset : Nat) : Option (List Nat) :=
  let length := number input offset layout.word
  if length ≤ layout.environmentWidth then
    some ((List.range length).map fun index =>
      number input (offset + layout.word + index * layout.word) layout.word)
  else none

def readRecord (layout : Layout) (input : Array Bool) (offset : Nat) : Option (List (Nat × Nat)) :=
  let length := number input offset layout.word
  if length ≤ layout.recordWidth then some (readPairs layout input (offset + layout.word) length)
  else none

/-- Every table the state refers to, read from the bits. -/
def readTables (layout : Layout) (input : Array Bool) : Option Tables := do
  let names ← readCounted layout input layout.nameOffset layout.nameSlots layout.nameEntryBits
    (readName layout input)
  let program ← ObjectiveDemandPackedCode.decode
    ⟨names.toArray, ← readRows layout input, ← readCodeFields layout input⟩
  let environments ← readCounted layout input layout.environmentOffset layout.environmentSlots
    layout.environmentEntryBits (readEnvironment layout input)
  let records ← readCounted layout input layout.recordOffset layout.recordSlots
    layout.recordEntryBits (readRecord layout input)
  pure ⟨program, environments.toArray, records.toArray⟩

/-- THE decoder: state and suspension bit, from the layout and the bits alone. -/
def decode (layout : Layout) (input : Array Bool) : Option (State × Bool) :=
  if input.size != layout.inputCount then none else do
    let (reference, suspended) ← ObjectiveDemandStateCodec.decode layout.shape
      (input.extract 0 layout.shape.inputCount)
    let tables ← readTables layout input
    pure (← ObjectiveDemandStorage.decode tables layout.depth reference, suspended)

def state (layout : Layout) (input : Array Bool) : Option State :=
  (decode layout input).map Prod.fst

/-! ### Writing (the producer of initial bits) -/

def word (layout : Layout) (value : Nat) : Option (Array Bool) :=
  if value < 2^layout.word then some (bits layout.word value) else none

def pad (width : Nat) (data : Array Bool) : Option (Array Bool) :=
  if data.size ≤ width then some (data ++ Array.replicate (width - data.size) false) else none

def concat (parts : List (Array Bool)) : Array Bool := parts.foldl (· ++ ·) #[]

def rowFits (layout : Layout) (row : Row) : Bool :=
  row.tag != paddingTag && row.tag < 2^tagBits && row.primitive < 2^primitiveBits &&
    row.a < 2^layout.word && row.b < 2^layout.word && row.c < 2^layout.word

def writeRows (layout : Layout) (rows : Array Row) : Option (Array Bool) :=
  if rows.size ≤ layout.codeSlots && rows.all (rowFits layout) then
    some (concat ((rows.toList ++ List.replicate (layout.codeSlots - rows.size)
      (⟨paddingTag, 0, 0, 0, 0⟩ : Row)).map (Row.bits layout.word)))
  else none

def writePairs (layout : Layout) (pairs : List (Nat × Nat)) : Option (Array Bool) := do
  let parts ← pairs.mapM fun (a, b) => do pure ((← word layout a) ++ (← word layout b))
  pure (concat parts)

def writeCounted {α : Type} (layout : Layout) (slots entryBits : Nat) (entries : List α)
    (entry : α → Option (Array Bool)) : Option (Array Bool) := do
  if entries.length ≤ slots then
    let body ← entries.mapM fun item => do pad entryBits (← entry item)
    pad (layout.word + slots * entryBits) (concat ((← word layout entries.length) :: body))
  else none

def writeCodeFields (layout : Layout) (fields : Array (Nat × Nat)) : Option (Array Bool) := do
  if fields.size ≤ layout.codeFieldSlots then
    pad layout.codeFieldBits ((← word layout fields.size) ++ (← writePairs layout fields.toList))
  else none

def writeName (layout : Layout) (name : String) : Option (Array Bool) := do
  let bytes := name.toUTF8.toList
  if bytes.length ≤ layout.nameBytes then
    pure ((← word layout bytes.length) ++ concat (bytes.map fun byte => bits 8 byte.toNat))
  else none

def writeEnvironment (layout : Layout) (environment : List Nat) : Option (Array Bool) := do
  if environment.length ≤ layout.environmentWidth then
    pure (concat ((← word layout environment.length) :: (← environment.mapM (word layout))))
  else none

def writeRecord (layout : Layout) (fields : List (Nat × Nat)) : Option (Array Bool) := do
  if fields.length ≤ layout.recordWidth then
    pure ((← word layout fields.length) ++ (← writePairs layout fields))
  else none

/-- The table regions, in layout order. -/
def writeTables (layout : Layout) (table : Table) (environments : Array (List Nat))
    (records : Array (List (Nat × Nat))) : Option (Array Bool) := do
  pure ((← writeRows layout table.rows) ++ (← writeCodeFields layout table.fields) ++
    (← writeCounted layout layout.nameSlots layout.nameEntryBits table.names.toList
      (writeName layout)) ++
    (← writeCounted layout layout.environmentSlots layout.environmentEntryBits
      environments.toList (writeEnvironment layout)) ++
    (← writeCounted layout layout.recordSlots layout.recordEntryBits records.toList
      (writeRecord layout)))

def encode (layout : Layout) (reference : StateRef) (table : Table)
    (environments : Array (List Nat)) (records : Array (List (Nat × Nat))) :
    Option (Array Bool) := do
  pure ((← ObjectiveDemandStateCodec.encode layout.shape reference) ++
    (← writeTables layout table environments records))

end Minidregg.Compiler.ObjectiveDemandRegions
