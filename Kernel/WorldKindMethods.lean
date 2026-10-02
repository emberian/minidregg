/- Source-owned executable method bindings for descriptor-interpreted instances.
After-core construction: not activated by the frozen native runtime profile.
Methods select immutable existing programs; they confer no mutation authority.
-/
import Compiler.WorldExecutionContract
import Compiler.WorldKindCell
import Compiler.NockProgramCodec
import Theory.Eval

namespace Minidregg.Kernel.WorldKindMethods

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.WorldKindDescriptor
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Store
open Minidregg.Kernel.WorldKindInstance

set_option autoImplicit false

/-- Descriptor-declared semantics, not a reserved numeric field or display name.
Exactly one ROM bytes field may carry the canonical table at key zero. -/
def tableMeaning : String := WorldExecutionContract.methodTableMeaning

/-- Existing evaluator output coordinates are explicitly bound to inner addresses.
The complete descriptor fixes the target field's meaning and codec. -/
structure OutputBinding where
  output : Nat
  field : Nat
  key : Nat
  deriving DecidableEq, Repr

structure Method where
  name : String
  program : Digest
  outputs : List OutputBinding
  deriving DecidableEq, Repr

abbrev Table := List Method

def outputStream : StreamCodec OutputBinding :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))
    (fun value => (value.output, value.field, value.key))
    (fun value => ⟨value.1, value.2.1, value.2.2⟩)
    (by intro value; cases value; rfl)

def methodStream : StreamCodec Method :=
  StreamCodec.xmap (StreamCodec.product PolicyRecordCodec.stringStream
      (StreamCodec.product digestStream (StreamCodec.list outputStream)))
    (fun value => (value.name, value.program, value.outputs))
    (fun value => ⟨value.1, value.2.1, value.2.2⟩)
    (by intro value; cases value; rfl)

def frame : List UInt8 := WorldExecutionContract.methodTableFrame

def encode (table : Table) : List UInt8 :=
  frame ++ (StreamCodec.list methodStream).encode table

def decode (bytes : List UInt8) : Option Table :=
  NockProgramCodec.framedDecode frame (StreamCodec.list methodStream) bytes

/-- Every mapped output has a distinct numeric address and evaluator coordinate.
ROM, bytes, unknown fields, duplicate method names/programs and aliases refuse. -/
def valid (descriptor : Descriptor) (table : Table) : Bool :=
  decide ((table.map Method.name).Nodup ∧ (table.map Method.program).Nodup) &&
  table.all fun method =>
    method.name != "" &&
    decide ((method.outputs.map OutputBinding.output).Nodup ∧
      (method.outputs.map fun output => (output.field, output.key)).Nodup) &&
    method.outputs.all fun output =>
      match descriptor.fields.find? (fun field => field.id == output.field) with
      | none => false
      | some field => field.codec != .bytes && field.discipline != .rom

/-- Read through the actual retained typed store. A caller cannot supply the
method table separately from the instance root authenticated by the transaction. -/
def tableOf (value : Instance) : Option Table := do
  let spaces := (List.finRange value.descriptor.fields.length).filter fun space =>
    (value.descriptor.fields.get space).meaning == tableMeaning
  let [space] := spaces | none
  let field := value.descriptor.fields.get space
  if field.codec != .bytes || field.discipline != .rom then none else do
    let raw ← value.store ⟨space, (0 : Nat)⟩
    -- Reuse the declared scalar codec rather than casting a dependent value.
    let bytes ← (ResourceBirthCodec.strictCodec bytesStream.toLawful).decode
      (field.codec.stream.encode raw)
    let table ← decode bytes
    if valid value.descriptor table then some table else none

def resolve (value : Instance) (program : Digest) : Option Method := do
  let table ← tableOf value
  table.find? fun method => method.program == program

def numeric (codec : ScalarCodec) (bytes : List UInt8) : Option Int :=
  match codec with
  | .natural => ((ResourceBirthCodec.strictCodec StreamCodec.nat.toLawful).decode bytes).map Int.ofNat
  | .integer => (ResourceBirthCodec.strictCodec IntStream.intStream.toLawful).decode bytes
  | .bytes => none

/-- Exact writes only: no erasure, byte payload or read is represented as an
integer output. This adapter never constructs or substitutes the actual patch. -/
def actionWrite (descriptor : Descriptor) (method : Method) (target : Nat)
    (action : Action) : Option Eval.FieldWrite := do
  let (field, key, bytes) ← match action with
    | .create field key bytes => some (field, key, bytes)
    | .write field key _ bytes => some (field, key, bytes)
    | .read _ _ _ | .erase _ _ _ => none
  let binding ← method.outputs.find? fun output => output.field == field && output.key == key
  let definition ← descriptor.fields.find? fun definition => definition.id == field
  let value ← numeric definition.codec bytes
  pure ⟨target, binding.output, value⟩

/-- A source-bound method has one exact program and distinct effect addresses.
Repeated writes cannot exploit Run.checkRun's set-like membership comparison. -/
def writes (pre : Store WorldKindCell.instanceLayout) (program : Digest)
    (target : Nat) (actions : List Action) : Option (List Eval.FieldWrite) := do
  let value ← WorldKindCell.instanceAt pre
  let method ← resolve value program
  let effects ← actions.mapM (actionWrite value.descriptor method target)
  if (effects.map Eval.FieldWrite.field).Nodup then some effects else none

end Minidregg.Kernel.WorldKindMethods
