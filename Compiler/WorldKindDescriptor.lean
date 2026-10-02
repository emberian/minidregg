/-
World-resident layout descriptors interpreted by the existing typed Store and
StoreCodec. This module is a source-owned codec/layout implementation, not a
native endpoint: authentication, birth binding and law admission must be
connected before a caller may install these values in the serving registry.
-/
import Compiler.StoreCodec
import Compiler.IntStream
import Compiler.PolicyRecordCodec
import Compiler.ResourceBirthCodec

namespace Minidregg.Compiler.WorldKindDescriptor

open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.PolicyRecordCodec (stringStream)

set_option autoImplicit false

/-- This is a compiled primitive menu, not a list of member-defined kinds.
A poll, inventory, score table or namespace does not add a constructor here. -/
inductive ScalarCodec where
  | natural
  | integer
  | bytes
  deriving DecidableEq, Repr

def ScalarCodec.Value : ScalarCodec → Type
  | .natural => Nat
  | .integer => Int
  | .bytes => List UInt8

instance scalarValueDecidable (codec : ScalarCodec) : DecidableEq codec.Value := by
  cases codec <;> unfold ScalarCodec.Value <;> infer_instance

def ScalarCodec.stream : (codec : ScalarCodec) → StreamCodec codec.Value
  | .natural => StreamCodec.nat
  | .integer => IntStream.intStream
  | .bytes => bytesStream

def ScalarCodec.codecId : ScalarCodec → String
  | .natural => "nat/base255-v1"
  | .integer => IntStream.intCodecId
  | .bytes => "bytes/length-prefix-v1"

def scalarCodecStream : StreamCodec ScalarCodec where
  encode
    | .natural => [0]
    | .integer => [1]
    | .bytes => [2]
  decodePrefix
    | 0 :: rest => some (.natural, rest)
    | 1 :: rest => some (.integer, rest)
    | 2 :: rest => some (.bytes, rest)
    | _ => none
  decodePrefix_encode := by intro codec suffix; cases codec <;> rfl

def disciplineStream : StreamCodec Discipline where
  encode
    | .rom => [0]
    | .ram => [1]
    | .appendOnly => [2]
  decodePrefix
    | 0 :: rest => some (.rom, rest)
    | 1 :: rest => some (.ram, rest)
    | 2 :: rest => some (.appendOnly, rest)
    | _ => none
  decodePrefix_encode := by intro discipline suffix; cases discipline <;> rfl

/-- Semantic identity and its definition are canonical schema data. Equal
storage types or equal numeric field IDs do not establish equal authority.
The label is for people; meaning identifies what a grant permits. -/
structure Field where
  id : Nat
  name : String
  meaning : String
  codec : ScalarCodec
  discipline : Discipline
  deriving DecidableEq, Repr

def fieldStream : StreamCodec Field :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product stringStream
        (StreamCodec.product stringStream
          (StreamCodec.product scalarCodecStream disciplineStream))))
    (fun field => (field.id, field.name, field.meaning, field.codec, field.discipline))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2⟩)
    (by intro field; cases field; rfl)

/-- Layout revisions are immutable. A live kind head can select a later
revision for new births; existing instances retain their exact descriptor. -/
structure Descriptor where
  kind : Nat
  revision : Nat
  fields : List Field
  deriving DecidableEq, Repr

def descriptorStream : StreamCodec Descriptor :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.list fieldStream)))
    (fun descriptor => (descriptor.kind, descriptor.revision, descriptor.fields))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro descriptor; cases descriptor; rfl)

def descriptorCodec : LawfulCodec Descriptor :=
  ResourceBirthCodec.strictCodec descriptorStream.toLawful

def Descriptor.Valid (descriptor : Descriptor) : Prop :=
  (descriptor.fields.map Field.id).Nodup ∧
  (descriptor.fields.map Field.name).Nodup ∧
  ∀ field ∈ descriptor.fields, field.name ≠ "" ∧ field.meaning ≠ ""

instance descriptorValidDecidable (descriptor : Descriptor) : Decidable descriptor.Valid := by
  unfold Descriptor.Valid
  infer_instance

/-- Canonical decoding is not enough: duplicate semantic addresses/names and
empty meaning declarations refuse before installation. -/
def decodeDefinition (bytes : List UInt8) : Option { descriptor : Descriptor // descriptor.Valid } := do
  let descriptor ← descriptorCodec.decode bytes
  if valid : descriptor.Valid then some ⟨descriptor, valid⟩ else none

theorem descriptor_roundtrip (descriptor : Descriptor) :
    descriptorCodec.decode (descriptorCodec.encode descriptor) = some descriptor :=
  descriptorCodec.decode_encode descriptor

theorem definition_roundtrip (descriptor : Descriptor) (valid : descriptor.Valid) :
    decodeDefinition (descriptorCodec.encode descriptor) = some ⟨descriptor, valid⟩ := by
  simp [decodeDefinition, descriptor_roundtrip, valid]

def Descriptor.identity (descriptor : Descriptor) : Digest :=
  (Sp800185Cshake256.hash "DREGG.WORLD.KIND.LAYOUT/v1".toUTF8.toList
    (descriptorCodec.encode descriptor)).digest

/-- One namespace per named field; a scalar uses key zero, a map uses arbitrary
natural keys. Both use precisely Store's existing ROM/RAM/append-only rules.
No blob cast or host-provided decoder is involved. -/
def layout (descriptor : Descriptor) : Layout.{0, 0, 0} where
  Namespace := Fin descriptor.fields.length
  Key := fun _ => Nat
  Value := fun space => (descriptor.fields.get space).codec.Value
  discipline := fun space => (descriptor.fields.get space).discipline

def finStream (size : Nat) : StreamCodec (Fin size) where
  encode index := StreamCodec.nat.encode index.val
  decodePrefix bytes := do
    let (index, suffix) ← StreamCodec.nat.decodePrefix bytes
    if bound : index < size then some (⟨index, bound⟩, suffix) else none
  decodePrefix_encode := by
    intro index suffix
    simp [StreamCodec.nat.decodePrefix_encode, index.isLt]

/-- StoreCodec's frame commits to the complete descriptor identity, including
field meanings. Its namespace order is not an implicit grant interpretation.
Hash collision resistance remains an explicit external assumption. -/
def wire (descriptor : Descriptor) : StoreCodec.Wire (layout descriptor) where
  name := "minidregg/world-kind/v1/" ++ toString descriptor.identity.value
  namespaces := List.finRange descriptor.fields.length
  namespaces_complete := by intro space; simp
  namespaceStream := finStream descriptor.fields.length
  keyStream := fun _ => StreamCodec.nat
  valueStream := fun space => (descriptor.fields.get space).codec.stream
  keyCodecId := fun _ => "nat/base255-v1"
  valueCodecId := fun space => (descriptor.fields.get space).codec.codecId

def materializer (descriptor : Descriptor) := StoreCodec.materializer (wire descriptor)

/-- The existing generic theorem gives the descriptor-generic K4 exit. -/
theorem layout_of_descriptor_roundtrip (descriptor : Descriptor)
    (store : Store (layout descriptor)) :
    StoreCodec.decode (wire descriptor) (StoreCodec.encode (wire descriptor) store) = some store :=
  StoreCodec.decode_encode (wire descriptor) store

theorem instance_rom_preserved (descriptor : Descriptor) (store : Store (layout descriptor))
    (patch : Patch (layout descriptor)) (address : Address (layout descriptor))
    (valid : Patch.ValidFrom store patch)
    (rom : (descriptor.fields.get address.1).discipline = .rom) :
    Patch.run store patch address = store address :=
  Patch.rom_preserved store patch address valid rom

/-- Capability meaning is bound to the descriptor, including an all-fields
scope. Selecting a later descriptor never implicitly widens an old grant. -/
structure Scope where
  descriptor : Descriptor
  fields : Option (List Nat)
  deriving DecidableEq, Repr

def Scope.Covers (scope : Scope) (descriptor : Descriptor) (field : Nat) : Prop :=
  scope.descriptor = descriptor ∧
  field ∈ descriptor.fields.map Field.id ∧
  (scope.fields = none ∨ ∃ fields, scope.fields = some fields ∧ field ∈ fields)

theorem all_fields_does_not_cross_revision (old next : Descriptor) (field : Nat)
    (changed : old ≠ next) : ¬ (Scope.mk old none).Covers next field := by
  intro covered
  exact changed covered.1

end Minidregg.Compiler.WorldKindDescriptor
