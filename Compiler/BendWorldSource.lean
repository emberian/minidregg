/- Sealed Bend source provenance. This is a canonical artifact codec, not a
source parser or permission to execute. The upstream parser/elaborator must
establish that these imports are the imports actually used by the checked Book.
No loader, network operation or foreign IO is performed by this module. -/
import Compiler.NockProgramCodec

namespace Minidregg.Compiler.BendWorldSource
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

def upstreamPin : String := "947db722640c86247849343657bf2f7ef01cb7f1"
def upstreamToolchain : String := "leanprover/lean4:v4.34.0"
def miniToolchain : String := "leanprover/lean4:v4.30.0"

structure Import where
  importAlias : String
  moduleIndex : Nat
  source : Digest
  deriving DecidableEq, Repr

structure Module where
  name : String
  bytes : List UInt8
  imports : List Import
  deriving DecidableEq, Repr

structure Package where
  modules : List Module
  entryModule : Nat
  entryDefinition : String
  deriving DecidableEq, Repr

def importStream : StreamCodec Import :=
  StreamCodec.xmap (StreamCodec.product PolicyRecordCodec.stringStream
      (StreamCodec.product StreamCodec.nat digestStream))
    (fun i => (i.importAlias, i.moduleIndex, i.source))
    (fun i => ⟨i.1, i.2.1, i.2.2⟩) (by intro i; cases i; rfl)

def moduleStream : StreamCodec Module :=
  StreamCodec.xmap (StreamCodec.product PolicyRecordCodec.stringStream
      (StreamCodec.product bytesStream (StreamCodec.list importStream)))
    (fun m => (m.name, m.bytes, m.imports))
    (fun m => ⟨m.1, m.2.1, m.2.2⟩) (by intro m; cases m; rfl)

def packageStream : StreamCodec Package :=
  StreamCodec.xmap (StreamCodec.product (StreamCodec.list moduleStream)
      (StreamCodec.product StreamCodec.nat PolicyRecordCodec.stringStream))
    (fun p => (p.modules, p.entryModule, p.entryDefinition))
    (fun p => ⟨p.1, p.2.1, p.2.2⟩) (by intro p; cases p; rfl)

def frame : List UInt8 := "DREGG/BEND/SOURCE/v1".toUTF8.toList
def encode (p : Package) : List UInt8 := frame ++ packageStream.encode p
def decode (bytes : List UInt8) : Option Package :=
  NockProgramCodec.framedDecode frame packageStream bytes

/-- Exact author bytes: line endings, comments and encoding are not normalized.
The package identity separately binds entry, module order and import aliases. -/
def sourceId (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.SOURCE/v1".toUTF8.toList bytes).digest

def packageId (p : Package) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.PACKAGE/v1".toUTF8.toList (encode p)).digest

def nameValid (name : String) : Bool :=
  !name.isEmpty && decide (NockProgramCodec.NulFree name)

/-- Imports address earlier sealed modules by index and exact source digest.
This refuses cycles, missing imports, alias ambiguity and changed imported bytes.
It does not attest that a manifest corresponds to the source syntax. -/
def wellFormed (p : Package) : Bool :=
  decide (p.entryModule < p.modules.length ∧ (p.modules.map Module.name).Nodup) &&
  nameValid p.entryDefinition &&
  (List.finRange p.modules.length).all fun index =>
    let m := p.modules[index]
    nameValid m.name && decide ((m.imports.map Import.importAlias).Nodup) &&
    m.imports.all fun i =>
      decide (i.moduleIndex < index.val) &&
      match p.modules[i.moduleIndex]? with
      | none => false
      | some imported =>
          (nameValid i.importAlias || decide (i.importAlias = "" ∧ imported.name = "Base")) &&
          decide (sourceId imported.bytes = i.source)

/-- Decoding accepts exactly the canonical framed encoding, with no trailing bytes. -/
theorem decode_canonical {bytes : List UInt8} {p : Package}
    (h : decode bytes = some p) : encode p = bytes :=
  NockProgramCodec.framedDecode_canonical h

theorem roundtrip (p : Package) : decode (encode p) = some p :=
  NockProgramCodec.framedDecode_encode frame packageStream p

end Minidregg.Compiler.BendWorldSource
