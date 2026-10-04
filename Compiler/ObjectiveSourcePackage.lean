/- Objective-only immutable source package identity. Exact author bytes, AST
bytes, ordered import locks and the parser/frontend/elaborator pins have a
separate canonical identity from typed core, execution plan, capacity and
current authority. The elaborator pin names the tool that lowered the selected
declaration to the published typed core; the receiver compares it with the
operator policy (`ObjectiveBendNativeAdmission.SourceSelection.elaboratorExact`),
so the policy's elaborator pin binds the package it admits. Edition 2. -/
import Compiler.NativeInvocationStatement
import Compiler.PolicyRecordCodec
import Theory.AssertAxioms
namespace Minidregg.Compiler.ObjectiveSourcePackage
open Minidregg.Theory Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
set_option autoImplicit false
structure Import where
  importAlias : String
  path : String
  target : Nat
  deriving DecidableEq, Repr
structure Module where
  name : String
  source : List UInt8
  ast : List UInt8
  imports : List Import
  deriving DecidableEq, Repr
structure Package where
  parserSha256 : String
  frontendSha256 : String
  /-- SHA-256 of the exact elaborator/lowerer source that produced the typed core. -/
  elaboratorSha256 : String
  modules : List Module
  entryModule : Nat
  entryDefinition : String
  deriving DecidableEq, Repr

def importStream : StreamCodec Import :=
  StreamCodec.xmap (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream StreamCodec.nat))
    (fun i => (i.importAlias,i.path,i.target)) (fun i => ⟨i.1,i.2.1,i.2.2⟩)
    (by intro i; cases i; rfl)
def moduleStream : StreamCodec Module :=
  StreamCodec.xmap (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.list importStream))))
    (fun m => (m.name,m.source,m.ast,m.imports)) (fun m => ⟨m.1,m.2.1,m.2.2.1,m.2.2.2⟩)
    (by intro m; cases m; rfl)
def stream : StreamCodec Package :=
  StreamCodec.xmap (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream (StreamCodec.product (StreamCodec.list moduleStream)
    (StreamCodec.product StreamCodec.nat PolicyRecordCodec.stringStream)))))
    (fun p => (p.parserSha256,p.frontendSha256,p.elaboratorSha256,p.modules,p.entryModule,p.entryDefinition))
    (fun p => ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2⟩)
    (by intro p; cases p; rfl)
def frame : List UInt8 := "DREGG/OBJECTIVE-BEND/SOURCE-PACKAGE".toUTF8.toList ++ [2]
def rawCodec : LawfulCodec Package where
  encode p := frame ++ stream.encode p
  decode bytes := if bytes.take frame.length = frame then
    stream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro p
    have exact := stream.toLawful.decode_encode p
    change stream.toLawful.decode (stream.encode p) = some p at exact
    simp [exact]
def codec : LawfulCodec Package := ResourceBirthCodec.strictCodec rawCodec
abbrev encode := codec.encode
abbrev decode := codec.decode

def identity (p : Package) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.SOURCE-PACKAGE/v2".toUTF8.toList (encode p)).digest

def selectedDeclaration (p : Package) : Option String :=
  p.modules[p.entryModule]?.map (fun m => m.name ++ "." ++ p.entryDefinition)

def shaPin (s : String) : Bool := s.length == 64 && s.toList.all
  (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f'))
def validName (s : String) : Bool := !s.isEmpty && !s.toList.contains (Char.ofNat 0)
/-- Structural validation only. Parser replay and source/AST/import fingerprint
validation occur in the actual captured-source producer; this is not an
elaboration or semantic correctness theorem. -/
def wellFormed (p : Package) : Bool :=
  shaPin p.parserSha256 && shaPin p.frontendSha256 && shaPin p.elaboratorSha256 &&
  validName p.entryDefinition &&
  decide (p.entryModule < p.modules.length ∧ p.modules.length ≤ 64 ∧ (p.modules.map Module.name).Nodup) &&
  (List.finRange p.modules.length).all fun i =>
    let m := p.modules[i]
    validName m.name && (String.fromUTF8? ⟨m.source.toArray⟩).isSome &&
    (String.fromUTF8? ⟨m.ast.toArray⟩).isSome &&
    decide ((m.imports.map Import.importAlias).Nodup) && m.imports.all
      (fun edge => validName edge.importAlias && validName edge.path && decide (edge.target < i.val))

@[simp] theorem roundtrip (p : Package) : decode (encode p) = some p := codec.decode_encode p
theorem encode_injective {a b : Package} (same : encode a = encode b) : a = b := by
  have decoded := congrArg decode same
  simpa only [roundtrip,Option.some.injEq] using decoded
theorem decoded_canonical {bytes : List UInt8} {p : Package}
    (accepted : decode bytes = some p) : encode p = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCodec accepted
#assert_axioms roundtrip
#assert_axioms encode_injective
#assert_axioms decoded_canonical
end Minidregg.Compiler.ObjectiveSourcePackage
