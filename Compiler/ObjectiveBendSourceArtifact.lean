/- Objective source publication carrier, edition 1. The selected source
Package/declaration and canonical annotated Core4 packet are distinct identities.
Checking establishes typed core only; a captured-source elaboration witness and
current source-read/authority remain receiving obligations. -/
import Compiler.NativeInvocationStatement
import Compiler.PolicyRecordCodec
import Theory.ObjectiveBendTyping
import Theory.AssertAxioms

namespace Minidregg.Compiler.ObjectiveBendSourceArtifact
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.ObjectiveBendTyping
open Lean
set_option autoImplicit false

structure Artifact where
  package : Digest
  declaration : String
  /-- Exact canonical typed-core.v2 JSON of the selected definition. -/
  typedCore : List UInt8
  inputCodec : Digest
  outputCodec : Digest
  deriving DecidableEq, Repr

def stream : StreamCodec Artifact :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product bytesStream (StreamCodec.product digestStream digestStream))))
    (fun a => (a.package,a.declaration,a.typedCore,a.inputCodec,a.outputCodec))
    (fun a => ⟨a.1,a.2.1,a.2.2.1,a.2.2.2.1,a.2.2.2.2⟩)
    (by intro a; cases a; rfl)

def frame : List UInt8 := "DREGG/OBJECTIVE-BEND/SOURCE-ARTIFACT".toUTF8.toList ++ [1]
def rawCodec : LawfulCodec Artifact where
  encode a := frame ++ stream.encode a
  decode bytes := if bytes.take frame.length = frame then
    stream.toLawful.decode (bytes.drop frame.length) else none
  decode_encode := by
    intro a
    have exact := stream.toLawful.decode_encode a
    change stream.toLawful.decode (stream.encode a) = some a at exact
    simp [exact]
def codec : LawfulCodec Artifact := ResourceBirthCodec.strictCodec rawCodec
abbrev encode := codec.encode
abbrev decode := codec.decode

def identity (a : Artifact) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.SOURCE-ARTIFACT/v1".toUTF8.toList (encode a)).digest

def schema : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.SOURCE-ARTIFACT-SCHEMA/v1".toUTF8.toList frame).digest

/-- The complete packet byte cap precedes UTF8/JSON/natural construction. This
bounds decoding input size; native scalar-bit and graph-work caps are separate. -/
def parsePacket (maxBytes : Nat) (bytes : List UInt8) : Except String Json := do
  if bytes.length > maxBytes then throw "Objective source packet byte capacity"
  let some text := String.fromUTF8? ⟨bytes.toArray⟩ | throw "Objective source UTF8"
  let json ← Json.parse text
  if json.compress.toUTF8.toList != bytes then throw "Objective source packet canonical JSON"
  pure json

/-- Authoring canonicalizes a real frontend packet without changing its parsed
JSON. Receiver checking still requires exact canonical bytes. -/
def canonicalizePacket (maxBytes : Nat) (bytes : List UInt8) : Except String (List UInt8) := do
  if bytes.length > maxBytes then throw "Objective source packet byte capacity"
  let some text := String.fromUTF8? ⟨bytes.toArray⟩ | throw "Objective source UTF8"
  let json ← Json.parse text
  let canonical := json.compress.toUTF8.toList
  if canonical.length > maxBytes then throw "Objective canonical source byte capacity"
  pure canonical

structure Checked (artifact : Artifact) (maxBytes : Nat) where
  private mk ::
  packetJson : Json
  jsonExact : parsePacket maxBytes artifact.typedCore = .ok packetJson
  packet : DecodedPacket
  packetExact : decodePacket packetJson = .ok packet
  closed : packet.context = []
  typed : Minidregg.Theory.ObjectiveBendTyping.Checked packet.source []

def checkWithin (artifact : Artifact) (maxBytes maxFuel : Nat) : Except String (Checked artifact maxBytes) := do
  if artifact.declaration.isEmpty then throw "Objective selected declaration required"
  match jsonExact : parsePacket maxBytes artifact.typedCore with
  | .error reason => throw reason
  | .ok json =>
    match packetExact : decodePacket json with
    | .error reason => throw reason
    | .ok packet =>
      if packet.fuel > maxFuel then throw "Objective source type-work capacity"
      if closed : packet.context = [] then
        let some typed := Minidregg.Theory.ObjectiveBendTyping.check packet.source [] packet.fuel
          | throw "Objective source typing/ownership refusal"
        pure ⟨json,jsonExact,packet,packetExact,closed,typed⟩
      else throw "Objective source definition must be closed"

def check (artifact : Artifact) (maxBytes : Nat) : Except String (Checked artifact maxBytes) :=
  checkWithin artifact maxBytes 16384

@[simp] theorem roundtrip (a : Artifact) : decode (encode a) = some a := codec.decode_encode a

theorem encode_injective {a b : Artifact} (same : encode a = encode b) : a = b := by
  have decoded := congrArg decode same
  simpa only [roundtrip,Option.some.injEq] using decoded

theorem decoded_canonical {bytes : List UInt8} {a : Artifact}
    (accepted : decode bytes = some a) : encode a = bytes :=
  ResourceBirthCodec.strictCodec_canonical rawCodec accepted

theorem selected_core_exact {a : Artifact} {maxBytes : Nat} (checked : Checked a maxBytes) :
    decodePacket checked.packetJson = .ok checked.packet := checked.packetExact

#assert_axioms roundtrip
#assert_axioms encode_injective
#assert_axioms decoded_canonical
#assert_axioms selected_core_exact
end Minidregg.Compiler.ObjectiveBendSourceArtifact
