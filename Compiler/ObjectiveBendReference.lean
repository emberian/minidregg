/- Compact instance behavior pins address exact governed source content. The
instance stores references, not repeated source packages or composed Books.
References never authorize a read; the native loader must authenticate the
current resource root, atom schema/content identity and exact closure. -/
import Compiler.ObjectiveBendPrototype
import Compiler.BendCoreAdmission

namespace Minidregg.Compiler.ObjectiveBendReference
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

structure Reference where
  resource : Nat
  root : Digest
  content : Digest
  deriving DecidableEq, Repr

def referenceStream : StreamCodec Reference :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream digestStream))
    (fun reference => (reference.resource, reference.root, reference.content))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩) (by intro reference; cases reference; rfl)

structure Pin where
  partials : List Reference
  /-- Exact composed source is stored independently of backend/profile metadata. -/
  core : Reference
  deriving DecidableEq, Repr

def pinStream : StreamCodec Pin :=
  StreamCodec.xmap (StreamCodec.product (StreamCodec.list referenceStream) referenceStream)
    (fun pin => (pin.partials, pin.core))
    (fun tuple => ⟨tuple.1, tuple.2⟩) (by intro pin; cases pin; rfl)
def frame : List UInt8 := "DREGG/OBJECTIVE-BEND/INSTANCE-REF/v1".toUTF8.toList
def encode (pin : Pin) : List UInt8 := frame ++ pinStream.encode pin
def decode (bytes : List UInt8) : Option Pin := NockProgramCodec.framedDecode frame pinStream bytes

def rootId (pin : Pin) : Option Nat := pin.partials.getLast?.map (fun reference => reference.content.value)

def partialDigest (prototype : ObjectiveBendPrototype.Partial) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.PROTOTYPE/v1".toUTF8.toList
    (ObjectiveBendPrototype.encode prototype)).digest

def partialSchema : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.PARTIAL-SCHEMA/v1".toUTF8.toList []).digest

structure Core where
  partials : List Digest
  book : List UInt8
  deriving DecidableEq, Repr

def coreStream : StreamCodec Core :=
  StreamCodec.xmap (StreamCodec.product (StreamCodec.list digestStream) bytesStream)
    (fun core => (core.partials, core.book)) (fun pair => ⟨pair.1, pair.2⟩)
    (by intro core; cases core; rfl)
def coreFrame : List UInt8 := "DREGG/OBJECTIVE-BEND/COMPOSED-SOURCE/v1".toUTF8.toList
def encodeCore (core : Core) : List UInt8 := coreFrame ++ coreStream.encode core
def decodeCore (bytes : List UInt8) : Option Core :=
  NockProgramCodec.framedDecode coreFrame coreStream bytes
def coreIdentity (core : Core) : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.COMPOSED-SOURCE/v1".toUTF8.toList
    (encodeCore core)).digest
def coreSchema : Digest :=
  (Sp800185Cshake256.hash "DREGG.OBJECTIVE-BEND.CORE-SCHEMA/v1".toUTF8.toList []).digest

/-- Transient loaded source must match every ordered persistent identity. Root
hash collision resistance is an external assumption, never an injectivity axiom
smuggled into the codec proof. -/
def Matches (pin : Pin) (partials : List ObjectiveBendPrototype.Partial)
    (core : Core) : Prop :=
  pin.partials.map Reference.content = partials.map partialDigest ∧
  pin.core.content = coreIdentity core ∧ core.partials = partials.map partialDigest

instance matchesDecidable (pin : Pin) (partials : List ObjectiveBendPrototype.Partial)
    (core : Core) : Decidable (Matches pin partials core) := by
  unfold Matches; infer_instance

theorem partial_identity_exact (prototype : ObjectiveBendPrototype.Partial) :
    (partialDigest prototype).value = ObjectiveBendPrototype.identity prototype := rfl

theorem roundtrip (pin : Pin) : decode (encode pin) = some pin :=
  NockProgramCodec.framedDecode_encode frame pinStream pin

theorem canonical {bytes : List UInt8} {pin : Pin} (accepted : decode bytes = some pin) :
    encode pin = bytes := NockProgramCodec.framedDecode_canonical accepted

theorem core_roundtrip (core : Core) : decodeCore (encodeCore core) = some core :=
  NockProgramCodec.framedDecode_encode coreFrame coreStream core

theorem core_canonical {bytes : List UInt8} {core : Core} (accepted : decodeCore bytes = some core) :
    encodeCore core = bytes := NockProgramCodec.framedDecode_canonical accepted

#assert_axioms core_roundtrip
#assert_axioms core_canonical
#assert_axioms partial_identity_exact
#assert_axioms roundtrip
#assert_axioms canonical
end Minidregg.Compiler.ObjectiveBendReference
