/- Canonical public key-material registration payload. Native authored storage
attributes the exact public material to a current member. This codec does not
prove secret-key possession, input validity, crypto security or threshold custody.
-/
import Compiler.BendInvocation

namespace Minidregg.Compiler.BendKeyRecord
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false

structure PublicMaterial where
  profile : String
  parametersSHA256 : String
  transformerSHA256 : String
  epochSHA256 : String
  publicKey : List UInt8
  relinearizationKey : Option (List UInt8)
  deriving DecidableEq, Repr
structure Registered where
  subject : SubjectId
  artifact : Digest
  method : Digest
  material : PublicMaterial
  deriving DecidableEq, Repr

def materialStream : StreamCodec PublicMaterial :=
  StreamCodec.xmap (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product PolicyRecordCodec.stringStream
    (StreamCodec.product bytesStream (StreamCodec.option bytesStream))))))
    (fun p => (p.profile, p.parametersSHA256, p.transformerSHA256,
      p.epochSHA256, p.publicKey, p.relinearizationKey))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩)
    (by intro p; cases p; rfl)
def stream : StreamCodec Registered :=
  StreamCodec.xmap (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream materialStream)))
    (fun r => (r.subject, r.artifact, r.method, r.material))
    (fun r => ⟨r.1, r.2.1, r.2.2.1, r.2.2.2⟩) (by intro r; cases r; rfl)
def frame : List UInt8 := "DREGG/BEND/REGISTERED-KEY/v1".toUTF8.toList
def encode (r : Registered) : List UInt8 := frame ++ stream.encode r
def decode (bytes : List UInt8) : Option Registered :=
  NockProgramCodec.framedDecode frame stream bytes
def keyId (r : Registered) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.REGISTERED-KEY/v1".toUTF8.toList (encode r)).digest

theorem roundtrip (r : Registered) : decode (encode r) = some r :=
  NockProgramCodec.framedDecode_encode frame stream r
theorem canonical {bytes : List UInt8} {r : Registered}
    (h : decode bytes = some r) : encode r = bytes :=
  NockProgramCodec.framedDecode_canonical h

end Minidregg.Compiler.BendKeyRecord
