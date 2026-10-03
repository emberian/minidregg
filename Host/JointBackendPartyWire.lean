/- Native endpoint authoring for the source-current private-party request.
The plan is signing data only. Only the actual source receiver's ordered Applied
readback can authorize backend work; op203 cannot do so. -/
import Kernel.JointBackendPartyAdmission
namespace Minidregg.Host.JointBackendPartyWire
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.JointBackendPartyCodec
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.JointBackendPartyAdmission
set_option autoImplicit false

/-- The limits apply after the complete native operation wrapper. The raw
request codec alone does not establish a physical transport capacity bound. -/
def maxNativeRequest : Nat := 262078
def maxNativeReply : Nat := 262070

def planBytes (requestBytes headerBytes : List UInt8) : List UInt8 :=
  "DREGG.JOINT.PRIVATE.PLAN".toUTF8.toList ++ [1] ++
  (StreamCodec.product bytesStream bytesStream).encode (requestBytes,headerBytes)

/-- Derive the actual existing native signing header at the current source
prefix. Header authoring is not a signature, capability or source admission. -/
def author (config : Config) (opened : Opened config) (bytes : List UInt8) :
    Except String (List UInt8) := do
  if bytes.length + 1 > maxNativeRequest then throw "private request exceeds full native frame capacity"
  let some request := decodeRequest bytes | throw "invalid private source request"
  let some pin := config.privatePartyEndpoint | throw "private party endpoint disabled"
  let prepared ← JointBackendPartyAdmission.prepare config opened pin request
  let header ← (CredentialSignatureAdmission.signingHeader opened.authority.snapshot
    (marker pin request prepared.row prepared.packet) ⟨.object,prepared.wanted⟩).mapError
      (fun _ => "private native signing header refused")
  let reply := planBytes bytes (CredentialSignedEnvelopeController.headerCodec.encode header)
  if reply.length > maxNativeReply then throw "private signing plan exceeds full native reply capacity"
  pure reply

/-- Detached signature assembly changes only the credential. The source
semantic marker excludes its randomness and still binds the exact original
backend record/sequence/message and all selected source context. -/
def assemble (request : JointBackendPartyCodec.Request) (headerBytes signature : List UInt8) :
    Except String (List UInt8) := do
  if signature.length != 64 then throw "native signature must be 64 bytes"
  let some header := CredentialSignedEnvelopeController.headerCodec.decode headerBytes
    | throw "noncanonical private signing header"
  if CredentialSignedEnvelopeController.headerCodec.encode header != headerBytes then
    throw "noncanonical private signing header"
  let some packet := decodeCarrier request.rawCarrier | throw "invalid private carrier"
  let credential := CredentialSignatureAdmission.canonicalEnvelopeCodec.encode ⟨header,signature⟩
  let carrier := {packet with credential}.carrierBytes
  let wire := requestBytes {request with rawCarrier := carrier}
  if carrier.length > 131100 || wire.length + 1 > maxNativeRequest then
    throw "signed private request exceeds full native capacity"
  pure wire

#assert_axioms author
#assert_axioms assemble
end Minidregg.Host.JointBackendPartyWire
