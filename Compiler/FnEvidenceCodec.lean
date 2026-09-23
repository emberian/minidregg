/-
Portable, public Mini native-prefix evidence. This is a transport codec, not
an admission decision. The retained image contains its genesis; the separate
pin is a claim to compare with the verifier's independently selected config.

P0 deliberately admits one accepted event. Every opaque field and the whole
package are bounded before any nested native image or signed-call decoder runs.
-/
import Compiler.NativeHostCodec

namespace Minidregg.Compiler.FnEvidenceCodec

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

structure Package where
  domain : Digest
  semantics : Digest
  genesisPin : Digest
  signedCall : List UInt8
  originalReceipt : Receipt
  acceptedPrefix : List UInt8
  deriving Repr

def packageStream : StreamCodec Package :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product bytesStream
            (StreamCodec.product receiptStream bytesStream)))))
    (fun value => (value.domain, value.semantics, value.genesisPin,
      value.signedCall, value.originalReceipt, value.acceptedPrefix))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def packageCodec : LawfulCodec Package :=
  framed "DREGG/FN/NATIVE-PREFIX/v1".toUTF8.toList packageStream

def maxPackageBytes : Nat := 20480
def maxCallBytes : Nat := 6144
def maxPrefixBytes : Nat := 12288

def checkShape (package : Package) : Except String Unit := do
  unless package.signedCall.length ≤ maxCallBytes do
    throw "signed call exceeds P0 evidence bound"
  unless package.acceptedPrefix.length ≤ maxPrefixBytes do
    throw "accepted prefix exceeds P0 evidence bound"
  unless package.originalReceipt.acceptedCount == 1 do
    throw "P0 evidence requires exactly one accepted event"

def encodeChecked (package : Package) : Except String (List UInt8) := do
  checkShape package
  let bytes := packageCodec.encode package
  unless bytes.length ≤ maxPackageBytes do
    throw "evidence package exceeds P0 bound"
  pure bytes

def decodeChecked (bytes : List UInt8) : Except String Package := do
  unless bytes.length ≤ maxPackageBytes do
    throw "evidence package exceeds P0 bound"
  let some package := packageCodec.decode bytes
    | throw "noncanonical or unsupported Mini evidence package"
  checkShape package
  pure package

@[simp] theorem package_roundtrip (value : Package) :
    packageCodec.decode (packageCodec.encode value) = some value :=
  packageCodec.decode_encode value

end Minidregg.Compiler.FnEvidenceCodec
