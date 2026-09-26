/-
Portable, public Mini native-prefix evidence. This is a transport codec, not
an admission decision. The retained image contains its genesis; the separate
pin is a claim to compare with the verifier's independently selected config.

The current profile carries a bounded original accepted prefix. Every opaque
field and the whole package are bounded before nested native decoders run.
The historical first-event frame remains separately decodable under its old
bounds and is never reinterpreted as the current profile.
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
  deriving DecidableEq, Repr

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
  framed "DREGG/FN/NATIVE-PREFIX/v2".toUTF8.toList packageStream

def historicalPackageCodec : LawfulCodec Package :=
  framed "DREGG/FN/NATIVE-PREFIX/v1".toUTF8.toList packageStream

def maxPackageBytes : Nat := 1048576
def maxCallBytes : Nat := 262144
def maxPrefixBytes : Nat := 786432
def maxSourceBytes : Nat := 1500000

/-- One v2 source renders at most 4*ceil(package/3) base64 octets plus CRLF
line breaks and bounded headers. fn's hybrid carrier adds keys, signatures and
framing; Mini's report retains that carrier and the package independently.
These are allocation ceilings for the linked native path, not Store policy. -/
def maxCarrierBytes : Nat := maxSourceBytes + 16384
def maxPortableInboxBytes : Nat := maxCarrierBytes + 4096
def maxHistoricalVerdictEventBytes : Nat := 65538
/-- Mini's portable article has at most 256 Newsgroups octets, so even without
assuming a particular separator spelling it names no more than 256 groups.
Qualified fn bbf52159 `books/records-shape.lisp` bounds the encoded article
record by payload + 1111 + 261 per group even for wide integer fields. The schema-1 `fn-e` in
`books/stx-accept-records.lisp` then carries that record, the exact authored
source, a verdict of at most 65538 octets, profile/content-subject/authored-id
of at most 64/256/256 octets, thirteen conservative CBOR heads of at most nine octets, and
the four-octet magic. This is Mini's selected portable profile ceiling, not a
claim that every fn deployment has this article limit. -/
def maxPortableGroups : Nat := 256
def maxFnArticleRecordBytes : Nat :=
  maxCarrierBytes + 1111 + 261 * maxPortableGroups
def maxFnCompositeOverheadBytes : Nat :=
  64 + 256 + 256 + 13 * 9 + 4
def maxStorePollEventBytes : Nat :=
  maxSourceBytes + maxFnArticleRecordBytes +
    maxHistoricalVerdictEventBytes + maxFnCompositeOverheadBytes
def maxStorePollInboxBytes : Nat :=
  maxStorePollEventBytes + maxHistoricalVerdictEventBytes + 4096
def maxPortableVerifyLineBytes : Nat := 2 * maxSourceBytes + 8192
def maxPollProjectionLineBytes : Nat :=
  2 * (maxStorePollEventBytes + maxHistoricalVerdictEventBytes) + 16384
def maxConsumerReportBytes : Nat :=
  maxPackageBytes + maxPortableInboxBytes + maxStorePollInboxBytes + 131072
def maxHostFrameBytes : Nat := 2 * maxConsumerReportBytes + 262144

/-- The selected qualified poll profile and every dependent allocation ceiling
are one checked arithmetic chain. A changed source/carrier bound must update
the complete chain, including the host's hex JSON frame. -/
theorem selected_poll_envelope_exact :
    maxStorePollEventBytes = 3150546 ∧
    maxStorePollInboxBytes = 3220180 ∧
    maxPollProjectionLineBytes = 6448552 ∧
    maxConsumerReportBytes = 5920308 ∧
    maxHostFrameBytes = 12102760 := by
  decide

/-- A local operator may choose tighter limits than this portable ceiling.
The fn Store must independently be configured to admit the resulting article;
the Store's article bound is never inferred from these Mini limits. -/
structure Limits where
  packageBytes : Nat := maxPackageBytes
  prefixBytes : Nat := maxPrefixBytes
  callBytes : Nat := maxCallBytes
  sourceBytes : Nat := maxSourceBytes
  deriving DecidableEq, Repr

def Limits.portable : Limits := {}

def Limits.valid (limits : Limits) : Bool :=
  1 ≤ limits.packageBytes && limits.packageBytes ≤ maxPackageBytes &&
  1 ≤ limits.prefixBytes && limits.prefixBytes ≤ maxPrefixBytes &&
  limits.prefixBytes ≤ limits.packageBytes &&
  1 ≤ limits.callBytes && limits.callBytes ≤ maxCallBytes &&
  1 ≤ limits.sourceBytes && limits.sourceBytes ≤ maxSourceBytes

def historicalMaxPackageBytes : Nat := 17408
def historicalMaxPrefixBytes : Nat := 12288
def historicalMaxCallBytes : Nat := 6144

def checkShape (limits : Limits) (package : Package) : Except String Unit := do
  unless limits.valid do throw "invalid operator evidence limits"
  unless package.signedCall.length ≤ limits.callBytes do
    throw "signed call exceeds evidence bound"
  unless package.acceptedPrefix.length ≤ limits.prefixBytes do
    throw "accepted prefix exceeds evidence bound"
  unless 1 ≤ package.originalReceipt.acceptedCount do
    throw "original receipt count must be positive"

def checkHistoricalShape (package : Package) : Except String Unit := do
  unless package.signedCall.length ≤ historicalMaxCallBytes &&
      package.acceptedPrefix.length ≤ historicalMaxPrefixBytes &&
      package.originalReceipt.acceptedCount == 1 do
    throw "historical first-event evidence exceeds its original profile"

def encodeCheckedWith (limits : Limits) (package : Package) : Except String (List UInt8) := do
  checkShape limits package
  let bytes := packageCodec.encode package
  unless bytes.length ≤ limits.packageBytes do
    throw "evidence package exceeds bound"
  pure bytes

def encodeChecked (package : Package) : Except String (List UInt8) :=
  encodeCheckedWith Limits.portable package

def decodeCheckedWith (limits : Limits) (bytes : List UInt8) : Except String Package := do
  unless limits.valid do throw "invalid operator evidence limits"
  unless bytes.length ≤ limits.packageBytes do
    throw "evidence package exceeds bound"
  match packageCodec.decode bytes with
  | some package =>
      checkShape limits package
      pure package
  | none =>
      unless bytes.length ≤ historicalMaxPackageBytes do
        throw "historical evidence package exceeds its original bound"
      let some package := historicalPackageCodec.decode bytes
        | throw "noncanonical or unsupported Mini evidence package"
      checkHistoricalShape package
      unless package.signedCall.length ≤ limits.callBytes &&
          package.acceptedPrefix.length ≤ limits.prefixBytes do
        throw "historical evidence exceeds operator limits"
      pure package

def decodeChecked (bytes : List UInt8) : Except String Package :=
  decodeCheckedWith Limits.portable bytes

@[simp] theorem package_roundtrip (value : Package) :
    packageCodec.decode (packageCodec.encode value) = some value :=
  packageCodec.decode_encode value

end Minidregg.Compiler.FnEvidenceCodec
