/-
# Compiler.CredentialSigningKeyCodec — the shared key-record codec

Extracted unchanged from CredentialSignedEnvelopeController. Both its signed
registry projection and the actual authority entry codec consume this one
stream; there is no independently encoded host key directory.
-/
import Compiler.Tower256ConcreteBackend
import Theory.CredentialSigningKey

namespace Minidregg.Compiler.CredentialSigningKeyCodec

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

abbrev KeyRecordTuple := Nat × Nat × Nat × Nat × List UInt8 × Nat × Nat × Bool

def keyRecordTupleStream : StreamCodec KeyRecordTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product bytesStream
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat StreamCodec.bool))))))

def toTuple (key : KeyRecord) : KeyRecordTuple :=
  (key.keyId, key.keyEpoch, key.algorithm, key.subject, key.publicKey,
    key.activeFrom, key.activeUntil, key.revoked)

def ofTuple : KeyRecordTuple → KeyRecord
  | (keyId, keyEpoch, algorithm, subject, publicKey, activeFrom, activeUntil, revoked) =>
      { keyId, keyEpoch, algorithm, subject, publicKey, activeFrom, activeUntil, revoked }

@[simp] theorem ofTuple_toTuple (key : KeyRecord) : ofTuple (toTuple key) = key := by
  cases key
  rfl

def keyRecordStream : StreamCodec KeyRecord :=
  StreamCodec.xmap keyRecordTupleStream toTuple ofTuple ofTuple_toTuple

def codec : LawfulCodec KeyRecord := keyRecordStream.toLawful

@[simp] theorem decode_encode (key : KeyRecord) :
    codec.decode (codec.encode key) = some key := codec.decode_encode key

end Minidregg.Compiler.CredentialSigningKeyCodec
