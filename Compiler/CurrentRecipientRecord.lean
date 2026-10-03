/- Member-authored recipient record. Parsing yields claims, never current key
or recipient authority. Suite1 is existing Ed25519/X25519 room wrapping. -/
import Compiler.PrivateSuccessorCustodyCodec
import Theory.AssertAxioms
namespace Minidregg.Compiler.CurrentRecipientRecord
open Minidregg.Theory.TypedAuthorization
set_option autoImplicit false
structure Claim where
  member : SubjectId
  epoch : Nat
  encryptionKey : List UInt8
  room : Nat
  keysCell : Nat
  signingKey : List UInt8
  signature : List UInt8
  deriving DecidableEq

def bigEndian (width n : Nat) : List UInt8 :=
  (List.range width).map (fun i => UInt8.ofNat (n / (256 ^ (width - 1 - i))))
def readBigEndian (bytes : List UInt8) : Nat :=
  bytes.foldl (fun n b => n * 256 + b.toNat) 0

def bounded (c : Claim) : Prop := c.member.value < 2^64 ∧ c.epoch < 2^32 ∧
  c.room < 2^64 ∧ c.keysCell < 2^64 ∧ c.encryptionKey.length = 32 ∧
  c.signingKey.length = 32 ∧ c.signature.length = 64
instance (c : Claim) : Decidable (bounded c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def payload (c : Claim) : List UInt8 := bigEndian 4 c.epoch ++ c.encryptionKey ++
  bigEndian 8 c.room ++ bigEndian 8 c.keysCell ++ c.signingKey ++ c.signature
def statement (c : Claim) : List UInt8 :=
  "DREGG/PRIVATE-ENC-KEY/v2".toUTF8.toList ++ [1] ++
  bigEndian 8 c.room ++ bigEndian 8 c.keysCell ++ bigEndian 8 c.member.value ++
  bigEndian 4 c.epoch ++ c.signingKey ++ c.encryptionKey

def decode (member : SubjectId) (bytes : List UInt8) : Option Claim := do
  if bytes.length != 148 then none else
  let claim : Claim := ⟨member,readBigEndian (bytes.take 4),
    (bytes.drop 4).take 32,readBigEndian ((bytes.drop 36).take 8),
    readBigEndian ((bytes.drop 44).take 8),(bytes.drop 52).take 32,bytes.drop 84⟩
  if bounded claim ∧ payload claim = bytes then some claim else none

/-- Exact statement includes every external scope and both key bindings;
credential randomness is excluded from the bytes verified by Ed25519. -/
theorem statement_exact (c : Claim) : statement c =
  "DREGG/PRIVATE-ENC-KEY/v2".toUTF8.toList ++ [1] ++
  bigEndian 8 c.room ++ bigEndian 8 c.keysCell ++ bigEndian 8 c.member.value ++
  bigEndian 4 c.epoch ++ c.signingKey ++ c.encryptionKey := rfl
#assert_axioms statement_exact
end Minidregg.Compiler.CurrentRecipientRecord
