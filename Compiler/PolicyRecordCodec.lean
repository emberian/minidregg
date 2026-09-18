/-
# Compiler.PolicyRecordCodec -- executable, canonical policy source

Version 2 encodes the complete `PolicyRecord`, including every `Pred`
constructor. Naturals use the shared compact base-255 stream codec; integers
use disjoint nonnegative/negative tags; strings retain their exact Unicode
scalar sequence. The AST is a typed postfix token stream. Its two stack sorts
distinguish predicates from predicate lists, so malformed trees fail rather
than acquiring an implicit meaning.

The decoder consumes all bytes and requires exact re-encoding. This last
check rejects redundant natural digits, invalid scalar aliases, and every
other noncanonical spelling accepted by a primitive stream decoder. The
universal round-trip and canonical-decoding laws below are kernel proofs.
The cSHAKE address is executable but is not claimed to be injective.
-/
import Compiler.CanonicalPolicyAdmission
import Compiler.Sp800185Cshake256
import Compiler.Tower256ConcreteBackend
import Mathlib.Data.Char

namespace Minidregg.Compiler.PolicyRecordCodec

open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Pred
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def intToWire : Int → Sum Nat Nat
  | .ofNat value => .inl value
  | .negSucc value => .inr value

def intOfWire : Sum Nat Nat → Int
  | .inl value => .ofNat value
  | .inr value => .negSucc value

def intStream : StreamCodec Int :=
  StreamCodec.xmap (StreamCodec.sum StreamCodec.nat StreamCodec.nat)
    intToWire intOfWire (by intro value; cases value <;> rfl)

def charStream : StreamCodec Char :=
  StreamCodec.xmap StreamCodec.nat Char.toNat Char.ofNat Char.ofNat_toNat

def stringStream : StreamCodec String :=
  StreamCodec.xmap (StreamCodec.list charStream) String.toList String.ofList
    (by intro value; exact String.ofList_toList)

/-- A finite first-order token vocabulary. `nil` and `cons` retain the exact
list constructor structure without recursive numeric pairing or unary codes. -/
inductive Token where
  | eq (slot : String) (value : Int)
  | le (slot : String) (value : Int)
  | memberOf (slot : String) (values : List Int)
  | writeOnce (slot : String)
  | monotone (slot : String)
  | witnessed (identifier : String)
  | not
  | all
  | any
  | nil
  | cons
  deriving DecidableEq, Repr

def slotIntStream := StreamCodec.product stringStream intStream
def slotListStream := StreamCodec.product stringStream (StreamCodec.list intStream)

def encodeToken : Token → List UInt8
  | .eq slot value => 0 :: slotIntStream.encode (slot, value)
  | .le slot value => 1 :: slotIntStream.encode (slot, value)
  | .memberOf slot values => 2 :: slotListStream.encode (slot, values)
  | .writeOnce slot => 3 :: stringStream.encode slot
  | .monotone slot => 4 :: stringStream.encode slot
  | .witnessed identifier => 5 :: stringStream.encode identifier
  | .not => [6]
  | .all => [7]
  | .any => [8]
  | .nil => [9]
  | .cons => [10]

def decodeToken : List UInt8 → Option (Token × List UInt8)
  | 0 :: bytes => do
      let ((slot, value), suffix) ← slotIntStream.decodePrefix bytes
      some (.eq slot value, suffix)
  | 1 :: bytes => do
      let ((slot, value), suffix) ← slotIntStream.decodePrefix bytes
      some (.le slot value, suffix)
  | 2 :: bytes => do
      let ((slot, values), suffix) ← slotListStream.decodePrefix bytes
      some (.memberOf slot values, suffix)
  | 3 :: bytes => do
      let (slot, suffix) ← stringStream.decodePrefix bytes
      some (.writeOnce slot, suffix)
  | 4 :: bytes => do
      let (slot, suffix) ← stringStream.decodePrefix bytes
      some (.monotone slot, suffix)
  | 5 :: bytes => do
      let (identifier, suffix) ← stringStream.decodePrefix bytes
      some (.witnessed identifier, suffix)
  | 6 :: suffix => some (.not, suffix)
  | 7 :: suffix => some (.all, suffix)
  | 8 :: suffix => some (.any, suffix)
  | 9 :: suffix => some (.nil, suffix)
  | 10 :: suffix => some (.cons, suffix)
  | _ => none

theorem decodeToken_encode (token : Token) (suffix : List UInt8) :
    decodeToken (encodeToken token ++ suffix) = some (token, suffix) := by
  cases token <;>
    simp [encodeToken, decodeToken, StreamCodec.decodePrefix_encode]

def tokenStream : StreamCodec Token where
  encode := encodeToken
  decodePrefix := decodeToken
  decodePrefix_encode := decodeToken_encode

abbrev Stack := List (Sum Pred PredList)

def step : Token → Stack → Option Stack
  | .eq slot value, stack => some (.inl (.eq slot value) :: stack)
  | .le slot value, stack => some (.inl (.le slot value) :: stack)
  | .memberOf slot values, stack => some (.inl (.memberOf slot values) :: stack)
  | .writeOnce slot, stack => some (.inl (.writeOnce slot) :: stack)
  | .monotone slot, stack => some (.inl (.monotone slot) :: stack)
  | .witnessed identifier, stack => some (.inl (.witnessed ⟨identifier⟩) :: stack)
  | .not, .inl predicate :: stack => some (.inl (.not predicate) :: stack)
  | .all, .inr predicates :: stack => some (.inl (.allL predicates) :: stack)
  | .any, .inr predicates :: stack => some (.inl (.anyL predicates) :: stack)
  | .nil, stack => some (.inr .nil :: stack)
  | .cons, .inr predicates :: .inl predicate :: stack =>
      some (.inr (.cons predicate predicates) :: stack)
  | _, _ => none

def runTokens : List Token → Stack → Option Stack
  | [], stack => some stack
  | token :: tokens, stack => do
      let next ← step token stack
      runTokens tokens next

mutual
/-- Difference-list construction keeps AST traversal linear in its node count. -/
def tokensInto : Pred → List Token → List Token
  | .eq slot value, suffix => .eq slot value :: suffix
  | .le slot value, suffix => .le slot value :: suffix
  | .memberOf slot values, suffix => .memberOf slot values :: suffix
  | .writeOnce slot, suffix => .writeOnce slot :: suffix
  | .monotone slot, suffix => .monotone slot :: suffix
  | .witnessed vk, suffix => .witnessed vk.id :: suffix
  | .not predicate, suffix => tokensInto predicate (.not :: suffix)
  | .allL predicates, suffix => listTokensInto predicates (.all :: suffix)
  | .anyL predicates, suffix => listTokensInto predicates (.any :: suffix)

def listTokensInto : PredList → List Token → List Token
  | .nil, suffix => .nil :: suffix
  | .cons predicate predicates, suffix =>
      tokensInto predicate (listTokensInto predicates (.cons :: suffix))
end

mutual
theorem runTokens_tokensInto (predicate : Pred) (suffix : List Token) (stack : Stack) :
    runTokens (tokensInto predicate suffix) stack =
      runTokens suffix (.inl predicate :: stack) := by
  cases predicate with
  | eq slot value => rfl
  | le slot value => rfl
  | memberOf slot values => rfl
  | writeOnce slot => rfl
  | monotone slot => rfl
  | witnessed vk => cases vk; rfl
  | not predicate =>
      rw [tokensInto, runTokens_tokensInto]
      rfl
  | allL predicates =>
      rw [tokensInto, runTokens_listTokensInto]
      rfl
  | anyL predicates =>
      rw [tokensInto, runTokens_listTokensInto]
      rfl

theorem runTokens_listTokensInto (predicates : PredList)
    (suffix : List Token) (stack : Stack) :
    runTokens (listTokensInto predicates suffix) stack =
      runTokens suffix (.inr predicates :: stack) := by
  cases predicates with
  | nil => rfl
  | cons predicate predicates =>
      rw [listTokensInto, runTokens_tokensInto, runTokens_listTokensInto]
      rfl
end

def encodePred (predicate : Pred) : List Token := tokensInto predicate []

def decodePred (tokens : List Token) : Option Pred := do
  let stack ← runTokens tokens []
  match stack with
  | [.inl predicate] => some predicate
  | _ => none

@[simp] theorem decodePred_encode (predicate : Pred) :
    decodePred (encodePred predicate) = some predicate := by
  simp [decodePred, encodePred, runTokens_tokensInto, runTokens]

abbrev RecordTuple := Nat × Nat × Digest × Digest × Option Digest × List Token

def recordTupleStream : StreamCodec RecordTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product (StreamCodec.option digestStream)
            (StreamCodec.list tokenStream)))))

def recordTuple (record : PolicyRecord) : RecordTuple :=
  (record.policyId.value, record.version, record.domain, record.semantics,
    record.previous, encodePred record.predicate)

def recordOfTuple (tuple : RecordTuple) : Option PolicyRecord := do
  let predicate ← decodePred tuple.2.2.2.2.2
  some
    { policyId := ⟨tuple.1⟩
      version := tuple.2.1
      domain := tuple.2.2.1
      semantics := tuple.2.2.2.1
      previous := tuple.2.2.2.2.1
      predicate := predicate }

@[simp] theorem recordOfTuple_tuple (record : PolicyRecord) :
    recordOfTuple (recordTuple record) = some record := by
  cases record
  simp [recordOfTuple, recordTuple]

def sourceVersion : Nat := 2

def wireFrame : List UInt8 := "LOOM/AUTH/POLICYRECORD".toUTF8.toList ++ [2]

def encode (record : PolicyRecord) : List UInt8 :=
  wireFrame ++ recordTupleStream.encode (recordTuple record)

def decodeRaw (bytes : List UInt8) : Option PolicyRecord :=
  if bytes.take wireFrame.length = wireFrame then do
    let tuple ← recordTupleStream.toLawful.decode (bytes.drop wireFrame.length)
    recordOfTuple tuple
  else none

@[simp] theorem decodeRaw_encode (record : PolicyRecord) :
    decodeRaw (encode record) = some record := by
  have payload := recordTupleStream.toLawful.decode_encode (recordTuple record)
  change recordTupleStream.toLawful.decode
    (recordTupleStream.encode (recordTuple record)) = some (recordTuple record) at payload
  simp [decodeRaw, encode, payload]

/-- Full consumption plus exact re-encoding admits one spelling per record. -/
def decode (bytes : List UInt8) : Option PolicyRecord := do
  let record ← decodeRaw bytes
  if encode record = bytes then some record else none

@[simp] theorem decode_encode (record : PolicyRecord) :
    decode (encode record) = some record := by
  simp [decode]

theorem decode_canonical {bytes : List UInt8} {record : PolicyRecord}
    (accepted : decode bytes = some record) : encode record = bytes := by
  unfold decode at accepted
  cases raw : decodeRaw bytes with
  | none => simp [raw] at accepted
  | some selected =>
      simp only [raw, bind, Option.bind] at accepted
      split at accepted
      next canonical =>
        cases Option.some.inj accepted
        exact canonical
      next => contradiction

theorem decode_some_iff (bytes : List UInt8) (record : PolicyRecord) :
    decode bytes = some record ↔ bytes = encode record := by
  constructor
  · intro accepted
    exact (decode_canonical accepted).symm
  · intro canonical
    rw [canonical, decode_encode]

def codec : LawfulCodec PolicyRecord where
  encode := encode
  decode := decode
  decode_encode := decode_encode

theorem encode_injective : Function.Injective encode := by
  intro left right equal
  have decoded := congrArg decode equal
  simpa using decoded

theorem rejects_noncanonical {bytes : List UInt8} {record : PolicyRecord}
    (parsed : decodeRaw bytes = some record) (different : encode record ≠ bytes) :
    decode bytes = none := by
  simp [decode, parsed, different]

theorem rejects_trailing (record : PolicyRecord) (suffix : List UInt8)
    (nonempty : suffix ≠ []) : decode (encode record ++ suffix) = none := by
  simp [decode, decodeRaw, encode, List.append_assoc,
    StreamCodec.toLawful, StreamCodec.decodePrefix_encode, nonempty]

theorem unknown_token_rejected (suffix : List UInt8) :
    decodeToken (255 :: suffix) = none := rfl

theorem wrong_stack_sort_rejected : decodePred [.nil, .not] = none := rfl

theorem stack_underflow_rejected : decodePred [.cons] = none := rfl

theorem extra_roots_rejected : decodePred [.nil, .all, .nil, .any] = none := rfl

def customization : List UInt8 := "LOOM.AUTH.POLICY.RECORD/v2".toUTF8.toList

def hashBytes (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash customization bytes).digest

def digest (record : PolicyRecord) : Digest := hashBytes (encode record)

end Minidregg.Compiler.PolicyRecordCodec

/-- info: 'Minidregg.Compiler.PolicyRecordCodec.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.decode_encode
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.decode_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.decode_canonical
