/-
# Compiler.PolicyRecordCodec -- executable, canonical policy source

Version 5 encodes the complete `PolicyRecord`, its component metadata and every `Pred`
constructor. Naturals use the shared compact base-255 stream codec; integers
use the one integer codec, `Compiler.IntStream.intStream` (zigzag base-255,
no tag byte); strings retain their exact Unicode
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
import Compiler.IntStream
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
  | ran (program : Nat)
  | not
  | all
  | any
  | nil
  | cons
  | eqSlots (left right : String)
  | leSlots (left right : String)
  | leSlotsOff (left right : String) (offset : Int)
  /-- Tag 16: commit–reveal of a tuple (value slots in order, blinder slot, commit slot). Tag 15
  was the single-value `hashEq` of K-HASHEQ; it is retired and refuses to decode, so a record
  carrying it is refused rather than read as a tuple. -/
  | hashEq (values : List String) (blinder commit : String)
  deriving DecidableEq, Repr

def slotIntStream := StreamCodec.product stringStream IntStream.intStream
def slotListStream := StreamCodec.product stringStream (StreamCodec.list IntStream.intStream)
def slotPairStream := StreamCodec.product stringStream stringStream
def slotPairIntStream := StreamCodec.product slotPairStream IntStream.intStream
def slotsPairStream :=
  StreamCodec.product (StreamCodec.list stringStream) (StreamCodec.product stringStream stringStream)

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
  | .eqSlots left right => 11 :: slotPairStream.encode (left, right)
  | .leSlots left right => 12 :: slotPairStream.encode (left, right)
  | .leSlotsOff left right offset => 13 :: slotPairIntStream.encode ((left, right), offset)
  | .hashEq values blinder commit => 16 :: slotsPairStream.encode (values, (blinder, commit))
  | .ran program => 14 :: StreamCodec.nat.encode program

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
  | 11 :: bytes => do
      let ((left, right), suffix) ← slotPairStream.decodePrefix bytes
      some (.eqSlots left right, suffix)
  | 12 :: bytes => do
      let ((left, right), suffix) ← slotPairStream.decodePrefix bytes
      some (.leSlots left right, suffix)
  | 13 :: bytes => do
      let (((left, right), offset), suffix) ← slotPairIntStream.decodePrefix bytes
      some (.leSlotsOff left right offset, suffix)
  | 16 :: bytes => do
      let ((values, (blinder, commit)), suffix) ← slotsPairStream.decodePrefix bytes
      some (.hashEq values blinder commit, suffix)
  | 14 :: bytes => do
      let (program, suffix) ← StreamCodec.nat.decodePrefix bytes
      some (.ran program, suffix)
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
  | .eqSlots left right, stack => some (.inl (.eqSlots left right) :: stack)
  | .leSlots left right, stack => some (.inl (.leSlots left right) :: stack)
  | .leSlotsOff left right offset, stack => some (.inl (.leSlotsOff left right offset) :: stack)
  | .hashEq values blinder commit, stack => some (.inl (.hashEq values blinder commit) :: stack)
  | .ran program, stack => some (.inl (.ran program) :: stack)
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
  | .eqSlots left right, suffix => .eqSlots left right :: suffix
  | .leSlots left right, suffix => .leSlots left right :: suffix
  | .leSlotsOff left right offset, suffix => .leSlotsOff left right offset :: suffix
  | .witnessed vk, suffix => .witnessed vk.id :: suffix
  | .hashEq values blinder commit, suffix => .hashEq values blinder commit :: suffix
  | .ran program, suffix => .ran program :: suffix
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
  | eqSlots left right => rfl
  | leSlots left right => rfl
  | leSlotsOff left right offset => rfl
  | witnessed vk => cases vk; rfl
  | hashEq values blinder commit => rfl
  | ran program => rfl
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

/-! Component metadata is first-order source, using the existing Pred token
stream and stream-codec combinators. Lists retain authored order in source;
resolved graph order is canonical and confers no method precedence. -/

abbrev SelectorTuple := Option (List Nat) × Option (List Nat) × Option (List Nat)
abbrev RefTuple := Nat × Nat × Option (Nat × Digest)
abbrev ComponentTuple := SelectorTuple × List Token × List RefTuple

def selectorTupleStream : StreamCodec SelectorTuple :=
  StreamCodec.product (StreamCodec.option (StreamCodec.list StreamCodec.nat))
    (StreamCodec.product (StreamCodec.option (StreamCodec.list StreamCodec.nat))
      (StreamCodec.option (StreamCodec.list StreamCodec.nat)))

def refTupleStream : StreamCodec RefTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.option (StreamCodec.product StreamCodec.nat digestStream)))

def componentTupleStream : StreamCodec ComponentTuple :=
  StreamCodec.product selectorTupleStream
    (StreamCodec.product (StreamCodec.list tokenStream) (StreamCodec.list refTupleStream))

def selectorTuple (selector : Minidregg.Theory.LawComposition.Selector) : SelectorTuple :=
  (selector.physicalKinds, selector.requestKinds, selector.verbs)

def selectorOfTuple (tuple : SelectorTuple) : Minidregg.Theory.LawComposition.Selector :=
  ⟨tuple.1, tuple.2.1, tuple.2.2⟩

@[simp] theorem selectorOfTuple_tuple (selector : Minidregg.Theory.LawComposition.Selector) :
    selectorOfTuple (selectorTuple selector) = selector := by cases selector; rfl

def refTuple (reference : Minidregg.Theory.LawComposition.PolicyRef) : RefTuple :=
  (reference.policyId.value, reference.facet.tag,
    match reference.selection with
    | .head => none
    | .pinned revision digest => some (revision, digest))

def refOfTuple (tuple : RefTuple) : Option Minidregg.Theory.LawComposition.PolicyRef := do
  let facet ← match tuple.2.1 with
    | 0 => some Minidregg.Theory.LawComposition.Facet.local
    | 1 => some Minidregg.Theory.LawComposition.Facet.descendants
    | _ => none
  let selection := match tuple.2.2 with
    | none => Minidregg.Theory.LawComposition.Selection.head
    | some (revision, digest) => .pinned revision digest
  some ⟨⟨tuple.1⟩, facet, selection⟩

@[simp] theorem refOfTuple_tuple (reference : Minidregg.Theory.LawComposition.PolicyRef) :
    refOfTuple (refTuple reference) = some reference := by
  rcases reference with ⟨⟨policy⟩, facet, selection⟩
  cases facet <;> cases selection <;> rfl

def refsOfTuples : List RefTuple → Option (List Minidregg.Theory.LawComposition.PolicyRef)
  | [] => some []
  | first :: rest => do
      let first ← refOfTuple first
      let rest ← refsOfTuples rest
      some (first :: rest)

@[simp] theorem refsOfTuples_tuples (references : List Minidregg.Theory.LawComposition.PolicyRef) :
    refsOfTuples (references.map refTuple) = some references := by
  induction references with
  | nil => rfl
  | cons first rest ih => simp [refsOfTuples, ih]

def componentTuple (component : Minidregg.Theory.LawComposition.Component) : ComponentTuple :=
  (selectorTuple component.selector, encodePred component.predicate, component.parents.map refTuple)

def componentOfTuple (tuple : ComponentTuple) : Option Minidregg.Theory.LawComposition.Component := do
  let predicate ← decodePred tuple.2.1
  let parents ← refsOfTuples tuple.2.2
  some ⟨selectorOfTuple tuple.1, predicate, parents⟩

@[simp] theorem componentOfTuple_tuple (component : Minidregg.Theory.LawComposition.Component) :
    componentOfTuple (componentTuple component) = some component := by
  cases component
  simp [componentOfTuple, componentTuple]

def exportOfTuple : Option ComponentTuple → Option (Option Minidregg.Theory.LawComposition.Component)
  | none => some none
  | some tuple => do
      let component ← componentOfTuple tuple
      some (some component)

@[simp] theorem exportOfTuple_tuple (component : Option Minidregg.Theory.LawComposition.Component) :
    exportOfTuple (component.map componentTuple) = some component := by
  cases component <;> simp [exportOfTuple]

abbrev RecordTuple := Nat × Nat × Digest × Digest × Option Digest × List Token ×
  SelectorTuple × List RefTuple × Option ComponentTuple

def recordTupleStream : StreamCodec RecordTuple :=
  StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream
        (StreamCodec.product digestStream
          (StreamCodec.product (StreamCodec.option digestStream)
            (StreamCodec.product (StreamCodec.list tokenStream)
              (StreamCodec.product selectorTupleStream
                (StreamCodec.product (StreamCodec.list refTupleStream)
                  (StreamCodec.option componentTupleStream))))))))

def recordTuple (record : PolicyRecord) : RecordTuple :=
  (record.policyId.value, record.version, record.domain, record.semantics,
    record.previous, encodePred record.predicate, selectorTuple record.localSelector,
    record.parents.map refTuple, record.descendants.map componentTuple)

def recordOfTuple (tuple : RecordTuple) : Option PolicyRecord := do
  let (policyId, version, domain, semantics, previous, tokens, selector, refs, exported) := tuple
  let predicate ← decodePred tokens
  let parents ← refsOfTuples refs
  let descendants ← exportOfTuple exported
  some
    { policyId := ⟨policyId⟩
      version := version
      domain := domain
      semantics := semantics
      previous := previous
      predicate := predicate
      localSelector := selectorOfTuple selector
      parents := parents
      descendants := descendants }

@[simp] theorem recordOfTuple_tuple (record : PolicyRecord) :
    recordOfTuple (recordTuple record) = some record := by
  cases record
  simp [recordOfTuple, recordTuple]

def sourceVersion : Nat := 5

def framePrefix : List UInt8 := "LOOM/AUTH/POLICYRECORD".toUTF8.toList

def wireFrame : List UInt8 := framePrefix ++ [5]

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

/-- `hashEq` is tag 16 with a (list of strings, string, string) payload. -/
theorem hashEq_tag (values : List String) (blinder commit : String) :
    (encodeToken (.hashEq values blinder commit)).head? = some 16 := rfl

theorem hashEq_token_round_trip (values : List String) (blinder commit : String)
    (suffix : List UInt8) :
    decodeToken (encodeToken (.hashEq values blinder commit) ++ suffix) =
      some (.hashEq values blinder commit, suffix) :=
  decodeToken_encode _ _

/-- Tags 11-13 are eqSlots/leSlots/leSlotsOff, 14 is `ran`, 16 is the tuple `hashEq`; 15 (the
retired single-value `hashEq`) and 17 refuse. -/
theorem unassigned_tags_rejected (suffix : List UInt8) :
    decodeToken (15 :: suffix) = none ∧ decodeToken (17 :: suffix) = none := ⟨rfl, rfl⟩

theorem wrong_stack_sort_rejected : decodePred [.nil, .not] = none := rfl

theorem stack_underflow_rejected : decodePred [.cons] = none := rfl

theorem extra_roots_rejected : decodePred [.nil, .all, .nil, .any] = none := rfl

/-- Version 2 records (the tagged `Sum` integer spelling) refuse to decode:
their frame byte is 2. -/
theorem v2_frame_refused (rest : List UInt8) :
    decode ((framePrefix ++ [2]) ++ rest) = none := by
  have taken : ((framePrefix ++ [2]) ++ rest).take wireFrame.length = framePrefix ++ [2] := by
    rw [wireFrame, List.append_assoc, List.length_append, List.take_length_add_append]
    rfl
  have differs : framePrefix ++ [2] ≠ wireFrame := by
    intro same
    have := List.append_cancel_left same
    simp at this
  have raw : decodeRaw ((framePrefix ++ [2]) ++ rest) = none := by
    unfold decodeRaw
    rw [if_neg (by rw [taken]; exact differs)]
  unfold decode
  rw [raw]
  rfl

/-- Version 3 records (the vocabulary without the slot-to-slot atoms) refuse to decode:
their frame byte is 3. -/
theorem v3_frame_refused (rest : List UInt8) :
    decode ((framePrefix ++ [3]) ++ rest) = none := by
  have taken : ((framePrefix ++ [3]) ++ rest).take wireFrame.length = framePrefix ++ [3] := by
    rw [wireFrame, List.append_assoc, List.length_append, List.take_length_add_append]
    rfl
  have differs : framePrefix ++ [3] ≠ wireFrame := by
    intro same
    have := List.append_cancel_left same
    simp at this
  have raw : decodeRaw ((framePrefix ++ [3]) ++ rest) = none := by
    unfold decodeRaw
    rw [if_neg (by rw [taken]; exact differs)]
  unfold decode
  rw [raw]
  rfl

/-- Version 4 records (the single-predicate source without law components) refuse to decode:
their frame byte is 4. -/
theorem v4_frame_refused (rest : List UInt8) :
    decode ((framePrefix ++ [4]) ++ rest) = none := by
  have taken : ((framePrefix ++ [4]) ++ rest).take wireFrame.length = framePrefix ++ [4] := by
    rw [wireFrame, List.append_assoc, List.length_append, List.take_length_add_append]
    rfl
  have differs : framePrefix ++ [4] ≠ wireFrame := by
    intro same
    have := List.append_cancel_left same
    simp at this
  have raw : decodeRaw ((framePrefix ++ [4]) ++ rest) = none := by
    unfold decodeRaw
    rw [if_neg (by rw [taken]; exact differs)]
  unfold decode
  rw [raw]
  rfl

/-- Conversely every version-5 encoding carries frame byte 5, so a version-3 decoder, whose first
check is `take wireFrame.length = framePrefix ++ [3]`, refuses every version-5 record — including
one whose predicate uses a slot-to-slot atom — before reading a token. -/
theorem encode_not_v3_frame (record : PolicyRecord) :
    (encode record).take (framePrefix ++ [3]).length ≠ framePrefix ++ [3] := by
  have hlen : (framePrefix ++ [3]).length = wireFrame.length := by simp [wireFrame]
  rw [hlen, encode, List.take_left]
  intro same
  have := List.append_cancel_left same
  simp at this

/-- The slot-to-slot atoms round-trip through the canonical record bytes, at every slot pair. -/
theorem eqSlots_record_round_trip (record : PolicyRecord) (left right : String)
    (h : record.predicate = .eqSlots left right) :
    decode (encode record) = some record ∧
      encodePred record.predicate = [.eqSlots left right] := by
  exact ⟨decode_encode record, by rw [h]; rfl⟩

theorem leSlots_record_round_trip (record : PolicyRecord) (left right : String)
    (h : record.predicate = .leSlots left right) :
    decode (encode record) = some record ∧
      encodePred record.predicate = [.leSlots left right] := by
  exact ⟨decode_encode record, by rw [h]; rfl⟩

/-- The two new tags are the bytes 11 and 12, distinct from every version-3 tag (0..10). -/
theorem slot_pair_tags (left right : String) :
    (encodeToken (.eqSlots left right)).head? = some 11 ∧
      (encodeToken (.leSlots left right)).head? = some 12 := ⟨rfl, rfl⟩

/-- The offset order atom round-trips through the canonical record bytes, at every slot pair and
every offset (negative included). -/
theorem leSlotsOff_record_round_trip (record : PolicyRecord) (left right : String) (offset : Int)
    (h : record.predicate = .leSlotsOff left right offset) :
    decode (encode record) = some record ∧
      encodePred record.predicate = [.leSlotsOff left right offset] := by
  exact ⟨decode_encode record, by rw [h]; rfl⟩

/-- `leSlotsOff` is tag 13, added to version 4 without a frame bump: v4 is not yet emitted
anywhere outside the lane that introduced it, and every tag below 13 keeps its meaning. -/
theorem leSlotsOff_tag (left right : String) (offset : Int) :
    (encodeToken (.leSlotsOff left right offset)).head? = some 13 := rfl

/-- The vocabulary is exactly tags 0..14 and 16: tag 15 (retired) and every byte of 17 or more
refuse to decode, so a record from any other vocabulary is refused rather than read. -/
theorem decodeToken_unknown_tag (tag : UInt8) (htag : 17 ≤ tag.toNat ∨ tag.toNat = 15)
    (rest : List UInt8) :
    decodeToken (tag :: rest) = none := by
  unfold decodeToken
  split <;> first
    | rfl
    | (rename_i heq; simp only [List.cons.injEq] at heq; obtain ⟨rfl, -⟩ := heq
       simp at htag)

def customization : List UInt8 := "LOOM.AUTH.POLICY.RECORD/v5".toUTF8.toList

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
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.v2_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.v2_frame_refused
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.v3_frame_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.v3_frame_refused
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.encode_not_v3_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.encode_not_v3_frame
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.eqSlots_record_round_trip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.eqSlots_record_round_trip
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.leSlots_record_round_trip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.leSlots_record_round_trip
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.leSlotsOff_record_round_trip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.leSlotsOff_record_round_trip
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.decodeToken_unknown_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.decodeToken_unknown_tag
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.hashEq_tag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.hashEq_tag
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.hashEq_token_round_trip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.hashEq_token_round_trip
/-- info: 'Minidregg.Compiler.PolicyRecordCodec.unassigned_tags_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Compiler.PolicyRecordCodec.unassigned_tags_rejected
