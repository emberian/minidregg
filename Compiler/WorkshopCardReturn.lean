/- Domain materialization of the ACTUAL executed Workshop Card. This is a
structural data decoder, not an evaluator or a private-release authority. The
shared source machine supplies Trace/Value; current invocation admission must
supply expected candidate/policy and independently authorized return custody. -/
import Compiler.BendSourceByteCodec
import Compiler.BendWorldPlan
import Compiler.BendCoreAdmission
import Theory.BendLiveMachine
import Theory.AssertAxioms

namespace Minidregg.Compiler.WorkshopCardReturn
open Minidregg.Theory
open Minidregg.Theory.BendTT
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend
open BendSourceRepresentation
set_option autoImplicit false

structure Candidate where
  source : List UInt8
  program : List UInt8
  revision : Nat
  deriving DecidableEq, Repr
structure Recommendation where
  candidate : Candidate
  policy : List UInt8
  ready : Bool
  deriving DecidableEq, Repr
structure Card where
  candidate : Candidate
  label : List UInt8
  review : Recommendation
  deriving DecidableEq, Repr

def pair (a b : Term) : Term := .Tup .Q1 a b
def unit : Term := .Lab "()"
def candidateTerm (c : Candidate) : Term :=
  pair (.Lab "CatalogReview.Candidate")
    (pair (bytesTerm c.source) (pair (bytesTerm c.program) (pair (natTerm c.revision) unit)))
def recommendationTerm (r : Recommendation) : Term :=
  pair (.Lab "CatalogReview.Recommendation")
    (pair (candidateTerm r.candidate) (pair (bytesTerm r.policy) (pair (boolTerm r.ready) unit)))
def cardTerm (c : Card) : Term :=
  pair (.Lab "ReusableWorkshop.Card")
    (pair (candidateTerm c.candidate) (pair (bytesTerm c.label) (pair (recommendationTerm c.review) unit)))

def decodeCandidate : Term → Option Candidate
  | .Tup .Q1 (.Lab "CatalogReview.Candidate")
      (.Tup .Q1 source (.Tup .Q1 program (.Tup .Q1 revision (.Lab "()")))) => do
        pure ⟨← decodeBytes source, ← decodeBytes program, ← decodeNat revision⟩
  | _ => none
def decodeRecommendation : Term → Option Recommendation
  | .Tup .Q1 (.Lab "CatalogReview.Recommendation")
      (.Tup .Q1 candidate (.Tup .Q1 policy (.Tup .Q1 ready (.Lab "()")))) => do
        pure ⟨← decodeCandidate candidate, ← decodeBytes policy, ← decodeBool ready⟩
  | _ => none
def decodeRaw : Term → Option Card
  | .Tup .Q1 (.Lab "ReusableWorkshop.Card")
      (.Tup .Q1 candidate (.Tup .Q1 label (.Tup .Q1 review (.Lab "()")))) => do
        pure ⟨← decodeCandidate candidate, ← decodeBytes label, ← decodeRecommendation review⟩
  | _ => none

/-- Exact reconstruction is checked at ingress. No byte truncation, ignored
fields, wrong constructor labels/quantities, annotations or dangling tails. -/
def decode (result : Term) : Option Card := do
  let card ← decodeRaw result
  if cardTerm card = result then some card else none

theorem decode_exact {result : Term} {card : Card} (h : decode result = some card) :
    cardTerm card = result := by
  unfold decode at h
  cases raw : decodeRaw result with
  | none => simp [raw] at h
  | some found =>
    simp only [raw, Option.bind_some] at h
    split at h
    · rename_i hExact
      have same := Option.some.inj h
      subst card
      exact hExact
    · cases h

theorem decode_candidate_roundtrip (c : Candidate) : decodeCandidate (candidateTerm c) = some c := by
  cases c
  simp [candidateTerm, pair, unit, decodeCandidate, decode_bytesTerm, decode_natTerm]
theorem decode_recommendation_roundtrip (r : Recommendation) :
    decodeRecommendation (recommendationTerm r) = some r := by
  cases r
  simp [recommendationTerm, pair, unit, decodeRecommendation,
    decode_candidate_roundtrip, decode_bytesTerm, decode_boolTerm]
theorem decode_roundtrip (c : Card) : decode (cardTerm c) = some c := by
  cases c
  simp [decode, decodeRaw, cardTerm, pair, unit, decode_candidate_roundtrip,
    decode_bytesTerm, decode_recommendation_roundtrip]

def candidateStream : StreamCodec Candidate :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product bytesStream StreamCodec.nat))
    (fun c => (c.source, c.program, c.revision)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (by intro c; cases c; rfl)
def recommendationStream : StreamCodec Recommendation :=
  StreamCodec.xmap (StreamCodec.product candidateStream (StreamCodec.product bytesStream StreamCodec.bool))
    (fun r => (r.candidate, r.policy, r.ready)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (by intro r; cases r; rfl)
def stream : StreamCodec Card :=
  StreamCodec.xmap (StreamCodec.product candidateStream (StreamCodec.product bytesStream recommendationStream))
    (fun c => (c.candidate, c.label, c.review)) (fun p => ⟨p.1, p.2.1, p.2.2⟩)
    (by intro c; cases c; rfl)
def frame : List UInt8 := "DREGG/WORKSHOP/CARD/v1".toUTF8.toList
def encode (card : Card) : List UInt8 := frame ++ stream.encode card
def decodePayload (bytes : List UInt8) : Option Card := NockProgramCodec.framedDecode frame stream bytes
theorem payload_roundtrip (card : Card) : decodePayload (encode card) = some card :=
  NockProgramCodec.framedDecode_encode frame stream card
theorem payload_canonical {bytes : List UInt8} {card : Card}
    (h : decodePayload bytes = some card) : encode card = bytes :=
  NockProgramCodec.framedDecode_canonical h

/-- Schema identity binds this source Card name to the WHOLE actual checked
Book, including dependent constructor definitions. It is not source publication
provenance: the world receiver additionally binds the immutable source package. -/
def schemaId (core : BendCoreAdmission.Checked) : Digest :=
  (Sp800185Cshake256.hash "DREGG.WORKSHOP.CARD-SCHEMA/v1".toUTF8.toList
    ((StreamCodec.product bytesStream PolicyRecordCodec.stringStream).encode
      (core.bytes, "ReusableWorkshop.Card"))).digest
def encodingId : Digest :=
  (Sp800185Cshake256.hash "DREGG.WORKSHOP.CARD-ENCODING/v1".toUTF8.toList frame).digest

/-- Plain parameters, NOT authority tokens. The actual native private-return
receiver must derive these from independently admitted context and release law. -/
structure Custody where
  name : String
  recipient : SubjectId
  keyEpoch : Digest
  audience : Digest
  generation : Nat

def returnSlot (core : BendCoreAdmission.Checked) (custody : Custody) (card : Card) :
    BendWorldPlan.ReturnSlot :=
  ⟨custody.name, schemaId core, encodingId, custody.recipient, custody.keyEpoch,
    custody.audience, custody.generation, encode card⟩

/-- A malformed or policy-changing override cannot be silently materialized
as the requested recommendation. The expected values require current input
admission outside this pure structural gate. A ready verdict is not adoption. -/
def matches (card : Card) (candidate : Candidate) (policy : List UInt8) : Bool :=
  decide (card.candidate = candidate ∧ card.review.candidate = candidate ∧ card.review.policy = policy)
theorem matches_exact {card : Card} {candidate : Candidate} {policy : List UInt8}
    (h : matches card candidate policy = true) :
    card.candidate = candidate ∧ card.review.candidate = candidate ∧ card.review.policy = policy := by
  simpa only [matches, decide_eq_true_eq] using h

structure Evaluated (core : BendCoreAdmission.Checked) (initial : Term) where
  result : Term
  count : Nat
  trace : BendLiveMachine.Trace core.book count initial result
  value : Value core.book result
  card : Card
  decoded : decode result = some card

def execute (core : BendCoreAdmission.Checked) (classificationTicks steps : Nat)
    (initial : Term) : Option (Evaluated core initial) :=
  match BendLiveMachine.executeChecked core.book classificationTicks steps initial with
  | .refused _ _ _ _ => none
  | .complete result count trace value =>
    match decoded : decode result with
    | none => none
    | some card => some ⟨result, count, trace, value, card, decoded⟩

/-- Exact admitted source method and exact actual argument term. Selection of
this entry from current immutable prototype/authority is the native binder's
job; this structure cannot stand in for that admission. -/
structure Invocation (core : BendCoreAdmission.Checked) (candidate : Candidate) where
  method : BendCoreAdmission.Entry core
  interfaceExact : method.definition.T =
    .All .Q2 (.Ref "CatalogReview.Candidate") (.Ref "ReusableWorkshop.Card")
def Invocation.initial {core : BendCoreAdmission.Checked} {candidate : Candidate}
    (call : Invocation core candidate) : Term :=
  .App .Q2 (.Ref call.method.name) (candidateTerm candidate)

structure Materialized (core : BendCoreAdmission.Checked) (candidate : Candidate)
    (call : Invocation core candidate) (policy : List UInt8) (custody : Custody) where
  evaluated : Evaluated core call.initial
  binding : matches evaluated.card candidate policy = true
  slot : BendWorldPlan.ReturnSlot
  exact : slot = returnSlot core custody evaluated.card

def materialize {core : BendCoreAdmission.Checked} {candidate : Candidate}
    (call : Invocation core candidate) (evaluated : Evaluated core call.initial)
    (policy : List UInt8) (custody : Custody) : Option (Materialized core candidate call policy custody) :=
  if binding : matches evaluated.card candidate policy = true then
    some ⟨evaluated, binding, returnSlot core custody evaluated.card, rfl⟩
  else none

theorem materialized_payload_exact {core : BendCoreAdmission.Checked}
    {candidate : Candidate} {call : Invocation core candidate} {policy : List UInt8} {custody : Custody}
    (m : Materialized core candidate call policy custody) :
    decodePayload m.slot.bytes = some m.evaluated.card := by
  rw [m.exact]
  exact payload_roundtrip m.evaluated.card
theorem materialized_source_exact {core : BendCoreAdmission.Checked}
    {candidate : Candidate} {call : Invocation core candidate} {policy : List UInt8} {custody : Custody}
    (m : Materialized core candidate call policy custody) :
    cardTerm m.evaluated.card = m.evaluated.result := decode_exact m.evaluated.decoded

#assert_axioms decode_exact
#assert_axioms decode_roundtrip
#assert_axioms payload_roundtrip
#assert_axioms payload_canonical
#assert_axioms matches_exact
#assert_axioms materialized_payload_exact
#assert_axioms materialized_source_exact
end Minidregg.Compiler.WorkshopCardReturn
