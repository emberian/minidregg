/-
# Kernel.Contracts.Identities — the shared identity contract

SHARED-CONTRACTS-20261003 §"Objects and identities", stated as source types with
fixed canonical bytes. This module is ADDITIVE: no existing per-domain type is
changed. `Kernel.Contracts.Refinements` proves which existing Mini identities
inject into these types; the per-domain collapse is the wave-2 follow-up.

Why `Kernel/` and not `Theory/`: `scripts/check-import-boundary.sh` bars
`Theory` from importing `Compiler`, and the tree's only lawful canonical-byte
machinery (`StreamCodec`, the strict `framed` decoder) is in `Compiler`.

* `WorldSource` — which world a coordinate belongs to: deployment domain,
  semantics digest and genesis seed digest (the three fields of
  `ReceiptContinuity.Identity`).
* `ObjectRef` — native identity + governing domain + declared semantic kind.
* `RevisionRef` — an exact world coordinate: source, height, world root. There
  is no name field, so "latest by name" is not expressible.
* `InvocationId` — ONE semantic request: source, transaction id, event id (the
  pair the native Host's `historicalReceipt` looks a request up by).
* `AttemptId`, `GenerationId`, `TransportNonce` — the DISTINCT related
  identities (SHARED-CONTRACTS separation 11). A retry is a new `AttemptId` of
  the same `InvocationId`; charging is keyed by `InvocationId`
  (`same_invocation_charges_once`), and secret-correlation consumption is keyed
  by `GenerationId`, which an attempt does not enter (`rowFor_retry`).
* `ArtifactRef` — exact digest/length/format + origin revision + custody
  obligations. A content address confers no read right
  (`content_address_does_not_confer_read`).
* `AcceptanceRef` — "invocation I was accepted, producing revision R": the
  shape of the native `Receipt`.

Canonical bytes, fixed here (every frame is `DREGG/CONTRACT/<KIND>/v1`):
`OBJECT-REF`, `REVISION-REF`, `INVOCATION`, `ATTEMPT`, `GENERATION`,
`TRANSPORT-NONCE`, `ARTIFACT-REF`, `ACCEPTANCE-REF`. Bodies are the
`Tower256ConcreteBackend.StreamCodec` field sequences in declaration order;
decoding is strict (`NockProgramCodec.framed` accepts only its own
re-encoding), and the first 17 frame bytes already separate every kind, so no
identity's bytes decode as another's (`invocation_family_frames_separate`).
-/
import Compiler.NockProgramCodec
import Theory.AssertAxioms

namespace Minidregg.Kernel.Contracts

open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.NockProgramCodec (framed framedDecode)

set_option autoImplicit false

/-! ## Types -/

structure WorldSource where
  domain : Digest
  semantics : Digest
  seed : Digest
  deriving DecidableEq, Repr

structure ObjectRef where
  /-- The native identity inside its domain (a cell id digest for Mini cells). -/
  native : Digest
  /-- The domain whose law governs the object. -/
  domain : Digest
  /-- The declared semantic kind (schema/kind digest), never inferred from bytes. -/
  kind : Digest
  deriving DecidableEq, Repr

structure RevisionRef where
  source : WorldSource
  /-- Accepted records through this revision (the native `acceptedCount`). -/
  height : Nat
  worldRoot : Digest
  deriving DecidableEq, Repr

structure InvocationId where
  source : WorldSource
  transaction : Digest
  event : Digest
  deriving DecidableEq, Repr

/-- One physical try at delivering an invocation (`retry-000N` in a retained
attempt directory). -/
structure AttemptId where
  invocation : InvocationId
  ordinal : Nat
  deriving DecidableEq, Repr

/-- The secret-correlation row an invocation consumes at one share generation. -/
structure GenerationId where
  invocation : InvocationId
  generation : Nat
  deriving DecidableEq, Repr

/-- The outer, per-packet nonce of one attempt. -/
structure TransportNonce where
  attempt : AttemptId
  nonce : List UInt8
  deriving DecidableEq, Repr

/-- Custody obligations an artifact carries. A read or execute right is an
explicit audience, never implied by holding the content address. -/
inductive Custody where
  | retainThrough (height : Nat)
  | readAudience (policyRoot : Digest)
  | executeAudience (policyRoot : Digest)
  | legalForgetting (rule : Digest)
  deriving DecidableEq, Repr

structure ArtifactRef where
  digest : Digest
  length : Nat
  format : Digest
  origin : RevisionRef
  custody : List Custody
  deriving DecidableEq, Repr

structure AcceptanceRef where
  invocation : InvocationId
  revision : RevisionRef
  deriving DecidableEq, Repr

/-! ## Stream bodies -/

def worldSourceStream : StreamCodec WorldSource :=
  StreamCodec.xmap (StreamCodec.product digestStream (StreamCodec.product digestStream digestStream))
    (fun v => (v.domain, v.semantics, v.seed)) (fun w => ⟨w.1, w.2.1, w.2.2⟩)
    (by intro v; cases v; rfl)

def objectRefStream : StreamCodec ObjectRef :=
  StreamCodec.xmap (StreamCodec.product digestStream (StreamCodec.product digestStream digestStream))
    (fun v => (v.native, v.domain, v.kind)) (fun w => ⟨w.1, w.2.1, w.2.2⟩)
    (by intro v; cases v; rfl)

def revisionRefStream : StreamCodec RevisionRef :=
  StreamCodec.xmap (StreamCodec.product worldSourceStream
      (StreamCodec.product StreamCodec.nat digestStream))
    (fun v => (v.source, v.height, v.worldRoot)) (fun w => ⟨w.1, w.2.1, w.2.2⟩)
    (by intro v; cases v; rfl)

def invocationIdStream : StreamCodec InvocationId :=
  StreamCodec.xmap (StreamCodec.product worldSourceStream
      (StreamCodec.product digestStream digestStream))
    (fun v => (v.source, v.transaction, v.event)) (fun w => ⟨w.1, w.2.1, w.2.2⟩)
    (by intro v; cases v; rfl)

def attemptIdStream : StreamCodec AttemptId :=
  StreamCodec.xmap (StreamCodec.product invocationIdStream StreamCodec.nat)
    (fun v => (v.invocation, v.ordinal)) (fun w => ⟨w.1, w.2⟩)
    (by intro v; cases v; rfl)

def generationIdStream : StreamCodec GenerationId :=
  StreamCodec.xmap (StreamCodec.product invocationIdStream StreamCodec.nat)
    (fun v => (v.invocation, v.generation)) (fun w => ⟨w.1, w.2⟩)
    (by intro v; cases v; rfl)

def transportNonceStream : StreamCodec TransportNonce :=
  StreamCodec.xmap (StreamCodec.product attemptIdStream bytesStream)
    (fun v => (v.attempt, v.nonce)) (fun w => ⟨w.1, w.2⟩)
    (by intro v; cases v; rfl)

def custodyStream : StreamCodec Custody :=
  StreamCodec.xmap
    (StreamCodec.sum StreamCodec.nat
      (StreamCodec.sum digestStream (StreamCodec.sum digestStream digestStream)))
    (fun v => match v with
      | .retainThrough h => .inl h
      | .readAudience r => .inr (.inl r)
      | .executeAudience r => .inr (.inr (.inl r))
      | .legalForgetting r => .inr (.inr (.inr r)))
    (fun w => match w with
      | .inl h => .retainThrough h
      | .inr (.inl r) => .readAudience r
      | .inr (.inr (.inl r)) => .executeAudience r
      | .inr (.inr (.inr r)) => .legalForgetting r)
    (by intro v; cases v <;> rfl)

def artifactRefStream : StreamCodec ArtifactRef :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product digestStream (StreamCodec.product revisionRefStream
        (StreamCodec.list custodyStream)))))
    (fun v => (v.digest, v.length, v.format, v.origin, v.custody))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2⟩)
    (by intro v; cases v; rfl)

def acceptanceRefStream : StreamCodec AcceptanceRef :=
  StreamCodec.xmap (StreamCodec.product invocationIdStream revisionRefStream)
    (fun v => (v.invocation, v.revision)) (fun w => ⟨w.1, w.2⟩)
    (by intro v; cases v; rfl)

/-! ## Frames (literal bytes, each spelled by a theorem) -/

/-- `DREGG/CONTRACT/OBJECT-REF/v1` -/
def objectRefFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 67, 79, 78, 84, 82, 65, 67, 84, 47, 79, 66, 74, 69, 67, 84, 45, 82, 69, 70, 47, 118, 49]
/-- `DREGG/CONTRACT/REVISION-REF/v1` -/
def revisionRefFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 67, 79, 78, 84, 82, 65, 67, 84, 47, 82, 69, 86, 73, 83, 73, 79, 78, 45, 82, 69, 70, 47, 118, 49]
/-- `DREGG/CONTRACT/INVOCATION/v1` -/
def invocationFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 67, 79, 78, 84, 82, 65, 67, 84, 47, 73, 78, 86, 79, 67, 65, 84, 73, 79, 78, 47, 118, 49]
/-- `DREGG/CONTRACT/ATTEMPT/v1` -/
def attemptFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 67, 79, 78, 84, 82, 65, 67, 84, 47, 65, 84, 84, 69, 77, 80, 84, 47, 118, 49]
/-- `DREGG/CONTRACT/GENERATION/v1` -/
def generationFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 67, 79, 78, 84, 82, 65, 67, 84, 47, 71, 69, 78, 69, 82, 65, 84, 73, 79, 78, 47, 118, 49]
/-- `DREGG/CONTRACT/TRANSPORT-NONCE/v1` -/
def transportNonceFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 67, 79, 78, 84, 82, 65, 67, 84, 47, 84, 82, 65, 78, 83, 80, 79, 82, 84, 45, 78, 79, 78, 67, 69, 47, 118, 49]
/-- `DREGG/CONTRACT/ARTIFACT-REF/v1` -/
def artifactRefFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 67, 79, 78, 84, 82, 65, 67, 84, 47, 65, 82, 84, 73, 70, 65, 67, 84, 45, 82, 69, 70, 47, 118, 49]
/-- `DREGG/CONTRACT/ACCEPTANCE-REF/v1` -/
def acceptanceRefFrame : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 67, 79, 78, 84, 82, 65, 67, 84, 47, 65, 67, 67, 69, 80, 84, 65, 78, 67, 69, 45, 82, 69, 70, 47, 118, 49]

theorem frames_spell :
    objectRefFrame = "DREGG/CONTRACT/OBJECT-REF/v1".toUTF8.toList ∧
    revisionRefFrame = "DREGG/CONTRACT/REVISION-REF/v1".toUTF8.toList ∧
    invocationFrame = "DREGG/CONTRACT/INVOCATION/v1".toUTF8.toList ∧
    attemptFrame = "DREGG/CONTRACT/ATTEMPT/v1".toUTF8.toList ∧
    generationFrame = "DREGG/CONTRACT/GENERATION/v1".toUTF8.toList ∧
    transportNonceFrame = "DREGG/CONTRACT/TRANSPORT-NONCE/v1".toUTF8.toList ∧
    artifactRefFrame = "DREGG/CONTRACT/ARTIFACT-REF/v1".toUTF8.toList ∧
    acceptanceRefFrame = "DREGG/CONTRACT/ACCEPTANCE-REF/v1".toUTF8.toList := by
  decide +kernel

/-! ## Codecs -/

def objectRefCodec : LawfulCodec ObjectRef := framed objectRefFrame objectRefStream
def revisionRefCodec : LawfulCodec RevisionRef := framed revisionRefFrame revisionRefStream
def invocationIdCodec : LawfulCodec InvocationId := framed invocationFrame invocationIdStream
def attemptIdCodec : LawfulCodec AttemptId := framed attemptFrame attemptIdStream
def generationIdCodec : LawfulCodec GenerationId := framed generationFrame generationIdStream
def transportNonceCodec : LawfulCodec TransportNonce :=
  framed transportNonceFrame transportNonceStream
def artifactRefCodec : LawfulCodec ArtifactRef := framed artifactRefFrame artifactRefStream
def acceptanceRefCodec : LawfulCodec AcceptanceRef :=
  framed acceptanceRefFrame acceptanceRefStream

/-- A framed codec's encoding is injective (decode is a left inverse). -/
theorem framed_encode_injective {α : Type} (frame : List UInt8) (stream : StreamCodec α) :
    Function.Injective (framed frame stream).encode := by
  intro a b same
  have ha := (framed frame stream).decode_encode a
  rw [same, (framed frame stream).decode_encode b] at ha
  exact (Option.some.inj ha).symm

/-- A byte string that differs from `frame` within its first `k` bytes never
decodes under `frame`, whatever follows. -/
theorem framedDecode_refuses_other_frame {α : Type} (frame old : List UInt8)
    (stream : StreamCodec α) (rest : List UInt8) (k : Nat) (hOld : k ≤ old.length)
    (hFrame : k ≤ frame.length) (differ : old.take k ≠ frame.take k) :
    framedDecode frame stream (old ++ rest) = none := by
  have hne : ¬ ((old ++ rest).take frame.length = frame) := by
    intro same
    apply differ
    have h := congrArg (List.take k) same
    rw [List.take_take, Nat.min_eq_left hFrame, List.take_append_of_le_length hOld] at h
    exact h
  unfold framedDecode
  rw [if_neg hne]

/-- Separation 11 on the wire: the bytes of an attempt, a generation row or a
transport nonce never decode as a semantic invocation, and an invocation's
bytes never decode as any of them. -/
theorem invocation_family_frames_separate (a : AttemptId) (g : GenerationId)
    (n : TransportNonce) (i : InvocationId) :
    invocationIdCodec.decode (attemptIdCodec.encode a) = none ∧
    invocationIdCodec.decode (generationIdCodec.encode g) = none ∧
    invocationIdCodec.decode (transportNonceCodec.encode n) = none ∧
    attemptIdCodec.decode (invocationIdCodec.encode i) = none ∧
    generationIdCodec.decode (invocationIdCodec.encode i) = none ∧
    transportNonceCodec.decode (invocationIdCodec.encode i) = none ∧
    attemptIdCodec.decode (transportNonceCodec.encode n) = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show framedDecode invocationFrame invocationIdStream (attemptFrame ++ attemptIdStream.encode a) = none
    exact framedDecode_refuses_other_frame invocationFrame attemptFrame invocationIdStream _ 17 (by decide) (by decide) (by decide)
  · show framedDecode invocationFrame invocationIdStream (generationFrame ++ generationIdStream.encode g) = none
    exact framedDecode_refuses_other_frame invocationFrame generationFrame invocationIdStream _ 17 (by decide) (by decide) (by decide)
  · show framedDecode invocationFrame invocationIdStream (transportNonceFrame ++ transportNonceStream.encode n) = none
    exact framedDecode_refuses_other_frame invocationFrame transportNonceFrame invocationIdStream _ 17 (by decide) (by decide) (by decide)
  · show framedDecode attemptFrame attemptIdStream (invocationFrame ++ invocationIdStream.encode i) = none
    exact framedDecode_refuses_other_frame attemptFrame invocationFrame attemptIdStream _ 17 (by decide) (by decide) (by decide)
  · show framedDecode generationFrame generationIdStream (invocationFrame ++ invocationIdStream.encode i) = none
    exact framedDecode_refuses_other_frame generationFrame invocationFrame generationIdStream _ 17 (by decide) (by decide) (by decide)
  · show framedDecode transportNonceFrame transportNonceStream (invocationFrame ++ invocationIdStream.encode i) = none
    exact framedDecode_refuses_other_frame transportNonceFrame invocationFrame transportNonceStream _ 17 (by decide) (by decide) (by decide)
  · show framedDecode attemptFrame attemptIdStream (transportNonceFrame ++ transportNonceStream.encode n) = none
    exact framedDecode_refuses_other_frame attemptFrame transportNonceFrame attemptIdStream _ 17 (by decide) (by decide) (by decide)

theorem objectRef_roundtrip (v : ObjectRef) :
    objectRefCodec.decode (objectRefCodec.encode v) = some v := objectRefCodec.decode_encode v
theorem revisionRef_roundtrip (v : RevisionRef) :
    revisionRefCodec.decode (revisionRefCodec.encode v) = some v := revisionRefCodec.decode_encode v
theorem invocationId_roundtrip (v : InvocationId) :
    invocationIdCodec.decode (invocationIdCodec.encode v) = some v :=
  invocationIdCodec.decode_encode v
theorem artifactRef_roundtrip (v : ArtifactRef) :
    artifactRefCodec.decode (artifactRefCodec.encode v) = some v := artifactRefCodec.decode_encode v
theorem acceptanceRef_roundtrip (v : AcceptanceRef) :
    acceptanceRefCodec.decode (acceptanceRefCodec.encode v) = some v :=
  acceptanceRefCodec.decode_encode v

/-! ## One semantic request, many attempts -/

def AttemptId.retry (attempt : AttemptId) : AttemptId :=
  { attempt with ordinal := attempt.ordinal + 1 }

/-- The paid-request ledger is keyed by the semantic request. -/
def charge (ledger : List InvocationId) (attempt : AttemptId) : List InvocationId :=
  if attempt.invocation ∈ ledger then ledger else ledger ++ [attempt.invocation]

/-- A retry is a different attempt of the same request. -/
theorem retry_distinct_same_request (attempt : AttemptId) :
    attempt.retry ≠ attempt ∧ attempt.retry.invocation = attempt.invocation := by
  refine ⟨?_, rfl⟩
  intro same
  have := congrArg AttemptId.ordinal same
  simp [AttemptId.retry] at this

/-- **Retrying physical delivery does not create a new paid request**: after
one attempt of an invocation is charged, every other attempt of that same
invocation (any ordinal, any transport nonce) leaves the ledger unchanged. -/
theorem same_invocation_charges_once (ledger : List InvocationId) (a b : AttemptId)
    (same : b.invocation = a.invocation) : charge (charge ledger a) b = charge ledger a := by
  unfold charge
  by_cases h : a.invocation ∈ ledger <;> simp [h, same]

/-- Non-vacuity: a fresh request IS charged. -/
theorem fresh_invocation_charged (ledger : List InvocationId) (a : AttemptId)
    (fresh : a.invocation ∉ ledger) : charge ledger a = ledger ++ [a.invocation] := by
  simp [charge, fresh]

/-- Every transport nonce of one attempt names the same paid request. -/
theorem nonce_does_not_name_a_request (n m : TransportNonce) (same : n.attempt = m.attempt)
    (ledger : List InvocationId) : charge (charge ledger n.attempt) m.attempt = charge ledger n.attempt :=
  same_invocation_charges_once ledger n.attempt m.attempt (by rw [same])

/-- The correlation row an attempt consumes is keyed by its invocation and the
share generation, never by the attempt ordinal. -/
def rowFor (attempt : AttemptId) (generation : Nat) : GenerationId :=
  ⟨attempt.invocation, generation⟩

theorem rowFor_retry (attempt : AttemptId) (generation : Nat) :
    rowFor attempt.retry generation = rowFor attempt generation := rfl

/-- Single-use consumption of correlation rows. -/
def consume (used : List GenerationId) (row : GenerationId) : Option (List GenerationId) :=
  if row ∈ used then none else some (used ++ [row])

/-- **The old secret correlation row cannot be consumed again by a retry.** -/
theorem retry_cannot_reconsume_row (used after : List GenerationId) (attempt : AttemptId)
    (generation : Nat) (first : consume used (rowFor attempt generation) = some after) :
    consume after (rowFor attempt.retry generation) = none := by
  unfold consume at first ⊢
  split at first
  · cases first
  · cases first
    rw [rowFor_retry]
    simp

theorem fresh_row_consumed (used : List GenerationId) (row : GenerationId) (fresh : row ∉ used) :
    consume used row = some (used ++ [row]) := by
  simp [consume, fresh]

/-! ## A content address is not a permission -/

/-- Fail closed: readable only under an explicit read audience the reader holds. -/
def ArtifactRef.mayRead (artifact : ArtifactRef) (holds : Digest → Bool) : Bool :=
  artifact.custody.any fun
    | .readAudience root => holds root
    | _ => false

theorem ArtifactRef.mayRead_requires_audience (artifact : ArtifactRef) (holds : Digest → Bool)
    (readable : artifact.mayRead holds = true) :
    ∃ root, Custody.readAudience root ∈ artifact.custody ∧ holds root = true := by
  unfold ArtifactRef.mayRead at readable
  obtain ⟨c, member, ok⟩ := List.any_eq_true.mp readable
  cases c with
  | readAudience root => exact ⟨root, member, ok⟩
  | retainThrough _ => simp at ok
  | executeAudience _ => simp at ok
  | legalForgetting _ => simp at ok

def exampleSource : WorldSource := ⟨⟨1⟩, ⟨2⟩, ⟨3⟩⟩
def exampleRevision : RevisionRef := ⟨exampleSource, 1, ⟨7⟩⟩

/-- **Same digest, length, format and origin; different read verdicts.**
Read permission is not a function of the content address. -/
theorem content_address_does_not_confer_read :
    ∃ a b : ArtifactRef, ∃ holds : Digest → Bool,
      a.digest = b.digest ∧ a.length = b.length ∧ a.format = b.format ∧ a.origin = b.origin ∧
      a.mayRead holds = true ∧ b.mayRead holds = false := by
  refine ⟨⟨⟨9⟩, 4, ⟨5⟩, exampleRevision, [.readAudience ⟨11⟩]⟩,
    ⟨⟨9⟩, 4, ⟨5⟩, exampleRevision, [.retainThrough 3]⟩,
    fun root => decide (root = ⟨11⟩), rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> decide

#assert_axioms framed_encode_injective
#assert_axioms framedDecode_refuses_other_frame
#assert_axioms invocation_family_frames_separate
#assert_axioms frames_spell
#assert_axioms objectRef_roundtrip
#assert_axioms revisionRef_roundtrip
#assert_axioms invocationId_roundtrip
#assert_axioms artifactRef_roundtrip
#assert_axioms acceptanceRef_roundtrip
#assert_axioms retry_distinct_same_request
#assert_axioms same_invocation_charges_once
#assert_axioms fresh_invocation_charged
#assert_axioms nonce_does_not_name_a_request
#assert_axioms retry_cannot_reconsume_row
#assert_axioms fresh_row_consumed
#assert_axioms ArtifactRef.mayRead_requires_audience
#assert_axioms content_address_does_not_confer_read

end Minidregg.Kernel.Contracts
