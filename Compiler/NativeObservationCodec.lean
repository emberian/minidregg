/-
Strict observation and authorized-preparation protocol. The challenge contains
only explicitly public commitments, clock/key/policy coordinates (inside the
actual canonical signing headers), and the client's own intent. Protected
payloads are released only by the source-owned observation controller.
-/
import Compiler.NativeProtocolFrames
import Compiler.NativeHostCodec

namespace Minidregg.Compiler.NativeObservationCodec

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

structure GrantRef where
  kind : ResourceKind
  target : Nat
  capability : CapabilityId
  deriving DecidableEq, Repr

inductive QueryView where
  | resource
  | policy
  /-- Only the exact observation grant used to authorize this query. -/
  | capability
  /-- The room's members, each with the greatest height at which it wrote a
  cell under the room that the reader's grant covers (PLACE §2.5). -/
  | who
  /-- The log entries above this height that wrote a cell under the room that
  the reader's grant covers, with those cells alone. -/
  | since (height : Nat)
  /-- The cell's canonical bytes as of this height (K-HISTORY-READ). -/
  | atHeight (height : Nat)
  /-- A stream window: the entries at positions `start … start+count-1`. -/
  | tail (start count : Nat)
  /-- The live links pointing at this document from cells the reader may
  observe (K-DOC-INDEX). -/
  | backlinks
  /-- The live links this document holds (K-DOC-INDEX). -/
  | links
  deriving DecidableEq, Repr

structure Query where
  kind : ResourceKind
  target : Nat
  view : QueryView
  deriving DecidableEq, Repr

inductive Purpose where
  | query (query : Query)
  | prepare (draft : NativeHostCodec.Draft)
  deriving DecidableEq, Repr

structure Intent where
  subject : SubjectId
  nonce : Nat
  purpose : Purpose
  grants : List GrantRef
  deriving DecidableEq, Repr

structure Challenge where
  intent : Intent
  domain : Digest
  semantics : Digest
  federation : FederationId
  /-- The world root the observation is answered from, at `height`. -/
  worldRoot : Digest
  /-- The authority cell's root at this observation.  Public read data: signing
  headers no longer carry it (they carry the plan's footprint), and a flow whose
  command still names an authority root reads it here. -/
  authorityRoot : Digest
  height : Nat
  /-- The deployment clock (`now`, `slot`) of the snapshot at `height`: the
  clock the read's law is judged at.  Public (the clock view publishes it). -/
  clockNow : Nat
  clockSlot : Nat
  headers : List (List UInt8)
  /-- The subject's Ed25519 signature over the intent's bytes (`intentCodec.encode`, whose
  frame separates it from every other signed message). The Host verifies it against the
  subject's current key before it reads anything about the intent's targets, and the signed
  observation carries it back so `authorize` checks it first too (FIX-DISCLOSE). -/
  intentSignature : List UInt8
  deriving DecidableEq, Repr

structure Signed where
  challenge : Challenge
  signatures : List (List UInt8)
  deriving DecidableEq, Repr

def grantStream : StreamCodec GrantRef :=
  StreamCodec.xmap (StreamCodec.product ResourceBirthCodec.resourceKindStream
    (StreamCodec.product StreamCodec.nat CredentialAuthorityEntryCodec.capabilityIdStream))
    (fun grant => (grant.kind, grant.target, grant.capability))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩) (by intro grant; cases grant; rfl)

/-- The view tag: the six fixed views as three booleans, then `since`, `at`
(each with its height) and a stream `tail` window (start, count). -/
def queryViewStream : StreamCodec QueryView :=
  StreamCodec.xmap
    (StreamCodec.sum
      (StreamCodec.sum (StreamCodec.sum StreamCodec.bool StreamCodec.bool) StreamCodec.bool)
      (StreamCodec.sum StreamCodec.nat
        (StreamCodec.sum StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat))))
    (fun view => match view with
      | .resource => .inl (.inl (.inl false))
      | .policy => .inl (.inl (.inl true))
      | .capability => .inl (.inl (.inr false))
      | .who => .inl (.inl (.inr true))
      | .backlinks => .inl (.inr false)
      | .links => .inl (.inr true)
      | .since height => .inr (.inl height)
      | .atHeight height => .inr (.inr (.inl height))
      | .tail start count => .inr (.inr (.inr (start, count))))
    (fun wire => match wire with
      | .inl (.inl (.inl false)) => .resource
      | .inl (.inl (.inl true)) => .policy
      | .inl (.inl (.inr false)) => .capability
      | .inl (.inl (.inr true)) => .who
      | .inl (.inr false) => .backlinks
      | .inl (.inr true) => .links
      | .inr (.inl height) => .since height
      | .inr (.inr (.inl height)) => .atHeight height
      | .inr (.inr (.inr (start, count))) => .tail start count)
    (by intro view; cases view <;> rfl)

def queryStream : StreamCodec Query :=
  StreamCodec.xmap (StreamCodec.product ResourceBirthCodec.resourceKindStream
    (StreamCodec.product StreamCodec.nat queryViewStream))
    (fun query => (query.kind, query.target, query.view))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩) (by intro query; cases query; rfl)

def purposeStream : StreamCodec Purpose :=
  StreamCodec.xmap (StreamCodec.sum queryStream NativeHostCodec.draftStream)
    (fun purpose => match purpose with
      | .query query => .inl query
      | .prepare draft => .inr draft)
    (fun wire => match wire with
      | .inl query => .query query
      | .inr draft => .prepare draft)
    (by intro purpose; cases purpose <;> rfl)

def intentStream : StreamCodec Intent :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product purposeStream (StreamCodec.list grantStream))))
    (fun intent => (intent.subject, intent.nonce, intent.purpose, intent.grants))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro intent; cases intent; rfl)

/-- final's intent frame before the union (who/since/at + tail). -/
def retiredIntentFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-INTENT/v4".toUTF8.toList

/-- the docuverse line's intent frame before the union (who/since/at + backlinks + links). -/
def retiredDocuverseIntentFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-INTENT/v5".toUTF8.toList

def intentCodec : LawfulCodec Intent := NativeHostCodec.framed intentFrame intentStream

def intentIdentity (intent : Intent) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-INTENT/v7".toUTF8.toList
    (intentCodec.encode intent)).digest

def federationStream : StreamCodec FederationId :=
  StreamCodec.xmap StreamCodec.nat (·.value) FederationId.mk (by intro value; cases value; rfl)

def challengeStream : StreamCodec Challenge :=
  StreamCodec.xmap
    (StreamCodec.product intentStream (StreamCodec.product digestStream (StreamCodec.product digestStream (StreamCodec.product federationStream (StreamCodec.product digestStream (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat (StreamCodec.product (StreamCodec.list bytesStream) bytesStream))))))))))
    (fun value => (value.intent, value.domain, value.semantics, value.federation, value.worldRoot, value.authorityRoot, value.height, value.clockNow, value.clockSlot, value.headers, value.intentSignature))
    (fun (intent, domain, semantics, federation, worldRoot, authorityRoot, height, clockNow, clockSlot, headers, intentSignature) =>
      ⟨intent, domain, semantics, federation, worldRoot, authorityRoot, height, clockNow, clockSlot, headers, intentSignature⟩)
    (by intro value; cases value; rfl)

def retiredChallengeFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v6".toUTF8.toList

def retiredDocuverseChallengeFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v7".toUTF8.toList

def challengeCodec : LawfulCodec Challenge := NativeHostCodec.framed challengeFrame challengeStream

def signedStream : StreamCodec Signed :=
  StreamCodec.xmap (StreamCodec.product challengeStream (StreamCodec.list bytesStream))
    (fun value => (value.challenge, value.signatures))
    (fun wire => ⟨wire.1, wire.2⟩) (by intro value; cases value; rfl)

def retiredSignedFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-SIGNED/v6".toUTF8.toList

def retiredDocuverseSignedFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-SIGNED/v7".toUTF8.toList

def signedCodec : LawfulCodec Signed := NativeHostCodec.framed signedFrame signedStream

/-- This merely transports signatures. It creates no observation token. -/
def assemble (challenge : Challenge) (signatures : List (List UInt8)) : Except String Signed :=
  if signatures.length = challenge.headers.length ∧ signatures.all (fun signature => signature.length == 64) then
    .ok ⟨challenge, signatures⟩
  else .error "observation signatures must match the header count and Ed25519 length"

@[simp] theorem intent_roundtrip (intent : Intent) :
    intentCodec.decode (intentCodec.encode intent) = some intent := intentCodec.decode_encode intent

@[simp] theorem challenge_roundtrip (challenge : Challenge) :
    challengeCodec.decode (challengeCodec.encode challenge) = some challenge := challengeCodec.decode_encode challenge

@[simp] theorem signed_roundtrip (signed : Signed) :
    signedCodec.decode (signedCodec.encode signed) = some signed := signedCodec.decode_encode signed

theorem intent_canonical {bytes : List UInt8} {intent : Intent}
    (decoded : intentCodec.decode bytes = some intent) : intentCodec.encode intent = bytes :=
  NativeHostCodec.framed_canonical _ _ decoded

theorem challenge_canonical {bytes : List UInt8} {challenge : Challenge}
    (decoded : challengeCodec.decode bytes = some challenge) : challengeCodec.encode challenge = bytes :=
  NativeHostCodec.framed_canonical _ _ decoded

theorem signed_canonical {bytes : List UInt8} {signed : Signed}
    (decoded : signedCodec.decode bytes = some signed) : signedCodec.encode signed = bytes :=
  NativeHostCodec.framed_canonical _ _ decoded

private theorem framed_refuses_prefix {A : Type} (frame old : List UInt8)
    (stream : StreamCodec A) (payload : List UInt8)
    (shorter : old.length ≤ frame.length) (different : frame.take old.length ≠ old) :
    (NativeHostCodec.framed frame stream).decode (old ++ payload) = none := by
  have mismatch : (old ++ payload).take frame.length ≠ frame := by
    intro equal
    have prefixEquality := congrArg (List.take old.length) equal
    have recoveredPrefix : old = frame.take old.length := by
      simpa [List.take_take, Nat.min_eq_left shorter] using prefixEquality
    exact different recoveredPrefix.symm
  have raw : (NativeHostCodec.framedRaw frame stream).decode (old ++ payload) = none := by
    simp [NativeHostCodec.framedRaw, mismatch]
  simp [NativeHostCodec.framed, ResourceBirthCodec.strictCodec, raw]

/-- A v6 challenge refuses to decode. -/
theorem v6_challenge_refused (payload : List UInt8) :
    challengeCodec.decode (retiredChallengeFrame ++ payload) = none := by
  exact framed_refuses_prefix challengeFrame retiredChallengeFrame challengeStream payload
    (by decide +kernel) (by decide +kernel)

/-- A v6 signed observation refuses to decode. -/
theorem v6_signed_refused (payload : List UInt8) :
    signedCodec.decode (retiredSignedFrame ++ payload) = none := by
  exact framed_refuses_prefix signedFrame retiredSignedFrame signedStream payload
    (by decide +kernel) (by decide +kernel)

/-- A v4 intent refuses to decode. -/
def retiredV3IntentFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-INTENT/v3".toUTF8.toList

theorem v3_intent_refused (payload : List UInt8) :
    intentCodec.decode (retiredV3IntentFrame ++ payload) = none := by
  have lengthExact : intentFrame.length = retiredV3IntentFrame.length := by decide +kernel
  have different : retiredV3IntentFrame ≠ intentFrame := by decide +kernel
  have raw : (NativeHostCodec.framedRaw intentFrame intentStream).decode
      (retiredV3IntentFrame ++ payload) = none := by
    simp [NativeHostCodec.framedRaw, lengthExact, different]
  simp [intentCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec, raw]

theorem v4_intent_refused (payload : List UInt8) :
    intentCodec.decode (retiredIntentFrame ++ payload) = none := by
  have lengthExact : intentFrame.length = retiredIntentFrame.length := by decide +kernel
  have different : retiredIntentFrame ≠ intentFrame := by decide +kernel
  have raw : (NativeHostCodec.framedRaw intentFrame intentStream).decode
      (retiredIntentFrame ++ payload) = none := by
    simp [NativeHostCodec.framedRaw, lengthExact, different]
  simp [intentCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec, raw]

/-- info: 'Minidregg.Compiler.NativeObservationCodec.v4_intent_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v4_intent_refused
/-- info: 'Minidregg.Compiler.NativeObservationCodec.v3_intent_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v3_intent_refused
/-- info: 'Minidregg.Compiler.NativeObservationCodec.v6_challenge_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v6_challenge_refused
/-- info: 'Minidregg.Compiler.NativeObservationCodec.v6_signed_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v6_signed_refused

/-- A v7 challenge (the docuverse line's frame) refuses to decode. -/
theorem v7_challenge_refused (payload : List UInt8) :
    challengeCodec.decode (retiredDocuverseChallengeFrame ++ payload) = none := by
  exact framed_refuses_prefix challengeFrame retiredDocuverseChallengeFrame challengeStream payload
    (by decide +kernel) (by decide +kernel)

/-- A v7 signed observation (the docuverse line's frame) refuses to decode. -/
theorem v7_signed_refused (payload : List UInt8) :
    signedCodec.decode (retiredDocuverseSignedFrame ++ payload) = none := by
  exact framed_refuses_prefix signedFrame retiredDocuverseSignedFrame signedStream payload
    (by decide +kernel) (by decide +kernel)

def retiredV8ChallengeFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v8".toUTF8.toList
def retiredV8SignedFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-SIGNED/v8".toUTF8.toList

theorem v8_challenge_refused (payload : List UInt8) :
    challengeCodec.decode (retiredV8ChallengeFrame ++ payload) = none := by
  exact framed_refuses_prefix challengeFrame retiredV8ChallengeFrame challengeStream payload
    (by decide +kernel) (by decide +kernel)

/-- A v7 signed observation (the docuverse line's frame) refuses to decode. -/
theorem v8_signed_refused (payload : List UInt8) :
    signedCodec.decode (retiredV8SignedFrame ++ payload) = none := by
  exact framed_refuses_prefix signedFrame retiredV8SignedFrame signedStream payload
    (by decide +kernel) (by decide +kernel)

/-- A v5 intent (the docuverse line's frame) refuses to decode. -/
theorem v5_intent_refused (payload : List UInt8) :
    intentCodec.decode (retiredDocuverseIntentFrame ++ payload) = none := by
  have lengthExact : intentFrame.length = retiredDocuverseIntentFrame.length := by decide +kernel
  have different : retiredDocuverseIntentFrame ≠ intentFrame := by decide +kernel
  have raw : (NativeHostCodec.framedRaw intentFrame intentStream).decode
      (retiredDocuverseIntentFrame ++ payload) = none := by
    simp [NativeHostCodec.framedRaw, lengthExact, different]
  simp [intentCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec, raw]
/-- info: 'Minidregg.Compiler.NativeObservationCodec.v7_challenge_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v7_challenge_refused
/-- info: 'Minidregg.Compiler.NativeObservationCodec.v7_signed_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v7_signed_refused
/-- info: 'Minidregg.Compiler.NativeObservationCodec.v5_intent_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v5_intent_refused

def retiredV9ChallengeFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v9".toUTF8.toList
def retiredV9SignedFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-SIGNED/v9".toUTF8.toList
def retiredV6IntentFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-INTENT/v6".toUTF8.toList

theorem v9_challenge_refused (payload : List UInt8) :
    challengeCodec.decode (retiredV9ChallengeFrame ++ payload) = none := by
  exact framed_refuses_prefix challengeFrame retiredV9ChallengeFrame challengeStream payload
    (by decide +kernel) (by decide +kernel)
theorem v9_signed_refused (payload : List UInt8) :
    signedCodec.decode (retiredV9SignedFrame ++ payload) = none := by
  exact framed_refuses_prefix signedFrame retiredV9SignedFrame signedStream payload
    (by decide +kernel) (by decide +kernel)
theorem v6_intent_refused (payload : List UInt8) :
    intentCodec.decode (retiredV6IntentFrame ++ payload) = none := by
  exact framed_refuses_prefix intentFrame retiredV6IntentFrame intentStream payload
    (by decide +kernel) (by decide +kernel)

end Minidregg.Compiler.NativeObservationCodec
