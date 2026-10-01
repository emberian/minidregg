/-
Strict observation and authorized-preparation protocol. The challenge contains
only explicitly public commitments, clock/key/policy coordinates (inside the
actual canonical signing headers), and the client's own intent. Protected
payloads are released only by the source-owned observation controller.
-/
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
  headers : List (List UInt8)
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

/-- The view tag: the six fixed views as three booleans, then `since`/`at`
with their height. -/
def queryViewStream : StreamCodec QueryView :=
  StreamCodec.xmap
    (StreamCodec.sum
      (StreamCodec.sum (StreamCodec.sum StreamCodec.bool StreamCodec.bool) StreamCodec.bool)
      (StreamCodec.sum StreamCodec.nat StreamCodec.nat))
    (fun view => match view with
      | .resource => .inl (.inl (.inl false))
      | .policy => .inl (.inl (.inl true))
      | .capability => .inl (.inl (.inr false))
      | .who => .inl (.inl (.inr true))
      | .backlinks => .inl (.inr false)
      | .links => .inl (.inr true)
      | .since height => .inr (.inl height)
      | .atHeight height => .inr (.inr height))
    (fun wire => match wire with
      | .inl (.inl (.inl false)) => .resource
      | .inl (.inl (.inl true)) => .policy
      | .inl (.inl (.inr false)) => .capability
      | .inl (.inl (.inr true)) => .who
      | .inl (.inr false) => .backlinks
      | .inl (.inr true) => .links
      | .inr (.inl height) => .since height
      | .inr (.inr height) => .atHeight height)
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

/-- v5 (K-DOC-INDEX): the query view gains `backlinks` and `links`, and the
view tag is re-laid out again; a v4 intent refuses (`v4_intent_refused`). v4
(K-INDEX) added `who`, `since h` and `at h`. -/
def intentFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-INTENT/v5".toUTF8.toList

def retiredIntentFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-INTENT/v4".toUTF8.toList

def intentCodec : LawfulCodec Intent := NativeHostCodec.framed intentFrame intentStream

def intentIdentity (intent : Intent) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-INTENT/v5".toUTF8.toList
    (intentCodec.encode intent)).digest

def federationStream : StreamCodec FederationId :=
  StreamCodec.xmap StreamCodec.nat (·.value) FederationId.mk (by intro value; cases value; rfl)

def challengeStream : StreamCodec Challenge :=
  StreamCodec.xmap
    (StreamCodec.product intentStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream (StreamCodec.product federationStream
        (StreamCodec.product digestStream (StreamCodec.product digestStream
          (StreamCodec.product StreamCodec.nat (StreamCodec.list bytesStream))))))))
    (fun value => (value.intent, value.domain, value.semantics, value.federation,
      value.worldRoot, value.authorityRoot, value.height, value.headers))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1,
      wire.2.2.2.2.1, wire.2.2.2.2.2.1, wire.2.2.2.2.2.2.1, wire.2.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

/-- v7 (K-DOC-INDEX): the embedded intent is v5. v6 (K-INDEX) embedded the
v4 intent. v5 (the wave-c merge) bound
`(worldRoot, height)`, named the authority root as public read data, and put
the plan footprint in the headers (envelope version 2). Every v5 challenge
refuses, and so does every v6 (`v6_challenge_refused`). -/
def challengeFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v7".toUTF8.toList

def retiredChallengeFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v6".toUTF8.toList

def challengeCodec : LawfulCodec Challenge := NativeHostCodec.framed challengeFrame challengeStream

def signedStream : StreamCodec Signed :=
  StreamCodec.xmap (StreamCodec.product challengeStream (StreamCodec.list bytesStream))
    (fun value => (value.challenge, value.signatures))
    (fun wire => ⟨wire.1, wire.2⟩) (by intro value; cases value; rfl)

def signedFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-SIGNED/v7".toUTF8.toList

def retiredSignedFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-SIGNED/v6".toUTF8.toList

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

/-- A v6 challenge refuses to decode. -/
theorem v6_challenge_refused (payload : List UInt8) :
    challengeCodec.decode (retiredChallengeFrame ++ payload) = none := by
  have lengthExact : challengeFrame.length = retiredChallengeFrame.length := by decide +kernel
  have different : retiredChallengeFrame ≠ challengeFrame := by decide +kernel
  have raw : (NativeHostCodec.framedRaw challengeFrame challengeStream).decode
      (retiredChallengeFrame ++ payload) = none := by
    simp [NativeHostCodec.framedRaw, lengthExact, different]
  simp [challengeCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec, raw]

/-- A v6 signed observation refuses to decode. -/
theorem v6_signed_refused (payload : List UInt8) :
    signedCodec.decode (retiredSignedFrame ++ payload) = none := by
  have lengthExact : signedFrame.length = retiredSignedFrame.length := by decide +kernel
  have different : retiredSignedFrame ≠ signedFrame := by decide +kernel
  have raw : (NativeHostCodec.framedRaw signedFrame signedStream).decode
      (retiredSignedFrame ++ payload) = none := by
    simp [NativeHostCodec.framedRaw, lengthExact, different]
  simp [signedCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec, raw]

/-- A v4 intent refuses to decode. -/
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
/-- info: 'Minidregg.Compiler.NativeObservationCodec.v6_challenge_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v6_challenge_refused
/-- info: 'Minidregg.Compiler.NativeObservationCodec.v6_signed_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v6_signed_refused

end Minidregg.Compiler.NativeObservationCodec
