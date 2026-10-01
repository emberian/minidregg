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

def queryViewStream : StreamCodec QueryView :=
  StreamCodec.xmap (StreamCodec.sum StreamCodec.bool StreamCodec.bool)
    (fun view => match view with
      | .resource => .inl false
      | .policy => .inl true
      | .capability => .inr false)
    (fun wire => match wire with
      | .inl false => .resource
      | .inl true => .policy
      | .inr _ => .capability)
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

/-- v3 embeds the v3 host draft and binds the complete ordered joint read
footprint. Old observation transcripts cannot be interpreted as joint intent. -/
def intentFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-INTENT/v3".toUTF8.toList

def intentCodec : LawfulCodec Intent := NativeHostCodec.framed intentFrame intentStream

def intentIdentity (intent : Intent) : Digest :=
  (Sp800185Cshake256.hash "DREGG.NATIVE-HOST.OBSERVE-INTENT/v3".toUTF8.toList
    (intentCodec.encode intent)).digest

def federationStream : StreamCodec FederationId :=
  StreamCodec.xmap StreamCodec.nat (·.value) FederationId.mk (by intro value; cases value; rfl)

def challengeStream : StreamCodec Challenge :=
  StreamCodec.xmap
    (StreamCodec.product intentStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream (StreamCodec.product federationStream
        (StreamCodec.product digestStream (StreamCodec.product digestStream
          (StreamCodec.product StreamCodec.nat
            (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat (StreamCodec.list bytesStream))))))))))
    (fun value => (value.intent, value.domain, value.semantics, value.federation,
      value.worldRoot, value.authorityRoot, value.height, value.clockNow, value.clockSlot,
      value.headers))
    (fun (intent, domain, semantics, federation, worldRoot, authorityRoot, height, now, slot,
        headers) =>
      ⟨intent, domain, semantics, federation, worldRoot, authorityRoot, height, now, slot, headers⟩)
    (by intro value; cases value; rfl)

/-- v6 (CLOCK-SUBJECT): the challenge also names the deployment clock
`(now, slot)` at `height`, the clock a read's law is judged at.  v5 bound
`(worldRoot, height)`, named the authority root as public read data, and its
headers carry the plan footprint (envelope version 2).  Every v5 challenge
refuses (`v5_challenge_refused`). -/
def challengeFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v6".toUTF8.toList

def retiredChallengeFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-CHALLENGE/v5".toUTF8.toList

def challengeCodec : LawfulCodec Challenge := NativeHostCodec.framed challengeFrame challengeStream

def signedStream : StreamCodec Signed :=
  StreamCodec.xmap (StreamCodec.product challengeStream (StreamCodec.list bytesStream))
    (fun value => (value.challenge, value.signatures))
    (fun wire => ⟨wire.1, wire.2⟩) (by intro value; cases value; rfl)

def signedFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-SIGNED/v6".toUTF8.toList

def retiredSignedFrame : List UInt8 := "DREGG/NATIVE-HOST/OBSERVE-SIGNED/v5".toUTF8.toList

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

/-- A v5 challenge (no clock) refuses to decode. -/
theorem v5_challenge_refused (payload : List UInt8) :
    challengeCodec.decode (retiredChallengeFrame ++ payload) = none := by
  have lengthExact : challengeFrame.length = retiredChallengeFrame.length := by decide +kernel
  have different : retiredChallengeFrame ≠ challengeFrame := by decide +kernel
  have raw : (NativeHostCodec.framedRaw challengeFrame challengeStream).decode
      (retiredChallengeFrame ++ payload) = none := by
    simp [NativeHostCodec.framedRaw, lengthExact, different]
  simp [challengeCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec, raw]

/-- A v5 signed observation refuses to decode. -/
theorem v5_signed_refused (payload : List UInt8) :
    signedCodec.decode (retiredSignedFrame ++ payload) = none := by
  have lengthExact : signedFrame.length = retiredSignedFrame.length := by decide +kernel
  have different : retiredSignedFrame ≠ signedFrame := by decide +kernel
  have raw : (NativeHostCodec.framedRaw signedFrame signedStream).decode
      (retiredSignedFrame ++ payload) = none := by
    simp [NativeHostCodec.framedRaw, lengthExact, different]
  simp [signedCodec, NativeHostCodec.framed, ResourceBirthCodec.strictCodec, raw]

/-- info: 'Minidregg.Compiler.NativeObservationCodec.v5_challenge_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v5_challenge_refused
/-- info: 'Minidregg.Compiler.NativeObservationCodec.v5_signed_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms v5_signed_refused

end Minidregg.Compiler.NativeObservationCodec
