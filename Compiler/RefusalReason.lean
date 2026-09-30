/-
# Compiler.RefusalReason -- the closed set of named Host refusals

A Host refusal names the admission branch that decided it. The outcome codec
commits to the name (one tag byte), never to prose, so a client renders the
reason from data. Detail text is fixed per reason on the observation path; it
carries a controller's typed `Reject` only for `operationRejected`, which is
reached after the requester's read authority has been established.

Disclosure order. A requester learns only what it is entitled to learn:

* before its key is selected, only `malformed` or `unknownKey` (enrollment is
  a public coordinate of the challenge);
* a challenge that no longer matches the current world root, authority root
  or height is `staleRoot` (all three are public challenge fields);
* after its signature verifies, every capability failure up to and including
  holder coverage and native use is `noGrant`. Absent, stolen, out-of-scope
  and other-target capabilities are therefore indistinguishable, so a key
  cannot probe another holder's revocation, validity window or epochs;
* only a covered holder with a verified use learns `revoked`,
  `outsideValidity`, `staleGrant` or `lawDenied`.

Blind submission keeps its uniform refusal (`undisclosed`); see
`NativeHost.publicSubmissionOutcome`.
-/
import Compiler.Tower256ConcreteBackend
import Compiler.CredentialSignatureAdmission
import Theory.AuthorizationDeclaration

namespace Minidregg.Compiler

open Minidregg.Theory
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

inductive RefusalReason where
  /-- The request does not decode, or does not match the operation it names. -/
  | malformed
  /-- The requesting subject has no enrolled, usable current key. -/
  | unknownKey
  /-- The signed challenge or plan names a world root, authority read or height that is no longer current. -/
  | staleRoot
  /-- The signature does not verify for the selected key and exact request. -/
  | badSignature
  /-- No capability held by this key covers this target and operation. -/
  | noGrant
  /-- The held capability, one of its ancestors, or one of its channels is revoked. -/
  | revoked
  /-- The request height is outside the held capability's validity window. -/
  | outsideValidity
  /-- The held capability's issuer or policy epoch is no longer current. -/
  | staleGrant
  /-- The resource's current committed law denies this operation. -/
  | lawDenied
  /-- Authorized, but the operation's controller or receiver refused it. -/
  | operationRejected
  /-- A different transaction already holds this transaction identity. -/
  | conflict
  /-- A blind submission was refused; by design no state-dependent reason is disclosed. -/
  | undisclosed
  deriving DecidableEq, Repr, Inhabited

namespace RefusalReason

/-- Stable wire and display name. -/
def name : RefusalReason → String
  | .malformed => "malformed"
  | .unknownKey => "unknown-key"
  | .staleRoot => "stale-root"
  | .badSignature => "bad-signature"
  | .noGrant => "no-grant"
  | .revoked => "revoked"
  | .outsideValidity => "outside-validity"
  | .staleGrant => "stale-grant"
  | .lawDenied => "law-denied"
  | .operationRejected => "operation-rejected"
  | .conflict => "conflict"
  | .undisclosed => "undisclosed"

/-- Fixed friend-facing text. It depends on the reason only. -/
def describe : RefusalReason → String
  | .malformed => "the request does not decode or does not match its operation"
  | .unknownKey => "this key is not enrolled on this Host"
  | .staleRoot => "the Host state moved since the challenge; observe again"
  | .badSignature => "the signature does not verify for this key and request"
  | .noGrant => "this key holds no grant covering this target and operation"
  | .revoked => "the grant, one of its ancestors, or one of its channels is revoked"
  | .outsideValidity => "the request is outside the grant's validity window"
  | .staleGrant => "the grant's issuer or policy epoch is no longer current"
  | .lawDenied => "the resource's current law denies this operation"
  | .operationRejected => "the operation was refused by its controller"
  | .conflict => "transaction identity conflict"
  | .undisclosed => "request refused; a blind submission discloses no reason"

def all : List RefusalReason :=
  [.malformed, .unknownKey, .staleRoot, .badSignature, .noGrant, .revoked,
    .outsideValidity, .staleGrant, .lawDenied, .operationRejected, .conflict, .undisclosed]

theorem mem_all (reason : RefusalReason) : reason ∈ all := by
  cases reason <;> decide

/-- Names are pairwise distinct, so the rendered name identifies the reason. -/
theorem name_injective : Function.Injective name := by
  intro left right same
  cases left <;> cases right <;> first | rfl | (simp [name] at same)

/-- One tag byte. An unknown tag refuses to decode. -/
def stream : StreamCodec RefusalReason where
  encode
    | .malformed => [0]
    | .unknownKey => [1]
    | .staleRoot => [2]
    | .badSignature => [3]
    | .noGrant => [4]
    | .revoked => [5]
    | .outsideValidity => [6]
    | .staleGrant => [7]
    | .lawDenied => [8]
    | .operationRejected => [9]
    | .conflict => [10]
    | .undisclosed => [11]
  decodePrefix
    | 0 :: suffix => some (.malformed, suffix)
    | 1 :: suffix => some (.unknownKey, suffix)
    | 2 :: suffix => some (.staleRoot, suffix)
    | 3 :: suffix => some (.badSignature, suffix)
    | 4 :: suffix => some (.noGrant, suffix)
    | 5 :: suffix => some (.revoked, suffix)
    | 6 :: suffix => some (.outsideValidity, suffix)
    | 7 :: suffix => some (.staleGrant, suffix)
    | 8 :: suffix => some (.lawDenied, suffix)
    | 9 :: suffix => some (.operationRejected, suffix)
    | 10 :: suffix => some (.conflict, suffix)
    | 11 :: suffix => some (.undisclosed, suffix)
    | _ => none
  decodePrefix_encode := by intro value suffix; cases value <;> rfl

theorem stream_unknown_tag (suffix : List UInt8) :
    stream.decodePrefix (12 :: suffix) = none := rfl

/-- The signature adapter's typed rejection, named. Key absence, unusable key
records and a key version that is unregistered or revoked (its standing in the
authority cell) are `unknownKey`: the subject has no usable current key. A
moved subject-key epoch, a signed footprint whose authority read has changed,
and a plan past its signed `validUntil` height are `staleRoot`: the signed plan
no longer describes the current state. A footprint that does not decode is
`malformed`; every envelope and binding failure is `badSignature`. -/
def ofSignature : CredentialSignatureAdmission.Reject → RefusalReason
  | .wrongDomain => .malformed
  | .missingCurrentKey => .unknownKey
  | .subjectKeyEpoch => .staleRoot
  | .unregisteredKey => .unknownKey
  | .revokedKey => .unknownKey
  | .unsupportedAlgorithm => .unknownKey
  | .publicKeyLength => .unknownKey
  | .envelope _ => .badSignature
  | .sourceBinding => .badSignature
  | .malformedFootprint => .malformed
  | .footprintStale _ => .staleRoot
  | .expired _ _ => .staleRoot

theorem ofSignature_missingCurrentKey :
    ofSignature .missingCurrentKey = .unknownKey := rfl

theorem ofSignature_envelope
    (failure : Kernel.CredentialSignedEnvelopeController.Failure CredentialSignatureIO.Error) :
    ofSignature (.envelope failure) = .badSignature := rfl

/-! ## Capability admission, component by component -/

/-- Every component of `Capability.Admissible`, in exactly the order that
`capabilityAdmissibleCheck` evaluates it, each paired with the reason its
failure is reported under. Holder and scope come first, so a key that does
not hold the capability learns only `noGrant`. -/
def capabilityChecks {kind : ResourceKind} (cap : Capability kind) (state : AuthState)
    (request : Request kind) : List (RefusalReason × Bool) :=
  [(.noGrant, holderCoversCheck cap.holder request.subject),
   (.noGrant, scopeCoversCheck cap.scope request),
   (.outsideValidity, decide (cap.notBefore ≤ request.height)),
   (.outsideValidity, decide (request.height ≤ cap.notAfter)),
   (.noGrant, decide (cap.policyId = request.policyId)),
   (.staleGrant, decide (cap.policyEpoch = request.policyEpoch)),
   (.staleGrant, decide (cap.policyEpoch = state.policyEpoch cap.policyId)),
   (.staleGrant, decide (cap.issuerEpoch = state.issuerEpoch cap.issuer)),
   (.revoked, decide (RevocationKey.capability cap.id ∉ state.revoked)),
   (.revoked, capabilityIdsUnrevoked state cap.ancestors),
   (.revoked, channelIdsUnrevoked state cap.channels)]

/-- The first failing component's reason; `none` exactly when admissible. -/
def capabilityRefusal {kind : ResourceKind} (cap : Capability kind) (state : AuthState)
    (request : Request kind) : Option RefusalReason :=
  ((capabilityChecks cap state request).find? (fun check => !check.2)).map Prod.fst

private theorem firstFailure_none_iff (checks : List (RefusalReason × Bool)) :
    (checks.find? (fun check => !check.2)).map Prod.fst = none ↔
      (checks.map Prod.snd).all (fun accepted => accepted) = true := by
  induction checks with
  | nil => simp
  | cons head tail ih =>
      obtain ⟨reason, accepted⟩ := head
      cases accepted <;> simp [ih]

/-- The classifier is the existing admission decision, not a second one: it
reports no reason exactly when `capabilityAdmissibleCheck` accepts. -/
theorem capabilityRefusal_eq_none_iff {kind : ResourceKind} (cap : Capability kind)
    (state : AuthState) (request : Request kind) :
    capabilityRefusal cap state request = none ↔
      capabilityAdmissibleCheck cap state request = true :=
  firstFailure_none_iff (capabilityChecks cap state request)

theorem capabilityRefusal_eq_none_iff_admissible {kind : ResourceKind}
    (cap : Capability kind) (state : AuthState) (request : Request kind) :
    capabilityRefusal cap state request = none ↔ cap.Admissible state request := by
  rw [capabilityRefusal_eq_none_iff, capabilityAdmissibleCheck_eq_true_iff]

/-- A capability whose holder does not cover the requester is reported as
`noGrant`, whatever else is true of it (revoked, expired or stale). -/
theorem capabilityRefusal_holder {kind : ResourceKind} (cap : Capability kind)
    (state : AuthState) (request : Request kind)
    (foreign : holderCoversCheck cap.holder request.subject = false) :
    capabilityRefusal cap state request = some .noGrant := by
  simp [capabilityRefusal, capabilityChecks, foreign]

/-! ## Both poles on concrete instances -/

namespace Sample

def owner : SubjectId := ⟨7⟩
def thief : SubjectId := ⟨9⟩
def target : ResourceId .object := ⟨42⟩

def state (revoked : Finset RevocationKey) (policyEpoch : Epoch) : AuthState where
  capabilityRoot := ⟨0⟩
  revocationRoot := ⟨0⟩
  policyRoot := ⟨0⟩
  policyAddress := fun _ _ => ⟨0⟩
  revoked := revoked
  issuerEpoch := fun _ => 0
  policyEpoch := fun _ => policyEpoch
  policyRevision := fun _ => 0
  subjectKeyEpoch := fun _ => 0

def grant (notAfter : Height) : Capability .object where
  id := ⟨100⟩
  root := ⟨100⟩
  parent := none
  issuer := ⟨1⟩
  holder := .subject owner
  scope := ⟨{target}, {.observeObject}, 1000⟩
  notBefore := 0
  notAfter := notAfter
  issuerEpoch := 0
  policyId := ⟨42⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def read (subject : SubjectId) (height : Height) : Request .object where
  domain := ⟨0⟩
  semantics := ⟨0⟩
  federation := ⟨0⟩
  subject := subject
  subjectKeyEpoch := 0
  target := target
  verb := .observeObject
  argsDigest := ⟨0⟩
  effectsDigest := ⟨0⟩
  nonce := 0
  height := height
  preStateRoot := ⟨0⟩
  policyId := ⟨42⟩
  policyEpoch := 0
  policyRevision := 0
  cost := 10

end Sample

open Sample in
theorem sample_admitted :
    capabilityRefusal (grant 50) (state ∅ 0) (read owner 5) = none := by decide

open Sample in
theorem sample_foreign_holder_noGrant :
    capabilityRefusal (grant 50) (state ∅ 0) (read thief 5) = some .noGrant := by decide

open Sample in
/-- A thief presenting a revoked capability still learns only `noGrant`. -/
theorem sample_foreign_revoked_noGrant :
    capabilityRefusal (grant 50) (state {.capability ⟨100⟩} 0) (read thief 5) =
      some .noGrant := by decide

open Sample in
theorem sample_revoked :
    capabilityRefusal (grant 50) (state {.capability ⟨100⟩} 0) (read owner 5) =
      some .revoked := by decide

open Sample in
theorem sample_outsideValidity :
    capabilityRefusal (grant 50) (state ∅ 0) (read owner 51) = some .outsideValidity := by decide

open Sample in
theorem sample_staleGrant :
    capabilityRefusal (grant 50) (state ∅ 1) { read owner 5 with policyEpoch := 1 } =
      some .staleGrant := by decide

open Sample in
theorem sample_other_target_noGrant :
    capabilityRefusal (grant 50) (state ∅ 0) { read owner 5 with target := ⟨43⟩ } =
      some .noGrant := by decide

end RefusalReason

/-- A named refusal with its display text. -/
structure Refusal where
  reason : RefusalReason
  detail : String
  deriving DecidableEq, Repr

/-- The fixed text for a reason; nothing state-dependent is added. -/
def Refusal.of (reason : RefusalReason) : Refusal := ⟨reason, reason.describe⟩

instance : ToString Refusal := ⟨fun refusal => s!"refused: {refusal.reason.name}: {refusal.detail}"⟩

end Minidregg.Compiler

#print axioms Minidregg.Compiler.RefusalReason.capabilityRefusal_eq_none_iff_admissible
#print axioms Minidregg.Compiler.RefusalReason.sample_admitted
#print axioms Minidregg.Compiler.RefusalReason.sample_revoked
