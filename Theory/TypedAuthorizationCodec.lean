/-
# Theory.TypedAuthorizationCodec -- a lawful codec for the common request

`HyperdocumentOperations.Config` demands `LawfulCodec (Request .object)`, and
none existed.  This builds one out of `Theory.ByteCodecs`, which is the first
real exercise of that toolkit: fifteen fields, thirteen of them natural-number
wrappers, one kind-indexed identifier, and one three-constructor verb.

The whole construction is mechanical, and deliberately so.  Every field codec
is `codecOfRetraction` over `natCodec`; the record codec is
`codecOfRetraction` over a right-nested tuple of them; and the retraction
proof is `rfl`, because structure eta makes rebuilding a record from its own
projections definitional.  That is the point of the toolkit: a `Config` should
cost a page, not a research problem.

Unary and therefore enormous, as `ByteCodecs` says.  Not a deployment codec.
-/
import Theory.ByteCodecs
import Theory.TypedAuthorization

namespace Minidregg.Theory.TypedAuthorizationCodec

open Minidregg.Theory.ByteCodecs
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## The natural-number wrappers -/

def digestCodec : LawfulCodec Digest :=
  codecOfRetraction natCodec Digest.value Digest.mk (fun _ => rfl)

def subjectIdCodec : LawfulCodec SubjectId :=
  codecOfRetraction natCodec SubjectId.value SubjectId.mk (fun _ => rfl)

def policyIdCodec : LawfulCodec PolicyId :=
  codecOfRetraction natCodec PolicyId.value PolicyId.mk (fun _ => rfl)

def federationIdCodec : LawfulCodec FederationId :=
  codecOfRetraction natCodec FederationId.value FederationId.mk (fun _ => rfl)

def resourceIdCodec (kind : ResourceKind) : LawfulCodec (ResourceId kind) :=
  codecOfRetraction natCodec ResourceId.value ResourceId.mk (fun _ => rfl)

/-! ## The one non-wrapper field -/

/-- Object verbs as a tag.  `backward` is total, so the retraction is a case
split rather than an option. -/
def objectVerbTag : Verb .object -> Nat
  | .observeObject => 0
  | .mutateObject => 1
  | .delegateObject => 2

def objectVerbOfTag : Nat -> Verb .object
  | 0 => .observeObject
  | 1 => .mutateObject
  | _ => .delegateObject

theorem objectVerbOfTag_tag (verb : Verb .object) :
    objectVerbOfTag (objectVerbTag verb) = verb := by
  cases verb <;> rfl

def objectVerbCodec : LawfulCodec (Verb .object) :=
  codecOfRetraction natCodec objectVerbTag objectVerbOfTag objectVerbOfTag_tag

/-! ## The request

The tuple is right-nested in field order, so `forward` and `backward` are each
one anonymous constructor and the retraction is `rfl`. -/

abbrev RequestTuple :=
  Digest × Digest × FederationId × SubjectId × Nat × ResourceId .object ×
    Verb .object × Digest × Digest × Nat × Nat × Digest × PolicyId × Nat × Nat

def requestTupleCodec : LawfulCodec RequestTuple :=
  pairCodec digestCodec (pairCodec digestCodec (pairCodec federationIdCodec
    (pairCodec subjectIdCodec (pairCodec natCodec
      (pairCodec (resourceIdCodec .object) (pairCodec objectVerbCodec
        (pairCodec digestCodec (pairCodec digestCodec (pairCodec natCodec
          (pairCodec natCodec (pairCodec digestCodec (pairCodec policyIdCodec
            (pairCodec natCodec natCodec)))))))))))))

def requestTuple (request : Request .object) : RequestTuple :=
  ⟨request.domain, request.semantics, request.federation, request.subject,
    request.subjectKeyEpoch, request.target, request.verb, request.argsDigest,
    request.effectsDigest, request.nonce, request.height, request.preStateRoot,
    request.policyId, request.policyEpoch, request.cost⟩

def requestOfTuple (tuple : RequestTuple) : Request .object where
  domain := tuple.1
  semantics := tuple.2.1
  federation := tuple.2.2.1
  subject := tuple.2.2.2.1
  subjectKeyEpoch := tuple.2.2.2.2.1
  target := tuple.2.2.2.2.2.1
  verb := tuple.2.2.2.2.2.2.1
  argsDigest := tuple.2.2.2.2.2.2.2.1
  effectsDigest := tuple.2.2.2.2.2.2.2.2.1
  nonce := tuple.2.2.2.2.2.2.2.2.2.1
  height := tuple.2.2.2.2.2.2.2.2.2.2.1
  preStateRoot := tuple.2.2.2.2.2.2.2.2.2.2.2.1
  policyId := tuple.2.2.2.2.2.2.2.2.2.2.2.2.1
  policyEpoch := tuple.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  cost := tuple.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem requestOfTuple_tuple (request : Request .object) :
    requestOfTuple (requestTuple request) = request := rfl

/-- **`LawfulCodec (Request .object)` exists.**  One of the three codecs
`HyperdocumentOperations.Config` demands. -/
def requestCodec : LawfulCodec (Request .object) :=
  codecOfRetraction requestTupleCodec requestTuple requestOfTuple
    requestOfTuple_tuple

/-! ## Teeth: the codec separates requests that differ anywhere

A codec that collapsed a field would round-trip and still be useless -- the
`decode_encode` law alone does not forbid `encode := fun _ => []` composed with
a constant `decode` unless the type is a subsingleton, and `Request` is not.
These check the two fields most load-bearing for authority. -/

theorem requestCodec_separates_target
    (request : Request .object) (other : ResourceId .object)
    (different : request.target ≠ other) :
    requestCodec.encode request ≠
      requestCodec.encode { request with target := other } := by
  intro same
  apply different
  have decoded := congrArg requestCodec.decode same
  rw [requestCodec.decode_encode, requestCodec.decode_encode] at decoded
  exact congrArg Request.target (Option.some.inj decoded)

theorem requestCodec_separates_effectsDigest
    (request : Request .object) (other : Digest)
    (different : request.effectsDigest ≠ other) :
    requestCodec.encode request ≠
      requestCodec.encode { request with effectsDigest := other } := by
  intro same
  apply different
  have decoded := congrArg requestCodec.decode same
  rw [requestCodec.decode_encode, requestCodec.decode_encode] at decoded
  exact congrArg Request.effectsDigest (Option.some.inj decoded)

#print axioms objectVerbOfTag_tag
#print axioms requestOfTuple_tuple
#print axioms requestCodec
#print axioms requestCodec_separates_target
#print axioms requestCodec_separates_effectsDigest

end Minidregg.Theory.TypedAuthorizationCodec
