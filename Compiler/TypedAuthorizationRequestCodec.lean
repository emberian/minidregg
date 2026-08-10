/-
# Compiler.TypedAuthorizationRequestCodec -- the common request, on the wire

`HyperdocumentOperations.Config` demands `LawfulCodec (Request .object)` and
nothing supplied one, which gates every carrier that needs a `Config`.

It belongs here rather than in `Theory/`.  Byte transport is a compiler
concern, the framework for it is `Tower256ConcreteBackend.StreamCodec` -- a
prefix codec carrying `decodePrefix (encode value ++ suffix) = some (value,
suffix)`, so sequential composition needs no delimiter -- and the neighbouring
tag codecs for resource kinds and verbs already live in
`SemanticTurnReceiptDescriptor`.  `Theory/` could not import any of it, which
is the correct reason it is not the home for this.

The whole construction is `xmap` over `nat` for each wrapper field, `product`
right-nested for the record, and `rfl` for the retraction, since structure eta
makes rebuilding a record from its own projections definitional.  Naturals ride
`StreamCodec.nat`'s base-255 little-endian digits, so the encoding is
logarithmic in each field.
-/
import Compiler.Tower256ConcreteBackend
import Theory.TypedAuthorization

namespace Minidregg.Compiler.TypedAuthorizationRequestCodec

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Wrapper fields -/

def subjectIdStream : StreamCodec SubjectId :=
  StreamCodec.xmap StreamCodec.nat SubjectId.value SubjectId.mk
    (by intro value; cases value; rfl)

def policyIdStream : StreamCodec PolicyId :=
  StreamCodec.xmap StreamCodec.nat PolicyId.value PolicyId.mk
    (by intro value; cases value; rfl)

def federationIdStream : StreamCodec FederationId :=
  StreamCodec.xmap StreamCodec.nat FederationId.value FederationId.mk
    (by intro value; cases value; rfl)

def resourceIdStream (kind : ResourceKind) : StreamCodec (ResourceId kind) :=
  StreamCodec.xmap StreamCodec.nat ResourceId.value ResourceId.mk
    (by intro value; cases value; rfl)

/-! ## The one dependent field

`Verb` is kind-indexed, so at a fixed kind it is a finite tag.  The tags agree
with `SemanticTurnReceiptDescriptor.verbTag` on the object constructors, which
keeps one numbering in the tree rather than two. -/

def objectVerbTag : Verb .object -> Nat
  | .observeObject => 1
  | .mutateObject => 2
  | .delegateObject => 3

def objectVerbOfTag : Nat -> Verb .object
  | 1 => .observeObject
  | 2 => .mutateObject
  | _ => .delegateObject

theorem objectVerbOfTag_tag (verb : Verb .object) :
    objectVerbOfTag (objectVerbTag verb) = verb := by
  cases verb <;> rfl

def objectVerbStream : StreamCodec (Verb .object) :=
  StreamCodec.xmap StreamCodec.nat objectVerbTag objectVerbOfTag
    objectVerbOfTag_tag

/-! ## The request -/

abbrev RequestTuple :=
  Digest × Digest × FederationId × SubjectId × Nat × ResourceId .object ×
    Verb .object × Digest × Digest × Nat × Nat × Digest × PolicyId × Nat × Nat

def requestTupleStream : StreamCodec RequestTuple :=
  StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product federationIdStream (StreamCodec.product subjectIdStream
      (StreamCodec.product StreamCodec.nat
        (StreamCodec.product (resourceIdStream .object)
          (StreamCodec.product objectVerbStream (StreamCodec.product digestStream
            (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat
              (StreamCodec.product StreamCodec.nat (StreamCodec.product digestStream
                (StreamCodec.product policyIdStream
                  (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))))))))

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

def requestStream : StreamCodec (Request .object) :=
  StreamCodec.xmap requestTupleStream requestTuple requestOfTuple
    requestOfTuple_tuple

/-- **`LawfulCodec (Request .object)` exists.**  One of the three codecs a
`HyperdocumentOperations.Config` demands. -/
def requestCodec : LawfulCodec (Request .object) := requestStream.toLawful

/-! ## Teeth: the encoding separates requests that differ where it matters

`decode_encode` alone does not forbid a codec that collapses a field -- it
would still round-trip if the type were a subsingleton, and `Request` is not.
These check the two fields authority most depends on: a codec that lost the
target would let one object be authorized and another installed. -/

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

/-- And the stream codec composes: encoding a request in front of arbitrary
trailing bytes still decodes to exactly that request and exactly that suffix.
This is the property `LawfulCodec` alone does not carry, and the reason a
`Declaration` codec can be built on top of this one. -/
theorem requestStream_composes (request : Request .object)
    (suffix : List UInt8) :
    requestStream.decodePrefix (requestStream.encode request ++ suffix) =
      some (request, suffix) :=
  requestStream.decodePrefix_encode request suffix

/-! ## Axiom pins -/

/-- info: 'Minidregg.Compiler.TypedAuthorizationRequestCodec.objectVerbOfTag_tag' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms objectVerbOfTag_tag
/-- info: 'Minidregg.Compiler.TypedAuthorizationRequestCodec.requestOfTuple_tuple' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms requestOfTuple_tuple
/-- info: 'Minidregg.Compiler.TypedAuthorizationRequestCodec.requestCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms requestCodec
/-- info: 'Minidregg.Compiler.TypedAuthorizationRequestCodec.requestCodec_separates_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms requestCodec_separates_target
/-- info: 'Minidregg.Compiler.TypedAuthorizationRequestCodec.requestCodec_separates_effectsDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms requestCodec_separates_effectsDigest
/-- info: 'Minidregg.Compiler.TypedAuthorizationRequestCodec.requestStream_composes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms requestStream_composes

end Minidregg.Compiler.TypedAuthorizationRequestCodec
