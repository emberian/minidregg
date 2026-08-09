/-
# Theory.HyperdocumentOperationIntent -- acyclic pre-commit operation identity

A mutable content record cannot store the final `VersionEventId` which hashes
an event containing that record's post-state root: doing so asks a deployment
hash for a fixed point.  Hyperdocument content instead stores `OperationId`,
derived from this pre-commit intent.  The intent binds canonical action bytes,
document/schema/parents/author, the expected content pre-root, and a nonce.  It
contains no post root, request/effect id, or final version id.

After content acceptance, the final `VersionEventRecord` binds this operation
id to the actual post root and request/effect identities.  Its separately
derived `VersionEventId` belongs in the append-only event-log cell.
-/
import Theory.Hyperdocument

namespace Minidregg.Theory.HyperdocumentOperationIntent

open IndexedProgram
open TypedAuthorization
open Hyperdocument

set_option autoImplicit false

/-- Complete first-order pre-commit identity.  `actionBytes` must be the lawful
codec output of the action payload used by the accepted-effect family. -/
structure OperationIntent where
  historyDomain : Digest
  document : DocumentId
  schema : CausalVersionDag.SchemaRef
  parents : List VersionEventId
  author : PrincipalRef
  expectedContentRoot : Digest
  nonce : Nat
  actionBytes : List UInt8
  deriving DecidableEq, Repr

/-- One selected canonical intent codec and abstract digest projection.  The
digest operation carries no collision-resistance or equality-reflection field. -/
structure Addressing where
  codec : LawfulCodec OperationIntent
  derivation : DigestDerivation

/-- Domain-separated operation-id preimage. -/
def idPreimage (addressing : Addressing) (intent : OperationIntent) :
    IdPreimage .v1 .operationIntent :=
  ⟨addressing.codec.encode intent⟩

def operationId (addressing : Addressing) (intent : OperationIntent) :
    OperationId :=
  deriveIdentifier addressing.derivation (idPreimage addressing intent)

@[simp] theorem idPreimage_payload
    (addressing : Addressing) (intent : OperationIntent) :
    (idPreimage addressing intent).payload = addressing.codec.encode intent :=
  rfl

/-- Canonical preimage bytes reflect exact intent equality before digesting. -/
theorem idPreimage_injective (addressing : Addressing) :
    Function.Injective (idPreimage addressing) := by
  intro left right equal
  apply lawfulCodec_encode_injective addressing.codec
  exact congrArg IdPreimage.payload equal

/-- Explicit old-cycle refuter: even when a caller mentions an arbitrary post
root, the canonical operation identity is unchanged because no post root is an
input to its preimage.  This is definitional, not a hash assumption. -/
def operationIdMentioningPost
    (addressing : Addressing) (intent : OperationIntent)
    (_postRoot : Digest) : OperationId :=
  operationId addressing intent

theorem operation_id_independent_of_post_root
    (addressing : Addressing) (intent : OperationIntent)
    (leftPost rightPost : Digest) :
    operationIdMentioningPost addressing intent leftPost =
      operationIdMentioningPost addressing intent rightPost :=
  rfl

/-- Compatibility helper for callers which have already computed a candidate
post root.  The argument is intentionally ignored by construction. -/
def idPreimageMentioningPost
    (addressing : Addressing) (intent : OperationIntent)
    (_postRoot : Digest) : IdPreimage .v1 .operationIntent :=
  idPreimage addressing intent

/-- The same tooth holds at canonical bytes, before an abstract digest can
possibly collapse two values. -/
theorem operation_preimage_independent_of_post_root
    (addressing : Addressing) (intent : OperationIntent)
    (leftPost rightPost : Digest) :
    encodePreimage (idPreimageMentioningPost addressing intent leftPost) =
      encodePreimage (idPreimageMentioningPost addressing intent rightPost) :=
  rfl

/-- Operation and final-version preimage byte domains are structurally
disjoint.  No cryptographic collision theorem is inferred from this fact. -/
theorem operation_version_preimage_domains_disjoint
    (addressing : Addressing) (intent : OperationIntent)
    (versionPayload : IdPreimage .v1 .versionEvent) :
    encodePreimage (idPreimage addressing intent) ≠
      encodePreimage versionPayload := by
  apply preimage_encodings_disjoint
  decide

/-- A declaration/action codec is bound to one exact intent by byte equality,
not by an untrusted Boolean flag. -/
structure ActionBytesExact
    (intent : OperationIntent)
    (canonicalActionBytes : List UInt8) : Prop where
  exact : intent.actionBytes = canonicalActionBytes

theorem ActionBytesExact.intent_eq_of_action_bytes_eq
    {left right : OperationIntent}
    (otherFields :
      { left with actionBytes := right.actionBytes } = right)
    (actionBytes : left.actionBytes = right.actionBytes) :
    left = right := by
  calc
    left = { left with actionBytes := right.actionBytes } := by
      cases left
      cases right
      simp_all
    _ = right := otherFields

#print axioms idPreimage_injective
#print axioms operation_id_independent_of_post_root
#print axioms operation_version_preimage_domains_disjoint

end Minidregg.Theory.HyperdocumentOperationIntent
