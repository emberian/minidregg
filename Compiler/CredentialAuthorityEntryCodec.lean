/-
# Compiler.CredentialAuthorityEntryCodec -- exact executable authority payloads

The payload types are the actual `TypedAuthorization.Capability` and
`CredentialAuthorityState.StoredCapability`; no transport-side authority
model participates. Finite sets are encoded in sorted natural-label order,
not through a noncomputable choice of enumeration. Naturals use the shared
compact prefix codec. Whole-page canonical decoding is enforced by the page
materializer, including rejection of aliases accepted by primitive codecs.
-/
import Compiler.TypedAuthorizationRequestCodec
import Compiler.CredentialSigningKeyCodec
import Theory.CredentialAuthorityState
import Mathlib.Data.Finset.Sort

namespace Minidregg.Compiler.CredentialAuthorityEntryCodec

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.TypedAuthorizationRequestCodec
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityFamily

set_option autoImplicit false

/-- Sorting is a computable canonical enumeration of the finite set. -/
def natSetStream : StreamCodec (Finset Nat) :=
  StreamCodec.xmap (StreamCodec.list StreamCodec.nat)
    (fun values => values.sort (· ≤ ·)) List.toFinset
    (by intro values; exact Finset.sort_toFinset _ _)

/-- Transport a sorted finite set along a concrete, total retraction.
Invalid natural labels may decode provisionally; exact whole-page re-encoding
rejects them before they become materialized authority. -/
def labeledSetStream {alpha : Type} [DecidableEq alpha]
    (label : alpha → Nat) (ofLabel : Nat → alpha)
    (roundtrip : ∀ value, ofLabel (label value) = value) :
    StreamCodec (Finset alpha) :=
  StreamCodec.xmap natSetStream (Finset.image label) (Finset.image ofLabel)
    (by
      intro values
      rw [Finset.image_image]
      simpa only [Function.comp_def, roundtrip] using
        (Finset.image_id : Finset.image _root_.id values = values))

def capabilityIdStream : StreamCodec CapabilityId :=
  StreamCodec.xmap StreamCodec.nat CapabilityId.value CapabilityId.mk
    (by intro value; cases value; rfl)

def issuerIdStream : StreamCodec IssuerId :=
  StreamCodec.xmap StreamCodec.nat IssuerId.value IssuerId.mk
    (by intro value; cases value; rfl)

def channelIdStream : StreamCodec ChannelId :=
  StreamCodec.xmap StreamCodec.nat ChannelId.value ChannelId.mk
    (by intro value; cases value; rfl)

def capabilitySetStream : StreamCodec (Finset CapabilityId) :=
  labeledSetStream CapabilityId.value CapabilityId.mk
    (by intro value; cases value; rfl)

def channelSetStream : StreamCodec (Finset ChannelId) :=
  labeledSetStream ChannelId.value ChannelId.mk
    (by intro value; cases value; rfl)

def resourceSetStream (kind : ResourceKind) :
    StreamCodec (Finset (ResourceId kind)) :=
  labeledSetStream ResourceId.value ResourceId.mk
    (by intro value; cases value; rfl)

def verbTag : {kind : ResourceKind} → Verb kind → Nat
  | _, .observeObject => 1
  | _, .mutateObject => 2
  | _, .delegateObject => 3
  | _, .observeAccount => 1
  | _, .transfer => 2
  | _, .delegateAccount => 3
  | _, .observeProgram => 1
  | _, .installProgram => 2
  | _, .delegateProgram => 3
  | _, .installPolicy => 4
  | _, .revokeCapability => 5

def verbOfTag : (kind : ResourceKind) → Nat → Verb kind
  | .object, 1 => .observeObject
  | .object, 2 => .mutateObject
  | .object, _ => .delegateObject
  | .account, 1 => .observeAccount
  | .account, 2 => .transfer
  | .account, _ => .delegateAccount
  | .program, 1 => .observeProgram
  | .program, 2 => .installProgram
  | .program, 4 => .installPolicy
  | .program, 5 => .revokeCapability
  | .program, _ => .delegateProgram

theorem verbOfTag_tag {kind : ResourceKind} (verb : Verb kind) :
    verbOfTag kind (verbTag verb) = verb := by
  cases verb <;> rfl

def verbSetStream (kind : ResourceKind) : StreamCodec (Finset (Verb kind)) :=
  labeledSetStream verbTag (verbOfTag kind) verbOfTag_tag

def holderStream : StreamCodec Holder where
  encode
    | .bearer => [0]
    | .subject subject => 1 :: subjectIdStream.encode subject
  decodePrefix
    | 0 :: suffix => some (.bearer, suffix)
    | 1 :: bytes => do
        let (subject, suffix) ← subjectIdStream.decodePrefix bytes
        some (.subject subject, suffix)
    | _ => none
  decodePrefix_encode := by
    intro holder suffix
    cases holder with
    | bearer => rfl
    | subject subject => simp [subjectIdStream.decodePrefix_encode]

abbrev ScopeTuple (kind : ResourceKind) :=
  Finset (ResourceId kind) × Finset (Verb kind) × Nat

def scopeTupleStream (kind : ResourceKind) : StreamCodec (ScopeTuple kind) :=
  StreamCodec.product (resourceSetStream kind)
    (StreamCodec.product (verbSetStream kind) StreamCodec.nat)

def scopeTuple {kind : ResourceKind} (scope : Scope kind) : ScopeTuple kind :=
  (scope.targets, scope.verbs, scope.maxCost)

def scopeOfTuple {kind : ResourceKind} (tuple : ScopeTuple kind) : Scope kind :=
  ⟨tuple.1, tuple.2.1, tuple.2.2⟩

def scopeStream (kind : ResourceKind) : StreamCodec (Scope kind) :=
  StreamCodec.xmap (scopeTupleStream kind) scopeTuple scopeOfTuple
    (by intro scope; rfl)

abbrev CapabilityTuple (kind : ResourceKind) :=
  CapabilityId × CapabilityId × Option CapabilityId × IssuerId × Holder ×
    Scope kind × Nat × Nat × Nat × PolicyId × Nat × Finset CapabilityId ×
    Finset ChannelId

def capabilityTupleStream (kind : ResourceKind) :
    StreamCodec (CapabilityTuple kind) :=
  StreamCodec.product capabilityIdStream
    (StreamCodec.product capabilityIdStream
      (StreamCodec.product (StreamCodec.option capabilityIdStream)
        (StreamCodec.product issuerIdStream
          (StreamCodec.product holderStream
            (StreamCodec.product (scopeStream kind)
              (StreamCodec.product StreamCodec.nat
                (StreamCodec.product StreamCodec.nat
                  (StreamCodec.product StreamCodec.nat
                    (StreamCodec.product policyIdStream
                      (StreamCodec.product StreamCodec.nat
                        (StreamCodec.product capabilitySetStream
                          channelSetStream)))))))))))

def capabilityTuple {kind : ResourceKind} (cap : Capability kind) :
    CapabilityTuple kind :=
  ⟨cap.id, cap.root, cap.parent, cap.issuer, cap.holder, cap.scope,
    cap.notBefore, cap.notAfter, cap.issuerEpoch, cap.policyId,
    cap.policyEpoch, cap.ancestors, cap.channels⟩

def capabilityOfTuple {kind : ResourceKind} (tuple : CapabilityTuple kind) :
    Capability kind where
  id := tuple.1
  root := tuple.2.1
  parent := tuple.2.2.1
  issuer := tuple.2.2.2.1
  holder := tuple.2.2.2.2.1
  scope := tuple.2.2.2.2.2.1
  notBefore := tuple.2.2.2.2.2.2.1
  notAfter := tuple.2.2.2.2.2.2.2.1
  issuerEpoch := tuple.2.2.2.2.2.2.2.2.1
  policyId := tuple.2.2.2.2.2.2.2.2.2.1
  policyEpoch := tuple.2.2.2.2.2.2.2.2.2.2.1
  ancestors := tuple.2.2.2.2.2.2.2.2.2.2.2.1
  channels := tuple.2.2.2.2.2.2.2.2.2.2.2.2

theorem capabilityOfTuple_tuple {kind : ResourceKind} (cap : Capability kind) :
    capabilityOfTuple (capabilityTuple cap) = cap := rfl

def capabilityStream (kind : ResourceKind) : StreamCodec (Capability kind) :=
  StreamCodec.xmap (capabilityTupleStream kind) capabilityTuple capabilityOfTuple
    capabilityOfTuple_tuple

/-- Exact origin data. A delegated request is historical source data, not
an authorization certificate; the effect family owns its creation proof. -/
def lineageOriginStream (kind : ResourceKind) : StreamCodec (LineageOrigin kind) where
  encode
    | .strict => [0]
    | .delegated request => 1 :: (requestStreamFor kind).encode request
  decodePrefix
    | 0 :: suffix => some (.strict, suffix)
    | 1 :: bytes => do
        let (request, suffix) ← (requestStreamFor kind).decodePrefix bytes
        some (.delegated request, suffix)
    | _ => none
  decodePrefix_encode := by
    intro origin suffix
    cases origin with
    | strict => rfl
    | delegated request => simp [(requestStreamFor kind).decodePrefix_encode]

def parentLinkStream (kind : ResourceKind) : StreamCodec (ParentLink kind) :=
  StreamCodec.xmap
    (StreamCodec.product (capabilityStream kind) (lineageOriginStream kind))
    (fun link => (link.parent, link.origin))
    (fun pair => ⟨pair.1, pair.2⟩)
    (by intro link; rfl)

def storedCapabilityStream (kind : ResourceKind) :
    StreamCodec (StoredCapability kind) :=
  StreamCodec.xmap
    (StreamCodec.product (capabilityStream kind)
      (StreamCodec.list (parentLinkStream kind)))
    (fun stored => (stored.head, stored.ancestry))
    (fun tuple => ⟨tuple.1, tuple.2⟩)
    (by intro stored; rfl)

/-- Origin tags never conflate a strict step with an explicit delegated step. -/
theorem lineage_origin_tags_separate (kind : ResourceKind) (request : Request kind) :
    (lineageOriginStream kind).encode .strict ≠
      (lineageOriginStream kind).encode (.delegated request) := by
  simp [lineageOriginStream]

/-- Retaining the resource-kind coordinate rejects a request transplanted
from a different kind, even inside an otherwise valid lineage record. -/
theorem lineage_origin_wrong_request_kind {actual expected : ResourceKind}
    (request : Request actual) (suffix : List UInt8) (different : actual ≠ expected) :
    (lineageOriginStream expected).decodePrefix
      (1 :: (someRequestStream.encode ⟨actual, request⟩ ++ suffix)) = none := by
  simp [lineageOriginStream, requestStreamFor_wrong_kind request suffix different]

/-- Every field of the capability, including lineage, survives transport. -/
theorem storedCapability_roundtrip (kind : ResourceKind)
    (stored : StoredCapability kind) (suffix : List UInt8) :
    (storedCapabilityStream kind).decodePrefix
        ((storedCapabilityStream kind).encode stored ++ suffix) =
      some (stored, suffix) :=
  (storedCapabilityStream kind).decodePrefix_encode stored suffix

/-- Changing a holder or any lineage detail changes the bytes: this is a
universal separation theorem, not a golden vector. -/
theorem storedCapability_encode_injective (kind : ResourceKind) :
    Function.Injective (storedCapabilityStream kind).encode := by
  intro left right equal
  have decoded := congrArg (storedCapabilityStream kind).toLawful.decode equal
  change (storedCapabilityStream kind).toLawful.decode
      ((storedCapabilityStream kind).toLawful.encode left) =
    (storedCapabilityStream kind).toLawful.decode
      ((storedCapabilityStream kind).toLawful.encode right) at decoded
  rw [(storedCapabilityStream kind).toLawful.decode_encode,
    (storedCapabilityStream kind).toLawful.decode_encode] at decoded
  exact Option.some.inj decoded

/-- A diagnostic representation uses the same computable exact encoding;
it does not invoke the noncomputable/unsafe `Finset` printer. -/
instance (kind : ResourceKind) : Repr (StoredCapability kind) where
  reprPrec stored precedence :=
    reprPrec ((storedCapabilityStream kind).encode stored) precedence

/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.storedCapability_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storedCapability_roundtrip
/-- info: 'Minidregg.Compiler.CredentialAuthorityEntryCodec.storedCapability_encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms storedCapability_encode_injective

end Minidregg.Compiler.CredentialAuthorityEntryCodec
