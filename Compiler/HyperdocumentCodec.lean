/-
# Compiler.HyperdocumentCodec -- the Hyperdocument value types, on the wire

`HyperdocumentOperations.Config` demands `LawfulCodec Action` and
`LawfulCodec Declaration`.  `Compiler.TypedAuthorizationRequestCodec` supplied
the third, `LawfulCodec (Request .object)`; this file walks the type tree the
first two need.

Everything rides `Tower256ConcreteBackend.StreamCodec`, whose append law makes
sequential composition delimiter-free, so each codec below is `xmap` over a
tag, `product` over a record, `sum`/tagged dispatch over an inductive, or
`list`/`option`/`finset` over a container.  No type here is recursive --
`ElementBody.container` holds a list of `ElementId`, not of `ElementBody` -- so
the walk is flat.

None of this is a deployment wire format.  `StreamCodec.finset` is
noncomputable because `Finset.toList` is, and a deployed transclusion reference
would carry an explicitly ordered field rather than a set.
-/
import Compiler.TypedAuthorizationRequestCodec
import Theory.StableRanges

namespace Minidregg.Compiler.HyperdocumentCodec

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.TypedAuthorizationRequestCodec
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest ResourceKind CapabilityId SubjectId)

set_option autoImplicit false

/-! ## Identifiers

Every semantic identifier is a `Digest` under a phantom version/domain index,
so one codec serves them all. -/

def identifierStream (version : CodecVersion) (domain : IdDomain) :
    StreamCodec (Identifier version domain) :=
  StreamCodec.xmap digestStream Identifier.digest Identifier.mk
    (by intro value; cases value; rfl)

def capabilityIdStream : StreamCodec CapabilityId :=
  StreamCodec.xmap StreamCodec.nat CapabilityId.value CapabilityId.mk
    (by intro value; cases value; rfl)

/-! ## Finite tags -/

def resourceKindTag : ResourceKind -> Nat
  | .object => 1
  | .account => 2
  | .program => 3

def resourceKindOfTag : Nat -> ResourceKind
  | 1 => .object
  | 2 => .account
  | _ => .program

def resourceKindStream : StreamCodec ResourceKind :=
  StreamCodec.xmap StreamCodec.nat resourceKindTag resourceKindOfTag
    (by intro value; cases value <;> rfl)

def transclusionModeTag : TransclusionMode -> Nat
  | .snapshot => 0
  | .live => 1

def transclusionModeOfTag : Nat -> TransclusionMode
  | 0 => .snapshot
  | _ => .live

def transclusionModeStream : StreamCodec TransclusionMode :=
  StreamCodec.xmap StreamCodec.nat transclusionModeTag transclusionModeOfTag
    (by intro value; cases value <;> rfl)

def openingShapeTag : StoredOpeningShape -> Nat
  | .value => 0
  | .range => 1

def openingShapeOfTag : Nat -> StoredOpeningShape
  | 0 => .value
  | _ => .range

def openingShapeStream : StreamCodec StoredOpeningShape :=
  StreamCodec.xmap StreamCodec.nat openingShapeTag openingShapeOfTag
    (by intro value; cases value <;> rfl)

def deathPolicyTag : EndpointDeathPolicy -> Nat
  | .invalidate => 0
  | .keepTombstone => 1
  | .preferPrevious => 2
  | .preferNext => 3
  | .preferPreviousThenNext => 4
  | .preferNextThenPrevious => 5

def deathPolicyOfTag : Nat -> EndpointDeathPolicy
  | 0 => .invalidate
  | 1 => .keepTombstone
  | 2 => .preferPrevious
  | 3 => .preferNext
  | 4 => .preferPreviousThenNext
  | _ => .preferNextThenPrevious

def deathPolicyStream : StreamCodec EndpointDeathPolicy :=
  StreamCodec.xmap StreamCodec.nat deathPolicyTag deathPolicyOfTag
    (by intro value; cases value <;> rfl)

/-! ## Small records -/

def principalRefStream : StreamCodec PrincipalRef :=
  StreamCodec.xmap
    (StreamCodec.product subjectIdStream
      (StreamCodec.product resourceKindStream capabilityIdStream))
    (fun value => (value.subject, value.capabilityKind, value.capabilityId))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro value; rfl)

def disclosureAtomStream : StreamCodec DisclosureAtom :=
  StreamCodec.xmap (StreamCodec.product digestStream bytesStream)
    (fun value => (value.namespaceId, value.payload))
    (fun tuple => ⟨tuple.1, tuple.2⟩)
    (by intro value; rfl)

def storedSourceIdentityStream : StreamCodec StoredSourceIdentity :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream digestStream)))
    (fun value => (value.historyDomain, value.objectRoot, value.historyEntryRoot,
      value.semanticRoot))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; rfl)

def openingDescriptorStream : StreamCodec OpeningDescriptor :=
  StreamCodec.xmap
    (StreamCodec.product openingShapeStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product bytesStream digestStream))))
    (fun value => (value.shape, value.openingCodecId, value.openingRelationId,
      value.canonicalDescriptor, value.openingCommitment))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1,
      tuple.2.2.2.2⟩)
    (by intro value; rfl)

noncomputable def storedTransclusionRefStream : StreamCodec StoredTransclusionRef :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product storedSourceIdentityStream
        (StreamCodec.product openingDescriptorStream
          (StreamCodec.product transclusionModeStream
            (StreamCodec.product (StreamCodec.finset disclosureAtomStream)
              (StreamCodec.finset disclosureAtomStream))))))
    (fun value => (value.referenceRoot, value.source, value.opening, value.mode,
      value.disclosureScope, value.capabilityCeiling))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1,
      tuple.2.2.2.2.1, tuple.2.2.2.2.2⟩)
    (by intro value; rfl)

/-! ## Content bodies -/

def atomKindTag : AtomKind -> Nat
  | .text => 0
  | .inlineObject _ => 1

def atomKindPayload : AtomKind -> List UInt8
  | .text => []
  | .inlineObject schema => digestStream.encode schema

def atomKindStream : StreamCodec AtomKind where
  encode value := StreamCodec.nat.encode (atomKindTag value) ++ atomKindPayload value
  decodePrefix bytes := do
    let (tag, afterTag) ← StreamCodec.nat.decodePrefix bytes
    match tag with
    | 0 => some (.text, afterTag)
    | _ => do
        let (schema, suffix) ← digestStream.decodePrefix afterTag
        some (.inlineObject schema, suffix)
  decodePrefix_encode := by
    intro value suffix
    cases value with
    | text => simp [atomKindTag, atomKindPayload, StreamCodec.nat.decodePrefix_encode]
    | inlineObject schema =>
        simp [atomKindTag, atomKindPayload, List.append_assoc,
          StreamCodec.nat.decodePrefix_encode, digestStream.decodePrefix_encode]

def atomRecordStream : StreamCodec AtomRecord :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product atomKindStream
        (StreamCodec.product bytesStream
          (StreamCodec.product principalRefStream
            (StreamCodec.product (identifierStream .v1 .operationIntent)
              (StreamCodec.option (identifierStream .v1 .operationIntent)))))))
    (fun value => (value.document, value.kind, value.payload, value.createdBy,
      value.createdAt, value.tombstonedAt))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1,
      tuple.2.2.2.2.1, tuple.2.2.2.2.2⟩)
    (by intro value; rfl)

def embedRefStream : StreamCodec EmbedRef :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .document)
      (StreamCodec.product (StreamCodec.option (identifierStream .v1 .element))
        (StreamCodec.option (identifierStream .v1 .versionEvent))))
    (fun value => (value.document, value.element, value.snapshot))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro value; rfl)

/-! ## Stored stable ranges

`Hyperdocument.StableRange` is the canonical stored/wire shape; the operational
`StableRanges.StableRange` below is the adapter's view of the same thing. Both
get codecs because both appear in payloads. -/

def anchorBiasTag : AnchorBias -> Nat
  | .before => 0
  | .after => 1

def anchorBiasOfTag : Nat -> AnchorBias
  | 0 => .before
  | _ => .after

def anchorBiasStream : StreamCodec AnchorBias :=
  StreamCodec.xmap StreamCodec.nat anchorBiasTag anchorBiasOfTag
    (by intro value; cases value <;> rfl)

def stablePointStream : StreamCodec StablePoint :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .run)
      (StreamCodec.product (StreamCodec.option (identifierStream .v1 .atom))
        (StreamCodec.product anchorBiasStream deathPolicyStream)))
    (fun value => (value.run, value.neighbor, value.bias, value.death))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro value; rfl)

def storedStableRangeStream : StreamCodec StableRange :=
  StreamCodec.xmap (StreamCodec.product stablePointStream stablePointStream)
    (fun value => (value.start, value.finish))
    (fun tuple => ⟨tuple.1, tuple.2⟩)
    (by intro value; rfl)

/-! ## Element bodies and link targets

The two multi-way unions.  Both are written longhand rather than through
`sum`, which would nest spuriously and force `Unit` payloads on the arms that
carry nothing. -/

def elementBodyTag : ElementBody -> Nat
  | .container _ => 0
  | .runs _ => 1
  | .embed _ => 2
  | .opaque _ _ => 3

def elementBodyStream : StreamCodec ElementBody where
  encode value :=
    StreamCodec.nat.encode (elementBodyTag value) ++
      match value with
      | .container children =>
          (StreamCodec.list (identifierStream .v1 .element)).encode children
      | .runs runs => (StreamCodec.list (identifierStream .v1 .run)).encode runs
      | .embed reference => embedRefStream.encode reference
      | .opaque schema payload =>
          digestStream.encode schema ++ bytesStream.encode payload
  decodePrefix bytes := do
    let (tag, afterTag) ← StreamCodec.nat.decodePrefix bytes
    match tag with
    | 0 => do
        let (children, suffix) ←
          (StreamCodec.list (identifierStream .v1 .element)).decodePrefix afterTag
        some (.container children, suffix)
    | 1 => do
        let (runs, suffix) ←
          (StreamCodec.list (identifierStream .v1 .run)).decodePrefix afterTag
        some (.runs runs, suffix)
    | 2 => do
        let (reference, suffix) ← embedRefStream.decodePrefix afterTag
        some (.embed reference, suffix)
    | _ => do
        let (schema, afterSchema) ← digestStream.decodePrefix afterTag
        let (payload, suffix) ← bytesStream.decodePrefix afterSchema
        some (.opaque schema payload, suffix)
  decodePrefix_encode := by
    intro value suffix
    cases value <;>
      simp [elementBodyTag, List.append_assoc,
        StreamCodec.nat.decodePrefix_encode,
        (StreamCodec.list (identifierStream .v1 .element)).decodePrefix_encode,
        (StreamCodec.list (identifierStream .v1 .run)).decodePrefix_encode,
        embedRefStream.decodePrefix_encode, digestStream.decodePrefix_encode,
        bytesStream.decodePrefix_encode]

def linkTargetTag : LinkTarget -> Nat
  | .document _ => 0
  | .element _ => 1
  | .range _ _ => 2
  | .transclusion _ _ => 3
  | .external _ _ _ => 4

noncomputable def linkTargetStream : StreamCodec LinkTarget where
  encode value :=
    StreamCodec.nat.encode (linkTargetTag value) ++
      match value with
      | .document target => (identifierStream .v1 .document).encode target
      | .element target => (identifierStream .v1 .element).encode target
      | .range document range =>
          (identifierStream .v1 .document).encode document ++
            storedStableRangeStream.encode range
      | .transclusion target reference =>
          (identifierStream .v1 .transclusion).encode target ++
            storedTransclusionRefStream.encode reference
      | .external scheme authority path =>
          bytesStream.encode scheme ++ bytesStream.encode authority ++
            bytesStream.encode path
  decodePrefix bytes := do
    let (tag, afterTag) ← StreamCodec.nat.decodePrefix bytes
    match tag with
    | 0 => do
        let (target, suffix) ←
          (identifierStream .v1 .document).decodePrefix afterTag
        some (.document target, suffix)
    | 1 => do
        let (target, suffix) ←
          (identifierStream .v1 .element).decodePrefix afterTag
        some (.element target, suffix)
    | 2 => do
        let (document, afterDocument) ←
          (identifierStream .v1 .document).decodePrefix afterTag
        let (range, suffix) ← storedStableRangeStream.decodePrefix afterDocument
        some (.range document range, suffix)
    | 3 => do
        let (target, afterTarget) ←
          (identifierStream .v1 .transclusion).decodePrefix afterTag
        let (reference, suffix) ←
          storedTransclusionRefStream.decodePrefix afterTarget
        some (.transclusion target reference, suffix)
    | _ => do
        let (scheme, afterScheme) ← bytesStream.decodePrefix afterTag
        let (authority, afterAuthority) ← bytesStream.decodePrefix afterScheme
        let (path, suffix) ← bytesStream.decodePrefix afterAuthority
        some (.external scheme authority path, suffix)
  decodePrefix_encode := by
    intro value suffix
    cases value <;>
      simp [linkTargetTag, List.append_assoc,
        StreamCodec.nat.decodePrefix_encode,
        (identifierStream .v1 .document).decodePrefix_encode,
        (identifierStream .v1 .element).decodePrefix_encode,
        (identifierStream .v1 .transclusion).decodePrefix_encode,
        storedStableRangeStream.decodePrefix_encode,
        storedTransclusionRefStream.decodePrefix_encode,
        bytesStream.decodePrefix_encode]

/-! ## Operational stable ranges -/

open Minidregg.Theory.StableRanges in
def locationStream : StreamCodec (Location RunId AtomId) :=
  StreamCodec.xmap
    (StreamCodec.product (identifierStream .v1 .run)
      (identifierStream .v1 .atom))
    (fun value => (value.run, value.atom))
    (fun tuple => ⟨tuple.1, tuple.2⟩)
    (by intro value; rfl)

open Minidregg.Theory.StableRanges in
def sideStream : StreamCodec Side :=
  StreamCodec.xmap StreamCodec.nat
    (fun value => match value with | .before => 0 | .after => 1)
    (fun tag => match tag with | 0 => .before | _ => .after)
    (by intro value; cases value <;> rfl)

open Minidregg.Theory.StableRanges in
def endpointStream : StreamCodec (Endpoint RunId AtomId) :=
  StreamCodec.xmap
    (StreamCodec.product locationStream
      (StreamCodec.product sideStream deathPolicyStream))
    (fun value => (value.location, value.side, value.onDeath))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2⟩)
    (by intro value; rfl)

open Minidregg.Theory.StableRanges in
def stableRangeStream : StreamCodec (StableRange RunId AtomId) :=
  StreamCodec.xmap (StreamCodec.product endpointStream endpointStream)
    (fun value => (value.start, value.stop))
    (fun tuple => ⟨tuple.1, tuple.2⟩)
    (by intro value; rfl)

end Minidregg.Compiler.HyperdocumentCodec
