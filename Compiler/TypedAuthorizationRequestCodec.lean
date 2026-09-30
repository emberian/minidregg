/-
# Compiler.TypedAuthorizationRequestCodec — one complete canonical request codec

All request consumers use the source-owned RequestWire projection, including
resource kind and explicit policy revision. Typed and existential codecs share
this one representation. Exact prefix re-encoding rejects noncanonical natural
spellings; kind mismatch and omitted revision are refused, never defaulted.
-/
import Compiler.Tower256ConcreteBackend
import Theory.AuthorizationDeclaration

namespace Minidregg.Compiler.TypedAuthorizationRequestCodec

open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration

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

/-- Pure wire projection is source-owned so lower backend manifests cannot
create an import cycle through this concrete byte codec. -/
abbrev requestWords := Minidregg.Theory.AuthorizationDeclaration.requestWords
abbrev requestWordCount := Minidregg.Theory.AuthorizationDeclaration.requestWordCount
abbrev requestWireOfWords := Minidregg.Theory.AuthorizationDeclaration.requestWireOfWords
abbrev requestWireOfWords_requestWords :=
  Minidregg.Theory.AuthorizationDeclaration.requestWireOfWords_requestWords
abbrev requestWireOfWords_exact :=
  @Minidregg.Theory.AuthorizationDeclaration.requestWireOfWords_exact
abbrev requestWords_injective :=
  Minidregg.Theory.AuthorizationDeclaration.requestWords_injective

/-- The exact consumed prefix is checked without needing value equality. -/
private def canonicalStream {α : Type} (codec : StreamCodec α) : StreamCodec α where
  encode := codec.encode
  decodePrefix bytes :=
    match codec.decodePrefix bytes with
    | none => none
    | some (value, suffix) =>
      if bytes = codec.encode value ++ suffix then some (value, suffix) else none
  decodePrefix_encode := by
    intro value suffix
    simp [codec.decodePrefix_encode]

private theorem canonicalStream_exact {α : Type} (codec : StreamCodec α)
    {bytes suffix : List UInt8} {value : α}
    (decoded : (canonicalStream codec).decodePrefix bytes = some (value, suffix)) :
    bytes = (canonicalStream codec).encode value ++ suffix := by
  cases parsed : codec.decodePrefix bytes with
  | none => simp [canonicalStream, parsed] at decoded
  | some pair =>
    rcases pair with ⟨actual, rest⟩
    simp only [canonicalStream, parsed] at decoded
    split at decoded
    next exactBytes =>
      cases Option.some.inj decoded
      exact exactBytes
    next => contradiction

private theorem canonicalStream_whole {α : Type} (codec : StreamCodec α)
    {bytes : List UInt8} {value : α}
    (decoded : (canonicalStream codec).toLawful.decode bytes = some value) :
    (canonicalStream codec).encode value = bytes := by
  unfold StreamCodec.toLawful at decoded
  cases parsed : (canonicalStream codec).decodePrefix bytes with
  | none => simp [parsed] at decoded
  | some pair =>
    rcases pair with ⟨actual, rest⟩
    simp only [parsed] at decoded
    change (if rest = [] then some actual else none) = some value at decoded
    split at decoded
    next empty =>
      have same : actual = value := Option.some.inj decoded
      subst actual
      have exactBytes := canonicalStream_exact codec parsed
      simpa only [empty, List.append_nil] using exactBytes.symm
    next => contradiction

private def rawRequestWireStream : StreamCodec RequestWire where
  encode request := (StreamCodec.list StreamCodec.nat).encode (requestWords request)
  decodePrefix bytes := do
    let (count, afterCount) ← StreamCodec.nat.decodePrefix bytes
    if count = requestWordCount then
      let (words, suffix) ← StreamCodec.decodeMany StreamCodec.nat count afterCount
      let request ← requestWireOfWords words
      some (request, suffix)
    else none
  decodePrefix_encode := by
    intro request suffix
    simp [StreamCodec.list, List.append_assoc,
      StreamCodec.nat.decodePrefix_encode, requestWords, requestWordCount,
      requestFieldOrder, StreamCodec.encodeMany, StreamCodec.decodeMany,
      requestWireOfWords, Minidregg.Theory.AuthorizationDeclaration.requestWords,
      Minidregg.Theory.AuthorizationDeclaration.requestWordCount,
      Minidregg.Theory.AuthorizationDeclaration.requestWireOfWords]

def requestWireStream : StreamCodec RequestWire := canonicalStream rawRequestWireStream

theorem requestWireStream_wrong_count (count : Nat) (payload : List UInt8)
    (wrong : count ≠ requestWordCount) :
    requestWireStream.decodePrefix (StreamCodec.nat.encode count ++ payload) = none := by
  simp [requestWireStream, canonicalStream, rawRequestWireStream,
    StreamCodec.nat.decodePrefix_encode, wrong]

/-- The preceding request vocabulary cannot acquire a fabricated zero revision. -/
theorem requestWireStream_rejects_omitted_revision (payload : List UInt8) :
    requestWireStream.decodePrefix (StreamCodec.nat.encode 16 ++ payload) = none :=
  requestWireStream_wrong_count 16 payload (by decide)

def requestWireCodec : LawfulCodec RequestWire := requestWireStream.toLawful

theorem requestWireStream_canonical {bytes suffix : List UInt8} {request : RequestWire}
    (decoded : requestWireStream.decodePrefix bytes = some (request, suffix)) :
    bytes = requestWireStream.encode request ++ suffix :=
  canonicalStream_exact rawRequestWireStream decoded

theorem requestWireCodec_canonical {bytes : List UInt8} {request : RequestWire}
    (decoded : requestWireCodec.decode bytes = some request) :
    requestWireCodec.encode request = bytes :=
  canonicalStream_whole rawRequestWireStream decoded

private def rawSomeRequestStream : StreamCodec SomeRequest where
  encode request := requestWireStream.encode (encodeRequest request)
  decodePrefix bytes := do
    let (wire, suffix) ← requestWireStream.decodePrefix bytes
    let request ← decodeRequest wire
    some (request, suffix)
  decodePrefix_encode := by
    intro request suffix
    simp [requestWireStream.decodePrefix_encode, decodeRequest_encodeRequest]

def someRequestStream : StreamCodec SomeRequest := canonicalStream rawSomeRequestStream

def someRequestCodec : LawfulCodec SomeRequest := someRequestStream.toLawful

theorem someRequestStream_canonical {bytes suffix : List UInt8} {request : SomeRequest}
    (decoded : someRequestStream.decodePrefix bytes = some (request, suffix)) :
    bytes = someRequestStream.encode request ++ suffix :=
  canonicalStream_exact rawSomeRequestStream decoded

theorem someRequestCodec_canonical {bytes : List UInt8} {request : SomeRequest}
    (decoded : someRequestCodec.decode bytes = some request) :
    someRequestCodec.encode request = bytes :=
  canonicalStream_whole rawSomeRequestStream decoded

theorem someRequestStream_rejects_wire (wire : RequestWire) (suffix : List UInt8)
    (invalid : decodeRequest wire = none) :
    someRequestStream.decodePrefix (requestWireStream.encode wire ++ suffix) = none := by
  simp [someRequestStream, canonicalStream, rawSomeRequestStream,
    requestWireStream.decodePrefix_encode, invalid]

private def rawRequestStreamFor (kind : ResourceKind) : StreamCodec (Request kind) where
  encode request := someRequestStream.encode ⟨kind, request⟩
  decodePrefix bytes := do
    let (⟨actualKind, request⟩, suffix) ← someRequestStream.decodePrefix bytes
    if same : actualKind = kind then some (same ▸ request, suffix) else none
  decodePrefix_encode := by
    intro request suffix
    simp [someRequestStream.decodePrefix_encode]

def requestStreamFor (kind : ResourceKind) : StreamCodec (Request kind) :=
  canonicalStream (rawRequestStreamFor kind)

def requestCodecFor (kind : ResourceKind) : LawfulCodec (Request kind) :=
  (requestStreamFor kind).toLawful

theorem requestStreamFor_canonical (kind : ResourceKind)
    {bytes suffix : List UInt8} {request : Request kind}
    (decoded : (requestStreamFor kind).decodePrefix bytes = some (request, suffix)) :
    bytes = (requestStreamFor kind).encode request ++ suffix :=
  canonicalStream_exact (rawRequestStreamFor kind) decoded

theorem requestCodecFor_canonical (kind : ResourceKind)
    {bytes : List UInt8} {request : Request kind}
    (decoded : (requestCodecFor kind).decode bytes = some request) :
    (requestCodecFor kind).encode request = bytes :=
  canonicalStream_whole (rawRequestStreamFor kind) decoded

theorem requestStreamFor_wrong_kind {actual expected : ResourceKind}
    (request : Request actual) (suffix : List UInt8) (different : actual ≠ expected) :
    (requestStreamFor expected).decodePrefix
      (someRequestStream.encode ⟨actual, request⟩ ++ suffix) = none := by
  simp [requestStreamFor, canonicalStream, rawRequestStreamFor,
    someRequestStream.decodePrefix_encode, different]

abbrev requestCodecVersion := Minidregg.Theory.AuthorizationDeclaration.requestCodecVersion

/-- The signed frame is the PLAN frame: a signature over the old whole-request
frame (`DREGG/AUTH/REQUEST`) does not verify against it. -/
def requestFrame : List UInt8 :=
  "DREGG/AUTH/PLAN".toUTF8.toList ++ [UInt8.ofNat requestCodecVersion]

/-- The request as a plan signs it.  `height` is the admission clock and
`preStateRoot` is the kernel's own pre-root of the leg's cell
(`MultiCellHyperedge.PreparedTuple.requestRoots` derives it from the validated
patch); neither is the signer's to bind.  Signing them bound every plan to the
exact journal length and to the whole root of every cell it touched, so any
commit anywhere invalidated every pending plan.  A plan bounds the clock with
the signed header's `validUntil` and states what it read at address level: a
command's per-cell `expectedTargetRoot` for a cell it reads whole, and the
header's authority footprint (`Theory.PlanBinding`).  The two words are encoded
as zero. -/
def planOf (request : SomeRequest) : SomeRequest :=
  ⟨request.1, { request.2 with height := 0, preStateRoot := ⟨0⟩ }⟩

def signedRequestBytes (request : SomeRequest) : List UInt8 :=
  requestFrame ++ someRequestStream.encode (planOf request)

theorem signedRequestBytes_exact (request : SomeRequest) :
    signedRequestBytes request =
      ("DREGG/AUTH/PLAN".toUTF8.toList ++ [2]) ++
        (StreamCodec.list StreamCodec.nat).encode
          (requestWords (encodeRequest (planOf request))) := rfl

/-- The signed bytes determine exactly the plan: every request field except the
admission clock and the kernel-derived pre-root. -/
theorem signedRequestBytes_eq_iff (left right : SomeRequest) :
    signedRequestBytes left = signedRequestBytes right ↔ planOf left = planOf right := by
  constructor
  · intro same
    have samePayload : someRequestCodec.encode (planOf left) =
        someRequestCodec.encode (planOf right) :=
      List.append_cancel_left same
    have decoded := congrArg someRequestCodec.decode samePayload
    simpa only [someRequestCodec.decode_encode, Option.some.injEq] using decoded
  · intro same
    unfold signedRequestBytes
    rw [same]

/-- Satisfied pole: a plan signed at one height and pre-root is the same signed
plan at any other. -/
theorem signedRequestBytes_clock_free {kind : ResourceKind} (request : Request kind)
    (height : Height) (root : Digest) :
    signedRequestBytes ⟨kind, { request with height := height, preStateRoot := root }⟩ =
      signedRequestBytes ⟨kind, request⟩ := rfl

/-- Refuted pole: every plan field is still bound; two requests whose plans
differ sign different bytes. -/
theorem signedRequestBytes_separates_plan {left right : SomeRequest}
    (different : planOf left ≠ planOf right) :
    signedRequestBytes left ≠ signedRequestBytes right :=
  fun same => different ((signedRequestBytes_eq_iff left right).1 same)

#print axioms requestWireOfWords_exact
#print axioms requestWords_injective
#print axioms requestWireCodec_canonical
#print axioms someRequestCodec_canonical
#print axioms requestCodecFor_canonical
#print axioms requestStreamFor_wrong_kind
#print axioms signedRequestBytes_exact
#print axioms signedRequestBytes_eq_iff
#print axioms signedRequestBytes_clock_free


private theorem resourceKindTag_of_decoded {tag : Nat} {kind : ResourceKind}
    (decoded : decodeResourceKind tag = some kind) : resourceKindTag kind = tag := by
  cases kind <;> unfold decodeResourceKind at decoded <;>
    split at decoded <;> simp_all [resourceKindTag]

private theorem verbTag_of_decoded {kind : ResourceKind} {tag : Nat} {verb : Verb kind}
    (decoded : decodeVerb kind tag = some verb) :
    Minidregg.Theory.AuthorizationDeclaration.verbTag verb = tag := by
  fun_cases decodeVerb kind tag <;>
    grind +lax [decodeVerb, Minidregg.Theory.AuthorizationDeclaration.verbTag]

theorem encodeRequest_of_decodeRequest {wire : RequestWire} {request : SomeRequest}
    (decoded : decodeRequest wire = some request) : encodeRequest request = wire := by
  unfold decodeRequest at decoded
  cases kindDecoded : decodeResourceKind wire.resourceKind with
  | none => simp [kindDecoded] at decoded
  | some kind =>
    cases verbDecoded : decodeVerb kind wire.verb with
    | none => simp [kindDecoded, verbDecoded] at decoded
    | some verb =>
      simp only [kindDecoded, bind, Option.bind, verbDecoded] at decoded
      cases Option.some.inj decoded
      have kindExact := resourceKindTag_of_decoded kindDecoded
      have verbExact := verbTag_of_decoded verbDecoded
      cases wire
      simp_all [encodeRequest]


#print axioms encodeRequest_of_decodeRequest

/-- Object clients share the complete kind-tagged codec; no second request layout. -/
def requestStream : StreamCodec (Request .object) := requestStreamFor .object

def requestCodec : LawfulCodec (Request .object) := requestCodecFor .object

theorem requestCodec_separates_target (request : Request .object)
    (other : ResourceId .object) (different : request.target ≠ other) :
    requestCodec.encode request ≠ requestCodec.encode { request with target := other } := by
  intro same
  apply different
  have decoded := congrArg requestCodec.decode same
  rw [requestCodec.decode_encode, requestCodec.decode_encode] at decoded
  exact congrArg Request.target (Option.some.inj decoded)

theorem requestCodec_separates_effectsDigest (request : Request .object)
    (other : Digest) (different : request.effectsDigest ≠ other) :
    requestCodec.encode request ≠ requestCodec.encode { request with effectsDigest := other } := by
  intro same
  apply different
  have decoded := congrArg requestCodec.decode same
  rw [requestCodec.decode_encode, requestCodec.decode_encode] at decoded
  exact congrArg Request.effectsDigest (Option.some.inj decoded)

theorem requestStream_composes (request : Request .object) (suffix : List UInt8) :
    requestStream.decodePrefix (requestStream.encode request ++ suffix) = some (request, suffix) :=
  requestStream.decodePrefix_encode request suffix

end Minidregg.Compiler.TypedAuthorizationRequestCodec
