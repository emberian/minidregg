/-
# Kernel.FnArchive — Mini's finalized history as fn archive articles

One archive article carries the finalized blocks of heights `[h, h+K)` with
their receipts (MINI-FN-660-REQUIREMENTS §3.3). Everything here is pure: the
article Mini signs and posts is a function of Mini-canonical persisted fields
only (the operator's archive profile and the committed log records), N1.

* **Bundle.** `bundleCodec` is a framed `StreamCodec` with a version word
  (`DREGG/FN/ARCHIVE-BUNDLE/v1`); it round-trips (`bundle_decode_encode`) and is
  canonical (`bundle_canonical`). A block is the exact durable-log record bytes
  (`DurableCheckpointCodec.recordFrame`) and the receipt the Host seals for it.
* **Message-ID.** `"<mini-archive-" ++ hex(cSHAKE256("DREGG.FN.ARCHIVE-MSGID/v1",
  preimage)) ++ "@" ++ domain ++ ">"`, the preimage the framed (domain,
  semantics, first height, last height, bundle digest). Framed, so two distinct
  tuples never share a preimage (`identityPreimage_injective`).
* **Authored source.** Five fixed headers, the version header
  `Mini-Archive: v1`, and the bundle bytes as base64 in 76-character CRLF lines.
  `Date` is the profile's persisted creation date, never the wall clock at send
  (fn performs no Date check and adds no Injection-Date when Date and
  Message-ID are supplied: FN-660-RESPONSE QF-7).
* **Extraction.** `extract` takes the identity Mini holds independently (the
  Message-ID it recorded at post time) and accepts exactly the rendered source
  of a bundle carrying that identity (`extract_render`, `extract_sound`): bytes
  reach the application only after that check (the M2 adapter contract (a)).
* **Size.** One source must fit fn's article bound A and one poll page
  (262,144 returned octets): an event over the page is refused by fn with no
  skip. `render` refuses a block over the profile's maximum block size and a
  source over the bound, by name, before anything is signed.
-/
import Kernel.FnReplyPublication
import Kernel.Base64

namespace Minidregg.Kernel.FnArchive

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.Tower256ConcreteBackend

set_option autoImplicit false

/-! ## Blocks and bundles -/

/-- One finalized block: the exact durable-log record bytes at its height
(`DurableCheckpointCodec.recordFrame.encode`) and the receipt the Host seals
for it (`acceptedCount` is the height). The log tag is the Store's own MAC and
is not archived. -/
structure Block where
  record : List UInt8
  receipt : Receipt
  deriving DecidableEq, Repr

def blockStream : StreamCodec Block :=
  StreamCodec.xmap (StreamCodec.product bytesStream receiptStream)
    (fun block => (block.record, block.receipt))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro block; cases block; rfl)

/-- The finalized blocks of heights `[first, first + blocks.length)`. -/
structure Bundle where
  domain : Digest
  semantics : Digest
  first : Nat
  blocks : List Block
  deriving DecidableEq, Repr

def bundleStream : StreamCodec Bundle :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.list blockStream))))
    (fun bundle => (bundle.domain, bundle.semantics, bundle.first, bundle.blocks))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2⟩)
    (by intro bundle; cases bundle; rfl)

/-- The bundle's version word. An unknown word refuses to decode. -/
def bundleFrame : List UInt8 := "DREGG/FN/ARCHIVE-BUNDLE/v1".toUTF8.toList

def bundleCodec : LawfulCodec Bundle := NativeHostCodec.framed bundleFrame bundleStream

theorem bundle_decode_encode (bundle : Bundle) :
    bundleCodec.decode (bundleCodec.encode bundle) = some bundle :=
  bundleCodec.decode_encode bundle

/-- Canonicity: only the encoding of a bundle decodes to it. -/
theorem bundle_canonical {bytes : List UInt8} {bundle : Bundle}
    (decoded : bundleCodec.decode bytes = some bundle) : bundleCodec.encode bundle = bytes :=
  NativeHostCodec.framed_canonical bundleFrame bundleStream decoded

theorem bundleCodec_encode_injective {left right : Bundle}
    (same : bundleCodec.encode left = bundleCodec.encode right) : left = right := by
  have l := bundle_decode_encode left
  rw [same, bundle_decode_encode right] at l
  exact (Option.some.inj l).symm

/-- The last height a bundle carries (`first` when it is empty). -/
def Bundle.last (bundle : Bundle) : Nat := bundle.first + bundle.blocks.length - 1

/-- Heights are consecutive from `first ≥ 1` and every receipt names its own
height; at least one block. -/
def Bundle.wellFormed (bundle : Bundle) : Bool :=
  !bundle.blocks.isEmpty && 1 ≤ bundle.first &&
    bundle.blocks.zipIdx.all fun (block, index) =>
      block.receipt.acceptedCount == bundle.first + index

def bundleDigest (bytes : List UInt8) : Digest :=
  (Sp800185Cshake256.hash "DREGG.FN.ARCHIVE-BUNDLE/v1".toUTF8.toList bytes).digest

/-! ## Identity -/

/-- What the Message-ID names: the domain, its semantics, the height range and
the digest of the exact bundle bytes. -/
structure Identity where
  domain : Digest
  semantics : Digest
  first : Nat
  last : Nat
  digest : Digest
  deriving DecidableEq, Repr

def identityStream : StreamCodec Identity :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat digestStream))))
    (fun id => (id.domain, id.semantics, id.first, id.last, id.digest))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2⟩)
    (by intro id; cases id; rfl)

def Bundle.identity (bundle : Bundle) : Identity :=
  ⟨bundle.domain, bundle.semantics, bundle.first, bundle.last,
    bundleDigest (bundleCodec.encode bundle)⟩

/-- Framed, so field boundaries cannot alias. -/
def identityPreimage (id : Identity) : List UInt8 :=
  "DREGG/FN/ARCHIVE-ID/v1".toUTF8.toList ++ identityStream.encode id

theorem identityPreimage_injective {left right : Identity}
    (same : identityPreimage left = identityPreimage right) : left = right := by
  have tail : identityStream.encode left = identityStream.encode right :=
    List.append_cancel_left same
  have l := identityStream.toLawful.decode_encode left
  have r := identityStream.toLawful.decode_encode right
  change identityStream.toLawful.decode (identityStream.encode left) = some left at l
  change identityStream.toLawful.decode (identityStream.encode right) = some right at r
  rw [tail, r] at l
  exact (Option.some.inj l).symm

def Identity.messageId (id : Identity) (messageIdDomain : String) : String :=
  let digest := Sp800185Cshake256.hash "DREGG.FN.ARCHIVE-MSGID/v1".toUTF8.toList
    (identityPreimage id)
  "<mini-archive-" ++ FnReplyPublication.hexBytes (digestStream.encode digest.digest) ++
    "@" ++ messageIdDomain ++ ">"

/-! ## The archive profile -/

/-- What the operator fixes once for a domain's archive, persisted with it:
the article's creation fields (`From`, the group, the Message-ID domain and the
`Date`, all checked by `CreationContext.valid`), the bundle size `k`, the
largest encoded block the profile admits, fn's article bound `A` and the poll
page. `carrierOverhead` budgets what fn adds around the authored source (the
FN-Authorship carrier and the served Xref, Path and Injection-Info lines;
measured 2026-10-04 on image d5b0b910: a 172-octet source served as 7,830). -/
structure Profile where
  creation : FnReplyPublication.CreationContext
  k : Nat
  maxBlockOctets : Nat
  articleBound : Nat
  pageBudget : Nat
  carrierOverhead : Nat
  deriving DecidableEq, Repr

/-- The proposed v1 poll page (fn `consumer-progress.md`). -/
def defaultPageBudget : Nat := 262144

def defaultCarrierOverhead : Nat := 16384

/-- The largest authored source the profile posts: what fn may store (A) and
what one poll reply may return, less fn's own additions. -/
def Profile.sourceBound (profile : Profile) : Nat :=
  min profile.articleBound profile.pageBudget - profile.carrierOverhead

/-! ### K sizing (requirements §3.3)

`blockCeiling m` over-approximates the stream bytes of one block whose record
is at most `m` octets: its length prefix, a receipt of two 512-bit digests, a
height and a world root (`digestStream` writes a base-255 digit string and a
terminator: at most 66 octets for a 512-bit value; a height below 2^64 at most
10). `sourceCeiling` adds the bundle frame and header and the base64 line
expansion (4 characters per 3 octets plus a CRLF per 76 characters) to the
header block. These are authored arithmetic; the theorem-backed bound is the
one `render` enforces on every source. -/
def digestCeiling : Nat := 66
def natCeiling : Nat := 10

def blockCeiling (maxBlockOctets : Nat) : Nat :=
  natCeiling + maxBlockOctets + 3 * digestCeiling + natCeiling

def bundleCeiling (k maxBlockOctets : Nat) : Nat :=
  bundleFrame.length + 2 * digestCeiling + 2 * natCeiling + k * blockCeiling maxBlockOctets

def headerCeiling : Nat := 1024

def sourceCeiling (k maxBlockOctets : Nat) : Nat :=
  let octets := bundleCeiling k maxBlockOctets
  let characters := 4 * ((octets + 2) / 3)
  headerCeiling + characters + 2 * (characters / 76 + 1)

inductive ProfileRefusal where
  | creationInvalid
  | kZero
  | pageAboveDefault
  | overheadExceedsBound
  | bundleExceedsBound (ceiling bound : Nat)
  deriving DecidableEq, Repr

def ProfileRefusal.word : ProfileRefusal → String
  | .creationInvalid => "archive creation fields are outside the article profile"
  | .kZero => "archive bundle size k must be at least one block"
  | .pageAboveDefault => "archive poll page exceeds fn's 262,144-octet poll page"
  | .overheadExceedsBound => "fn carrier overhead leaves no room for an authored source"
  | .bundleExceedsBound ceiling bound =>
      s!"one bundle of k blocks at the maximum block size could reach {ceiling} octets, over the {bound}-octet source bound"

/-- Refused at configuration if one bundle of `k` blocks at the profile's
maximum block size could exceed `min(A, page)` (with fn's carrier added). -/
def Profile.check (profile : Profile) : Except ProfileRefusal Unit := do
  unless profile.creation.valid do throw .creationInvalid
  unless 1 ≤ profile.k do throw .kZero
  unless profile.pageBudget ≤ defaultPageBudget do throw .pageAboveDefault
  unless profile.carrierOverhead < min profile.articleBound profile.pageBudget do
    throw .overheadExceedsBound
  let ceiling := sourceCeiling profile.k profile.maxBlockOctets
  unless ceiling ≤ profile.sourceBound do throw (.bundleExceedsBound ceiling profile.sourceBound)

/-! ## The authored source -/

def messageId (profile : Profile) (bundle : Bundle) : String :=
  bundle.identity.messageId profile.creation.messageIdDomain

/-- The header block, through the blank line. The Message-ID is an argument so
that the reader can rebuild it from the identity it holds. -/
def header (profile : Profile) (messageIdText : String) : List UInt8 :=
  ("From: " ++ profile.creation.fromMailbox ++ "\r\n" ++
    "Date: " ++ profile.creation.date ++ "\r\n" ++
    "Newsgroups: " ++ profile.creation.newsgroup ++ "\r\n" ++
    "Subject: Mini archive\r\n" ++
    "Message-ID: " ++ messageIdText ++ "\r\n" ++
    "Mini-Archive: v1\r\n" ++
    "\r\n").toUTF8.toList

def crlf : List UInt8 := [13, 10]

/-- The body: canonical padded base64 of the bundle bytes, 57 octets (76
characters) per CRLF line, with a final CRLF (`Base64.encodeLines` as bytes). -/
def bodyLines (bytes : List UInt8) : List UInt8 :=
  crlf.intercalate ((Base64.chunks bytes).map Base64.encode) ++ crlf

inductive RenderRefusal where
  | profile (refusal : ProfileRefusal)
  | bundleMalformed
  | wrongBlockCount (expected actual : Nat)
  | blockTooLarge (height octets : Nat)
  | messageIdTooLong
  | sourceTooLarge (octets bound : Nat)
  deriving DecidableEq, Repr

def RenderRefusal.word : RenderRefusal → String
  | .profile refusal => refusal.word
  | .bundleMalformed => "archive bundle heights are not consecutive from its first height"
  | .wrongBlockCount expected actual =>
      s!"archive bundle holds {actual} blocks, the profile's k is {expected}"
  | .blockTooLarge height octets =>
      s!"block {height} is {octets} octets, over the profile's maximum block size (raise it and re-check k)"
  | .messageIdTooLong => "archive Message-ID exceeds 256 octets"
  | .sourceTooLarge octets bound => s!"archive source is {octets} octets, over the {bound}-octet bound"

/-- The first block over the profile's maximum block size, if any. -/
def oversizedBlock (profile : Profile) (bundle : Bundle) : Option Block :=
  bundle.blocks.find? fun block => profile.maxBlockOctets < (blockStream.encode block).length

/-- Everything `render` checks before it builds the source. -/
def checkBundle (profile : Profile) (bundle : Bundle) : Except RenderRefusal Unit := do
  match profile.check with
  | .error refusal => throw (.profile refusal)
  | .ok () => pure ()
  unless bundle.wellFormed do throw .bundleMalformed
  unless bundle.blocks.length == profile.k do
    throw (.wrongBlockCount profile.k bundle.blocks.length)
  if let some block := oversizedBlock profile bundle then
    throw (.blockTooLarge block.receipt.acceptedCount (blockStream.encode block).length)
  unless (messageId profile bundle).utf8ByteSize ≤ 256 do throw .messageIdTooLong

/-- The exact authored source of a bundle under a profile. -/
def source (profile : Profile) (bundle : Bundle) : List UInt8 :=
  header profile (messageId profile bundle) ++ bodyLines (bundleCodec.encode bundle)

/-- The article Mini signs, or a named refusal before anything is signed. -/
def render (profile : Profile) (bundle : Bundle) : Except RenderRefusal (List UInt8) := do
  checkBundle profile bundle
  let bytes := source profile bundle
  if bytes.length ≤ profile.sourceBound then pure bytes
  else throw (.sourceTooLarge bytes.length profile.sourceBound)

theorem render_ok {profile : Profile} {bundle : Bundle} {bytes : List UInt8}
    (rendered : render profile bundle = .ok bytes) :
    checkBundle profile bundle = .ok () ∧ bytes = source profile bundle ∧
      bytes.length ≤ profile.sourceBound := by
  unfold render at rendered
  cases checked : checkBundle profile bundle with
  | error refusal => simp [checked, bind, Except.bind] at rendered
  | ok _ =>
      simp only [checked, bind, Except.bind] at rendered
      split at rendered
      · rename_i within
        cases rendered
        exact ⟨rfl, rfl, within⟩
      · cases rendered

/-- A rendered source fits the profile's bound: fn's article bound and one
poll page, with fn's carrier added. -/
theorem render_within {profile : Profile} {bundle : Bundle} {bytes : List UInt8}
    (rendered : render profile bundle = .ok bytes) : bytes.length ≤ profile.sourceBound :=
  (render_ok rendered).2.2

/-! ## N1: the article is a function of persisted canonical fields only

`render`, `source` and `messageId` are pure functions (no IO in their types)
of the persisted archive profile and the bundle. The Message-ID moreover
depends on the bundle only through its exact bytes and on the profile only
through its Message-ID domain: the date, sender, group and sizing never
enter it. -/

theorem messageId_of_bytes {profile profile' : Profile} {bundle bundle' : Bundle}
    (domain : profile.creation.messageIdDomain = profile'.creation.messageIdDomain)
    (bytes : bundleCodec.encode bundle = bundleCodec.encode bundle') :
    messageId profile bundle = messageId profile' bundle' := by
  cases bundleCodec_encode_injective bytes
  simp only [messageId, domain]

theorem render_of_bytes (profile : Profile) {bundle bundle' : Bundle}
    (bytes : bundleCodec.encode bundle = bundleCodec.encode bundle') :
    render profile bundle = render profile bundle' := by
  cases bundleCodec_encode_injective bytes
  rfl

/-- Distinct identities give distinct preimages, so two bundles share a
Message-ID only through a cSHAKE256 collision or a bundle-digest collision. -/
theorem messageId_preimage_separates {bundle bundle' : Bundle}
    (different : bundle.identity ≠ bundle'.identity) :
    identityPreimage bundle.identity ≠ identityPreimage bundle'.identity :=
  fun same => different (identityPreimage_injective same)

/-! ## The body lines decode -/

def notCrlf (byte : UInt8) : Bool := byte != 10 && byte != 13

theorem b64Char_not_crlf (n : Nat) : notCrlf (Base64.b64Char n) = true := by
  unfold Base64.b64Char notCrlf
  split_ifs <;> simp [UInt8.ext_iff] <;> omega

theorem pad_not_crlf : notCrlf Base64.pad = true := by decide

theorem encode_not_crlf : ∀ (bytes : List UInt8), ∀ c ∈ Base64.encode bytes, notCrlf c = true
  | _ :: _ :: _ :: rest => by
      intro c member
      simp only [Base64.encode, List.mem_cons] at member
      rcases member with rfl | rfl | rfl | rfl | member
      · exact b64Char_not_crlf _
      · exact b64Char_not_crlf _
      · exact b64Char_not_crlf _
      · exact b64Char_not_crlf _
      · exact encode_not_crlf rest c member
  | [_, _] => by
      intro c member
      simp only [Base64.encode, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact b64Char_not_crlf _
      · exact b64Char_not_crlf _
      · exact b64Char_not_crlf _
      · exact pad_not_crlf
  | [_] => by
      intro c member
      simp only [Base64.encode, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact b64Char_not_crlf _
      · exact b64Char_not_crlf _
      · exact pad_not_crlf
      · exact pad_not_crlf
  | [] => by simp [Base64.encode]

theorem filter_encode (bytes : List UInt8) :
    (Base64.encode bytes).filter notCrlf = Base64.encode bytes :=
  List.filter_eq_self.mpr (encode_not_crlf bytes)

theorem filter_intercalate :
    ∀ (lines : List (List UInt8)),
      (crlf.intercalate lines).filter notCrlf = (lines.map (·.filter notCrlf)).flatten
  | [] => rfl
  | [line] => by simp
  | line :: next :: rest => by
      rw [List.intercalate_cons_cons, List.filter_append, List.filter_append,
        filter_intercalate (next :: rest)]
      simp [crlf, notCrlf]

theorem flatten_encode_chunks (bytes : List UInt8) :
    ((Base64.chunks bytes).map Base64.encode).flatten = Base64.encode bytes := by
  rw [Base64.chunks]
  split
  · next empty => simp [empty, Base64.encode]
  · rw [List.map_cons, List.flatten_cons, flatten_encode_chunks (bytes.drop Base64.lineBytes)]
    by_cases long : Base64.lineBytes ≤ bytes.length
    · rw [← Base64.encode_append _ _ (by simp [List.length_take, Base64.lineBytes] at long ⊢; omega),
        List.take_append_drop]
    · have short : bytes.length ≤ Base64.lineBytes := by omega
      rw [List.drop_eq_nil_of_le short, List.take_of_length_le short]
      simp [Base64.encode]
termination_by bytes.length
decreasing_by
  have : bytes.length ≠ 0 := by simpa [List.length_eq_zero_iff] using ‹¬bytes = []›
  simp only [List.length_drop, Base64.lineBytes]
  omega

theorem bodyLines_filter (bytes : List UInt8) :
    (bodyLines bytes).filter notCrlf = Base64.encode bytes := by
  rw [bodyLines, List.filter_append, filter_intercalate, List.map_map]
  have each : ((fun line : List UInt8 => line.filter notCrlf) ∘ Base64.encode) = Base64.encode := by
    funext line; exact filter_encode line
  rw [each, flatten_encode_chunks]
  simp [crlf, notCrlf]

theorem bodyLines_decode (bytes : List UInt8) :
    Base64.decode ((bodyLines bytes).filter notCrlf) = some bytes := by
  rw [bodyLines_filter, Base64.decode_encode]

/-! ## Extraction: only the source of a bundle with the expected identity -/

inductive ExtractRefusal where
  /-- The source does not open with this profile's headers naming the expected
  Message-ID: a substituted or foreign article. -/
  | identityMismatch
  | bodyNotBase64
  | bundleUndecodable
  /-- The bundle decodes but its own identity is not the expected one. -/
  | bundleIdentityMismatch
  | outsideProfile (refusal : RenderRefusal)
  /-- The bundle decodes but the source is not its exact rendering. -/
  | notCanonical
  deriving DecidableEq, Repr

def ExtractRefusal.word : ExtractRefusal → String
  | .identityMismatch => "archive source does not carry the expected Message-ID under this profile"
  | .bodyNotBase64 => "archive body is not canonical base64"
  | .bundleUndecodable => "archive body is not a Mini archive bundle"
  | .bundleIdentityMismatch => "archive bundle's identity differs from the expected Message-ID"
  | .outsideProfile refusal => s!"archive bundle is outside the profile: {refusal.word}"
  | .notCanonical => "archive source is not the exact rendering of its bundle"

/-- The bundle in `bytes`, accepted only when `bytes` is exactly the rendered
source of a bundle whose Message-ID is `expected`, the identity Mini recorded
independently when it posted. -/
def extract (profile : Profile) (expected : String) (bytes : List UInt8) :
    Except ExtractRefusal Bundle :=
  let head := header profile expected
  if bytes.take head.length != head then .error .identityMismatch else
  match Base64.decode ((bytes.drop head.length).filter notCrlf) with
  | none => .error .bodyNotBase64
  | some payload =>
      match bundleCodec.decode payload with
      | none => .error .bundleUndecodable
      | some bundle =>
          if messageId profile bundle != expected then .error .bundleIdentityMismatch else
          match render profile bundle with
          | .error refusal => .error (.outsideProfile refusal)
          | .ok again => if again == bytes then .ok bundle else .error .notCanonical

/-- Extraction inverts rendering. -/
theorem extract_render {profile : Profile} {bundle : Bundle} {bytes : List UInt8}
    (rendered : render profile bundle = .ok bytes) :
    extract profile (messageId profile bundle) bytes = .ok bundle := by
  have exact := (render_ok rendered).2.1
  have headTake : bytes.take (header profile (messageId profile bundle)).length =
      header profile (messageId profile bundle) := by
    rw [exact, source]; simp
  have bodyDrop : bytes.drop (header profile (messageId profile bundle)).length =
      bodyLines (bundleCodec.encode bundle) := by
    rw [exact, source]; simp
  simp only [extract, headTake, bne_self_eq_false, Bool.false_eq_true, if_false, bodyDrop,
    bodyLines_decode, bundle_decode_encode, rendered, beq_self_eq_true, if_true]

/-- Soundness: an accepted source is exactly the rendering of the returned
bundle, and that bundle's Message-ID is the expected one. -/
theorem extract_sound {profile : Profile} {expected : String} {bytes : List UInt8}
    {bundle : Bundle} (accepted : extract profile expected bytes = .ok bundle) :
    render profile bundle = .ok bytes ∧ messageId profile bundle = expected := by
  unfold extract at accepted
  by_cases head : (bytes.take (header profile expected).length != header profile expected) = true
  · simp [head] at accepted
  · simp only [head, if_false, Bool.false_eq_true] at accepted
    cases decoded : Base64.decode ((bytes.drop (header profile expected).length).filter notCrlf) with
    | none => simp [decoded] at accepted
    | some payload =>
        simp only [decoded] at accepted
        cases bundled : bundleCodec.decode payload with
        | none => simp [bundled] at accepted
        | some found =>
            simp only [bundled] at accepted
            by_cases named : (messageId profile found != expected) = true
            · simp [named] at accepted
            · simp only [named, if_false, Bool.false_eq_true] at accepted
              cases rendered : render profile found with
              | error refusal => simp [rendered] at accepted
              | ok again =>
                  simp only [rendered] at accepted
                  by_cases same : (again == bytes) = true
                  · simp only [same, if_true, Except.ok.injEq] at accepted
                    subst accepted
                    exact ⟨by rw [rendered, eq_of_beq same], by simpa using named⟩
                  · simp [same] at accepted

#assert_axioms bundle_decode_encode bundle_canonical bundleCodec_encode_injective
  identityPreimage_injective render_ok render_within messageId_of_bytes render_of_bytes
  messageId_preimage_separates b64Char_not_crlf encode_not_crlf filter_encode
  filter_intercalate flatten_encode_chunks bodyLines_filter bodyLines_decode
  extract_render extract_sound

end Minidregg.Kernel.FnArchive
