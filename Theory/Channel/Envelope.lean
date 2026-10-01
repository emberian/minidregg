/-
# Theory.Channel.Envelope — a member's cell as its sealing fields (X25519 mode; CHANNELS.md §2.2, CH-CLIENT-1)

The member client (`mini channel`) seals one cell per tick. The cryptography is outside Lean (X25519,
cSHAKE256 key derivation, ChaCha20-Poly1305: §2.2's assumptions A1, A2); where each field sits in the
cell is here, so the client never re-implements the layout:

```
regular cell   header 8 |                  viewTag 1 | frag 4 | epk 32 | payload (C − 61) | tag 16
duty cell      header 8 | duty public 160 | viewTag 1 | frag 4 | epk 32 | payload (C − 221) | tag 16
```

The sealed part `viewTag | frag | epk | payload` is CH-CELL's `Plaintext .x25519` codec at the
header's sealed length (`envelopeCell_regular`, `envelopeCell_duty`), so at P1 a regular cell carries
195 payload bytes and a duty cell 35 (`P1_payloadCaps`). `frag` and `payload` hold AEAD ciphertext and
`tag` the AEAD tag; `viewTag` and `epk` are in the clear, as they must be for a recipient to find and
open the cell. The duty public part (`vrf | verdictRoot | accRoot`) is CH-DUTY's; this module only
places it.

Byte entry points:
* `minidregg_channel_payload_cap pid tick` — the payload capacity at that tick, 4 bytes big-endian;
* `minidregg_channel_seal_cell pid header duty viewTag frag epk payload tag` — the cell (`C` bytes), or
  empty when the class is unknown or a field has the wrong length (`sealCellBytesList_is_envelopeCell`,
  pole `sealCellBytesList_refuses_payload`);
* `minidregg_channel_open_cell pid cell` — the seven fields, each as `length 2 | bytes`, or empty when
  the input is not `C` bytes (`openCellBytesList_sealCell`, pole `openCellBytesList_refuses_length`).

Imports `Theory.Channel.Cell` only; pins in `Theory.Channel.Audit`.
-/
import Theory.Channel.Cell

namespace Minidregg.Theory.Channel

set_option autoImplicit false

/-! ## The layout at a header -/

/-- The duty public part's length at a header: 160 at a duty tick, 0 otherwise. -/
def dutyLenAt (h : Header) : Nat := if isDutyTick h then dutyPublicLen else 0

/-- The sealed part's length at a header. -/
def sealedLenAt (P : Profile) (h : Header) : Nat := if isDutyTick h then P.dutySealedLen else P.sealedLen

/-- The X25519-mode payload capacity at a header. -/
def payloadCapAt (P : Profile) (h : Header) : Nat := sealedLenAt P h - SealMode.x25519.overhead

theorem payloadCapAt_eq (P : Profile) (h : Header) :
    payloadCapAt P h = if isDutyTick h then P.dutyPayloadCap .x25519 else P.payloadCap .x25519 := by
  unfold payloadCapAt sealedLenAt Profile.dutyPayloadCap Profile.payloadCap
  split <;> rfl

theorem sealedLenAt_ge (P : Profile) (h : Header) : SealMode.x25519.overhead ≤ sealedLenAt P h := by
  have := plaintext_fits P .x25519
  unfold sealedLenAt; split <;> omega

/-- The parts after the header add up to the body: `duty + sealed + tag = C − 8`. -/
theorem envelope_parts_length (P : Profile) (h : Header) :
    dutyLenAt h + sealedLenAt P h + tagLen = P.bodyLen := by
  have := P.C_ge
  unfold dutyLenAt sealedLenAt
  rw [P.bodyLen_eq, tagLen_eq]
  split
  · rw [P.dutySealedLen_eq]; unfold dutyPublicLen; omega
  · rw [P.sealedLen_eq]; omega

/-! ## The cell of an envelope -/

/-- The body bytes: `duty ++ Plaintext.encode p ++ tag`. -/
def envelopeBody {P : Profile} {h : Header} (duty : Blob (dutyLenAt h))
    (p : Plaintext .x25519 (sealedLenAt P h)) (tag : Blob tagLen) : List UInt8 :=
  duty.val ++ p.encode ++ tag.val

theorem envelopeBody_length {P : Profile} {h : Header} (duty : Blob (dutyLenAt h))
    (p : Plaintext .x25519 (sealedLenAt P h)) (tag : Blob tagLen) :
    (envelopeBody duty p tag).length = P.bodyLen := by
  rw [← envelope_parts_length P h]
  simp only [envelopeBody, List.length_append, duty.property, tag.property,
    Plaintext.encode_length (sealedLenAt_ge P h) p]

/-- A member's cell: the envelope's body under its header, through CH-CELL's total parse `Cell.ofRaw`. -/
def envelopeCell {P : Profile} (h : Header) (duty : Blob (dutyLenAt h))
    (p : Plaintext .x25519 (sealedLenAt P h)) (tag : Blob tagLen) : Cell P :=
  Cell.ofRaw h ⟨envelopeBody duty p tag, envelopeBody_length duty p tag⟩

/-- The cell's bytes are the header, then the envelope's parts in order. -/
theorem envelopeCell_encode {P : Profile} (h : Header) (duty : Blob (dutyLenAt h))
    (p : Plaintext .x25519 (sealedLenAt P h)) (tag : Blob tagLen) :
    (envelopeCell (P := P) h duty p tag).encode = h.encode ++ envelopeBody duty p tag := by
  have hb := congrArg Blob.val (Cell.bodyBlob_ofRaw (P := P) h ⟨envelopeBody duty p tag, envelopeBody_length duty p tag⟩)
  simp only [Cell.bodyBlob] at hb
  simp only [envelopeCell, Cell.encode, Cell.ofRaw_header, hb]

/-- At a regular tick the cell's sealed part IS the plaintext codec of the envelope, and its tag the
envelope's tag. -/
theorem envelopeCell_regular {P : Profile} {h : Header} (hd : isDutyTick h = false)
    (duty : Blob (dutyLenAt h)) (p : Plaintext .x25519 (sealedLenAt P h)) (tag : Blob tagLen)
    {r : Regular P} (hr : (envelopeCell (P := P) h duty p tag).body = .regular r) :
    r.sealed.val = p.encode ∧ r.tag = tag := by
  have hb := congrArg Blob.val (Cell.bodyBlob_ofRaw (P := P) h ⟨envelopeBody duty p tag, envelopeBody_length duty p tag⟩)
  simp only [Cell.bodyBlob] at hb
  change (envelopeCell (P := P) h duty p tag).body.encode = _ at hb
  rw [hr] at hb
  have hdl : duty.val = [] := List.eq_nil_of_length_eq_zero (by rw [duty.property]; simp [dutyLenAt, hd])
  have hpl : p.encode.length = P.sealedLen := by
    rw [Plaintext.encode_length (sealedLenAt_ge P h) p]; simp [sealedLenAt, hd]
  simp only [Body.encode, envelopeBody, hdl, List.nil_append] at hb
  obtain ⟨hs, ht⟩ := List.append_inj hb (by rw [r.sealed.property, hpl])
  exact ⟨hs, Blob.ext ht⟩

/-- At a duty tick the duty public part is the envelope's duty bytes, the sealed part its plaintext
codec, and the tag its tag. -/
theorem envelopeCell_duty {P : Profile} {h : Header} (hd : isDutyTick h = true)
    (duty : Blob (dutyLenAt h)) (p : Plaintext .x25519 (sealedLenAt P h)) (tag : Blob tagLen)
    {d : Duty P} (hr : (envelopeCell (P := P) h duty p tag).body = .duty d) :
    d.vrf.val ++ d.verdictRoot.val ++ d.accRoot.val = duty.val ∧ d.sealed.val = p.encode ∧ d.tag = tag := by
  have hb := congrArg Blob.val (Cell.bodyBlob_ofRaw (P := P) h ⟨envelopeBody duty p tag, envelopeBody_length duty p tag⟩)
  simp only [Cell.bodyBlob] at hb
  change (envelopeCell (P := P) h duty p tag).body.encode = _ at hb
  rw [hr] at hb
  have hdl : duty.val.length = 160 := by rw [duty.property]; simp [dutyLenAt, hd, dutyPublicLen]
  have hpl : p.encode.length = P.dutySealedLen := by
    rw [Plaintext.encode_length (sealedLenAt_ge P h) p]; simp [sealedLenAt, hd]
  simp only [Body.encode, envelopeBody] at hb
  have hb' : (d.vrf.val ++ d.verdictRoot.val ++ d.accRoot.val) ++ (d.sealed.val ++ d.tag.val) =
      duty.val ++ (p.encode ++ tag.val) := by
    simpa only [List.append_assoc] using hb
  obtain ⟨hpub, hrest⟩ := List.append_inj hb' (by
    simp only [List.length_append, d.vrf.property, d.verdictRoot.property, d.accRoot.property, hdl])
  obtain ⟨hs, ht⟩ := List.append_inj hrest (by rw [d.sealed.property, hpl])
  exact ⟨hpub, hs, Blob.ext ht⟩

/-! ## Byte entry points -/

/-- A length-prefixed field: `length 2 | bytes` (big-endian; every field here is under 2¹⁶ bytes). -/
def lp (b : List UInt8) : List UInt8 := be16 (U16.ofNat b.length) ++ b

/-- Cut a byte string into consecutive pieces of the given lengths. -/
def cut : List Nat → List UInt8 → List (List UInt8)
  | [], _ => []
  | n :: ns, bytes => bytes.take n :: cut ns (bytes.drop n)

theorem cut_flatten : ∀ (pieces : List (List UInt8)),
    cut (pieces.map List.length) (pieces.foldr (· ++ ·) []) = pieces
  | [] => rfl
  | p :: ps => by
    simp only [List.map_cons, List.foldr_cons, cut, List.take_left' rfl, List.drop_left' rfl, cut_flatten ps]

/-- The 4-byte big-endian capacity at tick `tick` of class `pid`; empty for an unknown class. -/
def payloadCapBytesList (pid : UInt8) (tick : Nat) : List UInt8 :=
  match profileOfId pid with
  | none => []
  | some P =>
    let cap := payloadCapAt P ⟨0, 0, U16.ofNat tick, 0⟩
    [(cap / 16777216 % 256).toUInt8, (cap / 65536 % 256).toUInt8, (cap / 256 % 256).toUInt8, (cap % 256).toUInt8]

@[export minidregg_channel_payload_cap]
def payloadCapBytes (pid : UInt8) (tick : UInt32) : ByteArray := ⟨(payloadCapBytesList pid tick.toNat).toArray⟩

/-- At P1 (id 1) a regular cell carries 195 payload bytes and the duty cell (tick 0) 35. -/
theorem P1_payloadCaps :
    payloadCapBytesList 1 1 = [0, 0, 0, 195] ∧ payloadCapBytesList 1 0 = [0, 0, 0, 35] := by decide +kernel

/-- Every field has its length at this header. -/
def FieldsFit (P : Profile) (h : Header) (duty viewTag frag epk payload tag : List UInt8) : Prop :=
  duty.length = dutyLenAt h ∧ viewTag.length = 1 ∧ frag.length = 4 ∧ epk.length = 32 ∧
    payload.length = payloadCapAt P h ∧ tag.length = 16

instance (P : Profile) (h : Header) (duty viewTag frag epk payload tag : List UInt8) :
    Decidable (FieldsFit P h duty viewTag frag epk payload tag) := by
  unfold FieldsFit; infer_instance

/-- The cell of the fields, or empty. -/
def sealCellBytesList (pid : UInt8) (header duty viewTag frag epk payload tag : List UInt8) : List UInt8 :=
  match profileOfId pid with
  | none => []
  | some P =>
    match Header.decode header with
    | some (h, []) =>
      if FieldsFit P h duty viewTag frag epk payload tag then
        h.encode ++ duty ++ viewTag ++ frag ++ epk ++ payload ++ tag
      else []
    | _ => []

@[export minidregg_channel_seal_cell]
def sealCellBytes (pid : UInt8) (header duty viewTag frag epk payload tag : ByteArray) : ByteArray :=
  ⟨(sealCellBytesList pid header.toList duty.toList viewTag.toList frag.toList epk.toList payload.toList
    tag.toList).toArray⟩

/-- The fields of a cell, each length-prefixed, or empty. -/
def openCellBytesList (pid : UInt8) (bytes : List UInt8) : List UInt8 :=
  match profileOfId pid with
  | none => []
  | some P =>
    if bytes.length = P.C then
      match Header.decode bytes with
      | some (h, _) =>
        (cut [8, dutyLenAt h, 1, 4, 32, payloadCapAt P h, 16] bytes).flatMap lp
      | none => []
    else []

@[export minidregg_channel_open_cell]
def openCellBytes (pid : UInt8) (cell : ByteArray) : ByteArray := ⟨(openCellBytesList pid cell.toList).toArray⟩

/-- **The seal export is the envelope's cell**: fed a plaintext's fields, a duty part and a tag of the
header's lengths, it returns `(envelopeCell h duty p tag).encode` — `C` bytes (`cell_size_exact`). -/
theorem sealCellBytesList_is_envelopeCell {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P)
    (h : Header) (duty : Blob (dutyLenAt h)) (p : Plaintext .x25519 (sealedLenAt P h)) (tag : Blob tagLen) :
    sealCellBytesList pid h.encode duty.val [p.viewTag] p.frag.val p.epk.val p.payload.val tag.val =
      (envelopeCell (P := P) h duty p tag).encode := by
  have hfit : FieldsFit P h duty.val [p.viewTag] p.frag.val p.epk.val p.payload.val tag.val :=
    ⟨duty.property, rfl, p.frag.property, p.epk.property, p.payload.property, tag.property⟩
  have hdec : Header.decode h.encode = some (h, []) := by
    simpa using Header.decode_encode_append h []
  rw [envelopeCell_encode]
  simp only [sealCellBytesList, hp, hdec, if_pos hfit, envelopeBody, Plaintext.encode, List.append_assoc,
    List.cons_append, List.nil_append]

/-- The refusing pole: a payload of the wrong length is no cell. -/
theorem sealCellBytesList_refuses_payload {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P)
    (h : Header) {duty viewTag frag epk payload tag : List UInt8} (wrong : payload.length ≠ payloadCapAt P h) :
    sealCellBytesList pid h.encode duty viewTag frag epk payload tag = [] := by
  have hdec : Header.decode h.encode = some (h, []) := by
    simpa using Header.decode_encode_append h []
  have hn : ¬ FieldsFit P h duty viewTag frag epk payload tag := fun f => wrong f.2.2.2.2.1
  simp only [sealCellBytesList, hp, hdec, if_neg hn]

/-- **Opening inverts sealing**: the open export of a sealed cell returns exactly the seven fields it was
given, in order, each length-prefixed. -/
theorem openCellBytesList_sealCell {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P)
    (h : Header) {duty viewTag frag epk payload tag : List UInt8}
    (fit : FieldsFit P h duty viewTag frag epk payload tag) :
    openCellBytesList pid (sealCellBytesList pid h.encode duty viewTag frag epk payload tag) =
      [h.encode, duty, viewTag, frag, epk, payload, tag].flatMap lp := by
  obtain ⟨hd, hv, hf, he, hpl, ht⟩ := fit
  have hdec : Header.decode h.encode = some (h, []) := by
    simpa using Header.decode_encode_append h []
  have fit' : FieldsFit P h duty viewTag frag epk payload tag := ⟨hd, hv, hf, he, hpl, ht⟩
  have hparts := envelope_parts_length P h
  have hcap : payloadCapAt P h + 37 = sealedLenAt P h := by
    have := sealedLenAt_ge P h; unfold payloadCapAt; simp only [SealMode.overhead, SealMode.epkLen] at *; omega
  have hlen : (h.encode ++ duty ++ viewTag ++ frag ++ epk ++ payload ++ tag).length = P.C := by
    have := P.C_ge
    simp only [List.length_append, Header.encode_length, headerLen_eq, hd, hv, hf, he, hpl, ht]
    rw [P.bodyLen_eq, tagLen_eq] at hparts
    omega
  have hdec' : Header.decode (h.encode ++ duty ++ viewTag ++ frag ++ epk ++ payload ++ tag) =
      some (h, duty ++ viewTag ++ frag ++ epk ++ payload ++ tag) := by
    simpa [List.append_assoc] using Header.decode_encode_append h (duty ++ viewTag ++ frag ++ epk ++ payload ++ tag)
  have hcut := cut_flatten [h.encode, duty, viewTag, frag, epk, payload, tag]
  simp only [List.map_cons, List.map_nil, Header.encode_length, headerLen_eq, hd, hv, hf, he, hpl, ht,
    List.foldr_cons, List.foldr_nil, List.append_nil] at hcut
  simp only [sealCellBytesList, hp, hdec, if_pos fit', openCellBytesList, hlen, if_true, hdec']
  rw [show h.encode ++ duty ++ viewTag ++ frag ++ epk ++ payload ++ tag =
      h.encode ++ (duty ++ (viewTag ++ (frag ++ (epk ++ (payload ++ tag))))) by simp only [List.append_assoc]]
  rw [hcut]

/-- The refusing pole: bytes that are not `C` long have no fields. -/
theorem openCellBytesList_refuses_length {pid : UInt8} {P : Profile} (hp : profileOfId pid = some P)
    {bytes : List UInt8} (wrong : bytes.length ≠ P.C) : openCellBytesList pid bytes = [] := by
  simp [openCellBytesList, hp, wrong]

end Minidregg.Theory.Channel
