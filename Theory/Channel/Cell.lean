/-
# Theory.Channel.Cell — the channel class, the fixed-size cell and its canonical codec

CHANNELS.md §2.1–§2.2 (revision 2). A *class* is the tuple `(C, r, E, δ, δ_relay, μ)`; every slot of a
room's schedule emits one `C`-byte cell every tick. Two layouts share the size:

```
regular   header 8 | sealed (C − 24)                       | tag 16
duty      header 8 | vrf 96 | verdictRoot 32 | accRoot 32 | sealed (C − 184) | tag 16
```

`C = 256` at P0/P1 (`8 | 232 | 16`, duty `8 | 96 | 32 | 32 | 72 | 16`) and `C = 1,024` at P2
(`8 | 1000 | 16`, duty `8 | 96 | 32 | 32 | 840 | 16`). The header is `domain:2 | epoch:2 | tick:2 | slot:2`
big-endian. The layout is NOT tagged by a kind byte: a cell is a duty cell exactly when its header's tick
is `0` (the duty cell is the holder's cell at tick 0 of every epoch, §2.2), so the header decides the
layout and every `C`-byte string is exactly one cell.

The sealed part is opaque ciphertext here. Its plaintext layout (`viewTag 1 | frag 4 | [epk 32] |
payload`) has its own fixed-size codec below (`Plaintext`), so the payload capacities 195 / 227 (P1)
and 963 / 995 (P2) are theorems.

Candidate-independent: imports only `Init`. The axiom pins are in `Theory.Channel.Audit`.
-/


namespace Minidregg.Theory.Channel

set_option autoImplicit false

/-! ## Byte blobs of a fixed length -/

/-- Exactly `n` bytes. (A structure, not a `Subtype` abbreviation: its `DecidableEq` is then one instance
for every `n`, and Lean never unfolds a symbolic length such as `C − 184` to compare two blob types.) -/
structure Blob (n : Nat) where
  val : List UInt8
  property : val.length = n
  deriving DecidableEq

theorem Blob.ext {n : Nat} {a b : Blob n} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

/-- The first `n` bytes of a stream, zero-extended: total, and always exactly `n` bytes. The fill and
the sealing model draw fixed-length fields from an abstract byte stream (a PRF's output) through it. -/
def fit (n : Nat) (stream : List UInt8) : Blob n :=
  ⟨(stream ++ List.replicate n 0).take n, by simp⟩

theorem fit_val_of_length {n : Nat} (b : List UInt8) (h : b.length = n) : (fit n b).val = b := by
  simp [fit, ← h]

theorem fit_val_of_le {n : Nat} (b : List UInt8) (h : n ≤ b.length) : (fit n b).val = b.take n := by
  simp [fit, List.take_append_of_le_length h]

/-! ## The class -/

/-- The fixed parts of the layout. -/
def headerLen : Nat := 8
def tagLen : Nat := 16
/-- `vrf 96 | verdictRoot 32 | accRoot 32`: the duty cell's public part. -/
def dutyPublicLen : Nat := 160
/-- The largest sealing overhead (`viewTag 1 | frag 4 | epk 32`, X25519 mode). -/
def maxSealOverhead : Nat := 37

/-- A channel class `(C, r, E, δ, δ_relay, μ)` (CHANNELS.md §2 notation, §3 class menu). Times are in
milliseconds and the rate in millihertz, so P0's 0.1 Hz is exact. The two proof fields are the codec's
well-formedness: a duty cell's sealed part holds the largest sealing overhead, and a tick index fits
the header's two bytes. Timing well-formedness is the separate decidable `Profile.Timed`, so that a
badly-timed class is a refutable value rather than an unconstructible one. -/
structure Profile where
  /-- cell bytes -/
  C : Nat
  /-- ticks per second, in mHz -/
  rateMilliHz : Nat
  /-- ticks per channel epoch -/
  E : Nat
  /-- δ: the member emits at `frame + T_tick − δ` -/
  deltaMs : Nat
  /-- δ_relay: the relay's deadline is `frame + T_tick − δ_relay` -/
  deltaRelayMs : Nat
  /-- μ: a payload is eligible only if sealed by `emission − μ` -/
  muMs : Nat
  fits : headerLen + dutyPublicLen + maxSealOverhead + tagLen ≤ C
  epochFits : 0 < E ∧ E ≤ 65536

instance : DecidableEq Profile := fun a b =>
  if h : a.C = b.C ∧ a.rateMilliHz = b.rateMilliHz ∧ a.E = b.E ∧ a.deltaMs = b.deltaMs ∧
      a.deltaRelayMs = b.deltaRelayMs ∧ a.muMs = b.muMs then
    isTrue (by
      cases a; cases b
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
      subst h1 h2 h3 h4 h5 h6; rfl)
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

namespace Profile

/-- `T_tick = 1/r`, in ms. -/
def tickMs (P : Profile) : Nat := 1000000 / P.rateMilliHz

/-- The regular cell's sealed bytes, `C − 24`. -/
def sealedLen (P : Profile) : Nat := P.C - headerLen - tagLen
/-- The duty cell's sealed bytes, `C − 184`. Irreducible: elaborating a structure field of type
`Blob (C − 184)` otherwise unfolds `Nat.sub` on the symbolic `C` 184 times and exhausts the recursion
limit. Kernel `decide` and the equation lemma still see through it. -/
@[irreducible] def dutySealedLen (P : Profile) : Nat := P.C - headerLen - dutyPublicLen - tagLen
/-- Everything after the header, `C − 8`. -/
def bodyLen (P : Profile) : Nat := P.C - headerLen

/-- The class's timing is coherent: the rate is positive, a member's seal cutoff `frame + T − δ − μ`
falls after the frame (`δ + μ ≤ T`), and the relay's deadline falls after the member's emission
(`δ_relay < δ`). -/
def Timed (P : Profile) : Prop :=
  0 < P.rateMilliHz ∧ P.deltaMs + P.muMs ≤ P.tickMs ∧ P.deltaRelayMs < P.deltaMs

instance (P : Profile) : Decidable P.Timed := by unfold Timed; infer_instance

theorem C_ge (P : Profile) : 221 ≤ P.C := P.fits
theorem sealedLen_eq (P : Profile) : P.sealedLen = P.C - 24 := by unfold sealedLen headerLen tagLen; omega
theorem dutySealedLen_eq (P : Profile) : P.dutySealedLen = P.C - 184 := by
  unfold dutySealedLen headerLen dutyPublicLen tagLen; omega
theorem bodyLen_eq (P : Profile) : P.bodyLen = P.C - 8 := rfl

end Profile

theorem tagLen_eq : tagLen = 16 := rfl
theorem headerLen_eq : headerLen = 8 := rfl

/-- **P0 "phone"**: `C = 256 B, r = 0.1 Hz, E = 16` (E ASSUMED in §3), `δ / δ_relay / μ = 0.6 / 0.05 / 0.05 s`. -/
def P0 : Profile :=
  { C := 256, rateMilliHz := 100, E := 16, deltaMs := 600, deltaRelayMs := 50, muMs := 50,
    fits := by decide, epochFits := by decide }

/-- **P1 "room"**: `C = 256 B, r = 1 Hz, E = 16`, `0.3 / 0.02 / 0.05 s`. -/
def P1 : Profile :=
  { C := 256, rateMilliHz := 1000, E := 16, deltaMs := 300, deltaRelayMs := 20, muMs := 50,
    fits := by decide, epochFits := by decide }

/-- **P1 phone**: P1 with `δ = 0.6 s` (the phone variant differs only in δ). -/
def P1phone : Profile := { P1 with deltaMs := 600 }

/-- **P2 "fast"**: `C = 1,024 B, r = 5 Hz, E = 64`, `0.18 / 0.01 / 0.02 s`. -/
def P2 : Profile :=
  { C := 1024, rateMilliHz := 5000, E := 64, deltaMs := 180, deltaRelayMs := 10, muMs := 20,
    fits := by decide, epochFits := by decide }

/-- What a P2 phone variant at the phone δ = 0.6 s would be. It is NOT a class: `T_tick = 200 ms`. -/
def P2phoneAtPhoneDelta : Profile := { P2 with deltaMs := 600 }

theorem P0_timed : P0.Timed := by decide
theorem P1_timed : P1.Timed := by decide
theorem P1phone_timed : P1phone.Timed := by decide
theorem P2_timed : P2.Timed := by decide
/-- The refuting pole of `Timed`: a phone δ of 0.6 s does not fit P2's 200 ms tick, so P2 has no
phone variant in the §2 sense (§3's menu lists none; this says why). -/
theorem P2phoneAtPhoneDelta_not_timed : ¬ P2phoneAtPhoneDelta.Timed := by decide

theorem P1phone_differs_only_in_delta :
    P1phone.C = P1.C ∧ P1phone.rateMilliHz = P1.rateMilliHz ∧ P1phone.E = P1.E ∧
      P1phone.deltaRelayMs = P1.deltaRelayMs ∧ P1phone.muMs = P1.muMs ∧ P1phone.deltaMs ≠ P1.deltaMs :=
  by decide

theorem P1_layout : P1.sealedLen = 232 ∧ P1.dutySealedLen = 72 ∧ P1.tickMs = 1000 := by decide +kernel
theorem P0_layout : P0.sealedLen = 232 ∧ P0.dutySealedLen = 72 ∧ P0.tickMs = 10000 := by decide +kernel
theorem P2_layout : P2.sealedLen = 1000 ∧ P2.dutySealedLen = 840 ∧ P2.tickMs = 200 := by decide +kernel

/-! ## Header -/

/-- A two-byte header field. -/
abbrev U16 := Fin 65536

/-- `n mod 2¹⁶`: the header carries the low 16 bits of the epoch (see the report: the epoch WRAPS). -/
def U16.ofNat (n : Nat) : U16 := ⟨n % 65536, Nat.mod_lt _ (by decide)⟩

theorem U16.ofNat_val_of_lt {n : Nat} (h : n < 65536) : (U16.ofNat n).val = n := Nat.mod_eq_of_lt h

/-- `domain:2 | epoch:2 | tick:2 | slot:2`, big-endian. -/
structure Header where
  domain : U16
  epoch : U16
  tick : U16
  slot : U16
  deriving DecidableEq, Repr

def be16 (v : U16) : List UInt8 := [(v.val / 256).toUInt8, (v.val % 256).toUInt8]

def rd16 (hi lo : UInt8) : U16 :=
  ⟨hi.toNat * 256 + lo.toNat, by have := hi.toNat_lt; have := lo.toNat_lt; omega⟩

theorem rd16_be16 (v : U16) : rd16 ((v.val / 256).toUInt8) ((v.val % 256).toUInt8) = v := by
  apply Fin.ext
  have := v.isLt
  show (v.val / 256).toUInt8.toNat * 256 + (v.val % 256).toUInt8.toNat = v.val
  simp; omega

theorem be16_rd16 (hi lo : UInt8) : be16 (rd16 hi lo) = [hi, lo] := by
  have h1 := hi.toNat_lt
  have h2 := lo.toNat_lt
  simp only [be16, rd16, List.cons.injEq, and_true]
  constructor
  · rw [show (hi.toNat * 256 + lo.toNat) / 256 = hi.toNat by omega]; simp
  · rw [show (hi.toNat * 256 + lo.toNat) % 256 = lo.toNat by omega]; simp

def Header.encode (h : Header) : List UInt8 := be16 h.domain ++ be16 h.epoch ++ be16 h.tick ++ be16 h.slot

theorem Header.encode_length (h : Header) : h.encode.length = headerLen := by
  simp [Header.encode, be16, headerLen]

def Header.decode : List UInt8 → Option (Header × List UInt8)
  | a0 :: a1 :: b0 :: b1 :: c0 :: c1 :: d0 :: d1 :: rest =>
      some (⟨rd16 a0 a1, rd16 b0 b1, rd16 c0 c1, rd16 d0 d1⟩, rest)
  | _ => none

theorem Header.decode_encode_append (h : Header) (rest : List UInt8) :
    Header.decode (h.encode ++ rest) = some (h, rest) := by
  obtain ⟨d, e, t, s⟩ := h
  simp only [Header.encode, be16, List.cons_append, List.nil_append, Header.decode,
    rd16_be16]

theorem Header.decode_eq_some {bytes rest : List UInt8} {h : Header}
    (hd : Header.decode bytes = some (h, rest)) : bytes = h.encode ++ rest := by
  match bytes, hd with
  | a0 :: a1 :: b0 :: b1 :: c0 :: c1 :: d0 :: d1 :: rest', hd =>
    simp only [Header.decode, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp [Header.encode, be16_rd16]

/-! ## The cell -/

/-- The regular layout after the header: `sealed (C − 24) | tag 16`. -/
structure Regular (P : Profile) where
  sealed : Blob P.sealedLen
  tag : Blob tagLen
  deriving DecidableEq

/-- The duty layout after the header: `vrf 96 | verdictRoot 32 | accRoot 32 | sealed (C − 184) | tag 16`.
`vrf` is the ECVRF-EDWARDS25519-SHA512 proof (80 B) and 16 reserved bytes (§2.2). -/
structure Duty (P : Profile) where
  vrf : Blob 96
  verdictRoot : Blob 32
  accRoot : Blob 32
  sealed : Blob P.dutySealedLen
  tag : Blob tagLen
  deriving DecidableEq

/-- The two layouts after the header. (Two structures under one sum, rather than one inductive with the
fields inline: the latter's `noConfusion` makes Lean compare `Blob (C − 24)` with `Blob (C − 184)` by
unfolding `Nat.sub` on a symbolic `C`, which exhausts the recursion limit.) -/
inductive Body (P : Profile) where
  | regular (r : Regular P)
  | duty (d : Duty P)
  deriving DecidableEq

def Body.isDuty {P : Profile} : Body P → Bool
  | .regular .. => false
  | .duty .. => true

def Body.encode {P : Profile} : Body P → List UInt8
  | .regular ⟨s, t⟩ => s.val ++ t.val
  | .duty ⟨v, a, b, s, t⟩ => v.val ++ a.val ++ b.val ++ s.val ++ t.val

theorem Body.encode_length {P : Profile} (b : Body P) : b.encode.length = P.bodyLen := by
  have := P.C_ge
  cases b with
  | regular r =>
    obtain ⟨s, t⟩ := r
    simp only [Body.encode, List.length_append, s.property, t.property]
    rw [P.sealedLen_eq, P.bodyLen_eq, tagLen_eq]; omega
  | duty d =>
    obtain ⟨v, a, b, s, t⟩ := d
    simp only [Body.encode, List.length_append, v.property, a.property, b.property, s.property, t.property]
    rw [P.dutySealedLen_eq, P.bodyLen_eq, tagLen_eq]; omega

/-- The duty layout exactly at tick 0. -/
def isDutyTick (h : Header) : Bool := h.tick.val == 0

/-- A cell: a header and the body its tick selects. -/
structure Cell (P : Profile) where
  header : Header
  body : Body P
  layout : body.isDuty = isDutyTick header

theorem Cell.ext {P : Profile} {a b : Cell P} (hh : a.header = b.header) (hb : a.body = b.body) : a = b := by
  cases a; cases b; simp only at hh hb; subst hh hb; rfl

instance {P : Profile} : DecidableEq (Cell P) := fun a b =>
  if h : a.header = b.header ∧ a.body = b.body then isTrue (Cell.ext h.1 h.2)
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

/-- The cell's bytes: `header ++ body`. -/
def Cell.encode {P : Profile} (c : Cell P) : List UInt8 := c.header.encode ++ c.body.encode

/-- **`cell_size_exact`** (CHANNELS.md §2.2): every cell of class `P` is exactly `C` bytes, in both
layouts. -/
theorem cell_size_exact {P : Profile} (c : Cell P) : c.encode.length = P.C := by
  have := P.C_ge
  simp only [Cell.encode, List.length_append, Header.encode_length, Body.encode_length, P.bodyLen_eq,
    headerLen_eq]
  omega

/-- The body bytes as a blob. -/
def Cell.bodyBlob {P : Profile} (c : Cell P) : Blob P.bodyLen := ⟨c.body.encode, c.body.encode_length⟩

/-- The total parse of `C − 8` body bytes under a header: the header's tick picks the layout. Every
field is a slice of the input; `ofRaw_bodyBlob` / `bodyBlob_ofRaw` make it the inverse of `bodyBlob`. -/
def Cell.ofRaw {P : Profile} (h : Header) (b : Blob P.bodyLen) : Cell P :=
  if hd : isDutyTick h = true then
    { header := h
      body := .duty ⟨fit 96 b.val, fit 32 (b.val.drop 96), fit 32 (b.val.drop 128),
        fit P.dutySealedLen (b.val.drop 160), fit tagLen (b.val.drop (160 + P.dutySealedLen))⟩
      layout := by simp [Body.isDuty, hd] }
  else
    { header := h
      body := .regular ⟨fit P.sealedLen b.val, fit tagLen (b.val.drop P.sealedLen)⟩
      layout := by cases hh : isDutyTick h <;> simp_all [Body.isDuty] }

theorem Cell.ofRaw_header {P : Profile} (h : Header) (b : Blob P.bodyLen) : (Cell.ofRaw h b).header = h := by
  unfold Cell.ofRaw; split <;> rfl

theorem Cell.bodyBlob_ofRaw {P : Profile} (h : Header) (b : Blob P.bodyLen) :
    (Cell.ofRaw h b).bodyBlob = b := by
  have hf := P.C_ge
  have hb : b.val.length = P.C - 8 := b.property
  have hs := P.sealedLen_eq
  have hd := P.dutySealedLen_eq
  apply Blob.ext
  unfold Cell.ofRaw
  split
  · simp only [Cell.bodyBlob, Body.encode]
    rw [fit_val_of_le _ (by omega), fit_val_of_le _ (by simp; omega), fit_val_of_le _ (by simp; omega),
      fit_val_of_le _ (by simp; omega), fit_val_of_length _ (by simp [tagLen_eq]; omega)]
    rw [← List.take_add, ← List.take_add, ← List.take_add, List.take_append_drop]
  · simp only [Cell.bodyBlob, Body.encode]
    rw [fit_val_of_le _ (by omega), fit_val_of_length _ (by simp [tagLen_eq]; omega), List.take_append_drop]

theorem Cell.ofRaw_bodyBlob {P : Profile} (c : Cell P) : Cell.ofRaw c.header c.bodyBlob = c := by
  obtain ⟨h, body, lay⟩ := c
  apply Cell.ext (Cell.ofRaw_header _ _)
  unfold Cell.ofRaw
  cases body with
  | regular r =>
    obtain ⟨s, t⟩ := r
    have hd : isDutyTick h = false := by simpa [Body.isDuty] using lay.symm
    have hs := s.property; have ht := t.property
    simp only [hd, Bool.false_eq_true, ↓reduceDIte, Cell.bodyBlob, Body.encode, Body.regular.injEq,
      Regular.mk.injEq]
    constructor <;> apply Blob.ext
    · rw [fit_val_of_le _ (by simp [hs, ht])]; exact List.take_left' hs
    · rw [List.drop_left' hs, fit_val_of_length _ ht]
  | duty d =>
    obtain ⟨v, a, b, s, t⟩ := d
    have hd : isDutyTick h = true := by simpa [Body.isDuty] using lay.symm
    simp only [hd, ↓reduceDIte, Cell.bodyBlob, Body.encode, Body.duty.injEq, Duty.mk.injEq]
    have hv := v.property; have ha := a.property; have hb := b.property
    have hs := s.property; have ht := t.property
    have e96 : (v.val ++ a.val ++ b.val ++ s.val ++ t.val) = v.val ++ (a.val ++ (b.val ++ (s.val ++ t.val))) := by
      simp
    rw [e96]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> apply Blob.ext
    · rw [fit_val_of_le _ (by simp [hv])]; exact List.take_left' hv
    · rw [List.drop_left' hv, fit_val_of_le _ (by simp [ha])]; exact List.take_left' ha
    · rw [show (128 : Nat) = 96 + 32 from rfl, ← List.drop_drop, List.drop_left' hv, List.drop_left' ha,
        fit_val_of_le _ (by simp [hb])]
      exact List.take_left' hb
    · rw [show (160 : Nat) = 96 + 32 + 32 from rfl, ← List.drop_drop, ← List.drop_drop, List.drop_left' hv,
        List.drop_left' ha, List.drop_left' hb, fit_val_of_le _ (by simp [hs])]
      exact List.take_left' hs
    · rw [show 160 + P.dutySealedLen = 96 + 32 + 32 + P.dutySealedLen from rfl, ← List.drop_drop,
        ← List.drop_drop, ← List.drop_drop, List.drop_left' hv, List.drop_left' ha, List.drop_left' hb,
        List.drop_left' hs, fit_val_of_length _ ht]

/-! ## The codec -/

/-- Decode: an 8-byte header, then exactly `C − 8` body bytes, parsed in the layout the tick selects.
Anything of another length refuses. -/
def Cell.decode (P : Profile) (bytes : List UInt8) : Option (Cell P) :=
  match Header.decode bytes with
  | none => none
  | some (h, rest) => if hl : rest.length = P.bodyLen then some (Cell.ofRaw h ⟨rest, hl⟩) else none

theorem Cell.encode_eq_header_append {P : Profile} (c : Cell P) :
    c.encode = c.header.encode ++ c.bodyBlob.val := rfl

/-- **`cell_decode_canonical`**, the accepting pole: decoding a cell's bytes returns the cell. -/
theorem cell_decode_encode {P : Profile} (c : Cell P) : Cell.decode P c.encode = some c := by
  rw [Cell.encode_eq_header_append, Cell.decode, Header.decode_encode_append]
  simp only [c.bodyBlob.property, ↓reduceDIte]
  exact congrArg some (Cell.ofRaw_bodyBlob c)

/-- **`cell_decode_canonical`** as CHANNELS.md §2.2 states it: a decoded cell re-encodes to exactly the
bytes it came from. With `cell_decode_encode` the codec is a bijection onto its accepted set. -/
theorem cell_decode_canonical {P : Profile} {bytes : List UInt8} {c : Cell P}
    (accepted : Cell.decode P bytes = some c) : c.encode = bytes := by
  unfold Cell.decode at accepted
  split at accepted
  · cases accepted
  · rename_i h rest hd
    split at accepted
    · rename_i hl
      cases accepted
      rw [Cell.encode_eq_header_append, Cell.ofRaw_header, Cell.bodyBlob_ofRaw, Header.decode_eq_some hd]
    · cases accepted

theorem cell_decode_eq_some_iff {P : Profile} (bytes : List UInt8) (c : Cell P) :
    Cell.decode P bytes = some c ↔ c.encode = bytes :=
  ⟨cell_decode_canonical, fun h => h ▸ cell_decode_encode c⟩

theorem cell_encode_injective {P : Profile} : Function.Injective (Cell.encode (P := P)) := by
  intro a b h
  have := cell_decode_encode a
  rw [h, cell_decode_encode b] at this
  exact (Option.some.inj this).symm

/-- **`cell_decode_canonical`**, the refusing pole: a byte string of any length but `C` refuses. -/
theorem cell_decode_refuses_length {P : Profile} {bytes : List UInt8} (h : bytes.length ≠ P.C) :
    Cell.decode P bytes = none := by
  cases hd : Cell.decode P bytes with
  | none => rfl
  | some c => exact absurd ((cell_decode_canonical hd) ▸ cell_size_exact c) h

/-- The codec has no other refusal: every `C`-byte string is a cell. So "non-canonical" means exactly
"not `C` bytes" — there is no second encoding of any cell to refuse (`cell_encode_injective`), and no
`C`-byte string without a cell. -/
theorem cell_decode_total_on_length {P : Profile} {bytes : List UInt8} (h : bytes.length = P.C) :
    ∃ c, Cell.decode P bytes = some c := by
  have hf := P.fits
  simp only [headerLen, dutyPublicLen, maxSealOverhead, tagLen] at hf
  match bytes, h with
  | a0 :: a1 :: b0 :: b1 :: c0 :: c1 :: d0 :: d1 :: rest, h =>
    have hl : rest.length = P.bodyLen := by simp [Profile.bodyLen, headerLen] at h ⊢; omega
    exact ⟨Cell.ofRaw ⟨rd16 a0 a1, rd16 b0 b1, rd16 c0 c1, rd16 d0 d1⟩ ⟨rest, hl⟩,
      by simp only [Cell.decode, Header.decode, hl, ↓reduceDIte]⟩
  | [], h | [_], h | [_, _], h | [_, _, _], h | [_, _, _, _], h | [_, _, _, _, _], h
  | [_, _, _, _, _, _], h | [_, _, _, _, _, _, _], h => simp at h; omega

/-- The header a decoded cell carries is the header its first eight bytes spell. -/
theorem cell_header_bytes {P : Profile} (c : Cell P) : c.encode.take headerLen = c.header.encode := by
  rw [Cell.encode]; exact List.take_left' c.header.encode_length

/-! ## The sealed plaintext: `viewTag 1 | frag 4 | [epk 32] | payload` -/

/-- X25519 mode carries a 32-byte ephemeral key per cell; ML-KEM mode carries none (its ciphertext rides
in front of a message, in the sender's own cells, §2.2). -/
inductive SealMode where
  | x25519
  | mlkem
  deriving DecidableEq, Repr

def SealMode.epkLen : SealMode → Nat
  | .x25519 => 32
  | .mlkem => 0

/-- `viewTag 1 | frag 4 | epk`. -/
def SealMode.overhead (m : SealMode) : Nat := 1 + 4 + m.epkLen

theorem SealMode.overhead_le (m : SealMode) : m.overhead ≤ maxSealOverhead := by
  cases m <;> decide

/-- The plaintext of an `L`-byte sealed part. `frag` is the fragment header (`seq:2 | len:2`, ASSUMED);
`payload` is payload-or-padding, filling the rest. -/
structure Plaintext (m : SealMode) (L : Nat) where
  viewTag : UInt8
  frag : Blob 4
  epk : Blob m.epkLen
  payload : Blob (L - m.overhead)
  deriving DecidableEq

def Plaintext.encode {m : SealMode} {L : Nat} (p : Plaintext m L) : List UInt8 :=
  p.viewTag :: (p.frag.val ++ p.epk.val ++ p.payload.val)

theorem Plaintext.encode_length {m : SealMode} {L : Nat} (h : m.overhead ≤ L) (p : Plaintext m L) :
    p.encode.length = L := by
  simp [Plaintext.encode, p.frag.property, p.epk.property, p.payload.property, SealMode.overhead] at h ⊢
  omega

def Plaintext.decode (m : SealMode) (L : Nat) : List UInt8 → Option (Plaintext m L)
  | [] => none
  | v :: rest =>
    if hl : rest.length = 4 + m.epkLen + (L - m.overhead) then
      some ⟨v, ⟨rest.take 4, by simp; omega⟩, ⟨(rest.drop 4).take m.epkLen, by simp; omega⟩,
        ⟨rest.drop (4 + m.epkLen), by simp; omega⟩⟩
    else none

theorem Plaintext.decode_encode {m : SealMode} {L : Nat} (p : Plaintext m L) :
    Plaintext.decode m L p.encode = some p := by
  obtain ⟨v, f, e, pl⟩ := p
  have hf := f.property; have he := e.property; have hp := pl.property
  simp only [Plaintext.encode, Plaintext.decode, List.length_append, hf, he, hp, ↓reduceDIte,
    Option.some.injEq, Plaintext.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_⟩ <;> apply Blob.ext
  · simp [hf]
  · simp [hf, he]
  · simp [List.drop_append, hf, he]

theorem Plaintext.decode_canonical {m : SealMode} {L : Nat} {bytes : List UInt8} {p : Plaintext m L}
    (accepted : Plaintext.decode m L bytes = some p) : p.encode = bytes := by
  match bytes, accepted with
  | v :: rest, accepted =>
    simp only [Plaintext.decode] at accepted
    split at accepted
    · cases accepted
      simp only [Plaintext.encode, List.cons.injEq, true_and]
      rw [← List.drop_drop, List.append_assoc, List.take_append_drop, List.take_append_drop]
    · cases accepted

theorem Plaintext.encode_injective {m : SealMode} {L : Nat} :
    Function.Injective (Plaintext.encode (m := m) (L := L)) := by
  intro a b h
  have := Plaintext.decode_encode a
  rw [h, Plaintext.decode_encode b] at this
  exact (Option.some.inj this).symm

/-- The refusing pole: a sealed part of the wrong length has no plaintext. -/
theorem Plaintext.decode_refuses_length {m : SealMode} {L : Nat} (hm : m.overhead ≤ L)
    {bytes : List UInt8} (h : bytes.length ≠ L) : Plaintext.decode m L bytes = none := by
  cases hd : Plaintext.decode m L bytes with
  | none => rfl
  | some p => exact absurd ((Plaintext.decode_canonical hd) ▸ Plaintext.encode_length hm p) h

/-- Payload bytes per regular cell. -/
def Profile.payloadCap (P : Profile) (m : SealMode) : Nat := P.sealedLen - m.overhead
/-- Payload bytes per duty cell. -/
def Profile.dutyPayloadCap (P : Profile) (m : SealMode) : Nat := P.dutySealedLen - m.overhead

/-- §2.2's capacities: **195 / 227 B** per regular cell at P0/P1 (X25519 / ML-KEM mode), **963 / 995 B**
at P2; the duty cell's sealed part carries **35 / 67 B** at P0/P1 and 803 / 835 B at P2. -/
theorem payload_capacities :
    P1.payloadCap .x25519 = 195 ∧ P1.payloadCap .mlkem = 227 ∧
    P0.payloadCap .x25519 = 195 ∧ P0.payloadCap .mlkem = 227 ∧
    P2.payloadCap .x25519 = 963 ∧ P2.payloadCap .mlkem = 995 ∧
    P1.dutyPayloadCap .x25519 = 35 ∧ P1.dutyPayloadCap .mlkem = 67 ∧
    P2.dutyPayloadCap .x25519 = 803 ∧ P2.dutyPayloadCap .mlkem = 835 := by decide +kernel

/-- Every plaintext fits its sealed part at every class (both layouts, both modes) — the reason
`Profile.fits` asks for `maxSealOverhead` in the duty cell. -/
theorem plaintext_fits (P : Profile) (m : SealMode) :
    m.overhead ≤ P.sealedLen ∧ m.overhead ≤ P.dutySealedLen := by
  have := P.C_ge; have := m.overhead_le
  rw [P.sealedLen_eq, P.dutySealedLen_eq]
  simp only [maxSealOverhead] at *
  omega

/-! ## Byte entry points (`@[export]`) -/

/-- The published classes by id: `0` P0 · `1` P1 · `2` P1 phone · `3` P2. -/
def profileOfId : UInt8 → Option Profile
  | 0 => some P0
  | 1 => some P1
  | 2 => some P1phone
  | 3 => some P2
  | _ => none

/-- The codec as a byte function: `decodeCellBytesList id bytes` refuses with the empty array (unknown class
or not `C` bytes) and otherwise answers `[kind] ++ bytes`, `kind` `1` regular · `2` duty — the input
echoed is the cell's unique encoding (`cell_decode_canonical`). -/
def decodeCellBytesList (pid : UInt8) (bytes : List UInt8) : List UInt8 :=
  match profileOfId pid with
  | none => []
  | some P =>
    match Cell.decode P bytes with
    | none => []
    | some c => (if c.body.isDuty then 2 else 1) :: c.encode

/-- Encode from fields: `header 8 ++ body (C − 8)` assembled through `Cell.ofRaw` (the tick selects the
layout); the empty array when the class is unknown or the lengths are wrong. -/
def encodeCellBytesList (pid : UInt8) (header body : List UInt8) : List UInt8 :=
  match profileOfId pid with
  | none => []
  | some P =>
    match Header.decode header with
    | some (h, []) =>
      if hl : body.length = P.bodyLen then (Cell.ofRaw (P := P) h ⟨body, hl⟩).encode else []
    | _ => []

@[export minidregg_channel_cell_encode]
def encodeCellBytes (pid : UInt8) (header body : ByteArray) : ByteArray :=
  ⟨(encodeCellBytesList pid header.toList body.toList).toArray⟩

theorem decodeCellBytesList_accepts {P : Profile} {pid : UInt8} (hp : profileOfId pid = some P) (c : Cell P) :
    decodeCellBytesList pid c.encode = (if c.body.isDuty then 2 else 1) :: c.encode := by
  simp [decodeCellBytesList, hp, cell_decode_encode]

theorem decodeCellBytesList_refuses {P : Profile} {pid : UInt8} (hp : profileOfId pid = some P)
    {bytes : List UInt8} (h : bytes.length ≠ P.C) : decodeCellBytesList pid bytes = [] := by
  simp [decodeCellBytesList, hp, cell_decode_refuses_length h]

/-! ## Smoke: one P1 cell (256 B) and one P2 cell (1,024 B), by `decide` -/

namespace Smoke

def p1Header : Header := ⟨⟨7, by decide +kernel⟩, ⟨300, by decide +kernel⟩, ⟨5, by decide +kernel⟩, ⟨2, by decide +kernel⟩⟩
def p2Header : Header := ⟨⟨7, by decide +kernel⟩, ⟨300, by decide +kernel⟩, ⟨0, by decide +kernel⟩, ⟨513, by decide +kernel⟩⟩

/-- A P1 regular cell (tick 5). -/
def p1Cell : Cell P1 :=
  { header := p1Header
    body := .regular ⟨⟨List.replicate 232 0xAB, by decide +kernel⟩, ⟨List.replicate 16 0x5C, by decide +kernel⟩⟩
    layout := by decide +kernel }

/-- A P2 duty cell (tick 0). -/
def p2Cell : Cell P2 :=
  { header := p2Header
    body := .duty ⟨⟨List.replicate 96 1, by decide +kernel⟩, ⟨List.replicate 32 2, by decide +kernel⟩,
      ⟨List.replicate 32 3, by decide +kernel⟩, ⟨List.replicate 840 4, by decide +kernel⟩, ⟨List.replicate 16 5, by decide +kernel⟩⟩
    layout := by decide +kernel }

theorem p1Cell_size : p1Cell.encode.length = 256 := by decide +kernel
theorem p2Cell_size : p2Cell.encode.length = 1024 := by decide +kernel
theorem p1Cell_roundtrip : Cell.decode P1 p1Cell.encode = some p1Cell := by decide +kernel
theorem p2Cell_roundtrip : Cell.decode P2 p2Cell.encode = some p2Cell := by decide +kernel
/-- The header's bytes on the wire: domain 7, epoch 300 = `0x012C`, tick 5, slot 2. -/
theorem p1Cell_header_bytes : p1Cell.encode.take 8 = [0, 7, 1, 44, 0, 5, 0, 2] := by decide +kernel
/-- One byte short and one byte long both refuse. -/
theorem p1_short_refused : Cell.decode P1 (p1Cell.encode.take 255) = none := by decide +kernel
theorem p1_long_refused : Cell.decode P1 (p1Cell.encode ++ [0]) = none := by decide +kernel
/-- The class is not in the bytes — it is the domain's, published (§3) — so a 256-byte P1 cell read at
P2 refuses by length alone. -/
theorem p1_bytes_refused_at_p2 : Cell.decode P2 p1Cell.encode = none := by decide +kernel
/-- The byte entry point on the same cells: kind `1` (regular) for P1, `2` (duty) for P2. -/
theorem p1_export_kind : (decodeCellBytesList 1 p1Cell.encode).head? = some 1 := by decide +kernel
theorem p2_export_kind : (decodeCellBytesList 3 p2Cell.encode).head? = some 2 := by decide +kernel

end Smoke


end Minidregg.Theory.Channel
