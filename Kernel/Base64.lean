/-
# Kernel.Base64 — the one base64 codec (RFC 4648 §4, standard alphabet)

Two grammars over one alphabet, each total, each with both round trips:

* `b64Encode` / `b64Decode`: whole 3-byte groups, no padding. The enrollment
  memo uses it (a 51-byte ssh blob is exactly 68 characters).
  `b64Decode_b64Encode` and `b64Encode_b64Decode` say the grammar is canonical.
* `encode` / `decode`: padded. Every byte string encodes; a final group of one
  or two bytes carries `==` or `=`, and its unused low bits must be zero.
  `decode_encode` says every byte string round-trips; `encode_decode` says
  `decode` accepts exactly the canonical encodings (no non-zero spare bits,
  no padding except in the final group, no other alphabet). fn E1 bodies and
  the selected-release articles use it.

`encode_eq_b64Encode` ties the two on whole groups, so there is one encoder.
This replaces `FnPortableSource.decodeGroups` (a `partial def`, so nothing
could be proved about it) and the base64 section that lived in
`Kernel/PayEnrolMemo.lean`.
-/
import Theory.AxiomPin

namespace Minidregg.Kernel.Base64

set_option autoImplicit false

/-! ## The alphabet -/

def b64Char (n : Nat) : UInt8 :=
  if n < 26 then UInt8.ofNat (65 + n)
  else if n < 52 then UInt8.ofNat (71 + n)
  else if n < 62 then UInt8.ofNat (n - 4)
  else if n = 62 then 43 else 47

def b64Val (c : UInt8) : Option Nat :=
  if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then some (c.toNat - 65)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then some (c.toNat - 71)
  else if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat + 4)
  else if c.toNat = 43 then some 62
  else if c.toNat = 47 then some 63
  else none

/-- `'='`. -/
def pad : UInt8 := 61

theorem b64Val_b64Char_table : ∀ n, n < 64 → b64Val (b64Char n) = some n := by decide

def b64Inverts (k : Nat) : Bool :=
  match b64Val (UInt8.ofNat k) with
  | some n => decide (n < 64) && b64Char n == UInt8.ofNat k
  | none => true

theorem b64Char_b64Val_table : ∀ k, k < 256 → b64Inverts k = true := by decide +kernel

theorem b64Char_b64Val {c : UInt8} {n : Nat} (h : b64Val c = some n) :
    n < 64 ∧ b64Char n = c := by
  have table := b64Char_b64Val_table c.toNat c.toNat_lt
  simp only [b64Inverts, UInt8.ofNat_toNat, h, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at table
  exact table

theorem b64Val_pad : b64Val pad = none := by decide

theorem b64Char_ne_pad : ∀ n, n < 64 → b64Char n ≠ pad := by decide

/-! ## Whole groups, no padding -/

def b64Encode : List UInt8 → List UInt8
  | b₀ :: b₁ :: b₂ :: rest =>
      b64Char (b₀.toNat / 4) :: b64Char (b₀.toNat % 4 * 16 + b₁.toNat / 16) ::
        b64Char (b₁.toNat % 16 * 4 + b₂.toNat / 64) :: b64Char (b₂.toNat % 64) :: b64Encode rest
  | _ => []

def b64Decode : List UInt8 → Option (List UInt8)
  | [] => some []
  | c₀ :: c₁ :: c₂ :: c₃ :: rest =>
      match b64Val c₀, b64Val c₁, b64Val c₂, b64Val c₃, b64Decode rest with
      | some s₀, some s₁, some s₂, some s₃, some tail =>
          some (UInt8.ofNat (s₀ * 4 + s₁ / 16) :: UInt8.ofNat (s₁ % 16 * 16 + s₂ / 4) ::
            UInt8.ofNat (s₂ % 4 * 64 + s₃) :: tail)
      | _, _, _, _, _ => none
  | _ => none

/-- One decoded group re-encodes to its four characters. Shared by both grammars. -/
theorem group_reencodes {c₀ c₁ c₂ c₃ : UInt8} {s₀ s₁ s₂ s₃ : Nat}
    (h₀ : b64Val c₀ = some s₀) (h₁ : b64Val c₁ = some s₁)
    (h₂ : b64Val c₂ = some s₂) (h₃ : b64Val c₃ = some s₃) :
    b64Char ((UInt8.ofNat (s₀ * 4 + s₁ / 16)).toNat / 4) = c₀ ∧
    b64Char ((UInt8.ofNat (s₀ * 4 + s₁ / 16)).toNat % 4 * 16 +
      (UInt8.ofNat (s₁ % 16 * 16 + s₂ / 4)).toNat / 16) = c₁ ∧
    b64Char ((UInt8.ofNat (s₁ % 16 * 16 + s₂ / 4)).toNat % 16 * 4 +
      (UInt8.ofNat (s₂ % 4 * 64 + s₃)).toNat / 64) = c₂ ∧
    b64Char ((UInt8.ofNat (s₂ % 4 * 64 + s₃)).toNat % 64) = c₃ := by
  obtain ⟨l₀, e₀⟩ := b64Char_b64Val h₀
  obtain ⟨l₁, e₁⟩ := b64Char_b64Val h₁
  obtain ⟨l₂, e₂⟩ := b64Char_b64Val h₂
  obtain ⟨l₃, e₃⟩ := b64Char_b64Val h₃
  have v₀ : (UInt8.ofNat (s₀ * 4 + s₁ / 16)).toNat = s₀ * 4 + s₁ / 16 :=
    UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  have v₁ : (UInt8.ofNat (s₁ % 16 * 16 + s₂ / 4)).toNat = s₁ % 16 * 16 + s₂ / 4 :=
    UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  have v₂ : (UInt8.ofNat (s₂ % 4 * 64 + s₃)).toNat = s₂ % 4 * 64 + s₃ :=
    UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
  rw [v₀, v₁, v₂]
  have a₀ : (s₀ * 4 + s₁ / 16) / 4 = s₀ := by omega
  have a₁ : (s₀ * 4 + s₁ / 16) % 4 * 16 + (s₁ % 16 * 16 + s₂ / 4) / 16 = s₁ := by omega
  have a₂ : (s₁ % 16 * 16 + s₂ / 4) % 16 * 4 + (s₂ % 4 * 64 + s₃) / 64 = s₂ := by omega
  have a₃ : (s₂ % 4 * 64 + s₃) % 64 = s₃ := by omega
  rw [a₀, a₁, a₂, a₃]
  exact ⟨e₀, e₁, e₂, e₃⟩

/-- Three bytes survive one group's encode and decode. -/
theorem group_redecodes (b₀ b₁ b₂ : UInt8) :
    b64Val (b64Char (b₀.toNat / 4)) = some (b₀.toNat / 4) ∧
    b64Val (b64Char (b₀.toNat % 4 * 16 + b₁.toNat / 16)) =
      some (b₀.toNat % 4 * 16 + b₁.toNat / 16) ∧
    b64Val (b64Char (b₁.toNat % 16 * 4 + b₂.toNat / 64)) =
      some (b₁.toNat % 16 * 4 + b₂.toNat / 64) ∧
    b64Val (b64Char (b₂.toNat % 64)) = some (b₂.toNat % 64) ∧
    UInt8.ofNat (b₀.toNat / 4 * 4 + (b₀.toNat % 4 * 16 + b₁.toNat / 16) / 16) = b₀ ∧
    UInt8.ofNat ((b₀.toNat % 4 * 16 + b₁.toNat / 16) % 16 * 16 +
      (b₁.toNat % 16 * 4 + b₂.toNat / 64) / 4) = b₁ ∧
    UInt8.ofNat ((b₁.toNat % 16 * 4 + b₂.toNat / 64) % 4 * 64 + b₂.toNat % 64) = b₂ := by
  have h₀ := b₀.toNat_lt
  have h₁ := b₁.toNat_lt
  have h₂ := b₂.toNat_lt
  refine ⟨b64Val_b64Char_table _ (by omega), b64Val_b64Char_table _ (by omega),
    b64Val_b64Char_table _ (by omega), b64Val_b64Char_table _ (by omega), ?_, ?_, ?_⟩
  · have e : b₀.toNat / 4 * 4 + (b₀.toNat % 4 * 16 + b₁.toNat / 16) / 16 = b₀.toNat := by omega
    rw [e, UInt8.ofNat_toNat]
  · have e : (b₀.toNat % 4 * 16 + b₁.toNat / 16) % 16 * 16 +
        (b₁.toNat % 16 * 4 + b₂.toNat / 64) / 4 = b₁.toNat := by omega
    rw [e, UInt8.ofNat_toNat]
  · have e : (b₁.toNat % 16 * 4 + b₂.toNat / 64) % 4 * 64 + b₂.toNat % 64 = b₂.toNat := by
      omega
    rw [e, UInt8.ofNat_toNat]

theorem b64Decode_b64Encode : ∀ (bytes : List UInt8), bytes.length % 3 = 0 →
    b64Decode (b64Encode bytes) = some bytes
  | [], _ => rfl
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | b₀ :: b₁ :: b₂ :: rest, h => by
      have tail := b64Decode_b64Encode rest (by simp at h; omega)
      obtain ⟨d₀, d₁, d₂, d₃, r₀, r₁, r₂⟩ := group_redecodes b₀ b₁ b₂
      simp only [b64Encode, b64Decode, d₀, d₁, d₂, d₃, tail, r₀, r₁, r₂]

theorem b64Encode_b64Decode : ∀ {text bytes : List UInt8},
    b64Decode text = some bytes → b64Encode bytes = text
  | [], bytes, h => by simp [b64Decode] at h; subst h; rfl
  | [_], _, h => by simp [b64Decode] at h
  | [_, _], _, h => by simp [b64Decode] at h
  | [_, _, _], _, h => by simp [b64Decode] at h
  | c₀ :: c₁ :: c₂ :: c₃ :: rest, bytes, h => by
      simp only [b64Decode] at h
      match h₀ : b64Val c₀, h₁ : b64Val c₁, h₂ : b64Val c₂, h₃ : b64Val c₃,
          ht : b64Decode rest with
      | some s₀, some s₁, some s₂, some s₃, some tail =>
          rw [h₀, h₁, h₂, h₃, ht] at h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨e₀, e₁, e₂, e₃⟩ := group_reencodes h₀ h₁ h₂ h₃
          simp only [b64Encode, e₀, e₁, e₂, e₃, b64Encode_b64Decode ht]
      | none, _, _, _, _ => rw [h₀] at h; simp at h
      | some _, none, _, _, _ => rw [h₀, h₁] at h; simp at h
      | some _, some _, none, _, _ => rw [h₀, h₁, h₂] at h; simp at h
      | some _, some _, some _, none, _ => rw [h₀, h₁, h₂, h₃] at h; simp at h
      | some _, some _, some _, some _, none => rw [h₀, h₁, h₂, h₃, ht] at h; simp at h

theorem b64Encode_length : ∀ (bytes : List UInt8), bytes.length % 3 = 0 →
    (b64Encode bytes).length = 4 * (bytes.length / 3)
  | [], _ => rfl
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | _ :: _ :: _ :: rest, h => by
      have tail := b64Encode_length rest (by simp at h; omega)
      simp only [b64Encode, List.length_cons, tail]
      omega

/-! ## Padded -/

def encode : List UInt8 → List UInt8
  | b₀ :: b₁ :: b₂ :: rest =>
      b64Char (b₀.toNat / 4) :: b64Char (b₀.toNat % 4 * 16 + b₁.toNat / 16) ::
        b64Char (b₁.toNat % 16 * 4 + b₂.toNat / 64) :: b64Char (b₂.toNat % 64) :: encode rest
  | [b₀, b₁] =>
      [b64Char (b₀.toNat / 4), b64Char (b₀.toNat % 4 * 16 + b₁.toNat / 16),
        b64Char (b₁.toNat % 16 * 4), pad]
  | [b₀] => [b64Char (b₀.toNat / 4), b64Char (b₀.toNat % 4 * 16), pad, pad]
  | [] => []

/-- The final group `c₀ c₁ c₂ =`: one byte when `c₂` is `=` too, else two.
Spare low bits must be zero, so each byte string has one encoding. -/
def decodeFinal (c₀ c₁ c₂ : UInt8) : Option (List UInt8) :=
  match b64Val c₀, b64Val c₁ with
  | some s₀, some s₁ =>
      if c₂ = pad then
        if s₁ % 16 = 0 then some [UInt8.ofNat (s₀ * 4 + s₁ / 16)] else none
      else
        match b64Val c₂ with
        | some s₂ =>
            if s₂ % 4 = 0 then
              some [UInt8.ofNat (s₀ * 4 + s₁ / 16), UInt8.ofNat (s₁ % 16 * 16 + s₂ / 4)]
            else none
        | none => none
  | _, _ => none

def decode : List UInt8 → Option (List UInt8)
  | [] => some []
  | c₀ :: c₁ :: c₂ :: c₃ :: rest =>
      if rest = [] ∧ c₃ = pad then decodeFinal c₀ c₁ c₂
      else
        match b64Val c₀, b64Val c₁, b64Val c₂, b64Val c₃, decode rest with
        | some s₀, some s₁, some s₂, some s₃, some tail =>
            some (UInt8.ofNat (s₀ * 4 + s₁ / 16) :: UInt8.ofNat (s₁ % 16 * 16 + s₂ / 4) ::
              UInt8.ofNat (s₂ % 4 * 64 + s₃) :: tail)
        | _, _, _, _, _ => none
  | _ => none

theorem decode_encode : ∀ (bytes : List UInt8), decode (encode bytes) = some bytes
  | [] => rfl
  | [b₀] => by
      have h₀ := b₀.toNat_lt
      have v₀ := b64Val_b64Char_table (b₀.toNat / 4) (by omega)
      have v₁ := b64Val_b64Char_table (b₀.toNat % 4 * 16) (by omega)
      have e : b₀.toNat / 4 * 4 + b₀.toNat % 4 * 16 / 16 = b₀.toNat := by omega
      have z : b₀.toNat % 4 * 16 % 16 = 0 := by omega
      simp only [encode, decode, decodeFinal, v₀, v₁, z, e, UInt8.ofNat_toNat, and_self,
        if_true]
  | [b₀, b₁] => by
      have h₀ := b₀.toNat_lt
      have h₁ := b₁.toNat_lt
      have v₀ := b64Val_b64Char_table (b₀.toNat / 4) (by omega)
      have v₁ := b64Val_b64Char_table (b₀.toNat % 4 * 16 + b₁.toNat / 16) (by omega)
      have v₂ := b64Val_b64Char_table (b₁.toNat % 16 * 4) (by omega)
      have n₂ := b64Char_ne_pad (b₁.toNat % 16 * 4) (by omega)
      have e₀ : b₀.toNat / 4 * 4 + (b₀.toNat % 4 * 16 + b₁.toNat / 16) / 16 = b₀.toNat := by
        omega
      have e₁ : (b₀.toNat % 4 * 16 + b₁.toNat / 16) % 16 * 16 + b₁.toNat % 16 * 4 / 4 =
          b₁.toNat := by omega
      have z : b₁.toNat % 16 * 4 % 4 = 0 := by omega
      simp only [encode, decode, decodeFinal, v₀, v₁, v₂, n₂, z, e₀, e₁, UInt8.ofNat_toNat,
        and_self, if_true, if_false]
  | b₀ :: b₁ :: b₂ :: rest => by
      have h₂ := b₂.toNat_lt
      have n₃ := b64Char_ne_pad (b₂.toNat % 64) (by omega)
      obtain ⟨d₀, d₁, d₂, d₃, r₀, r₁, r₂⟩ := group_redecodes b₀ b₁ b₂
      simp only [encode, decode, n₃, and_false, if_false, d₀, d₁, d₂, d₃,
        decode_encode rest, r₀, r₁, r₂]

theorem decodeFinal_reencodes {c₀ c₁ c₂ : UInt8} {bytes : List UInt8}
    (h : decodeFinal c₀ c₁ c₂ = some bytes) : encode bytes = [c₀, c₁, c₂, pad] := by
  unfold decodeFinal at h
  match h₀ : b64Val c₀, h₁ : b64Val c₁ with
  | some s₀, some s₁ =>
      rw [h₀, h₁] at h
      obtain ⟨l₀, e₀⟩ := b64Char_b64Val h₀
      obtain ⟨l₁, e₁⟩ := b64Char_b64Val h₁
      by_cases p : c₂ = pad
      · by_cases z : s₁ % 16 = 0
        · simp only [p, z, if_true, Option.some.injEq] at h
          subst h
          have v : (UInt8.ofNat (s₀ * 4 + s₁ / 16)).toNat = s₀ * 4 + s₁ / 16 :=
            UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
          have a₀ : (s₀ * 4 + s₁ / 16) / 4 = s₀ := by omega
          have a₁ : (s₀ * 4 + s₁ / 16) % 4 * 16 = s₁ := by omega
          simp only [encode, v, a₀, a₁, e₀, e₁, p]
        · simp [p, z] at h
      · match h₂ : b64Val c₂ with
        | some s₂ =>
            obtain ⟨l₂, e₂⟩ := b64Char_b64Val h₂
            by_cases z : s₂ % 4 = 0
            · simp only [p, h₂, z, if_true, if_false, Option.some.injEq] at h
              subst h
              have v₀ : (UInt8.ofNat (s₀ * 4 + s₁ / 16)).toNat = s₀ * 4 + s₁ / 16 :=
                UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
              have v₁ : (UInt8.ofNat (s₁ % 16 * 16 + s₂ / 4)).toNat = s₁ % 16 * 16 + s₂ / 4 :=
                UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
              have a₀ : (s₀ * 4 + s₁ / 16) / 4 = s₀ := by omega
              have a₁ : (s₀ * 4 + s₁ / 16) % 4 * 16 + (s₁ % 16 * 16 + s₂ / 4) / 16 = s₁ := by
                omega
              have a₂ : (s₁ % 16 * 16 + s₂ / 4) % 16 * 4 = s₂ := by omega
              simp only [encode, v₀, v₁, a₀, a₁, a₂, e₀, e₁, e₂]
            · simp [p, h₂, z] at h
        | none => simp [p, h₂] at h
  | none, _ => rw [h₀] at h; simp at h
  | some _, none => rw [h₀, h₁] at h; simp at h

/-- Canonicity: `decode` accepts exactly the encodings `encode` produces. -/
theorem encode_decode : ∀ {text bytes : List UInt8},
    decode text = some bytes → encode bytes = text
  | [], bytes, h => by simp [decode] at h; subst h; rfl
  | [_], _, h => by simp [decode] at h
  | [_, _], _, h => by simp [decode] at h
  | [_, _, _], _, h => by simp [decode] at h
  | c₀ :: c₁ :: c₂ :: c₃ :: rest, bytes, h => by
      simp only [decode] at h
      by_cases f : rest = [] ∧ c₃ = pad
      · rw [if_pos f] at h
        obtain ⟨r, p⟩ := f
        subst r; subst p
        exact decodeFinal_reencodes h
      · rw [if_neg f] at h
        match h₀ : b64Val c₀, h₁ : b64Val c₁, h₂ : b64Val c₂, h₃ : b64Val c₃,
            ht : decode rest with
        | some s₀, some s₁, some s₂, some s₃, some tail =>
            rw [h₀, h₁, h₂, h₃, ht] at h
            simp only [Option.some.injEq] at h
            subst h
            obtain ⟨e₀, e₁, e₂, e₃⟩ := group_reencodes h₀ h₁ h₂ h₃
            simp only [encode, e₀, e₁, e₂, e₃, encode_decode ht]
        | none, _, _, _, _ => rw [h₀] at h; simp at h
        | some _, none, _, _, _ => rw [h₀, h₁] at h; simp at h
        | some _, some _, none, _, _ => rw [h₀, h₁, h₂] at h; simp at h
        | some _, some _, some _, none, _ => rw [h₀, h₁, h₂, h₃] at h; simp at h
        | some _, some _, some _, some _, none => rw [h₀, h₁, h₂, h₃, ht] at h; simp at h

/-- On whole groups the padded encoder is the unpadded one. -/
theorem encode_eq_b64Encode : ∀ (bytes : List UInt8), bytes.length % 3 = 0 →
    encode bytes = b64Encode bytes
  | [], _ => rfl
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | _ :: _ :: _ :: rest, h => by
      simp only [encode, b64Encode, encode_eq_b64Encode rest (by simp at h; omega)]

/-- Whole groups encode independently of what follows them, so a body folded
into lines of `3k` bytes is the line-by-line concatenation of one encoding. -/
theorem encode_append : ∀ (front back : List UInt8), front.length % 3 = 0 →
    encode (front ++ back) = encode front ++ encode back
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h
  | _ :: _ :: _ :: rest, back, h => by
      simp only [List.cons_append, encode, encode_append rest back (by simp at h; omega)]

/-! ## Lines

fn bodies fold base64 at 76 characters (57 bytes) per CRLF line. -/

def lineBytes : Nat := 57

/-- The input cut into 57-byte pieces, each a whole number of groups but the last. -/
def chunks (bytes : List UInt8) : List (List UInt8) :=
  if bytes = [] then []
  else bytes.take lineBytes :: chunks (bytes.drop lineBytes)
termination_by bytes.length
decreasing_by
  have : bytes.length ≠ 0 := by simpa [List.length_eq_zero_iff] using ‹¬bytes = []›
  simp only [List.length_drop, lineBytes]
  omega

theorem chunks_flatten (bytes : List UInt8) : (chunks bytes).flatten = bytes := by
  rw [chunks]
  split
  · next h => simp [h]
  · simp only [List.flatten_cons, chunks_flatten (bytes.drop lineBytes), List.take_append_drop]
termination_by bytes.length
decreasing_by
  have : bytes.length ≠ 0 := by simpa [List.length_eq_zero_iff] using ‹¬bytes = []›
  simp only [List.length_drop, lineBytes]
  omega

/-- Lines joined by CRLF, with a final CRLF: the fn E1 and selected-release body. -/
def encodeLines (bytes : List UInt8) : String :=
  String.intercalate "\r\n"
      ((chunks bytes).map fun line => String.ofList ((encode line).map fun b => Char.ofNat b.toNat)) ++
    "\r\n"

/-! ## The standard's own vectors, and refusals with teeth

RFC 4648 §10's test vectors, and three inputs `decode` must refuse: a final
group with non-zero spare bits, padding before the final group, and a
character outside the alphabet. -/

theorem rfc4648_vectors :
    encode "".toUTF8.toList = "".toUTF8.toList ∧
    encode "f".toUTF8.toList = "Zg==".toUTF8.toList ∧
    encode "fo".toUTF8.toList = "Zm8=".toUTF8.toList ∧
    encode "foo".toUTF8.toList = "Zm9v".toUTF8.toList ∧
    encode "foob".toUTF8.toList = "Zm9vYg==".toUTF8.toList ∧
    encode "fooba".toUTF8.toList = "Zm9vYmE=".toUTF8.toList ∧
    encode "foobar".toUTF8.toList = "Zm9vYmFy".toUTF8.toList := by decide +kernel

theorem decode_refuses_spare_bits : decode "Zh==".toUTF8.toList = none := by decide +kernel

theorem decode_refuses_inner_padding : decode "Zg==Zm9v".toUTF8.toList = none := by decide +kernel

theorem decode_refuses_alphabet : decode "Zm9-".toUTF8.toList = none := by decide +kernel

#assert_axioms b64Val_b64Char_table b64Char_b64Val_table b64Char_b64Val b64Val_pad
  b64Char_ne_pad group_reencodes group_redecodes
  b64Decode_b64Encode b64Encode_b64Decode b64Encode_length
  decode_encode decodeFinal_reencodes encode_decode encode_eq_b64Encode encode_append
  chunks_flatten rfc4648_vectors decode_refuses_spare_bits decode_refuses_inner_padding
  decode_refuses_alphabet

end Minidregg.Kernel.Base64
