/-
# Kernel.PayEnrolMemo — the self-enrollment memo (PAY §11.3), its frames and refusals

The memo a friend attaches to the enrollment payment is 400 ASCII bytes:

```
enrol:v1:<mini-pubkey hex 64>:<ssh-ed25519 blob base64 68>:<mini-sig hex 128>:<ssh-sig hex 128>
```

* hex is lowercase only; base64 is the standard alphabet with no padding (the
  51-byte blob is exactly 68 characters, with no spare bits), so the grammar is
  canonical: `parse_canonical` says an accepted memo is the encoding of its
  value, and `parse_encode` that every well-formed value is accepted.
* The ssh blob must be one `ssh-ed25519` wire blob,
  `string "ssh-ed25519" ‖ string key32`; the value keeps only the 32-byte key.
* `miniFrame` is what the Mini key signs (`mini-sig`):
  `"DREGG/PAY/ENROL/POSSESSION/v1" ‖ mint(32) ‖ enrolAddress(32) ‖ sshBlob(51)`.
* `sshsigMessage` is what `ssh-keygen -Y sign -n dregg-enrol@v1` signs
  (`ssh-sig`): `mint(32) ‖ enrolAddress(32) ‖ miniKey(32)`.  SSHSIG signs
  `sshsigSignedData namespace (SHA-512 message)`; Lean has no SHA-512, so the
  native verifier (`verify-sshsig`) computes the digest and this module fixes
  every other byte (`sshsig_signed_data_fixture` pins it to a real
  `ssh-keygen` run, the same bytes the Rust tests assert).

Every refusal is named (`Refusal`), and each one has a concrete kernel-decided
pole below.  A payment's memo reaches the kernel as a `MemoField`: the watcher
reports the raw bytes of the one memo instruction, or that there was none, or
that there were two or more (`unbound`), or that the one memo was not UTF-8 or
too long (`invalid`).
-/
import Compiler.ResourceBirthCodec
import Kernel.PayTariff

namespace Minidregg.Kernel.PayEnrolMemo

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.PayTariff (Address32)

set_option autoImplicit false

/-! ## Lowercase hex -/

def hexChar (n : Nat) : UInt8 := if n < 10 then UInt8.ofNat (48 + n) else UInt8.ofNat (87 + n)

def hexVal (c : UInt8) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else none

def hexEncode : List UInt8 → List UInt8
  | [] => []
  | b :: rest => hexChar (b.toNat / 16) :: hexChar (b.toNat % 16) :: hexEncode rest

def hexDecode : List UInt8 → Option (List UInt8)
  | [] => some []
  | [_] => none
  | hi :: lo :: rest =>
      match hexVal hi, hexVal lo, hexDecode rest with
      | some h, some l, some tail => some (UInt8.ofNat (16 * h + l) :: tail)
      | _, _, _ => none

theorem hexVal_hexChar_table : ∀ n, n < 16 → hexVal (hexChar n) = some n := by decide

def hexInverts (k : Nat) : Bool :=
  match hexVal (UInt8.ofNat k) with
  | some n => decide (n < 16) && hexChar n == UInt8.ofNat k
  | none => true

theorem hexChar_hexVal_table : ∀ k, k < 256 → hexInverts k = true := by decide +kernel

theorem uint8_ofNat_toNat (b : UInt8) : UInt8.ofNat b.toNat = b := UInt8.ofNat_toNat

theorem hexChar_hexVal {c : UInt8} {n : Nat} (h : hexVal c = some n) :
    n < 16 ∧ hexChar n = c := by
  have table := hexChar_hexVal_table c.toNat c.toNat_lt
  simp only [hexInverts, uint8_ofNat_toNat, h, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at table
  exact table

theorem hexEncode_length (bytes : List UInt8) : (hexEncode bytes).length = 2 * bytes.length := by
  induction bytes with
  | nil => rfl
  | cons b rest ih => simp [hexEncode, ih]; omega

theorem hexDecode_hexEncode (bytes : List UInt8) : hexDecode (hexEncode bytes) = some bytes := by
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
      have hi : b.toNat / 16 < 16 := by have := b.toNat_lt; omega
      have lo : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
      simp only [hexEncode, hexDecode, hexVal_hexChar_table _ hi, hexVal_hexChar_table _ lo, ih]
      have : 16 * (b.toNat / 16) + b.toNat % 16 = b.toNat := by omega
      rw [this, uint8_ofNat_toNat]

theorem hexEncode_hexDecode : ∀ {text bytes : List UInt8},
    hexDecode text = some bytes → hexEncode bytes = text
  | [], bytes, h => by simp [hexDecode] at h; subst h; rfl
  | [_], _, h => by simp [hexDecode] at h
  | hi :: lo :: rest, bytes, h => by
      simp only [hexDecode] at h
      match hh : hexVal hi, hl : hexVal lo, ht : hexDecode rest with
      | some n₁, some n₂, some tail =>
          rw [hh, hl, ht] at h
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨b₁, c₁⟩ := hexChar_hexVal hh
          obtain ⟨b₂, c₂⟩ := hexChar_hexVal hl
          have value : (UInt8.ofNat (16 * n₁ + n₂)).toNat = 16 * n₁ + n₂ := by
            exact UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
          simp only [hexEncode, value, hexEncode_hexDecode ht]
          have d : (16 * n₁ + n₂) / 16 = n₁ := by omega
          have m : (16 * n₁ + n₂) % 16 = n₂ := by omega
          rw [d, m, c₁, c₂]
      | none, _, _ => rw [hh] at h; simp at h
      | some _, none, _ => rw [hh, hl] at h; simp at h
      | some _, some _, none => rw [hh, hl, ht] at h; simp at h

/-! ## Standard base64, no padding, whole 3-byte groups -/

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

theorem b64Val_b64Char_table : ∀ n, n < 64 → b64Val (b64Char n) = some n := by decide

def b64Inverts (k : Nat) : Bool :=
  match b64Val (UInt8.ofNat k) with
  | some n => decide (n < 64) && b64Char n == UInt8.ofNat k
  | none => true

theorem b64Char_b64Val_table : ∀ k, k < 256 → b64Inverts k = true := by decide +kernel

theorem b64Char_b64Val {c : UInt8} {n : Nat} (h : b64Val c = some n) :
    n < 64 ∧ b64Char n = c := by
  have table := b64Char_b64Val_table c.toNat c.toNat_lt
  simp only [b64Inverts, uint8_ofNat_toNat, h, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at table
  exact table

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

theorem b64Decode_b64Encode : ∀ (bytes : List UInt8), bytes.length % 3 = 0 →
    b64Decode (b64Encode bytes) = some bytes
  | [], _ => rfl
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | b₀ :: b₁ :: b₂ :: rest, h => by
      have h₀ := b₀.toNat_lt
      have h₁ := b₁.toNat_lt
      have h₂ := b₂.toNat_lt
      have tail := b64Decode_b64Encode rest (by simp at h; omega)
      simp only [b64Encode, b64Decode,
        b64Val_b64Char_table _ (show b₀.toNat / 4 < 64 by omega),
        b64Val_b64Char_table _ (show b₀.toNat % 4 * 16 + b₁.toNat / 16 < 64 by omega),
        b64Val_b64Char_table _ (show b₁.toNat % 16 * 4 + b₂.toNat / 64 < 64 by omega),
        b64Val_b64Char_table _ (show b₂.toNat % 64 < 64 by omega), tail]
      have e₀ : b₀.toNat / 4 * 4 + (b₀.toNat % 4 * 16 + b₁.toNat / 16) / 16 = b₀.toNat := by omega
      have e₁ : (b₀.toNat % 4 * 16 + b₁.toNat / 16) % 16 * 16 +
          (b₁.toNat % 16 * 4 + b₂.toNat / 64) / 4 = b₁.toNat := by omega
      have e₂ : (b₁.toNat % 16 * 4 + b₂.toNat / 64) % 4 * 64 + b₂.toNat % 64 = b₂.toNat := by omega
      rw [e₀, e₁, e₂, uint8_ofNat_toNat, uint8_ofNat_toNat, uint8_ofNat_toNat]

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
          obtain ⟨l₀, e₀⟩ := b64Char_b64Val h₀
          obtain ⟨l₁, e₁⟩ := b64Char_b64Val h₁
          obtain ⟨l₂, e₂⟩ := b64Char_b64Val h₂
          obtain ⟨l₃, e₃⟩ := b64Char_b64Val h₃
          have v₀ : (UInt8.ofNat (s₀ * 4 + s₁ / 16)).toNat = s₀ * 4 + s₁ / 16 := by
            exact UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
          have v₁ : (UInt8.ofNat (s₁ % 16 * 16 + s₂ / 4)).toNat = s₁ % 16 * 16 + s₂ / 4 := by
            exact UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
          have v₂ : (UInt8.ofNat (s₂ % 4 * 64 + s₃)).toNat = s₂ % 4 * 64 + s₃ := by
            exact UInt8.toNat_ofNat_of_lt' (by simp only [UInt8.size]; omega)
          simp only [b64Encode, v₀, v₁, v₂, b64Encode_b64Decode ht]
          have a₀ : (s₀ * 4 + s₁ / 16) / 4 = s₀ := by omega
          have a₁ : (s₀ * 4 + s₁ / 16) % 4 * 16 + (s₁ % 16 * 16 + s₂ / 4) / 16 = s₁ := by omega
          have a₂ : (s₁ % 16 * 16 + s₂ / 4) % 16 * 4 + (s₂ % 4 * 64 + s₃) / 64 = s₂ := by omega
          have a₃ : (s₂ % 4 * 64 + s₃) % 64 = s₃ := by omega
          rw [a₀, a₁, a₂, a₃, e₀, e₁, e₂, e₃]
      | none, _, _, _, _ => rw [h₀] at h; simp at h
      | some _, none, _, _, _ => rw [h₀, h₁] at h; simp at h
      | some _, some _, none, _, _ => rw [h₀, h₁, h₂] at h; simp at h
      | some _, some _, some _, none, _ => rw [h₀, h₁, h₂, h₃] at h; simp at h
      | some _, some _, some _, some _, none => rw [h₀, h₁, h₂, h₃, ht] at h; simp at h

/-! ## The ssh-ed25519 wire blob -/

/-- `"ssh-ed25519"` as bytes. -/
def sshEd25519Name : List UInt8 := [115, 115, 104, 45, 101, 100, 50, 53, 53, 49, 57]

theorem sshEd25519Name_utf8 : sshEd25519Name = "ssh-ed25519".toUTF8.toList := by decide +kernel

/-- `string "ssh-ed25519" ‖ uint32 32`: the 19 bytes before the key. -/
def sshBlobPrefix : List UInt8 := [0, 0, 0, 11] ++ sshEd25519Name ++ [0, 0, 0, 32]

def sshBlobOf (key : List UInt8) : List UInt8 := sshBlobPrefix ++ key

/-- Exactly one ssh-ed25519 wire blob: the prefix and a 32-byte key. -/
def isEd25519Blob (blob : List UInt8) : Bool :=
  blob.length == 51 && blob.take 19 == sshBlobPrefix

/-! ## The memo -/

structure Memo where
  miniKey : List UInt8
  /-- The raw 32-byte Ed25519 key inside the ssh blob. -/
  sshKey : List UInt8
  miniSig : List UInt8
  sshSig : List UInt8
  deriving DecidableEq, Repr

def Memo.WellFormed (memo : Memo) : Prop :=
  memo.miniKey.length = 32 ∧ memo.sshKey.length = 32 ∧ memo.miniSig.length = 64 ∧
    memo.sshSig.length = 64

instance (memo : Memo) : Decidable memo.WellFormed := by
  unfold Memo.WellFormed
  infer_instance

def Memo.sshBlob (memo : Memo) : List UInt8 := sshBlobOf memo.sshKey

/-- The memo's refusals: all land in the journal as `memoMalformed`. -/
inductive Refusal
  /-- Not 400 bytes, not `enrol:`, or a separator out of place. -/
  | shape
  /-- `enrol:` but not `enrol:v1:`. -/
  | version
  | badMiniKey
  /-- Not base64 of one ssh-ed25519 blob (RSA, two keys, padding …). -/
  | badSshKey
  | badMiniSig
  | badSshSig
  deriving DecidableEq, Repr

/-- `"enrol:"` and `"v1:"` as bytes. -/
def enrolTag : List UInt8 := [101, 110, 114, 111, 108, 58]
def v1Tag : List UInt8 := [118, 49, 58]

theorem memoPrefix_utf8 : enrolTag ++ v1Tag = "enrol:v1:".toUTF8.toList := by decide +kernel

def separator : UInt8 := 58

def memoLength : Nat := 400

/-- Field widths before the last field: tag, version, mini key, `:`, ssh blob,
`:`, mini-sig, `:`.  The last field (the ssh-sig) is the remainder. -/
def fields : List Nat := [6, 3, 64, 1, 68, 1, 128, 1]

def cut : List Nat → List UInt8 → List (List UInt8)
  | [], rest => [rest]
  | n :: ns, bytes => bytes.take n :: cut ns (bytes.drop n)

theorem cut_flatten : ∀ (ns : List Nat) (bytes : List UInt8), (cut ns bytes).flatten = bytes
  | [], bytes => by simp [cut]
  | n :: ns, bytes => by simp [cut, cut_flatten ns]

theorem cut_append : ∀ (ns : List Nat) (parts : List (List UInt8)) (rest : List UInt8),
    parts.map List.length = ns → cut ns (parts.flatten ++ rest) = parts ++ [rest]
  | [], [], rest, _ => by simp [cut]
  | n :: ns, p :: ps, rest, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hp, hs⟩ := h
      subst hp
      simp [cut, List.append_assoc, cut_append ns ps rest hs]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

theorem cut_lengths : ∀ (ns : List Nat) (bytes : List UInt8), ns.sum ≤ bytes.length →
    (cut ns bytes).map List.length = ns ++ [bytes.length - ns.sum]
  | [], bytes, _ => by simp [cut]
  | n :: ns, bytes, h => by
      simp only [List.sum_cons] at h
      have hd : ns.sum ≤ (bytes.drop n).length := by rw [List.length_drop]; omega
      have rest := cut_lengths ns (bytes.drop n) hd
      rw [List.length_drop] at rest
      have taken : min n bytes.length = n := by omega
      simp only [cut, List.map_cons, rest, List.length_take, List.cons_append, List.sum_cons,
        taken, Nat.sub_sub]

def encode (memo : Memo) : List UInt8 :=
  [enrolTag, v1Tag, hexEncode memo.miniKey, [separator], b64Encode memo.sshBlob, [separator],
    hexEncode memo.miniSig, [separator]].flatten ++ hexEncode memo.sshSig

def fromOption {α : Type} (refusal : Refusal) : Option α → Except Refusal α
  | some value => .ok value
  | none => .error refusal

/-- The strict parser: tag, version, length and separators first (`shape`,
`version`), then each field in order. -/
def parse (bytes : List UInt8) : Except Refusal Memo :=
  match cut fields bytes with
  | [tag, version, miniHex, s₁, sshText, s₂, miniSigHex, s₃, sshSigHex] =>
      if tag ≠ enrolTag then .error .shape
      else if version ≠ v1Tag then .error .version
      else if bytes.length ≠ memoLength then .error .shape
      else if s₁ ≠ [separator] ∨ s₂ ≠ [separator] ∨ s₃ ≠ [separator] then .error .shape
      else
        match hexDecode miniHex with
        | none => .error .badMiniKey
        | some miniKey =>
          match b64Decode sshText with
          | none => .error .badSshKey
          | some blob =>
            if isEd25519Blob blob = false then .error .badSshKey
            else
              match hexDecode miniSigHex with
              | none => .error .badMiniSig
              | some miniSig =>
                match hexDecode sshSigHex with
                | none => .error .badSshSig
                | some sshSig => .ok ⟨miniKey, blob.drop 19, miniSig, sshSig⟩
  | _ => .error .shape

/-! ### Round trip and canonicity -/

theorem b64Encode_length : ∀ (bytes : List UInt8), bytes.length % 3 = 0 →
    (b64Encode bytes).length = 4 * (bytes.length / 3)
  | [], _ => rfl
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | _ :: _ :: _ :: rest, h => by
      have tail := b64Encode_length rest (by simp at h; omega)
      simp only [b64Encode, List.length_cons, tail]
      omega

theorem sshBlob_length {memo : Memo} (wf : memo.WellFormed) : memo.sshBlob.length = 51 := by
  simp [Memo.sshBlob, sshBlobOf, sshBlobPrefix, sshEd25519Name, wf.2.1]

theorem sshBlobPrefix_length : sshBlobPrefix.length = 19 := by decide

theorem isEd25519Blob_split {blob : List UInt8} (accepted : isEd25519Blob blob = true) :
    sshBlobOf (blob.drop 19) = blob ∧ (blob.drop 19).length = 32 := by
  simp only [isEd25519Blob, Bool.and_eq_true, beq_iff_eq] at accepted
  constructor
  · rw [sshBlobOf, ← accepted.2, List.take_append_drop]
  · simp [accepted.1]

theorem sshBlobOf_isEd25519 {key : List UInt8} (length : key.length = 32) :
    isEd25519Blob (sshBlobOf key) = true := by
  have take : (sshBlobPrefix ++ key).take 19 = sshBlobPrefix := by
    rw [← sshBlobPrefix_length]; exact List.take_left
  simp [isEd25519Blob, sshBlobOf, take, length, sshBlobPrefix_length]

theorem sshBlobOf_drop (key : List UInt8) : (sshBlobOf key).drop 19 = key := by
  rw [sshBlobOf, ← sshBlobPrefix_length]; exact List.drop_left

theorem encode_cut {memo : Memo} (wf : memo.WellFormed) :
    cut fields (encode memo) = [enrolTag, v1Tag, hexEncode memo.miniKey, [separator],
      b64Encode memo.sshBlob, [separator], hexEncode memo.miniSig, [separator],
      hexEncode memo.sshSig] := by
  have b64 : (b64Encode memo.sshBlob).length = 68 := by
    rw [b64Encode_length _ (by rw [sshBlob_length wf]), sshBlob_length wf]
  rw [encode, cut_append]
  · rfl
  · simp [fields, enrolTag, v1Tag, hexEncode_length, wf.1, wf.2.2.1, b64]

theorem encode_length {memo : Memo} (wf : memo.WellFormed) : (encode memo).length = memoLength := by
  have b64 : (b64Encode memo.sshBlob).length = 68 := by
    rw [b64Encode_length _ (by rw [sshBlob_length wf]), sshBlob_length wf]
  simp [encode, hexEncode_length, wf.1, wf.2.2.1, wf.2.2.2, b64, enrolTag, v1Tag, memoLength]

/-- **Round trip**: every well-formed memo value is accepted as itself. -/
theorem parse_encode {memo : Memo} (wf : memo.WellFormed) : parse (encode memo) = .ok memo := by
  have blob := sshBlobOf_isEd25519 wf.2.1
  have tripleBlob : (sshBlobOf memo.sshKey).length % 3 = 0 := by
    have := sshBlob_length wf
    rw [Memo.sshBlob] at this
    rw [this]
  unfold parse
  rw [encode_cut wf]
  simp only [ne_eq, not_true_eq_false, if_false, encode_length wf, or_self,
    hexDecode_hexEncode, Memo.sshBlob, b64Decode_b64Encode _ tripleBlob, blob,
    Bool.true_eq_false, sshBlobOf_drop]
  all_goals (cases memo; rfl)

/-- **Canonicity**: an accepted memo is exactly the encoding of its value. -/
theorem parse_canonical {bytes : List UInt8} {memo : Memo} (accepted : parse bytes = .ok memo) :
    encode memo = bytes ∧ memo.WellFormed := by
  unfold parse at accepted
  split at accepted
  next tag version miniHex s₁ sshText s₂ miniSigHex s₃ sshSigHex pieces =>
    by_cases t : tag = enrolTag
    · by_cases v : version = v1Tag
      · by_cases l : bytes.length = memoLength
        · by_cases s : s₁ = [separator] ∧ s₂ = [separator] ∧ s₃ = [separator]
          · obtain ⟨e₁, e₂, e₃⟩ := s
            have lengths := cut_lengths fields bytes (by rw [l]; decide)
            rw [pieces, l] at lengths
            simp only [fields, List.map_cons, List.map_nil, memoLength, List.sum_cons,
              List.sum_nil] at lengths
            simp only [List.cons_append, List.nil_append, List.cons.injEq] at lengths
            simp only [t, v, l, e₁, e₂, e₃, ne_eq, not_true_eq_false, if_false, or_self] at accepted
            split at accepted
            · simp at accepted
            next miniKey hk =>
              split at accepted
              · simp at accepted
              next blob hb =>
                by_cases ed : isEd25519Blob blob = true
                · simp only [ed, Bool.true_eq_false, if_false] at accepted
                  split at accepted
                  · simp at accepted
                  next miniSig hm =>
                    split at accepted
                    · simp at accepted
                    next sshSig hs =>
                      simp only [Except.ok.injEq] at accepted
                      subst accepted
                      have ck := hexEncode_hexDecode hk
                      have cb := b64Encode_b64Decode hb
                      have cm := hexEncode_hexDecode hm
                      have cs := hexEncode_hexDecode hs
                      obtain ⟨split, keyLength⟩ := isEd25519Blob_split ed
                      have whole := cut_flatten fields bytes
                      rw [pieces] at whole
                      refine ⟨?_, ?_⟩
                      · rw [← whole]
                        simp only [encode, Memo.sshBlob, split, ck, cb, cm, cs, t, v, e₁, e₂, e₃]
                        simp
                      · have lk := hexEncode_length miniKey
                        have lm := hexEncode_length miniSig
                        have ls := hexEncode_length sshSig
                        rw [ck] at lk; rw [cm] at lm; rw [cs] at ls
                        refine ⟨?_, keyLength, ?_, ?_⟩
                        · show miniKey.length = 32; omega
                        · show miniSig.length = 64; omega
                        · show sshSig.length = 64; omega
                · simp only [Bool.not_eq_true] at ed
                  simp [ed] at accepted
          · simp only [not_and_or] at s
            simp only [t, v, l, ne_eq, not_true_eq_false, if_false] at accepted
            rcases s with s | s | s <;> simp [s] at accepted
        · simp [t, v, l] at accepted
      · simp [t, v] at accepted
    · simp [t] at accepted
  next => simp at accepted

/-! ## What each signature is over (PAY §11.3) -/

/-- `"DREGG/PAY/ENROL/POSSESSION/v1"` as bytes. -/
def possessionTag : List UInt8 :=
  [68, 82, 69, 71, 71, 47, 80, 65, 89, 47, 69, 78, 82, 79, 76, 47, 80, 79, 83, 83, 69, 83, 83,
    73, 79, 78, 47, 118, 49]

theorem possessionTag_utf8 : possessionTag = "DREGG/PAY/ENROL/POSSESSION/v1".toUTF8.toList := by
  decide +kernel

/-- The Mini key's possession statement: it binds the mint, the enrollment
address and the ssh key it vouches for. -/
def miniFrame (mint enrolAddress : Address32) (memo : Memo) : List UInt8 :=
  possessionTag ++ mint ++ enrolAddress ++ memo.sshBlob

/-- `"dregg-enrol@v1"`: the SSHSIG namespace. -/
def sshsigNamespace : List UInt8 := [100, 114, 101, 103, 103, 45, 101, 110, 114, 111, 108, 64, 118, 49]

theorem sshsigNamespace_utf8 : sshsigNamespace = "dregg-enrol@v1".toUTF8.toList := by decide +kernel

/-- The message the ssh key signs through SSHSIG: it binds the mint, the
enrollment address and the Mini key it vouches for. -/
def sshsigMessage (mint enrolAddress : Address32) (memo : Memo) : List UInt8 :=
  mint ++ enrolAddress ++ memo.miniKey

/-- An SSH `string`: a big-endian uint32 length and the bytes. -/
def sshString (bytes : List UInt8) : List UInt8 :=
  let n := bytes.length
  [UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 256 % 256),
    UInt8.ofNat (n % 256)] ++ bytes

/-- `"SSHSIG"` and `"sha512"` as bytes. -/
def sshsigMagic : List UInt8 := [83, 83, 72, 83, 73, 71]
def sha512Name : List UInt8 := [115, 104, 97, 53, 49, 50]

/-- OpenSSH PROTOCOL.sshsig: the bytes an SSHSIG Ed25519 signature is over,
`"SSHSIG" ‖ string namespace ‖ string "" ‖ string "sha512" ‖ string H(message)`.
The digest is SHA-512 of the message, computed by the native verifier. -/
def sshsigSignedData (nameSpace digest : List UInt8) : List UInt8 :=
  sshsigMagic ++ sshString nameSpace ++ sshString [] ++ sshString sha512Name ++ sshString digest

/-! ## The memo as the watcher reports it -/

/-- What the watcher saw of the transaction's memo instructions (P1b). -/
inductive MemoField
  /-- No memo instruction. -/
  | absent
  /-- Exactly one memo instruction: its raw bytes. -/
  | present (bytes : List UInt8)
  /-- Two or more memo instructions (`memoUnbound`). -/
  | unbound
  /-- One memo that is not UTF-8 or is over 566 bytes (`memoInvalid`). -/
  | invalid
  deriving DecidableEq, Repr

def memoFieldStream : StreamCodec MemoField where
  encode
    | .absent => [0]
    | .present bytes => 1 :: bytesStream.encode bytes
    | .unbound => [2]
    | .invalid => [3]
  decodePrefix
    | 0 :: suffix => some (.absent, suffix)
    | 1 :: bytes => do
        let (value, suffix) ← bytesStream.decodePrefix bytes
        some (.present value, suffix)
    | 2 :: suffix => some (.unbound, suffix)
    | 3 :: suffix => some (.invalid, suffix)
    | _ => none
  decodePrefix_encode := by
    intro value suffix
    cases value with
    | present bytes => simp [bytesStream.decodePrefix_encode]
    | _ => rfl

/-! ## Journal reasons (PAY §11.3) -/

inductive JournalReason
  | memoMissing
  | memoUnbound
  | memoInvalid
  | memoMalformed (refusal : Refusal)
  | miniSigInvalid
  | sshSigInvalid
  | belowPrice
  | sshKeyTaken
  | sshKeyMismatch
  | subjectTaken
  deriving DecidableEq, Repr

def Refusal.code : Refusal → Nat
  | .shape => 0 | .version => 1 | .badMiniKey => 2 | .badSshKey => 3 | .badMiniSig => 4
  | .badSshSig => 5

def Refusal.ofCode : Nat → Option Refusal
  | 0 => some .shape | 1 => some .version | 2 => some .badMiniKey | 3 => some .badSshKey
  | 4 => some .badMiniSig | 5 => some .badSshSig | _ => none

def JournalReason.code : JournalReason → Nat
  | .memoMissing => 0 | .memoUnbound => 1 | .memoInvalid => 2
  | .memoMalformed refusal => 100 + refusal.code
  | .miniSigInvalid => 3 | .sshSigInvalid => 4 | .belowPrice => 5 | .sshKeyTaken => 6
  | .sshKeyMismatch => 7 | .subjectTaken => 8

def JournalReason.ofCode (code : Nat) : Option JournalReason :=
  match code with
  | 0 => some .memoMissing | 1 => some .memoUnbound | 2 => some .memoInvalid
  | 3 => some .miniSigInvalid | 4 => some .sshSigInvalid | 5 => some .belowPrice
  | 6 => some .sshKeyTaken | 7 => some .sshKeyMismatch | 8 => some .subjectTaken
  | n => if 100 ≤ n then (Refusal.ofCode (n - 100)).map .memoMalformed else none

theorem JournalReason.ofCode_code (reason : JournalReason) :
    JournalReason.ofCode reason.code = some reason := by
  cases reason with
  | memoMalformed refusal => cases refusal <;> decide
  | _ => decide

def journalReasonStream : StreamCodec JournalReason where
  encode reason := StreamCodec.nat.encode reason.code
  decodePrefix bytes := do
    let (code, suffix) ← StreamCodec.nat.decodePrefix bytes
    let reason ← JournalReason.ofCode code
    some (reason, suffix)
  decodePrefix_encode := by
    intro reason suffix
    simp [StreamCodec.nat.decodePrefix_encode, JournalReason.ofCode_code]

/-! ## The self-enrolled subject -/

def subjectCustomization : List UInt8 := "DREGG.PAY.SELF-ENROL.SUBJECT/v1".toUTF8.toList

/-- `subjectOf miniKey := cSHAKE("DREGG.PAY.SELF-ENROL.SUBJECT/v1", miniKey) mod 2⁶⁴`. -/
def subjectOf (miniKey : List UInt8) : Nat :=
  (Sp800185Cshake256.hash subjectCustomization miniKey).digest.value % 2 ^ 64

/-! ## Poles on a real memo

The fixture below is a real enrollment memo: the Mini key is the PyNaCl key of
seed `[42]*32`, the ssh key was made by `ssh-keygen -t ed25519` on persvati and
`ssh-sig` is the 64-byte signature inside `ssh-keygen -Y sign -n dregg-enrol@v1`
over `sshsigMessage fixtureMint fixtureAddress fixtureMemo` (the SSHSIG blob
verified with `ssh-keygen -Y check-novalidate`); `mini-sig` is PyNaCl's
signature over `miniFrame`.  The native tests verify both signatures. -/

def fixtureBytes : List UInt8 :=
  [101, 110, 114, 111, 108, 58, 118, 49, 58, 49, 57, 55, 102, 54, 98, 50, 51, 101, 49, 54, 99,
    56, 53, 51, 50, 99, 54, 97, 98, 99, 56, 51, 56, 102, 97, 99, 100, 53, 101, 97, 55, 56, 57,
    98, 101, 48, 99, 55, 54, 98, 50, 57, 50, 48, 51, 51, 52, 48, 51, 57, 98, 102, 97, 56, 98,
    51, 100, 51, 54, 56, 100, 54, 49, 58, 65, 65, 65, 65, 67, 51, 78, 122, 97, 67, 49, 108, 90,
    68, 73, 49, 78, 84, 69, 53, 65, 65, 65, 65, 73, 71, 48, 55, 115, 115, 119, 47, 110, 86, 81,
    121, 69, 112, 52, 102, 98, 111, 54, 120, 48, 68, 101, 102, 116, 116, 72, 53, 67, 100, 115,
    109, 117, 85, 73, 50, 56, 47, 110, 99, 47, 85, 107, 75, 58, 49, 97, 56, 57, 97, 52, 53, 52,
    52, 50, 53, 48, 100, 102, 51, 98, 101, 49, 54, 98, 100, 55, 48, 49, 51, 53, 55, 100, 49, 49,
    52, 99, 99, 98, 48, 48, 100, 97, 98, 100, 55, 57, 100, 97, 55, 55, 102, 51, 53, 99, 56, 97,
    51, 57, 52, 56, 55, 53, 99, 102, 55, 56, 100, 56, 101, 102, 54, 54, 98, 52, 55, 100, 56, 97,
    51, 99, 100, 101, 52, 99, 50, 49, 101, 102, 100, 54, 99, 57, 97, 101, 102, 100, 50, 102,
    101, 55, 52, 51, 48, 97, 100, 99, 48, 52, 55, 100, 54, 55, 55, 52, 54, 52, 57, 56, 50, 56,
    48, 99, 50, 55, 52, 97, 100, 97, 101, 50, 48, 50, 58, 101, 51, 48, 50, 52, 97, 49, 50, 50,
    102, 55, 102, 50, 48, 51, 51, 53, 99, 49, 54, 56, 98, 50, 50, 100, 52, 50, 56, 54, 49, 55,
    99, 98, 99, 102, 98, 52, 100, 99, 54, 100, 48, 98, 54, 56, 102, 50, 54, 100, 97, 101, 56,
    101, 50, 99, 50, 48, 51, 56, 54, 52, 49, 102, 100, 52, 48, 100, 54, 55, 50, 101, 55, 51, 57,
    98, 56, 97, 49, 100, 49, 97, 54, 56, 49, 102, 54, 100, 56, 52, 56, 56, 102, 52, 54, 48, 52,
    54, 57, 56, 53, 53, 55, 48, 102, 48, 101, 101, 51, 48, 100, 98, 48, 49, 97, 101, 51, 54, 49,
    51, 48, 57, 102, 102, 50, 49, 102, 48, 57]

def fixtureMemo : Memo :=
  ⟨[25, 127, 107, 35, 225, 108, 133, 50, 198, 171, 200, 56, 250, 205, 94, 167, 137, 190, 12,
    118, 178, 146, 3, 52, 3, 155, 250, 139, 61, 54, 141, 97],
   [109, 59, 178, 204, 63, 157, 84, 50, 18, 158, 31, 110, 142, 177, 208, 55, 159, 182, 209, 249,
    9, 219, 38, 185, 66, 54, 243, 249, 220, 253, 73, 10],
   [26, 137, 164, 84, 66, 80, 223, 59, 225, 107, 215, 1, 53, 125, 17, 76, 203, 0, 218, 189, 121,
    218, 119, 243, 92, 138, 57, 72, 117, 207, 120, 216, 239, 102, 180, 125, 138, 60, 222, 76,
    33, 239, 214, 201, 174, 253, 47, 231, 67, 10, 220, 4, 125, 103, 116, 100, 152, 40, 12, 39,
    74, 218, 226, 2],
   [227, 2, 74, 18, 47, 127, 32, 51, 92, 22, 139, 34, 212, 40, 97, 124, 188, 251, 77, 198, 208,
    182, 143, 38, 218, 232, 226, 194, 3, 134, 65, 253, 64, 214, 114, 231, 57, 184, 161, 209,
    166, 129, 246, 216, 72, 143, 70, 4, 105, 133, 87, 15, 14, 227, 13, 176, 26, 227, 97, 48,
    159, 242, 31, 9]⟩

def fixtureMint : Address32 :=
  [133, 37, 150, 108, 0, 243, 159, 245, 78, 245, 229, 55, 164, 115, 106, 244, 54, 73, 77, 31,
    22, 129, 198, 89, 189, 152, 227, 122, 194, 139, 239, 241]

def fixtureAddress : Address32 :=
  [22, 148, 106, 166, 99, 54, 45, 85, 125, 210, 30, 224, 142, 141, 166, 12, 46, 168, 167, 52,
    103, 113, 60, 124, 82, 5, 153, 30, 54, 99, 74, 245]

/-- SHA-512 of `sshsigMessage fixtureMint fixtureAddress fixtureMemo` (Python
`hashlib`); the Rust test recomputes it. -/
def fixtureDigest : List UInt8 :=
  [24, 48, 223, 136, 71, 92, 172, 97, 6, 110, 230, 159, 80, 23, 178, 137, 194, 137, 189, 228,
    73, 173, 112, 44, 86, 109, 197, 166, 209, 152, 61, 169, 122, 4, 183, 24, 116, 212, 138, 127,
    13, 121, 237, 239, 29, 53, 35, 51, 214, 66, 83, 246, 88, 92, 93, 90, 10, 154, 172, 19, 43,
    199, 89, 2]

/-- Satisfiable pole: the real memo parses to its four fields. -/
theorem fixture_parses : parse fixtureBytes = .ok fixtureMemo := by decide +kernel

theorem fixture_length : fixtureBytes.length = memoLength := by decide +kernel

theorem fixture_wellFormed : fixtureMemo.WellFormed := by decide +kernel

/-- The SSHSIG signed data of the fixture, byte for byte (the same bytes the
native `verify-sshsig` test asserts before verifying). -/
theorem sshsig_signed_data_fixture :
    sshsigSignedData sshsigNamespace fixtureDigest =
      [83, 83, 72, 83, 73, 71, 0, 0, 0, 14] ++ sshsigNamespace ++ [0, 0, 0, 0, 0, 0, 0, 6] ++
        sha512Name ++ [0, 0, 0, 64] ++ fixtureDigest := by decide +kernel

/-- Replace the byte at `index`. -/
def mutate (index : Nat) (value : UInt8) (bytes : List UInt8) : List UInt8 := bytes.set index value

/-- Refuting poles, one per refusal. -/
theorem short_memo_refused : parse (fixtureBytes.take 399) = .error .shape := by decide +kernel
theorem long_memo_refused : parse (fixtureBytes ++ [48]) = .error .shape := by decide +kernel
theorem not_enrol_refused : parse (mutate 0 69 fixtureBytes) = .error .shape := by decide +kernel
theorem version_refused : parse (mutate 7 50 fixtureBytes) = .error .version := by decide +kernel
theorem separator_refused : parse (mutate 73 59 fixtureBytes) = .error .shape := by decide +kernel
/-- An uppercase hex digit in the Mini key (`'F'` for `'f'` at byte 11). -/
theorem uppercase_mini_key_refused : parse (mutate 11 70 fixtureBytes) = .error .badMiniKey := by
  decide +kernel
/-- A `'='` padding character inside the ssh blob's base64. -/
theorem padded_ssh_key_refused : parse (mutate 141 61 fixtureBytes) = .error .badSshKey := by
  decide +kernel
/-- A base64 blob that decodes but names another algorithm: `ssh-ed25519` →
`ssh-ed25518` is base64 character 19 of the blob (`'5'` → `'4'`, memo byte 93). -/
theorem other_algorithm_refused : parse (mutate 93 52 fixtureBytes) = .error .badSshKey := by
  decide +kernel
theorem bad_mini_sig_refused : parse (mutate 200 103 fixtureBytes) = .error .badMiniSig := by
  decide +kernel
theorem bad_ssh_sig_refused : parse (mutate 399 71 fixtureBytes) = .error .badSshSig := by
  decide +kernel

#assert_axioms hexVal_hexChar_table
#assert_axioms hexChar_hexVal_table
#assert_axioms hexDecode_hexEncode
#assert_axioms hexEncode_hexDecode
#assert_axioms b64Val_b64Char_table
#assert_axioms b64Char_b64Val_table
#assert_axioms b64Decode_b64Encode
#assert_axioms b64Encode_b64Decode
#assert_axioms sshEd25519Name_utf8
#assert_axioms memoPrefix_utf8
#assert_axioms possessionTag_utf8
#assert_axioms sshsigNamespace_utf8
#assert_axioms cut_flatten
#assert_axioms cut_append
#assert_axioms cut_lengths
#assert_axioms encode_cut
#assert_axioms encode_length
#assert_axioms parse_encode
#assert_axioms parse_canonical
#assert_axioms JournalReason.ofCode_code
#assert_axioms fixture_parses
#assert_axioms fixture_length
#assert_axioms fixture_wellFormed
#assert_axioms sshsig_signed_data_fixture
#assert_axioms short_memo_refused
#assert_axioms long_memo_refused
#assert_axioms not_enrol_refused
#assert_axioms version_refused
#assert_axioms separator_refused
#assert_axioms uppercase_mini_key_refused
#assert_axioms padded_ssh_key_refused
#assert_axioms other_algorithm_refused
#assert_axioms bad_mini_sig_refused
#assert_axioms bad_ssh_sig_refused

end Minidregg.Kernel.PayEnrolMemo
