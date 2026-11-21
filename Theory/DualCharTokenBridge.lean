/-
# `Theory/DualCharTokenBridge.lean` — Free-Monoid BPE Detokenization, Split-Token Smuggling Refutation, & Emulation-Free Dual-Characteristic Rolling-Hash Soundness

Closes two coupled security hazards at the boundary between neural tensor inference
(`BabyBear` / `Ext4` / `p61` prime fields) and byte-level policy/redaction/LL(1) enforcement
(`Tower256` `GF(2^256)` + `cSHAKE256` salted content commitments):

1. **Free-Monoid Detokenization Homomorphism & Split-Token Secret-Smuggling Refutation
   (`detok_append`, `tokenLevelGuard_bypassed_by_bpe_split`, `tokenFree_not_implies_byteAbsent`):**
   - Models a BPE vocabulary `Vocab TokId := TokId → List UInt8` and detokenization
     `detok V ts := ts.flatMap V`, proving the free-monoid concatenation homomorphism
     `detok_append` and multi-segment `detok_flatten`.
   - Constructively refutes token-ID-level safety filters (`tokenLevelGuard_bypassed_by_bpe_split`
     and `tokenFree_not_implies_byteAbsent`): exhibits a concrete BPE vocabulary `demoBpeVocab`
     and two distinct non-canonical tokenizations `splitSeqA = ["s", "k-proj"]` and
     `splitSeqB = ["sk", "-proj"]` (`detok_not_injective`) such that **neither** sequence contains
     the banned `"sk-"` token ID and **no single token's bytes** contain `"sk-"`, yet `detok` of
     both contains `"sk-"`. Proves that byte-level `redactBytes` (`Theory.VerifiedAstTransducer`)
     scrubs all safe rules identically across every BPE split (`detok_redactBytes_scrubs_any_split`).

2. **Variable-Length Algebraic Rolling Hash & Degree-2 Token-ROM Fold
   (`evalBytesWith`, `evalBytesBase`, `stepTokenRoll`, `rollTokens_eq_evalBytes_detok`):**
   - Over **any** `[CommRing R]` (`ℤ`, `ZMod p_BB`, `Ext4`, `ZMod p_61`, and `Tower256`!), proves
     that folding the **degree-2 affine state transition**
     `(acc', totalLen') = (acc * B^{len_t} + val_t, totalLen + len_t)` across per-token ROM tuples
     `(len_t, B^{len_t}, evalBytes B (V t))` equals `(evalBytes B (detok V ts), (detok V ts).length)`
     on the nose (`rollTokensWith_eq_evalBytesWith_detok`, `rollTokens_eq_evalBytes_detok`) with
     **zero character-by-character inner loops** in the online circuit, and commutes naturally with
     every ring homomorphism `R →+* S` (`rollTokens_map_ringHom`).

3. **Schwartz–Zippel & `IntegerFingerprint` Cross-Characteristic Soundness + Falsifier Teeth
   (`evalBytesWith_eq_imp_bytes_eq_or_root`, `evalBytesBase_eq_imp_bytes_eq_or_root`,
    `dualChar_integer_fingerprint_bound`, `leadingZero_length_omission_falsifier`,
    `char2_natCast_alias_falsifier`):**
   - Over any `[Field F]` with an injective byte embedding `emb : UInt8 → F` (covering both prime
     fields `char(F) = 0 ∨ 256 ≤ char(F)` via `Nat.cast` AND binary extension fields `GF(2^256)`
     via `GF(2^8)` coordinate basis injection), proves that any two distinct `L`-byte streams
     `bs₁ ≠ bs₂` colliding at `(L, evalBytes)` force `B` to be a root of a nonzero polynomial of
     degree `< L` (`≤ L - 1` bad challenges, error `≤ (L - 1) / |S|`).
   - Proves two load-bearing falsifier teeth: (a) omitting `totalLen` lets `[0, 65]` (`"\x00A"`)
     and `[65]` (`"A"`) collide at **every** base `B` in **every** ring (`leadingZero_length_omission_falsifier`),
     and (b) naive `Nat.cast` in characteristic `2` aliases equal-length `[65]` (`"A"`) and `[67]`
     (`"C"`) at **every** base `B : ZMod 2` (`char2_natCast_alias_falsifier`).
   - Proves exact injectivity of fixed-base `B = 256` evaluation over `ℤ` (`evalBytesInt_injective_of_length_eq`)
     and connects directly to `Theory.IntegerFingerprint.pow_card_undetected_le` and
     `fingerprint_error_ratio_le` (`dualChar_integer_fingerprint_bound`), with full premise
     inhabitation (`dualChar_integer_fingerprint_inhabited`).

Import boundary: `Theory/` tier (`Mathlib.*` + `Theory.*` only).
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Theory.IntegerFingerprint
import Theory.VerifiedAstTransducer

namespace Minidregg.Theory.DualCharTokenBridge

open Polynomial
open Minidregg.Theory.IntegerFingerprint
open Minidregg.Theory.VerifiedAstTransducer

set_option autoImplicit false

/-! ## §1. Free-Monoid Detokenization Homomorphism & Split-Token Secret-Smuggling Refutation -/

/-- A tokenizer vocabulary maps each token identifier `t : TokId` to its finite UTF-8 / raw byte
sequence `V t : List UInt8`. -/
abbrev Vocab (TokId : Type*) := TokId → List UInt8

/-- Canonical BPE detokenization: concatenates per-token byte slices across `ts`. -/
def detok {TokId : Type*} (V : Vocab TokId) (ts : List TokId) : List UInt8 :=
  ts.flatMap V

@[simp] theorem detok_nil {TokId : Type*} (V : Vocab TokId) :
    detok V ([] : List TokId) = [] := rfl

@[simp] theorem detok_cons {TokId : Type*} (V : Vocab TokId) (t : TokId) (ts : List TokId) :
    detok V (t :: ts) = V t ++ detok V ts := rfl

@[simp] theorem detok_singleton {TokId : Type*} (V : Vocab TokId) (t : TokId) :
    detok V [t] = V t := by
  simp [detok]

/-- **Free-Monoid Homomorphism (`detok_append`).**
Detokenization is a monoid homomorphism from `(List TokId, ++, [])` to `(List UInt8, ++, [])`. -/
theorem detok_append {TokId : Type*} (V : Vocab TokId) (ts₁ ts₂ : List TokId) :
    detok V (ts₁ ++ ts₂) = detok V ts₁ ++ detok V ts₂ := by
  simp [detok]

/-- Multi-chunk associativity of detokenization across arbitrary chunkings `tss`. -/
theorem detok_flatten {TokId : Type*} (V : Vocab TokId) (tss : List (List TokId)) :
    detok V tss.flatten = (tss.map (detok V)).flatten := by
  induction tss with
  | nil => rfl
  | cons ts tss ih =>
      simp [List.flatten_cons, detok_append, ih]

/-- Concrete 6-token BPE vocabulary exhibiting canonical vs split-token `"sk-proj"` decompositions. -/
def tokBannedSkDash : Fin 6 := 0
def tokS            : Fin 6 := 1
def tokKProj        : Fin 6 := 2
def tokSk           : Fin 6 := 3
def tokDashProj     : Fin 6 := 4
def tokCleanOk      : Fin 6 := 5

def demoBpeVocab : Vocab (Fin 6)
  | ⟨0, _⟩ => asciiBytes "sk-"
  | ⟨1, _⟩ => asciiBytes "s"
  | ⟨2, _⟩ => asciiBytes "k-proj"
  | ⟨3, _⟩ => asciiBytes "sk"
  | ⟨4, _⟩ => asciiBytes "-proj"
  | ⟨5, _⟩ => asciiBytes "ok"

/-- First non-canonical BPE split `["s", "k-proj"]`. -/
def splitSeqA : List (Fin 6) := [tokS, tokKProj]

/-- Second BPE split `["sk", "-proj"]` (mirrors Qwen's pre-tokenizer letter/punctuation boundary). -/
def splitSeqB : List (Fin 6) := [tokSk, tokDashProj]

/-- **Split-Token Secret-Smuggling Theorem (`tokenLevelGuard_bypassed_by_bpe_split`).**
Exhibits two distinct token sequences `splitSeqA = [t_"s", t_"k-proj"]` and
`splitSeqB = [t_"sk", t_"-proj"]` such that:
1. `splitSeqA ≠ splitSeqB`, yet both detokenize to `asciiBytes "sk-proj"` (BPE non-injectivity),
2. Neither sequence contains the banned token ID `tokBannedSkDash` (`"sk-"`),
3. **Every individual token** in both sequences satisfies byte-level `AbsentW · "sk-"`,
4. Yet `detok demoBpeVocab` of **both** sequences contains `"sk-"` (`OccursInW`, `¬ AbsentW`)! -/
theorem tokenLevelGuard_bypassed_by_bpe_split :
    splitSeqA ≠ splitSeqB ∧
    detok demoBpeVocab splitSeqA = asciiBytes "sk-proj" ∧
    detok demoBpeVocab splitSeqB = asciiBytes "sk-proj" ∧
    tokBannedSkDash ∉ splitSeqA ∧
    tokBannedSkDash ∉ splitSeqB ∧
    (∀ t ∈ splitSeqA, AbsentW (demoBpeVocab t) (asciiBytes "sk-")) ∧
    (∀ t ∈ splitSeqB, AbsentW (demoBpeVocab t) (asciiBytes "sk-")) ∧
    OccursInW (detok demoBpeVocab splitSeqA) (asciiBytes "sk-") ∧
    OccursInW (detok demoBpeVocab splitSeqB) (asciiBytes "sk-") ∧
    ¬ AbsentW (detok demoBpeVocab splitSeqA) (asciiBytes "sk-") := by
  decide

/-- Detokenization is **not injective** on token sequences (`splitSeqA ≠ splitSeqB` share one byte image). -/
theorem detok_not_injective : ¬ Function.Injective (detok demoBpeVocab) := by
  intro hinj
  have h := tokenLevelGuard_bypassed_by_bpe_split
  exact h.1 (hinj (h.2.1.trans h.2.2.1.symm))

/-- **Refutation of Token-Level Safety Filtering (`tokenFree_not_implies_byteAbsent`).**
Banning a secret token ID `tBan` AND verifying `AbsentW (V t) pat` on every emitted token `t ∈ ts`
does **not** imply `AbsentW (detok V ts) pat` on the resulting UTF-8 byte stream. -/
theorem tokenFree_not_implies_byteAbsent :
    ¬ (∀ (V : Vocab (Fin 6)) (tBan : Fin 6) (pat : List UInt8) (ts : List (Fin 6)),
        tBan ∉ ts →
        (∀ t ∈ ts, AbsentW (V t) pat) →
        AbsentW (detok V ts) pat) := by
  intro hall
  rcases tokenLevelGuard_bypassed_by_bpe_split with
    ⟨_, _, _, hnotBanA, _, htokAbsA, _, _, _, hnotAbsDetok⟩
  exact hnotAbsDetok (hall demoBpeVocab tokBannedSkDash (asciiBytes "sk-") splitSeqA hnotBanA htokAbsA)

/-- **Byte-Level Redaction Invariance & Completeness Across All BPE Splits (`detok_redactBytes_scrubs_any_split`).**
Welding token sequences to `detok V ts` before applying `redactBytes` produces the **exact same**
sanitized byte stream across every BPE split `detok V ts₁ = detok V ts₂` and scrubs every safe
secret pattern regardless of token boundaries. -/
theorem detok_redactBytes_scrubs_any_split {TokId : Type*}
    (V : Vocab TokId) (rules : List (RedactRule UInt8))
    (hsafe : allRulesSafe rules = true) (ts₁ ts₂ : List TokId)
    (hsplit : detok V ts₁ = detok V ts₂) :
    redactBytes rules (detok V ts₁) = redactBytes rules (detok V ts₂) ∧
    (∀ r ∈ rules, AbsentW (redactBytes rules (detok V ts₁)) r.pat) := by
  refine ⟨by rw [hsplit], fun r hr => ?_⟩
  have hunpack := allRulesSafe_unpack hsafe r hr
  exact redactBytes_scrubs_all rules r hr hunpack.1 hunpack.2 (detok V ts₁)

/-! ## §2. Variable-Length Algebraic Rolling Hash & Degree-2 Token-ROM Fold -/

/-- Big-endian Horner evaluation of `bs : List UInt8` at base `B : R` under byte embedding `emb : UInt8 → R`:
`∑_{i=0}^{|bs|-1} emb(bs[i]) · B^{|bs| - 1 - i}`. -/
def evalBytesWith {R : Type*} [CommRing R] (emb : UInt8 → R) (B : R) (bs : List UInt8) : R :=
  bs.foldl (fun acc b => acc * B + emb b) 0

/-- Canonical ring-cast specialization `emb b = (b.toNat : R)` (`ℤ`, `ZMod p_BB`, `Ext4`, `ZMod p_61`). -/
def evalBytesBase {R : Type*} [CommRing R] (B : R) (bs : List UInt8) : R :=
  evalBytesWith (fun b => (b.toNat : R)) B bs

@[simp] theorem evalBytesWith_nil {R : Type*} [CommRing R] (emb : UInt8 → R) (B : R) :
    evalBytesWith emb B [] = 0 := rfl

@[simp] theorem evalBytesBase_nil {R : Type*} [CommRing R] (B : R) :
    evalBytesBase B [] = 0 := rfl

@[simp] theorem evalBytesWith_singleton {R : Type*} [CommRing R]
    (emb : UInt8 → R) (B : R) (b : UInt8) :
    evalBytesWith emb B [b] = emb b := by
  simp [evalBytesWith]

@[simp] theorem evalBytesBase_singleton {R : Type*} [CommRing R] (B : R) (b : UInt8) :
    evalBytesBase B [b] = (b.toNat : R) := by
  simp [evalBytesBase]

private theorem foldl_horner_shift {R : Type*} [CommRing R]
    (emb : UInt8 → R) (B : R) :
    ∀ (bs : List UInt8) (init : R),
      bs.foldl (fun acc b => acc * B + emb b) init =
        init * B ^ bs.length + evalBytesWith emb B bs := by
  intro bs
  induction bs with
  | nil =>
      intro init
      simp [evalBytesWith]
  | cons b bs ih =>
      intro init
      simp only [List.foldl_cons, List.length_cons, evalBytesWith]
      rw [ih (init * B + emb b), ih (0 * B + emb b)]
      ring

/-- **Exact Byte-Stream Concatenation Identity (`evalBytesWith_append`).** -/
theorem evalBytesWith_append {R : Type*} [CommRing R]
    (emb : UInt8 → R) (B : R) (xs ys : List UInt8) :
    evalBytesWith emb B (xs ++ ys) =
      evalBytesWith emb B xs * B ^ ys.length + evalBytesWith emb B ys := by
  unfold evalBytesWith
  rw [List.foldl_append]
  exact foldl_horner_shift emb B ys (xs.foldl (fun acc b => acc * B + emb b) 0)

/-- **Exact Byte-Stream Concatenation Identity (`evalBytesBase_append`).** -/
theorem evalBytesBase_append {R : Type*} [CommRing R]
    (B : R) (xs ys : List UInt8) :
    evalBytesBase B (xs ++ ys) =
      evalBytesBase B xs * B ^ ys.length + evalBytesBase B ys :=
  evalBytesWith_append (fun b => (b.toNat : R)) B xs ys

@[simp] theorem evalBytesWith_snoc {R : Type*} [CommRing R]
    (emb : UInt8 → R) (B : R) (xs : List UInt8) (b : UInt8) :
    evalBytesWith emb B (xs ++ [b]) = evalBytesWith emb B xs * B + emb b := by
  simpa using evalBytesWith_append emb B xs [b]

@[simp] theorem evalBytesBase_snoc {R : Type*} [CommRing R]
    (B : R) (xs : List UInt8) (b : UInt8) :
    evalBytesBase B (xs ++ [b]) = evalBytesBase B xs * B + (b.toNat : R) := by
  simpa using evalBytesBase_append B xs [b]

theorem evalBytesWith_cons {R : Type*} [CommRing R]
    (emb : UInt8 → R) (B : R) (b : UInt8) (bs : List UInt8) :
    evalBytesWith emb B (b :: bs) = emb b * B ^ bs.length + evalBytesWith emb B bs := by
  simpa using evalBytesWith_append emb B [b] bs

theorem evalBytesBase_cons {R : Type*} [CommRing R]
    (B : R) (b : UInt8) (bs : List UInt8) :
    evalBytesBase B (b :: bs) = (b.toNat : R) * B ^ bs.length + evalBytesBase B bs := by
  simpa using evalBytesBase_append B [b] bs

/-- Explicit closed-form sum of powers: `evalBytesBase B bs = ∑_{i=0}^{|bs|-1} bs_i · B^{|bs| - 1 - i}`. -/
theorem evalBytesBase_eq_sum_pow {R : Type*} [CommRing R] (B : R) (bs : List UInt8) :
    evalBytesBase B bs =
      ∑ i : Fin bs.length, ((bs[i.1]'i.2).toNat : R) * B ^ (bs.length - 1 - i.1) := by
  induction bs with
  | nil =>
      simp
  | cons b bs ih =>
      let f : Fin (bs.length + 1) → R := fun i =>
        (((b :: bs)[i.1]'i.2).toNat : R) * B ^ ((b :: bs).length - 1 - i.1)
      have hsum :
          (∑ i : Fin (b :: bs).length,
            (((b :: bs)[i.1]'i.2).toNat : R) * B ^ ((b :: bs).length - 1 - i.1)) =
          ∑ i : Fin (bs.length + 1), f i := rfl
      rw [evalBytesBase_cons, ih, hsum, Fin.sum_univ_succ]
      dsimp only [f]
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, List.getElem_cons_zero,
        Fin.val_zero, Fin.val_succ, List.getElem_cons_succ]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have hsub : bs.length - (i.1 + 1) = bs.length - 1 - i.1 := by omega
      rw [hsub]

/-- Precomputed per-token ROM tuple `(len_t, B^{len_t}, evalBytes B (V t))`. -/
structure TokenRomEntry (R : Type*) where
  len : ℕ
  pow : R
  val : R
deriving DecidableEq, Repr

/-- Build the ROM entry for token `t` under byte embedding `emb` and base `B`. -/
def tokenRomEntryWith {R : Type*} [CommRing R] {TokId : Type*}
    (emb : UInt8 → R) (V : Vocab TokId) (B : R) (t : TokId) : TokenRomEntry R :=
  { len := (V t).length
    pow := B ^ (V t).length
    val := evalBytesWith emb B (V t) }

/-- Build the canonical ROM entry `(len_t, B^{len_t}, evalBytesBase B (V t))`. -/
def tokenRomEntry {R : Type*} [CommRing R] {TokId : Type*}
    (V : Vocab TokId) (B : R) (t : TokId) : TokenRomEntry R :=
  tokenRomEntryWith (fun b => (b.toNat : R)) V B t

/-- **Degree-2 Affine Token Rolling Step (`stepTokenRoll`).**
Advances `(acc, totalLen)` across one variable-length token in **1 multiplication + 1 addition**
with zero per-character inner loop! -/
def stepTokenRoll {R : Type*} [CommRing R]
    (st : R × ℕ) (rom : TokenRomEntry R) : R × ℕ :=
  (st.1 * rom.pow + rom.val, st.2 + rom.len)

/-- Fold `stepTokenRoll` across token sequence `ts` under byte embedding `emb`. -/
def rollTokensWith {R : Type*} [CommRing R] {TokId : Type*}
    (emb : UInt8 → R) (V : Vocab TokId) (B : R) (ts : List TokId) : R × ℕ :=
  ts.foldl (fun st t => stepTokenRoll st (tokenRomEntryWith emb V B t)) (0, 0)

/-- Fold `stepTokenRoll` across token sequence `ts` under `evalBytesBase`. -/
def rollTokens {R : Type*} [CommRing R] {TokId : Type*}
    (V : Vocab TokId) (B : R) (ts : List TokId) : R × ℕ :=
  rollTokensWith (fun b => (b.toNat : R)) V B ts

private theorem foldl_stepTokenRoll_shift {R : Type*} [CommRing R] {TokId : Type*}
    (emb : UInt8 → R) (V : Vocab TokId) (B : R) :
    ∀ (ts : List TokId) (st : R × ℕ),
      ts.foldl (fun s t => stepTokenRoll s (tokenRomEntryWith emb V B t)) st =
        (st.1 * B ^ (detok V ts).length + evalBytesWith emb B (detok V ts),
         st.2 + (detok V ts).length) := by
  intro ts
  induction ts with
  | nil =>
      intro st
      cases st
      simp [detok]
  | cons t ts ih =>
      intro st
      rw [List.foldl_cons, ih, detok_cons, List.length_append, evalBytesWith_append]
      simp only [stepTokenRoll, tokenRomEntryWith, pow_add]
      ext <;> dsimp <;> ring

/-- **Variable-Length Token-to-Byte Rolling Identity (`rollTokensWith_eq_evalBytesWith_detok`).**
Over **any** `[CommRing R]` and **any** byte embedding `emb : UInt8 → R` (covering prime fields
AND characteristic-2 `Tower256`!), the degree-2 per-token ROM fold equals `(evalBytes, byteLen)`
of `detok V ts` on the nose. -/
theorem rollTokensWith_eq_evalBytesWith_detok {R : Type*} [CommRing R] {TokId : Type*}
    (emb : UInt8 → R) (V : Vocab TokId) (B : R) (ts : List TokId) :
    rollTokensWith emb V B ts =
      (evalBytesWith emb B (detok V ts), (detok V ts).length) := by
  unfold rollTokensWith
  rw [foldl_stepTokenRoll_shift emb V B ts (0, 0)]
  simp

/-- **Variable-Length Token-to-Byte Rolling Identity (`rollTokens_eq_evalBytes_detok`).** -/
theorem rollTokens_eq_evalBytes_detok {R : Type*} [CommRing R] {TokId : Type*}
    (V : Vocab TokId) (B : R) (ts : List TokId) :
    rollTokens V B ts = (evalBytesBase B (detok V ts), (detok V ts).length) :=
  rollTokensWith_eq_evalBytesWith_detok (fun b => (b.toNat : R)) V B ts

/-- **Split-Token Rolling Invariance (`rollTokens_eq_of_detok_eq`).**
Any two non-canonical BPE token sequences `ts₁, ts₂` detokenizing to the same byte stream
produce the **exact same** `(acc, totalLen)` state over every `CommRing R` and every base `B`. -/
theorem rollTokens_eq_of_detok_eq {R : Type*} [CommRing R] {TokId : Type*}
    (V : Vocab TokId) (B : R) {ts₁ ts₂ : List TokId}
    (hdetok : detok V ts₁ = detok V ts₂) :
    rollTokens V B ts₁ = rollTokens V B ts₂ := by
  rw [rollTokens_eq_evalBytes_detok, rollTokens_eq_evalBytes_detok, hdetok]

/-- Naturality of `evalBytesBase` under any ring homomorphism `f : R →+* S` (e.g. `ℤ →+* ZMod p`). -/
theorem evalBytesBase_map_ringHom {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (B : R) (bs : List UInt8) :
    f (evalBytesBase B bs) = evalBytesBase (f B) bs := by
  induction bs using List.reverseRecOn with
  | nil =>
      simp [evalBytesBase]
  | append_singleton xs b ih =>
      simp [evalBytesBase_snoc, ih]

/-- Naturality of `rollTokens` under any ring homomorphism `f : R →+* S`. -/
theorem rollTokens_map_ringHom {R S : Type*} [CommRing R] [CommRing S] {TokId : Type*}
    (f : R →+* S) (V : Vocab TokId) (B : R) (ts : List TokId) :
    (f (rollTokens V B ts).1, (rollTokens V B ts).2) = rollTokens V (f B) ts := by
  rw [rollTokens_eq_evalBytes_detok, rollTokens_eq_evalBytes_detok, evalBytesBase_map_ringHom]

/-! ## §3. Schwartz–Zippel Polynomial Soundness & Load-Bearing Falsifier Teeth -/

/-- Lift `bs : List UInt8` to its formal Horner polynomial in `Polynomial R` under `emb`. -/
noncomputable def bytePolyWith {R : Type*} [CommRing R]
    (emb : UInt8 → R) (bs : List UInt8) : Polynomial R :=
  bs.foldl (fun p b => p * X + C (emb b)) 0

/-- Canonical `Nat.cast` polynomial lift of `bs : List UInt8`. -/
noncomputable def bytePoly (R : Type*) [CommRing R] (bs : List UInt8) : Polynomial R :=
  bytePolyWith (fun b => (b.toNat : R)) bs

@[simp] theorem bytePolyWith_nil {R : Type*} [CommRing R] (emb : UInt8 → R) :
    bytePolyWith emb [] = 0 := rfl

@[simp] theorem bytePolyWith_snoc {R : Type*} [CommRing R]
    (emb : UInt8 → R) (xs : List UInt8) (b : UInt8) :
    bytePolyWith emb (xs ++ [b]) = bytePolyWith emb xs * X + C (emb b) := by
  simp [bytePolyWith]

/-- Evaluating `bytePolyWith emb bs` at `B : R` yields `evalBytesWith emb B bs`. -/
theorem eval_bytePolyWith {R : Type*} [CommRing R]
    (emb : UInt8 → R) (B : R) (bs : List UInt8) :
    (bytePolyWith emb bs).eval B = evalBytesWith emb B bs := by
  induction bs using List.reverseRecOn with
  | nil =>
      simp [bytePolyWith, evalBytesWith]
  | append_singleton xs b ih =>
      simp [bytePolyWith_snoc, evalBytesWith_snoc, ih]

theorem eval_bytePoly {R : Type*} [CommRing R] (B : R) (bs : List UInt8) :
    (bytePoly R bs).eval B = evalBytesBase B bs :=
  eval_bytePolyWith (fun b => (b.toNat : R)) B bs

private theorem coeff_bytePolyWith_eq_zero_of_le {R : Type*} [CommRing R]
    (emb : UInt8 → R) :
    ∀ (bs : List UInt8) (k : ℕ), bs.length ≤ k → (bytePolyWith emb bs).coeff k = 0 := by
  intro bs
  induction bs using List.reverseRecOn with
  | nil =>
      intro k _
      simp
  | append_singleton xs b ih =>
      intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [bytePolyWith_snoc, coeff_add, coeff_mul_X, coeff_C_succ, add_zero]
      exact ih k' (by omega)

/-- Degree bound: for every `bs`, `bytePolyWith emb bs` equals `0` or has `natDegree < bs.length`. -/
theorem bytePolyWith_eq_zero_or_natDegree_lt {R : Type*} [CommRing R]
    (emb : UInt8 → R) (bs : List UInt8) :
    bytePolyWith emb bs = 0 ∨ (bytePolyWith emb bs).natDegree < bs.length := by
  by_cases h0 : bytePolyWith emb bs = 0
  · exact Or.inl h0
  · right
    by_contra hnotlt
    have hle : bs.length ≤ (bytePolyWith emb bs).natDegree := Nat.le_of_not_lt hnotlt
    have hlead : (bytePolyWith emb bs).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr h0
    rw [leadingCoeff, coeff_bytePolyWith_eq_zero_of_le emb bs _ hle] at hlead
    exact hlead rfl

theorem natDegree_sub_bytePolyWith_lt {R : Type*} [CommRing R]
    (emb : UInt8 → R) {bs₁ bs₂ : List UInt8}
    (hlen : bs₁.length = bs₂.length) (hpos : 0 < bs₁.length) :
    (bytePolyWith emb bs₁ - bytePolyWith emb bs₂).natDegree < bs₁.length := by
  have h1 : (bytePolyWith emb bs₁).natDegree < bs₁.length := by
    rcases bytePolyWith_eq_zero_or_natDegree_lt emb bs₁ with h0 | hlt
    · simpa [h0] using hpos
    · exact hlt
  have h2 : (bytePolyWith emb bs₂).natDegree < bs₁.length := by
    rcases bytePolyWith_eq_zero_or_natDegree_lt emb bs₂ with h0 | hlt
    · simpa [h0] using hpos
    · omega
  exact (natDegree_sub_le _ _).trans_lt (max_lt h1 h2)

private theorem list_eq_snoc_of_pos_length {α : Type*} :
    ∀ (ys : List α), 0 < ys.length → ∃ xs y, ys = xs ++ [y] := by
  intro ys
  induction ys using List.reverseRecOn with
  | nil =>
      intro h
      simp at h
  | append_singleton xs y _ =>
      intro _
      exact ⟨xs, y, rfl⟩

/-- Equal-length injectivity of `bytePolyWith` whenever `emb : UInt8 → R` is injective. -/
theorem bytePolyWith_injective_of_length_eq {R : Type*} [CommRing R]
    {emb : UInt8 → R} (hemb : Function.Injective emb) :
    ∀ {bs₁ bs₂ : List UInt8},
      bs₁.length = bs₂.length →
      bytePolyWith emb bs₁ = bytePolyWith emb bs₂ →
      bs₁ = bs₂ := by
  intro bs₁
  induction bs₁ using List.reverseRecOn with
  | nil =>
      intro bs₂ hlen _
      exact (List.eq_nil_of_length_eq_zero hlen.symm).symm
  | append_singleton xs₁ b₁ ih =>
      intro bs₂ hlen hpoly
      have hpos₂ : 0 < bs₂.length := by
        rw [← hlen, List.length_append, List.length_singleton]
        omega
      obtain ⟨xs₂, b₂, rfl⟩ := list_eq_snoc_of_pos_length bs₂ hpos₂
      simp only [List.length_append, List.length_singleton] at hlen
      have hlen' : xs₁.length = xs₂.length := by omega
      rw [bytePolyWith_snoc, bytePolyWith_snoc] at hpoly
      have hc0 := congr_arg (fun q => q.coeff 0) hpoly
      simp only [coeff_add, coeff_mul_X_zero, zero_add, coeff_C_zero] at hc0
      have hb : b₁ = b₂ := hemb hc0
      have hxsPoly : bytePolyWith emb xs₁ = bytePolyWith emb xs₂ := by
        ext k
        have hck := congr_arg (fun q => q.coeff (k + 1)) hpoly
        simpa [coeff_add, coeff_mul_X, coeff_C_succ] using hck
      rw [ih hlen' hxsPoly, hb]

/-- **General Schwartz–Zippel Root Dichotomy (`evalBytesWith_eq_imp_bytes_eq_or_root`).**
Over **any** `[Field F]` (`Ext4` OR `Tower256`!) with an injective byte embedding `emb : UInt8 → F`,
two equal-length byte streams colliding at `evalBytesWith emb B` are either byte-for-byte identical
or witness `B` as a root of a nonzero polynomial of degree `< bs₁.length` (`≤ L - 1`). -/
theorem evalBytesWith_eq_imp_bytes_eq_or_root {F : Type*} [Field F]
    {emb : UInt8 → F} (hemb : Function.Injective emb)
    {bs₁ bs₂ : List UInt8} (B : F)
    (hlen : bs₁.length = bs₂.length)
    (heval : evalBytesWith emb B bs₁ = evalBytesWith emb B bs₂) :
    bs₁ = bs₂ ∨
      (bytePolyWith emb bs₁ - bytePolyWith emb bs₂ ≠ 0 ∧
       (bytePolyWith emb bs₁ - bytePolyWith emb bs₂).natDegree < bs₁.length ∧
       (bytePolyWith emb bs₁ - bytePolyWith emb bs₂).IsRoot B) := by
  by_cases heq : bs₁ = bs₂
  · exact Or.inl heq
  · right
    have hpos : 0 < bs₁.length := by
      cases bs₁ with
      | nil =>
          have hbs₂ : bs₂ = [] := List.eq_nil_of_length_eq_zero hlen.symm
          exact absurd (hbs₂.symm) heq
      | cons _ _ => simp
    have hnePoly : bytePolyWith emb bs₁ - bytePolyWith emb bs₂ ≠ 0 := by
      intro hsub
      exact heq (bytePolyWith_injective_of_length_eq hemb hlen (sub_eq_zero.mp hsub))
    have hroot : (bytePolyWith emb bs₁ - bytePolyWith emb bs₂).IsRoot B := by
      rw [IsRoot.def, eval_sub, eval_bytePolyWith, eval_bytePolyWith, heval, sub_self]
    exact ⟨hnePoly, natDegree_sub_bytePolyWith_lt emb hlen hpos, hroot⟩

/-- **Schwartz–Zippel Bad-Challenge Cardinality Bound (`card_colliding_bases_le`).**
For any finite challenge set `S : Finset F` and distinct `L`-byte streams `bs₁ ≠ bs₂`, at most
`L - 1` challenges `B ∈ S` yield an undetected byte-stream collision. -/
theorem card_colliding_bases_le {F : Type*} [Field F] [DecidableEq F]
    {emb : UInt8 → F} (hemb : Function.Injective emb)
    (S : Finset F) {bs₁ bs₂ : List UInt8}
    (hlen : bs₁.length = bs₂.length) (hne : bs₁ ≠ bs₂) :
    (S.filter (fun B => evalBytesWith emb B bs₁ = evalBytesWith emb B bs₂)).card ≤
      bs₁.length - 1 := by
  classical
  let Δ := bytePolyWith emb bs₁ - bytePolyWith emb bs₂
  have hpos : 0 < bs₁.length := by
    cases bs₁ with
    | nil =>
        have hbs₂ : bs₂ = [] := List.eq_nil_of_length_eq_zero hlen.symm
        exact absurd hbs₂.symm hne
    | cons _ _ => simp
  have hneΔ : Δ ≠ 0 := fun h0 =>
    hne (bytePolyWith_injective_of_length_eq hemb hlen (sub_eq_zero.mp h0))
  have hdeg : Δ.natDegree ≤ bs₁.length - 1 := by
    have hlt : Δ.natDegree < bs₁.length := natDegree_sub_bytePolyWith_lt emb hlen hpos
    omega
  have hsub : S.filter (fun B => evalBytesWith emb B bs₁ = evalBytesWith emb B bs₂) ⊆
      Δ.roots.toFinset := by
    intro B hB
    have hev := (Finset.mem_filter.mp hB).2
    rw [Multiset.mem_toFinset, mem_roots hneΔ, IsRoot.def]
    simp [Δ, eval_bytePolyWith, hev]
  calc (S.filter (fun B => evalBytesWith emb B bs₁ = evalBytesWith emb B bs₂)).card
      ≤ Δ.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Δ.roots.card := Multiset.toFinset_card_le _
    _ ≤ Δ.natDegree := Polynomial.card_roots' Δ
    _ ≤ bs₁.length - 1 := hdeg

/-- **Schwartz–Zippel Soundness Error Ratio (`schwartz_zippel_collision_ratio_le`).**
Over a uniform draw from any non-empty challenge set `S : Finset F` (including `S = Finset.univ` on
`[Fintype F]`, where `S.card = Fintype.card F`), collision probability is `≤ (L - 1) / |S|`. -/
theorem schwartz_zippel_collision_ratio_le {F : Type*} [Field F] [DecidableEq F]
    {emb : UInt8 → F} (hemb : Function.Injective emb)
    (S : Finset F) (hS : 0 < S.card) {bs₁ bs₂ : List UInt8}
    (hlen : bs₁.length = bs₂.length) (hne : bs₁ ≠ bs₂) :
    ((S.filter (fun B => evalBytesWith emb B bs₁ = evalBytesWith emb B bs₂)).card : ℚ) /
        (S.card : ℚ) ≤
      ((bs₁.length - 1 : ℕ) : ℚ) / (S.card : ℚ) := by
  have hnum :
      ((S.filter (fun B => evalBytesWith emb B bs₁ = evalBytesWith emb B bs₂)).card : ℚ) ≤
        ((bs₁.length - 1 : ℕ) : ℚ) := by
    exact_mod_cast card_colliding_bases_le hemb S hlen hne
  have hpos : (0 : ℚ) < (S.card : ℚ) := by exact_mod_cast hS
  exact div_le_div_of_nonneg_right hnum (le_of_lt hpos)

/-- Injectivity of `b ↦ (b.toNat : F)` whenever `ringChar F = 0 ∨ 256 ≤ ringChar F`
(covers `ℚ`, `ℤ`, `BabyBear`, `BabyBear Ext4`, and `p61`). -/
theorem natCast_uint8_injective_of_ringChar {F : Type*} [Field F]
    (hchar : ringChar F = 0 ∨ 256 ≤ ringChar F) :
    Function.Injective (fun b : UInt8 => (b.toNat : F)) := by
  have hlt_absurd : ∀ {u v : UInt8}, u.toNat < v.toNat → (u.toNat : F) = (v.toNat : F) → False := by
    intro u v hlt heq
    have hv : v.toNat < 256 := v.toBitVec.isLt
    let d : ℕ := v.toNat - u.toNat
    have hd_pos : 0 < d := by omega
    have hd_lt : d < 256 := by omega
    have hd_cast : (d : F) = 0 := by
      have hadd : u.toNat + d = v.toNat := by omega
      have hcast := congr_arg (Nat.cast (R := F)) hadd
      rw [Nat.cast_add, heq] at hcast
      linear_combination hcast
    have hdvd : ringChar F ∣ d := (ringChar.spec F d).mp hd_cast
    rcases hchar with hc0 | hc256
    · rw [hc0, zero_dvd_iff] at hdvd
      omega
    · have hle : ringChar F ≤ d := Nat.le_of_dvd hd_pos hdvd
      omega
  intro b₁ b₂ heq
  dsimp only at heq
  by_contra hne
  have hneNat : b₁.toNat ≠ b₂.toNat := fun h => hne (UInt8.ext h)
  rcases Nat.lt_or_gt_of_ne hneNat with h12 | h21
  · exact hlt_absurd h12 heq
  · exact hlt_absurd h21 heq.symm

/-- **`evalBytesBase_eq_imp_bytes_eq_or_root` (Canonical `Nat.cast` Specialization).** -/
theorem evalBytesBase_eq_imp_bytes_eq_or_root {F : Type*} [Field F]
    (hchar : ringChar F = 0 ∨ 256 ≤ ringChar F)
    {bs₁ bs₂ : List UInt8} (B : F)
    (hlen : bs₁.length = bs₂.length)
    (heval : evalBytesBase B bs₁ = evalBytesBase B bs₂) :
    bs₁ = bs₂ ∨
      (bytePoly F bs₁ - bytePoly F bs₂ ≠ 0 ∧
       (bytePoly F bs₁ - bytePoly F bs₂).natDegree < bs₁.length ∧
       (bytePoly F bs₁ - bytePoly F bs₂).IsRoot B) :=
  evalBytesWith_eq_imp_bytes_eq_or_root (natCast_uint8_injective_of_ringChar hchar) B hlen heval

/-- **Falsifier Tooth 1 — Why Binding `totalLen` Alongside `acc` Is Strictly Load-Bearing
(`leadingZero_length_omission_falsifier`).**
`[0, 65]` (`"\x00A"`, Qwen tokens `[188, 32]`) and `[65]` (`"A"`, Qwen token `[32]`) are distinct
byte streams, yet they evaluate to the **exact same** `evalBytesBase B` for **every** base `B` in
**every** commutative ring `R`! -/
theorem leadingZero_length_omission_falsifier :
    ([0, 65] : List UInt8) ≠ [65] ∧
    ([0, 65] : List UInt8).length ≠ ([65] : List UInt8).length ∧
    ∀ {R : Type*} [CommRing R] (B : R),
      evalBytesBase B [0, 65] = evalBytesBase B [65] := by
  refine ⟨by decide, by decide, ?_⟩
  intro R _ B
  change ((0 * B + ((0 : UInt8).toNat : R)) * B + ((65 : UInt8).toNat : R)) =
    (0 * B + ((65 : UInt8).toNat : R))
  simp

/-- **Falsifier Tooth 2 — Why Characteristic-2 (`Tower256`) Requires Injective `GF(2^8)` Basis
Embedding Rather Than `Nat.cast` (`char2_natCast_alias_falsifier`).**
Over `ZMod 2`, equal-length `[65]` (`"A"`) and `[67]` (`"C"`) are distinct 1-byte streams, yet
`evalBytesBase B [65] = evalBytesBase B [67]` at **every** base `B : ZMod 2`! -/
theorem char2_natCast_alias_falsifier :
    ([65] : List UInt8) ≠ [67] ∧
    ([65] : List UInt8).length = ([67] : List UInt8).length ∧
    ∀ B : ZMod 2, evalBytesBase B [65] = evalBytesBase B [67] := by
  refine ⟨by decide, by decide, ?_⟩
  intro B
  simp [evalBytesBase]
  decide

/-- **Tightness & Colliding-Root Branch Inhabitation (`colliding_root_branch_inhabited`).**
Over `ZMod 7` (`Fact (Nat.Prime 7)`), distinct equal-length 2-byte streams `[1, 5]` and `[2, 3]`
collide at `B = (2 : ZMod 7)` (`1·2 + 5 = 7 ≡ 0` and `2·2 + 3 = 7 ≡ 0`), inhabiting the root branch
and achieving the **exact tight Schwartz–Zippel bound** `#bad = 1 = L - 1` across `Finset.univ`! -/
theorem colliding_root_branch_inhabited :
    ([1, 5] : List UInt8) ≠ [2, 3] ∧
    ([1, 5] : List UInt8).length = ([2, 3] : List UInt8).length ∧
    evalBytesBase (2 : ZMod 7) [1, 5] = evalBytesBase (2 : ZMod 7) [2, 3] ∧
    ((Finset.univ : Finset (ZMod 7)).filter
      (fun B => evalBytesBase B [1, 5] = evalBytesBase B [2, 3])).card =
        ([1, 5] : List UInt8).length - 1 := by
  decide

/-! ## §4. Fixed-Base `ℤ` Radix Injectivity & `IntegerFingerprint` Cross-Characteristic Soundness -/

/-- Exact integer bounds `[0, 256^{|bs|})` for fixed-base `B = 256` evaluation over `ℤ`. -/
theorem evalBytesInt_bounds (bs : List UInt8) :
    0 ≤ evalBytesBase (256 : ℤ) bs ∧
      evalBytesBase (256 : ℤ) bs < (256 : ℤ) ^ bs.length := by
  induction bs using List.reverseRecOn with
  | nil =>
      simp [evalBytesBase]
  | append_singleton xs b ih =>
      rw [evalBytesBase_snoc, List.length_append, List.length_singleton, pow_succ]
      have hb0 : (0 : ℤ) ≤ (b.toNat : ℤ) := Nat.cast_nonneg _
      have hb256 : (b.toNat : ℤ) < 256 := by exact_mod_cast b.toBitVec.isLt
      constructor <;> linarith [ih.1, ih.2]

/-- **Unconditional Injectivity of `(length, evalBytesBase 256)` over `ℤ`
(`evalBytesInt_injective_of_length_eq`).** -/
theorem evalBytesInt_injective_of_length_eq :
    ∀ {bs₁ bs₂ : List UInt8},
      bs₁.length = bs₂.length →
      evalBytesBase (256 : ℤ) bs₁ = evalBytesBase (256 : ℤ) bs₂ →
      bs₁ = bs₂ := by
  intro bs₁
  induction bs₁ using List.reverseRecOn with
  | nil =>
      intro bs₂ hlen _
      exact (List.eq_nil_of_length_eq_zero hlen.symm).symm
  | append_singleton xs₁ b₁ ih =>
      intro bs₂ hlen heq
      have hpos₂ : 0 < bs₂.length := by
        rw [← hlen, List.length_append, List.length_singleton]
        omega
      obtain ⟨xs₂, b₂, rfl⟩ := list_eq_snoc_of_pos_length bs₂ hpos₂
      simp only [List.length_append, List.length_singleton] at hlen
      rw [evalBytesBase_snoc, evalBytesBase_snoc] at heq
      have hb₁_lt : (b₁.toNat : ℤ) < 256 := by exact_mod_cast b₁.toBitVec.isLt
      have hb₂_lt : (b₂.toNat : ℤ) < 256 := by exact_mod_cast b₂.toBitVec.isLt
      have hb₁_0 : (0 : ℤ) ≤ (b₁.toNat : ℤ) := Nat.cast_nonneg _
      have hb₂_0 : (0 : ℤ) ≤ (b₂.toNat : ℤ) := Nat.cast_nonneg _
      have hmod := congr_arg (· % (256 : ℤ)) heq
      have hrem1 : (evalBytesBase (256 : ℤ) xs₁ * 256 + (b₁.toNat : ℤ)) % 256 = (b₁.toNat : ℤ) := by
        rw [Int.mul_comm, Int.mul_add_emod_self_left, Int.emod_eq_of_lt hb₁_0 hb₁_lt]
      have hrem2 : (evalBytesBase (256 : ℤ) xs₂ * 256 + (b₂.toNat : ℤ)) % 256 = (b₂.toNat : ℤ) := by
        rw [Int.mul_comm, Int.mul_add_emod_self_left, Int.emod_eq_of_lt hb₂_0 hb₂_lt]
      rw [hrem1, hrem2] at hmod
      have hbNat : b₁.toNat = b₂.toNat := Int.ofNat.inj hmod
      have hbEq : b₁ = b₂ := UInt8.ext hbNat
      have hxsVal : evalBytesBase (256 : ℤ) xs₁ = evalBytesBase (256 : ℤ) xs₂ := by
        linarith
      rw [ih (by omega) hxsVal, hbEq]

/-- **`IntegerFingerprint.Row` Packaging for Fixed-Base Token-to-Byte Cross-Characteristic Weld.**
Encodes the integer equality `(rollTokens V 256 ts).1 * 1 = evalBytesBase 256 bs + 0 * 0`,
whose mod-`p` fingerprint is literally the prime-field rolling identity in `ZMod p`! -/
def tokenByteWeldRow {TokId : Type*} (V : Vocab TokId) (ts : List TokId) (bs : List UInt8) :
    Row :=
  { a := (rollTokens V (256 : ℤ) ts).1
    b := 1
    c := evalBytesBase (256 : ℤ) bs
    u := 0
    m := 0 }

/-- Under matching byte lengths, `tokenByteWeldRow` holds over `ℤ` **if and only if**
`detok V ts = bs` byte-for-byte. -/
theorem tokenByteWeldRow_holdsInt_iff_detok_eq {TokId : Type*}
    (V : Vocab TokId) (ts : List TokId) (bs : List UInt8)
    (hlen : (rollTokens V (256 : ℤ) ts).2 = bs.length) :
    (tokenByteWeldRow V ts bs).HoldsInt ↔ detok V ts = bs := by
  have hlenDetok : (detok V ts).length = bs.length := by
    simpa [rollTokens_eq_evalBytes_detok] using hlen
  unfold tokenByteWeldRow Row.HoldsInt
  simp only [mul_one, mul_zero, add_zero, rollTokens_eq_evalBytes_detok]
  exact ⟨evalBytesInt_injective_of_length_eq hlenDetok, fun h => by rw [h]⟩

/-- Fingerprinting `tokenByteWeldRow` at modulus `p` is **equivalent** to checking the degree-2
token-ROM rolling hash against `evalBytesBase` directly inside `ZMod p`! -/
theorem tokenByteWeldRow_holdsMod_iff_zmod_eq {TokId : Type*}
    (V : Vocab TokId) (ts : List TokId) (bs : List UInt8) (p : ℕ) :
    (tokenByteWeldRow V ts bs).HoldsMod p ↔
      (rollTokens V (256 : ZMod p) ts).1 = evalBytesBase (256 : ZMod p) bs := by
  unfold tokenByteWeldRow Row.HoldsMod
  simp only [mul_one, mul_zero, add_zero]
  rw [← ZMod.intCast_eq_intCast_iff]
  have h1 := congr_arg Prod.fst (rollTokens_map_ringHom (Int.castRingHom (ZMod p)) V (256 : ℤ) ts)
  have h2 := evalBytesBase_map_ringHom (Int.castRingHom (ZMod p)) (256 : ℤ) bs
  simpa using Iff.intro (fun h => h1.symm.trans (h.trans h2)) (fun h => h1.trans (h.trans h2.symm))

/-- Residual magnitude bound `|residual| ≤ 256^L - 1 < 256^L` for any equal-length `ts, bs`. -/
theorem tokenByteWeldRow_residual_natAbs_lt {TokId : Type*}
    (V : Vocab TokId) (ts : List TokId) (bs : List UInt8)
    (hlen : (rollTokens V (256 : ℤ) ts).2 = bs.length) :
    (tokenByteWeldRow V ts bs).residual.natAbs ≤ 256 ^ bs.length - 1 ∧
      (tokenByteWeldRow V ts bs).residual.natAbs < 256 ^ bs.length := by
  have hlenDetok : (detok V ts).length = bs.length := by
    simpa [rollTokens_eq_evalBytes_detok] using hlen
  have hb₁ := evalBytesInt_bounds (detok V ts)
  have hb₂ := evalBytesInt_bounds bs
  rw [hlenDetok] at hb₁
  have hres : (tokenByteWeldRow V ts bs).residual =
      evalBytesBase (256 : ℤ) (detok V ts) - evalBytesBase (256 : ℤ) bs := by
    simp [tokenByteWeldRow, Row.residual, rollTokens_eq_evalBytes_detok]
  have hpowPos : (0 : ℤ) < (256 : ℤ) ^ bs.length := by positivity
  have habsLt : |(tokenByteWeldRow V ts bs).residual| < (256 : ℤ) ^ bs.length := by
    rw [hres, abs_lt]
    constructor <;> linarith
  have hnatLt : (tokenByteWeldRow V ts bs).residual.natAbs < 256 ^ bs.length := by
    have hcast : ((tokenByteWeldRow V ts bs).residual.natAbs : ℤ) =
        |(tokenByteWeldRow V ts bs).residual| := Int.natCast_natAbs _
    have hpowCast : ((256 ^ bs.length : ℕ) : ℤ) = (256 : ℤ) ^ bs.length := by norm_cast
    rw [← hcast, ← hpowCast] at habsLt
    exact_mod_cast habsLt
  exact ⟨by omega, hnatLt⟩

/-- **`dualChar_integer_fingerprint_bound` — Cross-Characteristic Soundness via `Theory.IntegerFingerprint`.**
Connects fixed-base (`B = 256`) `L`-byte token-to-byte welding directly to
`Theory.IntegerFingerprint.pow_card_undetected_le`, `card_undetected_le_log`, and
`fingerprint_error_ratio_le`: if `detok V ts ≠ bs` (with matching length `L`), then across any
prime sampling space `space` bounded below by `P_floor > 1`:
1. `P_floor ^ (#bad primes) ≤ |residual| < 256^L`,
2. `#bad primes ≤ log_{P_floor} (256^L - 1) ≤ log_{P_floor} (256^L)`, and
3. The undetected prime fraction is at most `log_{P_floor} (256^L) / spaceFloor`. -/
theorem dualChar_integer_fingerprint_bound {TokId : Type*}
    (V : Vocab TokId) (ts : List TokId) (bs : List UInt8)
    (space : Finset ℕ) (P_floor spaceFloor : ℕ)
    (hlen : (rollTokens V (256 : ℤ) ts).2 = bs.length)
    (hne : detok V ts ≠ bs)
    (hP : 1 < P_floor)
    (hprime : ∀ p ∈ space, Nat.Prime p)
    (hfloor : ∀ p ∈ space, P_floor ≤ p)
    (hfloorPos : 0 < spaceFloor)
    (hspace : spaceFloor ≤ space.card) :
    P_floor ^ (undetected space (tokenByteWeldRow V ts bs)).card
      ≤ (tokenByteWeldRow V ts bs).residual.natAbs ∧
    (tokenByteWeldRow V ts bs).residual.natAbs < 256 ^ bs.length ∧
    (undetected space (tokenByteWeldRow V ts bs)).card
      ≤ Nat.log P_floor (256 ^ bs.length) ∧
    ((undetected space (tokenByteWeldRow V ts bs)).card : ℚ) / (space.card : ℚ)
      ≤ (Nat.log P_floor (256 ^ bs.length) : ℚ) / (spaceFloor : ℚ) := by
  have hfail : ¬ (tokenByteWeldRow V ts bs).HoldsInt := fun h =>
    hne ((tokenByteWeldRow_holdsInt_iff_detok_eq V ts bs hlen).mp h)
  have ⟨hresLe, hresLt⟩ := tokenByteWeldRow_residual_natAbs_lt V ts bs hlen
  have hbound : (tokenByteWeldRow V ts bs).residual.natAbs ≤ 256 ^ bs.length := le_of_lt hresLt
  refine ⟨pow_card_undetected_le hfail hprime hfloor, hresLt, ?_, ?_⟩
  · exact (card_undetected_le_log hP hfail hprime hfloor).trans (Nat.log_mono_right hbound)
  · exact fingerprint_error_ratio_le hP hfail hprime hfloor hbound hfloorPos hspace

/-! ### Premise Inhabitation for `dualChar_integer_fingerprint_bound` -/

/-- Forged byte target `"sk-porj"` (transposing `'r'` = 114 and `'o'` = 111 vs `detok splitSeqA = "sk-proj"`,
yielding residual `(114 - 111)·256^2 + (111 - 114)·256 = 195840`, divisible by prime `17`!). -/
def forgedTargetBytes : List UInt8 := asciiBytes "sk-porj"

def demoPrimeSpace : Finset ℕ := {17, 19, 23}

theorem demoPrimeSpace_prime : ∀ p ∈ demoPrimeSpace, Nat.Prime p := by
  intro p hp
  simp only [demoPrimeSpace, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl <;> norm_num

theorem demoPrimeSpace_floor : ∀ p ∈ demoPrimeSpace, 17 ≤ p := by decide

/-- **Non-Vacuity & Premise Inhabitation (`dualChar_integer_fingerprint_inhabited`).**
Inhabits every premise of `dualChar_integer_fingerprint_bound` with a non-empty undetected prime
set (`17 ∈ undetected`, since `17 ∣ 195840 = 3 · 255 · 256`) and verifies the bound in Lean's kernel. -/
theorem dualChar_integer_fingerprint_inhabited :
    (undetected demoPrimeSpace (tokenByteWeldRow demoBpeVocab splitSeqA forgedTargetBytes)).Nonempty ∧
    17 ^ (undetected demoPrimeSpace (tokenByteWeldRow demoBpeVocab splitSeqA forgedTargetBytes)).card
      ≤ (tokenByteWeldRow demoBpeVocab splitSeqA forgedTargetBytes).residual.natAbs ∧
    ((undetected demoPrimeSpace (tokenByteWeldRow demoBpeVocab splitSeqA forgedTargetBytes)).card : ℚ) /
        (demoPrimeSpace.card : ℚ)
      ≤ (Nat.log 17 (256 ^ forgedTargetBytes.length) : ℚ) / (3 : ℚ) := by
  have hmem : 17 ∈ undetected demoPrimeSpace (tokenByteWeldRow demoBpeVocab splitSeqA forgedTargetBytes) := by
    decide
  have hb := dualChar_integer_fingerprint_bound
    demoBpeVocab splitSeqA forgedTargetBytes demoPrimeSpace 17 3
    (by decide) (by decide) (by decide)
    demoPrimeSpace_prime demoPrimeSpace_floor (by decide) (by decide)
  exact ⟨⟨17, hmem⟩, hb.1, hb.2.2.2⟩

/-! ## §5. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Theory.DualCharTokenBridge.detok_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms detok_append
/-- info: 'Minidregg.Theory.DualCharTokenBridge.tokenLevelGuard_bypassed_by_bpe_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tokenLevelGuard_bypassed_by_bpe_split
/-- info: 'Minidregg.Theory.DualCharTokenBridge.detok_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms detok_not_injective
/-- info: 'Minidregg.Theory.DualCharTokenBridge.tokenFree_not_implies_byteAbsent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tokenFree_not_implies_byteAbsent
/-- info: 'Minidregg.Theory.DualCharTokenBridge.detok_redactBytes_scrubs_any_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms detok_redactBytes_scrubs_any_split
/-- info: 'Minidregg.Theory.DualCharTokenBridge.evalBytesBase_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalBytesBase_append
/-- info: 'Minidregg.Theory.DualCharTokenBridge.evalBytesBase_eq_sum_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalBytesBase_eq_sum_pow
/-- info: 'Minidregg.Theory.DualCharTokenBridge.rollTokensWith_eq_evalBytesWith_detok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rollTokensWith_eq_evalBytesWith_detok
/-- info: 'Minidregg.Theory.DualCharTokenBridge.rollTokens_eq_evalBytes_detok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rollTokens_eq_evalBytes_detok
/-- info: 'Minidregg.Theory.DualCharTokenBridge.rollTokens_eq_of_detok_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rollTokens_eq_of_detok_eq
/-- info: 'Minidregg.Theory.DualCharTokenBridge.evalBytesWith_eq_imp_bytes_eq_or_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalBytesWith_eq_imp_bytes_eq_or_root
/-- info: 'Minidregg.Theory.DualCharTokenBridge.card_colliding_bases_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms card_colliding_bases_le
/-- info: 'Minidregg.Theory.DualCharTokenBridge.schwartz_zippel_collision_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms schwartz_zippel_collision_ratio_le
/-- info: 'Minidregg.Theory.DualCharTokenBridge.evalBytesBase_eq_imp_bytes_eq_or_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalBytesBase_eq_imp_bytes_eq_or_root
/-- info: 'Minidregg.Theory.DualCharTokenBridge.leadingZero_length_omission_falsifier' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms leadingZero_length_omission_falsifier
/-- info: 'Minidregg.Theory.DualCharTokenBridge.char2_natCast_alias_falsifier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms char2_natCast_alias_falsifier
/-- info: 'Minidregg.Theory.DualCharTokenBridge.colliding_root_branch_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms colliding_root_branch_inhabited
/-- info: 'Minidregg.Theory.DualCharTokenBridge.evalBytesInt_injective_of_length_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalBytesInt_injective_of_length_eq
/-- info: 'Minidregg.Theory.DualCharTokenBridge.tokenByteWeldRow_holdsInt_iff_detok_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tokenByteWeldRow_holdsInt_iff_detok_eq
/-- info: 'Minidregg.Theory.DualCharTokenBridge.tokenByteWeldRow_holdsMod_iff_zmod_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tokenByteWeldRow_holdsMod_iff_zmod_eq
/-- info: 'Minidregg.Theory.DualCharTokenBridge.dualChar_integer_fingerprint_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dualChar_integer_fingerprint_bound
/-- info: 'Minidregg.Theory.DualCharTokenBridge.dualChar_integer_fingerprint_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dualChar_integer_fingerprint_inhabited

end Minidregg.Theory.DualCharTokenBridge
