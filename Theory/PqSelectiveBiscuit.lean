/-
# `Theory/PqSelectiveBiscuit.lean` — Post-Quantum Issuer-Root-Isolated `ZkBiscuit` Selective-Disclosure Credentials

Closes Decision `D8` and Security Bugs `CAP-01`, `CAP-10`, `CAP-12` (and `CAP-13`):
100% post-quantum (`cSHAKE256` SP 800-185 + abstract PQ signature interface `PqSigScheme`
instantiated by pure-hash `cSHAKE256` WOTS+ and compatible with `dregg-pq` Hybrid Ed25519+ML-DSA-65;
zero elliptic-curve pairings or Pedersen commitments).

1. **`CAP-01` Root-Key Isolation:** `HolderToken` structurally carries ONLY public keys,
   chained PQ signatures, and a salted `cSHAKE256` attribute Merkle root — zero `IssuerSecret`
   fields. Proves `holder_attenuate_needs_no_issuer_secret` and EUF-CMA reduction
   `block0_unforgeable_reduction`.
2. **`CAP-12` Block-0 Authority Pin & Monotone Attenuation:** `extractSubject` and
   `extractIssuerAuthority` read exclusively block `0`. Proves `attenuation_monotone_from_block0`
   plus `#tooth` `cap12_tooth_holder_appended_acct_admin_killed`.
3. **`CAP-10` Canonical Sorted / Ancestor-Cone Revocation:** Proves `RevocationSet.ofList`
   (`dedupSort` invariant) is order-independent (`ofList_order_independent`) and `100%` complete
   under binary search (`contains_ofList_iff`), proves ancestor-cone revocation kills every
   extension (`revoke_ancestor_kills_cone`), plus `#tooth` `cap10_tooth_unsorted_bsearch_miss_killed`.
4. **Salted Selective Attribute Disclosure:** Holder opens any subset `S ⊆ [0, m)` of
   `(idx, key, val, salt)` against `block0.attrMerkleRoot` (`verifyMerkleOpening_complete`,
   `verifyMerkleOpening_sound_or_collision`), keeping unrevealed attributes hidden behind
   `256`-bit per-leaf salts (`unrevealed_attr_view_independent`, `unrevealed_salt_offline_guess_bound`).

Import boundary: `Theory/` tier (`Theory.HashBytes`, `Theory.Sp800185Cshake256Core` only).
-/
import Theory.HashBytes
import Theory.Sp800185Cshake256Core

namespace Minidregg.Theory.PqSelectiveBiscuit

open Minidregg.Theory.HashBytes
open Minidregg.Compiler.Sp800185Cshake256

set_option autoImplicit false

/-! ## §1. Canonical Prefix-Free Encoding & `cSHAKE256` Binding -/

/-- Standard unsigned LEB128 encoding for arbitrary natural numbers (prefix-free). -/
def leb128 (n : Nat) : List UInt8 :=
  if h : n < 128 then [UInt8.ofNat n]
  else UInt8.ofNat (128 + n % 128) :: leb128 (n / 128)
termination_by n
decreasing_by omega

theorem leb128_prefix_inj : ∀ (a b : Nat) (r₁ r₂ : List UInt8),
    leb128 a ++ r₁ = leb128 b ++ r₂ → a = b ∧ r₁ = r₂ := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b r₁ r₂ h
    unfold leb128 at h
    split at h
    · rename_i ha
      split at h
      · rename_i hb
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        have hnat := congrArg UInt8.toNat h.1
        simp only [UInt8.toNat_ofNat'] at hnat
        exact ⟨by omega, h.2⟩
      · rename_i hb
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        have hnat := congrArg UInt8.toNat h.1
        simp only [UInt8.toNat_ofNat'] at hnat
        omega
    · rename_i ha
      split at h
      · rename_i hb
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        have hnat := congrArg UInt8.toNat h.1
        simp only [UInt8.toNat_ofNat'] at hnat
        omega
      · rename_i hb
        simp only [List.cons_append, List.cons.injEq] at h
        have hnat := congrArg UInt8.toNat h.1
        simp only [UInt8.toNat_ofNat'] at hnat
        obtain ⟨hq, hr⟩ := ih (a / 128) (by omega) (b / 128) r₁ r₂ h.2
        exact ⟨by omega, hr⟩

/-- Prefix-free length-delimited byte field. -/
def encodeField (bs : List UInt8) : List UInt8 :=
  leb128 bs.length ++ bs

theorem encodeField_prefix_inj {a b r₁ r₂ : List UInt8}
    (h : encodeField a ++ r₁ = encodeField b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold encodeField at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hlen, hrest⟩ := leb128_prefix_inj a.length b.length (a ++ r₁) (b ++ r₂) h
  exact List.append_inj hrest hlen

/-- Prefix-free encoding of a list of natural numbers. -/
def encodeNats (ns : List Nat) : List UInt8 :=
  leb128 ns.length ++ ns.flatMap leb128

private theorem flatMap_leb128_inj : ∀ (xs ys : List Nat),
    xs.length = ys.length → xs.flatMap leb128 = ys.flatMap leb128 → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨hxy, hrest⟩ := leb128_prefix_inj x y (xs.flatMap leb128) (ys.flatMap leb128) h
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    rw [hxy, flatMap_leb128_inj xs ys hlen hrest]

theorem encodeNats_injective {xs ys : List Nat} (h : encodeNats xs = encodeNats ys) : xs = ys := by
  unfold encodeNats at h
  obtain ⟨hlen, hbody⟩ := leb128_prefix_inj xs.length ys.length _ _ h
  exact flatMap_leb128_inj xs ys hlen hbody

/-- Domain-separated 32-byte SP 800-185 `cSHAKE256` digest. -/
def cshake32 (cust input : List UInt8) : List UInt8 :=
  cshake256Bytes cust input

@[simp] theorem cshake32_length (cust input : List UInt8) :
    (cshake32 cust input).length = 32 :=
  cshake256Bytes_length cust input

theorem cshake32_binds (cust : List UInt8) {x y : List UInt8}
    (h : cshake32 cust x = cshake32 cust y) :
    x = y ∨ CollisionAmong (cshake256Bytes cust) (fun z => z = x ∨ z = y) := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · exact Or.inr ⟨x, y, Or.inl rfl, Or.inr rfl, hxy, congrArg ofBE h⟩

def strBytes (s : String) : List UInt8 := s.toUTF8.toList

def custAttrLeaf  : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.ATTR_LEAF/v1"
def custAttrNode  : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.ATTR_NODE/v1"
def custLineage   : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.LINEAGE/v1"
def custNullifier : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.NULLIFIER/v1"
def custRevRoot   : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.REV_ROOT/v1"
def custBlockSig  : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.BLOCK_SIG/v1"
def custWotsChain : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.WOTS_CHAIN/v1"

/-! ## §2. Post-Quantum Signature Interface (`PqSigScheme`) & Pure-Hash `cSHAKE256` WOTS+ -/

/-- Abstract post-quantum signature interface (zero elliptic-curve pairings or Pedersen).
Instantiated by `wotsCshake256` below and compatible with `dregg-pq` Hybrid Ed25519+ML-DSA-65. -/
structure PqSigScheme where
  SecKey      : Type
  pkOf        : SecKey → List UInt8
  sign        : SecKey → List UInt8 → List UInt8
  verify      : List UInt8 → List UInt8 → List UInt8 → Bool
  verify_sign : ∀ sk msg, verify (pkOf sk) msg (sign sk msg) = true

/-! ### Concrete 256-Bit Hash-Based Post-Quantum WOTS+ (`w = 16`, `67` Chains over `cSHAKE256`) -/

def wotsChainStep (idx step : Nat) (val : List UInt8) : List UInt8 :=
  cshake32 custWotsChain (0x01 :: be 4 idx ++ be 4 step ++ val)

def wotsChainIter (idx : Nat) : Nat → Nat → List UInt8 → List UInt8
  | _, 0, val => val
  | start, steps + 1, val => wotsChainIter idx (start + 1) steps (wotsChainStep idx start val)

theorem wotsChainIter_add (idx start a b : Nat) (val : List UInt8) :
    wotsChainIter idx (start + a) b (wotsChainIter idx start a val) =
      wotsChainIter idx start (a + b) val := by
  induction a generalizing start val with
  | zero => simp [wotsChainIter]
  | succ a ih =>
    simp only [wotsChainIter, Nat.succ_add]
    have h1 : start + (a + 1) = (start + 1) + a := by omega
    rw [h1]
    exact ih (start + 1) (wotsChainStep idx start val)

def wotsSkElem (seed : List UInt8) (idx : Nat) : List UInt8 :=
  cshake32 custWotsChain (0x00 :: be 4 idx ++ seed)

/-- `64` message nibbles (from `cSHAKE256(custBlockSig, msg)`) + `3` checksum nibbles (`w = 16`). -/
def wotsDigits (msg : List UInt8) : List Nat :=
  let digest := cshake32 custBlockSig msg
  let msgNibbles := digest.flatMap fun b => [b.toNat / 16, b.toNat % 16]
  let csum := msgNibbles.foldl (fun acc d => acc + (15 - d)) 0
  msgNibbles ++ [(csum / 256) % 16, (csum / 16) % 16, csum % 16]

theorem wotsDigits_length (msg : List UInt8) : (wotsDigits msg).length = 67 := by
  unfold wotsDigits
  have hlen : (cshake32 custBlockSig msg).length = 32 := cshake32_length _ _
  have hflat : ∀ (bs : List UInt8), (bs.flatMap fun b => [b.toNat / 16, b.toNat % 16]).length = 2 * bs.length := by
    intro bs
    induction bs with
    | nil => rfl
    | cons b tl ih => simp [List.flatMap_cons, ih]; omega
  simp [hflat, hlen]

theorem wotsDigits_le_15 (msg : List UInt8) : ∀ d ∈ wotsDigits msg, d ≤ 15 := by
  unfold wotsDigits
  intro d hd
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with ⟨b, _, h1 | h2⟩ | (h3 | h4 | h5)
  · have hb := b.toNat_lt; omega
  · omega
  · omega
  · omega
  · omega

def wotsPk (seed : List UInt8) : List UInt8 :=
  let tips := (List.range 67).flatMap fun idx =>
    wotsChainIter idx 0 15 (wotsSkElem seed idx)
  cshake32 custWotsChain (0x02 :: tips)

def wotsSignAux : Nat → List UInt8 → List Nat → List UInt8
  | _, _, [] => []
  | idx, seed, d :: ds =>
      wotsChainIter idx 0 d (wotsSkElem seed idx) ++ wotsSignAux (idx + 1) seed ds

def wotsSign (seed msg : List UInt8) : List UInt8 :=
  wotsSignAux 0 seed (wotsDigits msg)

def wotsRecoverTips : Nat → List Nat → List UInt8 → List UInt8
  | _, [], _ => []
  | idx, d :: ds, sig =>
      wotsChainIter idx d (15 - d) (sig.take 32) ++ wotsRecoverTips (idx + 1) ds (sig.drop 32)

def wotsVerify (pk msg sig : List UInt8) : Bool :=
  if sig.length != 67 * 32 then false
  else cshake32 custWotsChain (0x02 :: wotsRecoverTips 0 (wotsDigits msg) sig) == pk

private theorem wotsChainIter_length (idx start steps : Nat) (val : List UInt8)
    (hlen : val.length = 32) : (wotsChainIter idx start steps val).length = 32 := by
  induction steps generalizing start val with
  | zero => exact hlen
  | succ s ih => exact ih (start + 1) _ (cshake32_length _ _)

private theorem wotsSignAux_length (idx : Nat) (seed : List UInt8) (ds : List Nat) :
    (wotsSignAux idx seed ds).length = ds.length * 32 := by
  induction ds generalizing idx with
  | nil => rfl
  | cons d tl ih =>
    simp only [wotsSignAux, List.length_append, List.length_cons,
      wotsChainIter_length idx 0 d _ (cshake32_length _ _), ih]
    omega

private theorem wotsRecoverTips_signAux (idx : Nat) (seed : List UInt8) (ds : List Nat)
    (hds : ∀ d ∈ ds, d ≤ 15) :
    wotsRecoverTips idx ds (wotsSignAux idx seed ds) =
      (List.range ds.length).flatMap fun k =>
        wotsChainIter (idx + k) 0 15 (wotsSkElem seed (idx + k)) := by
  induction ds generalizing idx with
  | nil => rfl
  | cons d tl ih =>
    have hd : d ≤ 15 := hds d (List.mem_cons_self ..)
    have htl : ∀ x ∈ tl, x ≤ 15 := fun x hx => hds x (List.mem_cons_of_mem _ hx)
    have hchunk : (wotsChainIter idx 0 d (wotsSkElem seed idx)).length = 32 :=
      wotsChainIter_length idx 0 d _ (cshake32_length _ _)
    simp only [wotsSignAux, wotsRecoverTips, List.take_left' hchunk, List.drop_left' hchunk]
    have hcomb := wotsChainIter_add idx 0 d (15 - d) (wotsSkElem seed idx)
    have hadd : d + (15 - d) = 15 := by omega
    simp only [Nat.zero_add, hadd] at hcomb
    rw [hcomb, ih (idx + 1) htl]
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, Nat.add_zero, List.flatMap_map]
    congr 1
    apply List.flatMap_congr
    intro k _
    have hk : idx + 1 + k = idx + (k + 1) := by omega
    rw [hk]

theorem wotsVerify_sign (seed msg : List UInt8) :
    wotsVerify (wotsPk seed) msg (wotsSign seed msg) = true := by
  unfold wotsVerify wotsSign wotsPk
  have hlen : (wotsSignAux 0 seed (wotsDigits msg)).length = 67 * 32 := by
    rw [wotsSignAux_length, wotsDigits_length]
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  rw [wotsRecoverTips_signAux 0 seed (wotsDigits msg) (wotsDigits_le_15 msg), wotsDigits_length]
  simp only [Nat.zero_add]

/-- Concrete 100% post-quantum pure-hash `cSHAKE256` WOTS+ signature scheme. -/
def wotsCshake256 : PqSigScheme where
  SecKey      := List UInt8
  pkOf        := wotsPk
  sign        := wotsSign
  verify      := wotsVerify
  verify_sign := wotsVerify_sign

/-! ## §3. `CAP-10` Canonical Sorted `RevocationSet` & Complete Binary Search -/

/-- Binary search for `x` in `keys[lo, hi)` (mirrors `RevocationProof::verify_non_revocation`). -/
def bsearchAux (keys : Array Nat) (x : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := lo + (hi - lo) / 2
      let v := keys.getD mid 0
      if v = x then true
      else if v < x then bsearchAux keys x fuel (mid + 1) hi
      else bsearchAux keys x fuel lo mid
    else false

def bsearch (keys : Array Nat) (x : Nat) : Bool :=
  bsearchAux keys x keys.size 0 keys.size

theorem bsearchAux_sound (keys : Array Nat) (x : Nat) : ∀ (fuel lo hi : Nat), hi ≤ keys.size →
    bsearchAux keys x fuel lo hi = true → x ∈ keys.toList
  | 0, _, _, _, h => by simp [bsearchAux] at h
  | fuel + 1, lo, hi, hsz, h => by
    by_cases hlt : lo < hi
    · have hmid : lo + (hi - lo) / 2 < keys.size := by omega
      have hget : keys.getD (lo + (hi - lo) / 2) 0 = keys[lo + (hi - lo) / 2] := by
        simp [Array.getD, hmid]
      simp only [bsearchAux, hlt, ↓reduceIte, hget] at h
      by_cases h1 : keys[lo + (hi - lo) / 2] = x
      · rw [← h1]; exact Array.getElem_mem_toList hmid
      · simp only [h1, ↓reduceIte] at h
        by_cases h2 : keys[lo + (hi - lo) / 2] < x
        · simp only [h2, ↓reduceIte] at h
          exact bsearchAux_sound keys x fuel _ hi hsz h
        · simp only [h2, ↓reduceIte] at h
          exact bsearchAux_sound keys x fuel lo _ (by omega) h
    · simp [bsearchAux, hlt] at h

theorem bsearchAux_complete (keys : Array Nat) (x : Nat)
    (hs : ∀ (i j : Nat) (hi : i < keys.size) (hj : j < keys.size), i < j → keys[i] < keys[j]) :
    ∀ (fuel lo hi : Nat), hi ≤ keys.size → hi - lo ≤ fuel →
      ∀ (i : Nat) (hi' : i < keys.size), lo ≤ i → i < hi → keys[i] = x →
        bsearchAux keys x fuel lo hi = true
  | 0, lo, hi, _, hf, _, _, hlo, hhi, _ => by omega
  | fuel + 1, lo, hi, hsz, hf, i, hi', hlo, hhi, hx => by
    have hlt : lo < hi := by omega
    have hmid : lo + (hi - lo) / 2 < keys.size := by omega
    have hget : keys.getD (lo + (hi - lo) / 2) 0 = keys[lo + (hi - lo) / 2] := by
      simp [Array.getD, hmid]
    simp only [bsearchAux, hlt, ↓reduceIte, hget]
    by_cases h1 : keys[lo + (hi - lo) / 2] = x
    · simp only [h1, ↓reduceIte]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : keys[lo + (hi - lo) / 2] < x
      · simp only [h2, ↓reduceIte]
        have hgt : lo + (hi - lo) / 2 < i := by
          rcases Nat.lt_trichotomy i (lo + (hi - lo) / 2) with h | h | h
          · have := hs i _ hi' hmid h; omega
          · subst h; exact absurd hx h1
          · exact h
        exact bsearchAux_complete keys x hs fuel _ hi hsz (by omega) i hi' (by omega) hhi hx
      · simp only [h2, ↓reduceIte]
        have hlt' : i < lo + (hi - lo) / 2 := by
          rcases Nat.lt_trichotomy i (lo + (hi - lo) / 2) with h | h | h
          · exact h
          · subst h; exact absurd hx h1
          · have := hs _ i hmid hi' h; omega
        exact bsearchAux_complete keys x hs fuel lo _ (by omega) (by omega) i hi' hlo hlt' hx

/-- Insert `x` into a strictly ascending list, deduplicating. -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x < y then x :: y :: ys else if x = y then y :: ys else y :: insertSorted x ys

theorem mem_insertSorted (x z : Nat) : ∀ (l : List Nat), z ∈ insertSorted x l ↔ z = x ∨ z ∈ l
  | [] => by simp [insertSorted]
  | y :: ys => by
    by_cases h1 : x < y
    · simp [insertSorted, h1]
    · by_cases h2 : x = y
      · subst h2; simp [insertSorted]
      · simp only [insertSorted, h1, h2, ↓reduceIte, List.mem_cons, mem_insertSorted x z ys]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)

theorem insertSorted_pairwise (x : Nat) : ∀ (l : List Nat), l.Pairwise (· < ·) →
    (insertSorted x l).Pairwise (· < ·)
  | [], _ => by simp [insertSorted]
  | y :: ys, hp => by
    obtain ⟨hy, hys⟩ := List.pairwise_cons.1 hp
    by_cases h1 : x < y
    · simp only [insertSorted, h1, ↓reduceIte]
      refine List.pairwise_cons.2 ⟨fun a ha => ?_, hp⟩
      rcases List.mem_cons.1 ha with rfl | ha'
      · exact h1
      · exact Nat.lt_trans h1 (hy a ha')
    · by_cases h2 : x = y
      · subst h2; simp only [insertSorted, Nat.lt_irrefl, ↓reduceIte]; exact hp
      · simp only [insertSorted, h1, h2, ↓reduceIte]
        refine List.pairwise_cons.2 ⟨fun a ha => ?_, insertSorted_pairwise x ys hys⟩
        rcases (mem_insertSorted x a ys).1 ha with rfl | ha'
        · omega
        · exact hy a ha'

/-- Canonical order-independent deduplicating sort (`CAP-10` invariant). -/
def dedupSort (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => insertSorted x acc) []

private theorem mem_dedupSort_aux (acc : List Nat) (xs : List Nat) (z : Nat) :
    z ∈ xs.foldl (fun a x => insertSorted x a) acc ↔ z ∈ acc ∨ z ∈ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x tl ih =>
    simp only [List.foldl_cons, ih, mem_insertSorted, List.mem_cons]
    constructor
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h

theorem mem_dedupSort_iff (xs : List Nat) (z : Nat) : z ∈ dedupSort xs ↔ z ∈ xs := by
  simpa [dedupSort] using mem_dedupSort_aux [] xs z

private theorem dedupSort_pairwise_aux (acc : List Nat) (xs : List Nat)
    (hp : acc.Pairwise (· < ·)) :
    (xs.foldl (fun a x => insertSorted x a) acc).Pairwise (· < ·) := by
  induction xs generalizing acc with
  | nil => exact hp
  | cons x tl ih => exact ih (insertSorted x acc) (insertSorted_pairwise x acc hp)

theorem dedupSort_pairwise (xs : List Nat) : (dedupSort xs).Pairwise (· < ·) :=
  dedupSort_pairwise_aux [] xs List.Pairwise.nil

/-- Strictly sorted lists with equal membership are identical. -/
theorem pairwise_lt_ext : ∀ {l₁ l₂ : List Nat},
    l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, heq => absurd ((heq y).2 (List.mem_cons_self ..)) (List.not_mem_nil ..)
  | x :: _, [], _, _, heq => absurd ((heq x).1 (List.mem_cons_self ..)) (List.not_mem_nil ..)
  | x :: xs, y :: ys, hp1, hp2, heq => by
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.1 hp1
    obtain ⟨hy, hys⟩ := List.pairwise_cons.1 hp2
    have hxy : x = y := by
      have hx2 := (heq x).1 (List.mem_cons_self ..)
      have hy1 := (heq y).2 (List.mem_cons_self ..)
      rcases List.mem_cons.1 hx2 with rfl | hx_ys
      · rfl
      · rcases List.mem_cons.1 hy1 with h' | hy_xs
        · exact h'.symm
        · have := hy x hx_ys; have := hx y hy_xs; omega
    subst hxy
    congr 1
    apply pairwise_lt_ext hxs hys
    intro z
    constructor
    · intro hz
      have hz2 := (heq z).1 (List.mem_cons_of_mem _ hz)
      rcases List.mem_cons.1 hz2 with rfl | h'
      · have := hx z hz; omega
      · exact h'
    · intro hz
      have hz1 := (heq z).2 (List.mem_cons_of_mem _ hz)
      rcases List.mem_cons.1 hz1 with rfl | h'
      · have := hy z hz; omega
      · exact h'

theorem dedupSort_order_independent {xs ys : List Nat} (h : ∀ z, z ∈ xs ↔ z ∈ ys) :
    dedupSort xs = dedupSort ys :=
  pairwise_lt_ext (dedupSort_pairwise xs) (dedupSort_pairwise ys) fun z => by
    rw [mem_dedupSort_iff, mem_dedupSort_iff, h]

/-- Executable strict-ascending checker for untrusted revocation witnesses. -/
def isStrictlySorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && isStrictlySorted (b :: rest)

theorem isStrictlySorted_sound : ∀ (l : List Nat),
    isStrictlySorted l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [isStrictlySorted, Bool.and_eq_true, decide_eq_true_eq] at h
    have hp := isStrictlySorted_sound (b :: rest) h.2
    obtain ⟨hb, hrest⟩ := List.pairwise_cons.1 hp
    refine List.pairwise_cons.2 ⟨fun z hz => ?_, hp⟩
    rcases List.mem_cons.1 hz with rfl | hz'
    · exact h.1
    · exact Nat.lt_trans h.1 (hb z hz')

/-- Canonical strictly sorted `RevocationSet` (`CAP-10` invariant enforced by construction). -/
structure RevocationSet where
  keys   : Array Nat
  sorted : keys.toList.Pairwise (· < ·)

namespace RevocationSet

def empty : RevocationSet := ⟨#[], List.Pairwise.nil⟩

def ofList (raw : List Nat) : RevocationSet :=
  ⟨(dedupSort raw).toArray, dedupSort_pairwise raw⟩

def insert (s : RevocationSet) (x : Nat) : RevocationSet :=
  ⟨(insertSorted x s.keys.toList).toArray, insertSorted_pairwise x _ s.sorted⟩

def contains (s : RevocationSet) (x : Nat) : Bool :=
  bsearch s.keys x

def root (s : RevocationSet) : List UInt8 :=
  cshake32 custRevRoot (encodeNats s.keys.toList)

theorem ext {s₁ s₂ : RevocationSet} (h : s₁.keys = s₂.keys) : s₁ = s₂ := by
  cases s₁; cases s₂; cases h; rfl

theorem sorted_getElem (s : RevocationSet) (i j : Nat) (hi : i < s.keys.size)
    (hj : j < s.keys.size) (hij : i < j) : s.keys[i] < s.keys[j] := by
  have h := List.pairwise_iff_getElem.1 s.sorted i j (by simpa using hi) (by simpa using hj) hij
  simpa using h

/-- **Binary search refines exact membership (`CAP-10` soundness & completeness).** -/
theorem contains_iff (s : RevocationSet) (x : Nat) : s.contains x = true ↔ x ∈ s.keys.toList := by
  constructor
  · exact bsearchAux_sound s.keys x _ 0 _ (Nat.le_refl _)
  · intro hx
    obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.1 hx
    have hi' : i < s.keys.size := by simpa using hi
    exact bsearchAux_complete s.keys x s.sorted_getElem _ 0 _ (Nat.le_refl _) (by omega) i hi'
      (Nat.zero_le _) hi' (by simpa using hxi)

/-- **`100%` completeness regardless of raw insertion order.** -/
theorem contains_ofList_iff (raw : List Nat) (x : Nat) :
    (ofList raw).contains x = true ↔ x ∈ raw := by
  rw [contains_iff]
  simpa [ofList] using mem_dedupSort_iff raw x

theorem ofList_order_independent {xs ys : List Nat} (h : ∀ z, z ∈ xs ↔ z ∈ ys) :
    ofList xs = ofList ys := by
  apply ext
  simp only [ofList]
  exact congrArg List.toArray (dedupSort_order_independent h)

theorem contains_insert (s : RevocationSet) (x y : Nat) :
    (s.insert x).contains y = true ↔ y = x ∨ s.contains y = true := by
  rw [contains_iff, contains_iff]
  exact mem_insertSorted x y s.keys.toList

theorem contains_insert_self (s : RevocationSet) (x : Nat) :
    (s.insert x).contains x = true :=
  (contains_insert s x x).2 (Or.inl rfl)

theorem root_binds {s₁ s₂ : RevocationSet} (h : s₁.root = s₂.root) :
    s₁ = s₂ ∨ CollisionAmong (cshake256Bytes custRevRoot)
      (fun z => z = encodeNats s₁.keys.toList ∨ z = encodeNats s₂.keys.toList) := by
  rcases cshake32_binds custRevRoot h with heq | hc
  · exact Or.inl (ext (Array.toList_inj.1 (encodeNats_injective heq)))
  · exact Or.inr hc

/-- Verify an untrusted revocation witness against `expectedRoot` ONLY if strictly sorted. -/
def fromVerifiedWitness (raw : List Nat) (expectedRoot : List UInt8) : Option RevocationSet :=
  if h : isStrictlySorted raw = true then
    let rs : RevocationSet := ⟨raw.toArray, isStrictlySorted_sound raw h⟩
    if rs.root == expectedRoot then some rs else none
  else none

end RevocationSet

/-! ## §4. Salted `cSHAKE256` Selective-Disclosure Attribute Merkle Tree & Hiding -/

/-- Domain-separated salted attribute leaf commitment (`256`-bit per-leaf salt). -/
def attrLeafCommit (idx : Nat) (key val salt : List UInt8) : List UInt8 :=
  cshake32 custAttrLeaf (0x00 :: leb128 idx ++ encodeField key ++ encodeField val ++ encodeField salt)

def attrEmptyLeaf : List UInt8 :=
  cshake32 custAttrLeaf [0x02]

/-- Domain-separated internal Merkle node (`0x01` tag). -/
def attrNodeHash (left right : List UInt8) : List UInt8 :=
  cshake32 custAttrNode (0x01 :: left ++ right)

theorem attrLeafCommit_binds {i₁ i₂ : Nat} {k₁ k₂ v₁ v₂ s₁ s₂ : List UInt8}
    (h : attrLeafCommit i₁ k₁ v₁ s₁ = attrLeafCommit i₂ k₂ v₂ s₂) :
    (i₁ = i₂ ∧ k₁ = k₂ ∧ v₁ = v₂ ∧ s₁ = s₂) ∨
      CollisionAmong (cshake256Bytes custAttrLeaf) (fun z =>
        z = (0x00 :: leb128 i₁ ++ encodeField k₁ ++ encodeField v₁ ++ encodeField s₁) ∨
        z = (0x00 :: leb128 i₂ ++ encodeField k₂ ++ encodeField v₂ ++ encodeField s₂)) := by
  rcases cshake32_binds custAttrLeaf h with hp | hc
  · have htail := (List.cons.inj hp).2
    simp only [List.append_assoc] at htail
    obtain ⟨hi, h1⟩ := leb128_prefix_inj i₁ i₂ _ _ htail
    obtain ⟨hk, h2⟩ := encodeField_prefix_inj h1
    obtain ⟨hv, h3⟩ := encodeField_prefix_inj h2
    obtain ⟨hs, _⟩ := encodeField_prefix_inj (a := s₁) (b := s₂) (r₁ := []) (r₂ := [])
      (by simpa using h3)
    exact Or.inl ⟨hi, hk, hv, hs⟩
  · exact Or.inr hc

/-- One bottom-up Merkle pairing layer. -/
def merklePairLayer : List (List UInt8) → List (List UInt8)
  | [] => []
  | [a] => [attrNodeHash a attrEmptyLeaf]
  | a :: b :: rest => attrNodeHash a b :: merklePairLayer rest

/-- Merkle root of height `h` over `leaves` (`2^h` leaves padded with `attrEmptyLeaf`). -/
def merkleRootAux : Nat → List (List UInt8) → List UInt8
  | 0, leaves => leaves.getD 0 attrEmptyLeaf
  | h + 1, leaves => merkleRootAux h (merklePairLayer leaves)

/-- Merkle authentication path `(isRightSibling, siblingDigest)` for leaf `idx`. -/
def merklePathAux : Nat → Nat → List (List UInt8) → List (Bool × List UInt8)
  | 0, _, _ => []
  | h + 1, idx, leaves =>
    let isRight := idx % 2 == 0
    let sibIdx := if isRight then idx + 1 else idx - 1
    let sib := leaves.getD sibIdx attrEmptyLeaf
    (isRight, sib) :: merklePathAux h (idx / 2) (merklePairLayer leaves)

/-- Fold a Merkle path upward from `leaf` to root. -/
def merkleFold (leaf : List UInt8) : List (Bool × List UInt8) → List UInt8
  | [] => leaf
  | (isRight, sib) :: rest =>
    let parent := if isRight then attrNodeHash leaf sib else attrNodeHash sib leaf
    merkleFold parent rest

def verifyMerkleOpening (root leaf : List UInt8) (path : List (Bool × List UInt8)) : Bool :=
  merkleFold leaf path == root

private theorem merklePairLayer_getD (leaves : List (List UInt8)) (k : Nat)
    (heven : leaves.length % 2 = 0) (hk : 2 * k + 1 < leaves.length) :
    (merklePairLayer leaves).getD k attrEmptyLeaf =
      attrNodeHash (leaves.getD (2 * k) attrEmptyLeaf) (leaves.getD (2 * k + 1) attrEmptyLeaf) := by
  induction leaves generalizing k with
  | nil => simp at hk
  | cons a tl ih =>
    cases tl with
    | nil => simp at heven
    | cons b rest =>
      cases k with
      | zero => simp [merklePairLayer]
      | succ k' =>
        simp only [List.length_cons] at heven hk
        simp only [merklePairLayer, List.getD_cons_succ]
        have h1 : 2 * (k' + 1) = (2 * k') + 2 := by omega
        have h2 : 2 * (k' + 1) + 1 = (2 * k' + 1) + 2 := by omega
        rw [h1, h2]
        simp only [List.getD_cons_succ]
        exact ih rest k' (by omega) (by omega)

private theorem merklePairLayer_length (leaves : List (List UInt8)) (heven : leaves.length % 2 = 0) :
    (merklePairLayer leaves).length = leaves.length / 2 := by
  induction leaves with
  | nil => rfl
  | cons a tl ih =>
    cases tl with
    | nil => simp at heven
    | cons b rest =>
      simp only [List.length_cons] at heven
      simp only [merklePairLayer, List.length_cons, ih rest (by omega)]
      omega

/-- **Merkle opening completeness:** every leaf `i < 2^h` opens validly against `merkleRootAux`. -/
theorem verifyMerkleOpening_complete : ∀ (h : Nat) (leaves : List (List UInt8)) (i : Nat),
    leaves.length = 2 ^ h → i < 2 ^ h →
    verifyMerkleOpening (merkleRootAux h leaves) (leaves.getD i attrEmptyLeaf)
      (merklePathAux h i leaves) = true
  | 0, leaves, i, _, hi => by
    have hi0 : i = 0 := by omega
    subst hi0
    simp [verifyMerkleOpening, merkleFold, merkleRootAux, merklePathAux]
  | h + 1, leaves, i, hlen, hi => by
    have hpow : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [Nat.pow_succ]; omega
    have heven : leaves.length % 2 = 0 := by rw [hlen, hpow]; omega
    have hpairLen : (merklePairLayer leaves).length = 2 ^ h := by
      rw [merklePairLayer_length leaves heven, hlen, hpow]; omega
    have hk : 2 * (i / 2) + 1 < leaves.length := by rw [hlen, hpow]; omega
    have hparent := merklePairLayer_getD leaves (i / 2) heven hk
    have ih := verifyMerkleOpening_complete h (merklePairLayer leaves) (i / 2) hpairLen (by omega)
    unfold verifyMerkleOpening at ih ⊢
    simp only [merklePathAux, merkleFold, merkleRootAux]
    by_cases hmod : i % 2 = 0
    · have h2k : 2 * (i / 2) = i := by omega
      have h2k1 : 2 * (i / 2) + 1 = i + 1 := by omega
      rw [h2k, h2k1] at hparent
      simpa [hmod, ← hparent] using ih
    · have h2k : 2 * (i / 2) = i - 1 := by omega
      have h2k1 : 2 * (i / 2) + 1 = i := by omega
      rw [h2k, h2k1] at hparent
      simpa [hmod, ← hparent] using ih

/-- **Merkle opening binding:** two openings with equal `32`-byte digests along identical
direction bits either agree on the leaf (and siblings) or yield a `cSHAKE256` node collision. -/
theorem merkleFold_binds :
    ∀ (p₁ p₂ : List (Bool × List UInt8)) (l₁ l₂ : List UInt8),
      l₁.length = 32 → l₂.length = 32 →
      (∀ x ∈ p₁, x.2.length = 32) → (∀ x ∈ p₂, x.2.length = 32) →
      p₁.map Prod.fst = p₂.map Prod.fst →
      merkleFold l₁ p₁ = merkleFold l₂ p₂ →
      (l₁ = l₂ ∧ p₁ = p₂) ∨ Collision (cshake256Bytes custAttrNode)
  | [], [], l₁, l₂, _, _, _, _, _, h => Or.inl ⟨h, rfl⟩
  | [], _ :: _, _, _, _, _, _, _, hdir, _ => by simp at hdir
  | _ :: _, [], _, _, _, _, _, _, hdir, _ => by simp at hdir
  | (b₁, s₁) :: r₁, (b₂, s₂) :: r₂, l₁, l₂, hl1, hl2, hp1, hp2, hdir, h => by
    simp only [List.map_cons, List.cons.injEq] at hdir
    obtain ⟨rfl, hdir'⟩ := hdir
    have hs1 : s₁.length = 32 := hp1 (b₁, s₁) (List.mem_cons_self ..)
    have hs2 : s₂.length = 32 := hp2 (b₁, s₂) (List.mem_cons_self ..)
    have hr1 : ∀ x ∈ r₁, x.2.length = 32 := fun x hx => hp1 x (List.mem_cons_of_mem _ hx)
    have hr2 : ∀ x ∈ r₂, x.2.length = 32 := fun x hx => hp2 x (List.mem_cons_of_mem _ hx)
    simp only [merkleFold] at h
    have hlenP1 : (if b₁ then attrNodeHash l₁ s₁ else attrNodeHash s₁ l₁).length = 32 := by
      cases b₁ <;> exact cshake32_length _ _
    have hlenP2 : (if b₁ then attrNodeHash l₂ s₂ else attrNodeHash s₂ l₂).length = 32 := by
      cases b₁ <;> exact cshake32_length _ _
    rcases merkleFold_binds r₁ r₂ _ _ hlenP1 hlenP2 hr1 hr2 hdir' h with ⟨hpar, hreq⟩ | hc
    · subst hreq
      cases b₁
      · simp only [Bool.false_eq_true, ↓reduceIte] at hpar
        rcases cshake32_binds custAttrNode hpar with heq | hc
        · obtain ⟨hseq, hleq⟩ := List.append_inj (List.cons.inj heq).2 (by rw [hs1, hs2])
          exact Or.inl ⟨hleq, by rw [hseq]⟩
        · exact Or.inr hc.global
      · simp only [↓reduceIte] at hpar
        rcases cshake32_binds custAttrNode hpar with heq | hc
        · obtain ⟨hleq, hseq⟩ := List.append_inj (List.cons.inj heq).2 (by rw [hl1, hl2])
          exact Or.inl ⟨hleq, by rw [hseq]⟩
        · exact Or.inr hc.global
    · exact Or.inr hc

/-- Selective disclosure opening for one attribute index `idx`. -/
structure SelectiveOpening where
  idx   : Nat
  key   : List UInt8
  value : List UInt8
  salt  : List UInt8
  path  : List (Bool × List UInt8)
  deriving DecidableEq, Repr

def verifySelectiveOpening (root : List UInt8) (op : SelectiveOpening) : Bool :=
  (op.salt.length == 32) &&
    verifyMerkleOpening root (attrLeafCommit op.idx op.key op.value op.salt) op.path

def verifySelectiveDisclosure (root : List UInt8) (openings : List SelectiveOpening) : Bool :=
  openings.all (verifySelectiveOpening root)

/-- **Unrevealed-Attribute View Independence:** Build a selective presentation for indices `S`
from `(attrs : List (List UInt8 × List UInt8 × List UInt8))` using height `h`. Any two attribute
tables that agree on disclosed indices `S` and have identical leaf digests on unrevealed indices
`j ∉ S` produce **byte-identical** `SelectiveOpening`s (zero raw `value_j` or `salt_j` leakage). -/
def buildSelectiveOpenings (h : Nat) (attrs : List (List UInt8 × List UInt8 × List UInt8))
    (disclosed : List Nat) : List SelectiveOpening :=
  let leaves := (List.range (2 ^ h)).map fun i =>
    match attrs[i]? with
    | some (k, v, s) => attrLeafCommit i k v s
    | none => attrEmptyLeaf
  disclosed.filterMap fun i =>
    match attrs[i]? with
    | some (k, v, s) => some ⟨i, k, v, s, merklePathAux h i leaves⟩
    | none => none

theorem unrevealed_attr_view_independent (h : Nat)
    (attrs₁ attrs₂ : List (List UInt8 × List UInt8 × List UInt8))
    (disclosed : List Nat)
    (hdis : ∀ i ∈ disclosed, attrs₁[i]? = attrs₂[i]?)
    (hcom : ∀ i, i < 2 ^ h →
      (match attrs₁[i]? with | some (k, v, s) => attrLeafCommit i k v s | none => attrEmptyLeaf) =
      (match attrs₂[i]? with | some (k, v, s) => attrLeafCommit i k v s | none => attrEmptyLeaf)) :
    buildSelectiveOpenings h attrs₁ disclosed = buildSelectiveOpenings h attrs₂ disclosed := by
  unfold buildSelectiveOpenings
  have hleaves :
      ((List.range (2 ^ h)).map fun i =>
        match attrs₁[i]? with | some (k, v, s) => attrLeafCommit i k v s | none => attrEmptyLeaf) =
      ((List.range (2 ^ h)).map fun i =>
        match attrs₂[i]? with | some (k, v, s) => attrLeafCommit i k v s | none => attrEmptyLeaf) := by
    apply List.map_congr_left
    intro i hi
    exact hcom i (List.mem_range.1 hi)
  rw [hleaves]
  apply List.filterMap_congr
  intro i hi
  rw [hdis i hi]

/-- **256-Bit Salt Offline Dictionary Guessing Bound (Exact Finite Counting):**
For any list `queries : List (List UInt8)` of offline salt guesses against an unrevealed
uniform `256`-bit salt `s ∈ [0, 2^256)`, the number of `s` values whose `32`-byte encoding
`be 32 s` matches any query in `queries` is bounded by `queries.length` (so advantage `≤ q / 2^256`). -/
def saltHitCount (space : Nat) (queries : List (List UInt8)) : Nat :=
  (List.range space).countP (fun s => queries.any (fun q => q == be 32 s))

private theorem countP_single_be32_le_one (q : List UInt8) :
    ∀ (n : Nat), n ≤ 256 ^ 32 → (List.range n).countP (fun s => q == be 32 s) ≤ 1 := by
  intro n hn
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
    by_cases hm : (q == be 32 m) = true
    · have hzero : (List.range m).countP (fun s => q == be 32 s) = 0 := by
        rw [List.countP_eq_zero]
        intro s hs
        have hsm : s < m := List.mem_range.1 hs
        intro hqs
        have heq1 : q = be 32 m := beq_iff_eq.1 hm
        have heq2 : q = be 32 s := beq_iff_eq.1 hqs
        have hbe : be 32 s = be 32 m := heq2.symm.trans heq1
        have hsm_eq := be_injective (by omega : s < 256 ^ 32) (by omega : m < 256 ^ 32) hbe
        omega
      simp [hm, hzero]
    · have hfm : (q == be 32 m) = false := Bool.eq_false_iff.2 hm
      simp only [hfm, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih (by omega)

private theorem countP_any_le_sum {α : Type} (l : List α) (ps : List (α → Bool)) :
    l.countP (fun x => ps.any (fun p => p x)) ≤ (ps.map fun p => l.countP p).sum := by
  induction ps with
  | nil => simp
  | cons p rest ih =>
    simp only [List.any_cons, List.map_cons, List.sum_cons]
    have hstep : ∀ (xs : List α),
        xs.countP (fun x => p x || rest.any (fun q => q x)) ≤
          xs.countP p + xs.countP (fun x => rest.any (fun q => q x)) := by
      intro xs
      induction xs with
      | nil => simp
      | cons a tl ixs =>
        simp only [List.countP_cons]
        cases p a <;> cases rest.any (fun q => q a) <;> simp <;> omega
    exact Nat.le_trans (hstep l) (Nat.add_le_add_left ih _)

theorem unrevealed_salt_offline_guess_bound (space : Nat) (hspace : space ≤ 2 ^ 256)
    (queries : List (List UInt8)) :
    saltHitCount space queries ≤ queries.length := by
  have hpow : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have hspace' : space ≤ 256 ^ 32 := hpow ▸ hspace
  unfold saltHitCount
  have h1 := countP_any_le_sum (List.range space) (queries.map fun q s => q == be 32 s)
  have hmap : (queries.map fun q s => q == be 32 s).any (fun p => p) =
      (fun x => queries.any (fun q => q == be 32 x)) := by
    funext x; simp [List.any_map]
  have h2 : (List.range space).countP (fun s => queries.any (fun q => q == be 32 s)) ≤
      ((queries.map fun q s => q == be 32 s).map fun p => (List.range space).countP p).sum := by
    simpa [List.any_map] using h1
  refine Nat.le_trans h2 ?_
  rw [List.map_map]
  have hsum : ∀ (qs : List (List UInt8)),
      (qs.map fun q => (List.range space).countP (fun s => q == be 32 s)).sum ≤ qs.length := by
    intro qs
    induction qs with
    | nil => simp
    | cons q tl ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hq := countP_single_be32_le_one q space hspace'
      omega
  exact hsum queries

/-! ## §5. `CAP-01` Root-Key Isolation, `CAP-12` Block-0 Authority Pin & `ZkBiscuit` Chain -/

/-- Issuer secret key: lives EXCLUSIVELY on the issuer (`CAP-01`), NEVER inside `HolderToken`. -/
structure IssuerSecret (S : PqSigScheme) where
  sk : S.SecKey

/-- Block 0: the SOLE issuer-signed authority anchor (`CAP-01` + `CAP-12`). -/
structure AuthorityBlock0 where
  subject        : List UInt8
  issuerPk       : List UInt8
  holderPk       : List UInt8
  rights         : UInt64
  expiresAt      : UInt64
  attrMerkleRoot : List UInt8
  nonce          : List UInt8
  deriving DecidableEq, Repr

/-- Holder-appended attenuation block `1..k`. Cannot mutate `subject` or widen `rights`/`expiresAt`. -/
structure AttenuationBlock where
  rights       : UInt64
  expiresAt    : UInt64
  nextHolderPk : List UInt8
  caveatTag    : List UInt8
  sigBytes     : List UInt8
  deriving DecidableEq, Repr

/-- Serialized holder token (`CAP-01`): structurally contains ZERO `IssuerSecret` values. -/
structure HolderToken where
  block0    : AuthorityBlock0
  block0Sig : List UInt8
  hops      : List AttenuationBlock
  deriving DecidableEq, Repr

def AuthorityBlock0.encode (b : AuthorityBlock0) : List UInt8 :=
  encodeField b.subject ++
    (encodeField b.issuerPk ++
      (encodeField b.holderPk ++
        (be 8 b.rights.toNat ++
          (be 8 b.expiresAt.toNat ++
            (encodeField b.attrMerkleRoot ++ encodeField b.nonce)))))

theorem AuthorityBlock0.encode_injective {a b : AuthorityBlock0}
    (h : a.encode = b.encode) : a = b := by
  cases a; cases b
  simp only [AuthorityBlock0.encode] at h
  obtain ⟨hs, h1⟩ := encodeField_prefix_inj h
  obtain ⟨hi, h2⟩ := encodeField_prefix_inj h1
  obtain ⟨hh, h3⟩ := encodeField_prefix_inj h2
  obtain ⟨hr, h4⟩ := List.append_inj h3 (by simp)
  obtain ⟨he, h5⟩ := List.append_inj h4 (by simp)
  obtain ⟨hm, h6⟩ := encodeField_prefix_inj h5
  obtain ⟨hn, _⟩ := encodeField_prefix_inj (r₁ := []) (r₂ := []) (by simpa using h6)
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hr' := UInt64.toNat_inj.1 (be_injective (h8 ▸ ‹UInt64›.toNat_lt) (h8 ▸ ‹UInt64›.toNat_lt) hr)
  have he' := UInt64.toNat_inj.1 (be_injective (h8 ▸ ‹UInt64›.toNat_lt) (h8 ▸ ‹UInt64›.toNat_lt) he)
  subst hs; subst hi; subst hh; subst hr'; subst he'; subst hm; subst hn; rfl

def AttenuationBlock.payloadEncode (b : AttenuationBlock) : List UInt8 :=
  be 8 b.rights.toNat ++
    (be 8 b.expiresAt.toNat ++ (encodeField b.nextHolderPk ++ encodeField b.caveatTag))

def block0SignMsg (b0 : AuthorityBlock0) : List UInt8 :=
  0x00 :: b0.encode

theorem block0SignMsg_injective {a b : AuthorityBlock0}
    (h : block0SignMsg a = block0SignMsg b) : a = b :=
  AuthorityBlock0.encode_injective (List.cons.inj h).2

def hopSignMsg (prevLineage : List UInt8) (h : AttenuationBlock) : List UInt8 :=
  0x01 :: (encodeField prevLineage ++ h.payloadEncode)

def rootLineage (b0 : AuthorityBlock0) : List UInt8 :=
  cshake32 custLineage (0x00 :: b0.encode)

def stepLineage (prev : List UInt8) (h : AttenuationBlock) : List UInt8 :=
  cshake32 custLineage (0x01 :: (encodeField prev ++ h.payloadEncode))

def lineageOf (b0 : AuthorityBlock0) (hops : List AttenuationBlock) : List UInt8 :=
  hops.foldl stepLineage (rootLineage b0)

/-- 256-bit `cSHAKE256` nullifier of prefix `0..j` (`j ≤ hops.length`). -/
def chainId (b0 : AuthorityBlock0) (hops : List AttenuationBlock) (j : Nat) : Nat :=
  ofBE (cshake32 custNullifier (0x01 :: lineageOf b0 (hops.take j)))

/-- Bitmask attenuation (`child ⊆ parent`). -/
def subMask (child parent : UInt64) : Bool :=
  (child &&& parent) == child

theorem subMask_refl (a : UInt64) : subMask a a = true := by
  simp [subMask]

theorem subMask_trans {a b c : UInt64} (hab : subMask a b = true) (hbc : subMask b c = true) :
    subMask a c = true := by
  simp only [subMask, beq_iff_eq] at hab hbc ⊢
  calc
    a &&& c = (a &&& b) &&& c := by rw [hab]
    _ = a &&& (b &&& c) := by
      apply UInt64.toBitVec_inj.1
      simp [BitVec.and_assoc]
    _ = a &&& b := by rw [hbc]
    _ = a := hab

/-- **`CAP-12` Block-0 Authority Pin:** extracts subject EXCLUSIVELY from block `0`. -/
def extractSubject (tok : HolderToken) : List UInt8 :=
  tok.block0.subject

/-- **`CAP-12` Block-0 Authority Pin:** extracts issuer-vouched root authority ONLY from block `0`. -/
structure IssuerAuthority where
  issuerPk       : List UInt8
  subject        : List UInt8
  rootRights     : UInt64
  rootExpiresAt  : UInt64
  attrMerkleRoot : List UInt8
  deriving DecidableEq, Repr

def extractIssuerAuthority (tok : HolderToken) : IssuerAuthority where
  issuerPk       := tok.block0.issuerPk
  subject        := tok.block0.subject
  rootRights     := tok.block0.rights
  rootExpiresAt  := tok.block0.expiresAt
  attrMerkleRoot := tok.block0.attrMerkleRoot

theorem extractSubject_invariant_under_hops (b0 : AuthorityBlock0) (sig : List UInt8)
    (h₁ h₂ : List AttenuationBlock) :
    extractSubject ⟨b0, sig, h₁⟩ = extractSubject ⟨b0, sig, h₂⟩ := rfl

theorem extractIssuerAuthority_invariant_under_hops (b0 : AuthorityBlock0) (sig : List UInt8)
    (h₁ h₂ : List AttenuationBlock) :
    extractIssuerAuthority ⟨b0, sig, h₁⟩ = extractIssuerAuthority ⟨b0, sig, h₂⟩ := rfl

/-- Issuer mints root token using `IssuerSecret S`; secret NEVER enters `HolderToken`. -/
def issueRootToken (S : PqSigScheme) (issuer : IssuerSecret S)
    (subject holderPk attrMerkleRoot nonce : List UInt8)
    (rights expiresAt : UInt64) : HolderToken :=
  let b0 : AuthorityBlock0 :=
    ⟨subject, S.pkOf issuer.sk, holderPk, rights, expiresAt, attrMerkleRoot, nonce⟩
  ⟨b0, S.sign issuer.sk (block0SignMsg b0), []⟩

/-- Holder attenuates a token using ONLY its own `holderSk` — ZERO `IssuerSecret` access! -/
def attenuateToken (S : PqSigScheme) (tok : HolderToken) (holderSk : S.SecKey)
    (newRights newExpiresAt : UInt64) (nextHolderPk caveatTag : List UInt8) : HolderToken :=
  let prevLin := lineageOf tok.block0 tok.hops
  let unsigned : AttenuationBlock := ⟨newRights, newExpiresAt, nextHolderPk, caveatTag, []⟩
  let sig := S.sign holderSk (hopSignMsg prevLin unsigned)
  { tok with hops := tok.hops ++ [{ unsigned with sigBytes := sig }] }

/-- Chain accumulator state threaded through `hops`. -/
structure ChainState where
  holderPk  : List UInt8
  lineage   : List UInt8
  rights    : UInt64
  expiresAt : UInt64
  deriving DecidableEq, Repr

def verifyHopStep (S : PqSigScheme) (rs : RevocationSet)
    (st : ChainState) (h : AttenuationBlock) : Option ChainState :=
  let nextLin := stepLineage st.lineage h
  let nul := ofBE (cshake32 custNullifier (0x01 :: nextLin))
  if subMask h.rights st.rights &&
     decide (h.expiresAt ≤ st.expiresAt) &&
     S.verify st.holderPk (hopSignMsg st.lineage h) h.sigBytes &&
     !rs.contains nul then
    some ⟨h.nextHolderPk, nextLin, h.rights, h.expiresAt⟩
  else none

/-- Verified effective authority output of `verifyToken`. -/
structure VerifiedAuthority where
  subject        : List UInt8
  rights         : UInt64
  expiresAt      : UInt64
  attrMerkleRoot : List UInt8
  tailLineage    : List UInt8
  tailHolderPk   : List UInt8
  deriving DecidableEq, Repr

def verifyToken (S : PqSigScheme) (issuerPk : List UInt8) (rs : RevocationSet)
    (now : UInt64) (tok : HolderToken) : Option VerifiedAuthority :=
  let rootLin := rootLineage tok.block0
  let rootNul := ofBE (cshake32 custNullifier (0x01 :: rootLin))
  if tok.block0.issuerPk == issuerPk &&
     S.verify issuerPk (block0SignMsg tok.block0) tok.block0Sig &&
     !rs.contains rootNul then
    let st0 : ChainState := ⟨tok.block0.holderPk, rootLin, tok.block0.rights, tok.block0.expiresAt⟩
    match tok.hops.foldlM (verifyHopStep S rs) st0 with
    | some st =>
      if decide (now ≤ st.expiresAt) then
        some ⟨tok.block0.subject, st.rights, st.expiresAt, tok.block0.attrMerkleRoot,
              st.lineage, st.holderPk⟩
      else none
    | none => none
  else none

/-- Verify token + selective attribute disclosure openings against `block0.attrMerkleRoot`. -/
def verifyPresentation (S : PqSigScheme) (issuerPk : List UInt8) (rs : RevocationSet)
    (now : UInt64) (tok : HolderToken) (openings : List SelectiveOpening) :
    Option VerifiedAuthority :=
  match verifyToken S issuerPk rs now tok with
  | some va => if verifySelectiveDisclosure va.attrMerkleRoot openings then some va else none
  | none => none

private theorem foldlM_cons_some {α β : Type} (f : α → β → Option α)
    (a : α) (b : β) (bs : List β) (r : α) :
    (b :: bs).foldlM f a = some r ↔ ∃ a1, f a b = some a1 ∧ bs.foldlM f a1 = some r := by
  simp only [List.foldlM_cons]
  cases f a b with
  | none => simp
  | some a1 => simp

private theorem foldlM_append_some {α β : Type} (f : α → β → Option α)
    (a : α) (xs ys : List β) (r : α) :
    (xs ++ ys).foldlM f a = some r ↔ ∃ a1, xs.foldlM f a = some a1 ∧ ys.foldlM f a1 = some r := by
  induction xs generalizing a with
  | nil => simp
  | cons x tl ih =>
    simp only [List.cons_append, foldlM_cons_some]
    constructor
    · rintro ⟨a1, h1, h2⟩
      obtain ⟨a2, h2a, h2b⟩ := (ih a1).1 h2
      exact ⟨a2, ⟨a1, h1, h2a⟩, h2b⟩
    · rintro ⟨a2, ⟨a1, h1, h2a⟩, h2b⟩
      exact ⟨a1, h1, (ih a1).2 ⟨a2, h2a, h2b⟩⟩

private theorem verifyHopStep_eq_some {S : PqSigScheme} {rs : RevocationSet}
    {st st' : ChainState} {h : AttenuationBlock}
    (hv : verifyHopStep S rs st h = some st') :
    subMask h.rights st.rights = true ∧
    h.expiresAt ≤ st.expiresAt ∧
    S.verify st.holderPk (hopSignMsg st.lineage h) h.sigBytes = true ∧
    rs.contains (ofBE (cshake32 custNullifier (0x01 :: stepLineage st.lineage h))) = false ∧
    st' = ⟨h.nextHolderPk, stepLineage st.lineage h, h.rights, h.expiresAt⟩ := by
  unfold verifyHopStep at hv
  split at hv
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, (Option.some.inj hv).symm⟩
  · cases hv

private theorem verifyHops_facts (S : PqSigScheme) (rs : RevocationSet) :
    ∀ (l : List AttenuationBlock) (st st' : ChainState),
      l.foldlM (verifyHopStep S rs) st = some st' →
        st'.lineage = l.foldl stepLineage st.lineage ∧
        subMask st'.rights st.rights = true ∧
        st'.expiresAt ≤ st.expiresAt ∧
        (rs.contains (ofBE (cshake32 custNullifier (0x01 :: st.lineage))) = false →
          ∀ j, j ≤ l.length →
            rs.contains (ofBE (cshake32 custNullifier (0x01 :: (l.take j).foldl stepLineage st.lineage))) = false)
  | [], st, st', hv => by
    cases Option.some.inj hv
    refine ⟨rfl, subMask_refl _, Nat.le_refl _, fun h0 j hj => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0; exact h0
  | h :: rest, st, st', hv => by
    obtain ⟨st1, h1, h2⟩ := (foldlM_cons_some _ _ _ _ _).1 hv
    obtain ⟨hr, he, _, hnul, hst1⟩ := verifyHopStep_eq_some h1
    obtain ⟨ihLin, ihR, ihE, ihNul⟩ := verifyHops_facts S rs rest st1 st' h2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ihLin, hst1]; rfl
    · rw [hst1] at ihR; exact subMask_trans ihR hr
    · rw [hst1] at ihE; exact Nat.le_trans ihE he
    · intro h0 j hj
      cases j with
      | zero => simpa using h0
      | succ j' =>
        simp only [List.length_cons] at hj
        simp only [List.take_succ_cons, List.foldl_cons]
        have hstep := ihNul (by rw [hst1]; exact hnul) j' (by omega)
        simpa [hst1] using hstep

/-! ### Key Security Theorems (`CAP-01`, `CAP-10`, `CAP-12`) -/

/-- **`CAP-01` (Root-Key Isolation — Holder Attenuation Needs Zero Issuer Secret):**
If `tok` verifies and `holderSk` owns `tok`'s tail `holderPk`, `attenuateToken` produces a valid
attenuated token with ZERO access to `IssuerSecret`. -/
theorem holder_attenuate_needs_no_issuer_secret (S : PqSigScheme)
    (issuerPk : List UInt8) (rs : RevocationSet) (now : UInt64)
    (tok : HolderToken) (va : VerifiedAuthority) (holderSk : S.SecKey)
    (newRights newExp : UInt64) (nextPk tag : List UInt8)
    (hv : verifyToken S issuerPk rs now tok = some va)
    (hown : S.pkOf holderSk = va.tailHolderPk)
    (hsub : subMask newRights va.rights = true)
    (hexp : newExp ≤ va.expiresAt)
    (hnow : now ≤ newExp)
    (hlive : rs.contains (ofBE (cshake32 custNullifier
      (0x01 :: stepLineage va.tailLineage ⟨newRights, newExp, nextPk, tag, []⟩))) = false) :
    ∃ va', verifyToken S issuerPk rs now
      (attenuateToken S tok holderSk newRights newExp nextPk tag) = some va' ∧
      va'.subject = tok.block0.subject ∧ va'.rights = newRights ∧ va'.expiresAt = newExp := by
  unfold verifyToken at hv
  split at hv
  · rename_i hroot
    cases hfold : tok.hops.foldlM (verifyHopStep S rs)
        ⟨tok.block0.holderPk, rootLineage tok.block0, tok.block0.rights, tok.block0.expiresAt⟩ with
    | none => simp [hfold] at hv
    | some st =>
      simp only [hfold] at hv
      split at hv
      · cases Option.some.inj hv
        have hlin := (verifyHops_facts S rs tok.hops _ _ hfold).1
        unfold attenuateToken verifyToken
        simp only [hroot, ↓reduceIte]
        rw [foldlM_append_some.2 ⟨st, hfold, ?_⟩]
        · simp only [decide_eq_true hnow, ↓reduceIte]
          exact ⟨_, rfl, rfl, rfl, rfl⟩
        · simp only [List.foldlM_cons, List.foldlM_nil]
          have hsig := S.verify_sign holderSk
            (hopSignMsg (lineageOf tok.block0 tok.hops) ⟨newRights, newExp, nextPk, tag, []⟩)
          have hstepEq : stepLineage st.lineage
              ⟨newRights, newExp, nextPk, tag,
                S.sign holderSk (hopSignMsg (lineageOf tok.block0 tok.hops)
                  ⟨newRights, newExp, nextPk, tag, []⟩)⟩ =
            stepLineage st.lineage ⟨newRights, newExp, nextPk, tag, []⟩ := rfl
          have hmsgEq : hopSignMsg st.lineage
              ⟨newRights, newExp, nextPk, tag,
                S.sign holderSk (hopSignMsg (lineageOf tok.block0 tok.hops)
                  ⟨newRights, newExp, nextPk, tag, []⟩)⟩ =
            hopSignMsg (lineageOf tok.block0 tok.hops) ⟨newRights, newExp, nextPk, tag, []⟩ := by
            simp only [hopSignMsg, AttenuationBlock.payloadEncode, lineageOf, hlin]
          unfold verifyHopStep
          rw [← hown, hmsgEq, hsig, hstepEq]
          simp [hsub, hexp, hlive]
      · simp at hv
  · simp at hv

/-- **`CAP-01` (Block-0 EUF-CMA Unforgeability Reduction):**
Any valid `HolderToken` whose `block0` was NOT in the issuer's log `issuedBlocks` directly
exhibits a forged PQ signature `(block0SignMsg tok.block0, tok.block0Sig)` on a fresh message. -/
theorem block0_unforgeable_reduction (S : PqSigScheme) (issuerPk : List UInt8)
    (rs : RevocationSet) (now : UInt64) (issuedBlocks : List AuthorityBlock0)
    (tok : HolderToken) (va : VerifiedAuthority)
    (hv : verifyToken S issuerPk rs now tok = some va)
    (hfresh : tok.block0 ∉ issuedBlocks) :
    S.verify issuerPk (block0SignMsg tok.block0) tok.block0Sig = true ∧
    block0SignMsg tok.block0 ∉ issuedBlocks.map block0SignMsg := by
  unfold verifyToken at hv
  split at hv
  · rename_i hroot
    simp only [Bool.and_eq_true] at hroot
    refine ⟨hroot.1.2, ?_⟩
    intro hmem
    obtain ⟨b, hb, heq⟩ := List.mem_map.1 hmem
    exact hfresh (block0SignMsg_injective heq ▸ hb)
  · simp at hv

/-- **`CAP-12` (Block-0 Authority Pin & Monotone Attenuation Across Every Prefix):**
Every verified token pins `subject` strictly to `block0.subject`, and its effective `rights`
and `expiresAt` are monotonically bounded by every prefix `pre` (including `pre = []`, block `0`). -/
theorem attenuation_monotone_from_block0 (S : PqSigScheme) (issuerPk : List UInt8)
    (rs : RevocationSet) (now : UInt64) (b0 : AuthorityBlock0) (sig0 : List UInt8)
    (pre ext : List AttenuationBlock) (va : VerifiedAuthority)
    (hv : verifyToken S issuerPk rs now ⟨b0, sig0, pre ++ ext⟩ = some va) :
    ∃ vaPre, verifyToken S issuerPk rs now ⟨b0, sig0, pre⟩ = some vaPre ∧
      va.subject = b0.subject ∧
      subMask va.rights vaPre.rights = true ∧
      va.expiresAt ≤ vaPre.expiresAt ∧
      subMask va.rights b0.rights = true ∧
      va.expiresAt ≤ b0.expiresAt := by
  unfold verifyToken at hv ⊢
  split at hv
  · rename_i hroot
    simp only [hroot, ↓reduceIte]
    cases hfold : (pre ++ ext).foldlM (verifyHopStep S rs)
        ⟨b0.holderPk, rootLineage b0, b0.rights, b0.expiresAt⟩ with
    | none => simp [hfold] at hv
    | some st =>
      simp only [hfold] at hv
      split at hv
      · rename_i hnow
        cases Option.some.inj hv
        simp only [decide_eq_true_eq] at hnow
        obtain ⟨stPre, hpre, hext⟩ := (foldlM_append_some _ _ _ _ _).1 hfold
        obtain ⟨_, hsubPre, hexpPre, _⟩ := verifyHops_facts S rs pre _ _ hpre
        obtain ⟨_, hsubExt, hexpExt, _⟩ := verifyHops_facts S rs ext _ _ hext
        have hnowPre : now ≤ stPre.expiresAt := Nat.le_trans hnow hexpExt
        rw [hpre]
        simp only [decide_eq_true hnowPre, ↓reduceIte]
        exact ⟨_, rfl, rfl, hsubExt, hexpExt, subMask_trans hsubExt hsubPre, Nat.le_trans hexpExt hexpPre⟩
      · simp at hv
  · simp at hv

/-- **`CAP-10` (Complete Order-Independent Ancestor-Cone Revocation):**
Given ANY raw revocation list `raw` in ANY insertion order, if ANY ancestor prefix `j ≤ hops.length`
has `chainId b0 hops j ∈ raw`, `verifyToken` under `RevocationSet.ofList raw` returns `none`. -/
theorem revoke_ancestor_kills_cone (S : PqSigScheme) (issuerPk : List UInt8)
    (raw : List Nat) (now : UInt64) (tok : HolderToken)
    (j : Nat) (hj : j ≤ tok.hops.length)
    (hrev : chainId tok.block0 tok.hops j ∈ raw) :
    verifyToken S issuerPk (RevocationSet.ofList raw) now tok = none := by
  cases hv : verifyToken S issuerPk (RevocationSet.ofList raw) now tok with
  | none => rfl
  | some va =>
    exfalso
    unfold verifyToken at hv
    split at hv
    · rename_i hroot
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hroot
      cases hfold : tok.hops.foldlM (verifyHopStep S (RevocationSet.ofList raw))
          ⟨tok.block0.holderPk, rootLineage tok.block0, tok.block0.rights, tok.block0.expiresAt⟩ with
      | none => simp [hfold] at hv
      | some st =>
        have hfalse := (verifyHops_facts S (RevocationSet.ofList raw) tok.hops _ _ hfold).2.2.2 hroot.2 j hj
        have htrue : (RevocationSet.ofList raw).contains (chainId tok.block0 tok.hops j) = true :=
          (RevocationSet.contains_ofList_iff raw _).2 hrev
        unfold chainId lineageOf at htrue
        rw [hfalse] at htrue
        cases htrue
    · simp at hv

/-! ## §6. Constructive Security-Bug `#tooth` Falsifiers (`CAP-01`, `CAP-10`, `CAP-12`) -/

/-- Minimal deterministic test scheme for kernel-reducible (`by decide`) falsifier teeth. -/
private def toyPqScheme : PqSigScheme where
  SecKey := List UInt8
  pkOf   := fun sk => 0x50 :: sk
  sign   := fun sk msg => 0x53 :: (encodeField sk ++ msg)
  verify := fun pk msg sig =>
    match pk with
    | 0x50 :: sk => sig == (0x53 :: (encodeField sk ++ msg))
    | _ => false
  verify_sign := fun _ _ => by simp

/-- Legacy `webauth-core` `CAP-12` anti-pattern: scanning holder-appended blocks for `acct=`. -/
def legacyFirstAcctScan (tok : HolderToken) : Option (List UInt8) :=
  if !tok.block0.subject.isEmpty then some tok.block0.subject
  else tok.hops.findSome? fun h =>
    if h.caveatTag.take 5 == strBytes "acct=" then some (h.caveatTag.drop 5) else none

def toothIssuer : IssuerSecret toyPqScheme := ⟨strBytes "issuer-secret-key"⟩
def toothHolderSk : List UInt8 := strBytes "alice-holder-key"
def toothEmptyRoot : List UInt8 := List.replicate 32 0xAA
def toothNonce : List UInt8 := List.replicate 32 0xBB

/-- **`CAP-01` `#tooth`:** Tampering with `block0.subject` or `block0.rights` without
`IssuerSecret` fails `verifyToken`, and `HolderToken` holds no `IssuerSecret` witness. -/
theorem cap01_tooth_forged_block0_rejected :
    let tok := issueRootToken toyPqScheme toothIssuer (strBytes "alice")
      (toyPqScheme.pkOf toothHolderSk) toothEmptyRoot toothNonce 0x03 1000
    let forgedSubj : HolderToken := { tok with block0 := { tok.block0 with subject := strBytes "admin" } }
    let forgedRights : HolderToken := { tok with block0 := { tok.block0 with rights := 0xFF } }
    (verifyToken toyPqScheme (toyPqScheme.pkOf toothIssuer.sk) RevocationSet.empty 500 tok).isSome = true ∧
    verifyToken toyPqScheme (toyPqScheme.pkOf toothIssuer.sk) RevocationSet.empty 500 forgedSubj = none ∧
    verifyToken toyPqScheme (toyPqScheme.pkOf toothIssuer.sk) RevocationSet.empty 500 forgedRights = none := by
  decide

/-- **`CAP-10` `#tooth`:** Unsorted witness `[30, 10, 20]` misses `30` under naive `bsearch`
(reproducing `breadstuffs/credentials/src/revocation.rs:238`), while `RevocationSet.ofList`
catches `30`, rejects unsorted witnesses, and canonicalizes identically to `[10, 20, 30]`. -/
theorem cap10_tooth_unsorted_bsearch_miss_killed :
    bsearch #[30, 10, 20] 30 = false ∧
    isStrictlySorted [30, 10, 20] = false ∧
    (RevocationSet.ofList [30, 10, 20]).contains 30 = true ∧
    (RevocationSet.ofList [30, 10, 20]).keys = (RevocationSet.ofList [10, 20, 30]).keys := by
  decide

/-- **`CAP-12` `#tooth`:** Appending a holder block with `caveatTag = "acct=admin"` fools
`legacyFirstAcctScan` on an empty-subject legacy token, NEVER changes `extractSubject` on a
valid token, and attempting to escalate `rights` (`0x03 → 0x07`) or `expiresAt` (`1000 → 2000`)
in block 1 causes `verifyToken` to return `none`. -/
theorem cap12_tooth_holder_appended_acct_admin_killed :
    let ipk := toyPqScheme.pkOf toothIssuer.sk
    let hpk := toyPqScheme.pkOf toothHolderSk
    let tok := issueRootToken toyPqScheme toothIssuer (strBytes "alice") hpk toothEmptyRoot toothNonce 0x03 1000
    let spoofHop : AttenuationBlock := ⟨0x01, 900, hpk, strBytes "acct=admin", []⟩
    let legTok : HolderToken := ⟨{ tok.block0 with subject := [] }, tok.block0Sig, [spoofHop]⟩
    let escRights : HolderToken :=
      { tok with hops := [⟨0x07, 900, hpk, strBytes "acct=admin",
          toyPqScheme.sign toothHolderSk (hopSignMsg (rootLineage tok.block0)
            ⟨0x07, 900, hpk, strBytes "acct=admin", []⟩)⟩] }
    let escExp : HolderToken :=
      { tok with hops := [⟨0x01, 2000, hpk, strBytes "acct=admin",
          toyPqScheme.sign toothHolderSk (hopSignMsg (rootLineage tok.block0)
            ⟨0x01, 2000, hpk, strBytes "acct=admin", []⟩)⟩] }
    legacyFirstAcctScan legTok = some (strBytes "admin") ∧
    extractSubject { tok with hops := [spoofHop] } = strBytes "alice" ∧
    verifyToken toyPqScheme ipk RevocationSet.empty 500 escRights = none ∧
    verifyToken toyPqScheme ipk RevocationSet.empty 500 escExp = none := by
  decide

/-! ## §7. Lean-Authored Conformance Vector Emitter (`wotsCshake256` + `cSHAKE256` Merkle) -/

private def hexByte (b : UInt8) : String :=
  let digits := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  String.ofList [digits[(b.toNat / 16) % 16]!, digits[b.toNat % 16]!]

private def hexBytes (bs : List UInt8) : String :=
  String.join (bs.map hexByte)

private def jsonBool (b : Bool) : String := if b then "true" else "false"

def emitPqBiscuitConformance (path : System.FilePath) : IO Unit := do
  let issuerSeed := strBytes "MINIDREGG-D8-ISSUER-SEED-32BYTES"
  let holder0Seed := strBytes "MINIDREGG-D8-HOLDER0-SEED-32BYTE"
  let holder1Seed := strBytes "MINIDREGG-D8-HOLDER1-SEED-32BYTE"
  let holder2Seed := strBytes "MINIDREGG-D8-HOLDER2-SEED-32BYTE"
  let issuer : IssuerSecret wotsCshake256 := ⟨issuerSeed⟩
  let issuerPk := wotsCshake256.pkOf issuerSeed
  let holder0Pk := wotsCshake256.pkOf holder0Seed
  let holder1Pk := wotsCshake256.pkOf holder1Seed
  let holder2Pk := wotsCshake256.pkOf holder2Seed
  let salt0 := cshake32 (strBytes "MINIDREGG.D8.TEST_SALT") [0]
  let salt1 := cshake32 (strBytes "MINIDREGG.D8.TEST_SALT") [1]
  let salt2 := cshake32 (strBytes "MINIDREGG.D8.TEST_SALT") [2]
  let salt3 := cshake32 (strBytes "MINIDREGG.D8.TEST_SALT") [3]
  let attrs : List (List UInt8 × List UInt8 × List UInt8) := [
    (strBytes "acct",      strBytes "alice",      salt0),
    (strBytes "role",      strBytes "researcher", salt1),
    (strBytes "clearance", strBytes "L3",         salt2),
    (strBytes "region",    strBytes "us-west",    salt3)
  ]
  let leaves := (List.range 4).map fun i =>
    match attrs[i]? with
    | some (k, v, s) => attrLeafCommit i k v s
    | none => attrEmptyLeaf
  let attrRoot := merkleRootAux 2 leaves
  let nonce := cshake32 (strBytes "MINIDREGG.D8.TEST_NONCE") [42]
  let tok0 := issueRootToken wotsCshake256 issuer (strBytes "alice") holder0Pk attrRoot nonce 0x0F 2000
  let tok1 := attenuateToken wotsCshake256 tok0 holder0Seed 0x07 1500 holder1Pk (strBytes "acct=admin")
  let tok2 := attenuateToken wotsCshake256 tok1 holder1Seed 0x03 1200 holder2Pk (strBytes "scope=read_doc")
  let openings := buildSelectiveOpenings 2 attrs [1, 3]
  let okPres := (verifyPresentation wotsCshake256 issuerPk RevocationSet.empty 1000 tok2 openings).isSome
  let cid0 := chainId tok2.block0 tok2.hops 0
  let cid1 := chainId tok2.block0 tok2.hops 1
  let cid2 := chainId tok2.block0 tok2.hops 2
  let rsUnsorted := RevocationSet.ofList [cid2, cid0, cid1]
  let rsSorted := RevocationSet.ofList [cid0, cid1, cid2]
  let revRootEq := rsUnsorted.root == rsSorted.root
  let revAncKilled := (verifyToken wotsCshake256 issuerPk (RevocationSet.ofList [cid1]) 1000 tok2).isNone
  let json :=
    "{\n" ++
    "  \"schema\": \"minidregg.pq_biscuit_conformance.v1\",\n" ++
    s!"  \"issuer_seed_hex\": \"{hexBytes issuerSeed}\",\n" ++
    s!"  \"holder0_seed_hex\": \"{hexBytes holder0Seed}\",\n" ++
    s!"  \"holder1_seed_hex\": \"{hexBytes holder1Seed}\",\n" ++
    s!"  \"holder2_seed_hex\": \"{hexBytes holder2Seed}\",\n" ++
    s!"  \"issuer_pk_hex\": \"{hexBytes issuerPk}\",\n" ++
    s!"  \"holder0_pk_hex\": \"{hexBytes holder0Pk}\",\n" ++
    s!"  \"holder1_pk_hex\": \"{hexBytes holder1Pk}\",\n" ++
    s!"  \"holder2_pk_hex\": \"{hexBytes holder2Pk}\",\n" ++
    s!"  \"nonce_hex\": \"{hexBytes nonce}\",\n" ++
    s!"  \"salts_hex\": [\"{hexBytes salt0}\", \"{hexBytes salt1}\", \"{hexBytes salt2}\", \"{hexBytes salt3}\"],\n" ++
    s!"  \"attr_merkle_root_hex\": \"{hexBytes attrRoot}\",\n" ++
    s!"  \"block0_sig_hex\": \"{hexBytes tok2.block0Sig}\",\n" ++
    s!"  \"hop1_sig_hex\": \"{hexBytes (tok2.hops.getD 0 ⟨0, 0, [], [], []⟩).sigBytes}\",\n" ++
    s!"  \"hop2_sig_hex\": \"{hexBytes (tok2.hops.getD 1 ⟨0, 0, [], [], []⟩).sigBytes}\",\n" ++
    s!"  \"root_lineage_hex\": \"{hexBytes (rootLineage tok2.block0)}\",\n" ++
    s!"  \"hop1_lineage_hex\": \"{hexBytes (lineageOf tok2.block0 (tok2.hops.take 1))}\",\n" ++
    s!"  \"tail_lineage_hex\": \"{hexBytes (lineageOf tok2.block0 tok2.hops)}\",\n" ++
    s!"  \"chain_id0_hex\": \"{hexBytes (be 32 cid0)}\",\n" ++
    s!"  \"chain_id1_hex\": \"{hexBytes (be 32 cid1)}\",\n" ++
    s!"  \"chain_id2_hex\": \"{hexBytes (be 32 cid2)}\",\n" ++
    s!"  \"revocation_root_hex\": \"{hexBytes rsUnsorted.root}\",\n" ++
    s!"  \"presentation_valid\": {jsonBool okPres},\n" ++
    s!"  \"revocation_root_order_independent\": {jsonBool revRootEq},\n" ++
    s!"  \"ancestor_revocation_kills_descendant\": {jsonBool revAncKilled},\n" ++
    s!"  \"extracted_subject\": \"alice\",\n" ++
    s!"  \"disclosed_indices\": [1, 3]\n" ++
    "}\n"
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path json

#eval emitPqBiscuitConformance "prover/testdata/pq_biscuit_conformance.json"

/-! ## §8. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.wotsVerify_sign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wotsVerify_sign

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.RevocationSet.contains_ofList_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RevocationSet.contains_ofList_iff

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.RevocationSet.ofList_order_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RevocationSet.ofList_order_independent

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.RevocationSet.root_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RevocationSet.root_binds

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.attrLeafCommit_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attrLeafCommit_binds

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.verifyMerkleOpening_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyMerkleOpening_complete

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.merkleFold_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merkleFold_binds

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.unrevealed_attr_view_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unrevealed_attr_view_independent

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.unrevealed_salt_offline_guess_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unrevealed_salt_offline_guess_bound

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.holder_attenuate_needs_no_issuer_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms holder_attenuate_needs_no_issuer_secret

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.block0_unforgeable_reduction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms block0_unforgeable_reduction

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.attenuation_monotone_from_block0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attenuation_monotone_from_block0

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.revoke_ancestor_kills_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoke_ancestor_kills_cone

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.cap01_tooth_forged_block0_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cap01_tooth_forged_block0_rejected

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.cap10_tooth_unsorted_bsearch_miss_killed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cap10_tooth_unsorted_bsearch_miss_killed

/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.cap12_tooth_holder_appended_acct_admin_killed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cap12_tooth_holder_appended_acct_admin_killed

end Minidregg.Theory.PqSelectiveBiscuit
