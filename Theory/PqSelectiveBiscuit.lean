/-
# `Theory/PqSelectiveBiscuit.lean` — Post-Quantum Issuer-Root-Isolated `ZkBiscuit` Selective-Disclosure Credentials
Closes Decision `D8` and Security Bugs `CAP-01`, `CAP-10`, `CAP-12` (and `CAP-13`):
100% post-quantum (`cSHAKE256` SP 800-185 + abstract PQ signature interface `PqSigScheme`,
instantiated by pure-hash `cSHAKE256` WOTS+ and compatible with `dregg-pq` Hybrid Ed25519+ML-DSA-65;
zero elliptic-curve pairings or Pedersen commitments).
Import boundary: `Theory/` tier (`Theory.HashBytes`, `Theory.Sp800185Cshake256Core` only).
-/
import Theory.HashBytes
import Theory.Sp800185Cshake256Core

namespace Minidregg.Theory.PqSelectiveBiscuit
open Minidregg.Theory.HashBytes
open Minidregg.Compiler.Sp800185Cshake256
set_option autoImplicit false

/-! ## §1. Prefix-Free Encoding & Domain-Separated `cSHAKE256` -/
def leb128 (n : Nat) : List UInt8 :=
  if h : n < 128 then [UInt8.ofNat n] else UInt8.ofNat (128 + n % 128) :: leb128 (n / 128)
termination_by n
decreasing_by omega
theorem leb128_prefix_inj : ∀ (a b : Nat) (r₁ r₂ : List UInt8),
    leb128 a ++ r₁ = leb128 b ++ r₂ → a = b ∧ r₁ = r₂ := by
  intro a; induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b r₁ r₂ h; unfold leb128 at h
    split at h <;> split at h <;>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h <;>
      have hnat := congrArg UInt8.toNat h.1 <;> simp only [UInt8.toNat_ofNat'] at hnat
    · exact ⟨by omega, h.2⟩
    · omega
    · omega
    · obtain ⟨hq, hr⟩ := ih (a / 128) (by omega) (b / 128) r₁ r₂ h.2; exact ⟨by omega, hr⟩
def encodeField (bs : List UInt8) : List UInt8 := leb128 bs.length ++ bs
theorem encodeField_prefix_inj {a b r₁ r₂ : List UInt8}
    (h : encodeField a ++ r₁ = encodeField b ++ r₂) : a = b ∧ r₁ = r₂ := by
  unfold encodeField at h; rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨hlen, hrest⟩ := leb128_prefix_inj a.length b.length (a ++ r₁) (b ++ r₂) h
  exact List.append_inj hrest hlen
def encodeNats (ns : List Nat) : List UInt8 := leb128 ns.length ++ ns.flatMap leb128
private theorem flatMap_leb128_inj : ∀ (xs ys : List Nat),
    xs.length = ys.length → xs.flatMap leb128 = ys.flatMap leb128 → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, h => by
    simp only [List.flatMap_cons] at h; obtain ⟨hxy, hrest⟩ := leb128_prefix_inj x y _ _ h
    simp only [List.length_cons, Nat.succ.injEq] at hlen; rw [hxy, flatMap_leb128_inj xs ys hlen hrest]
theorem encodeNats_injective {xs ys : List Nat} (h : encodeNats xs = encodeNats ys) : xs = ys := by
  obtain ⟨hlen, hbody⟩ := leb128_prefix_inj xs.length ys.length _ _ h; exact flatMap_leb128_inj xs ys hlen hbody
def cshake32 (cust input : List UInt8) : List UInt8 := cshake256Bytes cust input
@[simp] theorem cshake32_length (cust input : List UInt8) : (cshake32 cust input).length = 32 :=
  cshake256Bytes_length cust input
theorem cshake32_binds (cust : List UInt8) {x y : List UInt8} (h : cshake32 cust x = cshake32 cust y) :
    x = y ∨ CollisionAmong (cshake256Bytes cust) (fun z => z = x ∨ z = y) := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · exact Or.inr ⟨x, y, Or.inl rfl, Or.inr rfl, hxy, congrArg ofBE h⟩
def strBytes (s : String) : List UInt8 := s.toList.map fun c => UInt8.ofNat c.toNat
def custAttrLeaf  : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.ATTR_LEAF/v1"
def custAttrNode  : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.ATTR_NODE/v1"
def custLineage   : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.LINEAGE/v1"
def custNullifier : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.NULLIFIER/v1"
def custRevRoot   : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.REV_ROOT/v1"
def custBlockSig  : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.BLOCK_SIG/v1"
def custWotsChain : List UInt8 := strBytes "MINIDREGG.PQ_BISCUIT.WOTS_CHAIN/v1"

/-! ## §2. Post-Quantum Signature Interface (`PqSigScheme`) & Pure-Hash `cSHAKE256` WOTS+ -/
structure PqSigScheme where
  SecKey      : Type
  pkOf        : SecKey → List UInt8
  sign        : SecKey → List UInt8 → List UInt8
  verify      : List UInt8 → List UInt8 → List UInt8 → Bool
  verify_sign : ∀ sk msg, verify (pkOf sk) msg (sign sk msg) = true
def wotsChainStep (idx step : Nat) (val : List UInt8) : List UInt8 :=
  cshake32 custWotsChain (0x01 :: be 4 idx ++ be 4 step ++ val)
def wotsChainIter (idx : Nat) : Nat → Nat → List UInt8 → List UInt8
  | _, 0, val => val
  | start, steps + 1, val => wotsChainIter idx (start + 1) steps (wotsChainStep idx start val)
theorem wotsChainIter_add (idx start a b : Nat) (val : List UInt8) :
    wotsChainIter idx (start + a) b (wotsChainIter idx start a val) = wotsChainIter idx start (a + b) val := by
  induction a generalizing start val with
  | zero => simp [wotsChainIter]
  | succ a ih =>
    simp only [wotsChainIter, Nat.succ_add]; rw [show start + (a + 1) = (start + 1) + a by omega]
    exact ih (start + 1) (wotsChainStep idx start val)
def wotsSkElem (seed : List UInt8) (idx : Nat) : List UInt8 :=
  cshake32 custWotsChain (0x00 :: be 4 idx ++ seed)
def wotsDigits (msg : List UInt8) : List Nat :=
  let msgNibbles := (cshake32 custBlockSig msg).flatMap fun b => [b.toNat / 16, b.toNat % 16]
  let csum := msgNibbles.foldl (fun acc d => acc + (15 - d)) 0
  msgNibbles ++ [(csum / 256) % 16, (csum / 16) % 16, csum % 16]
theorem wotsDigits_length (msg : List UInt8) : (wotsDigits msg).length = 67 := by
  unfold wotsDigits
  have hflat : ∀ (bs : List UInt8), (bs.flatMap fun b => [b.toNat / 16, b.toNat % 16]).length = 2 * bs.length := by
    intro bs; induction bs with | nil => rfl | cons _ _ ih => simp [List.flatMap_cons, ih]; omega
  simp [hflat, cshake32_length]
theorem wotsDigits_le_15 (msg : List UInt8) : ∀ d ∈ wotsDigits msg, d ≤ 15 := by
  unfold wotsDigits; intro d hd
  simp only [List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with ⟨b, _, h | h⟩ | h | h | h
  · have := b.toNat_lt; omega
  · omega
  · omega
  · omega
  · omega
def wotsPk (seed : List UInt8) : List UInt8 :=
  cshake32 custWotsChain (0x02 :: (List.range 67).flatMap fun idx => wotsChainIter idx 0 15 (wotsSkElem seed idx))
def wotsSignAux : Nat → List UInt8 → List Nat → List UInt8
  | _, _, [] => []
  | idx, seed, d :: ds => wotsChainIter idx 0 d (wotsSkElem seed idx) ++ wotsSignAux (idx + 1) seed ds
def wotsSign (seed msg : List UInt8) : List UInt8 := wotsSignAux 0 seed (wotsDigits msg)
def wotsRecoverTips : Nat → List Nat → List UInt8 → List UInt8
  | _, [], _ => []
  | idx, d :: ds, sig => wotsChainIter idx d (15 - d) (sig.take 32) ++ wotsRecoverTips (idx + 1) ds (sig.drop 32)
def wotsVerify (pk msg sig : List UInt8) : Bool :=
  if sig.length != 67 * 32 then false
  else cshake32 custWotsChain (0x02 :: wotsRecoverTips 0 (wotsDigits msg) sig) == pk
private theorem wotsChainIter_length (idx start steps : Nat) (val : List UInt8) (h : val.length = 32) :
    (wotsChainIter idx start steps val).length = 32 := by
  induction steps generalizing start val with | zero => exact h | succ _ ih => exact ih _ _ (cshake32_length _ _)
private theorem wotsSignAux_length (idx : Nat) (seed : List UInt8) (ds : List Nat) :
    (wotsSignAux idx seed ds).length = ds.length * 32 := by
  induction ds generalizing idx with
  | nil => rfl
  | cons d _ ih =>
    have hc := wotsChainIter_length idx 0 d (wotsSkElem seed idx) (cshake32_length _ _)
    simp only [wotsSignAux, List.length_append, List.length_cons, ih, hc]; omega
private theorem list_flatMap_ext {α β : Type} (l : List α) {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with | nil => rfl | cons x _ ih =>
    simp only [List.flatMap_cons, h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
private theorem wotsRecoverTips_signAux (idx : Nat) (seed : List UInt8) (ds : List Nat) (hds : ∀ d ∈ ds, d ≤ 15) :
    wotsRecoverTips idx ds (wotsSignAux idx seed ds) =
      (List.range ds.length).flatMap fun k => wotsChainIter (idx + k) 0 15 (wotsSkElem seed (idx + k)) := by
  induction ds generalizing idx with
  | nil => rfl
  | cons d tl ih =>
    have hd : d ≤ 15 := hds d List.mem_cons_self
    have hc := wotsChainIter_length idx 0 d (wotsSkElem seed idx) (cshake32_length _ _)
    simp only [wotsSignAux, wotsRecoverTips, List.take_left' hc, List.drop_left' hc]
    have hcomb := wotsChainIter_add idx 0 d (15 - d) (wotsSkElem seed idx)
    have hadd : d + (15 - d) = 15 := by omega
    simp only [Nat.zero_add, hadd] at hcomb
    rw [hcomb, ih (idx + 1) (fun x hx => hds x (List.mem_cons_of_mem _ hx)),
      List.length_cons, List.range_succ_eq_map, List.flatMap_cons, Nat.add_zero, List.flatMap_map]
    apply congrArg (wotsChainIter idx 0 15 (wotsSkElem seed idx) ++ ·)
    exact list_flatMap_ext _ fun k _ => by simp only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 k]
theorem wotsVerify_sign (seed msg : List UInt8) : wotsVerify (wotsPk seed) msg (wotsSign seed msg) = true := by
  unfold wotsVerify wotsSign wotsPk
  have hlen : (wotsSignAux 0 seed (wotsDigits msg)).length = 67 * 32 := by rw [wotsSignAux_length, wotsDigits_length]
  simp only [hlen, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
  rw [wotsRecoverTips_signAux 0 seed (wotsDigits msg) (wotsDigits_le_15 msg), wotsDigits_length]
  simp only [Nat.zero_add]
def wotsCshake256 : PqSigScheme := ⟨List UInt8, wotsPk, wotsSign, wotsVerify, wotsVerify_sign⟩

/-! ## §3. `CAP-10` Canonical Sorted `RevocationSet` & Complete Binary Search -/
def bsearchAux (keys : Array Nat) (x : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := lo + (hi - lo) / 2; let v := keys.getD mid 0
      if v = x then true else if v < x then bsearchAux keys x fuel (mid + 1) hi else bsearchAux keys x fuel lo mid
    else false
def bsearch (keys : Array Nat) (x : Nat) : Bool := bsearchAux keys x keys.size 0 keys.size
theorem bsearchAux_sound (keys : Array Nat) (x : Nat) : ∀ (fuel lo hi : Nat), hi ≤ keys.size →
    bsearchAux keys x fuel lo hi = true → x ∈ keys.toList
  | 0, _, _, _, h => by simp [bsearchAux] at h
  | fuel + 1, lo, hi, hsz, h => by
    by_cases hlt : lo < hi
    · have hmid : lo + (hi - lo) / 2 < keys.size := by omega
      have hget : keys.getD (lo + (hi - lo) / 2) 0 = keys[lo + (hi - lo) / 2] := by simp [Array.getD, hmid]
      simp only [bsearchAux, hlt, ↓reduceIte, hget] at h
      by_cases h1 : keys[lo + (hi - lo) / 2] = x
      · rw [← h1]; exact Array.getElem_mem_toList hmid
      · simp only [h1, ↓reduceIte] at h
        by_cases h2 : keys[lo + (hi - lo) / 2] < x <;> simp only [h2, ↓reduceIte] at h
        · exact bsearchAux_sound keys x fuel _ hi hsz h
        · exact bsearchAux_sound keys x fuel lo _ (by omega) h
    · simp [bsearchAux, hlt] at h
theorem bsearchAux_complete (keys : Array Nat) (x : Nat)
    (hs : ∀ (i j : Nat) (hi : i < keys.size) (hj : j < keys.size), i < j → keys[i] < keys[j]) :
    ∀ (fuel lo hi : Nat), hi ≤ keys.size → hi - lo ≤ fuel →
      ∀ (i : Nat) (hi' : i < keys.size), lo ≤ i → i < hi → keys[i] = x → bsearchAux keys x fuel lo hi = true
  | 0, _, _, _, hf, _, _, _, _, _ => by omega
  | fuel + 1, lo, hi, hsz, hf, i, hi', hlo, hhi, hx => by
    have hlt : lo < hi := by omega
    have hmid : lo + (hi - lo) / 2 < keys.size := by omega
    have hget : keys.getD (lo + (hi - lo) / 2) 0 = keys[lo + (hi - lo) / 2] := by simp [Array.getD, hmid]
    simp only [bsearchAux, hlt, ↓reduceIte, hget]
    by_cases h1 : keys[lo + (hi - lo) / 2] = x
    · simp [h1]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : keys[lo + (hi - lo) / 2] < x <;> simp only [h2, ↓reduceIte]
      · have hgt : lo + (hi - lo) / 2 < i := by
          rcases Nat.lt_trichotomy i (lo + (hi - lo) / 2) with h | rfl | h
          · have := hs i _ hi' hmid h; omega
          · exact absurd hx h1
          · exact h
        exact bsearchAux_complete keys x hs fuel _ hi hsz (by omega) i hi' (by omega) hhi hx
      · have hlt' : i < lo + (hi - lo) / 2 := by
          rcases Nat.lt_trichotomy i (lo + (hi - lo) / 2) with h | rfl | h
          · exact h
          · exact absurd hx h1
          · have := hs _ i hmid hi' h; omega
        exact bsearchAux_complete keys x hs fuel lo _ (by omega) (by omega) i hi' hlo hlt' hx
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
        constructor <;> rintro (h | h | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
theorem insertSorted_pairwise (x : Nat) : ∀ (l : List Nat), l.Pairwise (· < ·) → (insertSorted x l).Pairwise (· < ·)
  | [], _ => by simp [insertSorted]
  | y :: ys, hp => by
    obtain ⟨hy, hys⟩ := List.pairwise_cons.1 hp
    by_cases h1 : x < y
    · simp only [insertSorted, h1, ↓reduceIte]
      refine List.pairwise_cons.2 ⟨fun a ha => ?_, hp⟩
      rcases List.mem_cons.1 ha with rfl | ha'; · exact h1
      · exact Nat.lt_trans h1 (hy a ha')
    · by_cases h2 : x = y
      · subst h2; simpa [insertSorted] using hp
      · simp only [insertSorted, h1, h2, ↓reduceIte]
        refine List.pairwise_cons.2 ⟨fun a ha => ?_, insertSorted_pairwise x ys hys⟩
        rcases (mem_insertSorted x a ys).1 ha with rfl | ha'; · omega
        · exact hy a ha'
def dedupSort (xs : List Nat) : List Nat := xs.foldl (fun acc x => insertSorted x acc) []
private theorem mem_dedupSort_aux (acc xs : List Nat) (z : Nat) :
    z ∈ xs.foldl (fun a x => insertSorted x a) acc ↔ z ∈ acc ∨ z ∈ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons x _ ih =>
    simp only [List.foldl_cons, ih, mem_insertSorted, List.mem_cons]
    constructor
    · rintro ((rfl | h) | h)
      · exact .inr (.inl rfl)
      · exact .inl h
      · exact .inr (.inr h)
    · rintro (h | rfl | h)
      · exact .inl (.inr h)
      · exact .inl (.inl rfl)
      · exact .inr h
theorem mem_dedupSort_iff (xs : List Nat) (z : Nat) : z ∈ dedupSort xs ↔ z ∈ xs := by
  simpa [dedupSort] using mem_dedupSort_aux [] xs z
private theorem dedupSort_pairwise_aux (acc xs : List Nat) (hp : acc.Pairwise (· < ·)) :
    (xs.foldl (fun a x => insertSorted x a) acc).Pairwise (· < ·) := by
  induction xs generalizing acc with | nil => exact hp | cons x _ ih => exact ih _ (insertSorted_pairwise x acc hp)
theorem dedupSort_pairwise (xs : List Nat) : (dedupSort xs).Pairwise (· < ·) :=
  dedupSort_pairwise_aux [] xs List.Pairwise.nil
theorem pairwise_lt_ext : ∀ {l₁ l₂ : List Nat},
    l₁.Pairwise (· < ·) → l₂.Pairwise (· < ·) → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, heq => nomatch (heq y).2 List.mem_cons_self
  | x :: _, [], _, _, heq => nomatch (heq x).1 List.mem_cons_self
  | x :: xs, y :: ys, hp1, hp2, heq => by
    obtain ⟨hx, hxs⟩ := List.pairwise_cons.1 hp1; obtain ⟨hy, hys⟩ := List.pairwise_cons.1 hp2
    have hxy : x = y := by
      rcases List.mem_cons.1 ((heq x).1 List.mem_cons_self) with rfl | h1
      · rfl
      · rcases List.mem_cons.1 ((heq y).2 List.mem_cons_self) with h2 | h2
        · exact h2.symm
        · have := hy x h1; have := hx y h2; omega
    subst hxy; congr 1; apply pairwise_lt_ext hxs hys; intro z; constructor
    · intro hz; rcases List.mem_cons.1 ((heq z).1 (List.mem_cons_of_mem _ hz)) with rfl | h'
      · have := hx z hz; omega
      · exact h'
    · intro hz; rcases List.mem_cons.1 ((heq z).2 (List.mem_cons_of_mem _ hz)) with rfl | h'
      · have := hy z hz; omega
      · exact h'
theorem dedupSort_order_independent {xs ys : List Nat} (h : ∀ z, z ∈ xs ↔ z ∈ ys) :
    dedupSort xs = dedupSort ys :=
  pairwise_lt_ext (dedupSort_pairwise xs) (dedupSort_pairwise ys) fun z => by
    rw [mem_dedupSort_iff, mem_dedupSort_iff, h]
def isStrictlySorted : List Nat → Bool
  | [] | [_] => true
  | a :: b :: rest => decide (a < b) && isStrictlySorted (b :: rest)
theorem isStrictlySorted_sound : ∀ (l : List Nat), isStrictlySorted l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    simp only [isStrictlySorted, Bool.and_eq_true, decide_eq_true_eq] at h
    have hp := isStrictlySorted_sound (b :: rest) h.2; obtain ⟨hb, _⟩ := List.pairwise_cons.1 hp
    refine List.pairwise_cons.2 ⟨fun z hz => ?_, hp⟩
    rcases List.mem_cons.1 hz with rfl | hz'; · exact h.1
    · exact Nat.lt_trans h.1 (hb z hz')
structure RevocationSet where
  keys   : Array Nat
  sorted : keys.toList.Pairwise (· < ·)

namespace RevocationSet
def empty : RevocationSet := ⟨#[], List.Pairwise.nil⟩
def ofList (raw : List Nat) : RevocationSet := ⟨(dedupSort raw).toArray, dedupSort_pairwise raw⟩
def insert (s : RevocationSet) (x : Nat) : RevocationSet :=
  ⟨(insertSorted x s.keys.toList).toArray, insertSorted_pairwise x _ s.sorted⟩
def contains (s : RevocationSet) (x : Nat) : Bool := bsearch s.keys x
def root (s : RevocationSet) : List UInt8 := cshake32 custRevRoot (encodeNats s.keys.toList)
theorem ext {s₁ s₂ : RevocationSet} (h : s₁.keys = s₂.keys) : s₁ = s₂ := by cases s₁; cases s₂; cases h; rfl
theorem sorted_getElem (s : RevocationSet) (i j : Nat) (hi : i < s.keys.size)
    (hj : j < s.keys.size) (hij : i < j) : s.keys[i] < s.keys[j] := by
  have h := List.pairwise_iff_getElem.1 s.sorted i j (by simpa using hi) (by simpa using hj) hij; simpa using h
theorem contains_iff (s : RevocationSet) (x : Nat) : s.contains x = true ↔ x ∈ s.keys.toList := by
  refine ⟨bsearchAux_sound s.keys x _ 0 _ (Nat.le_refl _), fun hx => ?_⟩
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.1 hx; have hi' : i < s.keys.size := by simpa using hi
  exact bsearchAux_complete s.keys x s.sorted_getElem _ 0 _ (Nat.le_refl _) (by omega)
    i hi' (Nat.zero_le _) hi' (by simpa using hxi)
theorem contains_ofList_iff (raw : List Nat) (x : Nat) : (ofList raw).contains x = true ↔ x ∈ raw := by
  rw [contains_iff]; simpa [ofList] using mem_dedupSort_iff raw x
theorem ofList_order_independent {xs ys : List Nat} (h : ∀ z, z ∈ xs ↔ z ∈ ys) : ofList xs = ofList ys :=
  ext (congrArg List.toArray (dedupSort_order_independent h))
theorem root_binds {s₁ s₂ : RevocationSet} (h : s₁.root = s₂.root) :
    s₁ = s₂ ∨ CollisionAmong (cshake256Bytes custRevRoot)
      (fun z => z = encodeNats s₁.keys.toList ∨ z = encodeNats s₂.keys.toList) := by
  rcases cshake32_binds custRevRoot h with heq | hc
  · exact Or.inl (ext (Array.toList_inj.1 (encodeNats_injective heq)))
  · exact Or.inr hc
def fromVerifiedWitness (raw : List Nat) (expectedRoot : List UInt8) : Option RevocationSet :=
  if h : isStrictlySorted raw = true then
    let rs : RevocationSet := ⟨raw.toArray, isStrictlySorted_sound raw h⟩
    if rs.root == expectedRoot then some rs else none
  else none
end RevocationSet

/-! ## §4. Salted `cSHAKE256` Selective-Disclosure Attribute Merkle Tree & Hiding -/
def attrLeafCommit (idx : Nat) (key val salt : List UInt8) : List UInt8 :=
  cshake32 custAttrLeaf (0x00 :: (leb128 idx ++ (encodeField key ++ (encodeField val ++ encodeField salt))))
def attrEmptyLeaf : List UInt8 := cshake32 custAttrLeaf [0x02]
def attrNodeHash (left right : List UInt8) : List UInt8 := cshake32 custAttrNode (0x01 :: left ++ right)
theorem attrLeafCommit_binds {i₁ i₂ : Nat} {k₁ k₂ v₁ v₂ s₁ s₂ : List UInt8}
    (h : attrLeafCommit i₁ k₁ v₁ s₁ = attrLeafCommit i₂ k₂ v₂ s₂) :
    (i₁ = i₂ ∧ k₁ = k₂ ∧ v₁ = v₂ ∧ s₁ = s₂) ∨
      CollisionAmong (cshake256Bytes custAttrLeaf) (fun z =>
        z = (0x00 :: (leb128 i₁ ++ (encodeField k₁ ++ (encodeField v₁ ++ encodeField s₁)))) ∨
        z = (0x00 :: (leb128 i₂ ++ (encodeField k₂ ++ (encodeField v₂ ++ encodeField s₂))))) := by
  rcases cshake32_binds custAttrLeaf h with hp | hc
  · obtain ⟨hi, h1⟩ := leb128_prefix_inj i₁ i₂ _ _ (List.cons.inj hp).2
    obtain ⟨hk, h2⟩ := encodeField_prefix_inj h1; obtain ⟨hv, h3⟩ := encodeField_prefix_inj h2
    have h3' : encodeField s₁ ++ [] = encodeField s₂ ++ [] := by rw [List.append_nil, List.append_nil]; exact h3
    obtain ⟨hs, _⟩ := encodeField_prefix_inj h3'; exact Or.inl ⟨hi, hk, hv, hs⟩
  · exact Or.inr hc
def merklePairLayer : List (List UInt8) → List (List UInt8)
  | [] => []
  | [a] => [attrNodeHash a attrEmptyLeaf]
  | a :: b :: rest => attrNodeHash a b :: merklePairLayer rest
def merkleRootAux : Nat → List (List UInt8) → List UInt8
  | 0, leaves => leaves.getD 0 attrEmptyLeaf
  | h + 1, leaves => merkleRootAux h (merklePairLayer leaves)
def merklePathAux : Nat → Nat → List (List UInt8) → List (Bool × List UInt8)
  | 0, _, _ => []
  | h + 1, idx, leaves =>
    let isRight := idx % 2 == 0
    (isRight, leaves.getD (if isRight then idx + 1 else idx - 1) attrEmptyLeaf) ::
      merklePathAux h (idx / 2) (merklePairLayer leaves)
def merkleFold (leaf : List UInt8) : List (Bool × List UInt8) → List UInt8
  | [] => leaf
  | (isRight, sib) :: rest => merkleFold (if isRight then attrNodeHash leaf sib else attrNodeHash sib leaf) rest
def verifyMerkleOpening (root leaf : List UInt8) (path : List (Bool × List UInt8)) : Bool :=
  merkleFold leaf path == root
private theorem merklePairLayer_getD : ∀ (leaves : List (List UInt8)) (k : Nat),
    leaves.length % 2 = 0 → 2 * k + 1 < leaves.length →
    (merklePairLayer leaves).getD k attrEmptyLeaf =
      attrNodeHash (leaves.getD (2 * k) attrEmptyLeaf) (leaves.getD (2 * k + 1) attrEmptyLeaf)
  | [], _, _, hk => by simp at hk
  | [_], _, heven, _ => by simp at heven
  | _ :: _ :: _, 0, _, _ => by simp [merklePairLayer]
  | _ :: _ :: rest, k' + 1, heven, hk => by
    simp only [List.length_cons] at heven hk
    have h1 : 2 * (k' + 1) = (2 * k') + 2 := by omega
    have h2 : 2 * k' + 2 + 1 = (2 * k' + 1) + 2 := by omega
    rw [merklePairLayer, List.getD_cons_succ, h1, h2]; simp only [List.getD_cons_succ]
    exact merklePairLayer_getD rest k' (by omega) (by omega)
private theorem merklePairLayer_length : ∀ (leaves : List (List UInt8)),
    leaves.length % 2 = 0 → (merklePairLayer leaves).length = leaves.length / 2
  | [], _ => rfl
  | [_], heven => by simp at heven
  | _ :: _ :: rest, heven => by
    simp only [List.length_cons] at heven ⊢
    rw [merklePairLayer, List.length_cons, merklePairLayer_length rest (by omega)]; omega
theorem verifyMerkleOpening_complete : ∀ (h : Nat) (leaves : List (List UInt8)) (i : Nat),
    leaves.length = 2 ^ h → i < 2 ^ h →
    verifyMerkleOpening (merkleRootAux h leaves) (leaves.getD i attrEmptyLeaf) (merklePathAux h i leaves) = true
  | 0, _, i, _, hi => by
    have : i = 0 := by omega
    subst this; simp [verifyMerkleOpening, merkleFold, merkleRootAux, merklePathAux]
  | h + 1, leaves, i, hlen, hi => by
    have hpow : 2 ^ (h + 1) = 2 * 2 ^ h := by rw [Nat.pow_succ]; omega
    have heven : leaves.length % 2 = 0 := by rw [hlen, hpow]; omega
    have hpairLen : (merklePairLayer leaves).length = 2 ^ h := by
      rw [merklePairLayer_length leaves heven, hlen, hpow]; omega
    have hparent := merklePairLayer_getD leaves (i / 2) heven (by rw [hlen, hpow]; omega)
    have ih := verifyMerkleOpening_complete h (merklePairLayer leaves) (i / 2) hpairLen (by omega)
    unfold verifyMerkleOpening at ih ⊢; simp only [merklePathAux, merkleFold, merkleRootAux]
    by_cases hmod : i % 2 = 0
    · rw [show 2 * (i / 2) = i by omega] at hparent
      simp only [hmod, beq_self_eq_true, ↓reduceIte]; rw [← hparent]; exact ih
    · rw [show 2 * (i / 2) = i - 1 by omega, show i - 1 + 1 = i by omega] at hparent
      simp only [beq_false_of_ne hmod, Bool.false_eq_true, ↓reduceIte]; rw [← hparent]; exact ih
theorem merkleFold_binds :
    ∀ (p₁ p₂ : List (Bool × List UInt8)) (l₁ l₂ : List UInt8),
      l₁.length = 32 → l₂.length = 32 → (∀ x ∈ p₁, x.2.length = 32) → (∀ x ∈ p₂, x.2.length = 32) →
      p₁.map Prod.fst = p₂.map Prod.fst → merkleFold l₁ p₁ = merkleFold l₂ p₂ →
      (l₁ = l₂ ∧ p₁ = p₂) ∨ Collision (cshake256Bytes custAttrNode)
  | [], [], _, _, _, _, _, _, _, h => Or.inl ⟨h, rfl⟩
  | [], _ :: _, _, _, _, _, _, _, hdir, _ => by simp at hdir
  | _ :: _, [], _, _, _, _, _, _, hdir, _ => by simp at hdir
  | (b₁, s₁) :: r₁, (b₂, s₂) :: r₂, l₁, l₂, hl1, hl2, hp1, hp2, hdir, h => by
    simp only [List.map_cons, List.cons.injEq] at hdir; obtain ⟨rfl, hdir'⟩ := hdir
    have hs1 := hp1 (b₁, s₁) List.mem_cons_self; have hs2 := hp2 (b₁, s₂) List.mem_cons_self
    simp only [merkleFold] at h
    have hP1 : (if b₁ then attrNodeHash l₁ s₁ else attrNodeHash s₁ l₁).length = 32 := by cases b₁ <;> exact cshake32_length _ _
    have hP2 : (if b₁ then attrNodeHash l₂ s₂ else attrNodeHash s₂ l₂).length = 32 := by cases b₁ <;> exact cshake32_length _ _
    rcases merkleFold_binds r₁ r₂ _ _ hP1 hP2 (fun x hx => hp1 x (List.mem_cons_of_mem _ hx))
        (fun x hx => hp2 x (List.mem_cons_of_mem _ hx)) hdir' h with ⟨hpar, rfl⟩ | hc
    · cases b₁
      · simp only [Bool.false_eq_true, ↓reduceIte] at hpar
        rcases cshake32_binds custAttrNode hpar with heq | hc
        · obtain ⟨hseq, hleq⟩ := List.append_inj (List.cons.inj heq).2 (by rw [hs1, hs2]); exact Or.inl ⟨hleq, by rw [hseq]⟩
        · exact Or.inr hc.global
      · simp only [↓reduceIte] at hpar
        rcases cshake32_binds custAttrNode hpar with heq | hc
        · obtain ⟨hleq, hseq⟩ := List.append_inj (List.cons.inj heq).2 (by rw [hl1, hl2]); exact Or.inl ⟨hleq, by rw [hseq]⟩
        · exact Or.inr hc.global
    · exact Or.inr hc
structure SelectiveOpening where
  idx   : Nat
  key   : List UInt8
  value : List UInt8
  salt  : List UInt8
  path  : List (Bool × List UInt8)
  deriving DecidableEq, Repr
def verifySelectiveOpening (root : List UInt8) (op : SelectiveOpening) : Bool :=
  (op.salt.length == 32) && verifyMerkleOpening root (attrLeafCommit op.idx op.key op.value op.salt) op.path
def verifySelectiveDisclosure (root : List UInt8) (openings : List SelectiveOpening) : Bool :=
  openings.all (verifySelectiveOpening root)
def buildSelectiveOpenings (h : Nat) (attrs : List (List UInt8 × List UInt8 × List UInt8))
    (disclosed : List Nat) : List SelectiveOpening :=
  let leaves := (List.range (2 ^ h)).map fun i =>
    match attrs[i]? with | some (k, v, s) => attrLeafCommit i k v s | none => attrEmptyLeaf
  disclosed.filterMap fun i =>
    match attrs[i]? with | some (k, v, s) => some ⟨i, k, v, s, merklePathAux h i leaves⟩ | none => none
private theorem list_filterMap_ext {α β : Type} (l : List α) {f g : α → Option β}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with | nil => rfl | cons x _ ih =>
    simp only [List.filterMap_cons, h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
theorem unrevealed_attr_view_independent (h : Nat)
    (attrs₁ attrs₂ : List (List UInt8 × List UInt8 × List UInt8)) (disclosed : List Nat)
    (hdis : ∀ i ∈ disclosed, attrs₁[i]? = attrs₂[i]?)
    (hcom : ∀ i, i < 2 ^ h →
      (match attrs₁[i]? with | some (k, v, s) => attrLeafCommit i k v s | none => attrEmptyLeaf) =
      (match attrs₂[i]? with | some (k, v, s) => attrLeafCommit i k v s | none => attrEmptyLeaf)) :
    buildSelectiveOpenings h attrs₁ disclosed = buildSelectiveOpenings h attrs₂ disclosed := by
  unfold buildSelectiveOpenings
  have hleaves :
      ((List.range (2 ^ h)).map fun i => match attrs₁[i]? with | some (k, v, s) => attrLeafCommit i k v s | none => attrEmptyLeaf) =
      ((List.range (2 ^ h)).map fun i => match attrs₂[i]? with | some (k, v, s) => attrLeafCommit i k v s | none => attrEmptyLeaf) :=
    List.map_congr_left fun i hi => hcom i (List.mem_range.1 hi)
  rw [hleaves]; exact list_filterMap_ext disclosed fun i hi => by rw [hdis i hi]
def saltHitCount (space : Nat) (queries : List (List UInt8)) : Nat :=
  (List.range space).countP (fun s => queries.any (fun q => q == be 32 s))
private theorem countP_single_be32_le_one (q : List UInt8) :
    ∀ (n : Nat), n ≤ 256 ^ 32 → (List.range n).countP (fun s => q == be 32 s) ≤ 1 := by
  intro n hn; induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
    by_cases hm : (q == be 32 m) = true
    · have hzero : (List.range m).countP (fun s => q == be 32 s) = 0 := by
        rw [List.countP_eq_zero]; intro s hs hqs
        have hsm : s < m := List.mem_range.1 hs
        have := be_injective (by omega : s < 256 ^ 32) (by omega : m < 256 ^ 32) ((beq_iff_eq.1 hqs).symm.trans (beq_iff_eq.1 hm)); omega
      simp [hm, hzero]
    · simp only [Bool.eq_false_iff.2 hm, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; exact ih (by omega)
theorem unrevealed_salt_offline_guess_bound (space : Nat) (hspace : space ≤ 2 ^ 256)
    (queries : List (List UInt8)) : saltHitCount space queries ≤ queries.length := by
  have hpow : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  have hspace' : space ≤ 256 ^ 32 := hpow ▸ hspace
  unfold saltHitCount; induction queries with
  | nil => simp
  | cons q tl ih =>
    have hsplit : ∀ (xs : List Nat),
        xs.countP (fun s => (q == be 32 s) || tl.any (fun r => r == be 32 s)) ≤
          xs.countP (fun s => q == be 32 s) + xs.countP (fun s => tl.any (fun r => r == be 32 s)) := by
      intro xs; induction xs with | nil => simp | cons a _ ixs =>
        simp only [List.countP_cons]; cases (q == be 32 a) <;> cases tl.any (fun r => r == be 32 a) <;> simp <;> omega
    have h1 := hsplit (List.range space); have h2 := countP_single_be32_le_one q space hspace'
    simp only [List.any_cons, List.length_cons]; omega

/-! ## §5. `CAP-01` Root-Key Isolation, `CAP-12` Block-0 Authority Pin & `ZkBiscuit` Chain -/
/-- Issuer secret key (`CAP-01`): NEVER placed inside `HolderToken`. -/
structure IssuerSecret (S : PqSigScheme) where
  sk : S.SecKey
structure AuthorityBlock0 where
  subject        : List UInt8
  issuerPk       : List UInt8
  holderPk       : List UInt8
  rights         : UInt64
  expiresAt      : UInt64
  attrMerkleRoot : List UInt8
  nonce          : List UInt8
  deriving DecidableEq, Repr
structure AttenuationBlock where
  rights       : UInt64
  expiresAt    : UInt64
  nextHolderPk : List UInt8
  caveatTag    : List UInt8
  sigBytes     : List UInt8
  deriving DecidableEq, Repr
structure HolderToken where
  block0    : AuthorityBlock0
  block0Sig : List UInt8
  hops      : List AttenuationBlock
  deriving DecidableEq, Repr
def AuthorityBlock0.encode (b : AuthorityBlock0) : List UInt8 :=
  encodeField b.subject ++ (encodeField b.issuerPk ++ (encodeField b.holderPk ++
    (be 8 b.rights.toNat ++ (be 8 b.expiresAt.toNat ++ (encodeField b.attrMerkleRoot ++ encodeField b.nonce)))))
theorem AuthorityBlock0.encode_injective {a b : AuthorityBlock0} (h : a.encode = b.encode) : a = b := by
  obtain ⟨s₁, i₁, h₁, r₁, e₁, m₁, n₁⟩ := a; obtain ⟨s₂, i₂, h₂, r₂, e₂, m₂, n₂⟩ := b
  simp only [AuthorityBlock0.encode] at h
  obtain ⟨rfl, k1⟩ := encodeField_prefix_inj h; obtain ⟨rfl, k2⟩ := encodeField_prefix_inj k1
  obtain ⟨rfl, k3⟩ := encodeField_prefix_inj k2; obtain ⟨hr, k4⟩ := List.append_inj k3 (by simp)
  obtain ⟨he, k5⟩ := List.append_inj k4 (by simp); obtain ⟨rfl, k6⟩ := encodeField_prefix_inj k5
  have k6' : encodeField n₁ ++ [] = encodeField n₂ ++ [] := by rw [List.append_nil, List.append_nil]; exact k6
  obtain ⟨rfl, _⟩ := encodeField_prefix_inj k6'
  have h8 : (2 : Nat) ^ 64 = 256 ^ 8 := by decide
  have hr' := UInt64.toNat_inj.1 (be_injective (h8 ▸ r₁.toNat_lt) (h8 ▸ r₂.toNat_lt) hr)
  have he' := UInt64.toNat_inj.1 (be_injective (h8 ▸ e₁.toNat_lt) (h8 ▸ e₂.toNat_lt) he)
  subst hr'; subst he'; rfl
def AttenuationBlock.payloadEncode (b : AttenuationBlock) : List UInt8 :=
  be 8 b.rights.toNat ++ (be 8 b.expiresAt.toNat ++ (encodeField b.nextHolderPk ++ encodeField b.caveatTag))
def block0SignMsg (b0 : AuthorityBlock0) : List UInt8 := 0x00 :: b0.encode
theorem block0SignMsg_injective {a b : AuthorityBlock0} (h : block0SignMsg a = block0SignMsg b) : a = b :=
  AuthorityBlock0.encode_injective (List.cons.inj h).2
def hopSignMsg (prevLineage : List UInt8) (h : AttenuationBlock) : List UInt8 :=
  0x01 :: (encodeField prevLineage ++ h.payloadEncode)
def rootLineage (b0 : AuthorityBlock0) : List UInt8 := cshake32 custLineage (0x00 :: b0.encode)
def stepLineage (prev : List UInt8) (h : AttenuationBlock) : List UInt8 :=
  cshake32 custLineage (0x01 :: (encodeField prev ++ h.payloadEncode))
def lineageOf (b0 : AuthorityBlock0) (hops : List AttenuationBlock) : List UInt8 :=
  hops.foldl stepLineage (rootLineage b0)
def chainId (b0 : AuthorityBlock0) (hops : List AttenuationBlock) (j : Nat) : Nat :=
  ofBE (cshake32 custNullifier (0x01 :: lineageOf b0 (hops.take j)))
def subMask (child parent : UInt64) : Bool := (child &&& parent) == child
theorem subMask_refl (a : UInt64) : subMask a a = true := by simp [subMask]
theorem subMask_trans {a b c : UInt64} (hab : subMask a b = true) (hbc : subMask b c = true) : subMask a c = true := by
  simp only [subMask, beq_iff_eq] at hab hbc ⊢
  calc a &&& c = (a &&& b) &&& c := by rw [hab]
    _ = a &&& (b &&& c) := UInt64.toBitVec_inj.1 (by simp [BitVec.and_assoc])
    _ = a &&& b := by rw [hbc]
    _ = a := hab
def extractSubject (tok : HolderToken) : List UInt8 := tok.block0.subject
structure IssuerAuthority where
  issuerPk       : List UInt8
  subject        : List UInt8
  rootRights     : UInt64
  rootExpiresAt  : UInt64
  attrMerkleRoot : List UInt8
  deriving DecidableEq, Repr
def extractIssuerAuthority (tok : HolderToken) : IssuerAuthority :=
  ⟨tok.block0.issuerPk, tok.block0.subject, tok.block0.rights, tok.block0.expiresAt, tok.block0.attrMerkleRoot⟩
theorem extractSubject_invariant_under_hops (b0 : AuthorityBlock0) (sig : List UInt8)
    (h₁ h₂ : List AttenuationBlock) : extractSubject ⟨b0, sig, h₁⟩ = extractSubject ⟨b0, sig, h₂⟩ := rfl
theorem extractIssuerAuthority_invariant_under_hops (b0 : AuthorityBlock0) (sig : List UInt8)
    (h₁ h₂ : List AttenuationBlock) : extractIssuerAuthority ⟨b0, sig, h₁⟩ = extractIssuerAuthority ⟨b0, sig, h₂⟩ := rfl
def issueRootToken (S : PqSigScheme) (issuer : IssuerSecret S)
    (subject holderPk attrMerkleRoot nonce : List UInt8) (rights expiresAt : UInt64) : HolderToken :=
  let b0 : AuthorityBlock0 := ⟨subject, S.pkOf issuer.sk, holderPk, rights, expiresAt, attrMerkleRoot, nonce⟩
  ⟨b0, S.sign issuer.sk (block0SignMsg b0), []⟩
def attenuateToken (S : PqSigScheme) (tok : HolderToken) (holderSk : S.SecKey)
    (newRights newExpiresAt : UInt64) (nextHolderPk caveatTag : List UInt8) : HolderToken :=
  let unsigned : AttenuationBlock := ⟨newRights, newExpiresAt, nextHolderPk, caveatTag, []⟩
  { tok with hops := tok.hops ++ [{ unsigned with sigBytes := S.sign holderSk (hopSignMsg (lineageOf tok.block0 tok.hops) unsigned) }] }
structure ChainState where
  holderPk  : List UInt8
  lineage   : List UInt8
  rights    : UInt64
  expiresAt : UInt64
  deriving DecidableEq, Repr
def verifyHopStep (S : PqSigScheme) (rs : RevocationSet) (st : ChainState) (h : AttenuationBlock) : Option ChainState :=
  if subMask h.rights st.rights && decide (h.expiresAt ≤ st.expiresAt) &&
     S.verify st.holderPk (hopSignMsg st.lineage h) h.sigBytes &&
     !rs.contains (ofBE (cshake32 custNullifier (0x01 :: stepLineage st.lineage h))) then
    some ⟨h.nextHolderPk, stepLineage st.lineage h, h.rights, h.expiresAt⟩
  else none
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
  if tok.block0.issuerPk == issuerPk && S.verify issuerPk (block0SignMsg tok.block0) tok.block0Sig &&
     !rs.contains (ofBE (cshake32 custNullifier (0x01 :: rootLineage tok.block0))) then
    match tok.hops.foldlM (verifyHopStep S rs)
        ⟨tok.block0.holderPk, rootLineage tok.block0, tok.block0.rights, tok.block0.expiresAt⟩ with
    | some st =>
      if decide (now ≤ st.expiresAt) then
        some ⟨tok.block0.subject, st.rights, st.expiresAt, tok.block0.attrMerkleRoot, st.lineage, st.holderPk⟩
      else none
    | none => none
  else none
def verifyPresentation (S : PqSigScheme) (issuerPk : List UInt8) (rs : RevocationSet)
    (now : UInt64) (tok : HolderToken) (openings : List SelectiveOpening) : Option VerifiedAuthority :=
  match verifyToken S issuerPk rs now tok with
  | some va => if verifySelectiveDisclosure va.attrMerkleRoot openings then some va else none
  | none => none
private theorem foldlM_cons_some {α β : Type} (f : α → β → Option α) (a : α) (b : β) (bs : List β) (r : α) :
    (b :: bs).foldlM f a = some r ↔ ∃ a1, f a b = some a1 ∧ bs.foldlM f a1 = some r := by
  simp only [List.foldlM_cons]; cases f a b <;> simp
private theorem foldlM_append_some {α β : Type} (f : α → β → Option α) (a : α) (xs ys : List β) (r : α) :
    (xs ++ ys).foldlM f a = some r ↔ ∃ a1, xs.foldlM f a = some a1 ∧ ys.foldlM f a1 = some r := by
  induction xs generalizing a with
  | nil => simp
  | cons x _ ih =>
    simp only [List.cons_append, foldlM_cons_some]
    exact ⟨by rintro ⟨a1, h1, h2⟩; obtain ⟨a2, ha, hb⟩ := (ih a1).1 h2; exact ⟨a2, ⟨a1, h1, ha⟩, hb⟩,
           by rintro ⟨a2, ⟨a1, h1, ha⟩, hb⟩; exact ⟨a1, h1, (ih a1).2 ⟨a2, ha, hb⟩⟩⟩
private theorem verifyHopStep_eq_some {S : PqSigScheme} {rs : RevocationSet}
    {st st' : ChainState} {h : AttenuationBlock} (hv : verifyHopStep S rs st h = some st') :
    subMask h.rights st.rights = true ∧ h.expiresAt ≤ st.expiresAt ∧
    S.verify st.holderPk (hopSignMsg st.lineage h) h.sigBytes = true ∧
    rs.contains (ofBE (cshake32 custNullifier (0x01 :: stepLineage st.lineage h))) = false ∧
    st' = ⟨h.nextHolderPk, stepLineage st.lineage h, h.rights, h.expiresAt⟩ := by
  unfold verifyHopStep at hv; split at hv
  · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
    exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2, (Option.some.inj hv).symm⟩
  · cases hv
private theorem verifyHops_facts (S : PqSigScheme) (rs : RevocationSet) :
    ∀ (l : List AttenuationBlock) (st st' : ChainState), l.foldlM (verifyHopStep S rs) st = some st' →
      st'.lineage = l.foldl stepLineage st.lineage ∧ subMask st'.rights st.rights = true ∧ st'.expiresAt ≤ st.expiresAt ∧
      (rs.contains (ofBE (cshake32 custNullifier (0x01 :: st.lineage))) = false →
        ∀ j, j ≤ l.length → rs.contains (ofBE (cshake32 custNullifier (0x01 :: (l.take j).foldl stepLineage st.lineage))) = false)
  | [], st, st', hv => by
    cases Option.some.inj hv; exact ⟨rfl, subMask_refl _, Nat.le_refl _, fun h0 _ _ => by simpa using h0⟩
  | h :: rest, st, st', hv => by
    obtain ⟨st1, h1, h2⟩ := (foldlM_cons_some _ _ _ _ _).1 hv
    obtain ⟨hr, he, _, hnul, hst1⟩ := verifyHopStep_eq_some h1
    obtain ⟨ihLin, ihR, ihE, ihNul⟩ := verifyHops_facts S rs rest st1 st' h2
    rw [hst1] at ihLin ihR ihE ihNul
    refine ⟨by rw [ihLin]; rfl, subMask_trans ihR hr, Nat.le_trans ihE he, fun h0 j hj => ?_⟩
    cases j with
    | zero => simpa using h0
    | succ j' => simp only [List.length_cons] at hj; simpa [List.take_succ_cons, List.foldl_cons] using ihNul hnul j' (by omega)
theorem holder_attenuate_needs_no_issuer_secret (S : PqSigScheme)
    (issuerPk : List UInt8) (rs : RevocationSet) (now : UInt64)
    (tok : HolderToken) (va : VerifiedAuthority) (holderSk : S.SecKey)
    (newRights newExp : UInt64) (nextPk tag : List UInt8)
    (hv : verifyToken S issuerPk rs now tok = some va)
    (hown : S.pkOf holderSk = va.tailHolderPk) (hsub : subMask newRights va.rights = true)
    (hexp : newExp ≤ va.expiresAt) (hnow : now ≤ newExp)
    (hlive : rs.contains (ofBE (cshake32 custNullifier
      (0x01 :: stepLineage va.tailLineage ⟨newRights, newExp, nextPk, tag, []⟩))) = false) :
    ∃ va', verifyToken S issuerPk rs now (attenuateToken S tok holderSk newRights newExp nextPk tag) = some va' ∧
      va'.subject = tok.block0.subject ∧ va'.rights = newRights ∧ va'.expiresAt = newExp := by
  unfold verifyToken at hv; split at hv
  · rename_i hroot
    cases hfold : tok.hops.foldlM (verifyHopStep S rs)
        ⟨tok.block0.holderPk, rootLineage tok.block0, tok.block0.rights, tok.block0.expiresAt⟩ with
    | none => simp [hfold] at hv
    | some st =>
      simp only [hfold] at hv; split at hv
      · cases Option.some.inj hv
        dsimp only at hown hsub hexp hlive
        have hlin := (verifyHops_facts S rs tok.hops _ _ hfold).1
        let u : AttenuationBlock := ⟨newRights, newExp, nextPk, tag, []⟩
        let sig := S.sign holderSk (hopSignMsg (lineageOf tok.block0 tok.hops) u)
        have happ : (tok.hops ++ [{ u with sigBytes := sig }]).foldlM (verifyHopStep S rs)
            ⟨tok.block0.holderPk, rootLineage tok.block0, tok.block0.rights, tok.block0.expiresAt⟩ =
            some ⟨nextPk, stepLineage st.lineage u, newRights, newExp⟩ := by
          rw [foldlM_append_some]; refine ⟨st, hfold, ?_⟩
          simp only [List.foldlM_cons, List.foldlM_nil]
          have hsig := S.verify_sign holderSk (hopSignMsg (lineageOf tok.block0 tok.hops) u)
          have hmsgEq : hopSignMsg st.lineage { u with sigBytes := sig } = hopSignMsg (lineageOf tok.block0 tok.hops) u := by
            simp only [hopSignMsg, AttenuationBlock.payloadEncode, lineageOf, hlin]
          have hstep : stepLineage st.lineage { u with sigBytes := sig } = stepLineage st.lineage u := rfl
          unfold verifyHopStep; rw [← hown, hmsgEq, hstep]
          simp [u, sig, hsig, hsub, hexp, hlive]
        have hres : verifyToken S issuerPk rs now (attenuateToken S tok holderSk newRights newExp nextPk tag) =
            some ⟨tok.block0.subject, newRights, newExp, tok.block0.attrMerkleRoot, stepLineage st.lineage u, nextPk⟩ := by
          unfold attenuateToken verifyToken; dsimp only; simp only [hroot, ↓reduceIte]
          change (match (tok.hops ++ [{ u with sigBytes := sig }]).foldlM (verifyHopStep S rs)
              ⟨tok.block0.holderPk, rootLineage tok.block0, tok.block0.rights, tok.block0.expiresAt⟩ with
            | some st' => if decide (now ≤ st'.expiresAt) then
                some (⟨tok.block0.subject, st'.rights, st'.expiresAt, tok.block0.attrMerkleRoot, st'.lineage, st'.holderPk⟩ : VerifiedAuthority)
              else none
            | none => none) = _
          rw [happ]; simp [hnow]
        exact ⟨_, hres, rfl, rfl, rfl⟩
      · simp at hv
  · simp at hv
theorem block0_unforgeable_reduction (S : PqSigScheme) (issuerPk : List UInt8)
    (rs : RevocationSet) (now : UInt64) (issuedBlocks : List AuthorityBlock0)
    (tok : HolderToken) (va : VerifiedAuthority)
    (hv : verifyToken S issuerPk rs now tok = some va) (hfresh : tok.block0 ∉ issuedBlocks) :
    S.verify issuerPk (block0SignMsg tok.block0) tok.block0Sig = true ∧
    block0SignMsg tok.block0 ∉ issuedBlocks.map block0SignMsg := by
  unfold verifyToken at hv; split at hv
  · rename_i hroot; simp only [Bool.and_eq_true] at hroot
    refine ⟨hroot.1.2, fun hmem => ?_⟩
    obtain ⟨b, hb, heq⟩ := List.mem_map.1 hmem; exact hfresh (block0SignMsg_injective heq ▸ hb)
  · simp at hv
theorem attenuation_monotone_from_block0 (S : PqSigScheme) (issuerPk : List UInt8)
    (rs : RevocationSet) (now : UInt64) (b0 : AuthorityBlock0) (sig0 : List UInt8)
    (pre ext : List AttenuationBlock) (va : VerifiedAuthority)
    (hv : verifyToken S issuerPk rs now ⟨b0, sig0, pre ++ ext⟩ = some va) :
    ∃ vaPre, verifyToken S issuerPk rs now ⟨b0, sig0, pre⟩ = some vaPre ∧
      va.subject = b0.subject ∧ subMask va.rights vaPre.rights = true ∧
      va.expiresAt ≤ vaPre.expiresAt ∧ subMask va.rights b0.rights = true ∧ va.expiresAt ≤ b0.expiresAt := by
  unfold verifyToken at hv; split at hv
  · rename_i hroot
    cases hfold : (pre ++ ext).foldlM (verifyHopStep S rs)
        ⟨b0.holderPk, rootLineage b0, b0.rights, b0.expiresAt⟩ with
    | none => simp [hfold] at hv
    | some st =>
      simp only [hfold] at hv; split at hv
      · rename_i hnow; cases Option.some.inj hv; simp only [decide_eq_true_eq] at hnow
        obtain ⟨stPre, hpre, hext⟩ := (foldlM_append_some _ _ _ _ _).1 hfold
        obtain ⟨_, hsubPre, hexpPre, _⟩ := verifyHops_facts S rs pre _ _ hpre
        obtain ⟨_, hsubExt, hexpExt, _⟩ := verifyHops_facts S rs ext _ _ hext
        refine ⟨⟨b0.subject, stPre.rights, stPre.expiresAt, b0.attrMerkleRoot, stPre.lineage, stPre.holderPk⟩,
          ?_, rfl, hsubExt, hexpExt, subMask_trans hsubExt hsubPre, Nat.le_trans hexpExt hexpPre⟩
        unfold verifyToken; dsimp only at hroot ⊢
        have hnp : now ≤ stPre.expiresAt := Nat.le_trans hnow hexpExt
        simp only [hroot, ↓reduceIte, hpre, decide_eq_true hnp]
      · simp at hv
  · simp at hv
theorem revoke_ancestor_kills_cone (S : PqSigScheme) (issuerPk : List UInt8)
    (raw : List Nat) (now : UInt64) (tok : HolderToken) (j : Nat) (hj : j ≤ tok.hops.length)
    (hrev : chainId tok.block0 tok.hops j ∈ raw) :
    verifyToken S issuerPk (RevocationSet.ofList raw) now tok = none := by
  cases hv : verifyToken S issuerPk (RevocationSet.ofList raw) now tok with
  | none => rfl
  | some va =>
    exfalso; unfold verifyToken at hv; split at hv
    · rename_i hroot; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hroot
      cases hfold : tok.hops.foldlM (verifyHopStep S (RevocationSet.ofList raw))
          ⟨tok.block0.holderPk, rootLineage tok.block0, tok.block0.rights, tok.block0.expiresAt⟩ with
      | none => simp [hfold] at hv
      | some st =>
        have hfalse := (verifyHops_facts S (RevocationSet.ofList raw) tok.hops _ _ hfold).2.2.2 hroot.2 j hj
        have htrue := (RevocationSet.contains_ofList_iff raw _).2 hrev
        unfold chainId lineageOf at htrue; rw [hfalse] at htrue; cases htrue
    · simp at hv

/-! ## §6. Constructive Security-Bug `#tooth` Falsifiers (`CAP-01`, `CAP-10`, `CAP-12`) -/
private def toyPqScheme : PqSigScheme where
  SecKey := List UInt8; pkOf := fun sk => 0x50 :: sk; sign := fun sk msg => 0x53 :: (encodeField sk ++ msg)
  verify := fun pk msg sig => match pk with | 0x50 :: sk => sig == (0x53 :: (encodeField sk ++ msg)) | _ => false
  verify_sign := fun _ _ => by simp
def legacyFirstAcctScan (tok : HolderToken) : Option (List UInt8) :=
  if !tok.block0.subject.isEmpty then some tok.block0.subject
  else tok.hops.findSome? fun h => if h.caveatTag.take 5 == strBytes "acct=" then some (h.caveatTag.drop 5) else none
def toothIssuer : IssuerSecret toyPqScheme := ⟨strBytes "issuer-secret-key"⟩
def toothHolderSk : List UInt8 := strBytes "alice-holder-key"
def toothEmptyRoot : List UInt8 := List.replicate 32 0xAA
def toothNonce : List UInt8 := List.replicate 32 0xBB
theorem cap01_tooth_forged_block0_rejected :
    let tok := issueRootToken toyPqScheme toothIssuer (strBytes "alice") (toyPqScheme.pkOf toothHolderSk) toothEmptyRoot toothNonce 0x03 1000
    (verifyToken toyPqScheme (toyPqScheme.pkOf toothIssuer.sk) RevocationSet.empty 500 tok).isSome = true ∧
    verifyToken toyPqScheme (toyPqScheme.pkOf toothIssuer.sk) RevocationSet.empty 500 { tok with block0 := { tok.block0 with subject := strBytes "admin" } } = none ∧
    verifyToken toyPqScheme (toyPqScheme.pkOf toothIssuer.sk) RevocationSet.empty 500 { tok with block0 := { tok.block0 with rights := 0xFF } } = none := by
  refine ⟨by simp [verifyToken, issueRootToken, toyPqScheme, RevocationSet.empty, RevocationSet.contains, bsearch, bsearchAux], ?_, ?_⟩
  · simp [verifyToken, issueRootToken, toyPqScheme]; intro h; exact absurd (block0SignMsg_injective h) (by decide)
  · simp [verifyToken, issueRootToken, toyPqScheme]; intro h; exact absurd (block0SignMsg_injective h) (by decide)
theorem cap10_tooth_unsorted_bsearch_miss_killed :
    bsearch #[30, 10, 20] 30 = false ∧ isStrictlySorted [30, 10, 20] = false ∧
    (RevocationSet.ofList [30, 10, 20]).contains 30 = true ∧
    (RevocationSet.ofList [30, 10, 20]).keys = (RevocationSet.ofList [10, 20, 30]).keys := by decide
theorem cap12_tooth_holder_appended_acct_admin_killed (anySig : List UInt8) :
    let ipk := toyPqScheme.pkOf toothIssuer.sk; let hpk := toyPqScheme.pkOf toothHolderSk
    let tok := issueRootToken toyPqScheme toothIssuer (strBytes "alice") hpk toothEmptyRoot toothNonce 0x03 1000
    let spoofHop : AttenuationBlock := ⟨0x01, 900, hpk, strBytes "acct=admin", anySig⟩
    legacyFirstAcctScan ⟨{ tok.block0 with subject := [] }, tok.block0Sig, [spoofHop]⟩ = some (strBytes "admin") ∧
    extractSubject { tok with hops := [spoofHop] } = strBytes "alice" ∧
    verifyToken toyPqScheme ipk RevocationSet.empty 500 { tok with hops := [⟨0x07, 900, hpk, strBytes "acct=admin", anySig⟩] } = none ∧
    verifyToken toyPqScheme ipk RevocationSet.empty 500 { tok with hops := [⟨0x01, 2000, hpk, strBytes "acct=admin", anySig⟩] } = none := by
  have h73 : (7 : UInt64) &&& 3 ≠ 7 := by decide
  have h21 : ¬ ((2000 : UInt64) ≤ 1000) := by decide
  refine ⟨by simp [legacyFirstAcctScan, strBytes], rfl, ?_, ?_⟩
  · simp [verifyToken, verifyHopStep, subMask, issueRootToken, toyPqScheme, RevocationSet.empty, RevocationSet.contains, bsearch, bsearchAux, h73]
  · simp [verifyToken, verifyHopStep, subMask, issueRootToken, toyPqScheme, RevocationSet.empty, RevocationSet.contains, bsearch, bsearchAux, h21]

/-! ## §7. Lean-Authored Conformance Vector Emitter & `#guard_msgs` Axiom Audit -/
private def hexBytes (bs : List UInt8) : String :=
  let d := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  String.join (bs.map fun b => String.ofList [d[(b.toNat / 16) % 16]!, d[b.toNat % 16]!])
def emitPqBiscuitConformance (path : System.FilePath) : IO Unit := do
  let iSeed := strBytes "MINIDREGG-D8-ISSUER-SEED-32BYTES"; let h0Seed := strBytes "MINIDREGG-D8-HOLDER0-SEED-32BYTE"
  let h1Seed := strBytes "MINIDREGG-D8-HOLDER1-SEED-32BYTE"; let h2Seed := strBytes "MINIDREGG-D8-HOLDER2-SEED-32BYTE"
  let iPk := wotsCshake256.pkOf iSeed; let h0Pk := wotsCshake256.pkOf h0Seed
  let h1Pk := wotsCshake256.pkOf h1Seed; let h2Pk := wotsCshake256.pkOf h2Seed
  let salts := (List.range 4).map fun i => cshake32 (strBytes "MINIDREGG.D8.TEST_SALT") [UInt8.ofNat i]
  let attrs := [(strBytes "acct", strBytes "alice", salts[0]!), (strBytes "role", strBytes "researcher", salts[1]!),
                (strBytes "clearance", strBytes "L3", salts[2]!), (strBytes "region", strBytes "us-west", salts[3]!)]
  let leaves := (List.range 4).map fun i => match attrs[i]? with | some (k, v, s) => attrLeafCommit i k v s | none => attrEmptyLeaf
  let attrRoot := merkleRootAux 2 leaves; let nonce := cshake32 (strBytes "MINIDREGG.D8.TEST_NONCE") [42]
  let tok0 := issueRootToken wotsCshake256 ⟨iSeed⟩ (strBytes "alice") h0Pk attrRoot nonce 0x0F 2000
  let tok1 := attenuateToken wotsCshake256 tok0 h0Seed 0x07 1500 h1Pk (strBytes "acct=admin")
  let tok2 := attenuateToken wotsCshake256 tok1 h1Seed 0x03 1200 h2Pk (strBytes "scope=read_doc")
  let okPres := (verifyPresentation wotsCshake256 iPk RevocationSet.empty 1000 tok2 (buildSelectiveOpenings 2 attrs [1, 3])).isSome
  let cid0 := chainId tok2.block0 tok2.hops 0; let cid1 := chainId tok2.block0 tok2.hops 1; let cid2 := chainId tok2.block0 tok2.hops 2
  let rsU := RevocationSet.ofList [cid2, cid0, cid1]; let rsS := RevocationSet.ofList [cid0, cid1, cid2]
  let jb (b : Bool) := if b then "true" else "false"
  let kv (k v : String) := s!"\"{k}\": \"{v}\""
  let fields : List String := [
    kv "schema" "minidregg.pq_biscuit_conformance.v1", kv "issuer_seed_hex" (hexBytes iSeed),
    kv "holder0_seed_hex" (hexBytes h0Seed), kv "holder1_seed_hex" (hexBytes h1Seed), kv "holder2_seed_hex" (hexBytes h2Seed),
    kv "issuer_pk_hex" (hexBytes iPk), kv "holder0_pk_hex" (hexBytes h0Pk), kv "holder1_pk_hex" (hexBytes h1Pk),
    kv "holder2_pk_hex" (hexBytes h2Pk), kv "nonce_hex" (hexBytes nonce),
    s!"\"salts_hex\": [\"{hexBytes salts[0]!}\", \"{hexBytes salts[1]!}\", \"{hexBytes salts[2]!}\", \"{hexBytes salts[3]!}\"]",
    kv "attr_merkle_root_hex" (hexBytes attrRoot), kv "block0_sig_hex" (hexBytes tok2.block0Sig),
    kv "hop1_sig_hex" (hexBytes (tok2.hops.getD 0 ⟨0,0,[],[],[]⟩).sigBytes),
    kv "hop2_sig_hex" (hexBytes (tok2.hops.getD 1 ⟨0,0,[],[],[]⟩).sigBytes),
    kv "root_lineage_hex" (hexBytes (rootLineage tok2.block0)),
    kv "hop1_lineage_hex" (hexBytes (lineageOf tok2.block0 (tok2.hops.take 1))),
    kv "tail_lineage_hex" (hexBytes (lineageOf tok2.block0 tok2.hops)),
    kv "chain_id0_hex" (hexBytes (be 32 cid0)), kv "chain_id1_hex" (hexBytes (be 32 cid1)),
    kv "chain_id2_hex" (hexBytes (be 32 cid2)), kv "revocation_root_hex" (hexBytes rsU.root),
    s!"\"presentation_valid\": {jb okPres}", s!"\"revocation_root_order_independent\": {jb (rsU.root == rsS.root)}",
    s!"\"ancestor_revocation_kills_descendant\": {jb (verifyToken wotsCshake256 iPk (RevocationSet.ofList [cid1]) 1000 tok2).isNone}",
    kv "extracted_subject" "alice", "\"disclosed_indices\": [1, 3]"
  ]
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path ("{\n  " ++ String.intercalate ",\n  " fields ++ "\n}\n")

#eval emitPqBiscuitConformance "prover/testdata/pq_biscuit_conformance.json"
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.wotsVerify_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wotsVerify_sign
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.RevocationSet.contains_ofList_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RevocationSet.contains_ofList_iff
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.RevocationSet.ofList_order_independent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RevocationSet.ofList_order_independent
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.verifyMerkleOpening_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyMerkleOpening_complete
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.merkleFold_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merkleFold_binds
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.unrevealed_attr_view_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unrevealed_attr_view_independent
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.unrevealed_salt_offline_guess_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unrevealed_salt_offline_guess_bound
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.holder_attenuate_needs_no_issuer_secret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms holder_attenuate_needs_no_issuer_secret
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.block0_unforgeable_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms block0_unforgeable_reduction
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.attenuation_monotone_from_block0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attenuation_monotone_from_block0
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.revoke_ancestor_kills_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms revoke_ancestor_kills_cone
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.cap01_tooth_forged_block0_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cap01_tooth_forged_block0_rejected
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.cap10_tooth_unsorted_bsearch_miss_killed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cap10_tooth_unsorted_bsearch_miss_killed
/-- info: 'Minidregg.Theory.PqSelectiveBiscuit.cap12_tooth_holder_appended_acct_admin_killed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cap12_tooth_holder_appended_acct_admin_killed

end Minidregg.Theory.PqSelectiveBiscuit
