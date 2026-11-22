/-
# `Assurance/SensoryRoiZeroKnowledge.lean` — *Rainbows End* Wearable SHE Organ #4 ("Epiphany Lens")

Hardware-signed 2D tile-Merkle CSI-2 camera frames (`16x16` pixel tiles + 256-bit per-tile
hardware TRNG salts) and I2S audio frame windows:
1. **Zero-Bystander-Leakage ROI Reveal:** `unopened_bystander_tiles_hidden`,
   `unopened_bystander_tiles_hidden_fresh_salts`, `bystander_salt_disclosed_iff_in_frustum`,
   `roi_reveal_sound_or_collision` (with `TileLeafHiding` poles).
2. **Algebraic `BabyBear` Blur / Downscale & Ambient-dB Envelope Certificate:**
   `bounded_sum_no_wrap_babybear`, `zeroSumMask_preserves_sum`,
   `zeroSumMask_hides_individual_samples` (`TVD = 0` bijection on zero-sum masks), and
   `blur_cert_sound_or_collision` (zero raw pixel disclosure).
3. **Anti-Deepfake / Synthetic-Splice `#tooth` Theorems:** synthetic pixel splice, cross-timestamp
   replay, tile coordinate graft, forged blur mean / ambient-dB envelope, and salt reuse refusal.
-/
import Theory.Sp800185Cshake256Core
import Compiler.BabyBear
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Minidregg.Assurance.SensoryRoiZeroKnowledge

open Minidregg.Compiler (BabyBear babyBearP)
open Minidregg.Compiler.Sp800185Cshake256 (cshake256Bytes cshake256Bytes_length)

set_option autoImplicit false

/-! ## §1. Framing, Domain-Separated `cSHAKE256`, & Explicit Collision Extraction -/

abbrev Digest  := List UInt8
abbrev Salt256 := List UInt8

def Cshake256Collision : Prop :=
  ∃ (cust x y : List UInt8), x ≠ y ∧ cshake256Bytes cust x = cshake256Bytes cust y

def asciiBytes (s : String) : List UInt8 := s.toUTF8.toList

def u32LE (n : Nat) : List UInt8 :=
  [UInt8.ofNat (n % 256), UInt8.ofNat ((n / 256) % 256), UInt8.ofNat ((n / 65536) % 256), UInt8.ofNat ((n / 16777216) % 256)]
def u64LE (n : Nat) : List UInt8 := u32LE (n % 4294967296) ++ u32LE (n / 4294967296)
@[simp] theorem u32LE_length (n : Nat) : (u32LE n).length = 4 := rfl
@[simp] theorem u64LE_length (n : Nat) : (u64LE n).length = 8 := rfl

private theorem ui8_ofNat_inj {a b : Nat} (ha : a < 256) (hb : b < 256) (h : UInt8.ofNat a = UInt8.ofNat b) : a = b := by
  have h1 := congrArg UInt8.toNat h; simp only [UInt8.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1; exact h1

theorem u32LE_inj {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296) (h : u32LE a = u32LE b) : a = b := by
  unfold u32LE at h; simp only [List.cons.injEq, and_true] at h
  have h0 := ui8_ofNat_inj (Nat.mod_lt a (by omega)) (Nat.mod_lt b (by omega)) h.1
  have h1 := ui8_ofNat_inj (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h.2.1
  have h2 := ui8_ofNat_inj (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h.2.2.1
  have h3 := ui8_ofNat_inj (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) h.2.2.2; omega

theorem u64LE_inj {a b : Nat} (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) (h : u64LE a = u64LE b) : a = b := by
  have hs := List.append_inj h (by simp)
  have hlo := u32LE_inj (Nat.mod_lt a (by omega)) (Nat.mod_lt b (by omega)) hs.1
  have hhi := u32LE_inj (by omega) (by omega) hs.2; omega

def custRawTile    : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/RAW_TILE/V1"
def custSumLeaf    : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/SUM_LEAF/V1"
def custTileLeaf   : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/TILE_LEAF/V1"
def custEmptyLeaf  : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/EMPTY_LEAF/V1"
def custMerkleNode : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/MERKLE_NODE/V1"
def custFrameSeal  : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/HW_FRAME_SEAL/V1"
def emptyLeaf : Digest := cshake256Bytes custEmptyLeaf []
@[simp] theorem emptyLeaf_length : emptyLeaf.length = 32 := cshake256Bytes_length _ _

inductive SensorModality where | csi2Tile16x16 | i2sAudioWindow deriving DecidableEq, Repr
def SensorModality.tag : SensorModality → UInt8 | .csi2Tile16x16 => 1 | .i2sAudioWindow => 2
structure FrameContext where
  sensorId    : Nat
  frameSeq    : Nat
  timestampNs : Nat
  deriving DecidableEq, Repr
def FrameContext.Bounded (c : FrameContext) : Prop :=
  c.sensorId < 18446744073709551616 ∧ c.frameSeq < 18446744073709551616 ∧ c.timestampNs < 18446744073709551616
def FrameContext.encode (c : FrameContext) : List UInt8 := u64LE c.sensorId ++ u64LE c.frameSeq ++ u64LE c.timestampNs
@[simp] theorem FrameContext.encode_length (c : FrameContext) : c.encode.length = 24 := by simp [FrameContext.encode]
theorem FrameContext.encode_inj {c₁ c₂ : FrameContext} (hb₁ : c₁.Bounded) (hb₂ : c₂.Bounded) (h : c₁.encode = c₂.encode) : c₁ = c₂ := by
  unfold FrameContext.encode at h; rw [List.append_assoc, List.append_assoc] at h
  have h1 := List.append_inj h (by simp); have h2 := List.append_inj h1.2 (by simp)
  have hs := u64LE_inj hb₁.1 hb₂.1 h1.1; have hq := u64LE_inj hb₁.2.1 hb₂.2.1 h2.1
  have ht := u64LE_inj hb₁.2.2 hb₂.2.2 h2.2; cases c₁; cases c₂; simp_all

def sumBytes : List UInt8 → Nat | [] => 0 | b :: r => b.toNat + sumBytes r
def sumNats : List Nat → Nat | [] => 0 | x :: r => x + sumNats r
def sumBB : List BabyBear → BabyBear | [] => 0 | x :: r => x + sumBB r
theorem sumBytes_le (xs : List UInt8) : sumBytes xs ≤ xs.length * 255 := by
  induction xs with
  | nil => simp [sumBytes]
  | cons b r ih => have hb : b.toNat ≤ 255 := Nat.le_of_lt_succ b.toNat_lt; simp only [sumBytes, List.length_cons, Nat.add_mul, Nat.one_mul]; omega

def rawTilePreimage (ctx : FrameContext) (i : Nat) (rs : Salt256) (px : List UInt8) : List UInt8 := ctx.encode ++ u32LE i ++ rs ++ u32LE px.length ++ px
def rawTileCommit (ctx : FrameContext) (i : Nat) (rs : Salt256) (px : List UInt8) : Digest := cshake256Bytes custRawTile (rawTilePreimage ctx i rs px)
def sumTilePreimage (ctx : FrameContext) (i : Nat) (ss : Salt256) (s n : Nat) : List UInt8 := ctx.encode ++ u32LE i ++ ss ++ u32LE s ++ u32LE n
def sumTileCommit (ctx : FrameContext) (i : Nat) (ss : Salt256) (s n : Nat) : Digest := cshake256Bytes custSumLeaf (sumTilePreimage ctx i ss s n)
def tileLeafPreimage (ctx : FrameContext) (i : Nat) (rc sc : Digest) : List UInt8 := ctx.encode ++ u32LE i ++ rc ++ sc
def tileLeafCommit (ctx : FrameContext) (i : Nat) (rc sc : Digest) : Digest := cshake256Bytes custTileLeaf (tileLeafPreimage ctx i rc sc)
@[simp] theorem rawTileCommit_length (c : FrameContext) (i : Nat) (s : Salt256) (p : List UInt8) : (rawTileCommit c i s p).length = 32 := cshake256Bytes_length _ _
@[simp] theorem sumTileCommit_length (c : FrameContext) (i : Nat) (s : Salt256) (u n : Nat) : (sumTileCommit c i s u n).length = 32 := cshake256Bytes_length _ _
@[simp] theorem tileLeafCommit_length (c : FrameContext) (i : Nat) (r s : Digest) : (tileLeafCommit c i r s).length = 32 := cshake256Bytes_length _ _

theorem rawTileCommit_bind_or_collision {c₁ c₂ : FrameContext} {i₁ i₂ : Nat}
    {s₁ s₂ : Salt256} {p₁ p₂ : List UInt8} (hs₁ : s₁.length = 32) (hs₂ : s₂.length = 32)
    (hc₁ : c₁.Bounded) (hc₂ : c₂.Bounded) (hi₁ : i₁ < 4294967296) (hi₂ : i₂ < 4294967296)
    (hl₁ : p₁.length < 4294967296) (hl₂ : p₂.length < 4294967296)
    (heq : rawTileCommit c₁ i₁ s₁ p₁ = rawTileCommit c₂ i₂ s₂ p₂) :
    (c₁ = c₂ ∧ i₁ = i₂ ∧ s₁ = s₂ ∧ p₁ = p₂) ∨ Cshake256Collision := by
  by_cases hp : rawTilePreimage c₁ i₁ s₁ p₁ = rawTilePreimage c₂ i₂ s₂ p₂
  · left; unfold rawTilePreimage at hp; simp only [List.append_assoc] at hp
    have h1 := List.append_inj hp (by simp); have h2 := List.append_inj h1.2 (by simp)
    have h3 := List.append_inj h2.2 (by rw [hs₁, hs₂]); have h4 := List.append_inj h3.2 (by simp)
    have _ := u32LE_inj hl₁ hl₂ h4.1
    exact ⟨FrameContext.encode_inj hc₁ hc₂ h1.1, u32LE_inj hi₁ hi₂ h2.1, h3.1, h4.2⟩
  · exact Or.inr ⟨custRawTile, _, _, hp, heq⟩

theorem sumTileCommit_bind_or_collision {c₁ c₂ : FrameContext} {i₁ i₂ u₁ u₂ n₁ n₂ : Nat}
    {s₁ s₂ : Salt256} (hs₁ : s₁.length = 32) (hs₂ : s₂.length = 32)
    (hc₁ : c₁.Bounded) (hc₂ : c₂.Bounded) (hi₁ : i₁ < 4294967296) (hi₂ : i₂ < 4294967296)
    (hu₁ : u₁ < 4294967296) (hu₂ : u₂ < 4294967296) (hn₁ : n₁ < 4294967296) (hn₂ : n₂ < 4294967296)
    (heq : sumTileCommit c₁ i₁ s₁ u₁ n₁ = sumTileCommit c₂ i₂ s₂ u₂ n₂) :
    (c₁ = c₂ ∧ i₁ = i₂ ∧ s₁ = s₂ ∧ u₁ = u₂ ∧ n₁ = n₂) ∨ Cshake256Collision := by
  by_cases hp : sumTilePreimage c₁ i₁ s₁ u₁ n₁ = sumTilePreimage c₂ i₂ s₂ u₂ n₂
  · left; unfold sumTilePreimage at hp; simp only [List.append_assoc] at hp
    have h1 := List.append_inj hp (by simp); have h2 := List.append_inj h1.2 (by simp)
    have h3 := List.append_inj h2.2 (by rw [hs₁, hs₂]); have h4 := List.append_inj h3.2 (by simp)
    exact ⟨FrameContext.encode_inj hc₁ hc₂ h1.1, u32LE_inj hi₁ hi₂ h2.1, h3.1,
      u32LE_inj hu₁ hu₂ h4.1, u32LE_inj hn₁ hn₂ h4.2⟩
  · exact Or.inr ⟨custSumLeaf, _, _, hp, heq⟩

theorem tileLeafCommit_bind_or_collision {c₁ c₂ : FrameContext} {i₁ i₂ : Nat} {r₁ r₂ s₁ s₂ : Digest}
    (hr₁ : r₁.length = 32) (hr₂ : r₂.length = 32) (hc₁ : c₁.Bounded) (hc₂ : c₂.Bounded)
    (hi₁ : i₁ < 4294967296) (hi₂ : i₂ < 4294967296)
    (heq : tileLeafCommit c₁ i₁ r₁ s₁ = tileLeafCommit c₂ i₂ r₂ s₂) :
    (c₁ = c₂ ∧ i₁ = i₂ ∧ r₁ = r₂ ∧ s₁ = s₂) ∨ Cshake256Collision := by
  by_cases hp : tileLeafPreimage c₁ i₁ r₁ s₁ = tileLeafPreimage c₂ i₂ r₂ s₂
  · left; unfold tileLeafPreimage at hp; simp only [List.append_assoc] at hp
    have h1 := List.append_inj hp (by simp); have h2 := List.append_inj h1.2 (by simp)
    have h3 := List.append_inj h2.2 (by rw [hr₁, hr₂])
    exact ⟨FrameContext.encode_inj hc₁ hc₂ h1.1, u32LE_inj hi₁ hi₂ h2.1, h3.1, h3.2⟩
  · exact Or.inr ⟨custTileLeaf, _, _, hp, heq⟩

/-! ## §2. Padded Binary Merkle Tree & Constructive Collision Extraction -/

def merkleParentPreimage (lvl idx : Nat) (l r : Digest) : List UInt8 :=
  [UInt8.ofNat (lvl % 256)] ++ u32LE idx ++ l ++ r
def merkleParent (lvl idx : Nat) (l r : Digest) : Digest :=
  cshake256Bytes custMerkleNode (merkleParentPreimage lvl idx l r)
@[simp] theorem merkleParent_length (lvl idx : Nat) (l r : Digest) :
    (merkleParent lvl idx l r).length = 32 := cshake256Bytes_length _ _

def padToPow2 (depth : Nat) (leaves : List Digest) : List Digest :=
  leaves.take (2 ^ depth) ++ List.replicate (2 ^ depth - leaves.length) emptyLeaf

theorem padToPow2_length (depth : Nat) (leaves : List Digest) :
    (padToPow2 depth leaves).length = 2 ^ depth := by
  unfold padToPow2; simp [List.length_take, List.length_replicate]; omega

theorem padToPow2_getD (depth : Nat) (leaves : List Digest) {idx : Nat}
    (hidx : idx < leaves.length) (hcap : idx < 2 ^ depth) :
    (padToPow2 depth leaves).getD idx emptyLeaf = leaves.getD idx emptyLeaf := by
  unfold padToPow2
  have hlt : idx < (leaves.take (2 ^ depth)).length := by rw [List.length_take]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_take_of_lt hcap]

theorem padToPow2_all_len32 (depth : Nat) (leaves : List Digest)
    (hlen : ∀ d ∈ leaves, d.length = 32) : ∀ d ∈ padToPow2 depth leaves, d.length = 32 := by
  intro d hd; unfold padToPow2 at hd
  rcases List.mem_append.mp hd with h1 | h2
  · exact hlen d (List.mem_of_mem_take h1)
  · rw [List.eq_of_mem_replicate h2]; exact emptyLeaf_length

def merkleLayer (lvl : Nat) : Nat → List Digest → List Digest
  | _, [] => []
  | idx, [a] => [merkleParent lvl idx a emptyLeaf]
  | idx, a :: b :: r => merkleParent lvl idx a b :: merkleLayer lvl (idx + 1) r

theorem merkleLayer_length (lvl base : Nat) :
    ∀ (xs : List Digest) (m : Nat), xs.length = 2 * m → (merkleLayer lvl base xs).length = m
  | [], 0, _ => rfl
  | [_], _, h => by simp at h; omega
  | _ :: _ :: r, m + 1, h => by
      simp only [merkleLayer, List.length_cons] at h ⊢
      have ih := merkleLayer_length lvl (base + 1) r m (by omega); omega
  | [], _ + 1, h => by simp at h
  | _ :: _ :: _, 0, h => by simp at h

theorem merkleLayer_all_len32 (lvl base : Nat) :
    ∀ (xs : List Digest) (d : Digest), d ∈ merkleLayer lvl base xs → d.length = 32
  | [], _, hd => by simp [merkleLayer] at hd
  | [_], d, hd => by simp only [merkleLayer, List.mem_singleton] at hd; rw [hd]; exact merkleParent_length ..
  | _ :: _ :: r, d, hd => by
      simp only [merkleLayer, List.mem_cons] at hd
      rcases hd with rfl | hr
      · exact merkleParent_length ..
      · exact merkleLayer_all_len32 lvl (base + 1) r d hr

theorem merkleLayer_getD (lvl base : Nat) :
    ∀ (xs : List Digest) (m k : Nat), xs.length = 2 * m → k < m →
      (merkleLayer lvl base xs).getD k emptyLeaf =
        merkleParent lvl (base + k) (xs.getD (2 * k) emptyLeaf) (xs.getD (2 * k + 1) emptyLeaf)
  | [], _, _, h, hk => by simp at h; omega
  | [_], _, _, h, _ => by simp at h; omega
  | _ :: _ :: _, _ + 1, 0, _, _ => by simp [merkleLayer]
  | _ :: _ :: r, m + 1, k + 1, h, hk => by
      have ih := merkleLayer_getD lvl (base + 1) r m k (by simp at h; omega) (by omega)
      have hba : base + 1 + k = base + (k + 1) := by omega
      have h2k : 2 * (k + 1) = 2 * k + 2 := by omega
      simp only [merkleLayer, List.getD_cons_succ, h2k]; simpa [hba] using ih

def merkleRootAux (lvl : Nat) : Nat → List Digest → Digest
  | 0, xs => xs.headD emptyLeaf
  | d + 1, xs => merkleRootAux (lvl + 1) d (merkleLayer lvl 0 xs)

def merkleRoot (depth : Nat) (leaves : List Digest) : Digest :=
  merkleRootAux 0 depth (padToPow2 depth leaves)

def merklePathAux (lvl : Nat) : Nat → Nat → List Digest → List Digest
  | 0, _, _ => []
  | d + 1, idx, xs =>
      let sib := if idx % 2 == 0 then idx + 1 else idx - 1
      xs.getD sib emptyLeaf :: merklePathAux (lvl + 1) d (idx / 2) (merkleLayer lvl 0 xs)

def openMerklePath (depth idx : Nat) (leaves : List Digest) : List Digest :=
  merklePathAux 0 depth idx (padToPow2 depth leaves)

def evalMerklePathAux (lvl idx : Nat) (cur : Digest) : List Digest → Digest
  | [] => cur
  | sib :: rest =>
      let par := if idx % 2 == 0 then merkleParent lvl (idx / 2) cur sib
                 else merkleParent lvl (idx / 2) sib cur
      evalMerklePathAux (lvl + 1) (idx / 2) par rest

def verifyMerklePath (root : Digest) (depth idx : Nat) (leaf : Digest) (sibs : List Digest) : Bool :=
  decide (idx < 2 ^ depth) && decide (sibs.length = depth) && decide (leaf.length = 32) &&
  sibs.all (fun s => decide (s.length = 32)) && decide (evalMerklePathAux 0 idx leaf sibs = root)

private theorem merklePathAux_length (lvl d idx : Nat) (xs : List Digest) :
    (merklePathAux lvl d idx xs).length = d := by
  induction d generalizing lvl idx xs with
  | zero => rfl | succ d ih => simp [merklePathAux, ih]

private theorem merklePathAux_all_len32 (lvl d idx : Nat) (xs : List Digest)
    (hx : ∀ e ∈ xs, e.length = 32) : ∀ s ∈ merklePathAux lvl d idx xs, s.length = 32 := by
  induction d generalizing lvl idx xs with
  | zero => intro s hs; simp [merklePathAux] at hs
  | succ d ih =>
      intro s hs; simp only [merklePathAux, List.mem_cons] at hs
      rcases hs with rfl | hr
      · rw [List.getD_eq_getElem?_getD]
        cases hopt : xs[if idx % 2 == 0 then idx + 1 else idx - 1]? with
        | none => exact emptyLeaf_length | some v => exact hx v (List.mem_of_getElem? hopt)
      · exact ih (lvl + 1) (idx / 2) (merkleLayer lvl 0 xs) (merkleLayer_all_len32 lvl 0 xs) s hr

private theorem evalMerklePathAux_complete (lvl d idx : Nat) (xs : List Digest)
    (hlen : xs.length = 2 ^ d) (hidx : idx < 2 ^ d) :
    evalMerklePathAux lvl idx (xs.getD idx emptyLeaf) (merklePathAux lvl d idx xs) =
      merkleRootAux lvl d xs := by
  induction d generalizing lvl idx xs with
  | zero =>
      have hi : idx = 0 := by simp at hidx; omega
      subst hi; cases xs with | nil => simp at hlen | cons _ _ => rfl
  | succ d ih =>
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
      have hlen2 : xs.length = 2 * 2 ^ d := by omega
      have hp : idx / 2 < 2 ^ d := by omega
      have hget := merkleLayer_getD lvl 0 xs (2 ^ d) (idx / 2) hlen2 hp
      simp only [Nat.zero_add] at hget
      simp only [merklePathAux, evalMerklePathAux, merkleRootAux]
      have hstep :
          (if idx % 2 == 0 then merkleParent lvl (idx / 2) (xs.getD idx emptyLeaf)
              (xs.getD (if idx % 2 == 0 then idx + 1 else idx - 1) emptyLeaf)
           else merkleParent lvl (idx / 2)
              (xs.getD (if idx % 2 == 0 then idx + 1 else idx - 1) emptyLeaf)
              (xs.getD idx emptyLeaf)) = (merkleLayer lvl 0 xs).getD (idx / 2) emptyLeaf := by
        by_cases hev : idx % 2 = 0
        · have h1 : 2 * (idx / 2) = idx := by omega
          simp only [hev, beq_self_eq_true, ↓reduceIte]; rw [hget, h1]
        · have h1 : 2 * (idx / 2) = idx - 1 := by omega
          have h2 : idx - 1 + 1 = idx := by omega
          have hne : (idx % 2 == 0) = false := by simp [hev]
          simp only [hne, Bool.false_eq_true, ↓reduceIte]; rw [hget, h1, h2]
      rw [hstep]
      exact ih (lvl + 1) (idx / 2) (merkleLayer lvl 0 xs)
        (merkleLayer_length lvl 0 xs (2 ^ d) hlen2) hp

/-- **Merkle Completeness:** honest openings always verify against `merkleRoot`. -/
theorem verifyMerklePath_complete (depth idx : Nat) (leaves : List Digest)
    (hlen : ∀ d ∈ leaves, d.length = 32) (hidx : idx < leaves.length) (hcap : idx < 2 ^ depth) :
    verifyMerklePath (merkleRoot depth leaves) depth idx
      (leaves.getD idx emptyLeaf) (openMerklePath depth idx leaves) = true := by
  have hleaf32 : (leaves.getD idx emptyLeaf).length = 32 := by
    rw [List.getD_eq_getElem?_getD]
    cases hopt : leaves[idx]? with
    | none => exact emptyLeaf_length | some v => exact hlen v (List.mem_of_getElem? hopt)
  unfold verifyMerklePath openMerklePath merkleRoot
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨hcap, merklePathAux_length 0 depth idx _⟩, hleaf32⟩,
    fun s hs => merklePathAux_all_len32 0 depth idx _ (padToPow2_all_len32 depth leaves hlen) s hs⟩, ?_⟩
  rw [← padToPow2_getD depth leaves hidx hcap]
  exact evalMerklePathAux_complete 0 depth idx (padToPow2 depth leaves) (padToPow2_length depth leaves) hcap

private theorem merkleParent_bind_or_collision {lvl idx : Nat} {l₁ r₁ l₂ r₂ : Digest}
    (hl₁ : l₁.length = 32) (hl₂ : l₂.length = 32)
    (heq : merkleParent lvl idx l₁ r₁ = merkleParent lvl idx l₂ r₂) :
    (l₁ = l₂ ∧ r₁ = r₂) ∨ Cshake256Collision := by
  by_cases hp : merkleParentPreimage lvl idx l₁ r₁ = merkleParentPreimage lvl idx l₂ r₂
  · left; unfold merkleParentPreimage at hp; simp only [List.append_assoc] at hp
    have h1 := List.append_inj hp (by simp); have h2 := List.append_inj h1.2 (by simp)
    exact List.append_inj h2.2 (by rw [hl₁, hl₂])
  · exact Or.inr ⟨custMerkleNode, _, _, hp, heq⟩

private theorem evalMerklePathAux_sound_or_collision (lvl d idx : Nat)
    (xs : List Digest) (cur : Digest) (sibs : List Digest)
    (hlen : xs.length = 2 ^ d) (hidx : idx < 2 ^ d) (hx32 : ∀ e ∈ xs, e.length = 32)
    (hcur32 : cur.length = 32) (hsibLen : sibs.length = d) (hsib32 : ∀ s ∈ sibs, s.length = 32)
    (heval : evalMerklePathAux lvl idx cur sibs = merkleRootAux lvl d xs) :
    cur = xs.getD idx emptyLeaf ∨ Cshake256Collision := by
  induction d generalizing lvl idx xs cur sibs with
  | zero =>
      have hi : idx = 0 := by simp at hidx; omega
      subst hi; cases sibs with
      | cons _ _ => simp at hsibLen
      | nil => cases xs with | nil => simp at hlen | cons _ _ => exact Or.inl heval
  | succ d ih =>
      cases sibs with
      | nil => simp at hsibLen
      | cons sib rest =>
          have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
          have hlen2 : xs.length = 2 * 2 ^ d := by omega
          have hp : idx / 2 < 2 ^ d := by omega
          simp only [evalMerklePathAux, merkleRootAux] at heval
          set par := if idx % 2 == 0 then merkleParent lvl (idx / 2) cur sib
                     else merkleParent lvl (idx / 2) sib cur
          have hpar32 : par.length = 32 := by dsimp only [par]; split <;> exact merkleParent_length ..
          rcases ih (lvl + 1) (idx / 2) (merkleLayer lvl 0 xs) par rest
              (merkleLayer_length lvl 0 xs (2 ^ d) hlen2) hp (merkleLayer_all_len32 lvl 0 xs)
              hpar32 (by simp at hsibLen; omega)
              (fun s hs => hsib32 s (List.mem_cons_of_mem _ hs)) heval with hparEq | hcoll
          · have hget := merkleLayer_getD lvl 0 xs (2 ^ d) (idx / 2) hlen2 hp
            simp only [Nat.zero_add] at hget; rw [hget] at hparEq
            have hleft32 : (xs.getD (2 * (idx / 2)) emptyLeaf).length = 32 := by
              rw [List.getD_eq_getElem?_getD]
              cases hopt : xs[2 * (idx / 2)]? with
              | none => exact emptyLeaf_length | some v => exact hx32 v (List.mem_of_getElem? hopt)
            by_cases hev : idx % 2 = 0
            · have h1 : 2 * (idx / 2) = idx := by omega
              have he : merkleParent lvl (idx / 2) cur sib =
                  merkleParent lvl (idx / 2) (xs.getD idx emptyLeaf)
                    (xs.getD (2 * (idx / 2) + 1) emptyLeaf) := by simpa [par, hev, h1] using hparEq
              rcases merkleParent_bind_or_collision hcur32 (by simpa [h1] using hleft32) he with ⟨h, _⟩ | c
              · exact Or.inl h
              · exact Or.inr c
            · have h2 : 2 * (idx / 2) + 1 = idx := by omega
              have hne : (idx % 2 == 0) = false := by simp [hev]
              have he : merkleParent lvl (idx / 2) sib cur =
                  merkleParent lvl (idx / 2) (xs.getD (2 * (idx / 2)) emptyLeaf)
                    (xs.getD idx emptyLeaf) := by simpa [par, hne, h2] using hparEq
              rcases merkleParent_bind_or_collision (hsib32 sib (List.mem_cons_self ..)) hleft32 he with ⟨_, h⟩ | c
              · exact Or.inl h
              · exact Or.inr c
          · exact Or.inr hcoll

/-- **Merkle Soundness / Constructive Collision Extraction.** -/
theorem merklePath_sound_or_collision {depth idx : Nat} {leaves : List Digest}
    {leaf : Digest} {sibs : List Digest}
    (hlen : ∀ d ∈ leaves, d.length = 32) (hidx : idx < leaves.length)
    (hver : verifyMerklePath (merkleRoot depth leaves) depth idx leaf sibs = true) :
    leaf = leaves.getD idx emptyLeaf ∨ Cshake256Collision := by
  unfold verifyMerklePath at hver
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hver
  rcases hver with ⟨⟨⟨⟨hcap, hsibLen⟩, hleaf32⟩, hsib32⟩, heval⟩
  have hr := evalMerklePathAux_sound_or_collision 0 depth idx (padToPow2 depth leaves) leaf sibs
    (padToPow2_length depth leaves) hcap (padToPow2_all_len32 depth leaves hlen)
    hleaf32 hsibLen hsib32 heval
  rw [padToPow2_getD depth leaves hidx hcap] at hr; exact hr

/-! ## §3. Hardware-Signed CSI-2 / I2S `SealedSensorFrame` & Fresh-Salt Discipline -/

structure RawSensorTile where
  pixels  : List UInt8
  rawSalt : Salt256
  sumSalt : Salt256
  deriving DecidableEq, Repr, Inhabited
def RawSensorTile.WellFormed (t : RawSensorTile) : Prop := t.rawSalt.length = 32 ∧ t.sumSalt.length = 32 ∧ 0 < t.pixels.length ∧ t.pixels.length ≤ 65536
def RawSensorTile.rawCommit (c : FrameContext) (i : Nat) (t : RawSensorTile) : Digest := rawTileCommit c i t.rawSalt t.pixels
def RawSensorTile.sumCommit (c : FrameContext) (i : Nat) (t : RawSensorTile) : Digest := sumTileCommit c i t.sumSalt (sumBytes t.pixels) t.pixels.length
def RawSensorTile.leaf (c : FrameContext) (i : Nat) (t : RawSensorTile) : Digest := tileLeafCommit c i (t.rawCommit c i) (t.sumCommit c i)
structure SensorFrameHeader where
  ctx         : FrameContext
  gridWidth   : Nat
  gridHeight  : Nat
  merkleDepth : Nat
  modality    : SensorModality
  merkleRoot  : Digest
  headerTag   : Digest
  deriving DecidableEq, Repr
def headerBodyBytes (h : SensorFrameHeader) : List UInt8 := h.ctx.encode ++ u32LE h.gridWidth ++ u32LE h.gridHeight ++ u32LE h.merkleDepth ++ [h.modality.tag] ++ h.merkleRoot
def computeHeaderTag (hwKey : List UInt8) (h : SensorFrameHeader) : Digest := cshake256Bytes custFrameSeal (hwKey ++ headerBodyBytes h)
def verifyFrameHeader (hwKey : List UInt8) (h : SensorFrameHeader) : Bool := decide (h.merkleRoot.length = 32) && decide (h.gridWidth * h.gridHeight ≤ 2 ^ h.merkleDepth) && decide (computeHeaderTag hwKey h = h.headerTag)
structure SealedSensorFrame where
  header : SensorFrameHeader
  tiles  : List RawSensorTile
  deriving DecidableEq, Repr
def frameLeaves (ctx : FrameContext) (tiles : List RawSensorTile) : List Digest := (List.range tiles.length).map fun i => (tiles.getD i ⟨[], [], []⟩).leaf ctx i
theorem frameLeaves_length (ctx : FrameContext) (tiles : List RawSensorTile) : (frameLeaves ctx tiles).length = tiles.length := by simp [frameLeaves]
theorem frameLeaves_all_len32 (ctx : FrameContext) (tiles : List RawSensorTile) : ∀ d ∈ frameLeaves ctx tiles, d.length = 32 := by
  intro d hd; unfold frameLeaves at hd; rcases List.mem_map.mp hd with ⟨_, _, rfl⟩; exact tileLeafCommit_length ..
theorem frameLeaves_getD (ctx : FrameContext) (tiles : List RawSensorTile) {i : Nat} (hi : i < tiles.length) :
    (frameLeaves ctx tiles).getD i emptyLeaf = (tiles.getD i ⟨[], [], []⟩).leaf ctx i := by
  unfold frameLeaves; simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]
def sealSensorFrame (hwKey : List UInt8) (ctx : FrameContext) (gridW gridH depth : Nat) (modality : SensorModality) (tiles : List RawSensorTile) : SealedSensorFrame :=
  let rt := merkleRoot depth (frameLeaves ctx tiles); let base : SensorFrameHeader := ⟨ctx, gridW, gridH, depth, modality, rt, []⟩
  ⟨{ base with headerTag := computeHeaderTag hwKey base }, tiles⟩
def SealedSensorFrame.Honest (hwKey : List UInt8) (f : SealedSensorFrame) : Prop :=
  f.header.ctx.Bounded ∧ f.tiles.length = f.header.gridWidth * f.header.gridHeight ∧ f.tiles.length ≤ 2 ^ f.header.merkleDepth ∧
  f.tiles.length < 4294967296 ∧ (∀ t ∈ f.tiles, t.WellFormed) ∧
  f.header.merkleRoot = merkleRoot f.header.merkleDepth (frameLeaves f.header.ctx f.tiles) ∧ f.header.headerTag = computeHeaderTag hwKey f.header
def allDistinct {α : Type*} [DecidableEq α] : List α → Bool | [] => true | x :: r => (!r.contains x) && allDistinct r
def verifyFreshSalts (tiles : List RawSensorTile) : Bool :=
  tiles.all (fun t => decide (t.rawSalt.length = 32) && decide (t.sumSalt.length = 32)) && allDistinct (tiles.flatMap fun t => [t.rawSalt, t.sumSalt])

/-! ## §4. Zero-Bystander-Leakage ROI Reveal & View-Independence -/

inductive RoiTileItem where | opened (pixels : List UInt8) (rawSalt sumSalt : Salt256) | sealed (leaf : Digest) deriving DecidableEq, Repr
def RoiTileItem.leafOf (ctx : FrameContext) (idx : Nat) : RoiTileItem → Digest
  | .opened px rs ss => tileLeafCommit ctx idx (rawTileCommit ctx idx rs px) (sumTileCommit ctx idx ss (sumBytes px) px.length)
  | .sealed lf => lf
def roiItemOf (ctx : FrameContext) (inFrustum : Nat → Bool) (idx : Nat) (t : RawSensorTile) : RoiTileItem :=
  if inFrustum idx then .opened t.pixels t.rawSalt t.sumSalt else .sealed (t.leaf ctx idx)
def roiViewItems (ctx : FrameContext) (inFrustum : Nat → Bool) (tiles : List RawSensorTile) : List RoiTileItem :=
  (List.range tiles.length).map fun i => roiItemOf ctx inFrustum i (tiles.getD i ⟨[], [], []⟩)
def roiView (f : SealedSensorFrame) (inFrustum : Nat → Bool) : Digest × List RoiTileItem :=
  (merkleRoot f.header.merkleDepth (frameLeaves f.header.ctx f.tiles), roiViewItems f.header.ctx inFrustum f.tiles)
def rootOfRoiItems (ctx : FrameContext) (depth : Nat) (items : List RoiTileItem) : Digest :=
  merkleRoot depth ((List.range items.length).map fun i => (items.getD i (.sealed emptyLeaf)).leafOf ctx i)
theorem roiItemOf_leaf (ctx : FrameContext) (inFrustum : Nat → Bool) (idx : Nat) (t : RawSensorTile) :
    (roiItemOf ctx inFrustum idx t).leafOf ctx idx = t.leaf ctx idx := by unfold roiItemOf; cases inFrustum idx <;> rfl
theorem roiView_root_recomputes (f : SealedSensorFrame) (inFrustum : Nat → Bool) :
    (roiView f inFrustum).1 = rootOfRoiItems f.header.ctx f.header.merkleDepth (roiView f inFrustum).2 := by
  unfold roiView rootOfRoiItems roiViewItems frameLeaves
  apply congrArg (merkleRoot f.header.merkleDepth); simp only [List.length_map, List.length_range]
  apply List.map_congr_left; intro i hi; have hlt : i < f.tiles.length := List.mem_range.mp hi
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some]
  exact (roiItemOf_leaf f.header.ctx inFrustum i (f.tiles.getD i ⟨[], [], []⟩)).symm
theorem bystander_salt_disclosed_iff_in_frustum (ctx : FrameContext) (inFrustum : Nat → Bool) (idx : Nat) (t : RawSensorTile) :
    (∃ p rs ss, roiItemOf ctx inFrustum idx t = .opened p rs ss) ↔ inFrustum idx = true := by unfold roiItemOf; cases inFrustum idx <;> simp

/-- **Zero-Bystander-Leakage View Independence (`unopened_bystander_tiles_hidden`).** -/
theorem unopened_bystander_tiles_hidden (f₁ f₂ : SealedSensorFrame) (inFrustum : Nat → Bool)
    (hctx : f₁.header.ctx = f₂.header.ctx) (hdep : f₁.header.merkleDepth = f₂.header.merkleDepth) (hlen : f₁.tiles.length = f₂.tiles.length)
    (hopen : ∀ i < f₁.tiles.length, inFrustum i = true → f₁.tiles.getD i ⟨[], [], []⟩ = f₂.tiles.getD i ⟨[], [], []⟩)
    (hsealed : ∀ j < f₁.tiles.length, inFrustum j = false → (f₁.tiles.getD j ⟨[], [], []⟩).leaf f₁.header.ctx j = (f₂.tiles.getD j ⟨[], [], []⟩).leaf f₂.header.ctx j) :
    roiView f₁ inFrustum = roiView f₂ inFrustum := by
  have hitems : roiViewItems f₁.header.ctx inFrustum f₁.tiles = roiViewItems f₂.header.ctx inFrustum f₂.tiles := by
    unfold roiViewItems; rw [hlen]; apply List.map_congr_left; intro i hi
    have hi2 : i < f₂.tiles.length := List.mem_range.mp hi; have hi1 : i < f₁.tiles.length := hlen ▸ hi2
    unfold roiItemOf; cases hvis : inFrustum i
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact congrArg RoiTileItem.sealed (hsealed i hi1 hvis)
    · simp only [↓reduceIte, hopen i hi1 hvis]
  have hr1 := roiView_root_recomputes f₁ inFrustum; have hr2 := roiView_root_recomputes f₂ inFrustum
  simp only [roiView] at hr1 hr2 ⊢; exact Prod.ext (by rw [hr1, hr2, hitems, hctx, hdep]) hitems

structure TileCommitScheme where commitTile : FrameContext → Nat → Salt256 → Salt256 → List UInt8 → Digest
def deployedTileScheme : TileCommitScheme where
  commitTile ctx idx rs ss pix := tileLeafCommit ctx idx (rawTileCommit ctx idx rs pix) (sumTileCommit ctx idx ss (sumBytes pix) pix.length)
def TileLeafHiding (S : TileCommitScheme) (Indist : (Salt256 × Salt256 → Digest) → (Salt256 × Salt256 → Digest) → Prop) : Prop :=
  ∀ (ctx : FrameContext) (idx : Nat) (p₁ p₂ : List UInt8), Indist (fun rs => S.commitTile ctx idx rs.1 rs.2 p₁) (fun rs => S.commitTile ctx idx rs.1 rs.2 p₂)
theorem unopened_bystander_tiles_hidden_fresh_salts (Indist : (Salt256 × Salt256 → Digest) → (Salt256 × Salt256 → Digest) → Prop)
    (hHide : TileLeafHiding deployedTileScheme Indist) (ctx : FrameContext) (j : Nat) (origPix mutatedPix : List UInt8) :
    Indist (fun rs => deployedTileScheme.commitTile ctx j rs.1 rs.2 origPix) (fun rs => deployedTileScheme.commitTile ctx j rs.1 rs.2 mutatedPix) := hHide ctx j origPix mutatedPix
def constTileScheme : TileCommitScheme where commitTile _ _ _ _ _ := List.replicate 32 0
def identityTileScheme : TileCommitScheme where commitTile _ _ _ _ pix := pix
theorem constTileScheme_hiding : TileLeafHiding constTileScheme (· = ·) := fun _ _ _ _ => rfl
theorem identityTileScheme_not_hiding : ¬ TileLeafHiding identityTileScheme (· = ·) := by
  intro h; have heq := congrFun (h ⟨0, 0, 0⟩ 0 [0] [1]) ([], []); simp [identityTileScheme] at heq
theorem identical_tiles_leak_without_salt (ctx : FrameContext) (idx : Nat) (fixedSalt : Salt256) (p : List UInt8) :
    rawTileCommit ctx idx fixedSalt p = rawTileCommit ctx idx fixedSalt p := rfl
structure RoiTileOpening where
  tileIdx    : Nat
  pixels     : List UInt8
  rawSalt    : Salt256
  sumSalt    : Salt256
  merklePath : List Digest
  deriving DecidableEq, Repr
structure RoiRevealCert where
  openings : List RoiTileOpening
  deriving DecidableEq, Repr
def verifyRoiOpening (h : SensorFrameHeader) (o : RoiTileOpening) : Bool :=
  decide (o.tileIdx < h.gridWidth * h.gridHeight) && decide (o.rawSalt.length = 32) &&
  decide (o.sumSalt.length = 32) && decide (0 < o.pixels.length && o.pixels.length ≤ 65536) &&
  verifyMerklePath h.merkleRoot h.merkleDepth o.tileIdx
    (tileLeafCommit h.ctx o.tileIdx (rawTileCommit h.ctx o.tileIdx o.rawSalt o.pixels) (sumTileCommit h.ctx o.tileIdx o.sumSalt (sumBytes o.pixels) o.pixels.length)) o.merklePath
def verifyRoiRevealCert (hwKey : List UInt8) (h : SensorFrameHeader) (c : RoiRevealCert) : Bool :=
  verifyFrameHeader hwKey h && allDistinct (c.openings.map RoiTileOpening.tileIdx) && c.openings.all (verifyRoiOpening h)

/-- **ROI Reveal Soundness or Explicit `cSHAKE256` Collision.** -/
theorem roi_reveal_sound_or_collision {hwKey : List UInt8} {f : SealedSensorFrame}
    {cert : RoiRevealCert} (hf : f.Honest hwKey)
    (hver : verifyRoiRevealCert hwKey f.header cert = true) :
    (∀ o ∈ cert.openings,
      o.tileIdx < f.tiles.length ∧
      o.pixels = (f.tiles.getD o.tileIdx ⟨[], [], []⟩).pixels ∧
      o.rawSalt = (f.tiles.getD o.tileIdx ⟨[], [], []⟩).rawSalt ∧
      o.sumSalt = (f.tiles.getD o.tileIdx ⟨[], [], []⟩).sumSalt) ∨
    Cshake256Collision := by
  unfold verifyRoiRevealCert at hver
  simp only [Bool.and_eq_true, List.all_eq_true] at hver
  rcases hver with ⟨⟨_, _⟩, hall⟩
  by_cases hgood : ∀ o ∈ cert.openings,
      o.tileIdx < f.tiles.length ∧
      o.pixels = (f.tiles.getD o.tileIdx ⟨[], [], []⟩).pixels ∧
      o.rawSalt = (f.tiles.getD o.tileIdx ⟨[], [], []⟩).rawSalt ∧
      o.sumSalt = (f.tiles.getD o.tileIdx ⟨[], [], []⟩).sumSalt
  · exact Or.inl hgood
  · right; push Not at hgood; rcases hgood with ⟨o, hoMem, hbad⟩
    have hvo := hall o hoMem; unfold verifyRoiOpening at hvo
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hvo
    rcases hvo with ⟨⟨⟨⟨hidxGrid, hrs32⟩, hss32⟩, ⟨_, hlenLe⟩⟩, hmpath⟩
    have hidx : o.tileIdx < f.tiles.length := by rw [hf.2.1]; exact hidxGrid
    have hwf := hf.2.2.2.2.1 (f.tiles.getD o.tileIdx ⟨[], [], []⟩) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
      exact List.getElem_mem hidx)
    rw [hf.2.2.2.2.2.1] at hmpath
    rcases merklePath_sound_or_collision (frameLeaves_all_len32 f.header.ctx f.tiles)
        (by rw [frameLeaves_length]; exact hidx) hmpath with hleafEq | hcoll
    · rw [frameLeaves_getD f.header.ctx f.tiles hidx] at hleafEq
      unfold RawSensorTile.leaf RawSensorTile.rawCommit RawSensorTile.sumCommit at hleafEq
      have hiB : o.tileIdx < 4294967296 := by have := hf.2.2.2.1; omega
      rcases tileLeafCommit_bind_or_collision (rawTileCommit_length ..) (rawTileCommit_length ..)
          hf.1 hf.1 hiB hiB hleafEq with ⟨_, _, hrcEq, hscEq⟩ | hcoll
      · rcases rawTileCommit_bind_or_collision hrs32 hwf.1 hf.1 hf.1 hiB hiB
            (by omega) (by have := hwf.2.2.2; omega) hrcEq with ⟨_, _, hrsEq, hpixEq⟩ | hcoll
        · have hs1 : sumBytes o.pixels < 4294967296 := by have := sumBytes_le o.pixels; omega
          have hs2 : sumBytes (f.tiles.getD o.tileIdx ⟨[], [], []⟩).pixels < 4294967296 := by
            have := sumBytes_le (f.tiles.getD o.tileIdx ⟨[], [], []⟩).pixels; have := hwf.2.2.2; omega
          rcases sumTileCommit_bind_or_collision hss32 hwf.2.1 hf.1 hf.1 hiB hiB
              hs1 hs2 (by omega) (by have := hwf.2.2.2; omega) hscEq with ⟨_, _, hssEq, _, _⟩ | hcoll
          · exact False.elim (hbad hidx hpixEq hrsEq hssEq)
          · exact hcoll
        · exact hcoll
      · exact hcoll
    · exact hcoll

/-! ## §5. Algebraic `BabyBear` Blur / Downscale & Ambient-dB Envelope Certificates -/

theorem bounded_sum_no_wrap_babybear (xs : List UInt8) (hlen : xs.length * 255 < babyBearP) :
    ((sumBytes xs : BabyBear)).val = sumBytes xs := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (sumBytes_le xs) hlen)]

theorem bounded_nat_no_wrap_babybear {n : Nat} (h : n < babyBearP) : ((n : BabyBear)).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

def applyMask (pixels : List UInt8) (mask : List BabyBear) : List BabyBear :=
  List.zipWith (fun b m => (b.toNat : BabyBear) + m) pixels mask

def shiftMask (p p' : List UInt8) (mask : List BabyBear) : List BabyBear :=
  List.zipWith (fun ab m => m + (ab.1.toNat : BabyBear) - (ab.2.toNat : BabyBear))
    (List.zip p p') mask

theorem zeroSumMask_preserves_sum :
    ∀ (pixels : List UInt8) (mask : List BabyBear), pixels.length = mask.length →
      sumBB (applyMask pixels mask) = (sumBytes pixels : BabyBear) + sumBB mask
  | [], [], _ => by simp [applyMask, sumBB, sumBytes]
  | a :: ps, m :: ms, hlen => by
      have ih := zeroSumMask_preserves_sum ps ms (by simp at hlen; omega)
      simp only [applyMask, List.zipWith_cons_cons, sumBB, sumBytes]
      change (a.toNat : BabyBear) + m + sumBB (applyMask ps ms) = _
      rw [ih]; push_cast; ring

private theorem shiftMask_sum_aux :
    ∀ (p p' : List UInt8) (mask : List BabyBear),
      p.length = p'.length → p.length = mask.length →
      sumBB (shiftMask p p' mask) =
        sumBB mask + (sumBytes p : BabyBear) - (sumBytes p' : BabyBear)
  | [], [], [], _, _ => by simp [shiftMask, sumBB, sumBytes]
  | a :: ps, b :: ps', m :: ms, h1, h2 => by
      have ih := shiftMask_sum_aux ps ps' ms (by simp at h1; omega) (by simp at h2; omega)
      simp only [shiftMask, List.zip_cons_cons, List.zipWith_cons_cons, sumBB, sumBytes]
      change m + (a.toNat : BabyBear) - (b.toNat : BabyBear) + sumBB (shiftMask ps ps' ms) = _
      rw [ih]; push_cast; ring

private theorem applyMask_shiftMask_aux :
    ∀ (p p' : List UInt8) (mask : List BabyBear),
      p.length = p'.length → p.length = mask.length →
      applyMask p' (shiftMask p p' mask) = applyMask p mask
  | [], [], [], _, _ => rfl
  | _ :: ps, _ :: ps', _ :: ms, h1, h2 => by
      have ih := applyMask_shiftMask_aux ps ps' ms (by simp at h1; omega) (by simp at h2; omega)
      simp only [applyMask, shiftMask, List.zip_cons_cons, List.zipWith_cons_cons, List.cons.injEq]
      exact ⟨by ring, ih⟩

private theorem shiftMask_involutive_aux :
    ∀ (p p' : List UInt8) (mask : List BabyBear),
      p.length = p'.length → p.length = mask.length →
      shiftMask p' p (shiftMask p p' mask) = mask
  | [], [], [], _, _ => rfl
  | _ :: ps, _ :: ps', _ :: ms, h1, h2 => by
      have ih := shiftMask_involutive_aux ps ps' ms (by simp at h1; omega) (by simp at h2; omega)
      simp only [shiftMask, List.zip_cons_cons, List.zipWith_cons_cons, List.cons.injEq]
      exact ⟨by ring, ih⟩

/-- **Unconditional Zero-Knowledge Sub-Tile Pixel / Speech Formant Hiding (`TVD = 0` Bijection).** -/
theorem zeroSumMask_hides_individual_samples (p p' : List UInt8) (m : List BabyBear)
    (hlen : p.length = p'.length) (hmlen : p.length = m.length)
    (hsum : sumBytes p = sumBytes p') (hzero : sumBB m = 0) :
    sumBB (shiftMask p p' m) = 0 ∧
    applyMask p' (shiftMask p p' m) = applyMask p m ∧
    shiftMask p' p (shiftMask p p' m) = m :=
  ⟨by rw [shiftMask_sum_aux p p' m hlen hmlen, hzero, hsum]; ring,
   applyMask_shiftMask_aux p p' m hlen hmlen,
   shiftMask_involutive_aux p p' m hlen hmlen⟩

structure BlurTileEntry where
  tileIdx         : Nat
  tileSum         : Nat
  tileLen         : Nat
  meanValue       : Nat
  sumSalt         : Salt256
  sealedRawCommit : Digest
  merklePath      : List Digest
  deriving DecidableEq, Repr
structure BlurEnvelopeCert where
  entries            : List BlurTileEntry
  claimedEnvelopeSum : Nat
  maskedTerms        : List BabyBear
  deriving DecidableEq, Repr
def verifyBlurEntry (h : SensorFrameHeader) (e : BlurTileEntry) : Bool :=
  decide (e.tileIdx < h.gridWidth * h.gridHeight) && decide (0 < e.tileLen && e.tileLen ≤ 65536) &&
  decide (e.tileSum ≤ e.tileLen * 255) && decide (e.meanValue = e.tileSum / e.tileLen) &&
  decide (e.sumSalt.length = 32) && decide (e.sealedRawCommit.length = 32) &&
  verifyMerklePath h.merkleRoot h.merkleDepth e.tileIdx
    (tileLeafCommit h.ctx e.tileIdx e.sealedRawCommit (sumTileCommit h.ctx e.tileIdx e.sumSalt e.tileSum e.tileLen)) e.merklePath
def verifyBlurEnvelopeCert (hwKey : List UInt8) (h : SensorFrameHeader) (c : BlurEnvelopeCert) : Bool :=
  let totalSamples := sumNats (c.entries.map BlurTileEntry.tileLen)
  let totalSum     := sumNats (c.entries.map BlurTileEntry.tileSum)
  verifyFrameHeader hwKey h && allDistinct (c.entries.map BlurTileEntry.tileIdx) &&
  decide (totalSamples * 255 < babyBearP) && decide (c.claimedEnvelopeSum = totalSum) &&
  decide (c.maskedTerms.length = c.entries.length) && decide (sumBB c.maskedTerms = (c.claimedEnvelopeSum : BabyBear)) &&
  c.entries.all (verifyBlurEntry h)

private theorem sumNats_map_congr {α : Type*} (xs : List α) (f g : α → Nat)
    (h : ∀ x ∈ xs, f x = g x) : sumNats (xs.map f) = sumNats (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons a r ih =>
      simp only [List.map_cons, sumNats]
      rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem sumNats_le_bound (es : List BlurTileEntry)
    (h : ∀ e ∈ es, e.tileSum ≤ e.tileLen * 255) :
    sumNats (es.map BlurTileEntry.tileSum) ≤ sumNats (es.map BlurTileEntry.tileLen) * 255 := by
  induction es with
  | nil => simp [sumNats]
  | cons e r ih =>
      simp only [List.map_cons, sumNats, Nat.add_mul]
      have h1 := h e (List.mem_cons_self ..)
      have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)); omega

/-- **Algebraic Blur & Ambient-dB Envelope Soundness (`blur_cert_sound_or_collision`).** -/
theorem blur_cert_sound_or_collision {hwKey : List UInt8} {f : SealedSensorFrame}
    {cert : BlurEnvelopeCert} (hf : f.Honest hwKey)
    (hver : verifyBlurEnvelopeCert hwKey f.header cert = true) :
    ((∀ e ∈ cert.entries,
        e.tileIdx < f.tiles.length ∧
        e.tileSum = sumBytes (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels ∧
        e.tileLen = (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels.length ∧
        e.meanValue = sumBytes (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels /
          (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels.length) ∧
      cert.claimedEnvelopeSum =
        sumNats (cert.entries.map fun e => sumBytes (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels) ∧
      (sumBB cert.maskedTerms).val = cert.claimedEnvelopeSum) ∨
    Cshake256Collision := by
  unfold verifyBlurEnvelopeCert at hver
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hver
  rcases hver with ⟨⟨⟨⟨⟨⟨_, _⟩, hnoWrap⟩, hclaimEq⟩, _⟩, hbbSum⟩, hall⟩
  by_cases hgood : ∀ e ∈ cert.entries,
      e.tileIdx < f.tiles.length ∧
      e.tileSum = sumBytes (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels ∧
      e.tileLen = (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels.length ∧
      e.meanValue = sumBytes (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels /
        (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels.length
  · left
    have hsumEq : cert.claimedEnvelopeSum =
        sumNats (cert.entries.map fun e => sumBytes (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels) := by
      rw [hclaimEq]; exact sumNats_map_congr cert.entries _ _ (fun e he => (hgood e he).2.1)
    have hle := sumNats_le_bound cert.entries fun e he => by
      have hve := hall e he; unfold verifyBlurEntry at hve
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hve; exact hve.1.1.1.1.2
    refine ⟨hgood, hsumEq, ?_⟩; rw [hbbSum, bounded_nat_no_wrap_babybear (by omega)]
  · right; push Not at hgood; rcases hgood with ⟨e, heMem, hbad⟩
    have hve := hall e heMem; unfold verifyBlurEntry at hve
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hve
    rcases hve with ⟨⟨⟨⟨⟨⟨hidxGrid, ⟨_, hlenLe⟩⟩, hsumLe⟩, hmeanEq⟩, hss32⟩, hraw32⟩, hmpath⟩
    have hidx : e.tileIdx < f.tiles.length := by rw [hf.2.1]; exact hidxGrid
    have hwf := hf.2.2.2.2.1 (f.tiles.getD e.tileIdx ⟨[], [], []⟩) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
      exact List.getElem_mem hidx)
    rw [hf.2.2.2.2.2.1] at hmpath
    rcases merklePath_sound_or_collision (frameLeaves_all_len32 f.header.ctx f.tiles)
        (by rw [frameLeaves_length]; exact hidx) hmpath with hleafEq | hcoll
    · rw [frameLeaves_getD f.header.ctx f.tiles hidx] at hleafEq
      unfold RawSensorTile.leaf RawSensorTile.rawCommit RawSensorTile.sumCommit at hleafEq
      have hiB : e.tileIdx < 4294967296 := by have := hf.2.2.2.1; omega
      rcases tileLeafCommit_bind_or_collision hraw32 (rawTileCommit_length ..)
          hf.1 hf.1 hiB hiB hleafEq with ⟨_, _, _, hscEq⟩ | hcoll
      · have hs2 : sumBytes (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels < 4294967296 := by
          have := sumBytes_le (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels; have := hwf.2.2.2; omega
        rcases sumTileCommit_bind_or_collision hss32 hwf.2.1 hf.1 hf.1 hiB hiB
            (by omega) hs2 (by omega) (by have := hwf.2.2.2; omega) hscEq with
            ⟨_, _, _, hsumEq, hlenEq⟩ | hcoll
        · exact False.elim (hbad hidx hsumEq hlenEq (by rw [hmeanEq, hsumEq, hlenEq]))
        · exact hcoll
      · exact hcoll
    · exact hcoll

/-! ## §6. Anti-Deepfake / Synthetic-Splice `#tooth` Theorems -/

theorem tooth_synthetic_pixel_splice_refused {hwKey : List UInt8} {f : SealedSensorFrame}
    {cert : RoiRevealCert} {o : RoiTileOpening} (hf : f.Honest hwKey) (ho : o ∈ cert.openings)
    (hspliced : o.pixels ≠ (f.tiles.getD o.tileIdx ⟨[], [], []⟩).pixels) :
    verifyRoiRevealCert hwKey f.header cert = false ∨ Cshake256Collision := by
  cases h : verifyRoiRevealCert hwKey f.header cert
  · exact Or.inl rfl
  · rcases roi_reveal_sound_or_collision hf h with hok | hcoll
    · exact False.elim (hspliced (hok o ho).2.1)
    · exact Or.inr hcoll

theorem tooth_cross_timestamp_replay_refused {hwKey : List UInt8} {h₁ h₂ : SensorFrameHeader}
    (hb₁ : h₁.ctx.Bounded) (hb₂ : h₂.ctx.Bounded)
    (htag : h₁.headerTag = computeHeaderTag hwKey h₁)
    (hreplay : h₂.headerTag = h₁.headerTag) (hdiff : h₁.ctx ≠ h₂.ctx) :
    verifyFrameHeader hwKey h₂ = false ∨ Cshake256Collision := by
  cases hv : verifyFrameHeader hwKey h₂
  · exact Or.inl rfl
  · right; unfold verifyFrameHeader at hv; simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    refine ⟨custFrameSeal, hwKey ++ headerBodyBytes h₂, hwKey ++ headerBodyBytes h₁, ?_, ?_⟩
    · intro hs; have hb := List.append_cancel_left hs
      unfold headerBodyBytes at hb; simp only [List.append_assoc] at hb
      exact hdiff (FrameContext.encode_inj hb₁ hb₂ (List.append_inj hb (by simp)).1.symm)
    · change computeHeaderTag hwKey h₂ = computeHeaderTag hwKey h₁; rw [hv.2, hreplay, htag]

theorem tooth_tile_coordinate_graft_refused {ctx : FrameContext} {i₁ i₂ : Nat}
    {rc₁ sc₁ rc₂ sc₂ : Digest} (hctx : ctx.Bounded) (hi₁ : i₁ < 4294967296) (hi₂ : i₂ < 4294967296)
    (hr₁ : rc₁.length = 32) (hr₂ : rc₂.length = 32) (hne : i₁ ≠ i₂)
    (hgraft : tileLeafCommit ctx i₁ rc₁ sc₁ = tileLeafCommit ctx i₂ rc₂ sc₂) : Cshake256Collision := by
  rcases tileLeafCommit_bind_or_collision hr₁ hr₂ hctx hctx hi₁ hi₂ hgraft with ⟨_, h, _, _⟩ | c
  · exact False.elim (hne h)
  · exact c

theorem tooth_forged_blur_mean_refused {hwKey : List UInt8} {f : SealedSensorFrame}
    {cert : BlurEnvelopeCert} (hf : f.Honest hwKey)
    (hforged : cert.claimedEnvelopeSum ≠
      sumNats (cert.entries.map fun e => sumBytes (f.tiles.getD e.tileIdx ⟨[], [], []⟩).pixels)) :
    verifyBlurEnvelopeCert hwKey f.header cert = false ∨ Cshake256Collision := by
  cases hv : verifyBlurEnvelopeCert hwKey f.header cert
  · exact Or.inl rfl
  · rcases blur_cert_sound_or_collision hf hv with ⟨_, heq, _⟩ | c
    · exact False.elim (hforged heq)
    · exact Or.inr c

def demoSalt (base : Nat) : Salt256 := (List.range 32).map fun i => UInt8.ofNat (base + i)

theorem tooth_unmasked_salt_reuse_refused :
    verifyFreshSalts [⟨[1, 2], demoSalt 0x10, demoSalt 0x10⟩] = false ∧
    verifyFreshSalts [⟨[1, 2], demoSalt 0x10, demoSalt 0x30⟩,
                      ⟨[3, 4], demoSalt 0x10, demoSalt 0x50⟩] = false ∧
    verifyFreshSalts [⟨[1, 2], demoSalt 0x10, demoSalt 0x30⟩,
                      ⟨[3, 4], demoSalt 0x50, demoSalt 0x70⟩] = true := by decide

theorem tooth_blur_bad_mean_rejected :
    verifyBlurEntry ⟨⟨7, 1, 1000⟩, 2, 2, 2, .csi2Tile16x16, List.replicate 32 0, List.replicate 32 0⟩
      ⟨0, 25600, 256, 101, demoSalt 0x10, List.replicate 32 0, [List.replicate 32 0, List.replicate 32 0]⟩ = false := by
  decide

/-! ## §7. Concrete 2x2 `16x16` CSI-2 & I2S Conformance Witness + JSON Emitter -/

def demoHwKey    : List UInt8   := (List.range 32).map fun i => UInt8.ofNat (0xA5 + i)
def demoCsi2Ctx  : FrameContext := ⟨0x4550495048414E59, 42, 1732234567000000000⟩
def demoAudioCtx : FrameContext := ⟨0x4932535F41554449, 99, 1732234567016666666⟩
def mkSamples (len base step m : Nat) : List UInt8 := (List.range len).map fun k => UInt8.ofNat ((base + k * step) % m)

def demoCsi2Tiles : List RawSensorTile :=
  [⟨mkSamples 256 40 1 256, demoSalt 0x10, demoSalt 0x30⟩, ⟨mkSamples 256 120 3 256, demoSalt 0x50, demoSalt 0x70⟩,
   ⟨mkSamples 256 20 5 256, demoSalt 0x90, demoSalt 0xB0⟩, ⟨mkSamples 256 180 7 256, demoSalt 0xD0, demoSalt 0xE0⟩]
def demoAudioTiles : List RawSensorTile :=
  [⟨mkSamples 64 10 1 128, demoSalt 0x30, demoSalt 0x10⟩, ⟨mkSamples 64 25 2 128, demoSalt 0x70, demoSalt 0x50⟩]

private def hexBytes (bytes : List UInt8) : String :=
  String.join (bytes.map fun b => let d := "0123456789abcdef".toList; String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])
private def jBool (b : Bool) : String := if b then "true" else "false"
private def jStrs (xs : List String) : String := "[" ++ String.intercalate ", " (xs.map fun s => "\"" ++ s ++ "\"") ++ "]"
private def jNats (xs : List Nat) : String := "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

private def emitSensoryRoiConformance (path : System.FilePath) : IO Unit := do
  let f := sealSensorFrame demoHwKey demoCsi2Ctx 2 2 2 .csi2Tile16x16 demoCsi2Tiles
  let lvs := frameLeaves demoCsi2Ctx demoCsi2Tiles
  let t0 := demoCsi2Tiles[0]!; let t2 := demoCsi2Tiles[2]!
  let p0 := openMerklePath 2 0 lvs; let p2 := openMerklePath 2 2 lvs
  let roiCert : RoiRevealCert := ⟨[⟨0, t0.pixels, t0.rawSalt, t0.sumSalt, p0⟩]⟩
  let okRoi := verifyRoiRevealCert demoHwKey f.header roiCert
  let spliced := match t0.pixels with | [] => [] | b :: r => (b + 1) :: r
  let badSplice := !verifyRoiRevealCert demoHwKey f.header ⟨[⟨0, spliced, t0.rawSalt, t0.sumSalt, p0⟩]⟩
  let badReplay := !verifyRoiRevealCert demoHwKey { f.header with ctx := { f.header.ctx with timestampNs := f.header.ctx.timestampNs + 1 } } roiCert
  let s2 := sumBytes t2.pixels; let m2 := s2 / t2.pixels.length
  let be2 : BlurTileEntry := ⟨2, s2, t2.pixels.length, m2, t2.sumSalt, t2.rawCommit demoCsi2Ctx 2, p2⟩
  let okBlur := verifyBlurEnvelopeCert demoHwKey f.header ⟨[be2], s2, [(s2 : BabyBear)]⟩
  let badBlur := !verifyBlurEnvelopeCert demoHwKey f.header ⟨[{ be2 with tileSum := s2 + 1, meanValue := (s2 + 1) / t2.pixels.length }], s2 + 1, [((s2 + 1 : Nat) : BabyBear)]⟩
  let af := sealSensorFrame demoHwKey demoAudioCtx 2 1 1 .i2sAudioWindow demoAudioTiles
  let alvs := frameLeaves demoAudioCtx demoAudioTiles
  let a0 := demoAudioTiles[0]!; let a1 := demoAudioTiles[1]!
  let sa0 := sumBytes a0.pixels; let sa1 := sumBytes a1.pixels; let eWin := sa0 + sa1
  let maskVal : Nat := 1234567
  let y0 : BabyBear := (sa0 : BabyBear) + (maskVal : BabyBear)
  let y1 : BabyBear := (sa1 : BabyBear) - (maskVal : BabyBear)
  let okAudio := verifyBlurEnvelopeCert demoHwKey af.header
    ⟨[⟨0, sa0, a0.pixels.length, sa0 / a0.pixels.length, a0.sumSalt, a0.rawCommit demoAudioCtx 0, openMerklePath 1 0 alvs⟩,
      ⟨1, sa1, a1.pixels.length, sa1 / a1.pixels.length, a1.sumSalt, a1.rawCommit demoAudioCtx 1, openMerklePath 1 1 alvs⟩], eWin, [y0, y1]⟩
  let okSalts := verifyFreshSalts demoCsi2Tiles
  unless okRoi && badSplice && badReplay && okBlur && badBlur && okAudio && okSalts do
    throw (IO.userError "SensoryRoiZeroKnowledge self-check failed")
  let json :=
    "{\n  \"schema\": \"minidregg.sensory_roi_conformance.v1\", \"source\": \"Assurance/SensoryRoiZeroKnowledge.lean\",\n" ++
    s!"  \"hw_key_hex\": \"{hexBytes demoHwKey}\", \"empty_leaf_hex\": \"{hexBytes emptyLeaf}\",\n" ++
    "  \"csi2_frame\": {\n" ++
    s!"    \"sensor_id\": {demoCsi2Ctx.sensorId}, \"frame_seq\": {demoCsi2Ctx.frameSeq}, \"timestamp_ns\": {demoCsi2Ctx.timestampNs},\n" ++
    s!"    \"grid_width\": 2, \"grid_height\": 2, \"merkle_depth\": 2,\n" ++
    s!"    \"merkle_root_hex\": \"{hexBytes f.header.merkleRoot}\", \"header_tag_hex\": \"{hexBytes f.header.headerTag}\",\n" ++
    s!"    \"tile_leaves_hex\": {jStrs (lvs.map hexBytes)}, \"tiles_pixels_hex\": {jStrs (demoCsi2Tiles.map fun t => hexBytes t.pixels)},\n" ++
    s!"    \"tiles_raw_salts_hex\": {jStrs (demoCsi2Tiles.map fun t => hexBytes t.rawSalt)}, \"tiles_sum_salts_hex\": {jStrs (demoCsi2Tiles.map fun t => hexBytes t.sumSalt)},\n" ++
    s!"    \"roi_tile0_path_hex\": {jStrs (p0.map hexBytes)}, \"blur_tile2_sum\": {s2}, \"blur_tile2_mean\": {m2},\n" ++
    s!"    \"blur_tile2_sealed_raw_commit_hex\": \"{hexBytes (t2.rawCommit demoCsi2Ctx 2)}\", \"blur_tile2_path_hex\": {jStrs (p2.map hexBytes)}\n  },\n" ++
    "  \"i2s_audio_frame\": {\n" ++
    s!"    \"sensor_id\": {demoAudioCtx.sensorId}, \"frame_seq\": {demoAudioCtx.frameSeq}, \"timestamp_ns\": {demoAudioCtx.timestampNs},\n" ++
    s!"    \"grid_width\": 2, \"grid_height\": 1, \"merkle_depth\": 1,\n" ++
    s!"    \"merkle_root_hex\": \"{hexBytes af.header.merkleRoot}\", \"header_tag_hex\": \"{hexBytes af.header.headerTag}\",\n" ++
    s!"    \"windows_pixels_hex\": {jStrs (demoAudioTiles.map fun t => hexBytes t.pixels)}, \"windows_raw_salts_hex\": {jStrs (demoAudioTiles.map fun t => hexBytes t.rawSalt)},\n" ++
    s!"    \"windows_sum_salts_hex\": {jStrs (demoAudioTiles.map fun t => hexBytes t.sumSalt)}, \"envelope_sum\": {eWin}, \"mask_scalar\": {maskVal},\n" ++
    s!"    \"masked_terms_bb\": {jNats [y0.val, y1.val]}\n  },\n" ++
    "  \"lean_self_checks\": {\n" ++
    s!"    \"roi_ok\": {jBool okRoi}, \"splice_refused\": {jBool badSplice}, \"replay_refused\": {jBool badReplay},\n" ++
    s!"    \"blur_ok\": {jBool okBlur}, \"forged_blur_refused\": {jBool badBlur}, \"audio_envelope_ok\": {jBool okAudio}, \"fresh_salts_ok\": {jBool okSalts}\n  }\n}\n"
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path json

#eval emitSensoryRoiConformance "prover/testdata/sensory_roi_conformance.json"

/-! ## §8. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.merklePath_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merklePath_sound_or_collision
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.unopened_bystander_tiles_hidden' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unopened_bystander_tiles_hidden
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.unopened_bystander_tiles_hidden_fresh_salts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unopened_bystander_tiles_hidden_fresh_salts
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.bystander_salt_disclosed_iff_in_frustum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bystander_salt_disclosed_iff_in_frustum
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.roi_reveal_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roi_reveal_sound_or_collision
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.bounded_sum_no_wrap_babybear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bounded_sum_no_wrap_babybear
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.zeroSumMask_hides_individual_samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zeroSumMask_hides_individual_samples
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.blur_cert_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms blur_cert_sound_or_collision
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_synthetic_pixel_splice_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_synthetic_pixel_splice_refused
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_cross_timestamp_replay_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_cross_timestamp_replay_refused
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_tile_coordinate_graft_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_tile_coordinate_graft_refused
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_forged_blur_mean_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_forged_blur_mean_refused
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_unmasked_salt_reuse_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms tooth_unmasked_salt_reuse_refused

end Minidregg.Assurance.SensoryRoiZeroKnowledge
