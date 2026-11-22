/-
# `Assurance/SensoryRoiZeroKnowledge.lean` — *Rainbows End* Wearable SHE Organ #4 ("Epiphany Lens" v2)

Asymmetric post-quantum (`WotsCshake256` / XMSS) raw-only CSI-2 camera & I2S audio sensor provenance
with **ZERO capture-time `sumCommit`**, **ZERO symmetric `hwKey`**, **ZERO cleartext `tile_sum`**,
and **REAL `BabyBearExt4` (`u^4 = 11`) HVZK masked sumcheck + `UD-100` BaseFold/FRI proofs**:
1. **Asymmetric PQ Enclave Header Attestation (`WotsCshake256` / XMSS):** `verifyFrameHeader` holds
   ONLY `EnclavePublicKey` and enforces Rust's exact geometry/bounds; proves
   `verifyFrameHeader_bodyBounded`, `verifyFrameHeader_wots_complete`, `headerSigningPayload_inj`,
   `header_unforgeable_without_sk` (`treeDepth = 0`), `header_unforgeable_xmss_or_collision`
   (`treeDepth > 0`), and `tooth_cross_timestamp_replay_refused`.
2. **Raw-Only Zero-Bystander-Leakage ROI Reveal (ZERO `sumCommit`):** `merklePath_sound_or_collision`,
   `unopened_bystander_tiles_hidden`, `unopened_bystander_tiles_hidden_fresh_salts` (+ poles),
   `bystander_salt_disclosed_iff_in_frustum`, and `roi_reveal_sound_or_collision` (`len = tileLen`).
3. **Boolean Remainder Range Check, Box-Blur Division, `BabyBearExt4` HVZK & `UD-100` Arithmetic:**
   `booleanBitsNat_lt`, `blur_div_unique_of_boolean_rem`, `tooth_unconstrained_rem_forges_blur_mean`,
   `ext4_hvzk_sumcheck_gap_zero` (ideal uniform `GMaskExt4` sumcheck view `TVD = 0`),
   `ud100_query_arithmetic_rate4_q148_pow16`, and `tooth_q48_rate4_not_ud100`.
   *Scope (`[OPEN]` seams):* full composed ROM/FS/FRI verifier soundness (`[BCIKS20]` Thm 1.7),
   full-wire joint HVZK + seeded CSPRNG reduction, and `rtRaw` PCS encoder formalization remain open.
4. **Refutation of v1 Cleartext `tile_sum` (`[REFUTED: v1 BlurTileEntry cleartext tile_sum]`):**
   `tooth_cleartext_tile_sum_leaks_spatial_luminance` (`[25600, 0]` vs `[12800, 12800]` separated
   with advantage `1` in v1 vs exact `TVD = 0` in v2 `AmbientEnvelopeZkProof`).
-/
import Theory.Sp800185Cshake256Core
import Theory.PqSelectiveBiscuit
import Theory.SumcheckHvzkMask
import Compiler.BabyBear
import Selvage.BabyBearExt4
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Minidregg.Assurance.SensoryRoiZeroKnowledge

open scoped BigOperators
open Minidregg.Compiler (BabyBear babyBearP)
open Minidregg.Compiler.Sp800185Cshake256 (cshake256Bytes cshake256Bytes_length)
open Minidregg.Theory.PqSelectiveBiscuit (PqSigScheme wotsCshake256 wotsPk wotsSign wotsVerify wotsVerify_sign)
open Minidregg.Theory.FiniteTapeGap (GapAtMost not_gapAtMost_of_separating)
open Minidregg.Theory.SumcheckHvzkMask (TargetPoly MaskSpace PublicGMaskView evalTargetPoly cubeSum
  publicGMaskScaledView hvzkSumcheck_publicGMask_scaled_gapAtMost_zero)
open Minidregg.Selvage.BabyBearExt4 (Ext4 coefficients)

set_option autoImplicit false

/-! ## §1. Framing, Domain-Separated `cSHAKE256` (v2, Raw-Only), & Collision Extraction -/

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

def custRawTile    : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/RAW_TILE/V2"
def custEmptyLeaf  : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/EMPTY_LEAF/V2"
def custMerkleNode : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/MERKLE_NODE/V2"
def custXmssLeaf   : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/XMSS_LEAF/V2"
def custFrameSeal  : List UInt8 := asciiBytes "MINIDREGG/SENSORY_ROI/FRAME_SEAL/V2"
def emptyLeaf : Digest := cshake256Bytes custEmptyLeaf []
@[simp] theorem emptyLeaf_length : emptyLeaf.length = 32 := cshake256Bytes_length _ _

inductive SensorModality where | csi2Tile16x16 | i2sAudioWindow deriving DecidableEq, Repr
def SensorModality.tag : SensorModality → UInt8 | .csi2Tile16x16 => 1 | .i2sAudioWindow => 2
theorem SensorModality.tag_inj {a b : SensorModality} (h : a.tag = b.tag) : a = b := by
  cases a <;> cases b <;> simp [SensorModality.tag] at h ⊢

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
theorem sumBytes_le (xs : List UInt8) : sumBytes xs ≤ xs.length * 255 := by
  induction xs with
  | nil => simp [sumBytes]
  | cons b r ih => have hb : b.toNat ≤ 255 := Nat.le_of_lt_succ b.toNat_lt; simp only [sumBytes, List.length_cons, Nat.add_mul, Nat.one_mul]; omega

/-- Single raw-only per-tile commitment (ZERO `sumCommit`, ZERO `sumSalt`). -/
def rawTilePreimage (ctx : FrameContext) (i : Nat) (rs : Salt256) (px : List UInt8) : List UInt8 :=
  ctx.encode ++ u32LE i ++ rs ++ u32LE px.length ++ px
def rawTileCommit (ctx : FrameContext) (i : Nat) (rs : Salt256) (px : List UInt8) : Digest :=
  cshake256Bytes custRawTile (rawTilePreimage ctx i rs px)
@[simp] theorem rawTileCommit_length (c : FrameContext) (i : Nat) (s : Salt256) (p : List UInt8) :
    (rawTileCommit c i s p).length = 32 := cshake256Bytes_length _ _

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

/-! ## §2. Padded Binary Merkle Tree & Constructive Collision Extraction -/

def merkleParentPreimage (lvl idx : Nat) (l r : Digest) : List UInt8 := [UInt8.ofNat (lvl % 256)] ++ u32LE idx ++ l ++ r
def merkleParent (lvl idx : Nat) (l r : Digest) : Digest := cshake256Bytes custMerkleNode (merkleParentPreimage lvl idx l r)
@[simp] theorem merkleParent_length (lvl idx : Nat) (l r : Digest) : (merkleParent lvl idx l r).length = 32 := cshake256Bytes_length _ _

def padToPow2 (depth : Nat) (leaves : List Digest) : List Digest :=
  leaves.take (2 ^ depth) ++ List.replicate (2 ^ depth - leaves.length) emptyLeaf
theorem padToPow2_length (depth : Nat) (leaves : List Digest) : (padToPow2 depth leaves).length = 2 ^ depth := by
  unfold padToPow2; simp [List.length_take, List.length_replicate]; omega
theorem padToPow2_getD (depth : Nat) (leaves : List Digest) {idx : Nat} (hidx : idx < leaves.length) (hcap : idx < 2 ^ depth) :
    (padToPow2 depth leaves).getD idx emptyLeaf = leaves.getD idx emptyLeaf := by
  unfold padToPow2; have hlt : idx < (leaves.take (2 ^ depth)).length := by rw [List.length_take]; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_take_of_lt hcap]
theorem padToPow2_all_len32 (depth : Nat) (leaves : List Digest) (hlen : ∀ d ∈ leaves, d.length = 32) :
    ∀ d ∈ padToPow2 depth leaves, d.length = 32 := by
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
      have ih := merkleLayer_length lvl (base + 1) r m (by omega)
      omega
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
def merkleRoot (depth : Nat) (leaves : List Digest) : Digest := merkleRootAux 0 depth (padToPow2 depth leaves)

def merklePathAux (lvl : Nat) : Nat → Nat → List Digest → List Digest
  | 0, _, _ => []
  | d + 1, idx, xs =>
      let sib := if idx % 2 == 0 then idx + 1 else idx - 1
      xs.getD sib emptyLeaf :: merklePathAux (lvl + 1) d (idx / 2) (merkleLayer lvl 0 xs)
def openMerklePath (depth idx : Nat) (leaves : List Digest) : List Digest := merklePathAux 0 depth idx (padToPow2 depth leaves)

def evalMerklePathAux (lvl idx : Nat) (cur : Digest) : List Digest → Digest
  | [] => cur
  | sib :: rest =>
      let par := if idx % 2 == 0 then merkleParent lvl (idx / 2) cur sib else merkleParent lvl (idx / 2) sib cur
      evalMerklePathAux (lvl + 1) (idx / 2) par rest

def verifyMerklePath (root : Digest) (depth idx : Nat) (leaf : Digest) (sibs : List Digest) : Bool :=
  decide (idx < 2 ^ depth) && decide (sibs.length = depth) && decide (leaf.length = 32) &&
  sibs.all (fun s => decide (s.length = 32)) && decide (evalMerklePathAux 0 idx leaf sibs = root)

private theorem merklePathAux_length (lvl d idx : Nat) (xs : List Digest) : (merklePathAux lvl d idx xs).length = d := by
  induction d generalizing lvl idx xs with | zero => rfl | succ d ih => simp [merklePathAux, ih]

private theorem merklePathAux_all_len32 (lvl d idx : Nat) (xs : List Digest) (hx : ∀ e ∈ xs, e.length = 32) :
    ∀ s ∈ merklePathAux lvl d idx xs, s.length = 32 := by
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
    evalMerklePathAux lvl idx (xs.getD idx emptyLeaf) (merklePathAux lvl d idx xs) = merkleRootAux lvl d xs := by
  induction d generalizing lvl idx xs with
  | zero =>
      have hi : idx = 0 := by simp at hidx; omega
      subst hi; cases xs with | nil => simp at hlen | cons _ _ => rfl
  | succ d ih =>
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
      have hlen2 : xs.length = 2 * 2 ^ d := by omega
      have hp : idx / 2 < 2 ^ d := by omega
      have hget := merkleLayer_getD lvl 0 xs (2 ^ d) (idx / 2) hlen2 hp; simp only [Nat.zero_add] at hget
      simp only [merklePathAux, evalMerklePathAux, merkleRootAux]
      have hstep :
          (if idx % 2 == 0 then merkleParent lvl (idx / 2) (xs.getD idx emptyLeaf)
              (xs.getD (if idx % 2 == 0 then idx + 1 else idx - 1) emptyLeaf)
           else merkleParent lvl (idx / 2)
              (xs.getD (if idx % 2 == 0 then idx + 1 else idx - 1) emptyLeaf) (xs.getD idx emptyLeaf)) =
          (merkleLayer lvl 0 xs).getD (idx / 2) emptyLeaf := by
        by_cases hev : idx % 2 = 0
        · have h1 : 2 * (idx / 2) = idx := by omega
          simp only [hev, beq_self_eq_true, ↓reduceIte]; rw [hget, h1]
        · have h1 : 2 * (idx / 2) = idx - 1 := by omega
          have h2 : idx - 1 + 1 = idx := by omega
          have hne : (idx % 2 == 0) = false := by simp [hev]
          simp only [hne, Bool.false_eq_true, ↓reduceIte]; rw [hget, h1, h2]
      rw [hstep]; exact ih (lvl + 1) (idx / 2) (merkleLayer lvl 0 xs) (merkleLayer_length lvl 0 xs (2 ^ d) hlen2) hp

theorem verifyMerklePath_complete (depth idx : Nat) (leaves : List Digest)
    (hlen : ∀ d ∈ leaves, d.length = 32) (hidx : idx < leaves.length) (hcap : idx < 2 ^ depth) :
    verifyMerklePath (merkleRoot depth leaves) depth idx (leaves.getD idx emptyLeaf) (openMerklePath depth idx leaves) = true := by
  have hleaf32 : (leaves.getD idx emptyLeaf).length = 32 := by
    rw [List.getD_eq_getElem?_getD]; cases hopt : leaves[idx]? with
    | none => exact emptyLeaf_length | some v => exact hlen v (List.mem_of_getElem? hopt)
  unfold verifyMerklePath openMerklePath merkleRoot; simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨hcap, merklePathAux_length 0 depth idx _⟩, hleaf32⟩,
    fun s hs => merklePathAux_all_len32 0 depth idx _ (padToPow2_all_len32 depth leaves hlen) s hs⟩, ?_⟩
  rw [← padToPow2_getD depth leaves hidx hcap]
  exact evalMerklePathAux_complete 0 depth idx (padToPow2 depth leaves) (padToPow2_length depth leaves) hcap

private theorem merkleParent_bind_or_collision {lvl idx : Nat} {l₁ r₁ l₂ r₂ : Digest}
    (hl₁ : l₁.length = 32) (hl₂ : l₂.length = 32) (heq : merkleParent lvl idx l₁ r₁ = merkleParent lvl idx l₂ r₂) :
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
          set par := if idx % 2 == 0 then merkleParent lvl (idx / 2) cur sib else merkleParent lvl (idx / 2) sib cur
          have hpar32 : par.length = 32 := by dsimp only [par]; split <;> exact merkleParent_length ..
          rcases ih (lvl + 1) (idx / 2) (merkleLayer lvl 0 xs) par rest
              (merkleLayer_length lvl 0 xs (2 ^ d) hlen2) hp (merkleLayer_all_len32 lvl 0 xs)
              hpar32 (by simp at hsibLen; omega) (fun s hs => hsib32 s (List.mem_cons_of_mem _ hs)) heval with hparEq | hcoll
          · have hget := merkleLayer_getD lvl 0 xs (2 ^ d) (idx / 2) hlen2 hp
            simp only [Nat.zero_add] at hget; rw [hget] at hparEq
            have hleft32 : (xs.getD (2 * (idx / 2)) emptyLeaf).length = 32 := by
              rw [List.getD_eq_getElem?_getD]; cases hopt : xs[2 * (idx / 2)]? with
              | none => exact emptyLeaf_length | some v => exact hx32 v (List.mem_of_getElem? hopt)
            by_cases hev : idx % 2 = 0
            · have h1 : 2 * (idx / 2) = idx := by omega
              have he : merkleParent lvl (idx / 2) cur sib =
                  merkleParent lvl (idx / 2) (xs.getD idx emptyLeaf) (xs.getD (2 * (idx / 2) + 1) emptyLeaf) := by
                simpa [par, hev, h1] using hparEq
              rcases merkleParent_bind_or_collision hcur32 (by simpa [h1] using hleft32) he with ⟨h, _⟩ | c
              · exact Or.inl h
              · exact Or.inr c
            · have h2 : 2 * (idx / 2) + 1 = idx := by omega
              have hne : (idx % 2 == 0) = false := by simp [hev]
              have he : merkleParent lvl (idx / 2) sib cur =
                  merkleParent lvl (idx / 2) (xs.getD (2 * (idx / 2)) emptyLeaf) (xs.getD idx emptyLeaf) := by
                simpa [par, hne, h2] using hparEq
              rcases merkleParent_bind_or_collision (hsib32 sib (List.mem_cons_self ..)) hleft32 he with ⟨_, h⟩ | c
              · exact Or.inl h
              · exact Or.inr c
          · exact Or.inr hcoll

theorem merklePath_sound_or_collision {depth idx : Nat} {leaves : List Digest} {leaf : Digest} {sibs : List Digest}
    (hlen : ∀ d ∈ leaves, d.length = 32) (hidx : idx < leaves.length)
    (hver : verifyMerklePath (merkleRoot depth leaves) depth idx leaf sibs = true) :
    leaf = leaves.getD idx emptyLeaf ∨ Cshake256Collision := by
  unfold verifyMerklePath at hver; simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hver
  rcases hver with ⟨⟨⟨⟨hcap, hsibLen⟩, hleaf32⟩, hsib32⟩, heval⟩
  have hr := evalMerklePathAux_sound_or_collision 0 depth idx (padToPow2 depth leaves) leaf sibs
    (padToPow2_length depth leaves) hcap (padToPow2_all_len32 depth leaves hlen) hleaf32 hsibLen hsib32 heval
  rw [padToPow2_getD depth leaves hidx hcap] at hr; exact hr

/-! ## §3. Asymmetric PQ Enclave Signing (`WotsCshake256`, ZERO `hwKey`, ZERO `sumCommit`) -/

/-- Public verification key held by verifiers (ZERO secret material; verifier CANNOT forge headers). -/
structure EnclavePublicKey where
  root      : Digest
  treeDepth : Nat
  deriving DecidableEq, Repr

/-- Hardware-captured raw tile paired with ONE 256-bit TRNG salt (ZERO `sumSalt`, ZERO `sumCommit`). -/
structure RawSensorTile where
  pixels  : List UInt8
  rawSalt : Salt256
  deriving DecidableEq, Repr, Inhabited

def RawSensorTile.WellFormed (t : RawSensorTile) : Prop := t.rawSalt.length = 32 ∧ 0 < t.pixels.length ∧ t.pixels.length ≤ 65536
def RawSensorTile.leaf (c : FrameContext) (i : Nat) (t : RawSensorTile) : Digest := rawTileCommit c i t.rawSalt t.pixels

/-- Enclave-signed sensor frame header binding `tileMerkleRoot` + PCS `rtRaw` via `WotsCshake256`. -/
structure SensorFrameHeader where
  ctx            : FrameContext
  gridWidth      : Nat
  gridHeight     : Nat
  tileLen        : Nat
  merkleDepth    : Nat
  modality       : SensorModality
  tileMerkleRoot : Digest
  rtRaw          : Digest
  enclavePk      : EnclavePublicKey
  otsIndex       : Nat
  otsPk          : Digest
  wotsSig        : List UInt8
  otsAuthPath    : List Digest
  deriving DecidableEq, Repr

def SensorFrameHeader.BodyBounded (h : SensorFrameHeader) : Prop :=
  h.ctx.Bounded ∧ h.gridWidth < 4294967296 ∧ h.gridHeight < 4294967296 ∧ h.tileLen < 4294967296 ∧
  h.merkleDepth < 4294967296 ∧ h.tileMerkleRoot.length = 32 ∧ h.rtRaw.length = 32 ∧
  h.enclavePk.root.length = 32 ∧ h.enclavePk.treeDepth < 256 ∧ h.otsIndex < 4294967296 ∧ h.otsPk.length = 32

def headerSigningPayload (h : SensorFrameHeader) : List UInt8 :=
  custFrameSeal ++ h.ctx.encode ++ u32LE h.gridWidth ++ u32LE h.gridHeight ++ u32LE h.tileLen ++
  u32LE h.merkleDepth ++ [h.modality.tag] ++ h.tileMerkleRoot ++ h.rtRaw ++ h.enclavePk.root ++
  [UInt8.ofNat (h.enclavePk.treeDepth % 256)] ++ u32LE h.otsIndex ++ h.otsPk

theorem headerSigningPayload_inj {h₁ h₂ : SensorFrameHeader}
    (hb₁ : h₁.BodyBounded) (hb₂ : h₂.BodyBounded) (heq : headerSigningPayload h₁ = headerSigningPayload h₂) :
    h₁.ctx = h₂.ctx ∧ h₁.gridWidth = h₂.gridWidth ∧ h₁.gridHeight = h₂.gridHeight ∧ h₁.tileLen = h₂.tileLen ∧
    h₁.merkleDepth = h₂.merkleDepth ∧ h₁.modality = h₂.modality ∧ h₁.tileMerkleRoot = h₂.tileMerkleRoot ∧
    h₁.rtRaw = h₂.rtRaw ∧ h₁.enclavePk = h₂.enclavePk ∧ h₁.otsIndex = h₂.otsIndex ∧ h₁.otsPk = h₂.otsPk := by
  unfold headerSigningPayload at heq; simp only [List.append_assoc] at heq
  have h0 := List.append_cancel_left heq; have h1 := List.append_inj h0 (by simp)
  have h2 := List.append_inj h1.2 (by simp); have h3 := List.append_inj h2.2 (by simp)
  have h4 := List.append_inj h3.2 (by simp); have h5 := List.append_inj h4.2 (by simp)
  have h6 := List.append_inj h5.2 (by simp)
  have h7 := List.append_inj h6.2 (by rw [hb₁.2.2.2.2.2.1, hb₂.2.2.2.2.2.1])
  have h8 := List.append_inj h7.2 (by rw [hb₁.2.2.2.2.2.2.1, hb₂.2.2.2.2.2.2.1])
  have h9 := List.append_inj h8.2 (by rw [hb₁.2.2.2.2.2.2.2.1, hb₂.2.2.2.2.2.2.2.1])
  have h10 := List.append_inj h9.2 (by simp); have h11 := List.append_inj h10.2 (by simp)
  have hmod : h₁.modality = h₂.modality := SensorModality.tag_inj (by simpa using h6.1)
  have hdep : h₁.enclavePk.treeDepth = h₂.enclavePk.treeDepth := by
    have hd := ui8_ofNat_inj (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (by simpa using h10.1)
    have hlt1 := hb₁.2.2.2.2.2.2.2.2.1
    have hlt2 := hb₂.2.2.2.2.2.2.2.2.1
    omega
  have hpk : h₁.enclavePk = h₂.enclavePk := by cases ep1 : h₁.enclavePk; cases ep2 : h₂.enclavePk; simp_all
  exact ⟨FrameContext.encode_inj hb₁.1 hb₂.1 h1.1, u32LE_inj hb₁.2.1 hb₂.2.1 h2.1, u32LE_inj hb₁.2.2.1 hb₂.2.2.1 h3.1,
    u32LE_inj hb₁.2.2.2.1 hb₂.2.2.2.1 h4.1, u32LE_inj hb₁.2.2.2.2.1 hb₂.2.2.2.2.1 h5.1,
    hmod, h7.1, h8.1, hpk, u32LE_inj hb₁.2.2.2.2.2.2.2.2.2.1 hb₂.2.2.2.2.2.2.2.2.2.1 h11.1, h11.2⟩

def isPow2Le16 (n : Nat) : Bool := (List.range 17).any (fun k => n == 2 ^ k)
theorem isPow2Le16_iff (n : Nat) : isPow2Le16 n = true ↔ ∃ k ≤ 16, n = 2 ^ k := by
  simp only [isPow2Le16, List.any_eq_true, List.mem_range, beq_iff_eq]
  exact ⟨fun ⟨k, hk, heq⟩ => ⟨k, by omega, heq⟩, fun ⟨k, hk, heq⟩ => ⟨k, by omega, heq⟩⟩
theorem isPow2Le16_bounds {n : Nat} (h : isPow2Le16 n = true) : 0 < n ∧ n ≤ 65536 := by
  rcases (isPow2Le16_iff n).mp h with ⟨k, hk, rfl⟩
  exact ⟨Nat.pow_pos (by omega), le_trans (Nat.pow_le_pow_right (by omega) hk) (by norm_num)⟩

def xmssLeafPreimage (depth otsIdx : Nat) (otsPk : Digest) : List UInt8 :=
  [UInt8.ofNat (depth % 256)] ++ u32LE otsIdx ++ otsPk
def xmssLeaf (depth otsIdx : Nat) (otsPk : Digest) : Digest :=
  cshake256Bytes custXmssLeaf (xmssLeafPreimage depth otsIdx otsPk)
@[simp] theorem xmssLeaf_length (d i : Nat) (pk : Digest) : (xmssLeaf d i pk).length = 32 := cshake256Bytes_length _ _

theorem xmssLeaf_bind_or_collision {d₁ d₂ i₁ i₂ : Nat} {pk₁ pk₂ : Digest}
    (hd₁ : d₁ < 256) (hd₂ : d₂ < 256) (hi₁ : i₁ < 4294967296) (hi₂ : i₂ < 4294967296)
    (heq : xmssLeaf d₁ i₁ pk₁ = xmssLeaf d₂ i₂ pk₂) :
    (d₁ = d₂ ∧ i₁ = i₂ ∧ pk₁ = pk₂) ∨ Cshake256Collision := by
  by_cases hp : xmssLeafPreimage d₁ i₁ pk₁ = xmssLeafPreimage d₂ i₂ pk₂
  · left; unfold xmssLeafPreimage at hp; simp only [List.append_assoc] at hp
    have h1 := List.append_inj hp (by simp); have h2 := List.append_inj h1.2 (by simp)
    have hd := ui8_ofNat_inj (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) (by simpa using h1.1)
    exact ⟨by omega, u32LE_inj hi₁ hi₂ h2.1, h2.2⟩
  · exact Or.inr ⟨custXmssLeaf, _, _, hp, heq⟩

/-- Asymmetric verifier: consumes ONLY `expectedPk : EnclavePublicKey` (NO secret key; aligned with Rust). -/
def verifyFrameHeader (expectedPk : EnclavePublicKey) (h : SensorFrameHeader) : Bool :=
  decide (h.enclavePk = expectedPk) && decide (expectedPk.root.length = 32) && decide (expectedPk.treeDepth < 32) &&
  decide (h.ctx.sensorId < 18446744073709551616 && h.ctx.frameSeq < 18446744073709551616 &&
    h.ctx.timestampNs < 18446744073709551616) &&
  decide (h.gridWidth < 4294967296 && h.gridHeight < 4294967296 && h.otsIndex < 4294967296) &&
  decide (h.tileMerkleRoot.length = 32) && decide (h.rtRaw.length = 32) && decide (h.otsPk.length = 32) &&
  isPow2Le16 h.tileLen && decide (h.merkleDepth < 31) &&
  decide (0 < h.gridWidth * h.gridHeight && h.gridWidth * h.gridHeight ≤ 2 ^ h.merkleDepth) &&
  decide (h.otsAuthPath.length = expectedPk.treeDepth) && wotsVerify h.otsPk (headerSigningPayload h) h.wotsSig &&
  (if expectedPk.treeDepth = 0 then decide (h.otsIndex = 0) && decide (h.otsPk = expectedPk.root)
   else verifyMerklePath expectedPk.root expectedPk.treeDepth h.otsIndex
          (xmssLeaf expectedPk.treeDepth h.otsIndex h.otsPk) h.otsAuthPath)

theorem verifyFrameHeader_bodyBounded {expectedPk : EnclavePublicKey} {h : SensorFrameHeader}
    (hver : verifyFrameHeader expectedPk h = true) : h.BodyBounded ∧ isPow2Le16 h.tileLen = true ∧ h.merkleDepth < 31 := by
  unfold verifyFrameHeader at hver; simp only [Bool.and_eq_true, decide_eq_true_eq] at hver
  rcases hver with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hepk, hroot⟩, htd⟩, ⟨⟨hs, hf⟩, ht⟩⟩, ⟨⟨hgw, hgh⟩, hoi⟩⟩, htmr⟩, hrt⟩, hopk⟩, hpow⟩, hmd⟩, _⟩, _⟩, _⟩, _⟩
  have htb := (isPow2Le16_bounds hpow).2
  refine ⟨⟨⟨hs, hf, ht⟩, hgw, hgh, by omega, by omega, htmr, hrt, ?_, ?_, hoi, hopk⟩, hpow, hmd⟩ <;>
    (rw [hepk]; omega)

structure SealedSensorFrame where
  header : SensorFrameHeader
  tiles  : List RawSensorTile
  deriving DecidableEq, Repr

def frameLeaves (ctx : FrameContext) (tiles : List RawSensorTile) : List Digest :=
  (List.range tiles.length).map fun i => (tiles.getD i ⟨[], []⟩).leaf ctx i
theorem frameLeaves_length (ctx : FrameContext) (tiles : List RawSensorTile) : (frameLeaves ctx tiles).length = tiles.length := by simp [frameLeaves]
theorem frameLeaves_all_len32 (ctx : FrameContext) (tiles : List RawSensorTile) : ∀ d ∈ frameLeaves ctx tiles, d.length = 32 := by
  intro d hd; unfold frameLeaves at hd; rcases List.mem_map.mp hd with ⟨_, _, rfl⟩; exact rawTileCommit_length ..
theorem frameLeaves_getD (ctx : FrameContext) (tiles : List RawSensorTile) {i : Nat} (hi : i < tiles.length) :
    (frameLeaves ctx tiles).getD i emptyLeaf = (tiles.getD i ⟨[], []⟩).leaf ctx i := by
  unfold frameLeaves; simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]

/-- Single-key (`treeDepth = 0`) WOTS+ frame sealer (binds `tileMerkleRoot` and PCS `rtRaw`). -/
def sealSensorFrameWots (wotsSeed : List UInt8) (ctx : FrameContext) (gridW gridH tileLen depth : Nat)
    (modality : SensorModality) (rtRaw : Digest) (tiles : List RawSensorTile) : SealedSensorFrame :=
  let pk := wotsPk wotsSeed; let epk : EnclavePublicKey := ⟨pk, 0⟩
  let rt := merkleRoot depth (frameLeaves ctx tiles)
  let base : SensorFrameHeader := ⟨ctx, gridW, gridH, tileLen, depth, modality, rt, rtRaw, epk, 0, pk, [], []⟩
  ⟨{ base with wotsSig := wotsSign wotsSeed (headerSigningPayload base) }, tiles⟩

theorem verifyFrameHeader_wots_complete (wotsSeed : List UInt8) (ctx : FrameContext)
    (gridW gridH tileLen depth : Nat) (modality : SensorModality) (rtRaw : Digest) (tiles : List RawSensorTile)
    (hctx : ctx.Bounded) (hgw : gridW < 4294967296) (hgh : gridH < 4294967296)
    (hrt : rtRaw.length = 32) (htl : isPow2Le16 tileLen = true) (hdep : depth < 31)
    (hg : 0 < gridW * gridH ∧ gridW * gridH ≤ 2 ^ depth) :
    let f := sealSensorFrameWots wotsSeed ctx gridW gridH tileLen depth modality rtRaw tiles
    verifyFrameHeader ⟨wotsPk wotsSeed, 0⟩ f.header = true := by
  dsimp only [sealSensorFrameWots, verifyFrameHeader]
  have hpk32 : (wotsPk wotsSeed).length = 32 := cshake256Bytes_length _ _
  have hmr32 : (merkleRoot depth (frameLeaves ctx tiles)).length = 32 := by
    have haux : ∀ (lvl d : Nat) (xs : List Digest), (∀ e ∈ xs, e.length = 32) → (merkleRootAux lvl d xs).length = 32 := by
      intro lvl d; induction d generalizing lvl with
      | zero => intro xs hx; cases xs with | nil => exact emptyLeaf_length | cons a _ => exact hx a List.mem_cons_self
      | succ d ih => intro xs _; exact ih (lvl + 1) _ (merkleLayer_all_len32 lvl 0 xs)
    exact haux 0 depth _ (padToPow2_all_len32 depth _ (frameLeaves_all_len32 ctx tiles))
  have hpay : headerSigningPayload
      { ctx := ctx, gridWidth := gridW, gridHeight := gridH, tileLen := tileLen, merkleDepth := depth, modality := modality,
        tileMerkleRoot := merkleRoot depth (frameLeaves ctx tiles), rtRaw := rtRaw, enclavePk := ⟨wotsPk wotsSeed, 0⟩,
        otsIndex := 0, otsPk := wotsPk wotsSeed,
        wotsSig := wotsSign wotsSeed (headerSigningPayload ⟨ctx, gridW, gridH, tileLen, depth, modality,
          merkleRoot depth (frameLeaves ctx tiles), rtRaw, ⟨wotsPk wotsSeed, 0⟩, 0, wotsPk wotsSeed, [], []⟩),
        otsAuthPath := [] } =
      headerSigningPayload ⟨ctx, gridW, gridH, tileLen, depth, modality,
        merkleRoot depth (frameLeaves ctx tiles), rtRaw, ⟨wotsPk wotsSeed, 0⟩, 0, wotsPk wotsSeed, [], []⟩ := rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq, ↓reduceIte, List.length_nil, hpk32, hmr32, hrt,
    hctx.1, hctx.2.1, hctx.2.2, hgw, hgh, htl, hdep, hg.1, hg.2, hpay, wotsVerify_sign, and_self, true_and, and_true]
  omega

def SigForgery (S : PqSigScheme) (pk : List UInt8) (signedMsgs : List (List UInt8)) (msg sig : List UInt8) : Prop :=
  S.verify pk msg sig = true ∧ msg ∉ signedMsgs

/-- **Asymmetric Header Non-Forgeability (`treeDepth = 0`):** any fresh accepted payload exhibits a
`wotsCshake256` signature forgery (`SigForgery`). -/
theorem header_unforgeable_without_sk {pk : Digest} {signedMsgs : List (List UInt8)} {h : SensorFrameHeader}
    (hver : verifyFrameHeader ⟨pk, 0⟩ h = true) (hfresh : headerSigningPayload h ∉ signedMsgs) :
    SigForgery wotsCshake256 pk signedMsgs (headerSigningPayload h) h.wotsSig := by
  unfold verifyFrameHeader at hver; simp only [Bool.and_eq_true, decide_eq_true_eq, ↓reduceIte] at hver
  exact ⟨by simpa [wotsCshake256, hver.2.2] using hver.1.2, hfresh⟩

def xmssLeaves (depth : Nat) (otsPks : List Digest) : List Digest :=
  (List.range otsPks.length).map fun k => xmssLeaf depth k (otsPks.getD k emptyLeaf)

/-- **Stateful XMSS (`treeDepth > 0`) Header Non-Forgeability Reduction:** any fresh accepted payload
at leaf `h.otsIndex < otsPks.length` either exhibits a `wotsCshake256` forgery against the authentic
leaf key `otsPks[h.otsIndex]` OR extracts a `cSHAKE256` collision (`Cshake256Collision`). -/
theorem header_unforgeable_xmss_or_collision {depth : Nat} {otsPks : List Digest}
    {signedMsgs : List (List UInt8)} {h : SensorFrameHeader}
    (hdPos : 0 < depth) (hidx : h.otsIndex < otsPks.length)
    (hver : verifyFrameHeader ⟨merkleRoot depth (xmssLeaves depth otsPks), depth⟩ h = true)
    (hfresh : headerSigningPayload h ∉ signedMsgs) :
    SigForgery wotsCshake256 (otsPks.getD h.otsIndex emptyLeaf) signedMsgs (headerSigningPayload h) h.wotsSig ∨
    Cshake256Collision := by
  have hbd := (verifyFrameHeader_bodyBounded hver).1
  unfold verifyFrameHeader at hver
  have hne0 : ¬ (depth = 0) := by omega
  simp only [Bool.and_eq_true, decide_eq_true_eq, hne0, ↓reduceIte] at hver
  have htd : depth < 32 := hver.1.1.1.1.1.1.1.1.1.1.1.2
  have hwots : wotsVerify h.otsPk (headerSigningPayload h) h.wotsSig = true := hver.1.2
  have hmpath : verifyMerklePath (merkleRoot depth (xmssLeaves depth otsPks)) depth h.otsIndex
      (xmssLeaf depth h.otsIndex h.otsPk) h.otsAuthPath = true := hver.2
  have hlen32 : ∀ d ∈ xmssLeaves depth otsPks, d.length = 32 := by
    intro d hd; unfold xmssLeaves at hd; rcases List.mem_map.mp hd with ⟨_, _, rfl⟩; exact xmssLeaf_length ..
  rcases merklePath_sound_or_collision hlen32 (by simp [xmssLeaves, hidx]) hmpath with hleafEq | hcoll
  · have hget : (xmssLeaves depth otsPks).getD h.otsIndex emptyLeaf =
        xmssLeaf depth h.otsIndex (otsPks.getD h.otsIndex emptyLeaf) := by
      unfold xmssLeaves; simp [List.getD_eq_getElem?_getD, List.getElem?_range hidx]
    rw [hget] at hleafEq
    rcases xmssLeaf_bind_or_collision (by omega) (by omega) hbd.2.2.2.2.2.2.2.2.2.1
        hbd.2.2.2.2.2.2.2.2.2.1 hleafEq with ⟨_, _, hpkEq⟩ | hcoll
    · exact Or.inl ⟨by simpa [wotsCshake256, hpkEq] using hwots, hfresh⟩
    · exact Or.inr hcoll
  · exact Or.inr hcoll

theorem tooth_cross_timestamp_replay_refused {pk : Digest} {h₁ h₂ : SensorFrameHeader}
    (hb₁ : h₁.BodyBounded) (hdiff : h₁.ctx ≠ h₂.ctx)
    (hver : verifyFrameHeader ⟨pk, 0⟩ h₂ = true) :
    SigForgery wotsCshake256 pk [headerSigningPayload h₁] (headerSigningPayload h₂) h₂.wotsSig := by
  have hb₂ := (verifyFrameHeader_bodyBounded hver).1
  apply header_unforgeable_without_sk hver; intro hmem; simp only [List.mem_singleton] at hmem
  exact hdiff (headerSigningPayload_inj hb₂ hb₁ hmem).1.symm

def SealedSensorFrame.Honest (expectedPk : EnclavePublicKey) (f : SealedSensorFrame) : Prop :=
  f.header.ctx.Bounded ∧ f.tiles.length = f.header.gridWidth * f.header.gridHeight ∧
  f.tiles.length ≤ 2 ^ f.header.merkleDepth ∧ f.tiles.length < 4294967296 ∧ (∀ t ∈ f.tiles, t.WellFormed) ∧
  f.header.tileMerkleRoot = merkleRoot f.header.merkleDepth (frameLeaves f.header.ctx f.tiles) ∧
  verifyFrameHeader expectedPk f.header = true

def allDistinct {α : Type*} [DecidableEq α] : List α → Bool | [] => true | x :: r => (!r.contains x) && allDistinct r
def verifyFreshSalts (tiles : List RawSensorTile) : Bool :=
  tiles.all (fun t => decide (t.rawSalt.length = 32)) && allDistinct (tiles.map RawSensorTile.rawSalt)

/-! ## §4. Raw-Only Zero-Bystander-Leakage ROI Reveal & View-Independence -/

inductive RoiTileItem where | opened (pixels : List UInt8) (rawSalt : Salt256) | sealed (leaf : Digest) deriving DecidableEq, Repr
def RoiTileItem.leafOf (ctx : FrameContext) (idx : Nat) : RoiTileItem → Digest
  | .opened px rs => rawTileCommit ctx idx rs px | .sealed lf => lf
def roiItemOf (ctx : FrameContext) (inFrustum : Nat → Bool) (idx : Nat) (t : RawSensorTile) : RoiTileItem :=
  if inFrustum idx then .opened t.pixels t.rawSalt else .sealed (t.leaf ctx idx)
def roiViewItems (ctx : FrameContext) (inFrustum : Nat → Bool) (tiles : List RawSensorTile) : List RoiTileItem :=
  (List.range tiles.length).map fun i => roiItemOf ctx inFrustum i (tiles.getD i ⟨[], []⟩)
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
  exact (roiItemOf_leaf f.header.ctx inFrustum i (f.tiles.getD i ⟨[], []⟩)).symm
theorem bystander_salt_disclosed_iff_in_frustum (ctx : FrameContext) (inFrustum : Nat → Bool) (idx : Nat) (t : RawSensorTile) :
    (∃ p rs, roiItemOf ctx inFrustum idx t = .opened p rs) ↔ inFrustum idx = true := by unfold roiItemOf; cases inFrustum idx <;> simp

theorem unopened_bystander_tiles_hidden (f₁ f₂ : SealedSensorFrame) (inFrustum : Nat → Bool)
    (hctx : f₁.header.ctx = f₂.header.ctx) (hdep : f₁.header.merkleDepth = f₂.header.merkleDepth) (hlen : f₁.tiles.length = f₂.tiles.length)
    (hopen : ∀ i < f₁.tiles.length, inFrustum i = true → f₁.tiles.getD i ⟨[], []⟩ = f₂.tiles.getD i ⟨[], []⟩)
    (hsealed : ∀ j < f₁.tiles.length, inFrustum j = false →
      (f₁.tiles.getD j ⟨[], []⟩).leaf f₁.header.ctx j = (f₂.tiles.getD j ⟨[], []⟩).leaf f₂.header.ctx j) :
    roiView f₁ inFrustum = roiView f₂ inFrustum := by
  have hitems : roiViewItems f₁.header.ctx inFrustum f₁.tiles = roiViewItems f₂.header.ctx inFrustum f₂.tiles := by
    unfold roiViewItems; rw [hlen]; apply List.map_congr_left; intro i hi
    have hi2 : i < f₂.tiles.length := List.mem_range.mp hi; have hi1 : i < f₁.tiles.length := hlen ▸ hi2
    unfold roiItemOf; cases hvis : inFrustum i
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact congrArg RoiTileItem.sealed (hsealed i hi1 hvis)
    · simp only [↓reduceIte, hopen i hi1 hvis]
  have hr1 := roiView_root_recomputes f₁ inFrustum; have hr2 := roiView_root_recomputes f₂ inFrustum
  simp only [roiView] at hr1 hr2 ⊢; exact Prod.ext (by rw [hr1, hr2, hitems, hctx, hdep]) hitems

structure TileCommitScheme where
  commitTile : FrameContext → Nat → Salt256 → List UInt8 → Digest
def deployedTileScheme : TileCommitScheme where commitTile ctx idx rs pix := rawTileCommit ctx idx rs pix
def TileLeafHiding (S : TileCommitScheme) (Indist : (Salt256 → Digest) → (Salt256 → Digest) → Prop) : Prop :=
  ∀ (ctx : FrameContext) (idx : Nat) (p₁ p₂ : List UInt8), Indist (fun rs => S.commitTile ctx idx rs p₁) (fun rs => S.commitTile ctx idx rs p₂)
theorem unopened_bystander_tiles_hidden_fresh_salts (Indist : (Salt256 → Digest) → (Salt256 → Digest) → Prop)
    (hHide : TileLeafHiding deployedTileScheme Indist) (ctx : FrameContext) (j : Nat) (origPix mutatedPix : List UInt8) :
    Indist (fun rs => deployedTileScheme.commitTile ctx j rs origPix) (fun rs => deployedTileScheme.commitTile ctx j rs mutatedPix) :=
  hHide ctx j origPix mutatedPix
def constTileScheme : TileCommitScheme where commitTile _ _ _ _ := List.replicate 32 0
def identityTileScheme : TileCommitScheme where commitTile _ _ _ pix := pix
theorem constTileScheme_hiding : TileLeafHiding constTileScheme (· = ·) := fun _ _ _ _ => rfl
theorem identityTileScheme_not_hiding : ¬ TileLeafHiding identityTileScheme (· = ·) := by
  intro h; have heq := congrFun (h ⟨0, 0, 0⟩ 0 [0] [1]) []; simp [identityTileScheme] at heq

structure RoiTileOpening where
  tileIdx    : Nat
  pixels     : List UInt8
  rawSalt    : Salt256
  merklePath : List Digest
  deriving DecidableEq, Repr
structure RoiRevealCert where
  openings : List RoiTileOpening
  deriving DecidableEq, Repr

def verifyRoiOpening (h : SensorFrameHeader) (o : RoiTileOpening) : Bool :=
  decide (o.tileIdx < h.gridWidth * h.gridHeight) && decide (o.rawSalt.length = 32) &&
  decide (o.pixels.length = h.tileLen) &&
  verifyMerklePath h.tileMerkleRoot h.merkleDepth o.tileIdx (rawTileCommit h.ctx o.tileIdx o.rawSalt o.pixels) o.merklePath
def verifyRoiRevealCert (expectedPk : EnclavePublicKey) (h : SensorFrameHeader) (c : RoiRevealCert) : Bool :=
  verifyFrameHeader expectedPk h && allDistinct (c.openings.map RoiTileOpening.tileIdx) && c.openings.all (verifyRoiOpening h)

theorem roi_reveal_sound_or_collision {expectedPk : EnclavePublicKey} {f : SealedSensorFrame}
    {cert : RoiRevealCert} (hf : f.Honest expectedPk) (hver : verifyRoiRevealCert expectedPk f.header cert = true) :
    (∀ o ∈ cert.openings, o.tileIdx < f.tiles.length ∧
      o.pixels = (f.tiles.getD o.tileIdx ⟨[], []⟩).pixels ∧ o.rawSalt = (f.tiles.getD o.tileIdx ⟨[], []⟩).rawSalt) ∨
    Cshake256Collision := by
  unfold verifyRoiRevealCert at hver; simp only [Bool.and_eq_true, List.all_eq_true] at hver
  rcases hver with ⟨⟨hfh, _⟩, hall⟩
  have htlLe : f.header.tileLen ≤ 65536 := (isPow2Le16_bounds (verifyFrameHeader_bodyBounded hfh).2.1).2
  by_cases hgood : ∀ o ∈ cert.openings, o.tileIdx < f.tiles.length ∧
      o.pixels = (f.tiles.getD o.tileIdx ⟨[], []⟩).pixels ∧ o.rawSalt = (f.tiles.getD o.tileIdx ⟨[], []⟩).rawSalt
  · exact Or.inl hgood
  · right; push Not at hgood; rcases hgood with ⟨o, hoMem, hbad⟩
    have hvo := hall o hoMem; unfold verifyRoiOpening at hvo; simp only [Bool.and_eq_true, decide_eq_true_eq] at hvo
    rcases hvo with ⟨⟨⟨hidxGrid, hrs32⟩, hlenEq⟩, hmpath⟩
    have hidx : o.tileIdx < f.tiles.length := by rw [hf.2.1]; exact hidxGrid
    have hwf := hf.2.2.2.2.1 (f.tiles.getD o.tileIdx ⟨[], []⟩) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]; exact List.getElem_mem hidx)
    rw [hf.2.2.2.2.2.1] at hmpath
    rcases merklePath_sound_or_collision (frameLeaves_all_len32 f.header.ctx f.tiles)
        (by rw [frameLeaves_length]; exact hidx) hmpath with hleafEq | hcoll
    · rw [frameLeaves_getD f.header.ctx f.tiles hidx] at hleafEq; unfold RawSensorTile.leaf at hleafEq
      have hiB : o.tileIdx < 4294967296 := by have := hf.2.2.2.1; omega
      rcases rawTileCommit_bind_or_collision hrs32 hwf.1 hf.1 hf.1 hiB hiB
          (by omega) (by have := hwf.2.2; omega) hleafEq with ⟨_, _, hrsEq, hpixEq⟩ | hcoll
      · exact False.elim (hbad hidx hpixEq hrsEq)
      · exact hcoll
    · exact hcoll

theorem tooth_synthetic_pixel_splice_refused {expectedPk : EnclavePublicKey} {f : SealedSensorFrame}
    {cert : RoiRevealCert} {o : RoiTileOpening} (hf : f.Honest expectedPk) (ho : o ∈ cert.openings)
    (hspliced : o.pixels ≠ (f.tiles.getD o.tileIdx ⟨[], []⟩).pixels) :
    verifyRoiRevealCert expectedPk f.header cert = false ∨ Cshake256Collision := by
  cases h : verifyRoiRevealCert expectedPk f.header cert
  · exact Or.inl rfl
  · rcases roi_reveal_sound_or_collision hf h with hok | hcoll
    · exact False.elim (hspliced (hok o ho).2.1)
    · exact Or.inr hcoll

theorem tooth_tile_coordinate_graft_refused {ctx : FrameContext} {i₁ i₂ : Nat} {s₁ s₂ : Salt256} {p₁ p₂ : List UInt8}
    (hctx : ctx.Bounded) (hs₁ : s₁.length = 32) (hs₂ : s₂.length = 32) (hi₁ : i₁ < 4294967296) (hi₂ : i₂ < 4294967296)
    (hl₁ : p₁.length < 4294967296) (hl₂ : p₂.length < 4294967296) (hne : i₁ ≠ i₂)
    (hgraft : rawTileCommit ctx i₁ s₁ p₁ = rawTileCommit ctx i₂ s₂ p₂) : Cshake256Collision := by
  rcases rawTileCommit_bind_or_collision hs₁ hs₂ hctx hctx hi₁ hi₂ hl₁ hl₂ hgraft with ⟨_, h, _, _⟩ | c
  · exact False.elim (hne h)
  · exact c

/-! ## §5. Boolean Remainder Range Check, Box-Blur Division, `BabyBearExt4` HVZK & `UD-100` -/

theorem boolean_bit_iff_zero_or_one (b : BabyBear) : b * (1 - b) = 0 ↔ b = 0 ∨ b = 1 := by
  constructor
  · intro h; rcases mul_eq_zero.mp h with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1).symm
  · rintro (rfl | rfl) <;> ring

def booleanBitsNat (m : Nat) (b : Fin m → BabyBear) : Nat := ∑ k : Fin m, 2 ^ k.val * (b k).val

private theorem sum_pow_two_lt : ∀ m : Nat, (∑ k : Fin m, 2 ^ k.val) + 1 = 2 ^ m
  | 0 => by simp
  | m + 1 => by
      rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
      have ih := sum_pow_two_lt m; rw [Nat.pow_succ]; omega

/-- `m` Boolean bit columns `b_k (1 - b_k) = 0` over `BabyBear` force `rem = ∑ 2^k b_k < 2^m`. -/
theorem booleanBitsNat_lt {m : Nat} (b : Fin m → BabyBear) (hbool : ∀ k : Fin m, b k * (1 - b k) = 0) :
    booleanBitsNat m b < 2 ^ m ∧
    ((booleanBitsNat m b : Nat) : BabyBear) = ∑ k : Fin m, (2 ^ k.val : BabyBear) * b k := by
  have hle1 : ∀ k : Fin m, (b k).val ≤ 1 := fun k => by
    rcases (boolean_bit_iff_zero_or_one (b k)).mp (hbool k) with h0 | h1
    · rw [h0]; simp
    · rw [h1]; decide
  have hlt : booleanBitsNat m b < 2 ^ m := by
    have hsumLe : booleanBitsNat m b ≤ ∑ k : Fin m, 2 ^ k.val :=
      Finset.sum_le_sum fun k _ => by simpa [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ k.val) (hle1 k)
    have := sum_pow_two_lt m; omega
  have hcast : ((booleanBitsNat m b : Nat) : BabyBear) = ∑ k : Fin m, (2 ^ k.val : BabyBear) * b k := by
    unfold booleanBitsNat; rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => by rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_zmod_val]
  exact ⟨hlt, hcast⟩

/-- **Exact Box-Blur Division Soundness (general `2^m` tile size, `m ≤ 16`).** -/
theorem blur_div_unique_pow2 {m : Nat} (hm : m ≤ 16) (pixels : List UInt8) (hlen : pixels.length = 2 ^ m)
    (B : Nat) (hB : B < 256) (b : Fin m → BabyBear) (hbool : ∀ k : Fin m, b k * (1 - b k) = 0)
    (heq : ((sumBytes pixels : Nat) : BabyBear) =
      ((2 ^ m : Nat) : BabyBear) * (B : BabyBear) + ∑ k : Fin m, (2 ^ k.val : BabyBear) * b k) :
    2 ^ m * B + booleanBitsNat m b = sumBytes pixels ∧ booleanBitsNat m b < 2 ^ m ∧ B = sumBytes pixels / 2 ^ m := by
  rcases booleanBitsNat_lt b hbool with ⟨hremLt, hremCast⟩
  have hpowLe : 2 ^ m ≤ 65536 := le_trans (Nat.pow_le_pow_right (by omega) hm) (by norm_num)
  have hsumLt : sumBytes pixels < babyBearP := by have := sumBytes_le pixels; rw [hlen] at this; unfold babyBearP; omega
  have hrhsLt : 2 ^ m * B + booleanBitsNat m b < babyBearP := by
    have : 2 ^ m * B ≤ 65536 * 255 := by nlinarith
    unfold babyBearP; omega
  have hcastEq : ((sumBytes pixels : Nat) : BabyBear) = (((2 ^ m * B + booleanBitsNat m b : Nat) : BabyBear)) := by
    rw [heq, ← hremCast]; push_cast; rfl
  have hnatEq : 2 ^ m * B + booleanBitsNat m b = sumBytes pixels := by
    have hv := congrArg ZMod.val hcastEq
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hsumLt, Nat.mod_eq_of_lt hrhsLt] at hv; exact hv.symm
  have hpos : 0 < 2 ^ m := Nat.pow_pos (by omega)
  exact ⟨hnatEq, hremLt, by rw [← hnatEq, Nat.mul_add_div hpos, Nat.div_eq_of_lt hremLt, Nat.add_zero]⟩

/-- **Exact `16x16` (`256`-pixel) Box-Blur Soundness (`256 * B + rem = sum Raw ∧ rem < 256 -> B = sum / 256`).** -/
theorem blur_div_unique_of_boolean_rem (pixels : List UInt8) (hlen : pixels.length = 256)
    (B : Nat) (hB : B < 256) (b : Fin 8 → BabyBear) (hbool : ∀ k : Fin 8, b k * (1 - b k) = 0)
    (heq : ((sumBytes pixels : Nat) : BabyBear) =
      (256 : BabyBear) * (B : BabyBear) + ∑ k : Fin 8, (2 ^ k.val : BabyBear) * b k) :
    256 * B + booleanBitsNat 8 b = sumBytes pixels ∧ booleanBitsNat 8 b < 256 ∧ B = sumBytes pixels / 256 := by
  simpa using blur_div_unique_pow2 (m := 8) (by omega) pixels hlen B hB b hbool (by simpa using heq)

theorem tooth_unconstrained_rem_forges_blur_mean :
    ((25600 : Nat) : BabyBear) = (256 : BabyBear) * (99 : BabyBear) + (256 : BabyBear) ∧ (99 : Nat) ≠ 25600 / 256 := by
  constructor <;> decide

noncomputable instance instFintypeExt4 : Fintype Ext4 :=
  Fintype.ofEquiv (Fin Minidregg.Selvage.BabyBearExt4.extensionPolynomial.natDegree →
    Minidregg.Selvage.BabyBearExt4.BabyBear) coefficients.symm

theorem ext4_two_ne_zero : (2 : Ext4) ≠ 0 := by
  intro h
  have h2ne : (2 : Minidregg.Selvage.BabyBearExt4.BabyBear) ≠ 0 := by decide
  have hinj := RingHom.injective (algebraMap Minidregg.Selvage.BabyBearExt4.BabyBear Ext4)
  exact h2ne (hinj (by rw [map_ofNat, map_zero]; exact h))

/-- **Perfect HVZK Sumcheck Hiding over `BabyBearExt4` (`TVD = 0`).** -/
theorem ext4_hvzk_sumcheck_gap_zero {ℓ d tapes den : Nat} (hℓ : 1 ≤ ℓ) (hden : 0 < den)
    {ρ : Ext4} (hρ : ρ ≠ 0) (r : Fin ℓ → Ext4) (P₀ P₁ : TargetPoly ℓ d Ext4)
    (hpub : cubeSum (evalTargetPoly P₀) = cubeSum (evalTargetPoly P₁))
    (enum : Fin tapes ≃ MaskSpace ℓ d Ext4) (D : PublicGMaskView ℓ d Ext4 → Bool) :
    GapAtMost tapes 0 den (fun t => D (publicGMaskScaledView r ρ P₀ (enum t)))
      (fun t => D (publicGMaskScaledView r ρ P₁ (enum t))) :=
  hvzkSumcheck_publicGMask_scaled_gapAtMost_zero ext4_two_ne_zero hℓ hden hρ r P₀ P₁ hpub enum D

/-- **Query-Term Arithmetic (`rate = 1/4`, `q = 148`, `16`-bit PoW):** bare single-trial UDR
(`(5/8)^148 < 2^{-100}`, WITHOUT relying on PoW) AND `η = 1/32` slack work-adjusted
(`(21/32)^148 / 2^{16} < 2^{-100}`). *Scope:* query-arithmetic inequalities only; full composed
verifier ROM/FS/FRI/correlated-agreement (`[BCIKS20]` Thm 1.7) soundness is an `[OPEN]` seam. -/
theorem ud100_query_arithmetic_rate4_q148_pow16 :
    ((5 : ℚ) / 8) ^ 148 < (1 : ℚ) / (2 : ℚ) ^ 100 ∧
    ((21 : ℚ) / 32) ^ 148 / (2 : ℚ) ^ 16 < (1 : ℚ) / (2 : ℚ) ^ 100 := by
  constructor <;> norm_num

/-- **Query-Regime Tooth:** `q = 48` at `rate = 1/4` + `16`-bit PoW only reaches `48.55` bits in UDR. -/
theorem tooth_q48_rate4_not_ud100 : (1 : ℚ) / (2 : ℚ) ^ 50 < ((5 : ℚ) / 8) ^ 48 / (2 : ℚ) ^ 16 := by norm_num

/-! ## §6. `#tooth` Refutation of v1 Cleartext `tile_sum` Theater vs v2 `AmbientEnvelopeZkProof` -/

abbrev V1CleartextTranscript := List Nat × List BabyBear
def v1FrameASums : List Nat := [25600, 0]
def v1FrameBSums : List Nat := [12800, 12800]

noncomputable def ambientTargetA : TargetPoly 1 2 Ext4 :=
  fun e => if e 0 = 0 then (25600 : Ext4) else if e 0 = 1 then -(25600 : Ext4) else 0
noncomputable def ambientTargetB : TargetPoly 1 2 Ext4 :=
  fun e => if e 0 = 0 then (12800 : Ext4) else 0

private theorem cubeSum_ell1_d2 (P : TargetPoly 1 2 Ext4) :
    cubeSum (evalTargetPoly P) =
      2 * P (fun _ => 0) + P (fun _ => 1) + P (fun _ => 2) := by
  unfold cubeSum evalTargetPoly
  let eb : (Fin 1 → Bool) ≃ Bool := Equiv.funUnique (Fin 1) Bool
  let e3 : (Fin 1 → Fin 3) ≃ Fin 3 := Equiv.funUnique (Fin 1) (Fin 3)
  rw [Fintype.sum_equiv eb _ (fun b => ∑ e : Fin 1 → Fin 3, P e * ∏ j : Fin 1, (Theory.SumcheckHvzkMask.bitVal b : Ext4) ^ (e j : Nat))
      (fun x => Finset.sum_congr rfl fun e _ => by
        rw [Fin.prod_univ_one, Fin.prod_univ_one]; rfl),
    Fintype.sum_bool]
  have h1 : ∀ y : Ext4, (∑ e : Fin 1 → Fin 3, P e * ∏ j : Fin 1, y ^ (e j : Nat)) =
      P (fun _ => 0) + P (fun _ => 1) * y + P (fun _ => 2) * y ^ 2 := fun y => by
    rw [Fintype.sum_equiv e3 _ (fun k : Fin 3 => P (fun _ => k) * y ^ (k : Nat)) (fun e => by
      have he : e = fun _ => e 0 := by funext i; fin_cases i; rfl
      have he3 : e3 e = e 0 := rfl
      rw [he3, Fin.prod_univ_one]; conv_lhs => rw [he])]
    rw [Fin.sum_univ_three]; simp [add_assoc]
  simp only [Theory.SumcheckHvzkMask.bitVal_true, Theory.SumcheckHvzkMask.bitVal_false, h1]; ring

/-- **`#tooth` `[REFUTED: v1 BlurTileEntry cleartext tile_sum]` (`tooth_cleartext_tile_sum_leaks_spatial_luminance`):**
Two 2-tile frames with identical ambient total `25600` (`[25600, 0]` vs `[12800, 12800]`):
1. In v1 (`BlurTileEntry`), cleartext `tile_sum` yields advantage-`1` distinguishable transcripts
   under ANY zero-sum `masked_terms` (`¬ GapAtMost` for every `num < den`).
2. In v2 (`AmbientEnvelopeZkProof` over `BabyBearExt4.Ext4`), `GMaskExt4` yields exact `TVD = 0`
   witness-indistinguishability (`GapAtMost tapes 0 den`) against every distinguisher `D_v2`. -/
theorem tooth_cleartext_tile_sum_leaks_spatial_luminance
    {tapes num den : Nat} (hsmall : num < den) (maskA maskB : Fin tapes → List BabyBear)
    {ρ : Ext4} (hρ : ρ ≠ 0) (r : Fin 1 → Ext4)
    (enum : Fin tapes ≃ MaskSpace 1 2 Ext4) (D_v2 : PublicGMaskView 1 2 Ext4 → Bool) :
    (v1FrameASums.sum = 25600 ∧ v1FrameBSums.sum = 25600) ∧
    (∃ D_v1 : V1CleartextTranscript → Bool,
      ¬ GapAtMost tapes num den (fun t => D_v1 (v1FrameASums, maskA t)) (fun t => D_v1 (v1FrameBSums, maskB t))) ∧
    GapAtMost tapes 0 den (fun t => D_v2 (publicGMaskScaledView r ρ ambientTargetA (enum t)))
      (fun t => D_v2 (publicGMaskScaledView r ρ ambientTargetB (enum t))) := by
  refine ⟨by decide, ⟨fun tr => decide (tr.1 = v1FrameASums),
    not_gapAtMost_of_separating hsmall (fun _ => by simp) (fun _ => by simp [v1FrameASums, v1FrameBSums])⟩, ?_⟩
  refine ext4_hvzk_sumcheck_gap_zero (by omega) (by omega) hρ r ambientTargetA ambientTargetB ?_ enum D_v2
  rw [cubeSum_ell1_d2, cubeSum_ell1_d2]; simp only [ambientTargetA, ambientTargetB]; norm_num

def demoSalt (base : Nat) : Salt256 := (List.range 32).map fun i => UInt8.ofNat (base + i)
theorem tooth_unmasked_salt_reuse_refused :
    verifyFreshSalts [⟨[1, 2], demoSalt 0x10⟩, ⟨[3, 4], demoSalt 0x10⟩] = false ∧
    verifyFreshSalts [⟨[1, 2], demoSalt 0x10⟩, ⟨[3, 4], demoSalt 0x50⟩] = true := by decide

/-! ## §7. Concrete v2 Asymmetric-PQ Conformance Witness + JSON Emitter -/

def demoWotsSeedCsi2  : List UInt8   := (List.range 32).map fun i => UInt8.ofNat (0xA5 + i)
def demoWotsSeedAudio : List UInt8   := (List.range 32).map fun i => UInt8.ofNat (0x5A + i)
def demoRtRawCsi2     : Digest       := cshake256Bytes (asciiBytes "MINIDREGG/SENSORY_ROI/DEMO_RT_RAW/CSI2/V2") [1]
def demoRtRawAudio    : Digest       := cshake256Bytes (asciiBytes "MINIDREGG/SENSORY_ROI/DEMO_RT_RAW/AUDIO/V2") [2]
def demoCsi2Ctx       : FrameContext := ⟨0x4550495048414E59, 42, 1732234567000000000⟩
def demoAudioCtx      : FrameContext := ⟨0x4932535F41554449, 99, 1732234567016666666⟩
def mkSamples (len base step m : Nat) : List UInt8 := (List.range len).map fun k => UInt8.ofNat ((base + k * step) % m)

def demoCsi2Tiles : List RawSensorTile :=
  [⟨mkSamples 256 40 1 256, demoSalt 0x10⟩, ⟨mkSamples 256 120 3 256, demoSalt 0x50⟩,
   ⟨mkSamples 256 20 5 256, demoSalt 0x90⟩, ⟨mkSamples 256 180 7 256, demoSalt 0xD0⟩]
def demoAudioTiles : List RawSensorTile :=
  [⟨mkSamples 64 10 1 128, demoSalt 0x30⟩, ⟨mkSamples 64 25 2 128, demoSalt 0x70⟩]

private def hexBytes (bytes : List UInt8) : String :=
  String.join (bytes.map fun b => let d := "0123456789abcdef".toList; String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])
private def jBool (b : Bool) : String := if b then "true" else "false"
private def jStrs (xs : List String) : String := "[" ++ String.intercalate ", " (xs.map fun s => "\"" ++ s ++ "\"") ++ "]"
private def jNats (xs : List Nat) : String := "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

private def emitSensoryRoiConformance (path : System.FilePath) : IO Unit := do
  let f := sealSensorFrameWots demoWotsSeedCsi2 demoCsi2Ctx 2 2 256 2 .csi2Tile16x16 demoRtRawCsi2 demoCsi2Tiles
  let epkC : EnclavePublicKey := ⟨wotsPk demoWotsSeedCsi2, 0⟩
  let lvs := frameLeaves demoCsi2Ctx demoCsi2Tiles
  let t0 := demoCsi2Tiles[0]!; let p0 := openMerklePath 2 0 lvs
  let roiCert : RoiRevealCert := ⟨[⟨0, t0.pixels, t0.rawSalt, p0⟩]⟩
  let okHdr := verifyFrameHeader epkC f.header; let okRoi := verifyRoiRevealCert epkC f.header roiCert
  let spliced := match t0.pixels with | [] => [] | b :: r => (b + 1) :: r
  let badSplice := !verifyRoiRevealCert epkC f.header ⟨[⟨0, spliced, t0.rawSalt, p0⟩]⟩
  let badReplay := !verifyRoiRevealCert epkC { f.header with ctx := { f.header.ctx with timestampNs := f.header.ctx.timestampNs + 1 } } roiCert
  let badSigBytes := match f.header.wotsSig with | [] => [] | b :: r => (b + 1) :: r
  let badSig := !verifyFrameHeader epkC { f.header with wotsSig := badSigBytes }
  let sumsC := demoCsi2Tiles.map fun t => sumBytes t.pixels
  let meansC := sumsC.map fun s => s / 256; let remsC := sumsC.map fun s => s % 256
  let okBlurDiv := (List.zip sumsC (List.zip meansC remsC)).all fun (s, (m, r)) => decide (256 * m + r = s && r < 256 && m < 256)
  let af := sealSensorFrameWots demoWotsSeedAudio demoAudioCtx 2 1 64 1 .i2sAudioWindow demoRtRawAudio demoAudioTiles
  let epkA : EnclavePublicKey := ⟨wotsPk demoWotsSeedAudio, 0⟩
  let okAudioHdr := verifyFrameHeader epkA af.header
  let audioTotal := (demoAudioTiles.map fun t => sumBytes t.pixels).sum
  let okSalts := verifyFreshSalts demoCsi2Tiles && verifyFreshSalts demoAudioTiles
  unless okHdr && okRoi && badSplice && badReplay && badSig && okBlurDiv && okAudioHdr && okSalts do
    throw (IO.userError "SensoryRoiZeroKnowledge v2 self-check failed")
  let json :=
    "{\n  \"schema\": \"minidregg.sensory_roi_conformance.v2\", \"source\": \"Assurance/SensoryRoiZeroKnowledge.lean\",\n" ++
    s!"  \"empty_leaf_hex\": \"{hexBytes emptyLeaf}\",\n  \"csi2_frame\": \{\n" ++
    s!"    \"wots_seed_hex\": \"{hexBytes demoWotsSeedCsi2}\", \"enclave_pk_hex\": \"{hexBytes epkC.root}\",\n" ++
    s!"    \"sensor_id\": {demoCsi2Ctx.sensorId}, \"frame_seq\": {demoCsi2Ctx.frameSeq}, \"timestamp_ns\": {demoCsi2Ctx.timestampNs},\n" ++
    s!"    \"grid_width\": 2, \"grid_height\": 2, \"tile_len\": 256, \"merkle_depth\": 2,\n" ++
    s!"    \"tile_merkle_root_hex\": \"{hexBytes f.header.tileMerkleRoot}\", \"rt_raw_hex\": \"{hexBytes demoRtRawCsi2}\",\n" ++
    s!"    \"signing_payload_hex\": \"{hexBytes (headerSigningPayload f.header)}\", \"wots_sig_hex\": \"{hexBytes f.header.wotsSig}\",\n" ++
    s!"    \"raw_commits_hex\": {jStrs (lvs.map hexBytes)}, \"tiles_pixels_hex\": {jStrs (demoCsi2Tiles.map fun t => hexBytes t.pixels)},\n" ++
    s!"    \"tiles_raw_salts_hex\": {jStrs (demoCsi2Tiles.map fun t => hexBytes t.rawSalt)}, \"roi_tile0_path_hex\": {jStrs (p0.map hexBytes)},\n" ++
    s!"    \"expected_blur_means\": {jNats meansC}, \"expected_ambient_total\": {sumsC.sum}\n  },\n  \"i2s_audio_frame\": \{\n" ++
    s!"    \"wots_seed_hex\": \"{hexBytes demoWotsSeedAudio}\", \"enclave_pk_hex\": \"{hexBytes epkA.root}\",\n" ++
    s!"    \"sensor_id\": {demoAudioCtx.sensorId}, \"frame_seq\": {demoAudioCtx.frameSeq}, \"timestamp_ns\": {demoAudioCtx.timestampNs},\n" ++
    s!"    \"grid_width\": 2, \"grid_height\": 1, \"tile_len\": 64, \"merkle_depth\": 1,\n" ++
    s!"    \"tile_merkle_root_hex\": \"{hexBytes af.header.tileMerkleRoot}\", \"rt_raw_hex\": \"{hexBytes demoRtRawAudio}\",\n" ++
    s!"    \"signing_payload_hex\": \"{hexBytes (headerSigningPayload af.header)}\", \"wots_sig_hex\": \"{hexBytes af.header.wotsSig}\",\n" ++
    s!"    \"windows_pixels_hex\": {jStrs (demoAudioTiles.map fun t => hexBytes t.pixels)}, \"windows_raw_salts_hex\": {jStrs (demoAudioTiles.map fun t => hexBytes t.rawSalt)},\n" ++
    s!"    \"expected_ambient_total\": {audioTotal}\n  },\n  \"lean_self_checks\": \{\n" ++
    s!"    \"wots_header_ok\": {jBool (okHdr && okAudioHdr)}, \"roi_ok\": {jBool okRoi}, \"splice_refused\": {jBool badSplice},\n" ++
    s!"    \"replay_refused\": {jBool badReplay}, \"forged_sig_refused\": {jBool badSig}, \"blur_div_ok\": {jBool okBlurDiv}, \"fresh_salts_ok\": {jBool okSalts}\n  }\n}\n"
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path json

#eval emitSensoryRoiConformance "prover/testdata/sensory_roi_conformance.json"

/-! ## §8. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.verifyFrameHeader_wots_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyFrameHeader_wots_complete
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.header_unforgeable_without_sk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms header_unforgeable_without_sk
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.header_unforgeable_xmss_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms header_unforgeable_xmss_or_collision
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_cross_timestamp_replay_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_cross_timestamp_replay_refused
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.merklePath_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merklePath_sound_or_collision
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.unopened_bystander_tiles_hidden' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unopened_bystander_tiles_hidden
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.roi_reveal_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms roi_reveal_sound_or_collision
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.blur_div_unique_of_boolean_rem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms blur_div_unique_of_boolean_rem
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_unconstrained_rem_forges_blur_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_unconstrained_rem_forges_blur_mean
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.ext4_hvzk_sumcheck_gap_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ext4_hvzk_sumcheck_gap_zero
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.ud100_query_arithmetic_rate4_q148_pow16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ud100_query_arithmetic_rate4_q148_pow16
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_q48_rate4_not_ud100' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_q48_rate4_not_ud100
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_cleartext_tile_sum_leaks_spatial_luminance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_cleartext_tile_sum_leaks_spatial_luminance
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_synthetic_pixel_splice_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_synthetic_pixel_splice_refused
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_tile_coordinate_graft_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_tile_coordinate_graft_refused
/-- info: 'Minidregg.Assurance.SensoryRoiZeroKnowledge.tooth_unmasked_salt_reuse_refused' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms tooth_unmasked_salt_reuse_refused

end Minidregg.Assurance.SensoryRoiZeroKnowledge
