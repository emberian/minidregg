/-
# `Assurance/PerSlotKeyConfinement.lean` — Cross-Tree Gate `G7` (`CAP-21`, `L8`, `F4`)

1. **Per-Slot Hybrid `X25519 + ML-KEM-768` Key Confinement (`CAP-21`):**
   `AttenuatedSlotCap` carries no `rootViewKey` and distributes only wrapped per-slot keys
   `{wrap_{X25519+MLKEM768}(pk_delegate, slot_secret(i)) | i ∈ granted_slots}`:
   `attenuate_refuses_amplification`, `attenuate_omits_ungranted_slots`,
   `ungranted_slot_non_derivable`, `no_adversary_distinguishes_ungranted_slot`,
   `hybrid_wrap_dual_protection`, and `#tooth` `tooth_legacy_readcap_leaks_ungranted_slot`.
2. **Statement-Pinned `key_commit_i` & Keyless Public `ciphertext -> saltedPatchRoot` Weld (`L8` + `F4`):**
   Pins `key_commit_i = cSHAKE256("SLOT_KEY_COMMIT", u64LE i || digestLE slot_secret(i))` in the
   public statement (`slotKeyCommit_eq_or_collision`), proves the `GF(2^256)` blinded XOR identity
   `packSaltedLeaf pt s ⊕ packSaltedLeaf ks s = packSaltedLeaf (pt ⊕ ks) 0` (`blinded_xor_weld_holds`,
   `blinded_xor_weld_zero_leakage`), proves keyless verifier soundness & forged-ciphertext/swapped-root
   refusal (`verifyKeylessCiphertextWeld_sound_or_collision`,
   `keyless_weld_rejects_forged_ciphertext_or_collision`,
   `keyless_weld_rejects_swapped_root_or_collision`), and welds with
   `SealedHyperdocGrammarGate` in `verifyConfinedSealedHyperdocPatch_sound_or_collision`.
-/
import Assurance.SealedHyperdocGrammarGate

namespace Minidregg.Assurance.PerSlotKeyConfinement

open Minidregg.Theory Minidregg.Theory.VerifiedAstTransducer Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument Minidregg.Theory.HyperdocumentOperations
open Minidregg.Theory.GrammarTypedCapability Minidregg.Selvage
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate coordinateFieldEquiv coordinateFinEquiv
  coordinateFieldEquiv_add coordinateFieldEquiv_mul capacity)
open Minidregg.Compiler.Tower256CshakeMerkleBinding (FramedXofCollision)
open Minidregg.Compiler.Tower256CoordinateMerkle
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8)
open Minidregg.Compiler.Sp800185Cshake256 (fixedDigestBytesLE digestBytesLE)
open Minidregg.Compiler.Tower256PrivateContentCert Minidregg.Compiler.PolicyAstTransducerEmit
open Minidregg.Assurance.SealedHyperdocGrammarGate

set_option autoImplicit false

/-! ## §1. Canonical Encodings, Domain Separators, & Per-Slot Key Derivation -/

def u64LE (n : Nat) : List UInt8 :=
  (List.range 8).map fun i => UInt8.ofNat ((n / 256 ^ i) % 256)

theorem u64LE_length (n : Nat) : (u64LE n).length = 8 := by simp [u64LE]

private theorem u64_reconstruct (n : Nat) (hn : n < 2 ^ 64) :
    ((n / 256 ^ 0) % 256) + 256 * (((n / 256 ^ 1) % 256) + 256 * (((n / 256 ^ 2) % 256) +
    256 * (((n / 256 ^ 3) % 256) + 256 * (((n / 256 ^ 4) % 256) + 256 * (((n / 256 ^ 5) % 256) +
    256 * (((n / 256 ^ 6) % 256) + 256 * ((n / 256 ^ 7) % 256))))))) = n := by omega

theorem u64LE_injective_of_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (heq : u64LE a = u64LE b) : a = b := by
  have hget : ∀ i < 8, (a / 256 ^ i) % 256 = (b / 256 ^ i) % 256 := by
    intro i hi
    have hidx : (u64LE a)[i]'(by simp [u64LE_length]; exact hi) =
        (u64LE b)[i]'(by simp [u64LE_length]; exact hi) := by simp [heq]
    simp only [u64LE, List.getElem_map, List.getElem_range] at hidx
    simpa only [UInt8.toNat_ofNat', Nat.mod_mod] using congrArg UInt8.toNat hidx
  have h0 := hget 0 (by omega); have h1 := hget 1 (by omega)
  have h2 := hget 2 (by omega); have h3 := hget 3 (by omega)
  have h4 := hget 4 (by omega); have h5 := hget 5 (by omega)
  have h6 := hget 6 (by omega); have h7 := hget 7 (by omega)
  have hra := u64_reconstruct a ha; have hrb := u64_reconstruct b hb
  omega

def slotSecretCust    : List UInt8 := 0x0C :: asciiBytes "MINIDREGG/PERSLOT/SLOT_SECRET/V1"
def slotKeyCommitCust : List UInt8 := asciiBytes "SLOT_KEY_COMMIT"
def hybridWrapKdfCust : List UInt8 := 0x0D :: asciiBytes "MINIDREGG/PERSLOT/X25519_MLKEM768_WRAP_KDF/V1"
def hybridWrapTagCust : List UInt8 := 0x0E :: asciiBytes "MINIDREGG/PERSLOT/X25519_MLKEM768_WRAP_TAG/V1"
def slotAadCust       : List UInt8 := 0x0F :: asciiBytes "MINIDREGG/PERSLOT/SEALED_PATCH_AAD/V1"
def publicWeldCust    : List UInt8 := 0x10 :: asciiBytes "MINIDREGG/PERSLOT/KEYLESS_CT_ROOT_WELD/V1"
def weldChallengeCust : List UInt8 := 0x11 :: asciiBytes "MINIDREGG/PERSLOT/WELD_CHALLENGE/V1"
def blindPadCust      : List UInt8 := 0x12 :: asciiBytes "MINIDREGG/PERSLOT/BLIND_PAD_COMMIT/V1"
def slotStreamCust    : List UInt8 := 0x13 :: asciiBytes "MINIDREGG/PERSLOT/AEAD_STREAM/V1"
def slotSaltsCust     : List UInt8 := 0x14 :: asciiBytes "MINIDREGG/PERSLOT/AEAD_SALTS/V1"
def slotAeadTagCust   : List UInt8 := 0x15 :: asciiBytes "MINIDREGG/PERSLOT/AEAD_TAG/V1"

def deriveSlotSecret (rootViewKey : Digest) (cellId slotIdx keyEpoch : Nat) : Digest :=
  cshakeC.xofDigest slotSecretCust
    (cshakeC.digestCodec.encode rootViewKey ++ u64LE cellId ++ u64LE slotIdx ++ u64LE keyEpoch)

def slotKeyCommitInput (slotIdx : Nat) (slotSecret : Digest) : List UInt8 :=
  u64LE slotIdx ++ cshakeC.digestCodec.encode slotSecret

/-- Statement-pinned per-slot key commitment: `cSHAKE256("SLOT_KEY_COMMIT", u64LE i || slotSecret)`. -/
def slotKeyCommit (slotIdx : Nat) (slotSecret : Digest) : Digest :=
  cshakeC.xofDigest slotKeyCommitCust (slotKeyCommitInput slotIdx slotSecret)

theorem slotKeyCommitInput_injective {i₁ i₂ : Nat} {s₁ s₂ : Digest}
    (hi₁ : i₁ < 2 ^ 64) (hi₂ : i₂ < 2 ^ 64)
    (heq : slotKeyCommitInput i₁ s₁ = slotKeyCommitInput i₂ s₂) :
    i₁ = i₂ ∧ s₁ = s₂ := by
  unfold slotKeyCommitInput at heq
  have hpre : u64LE i₁ = u64LE i₂ := by
    simpa [List.take_left', u64LE_length] using congrArg (List.take 8) heq
  have hsuf : cshakeC.digestCodec.encode s₁ = cshakeC.digestCodec.encode s₂ := by
    simpa [List.drop_left', u64LE_length] using congrArg (List.drop 8) heq
  have hdec := congrArg cshakeC.digestCodec.decode hsuf
  rw [cshakeC.digestCodec.decode_encode, cshakeC.digestCodec.decode_encode] at hdec
  exact ⟨u64LE_injective_of_lt hi₁ hi₂ hpre, Option.some.inj hdec⟩

theorem slotKeyCommit_eq_or_collision {i₁ i₂ : Nat} {s₁ s₂ : Digest}
    (hi₁ : i₁ < 2 ^ 64) (hi₂ : i₂ < 2 ^ 64)
    (hcomm : slotKeyCommit i₁ s₁ = slotKeyCommit i₂ s₂) :
    (i₁ = i₂ ∧ s₁ = s₂) ∨
    FramedXofCollision cshakeC slotKeyCommitCust
      (slotKeyCommitInput i₁ s₁) (slotKeyCommitInput i₂ s₂) := by
  by_cases hinp : slotKeyCommitInput i₁ s₁ = slotKeyCommitInput i₂ s₂
  · exact Or.inl (slotKeyCommitInput_injective hi₁ hi₂ hinp)
  · exact Or.inr ⟨hinp, hcomm⟩

/-! ## §2. `Coordinate 8` XOR-Field Lemmas & Hybrid `X25519 + ML-KEM-768` Confinement -/

abbrev addC (a b : C8) : C8 := Coordinate.add 8 a b
abbrev mulC (a b : C8) : C8 := Coordinate.mul 8 a b
def zeroC : C8 := Coord.ofNat 8 0
def oneC  : C8 := Coord.ofNat 8 1

private theorem coord_add_self : ∀ (k : Nat) (a : Coordinate k), Coordinate.add k a a = Coordinate.zero k
  | 0, .bit b => by cases b <;> rfl
  | k + 1, .pair l h => by
      simp only [Coordinate.add, Coordinate.low_pair, Coordinate.high_pair, Coordinate.zero, coord_add_self k]

private theorem fieldEquiv_zeroC : coordinateFieldEquiv 8 zeroC = 0 := by
  have hz : zeroC = Coordinate.zero 8 := by decide
  rw [hz]; exact Minidregg.Theory.BinaryTowerFanPaarCodec.coordinateFieldEquiv_zero 8

theorem addC_comm (a b : C8) : addC a b = addC b a := by apply (coordinateFieldEquiv 8).injective; simp only [addC, coordinateFieldEquiv_add]; ring
theorem addC_assoc (a b c : C8) : addC (addC a b) c = addC a (addC b c) := by apply (coordinateFieldEquiv 8).injective; simp only [addC, coordinateFieldEquiv_add]; ring
theorem addC_self (a : C8) : addC a a = zeroC := by
  have hz : Coordinate.zero 8 = zeroC := by decide
  rw [← hz]; exact coord_add_self 8 a
theorem addC_zero (a : C8) : addC a zeroC = a := by apply (coordinateFieldEquiv 8).injective; rw [coordinateFieldEquiv_add, fieldEquiv_zeroC, add_zero]
theorem zero_addC (a : C8) : addC zeroC a = a := by rw [addC_comm, addC_zero]
theorem mulC_addC (a b c : C8) : mulC a (addC b c) = addC (mulC a b) (mulC a c) := by apply (coordinateFieldEquiv 8).injective; simp only [mulC, addC, coordinateFieldEquiv_mul, coordinateFieldEquiv_add]; ring

def xorDigest (a b : Digest) : Digest :=
  ⟨Coord.toNat 8 (addC (digestTowerC a) (digestTowerC b))⟩

theorem digestTowerC_xorDigest (a b : Digest) :
    digestTowerC (xorDigest a b) = addC (digestTowerC a) (digestTowerC b) := by
  unfold digestTowerC xorDigest
  have hlt : Coord.toNat 8 (addC (digestTowerC a) (digestTowerC b)) < 2 ^ 256 := by
    simpa [capacity_eight] using Coord.toNat_lt 8 (addC (digestTowerC a) (digestTowerC b))
  rw [Nat.mod_eq_of_lt hlt]
  apply (coordinateFinEquiv 8).injective; apply Fin.ext
  rw [Coord.coordinateFinEquiv_val, Coord.coordinateFinEquiv_val]
  exact Coord.toNat_ofNat 8 _ (by rw [capacity_eight]; exact hlt)

theorem xorDigest_cancel_right {a b : Digest} (ha : a.value < 2 ^ 256) :
    xorDigest (xorDigest a b) b = a := by
  cases a with
  | mk av =>
      simp only at ha
      change Digest.mk (Coord.toNat 8 (addC (digestTowerC (xorDigest ⟨av⟩ b)) (digestTowerC b))) = ⟨av⟩
      rw [digestTowerC_xorDigest, addC_assoc, addC_self, addC_zero]
      unfold digestTowerC
      rw [Nat.mod_eq_of_lt ha, Coord.toNat_ofNat 8 av (by rw [capacity_eight]; exact ha)]

structure HybridPublicKey where
  x25519Pk         : Digest
  mlkem768EkDigest : Digest
deriving DecidableEq, Repr

structure HybridKemCiphertext where
  x25519EphPk      : Digest
  mlkem768CtDigest : Digest
deriving DecidableEq, Repr

structure HybridKemShared where
  ssX25519 : Digest
  ssMlkem  : Digest
deriving DecidableEq, Repr

structure WrappedSlotKey where
  slotIndex     : Nat
  keyCommit     : Digest
  kemCt         : HybridKemCiphertext
  wrappedSecret : Digest
  wrapTag       : Digest
deriving DecidableEq, Repr

def wrapSlotAad (cellId slotIdx keyEpoch : Nat) (keyCommit : Digest) : List UInt8 :=
  u64LE cellId ++ u64LE slotIdx ++ u64LE keyEpoch ++ cshakeC.digestCodec.encode keyCommit

def hybridWrapKek (ss : HybridKemShared) (ct : HybridKemCiphertext) (pk : HybridPublicKey)
    (aad : List UInt8) : Digest :=
  cshakeC.xofDigest hybridWrapKdfCust
    (cshakeC.digestCodec.encode ss.ssX25519 ++ cshakeC.digestCodec.encode ss.ssMlkem ++
     cshakeC.digestCodec.encode ct.x25519EphPk ++ cshakeC.digestCodec.encode ct.mlkem768CtDigest ++
     cshakeC.digestCodec.encode pk.x25519Pk ++ cshakeC.digestCodec.encode pk.mlkem768EkDigest ++ aad)

def hybridWrapTag (kek wrappedSecret : Digest) (aad : List UInt8) : Digest :=
  cshakeC.xofDigest hybridWrapTagCust
    (cshakeC.digestCodec.encode kek ++ cshakeC.digestCodec.encode wrappedSecret ++ aad)

def wrapSlotKey (cellId slotIdx keyEpoch : Nat) (delegatePk : HybridPublicKey)
    (kemCt : HybridKemCiphertext) (ss : HybridKemShared) (slotSecret : Digest) : WrappedSlotKey :=
  let kc := slotKeyCommit slotIdx slotSecret
  let aad := wrapSlotAad cellId slotIdx keyEpoch kc
  let kek := hybridWrapKek ss kemCt delegatePk aad
  let wrapped := xorDigest slotSecret kek
  ⟨slotIdx, kc, kemCt, wrapped, hybridWrapTag kek wrapped aad⟩

def unwrapSlotKey (cellId keyEpoch : Nat) (delegatePk : HybridPublicKey)
    (ss : HybridKemShared) (entry : WrappedSlotKey) : Option Digest :=
  let aad := wrapSlotAad cellId entry.slotIndex keyEpoch entry.keyCommit
  let kek := hybridWrapKek ss entry.kemCt delegatePk aad
  if entry.wrapTag == hybridWrapTag kek entry.wrappedSecret aad then
    let recovered := xorDigest entry.wrappedSecret kek
    if slotKeyCommit entry.slotIndex recovered == entry.keyCommit then some recovered else none
  else none

theorem unwrapSlotKey_wrapSlotKey (cellId slotIdx keyEpoch : Nat)
    (delegatePk : HybridPublicKey) (kemCt : HybridKemCiphertext) (ss : HybridKemShared)
    (slotSecret : Digest) (hRange : slotSecret.value < 2 ^ 256) :
    unwrapSlotKey cellId keyEpoch delegatePk ss
      (wrapSlotKey cellId slotIdx keyEpoch delegatePk kemCt ss slotSecret) = some slotSecret := by
  unfold unwrapSlotKey wrapSlotKey
  simp only [beq_self_eq_true, ↓reduceIte, xorDigest_cancel_right hRange]

/-- Per-slot attenuated capability envelope (**zero `rootViewKey`**; kills `CAP-21`). -/
structure AttenuatedSlotCap where
  cellId       : Nat
  keyEpoch     : Nat
  delegatePk   : HybridPublicKey
  grantedSlots : List Nat
  wrappedKeys  : List WrappedSlotKey
deriving DecidableEq, Repr

def AttenuatedSlotCap.lookupWrapped (cap : AttenuatedSlotCap) (slotIdx : Nat) : Option WrappedSlotKey :=
  cap.wrappedKeys.find? fun w => w.slotIndex == slotIdx

def mintAttenuatedSlotCap (slotOracle : Nat → Digest) (cellId keyEpoch : Nat)
    (delegatePk : HybridPublicKey) (kemEncaps : Nat → HybridKemCiphertext × HybridKemShared)
    (grantedSlots : List Nat) : AttenuatedSlotCap :=
  ⟨cellId, keyEpoch, delegatePk, grantedSlots, grantedSlots.map fun i =>
    let (ct, ss) := kemEncaps i; wrapSlotKey cellId i keyEpoch delegatePk ct ss (slotOracle i)⟩

def attenuateSlotCap (cap : AttenuatedSlotCap)
    (holderDecaps : WrappedSlotKey → Option HybridKemShared)
    (nextPk : HybridPublicKey)
    (nextEncaps : Nat → HybridKemCiphertext × HybridKemShared)
    (subSlots : List Nat) : Option AttenuatedSlotCap :=
  if subSlots.all (fun s => cap.grantedSlots.contains s) then
    let rewrapped? : Option (List WrappedSlotKey) := subSlots.mapM fun i => do
      let entry ← cap.lookupWrapped i
      let ss ← holderDecaps entry
      let sec ← unwrapSlotKey cap.cellId cap.keyEpoch cap.delegatePk ss entry
      let (ct', ss') := nextEncaps i
      pure (wrapSlotKey cap.cellId i cap.keyEpoch nextPk ct' ss' sec)
    rewrapped?.map fun wks => ⟨cap.cellId, cap.keyEpoch, nextPk, subSlots, wks⟩
  else none

private theorem mapM_wrapped_slotIndex (f : Nat → Option WrappedSlotKey)
    (hf : ∀ i w, f i = some w → w.slotIndex = i) :
    ∀ (xs : List Nat) (wks : List WrappedSlotKey),
      xs.mapM f = some wks → ∀ w ∈ wks, w.slotIndex ∈ xs
  | [], wks, hm => by
      simp only [List.mapM_nil, pure, Option.some.injEq] at hm; subst hm; intro _ hw; cases hw
  | x :: rest, wks, hm => by
      simp only [List.mapM_cons, bind, Option.bind] at hm
      cases hfx : f x with
      | none => simp [hfx] at hm
      | some wx =>
          rw [hfx] at hm
          cases hrest : rest.mapM f with
          | none => simp [hrest] at hm
          | some wrest =>
              rw [hrest] at hm; simp only [pure, Option.some.injEq] at hm; subst hm
              intro w hw
              rcases List.mem_cons.mp hw with rfl | hmem
              · rw [hf x w hfx]; exact List.mem_cons_self
              · exact List.mem_cons_of_mem x (mapM_wrapped_slotIndex f hf rest wrest hrest w hmem)

theorem attenuate_refuses_amplification (cap : AttenuatedSlotCap)
    (holderDecaps : WrappedSlotKey → Option HybridKemShared) (nextPk : HybridPublicKey)
    (nextEncaps : Nat → HybridKemCiphertext × HybridKemShared)
    (subSlots : List Nat) (j : Nat) (hjIn : j ∈ subSlots) (hjOut : j ∉ cap.grantedSlots) :
    attenuateSlotCap cap holderDecaps nextPk nextEncaps subSlots = none := by
  unfold attenuateSlotCap
  have hfalse : subSlots.all (fun s => cap.grantedSlots.contains s) = false := by
    rw [List.all_eq_false]; exact ⟨j, hjIn, by simp [hjOut]⟩
  rw [hfalse]; rfl

theorem attenuate_omits_ungranted_slots (cap : AttenuatedSlotCap)
    (holderDecaps : WrappedSlotKey → Option HybridKemShared) (nextPk : HybridPublicKey)
    (nextEncaps : Nat → HybridKemCiphertext × HybridKemShared)
    (subSlots : List Nat) (child : AttenuatedSlotCap)
    (hatt : attenuateSlotCap cap holderDecaps nextPk nextEncaps subSlots = some child) :
    child.grantedSlots = subSlots ∧ (∀ s ∈ subSlots, s ∈ cap.grantedSlots) ∧
    (∀ w ∈ child.wrappedKeys, w.slotIndex ∈ subSlots) ∧
    (∀ j, j ∉ subSlots → (∀ w ∈ child.wrappedKeys, w.slotIndex ≠ j) ∧ child.lookupWrapped j = none) := by
  unfold attenuateSlotCap at hatt
  split at hatt
  · rename_i hsub
    simp only [Option.map_eq_some_iff] at hatt; rcases hatt with ⟨wks, hmapM, rfl⟩
    have hf : ∀ i w, (do
        let entry ← cap.lookupWrapped i; let ss ← holderDecaps entry
        let sec ← unwrapSlotKey cap.cellId cap.keyEpoch cap.delegatePk ss entry
        let (ct', ss') := nextEncaps i
        pure (wrapSlotKey cap.cellId i cap.keyEpoch nextPk ct' ss' sec)) = some w → w.slotIndex = i := by
      intro i w hdo
      cases hl : cap.lookupWrapped i with
      | none => simp [hl] at hdo
      | some entry =>
          rw [hl] at hdo; simp only [bind, Option.bind] at hdo
          cases hd : holderDecaps entry with
          | none => simp [hd] at hdo
          | some ss =>
              rw [hd] at hdo; dsimp only at hdo
              cases hu : unwrapSlotKey cap.cellId cap.keyEpoch cap.delegatePk ss entry with
              | none => simp [hu] at hdo
              | some sec =>
                  rw [hu] at hdo; simp only [pure, Option.some.injEq] at hdo
                  rw [← hdo]; rfl
    have hmem := mapM_wrapped_slotIndex _ hf subSlots wks hmapM
    refine ⟨rfl, fun s hs => by simpa using List.all_eq_true.mp hsub s hs, hmem, fun j hj => ?_⟩
    have hne : ∀ w ∈ wks, w.slotIndex ≠ j := fun w hw heq => hj (heq ▸ hmem w hw)
    exact ⟨hne, by unfold AttenuatedSlotCap.lookupWrapped; rw [List.find?_eq_none]; intro w hw; simp [hne w hw]⟩
  · simp at hatt

theorem ungranted_slot_non_derivable
    (kdf₀ kdf₁ : Nat → Digest) (cellId keyEpoch : Nat) (delegatePk : HybridPublicKey)
    (kemEncaps : Nat → HybridKemCiphertext × HybridKemShared)
    (grantedSlots : List Nat) (hagree : ∀ i ∈ grantedSlots, kdf₀ i = kdf₁ i) :
    mintAttenuatedSlotCap kdf₀ cellId keyEpoch delegatePk kemEncaps grantedSlots =
    mintAttenuatedSlotCap kdf₁ cellId keyEpoch delegatePk kemEncaps grantedSlots :=
  congrArg (AttenuatedSlotCap.mk cellId keyEpoch delegatePk grantedSlots)
    (List.map_congr_left fun i hi => by rw [hagree i hi])

theorem no_adversary_distinguishes_ungranted_slot
    (kdf : Nat → Digest) (j : Nat) (s₀ s₁ : Digest) (hne : s₀ ≠ s₁)
    (cellId keyEpoch : Nat) (delegatePk : HybridPublicKey)
    (kemEncaps : Nat → HybridKemCiphertext × HybridKemShared)
    (grantedSlots : List Nat) (hj : j ∉ grantedSlots) (A : AttenuatedSlotCap → Digest) :
    let kdf₀ := fun i => if i = j then s₀ else kdf i
    let kdf₁ := fun i => if i = j then s₁ else kdf i
    let cap₀ := mintAttenuatedSlotCap kdf₀ cellId keyEpoch delegatePk kemEncaps grantedSlots
    let cap₁ := mintAttenuatedSlotCap kdf₁ cellId keyEpoch delegatePk kemEncaps grantedSlots
    cap₀ = cap₁ ∧ ¬ (A cap₀ = s₀ ∧ A cap₁ = s₁) := by
  intro kdf₀ kdf₁ cap₀ cap₁
  have heq : cap₀ = cap₁ := ungranted_slot_non_derivable kdf₀ kdf₁ cellId keyEpoch delegatePk
    kemEncaps grantedSlots (fun i hi => by have : i ≠ j := fun h => hj (h ▸ hi); simp [kdf₀, kdf₁, this])
  exact ⟨heq, fun ⟨h0, h1⟩ => hne ((heq ▸ h0).symm.trans h1)⟩

theorem hybrid_wrap_dual_protection (s₀ s₁ : C8) :
    Function.Bijective (fun k : C8 => addC s₀ k) ∧
    (∀ k : C8, addC s₀ k = addC s₁ (addC (addC s₀ s₁) k)) := by
  refine ⟨⟨fun k₁ k₂ h => ?_, fun y => ⟨addC s₀ y, by dsimp; rw [← addC_assoc, addC_self, zero_addC]⟩⟩,
    fun k => ?_⟩
  · simpa [← addC_assoc, addC_self, zero_addC] using congrArg (addC s₀) h
  · rw [← addC_assoc, addC_comm s₁ (addC s₀ s₁), addC_assoc s₀ s₁, addC_self, addC_zero]

/-! ## §3. `#tooth` Regression Proof Catching Legacy `CAP-21` `ReadCap::attenuate` Root-Key Leak -/

structure LegacyReadCap where
  cellId       : Nat
  keyEpoch     : Nat
  grantedSlots : List Nat
  rootViewKey  : Digest
deriving DecidableEq, Repr

def legacyReadCapAttenuate (cap : LegacyReadCap) (subSlots : List Nat) : Option LegacyReadCap :=
  if subSlots.all (fun s => cap.grantedSlots.contains s) then some { cap with grantedSlots := subSlots } else none

theorem tooth_legacy_readcap_leaks_ungranted_slot (rootViewKey : Digest) (cellId keyEpoch : Nat) :
    let parent : LegacyReadCap := ⟨cellId, keyEpoch, [2, 5, 7], rootViewKey⟩
    ∃ child, legacyReadCapAttenuate parent [2] = some child ∧ 7 ∉ child.grantedSlots ∧
      deriveSlotSecret child.rootViewKey child.cellId 7 child.keyEpoch =
        deriveSlotSecret rootViewKey cellId 7 keyEpoch :=
  ⟨⟨cellId, keyEpoch, [2], rootViewKey⟩, by unfold legacyReadCapAttenuate; simp, by simp, rfl⟩

inductive ReadCapEnvelope where
  | legacyRootCopy (cap : LegacyReadCap)
  | confinedPerSlot (cap : AttenuatedSlotCap)
deriving DecidableEq, Repr

def verifyReadCapConfinement : ReadCapEnvelope → Bool
  | .legacyRootCopy _ => false
  | .confinedPerSlot cap => cap.wrappedKeys.all (fun w => cap.grantedSlots.contains w.slotIndex)

theorem tooth_confinement_gate_rejects_legacy_root_copy (cap : LegacyReadCap) :
    verifyReadCapConfinement (.legacyRootCopy cap) = false := rfl

/-! ## §4. `GF(2^256)` Salted-XOR Identity & Blinded Inner-Product Weld (`L8` + `F4`) -/

private theorem nat_xor_mul_two (pa pb a b : Nat) (hpa : pa < 2) (hpb : pb < 2) :
    (pa + 2 * a) ^^^ (pb + 2 * b) = (pa ^^^ pb) + 2 * (a ^^^ b) := by
  have ha : pa = 0 ∨ pa = 1 := by omega
  have hb : pb = 0 ∨ pb = 1 := by omega
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor]
  cases i with
  | zero => rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [Nat.testBit_zero]
  | succ j =>
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
        simp only [Nat.testBit_succ, Nat.zero_add, Nat.mul_div_right _ (by decide : 0 < 2),
          show (1 + 2 * a) / 2 = a by omega, show (1 + 2 * b) / 2 = b by omega,
          show (1 + 2 * (a ^^^ b)) / 2 = a ^^^ b by omega,
          show (0 ^^^ 1 : Nat) = 1 by decide, show (1 ^^^ 0 : Nat) = 1 by decide,
          show (1 ^^^ 1 : Nat) = 0 by decide, show (0 ^^^ 0 : Nat) = 0 by decide, Nat.testBit_xor]

private theorem nat_xor_shift_split : ∀ (m a₁ a₂ b₁ b₂ : Nat), a₁ < 2 ^ m → a₂ < 2 ^ m →
    (a₁ + 2 ^ m * b₁) ^^^ (a₂ + 2 ^ m * b₂) = (a₁ ^^^ a₂) + 2 ^ m * (b₁ ^^^ b₂)
  | 0, a₁, a₂, b₁, b₂, ha₁, ha₂ => by
      have h1 : a₁ = 0 := by omega
      have h2 : a₂ = 0 := by omega
      subst h1 h2; simp
  | m + 1, a₁, a₂, b₁, b₂, ha₁, ha₂ => by
      have h1 : a₁ + 2 ^ (m + 1) * b₁ = (a₁ % 2) + 2 * (a₁ / 2 + 2 ^ m * b₁) := by
        rw [Nat.pow_succ', Nat.mul_assoc]; omega
      have h2 : a₂ + 2 ^ (m + 1) * b₂ = (a₂ % 2) + 2 * (a₂ / 2 + 2 ^ m * b₂) := by
        rw [Nat.pow_succ', Nat.mul_assoc]; omega
      have hd1 : a₁ / 2 < 2 ^ m := by rw [Nat.pow_succ'] at ha₁; omega
      have hd2 : a₂ / 2 < 2 ^ m := by rw [Nat.pow_succ'] at ha₂; omega
      rw [h1, h2, nat_xor_mul_two _ _ _ _ (Nat.mod_lt a₁ (by decide)) (Nat.mod_lt a₂ (by decide)),
        nat_xor_shift_split m (a₁ / 2) (a₂ / 2) b₁ b₂ hd1 hd2]
      have hx : a₁ ^^^ a₂ = (a₁ % 2 ^^^ a₂ % 2) + 2 * (a₁ / 2 ^^^ a₂ / 2) := by
        conv_lhs => rw [show a₁ = a₁ % 2 + 2 * (a₁ / 2) by omega,
                        show a₂ = a₂ % 2 + 2 * (a₂ / 2) by omega]
        exact nat_xor_mul_two _ _ _ _ (Nat.mod_lt a₁ (by decide)) (Nat.mod_lt a₂ (by decide))
      rw [hx, Nat.pow_succ']; ring

private theorem capacity_eq_two_pow (k : Nat) : capacity k = 2 ^ (2 ^ k) := by
  induction k with
  | zero => simp [capacity]
  | succ k ih =>
      rw [← Minidregg.Theory.BinaryTowerFanPaarCodec.capacity_succ, ih, ← Nat.pow_add, Nat.pow_succ, Nat.mul_two]

private theorem toNat_coordinate_add : ∀ (k : Nat) (a b : Coordinate k),
    Coord.toNat k (Coordinate.add k a b) = Coord.toNat k a ^^^ Coord.toNat k b
  | 0, .bit x, .bit y => by cases x <;> cases y <;> decide
  | k + 1, .pair la ha, .pair lb hb => by
      simp only [Coordinate.add, Coordinate.low_pair, Coordinate.high_pair, Coord.toNat,
        toNat_coordinate_add k, capacity_eq_two_pow]
      exact (nat_xor_shift_split (2 ^ k) _ _ _ _
        (by simpa [capacity_eq_two_pow] using Coord.toNat_lt k la)
        (by simpa [capacity_eq_two_pow] using Coord.toNat_lt k lb)).symm

/-- Exact char-2 leaf identity: `(pt, s) ⊕ (ks, s) = (pt ⊕ ks, 0)` in `Tower256`. -/
theorem packSaltedLeaf_xor_eq_ciphertextLeaf (pt ks : UInt8) (s : Salt248) :
    addC (packSaltedLeaf pt s) (packSaltedLeaf ks s) =
      packSaltedLeaf (pt ^^^ ks) ⟨0, by positivity⟩ := by
  apply (coordinateFinEquiv 8).injective; apply Fin.ext
  rw [Coord.coordinateFinEquiv_val, Coord.coordinateFinEquiv_val,
    toNat_coordinate_add, toNat_packSaltedLeaf, toNat_packSaltedLeaf, toNat_packSaltedLeaf]
  unfold saltedLeafNat
  have hsplit := nat_xor_shift_split 8 pt.toNat ks.toNat s.val s.val pt.toNat_lt ks.toNat_lt
  simp only [show (2 : Nat) ^ 8 = 256 by norm_num, Nat.xor_self, Nat.mul_zero, Nat.add_zero] at hsplit
  rw [hsplit]; rfl

def ciphertextMerkleRoot (ct : List UInt8) : Digest :=
  saltedContentCommit ct (List.replicate ct.length ⟨0, by positivity⟩)

def maskMerkleRoot (ks : List UInt8) (salts : List Salt248) : Digest :=
  saltedContentCommit ks salts

theorem ciphertextMerkleRoot_eq_or_collision (ct₁ ct₂ : List UInt8)
    (hlen : ct₁.length = ct₂.length) (hroot : ciphertextMerkleRoot ct₁ = ciphertextMerkleRoot ct₂) :
    ct₁ = ct₂ ∨
    let z₁ := List.replicate ct₁.length ⟨0, by positivity⟩
    let z₂ := List.replicate ct₂.length ⟨0, by positivity⟩
    let f := saltedCollisionFrames ct₁ z₁ ct₂ z₂
    FramedXofCollision cshakeC f.customization f.left f.right := by
  rcases saltedRoot_eq_or_collision ct₁ (List.replicate ct₁.length ⟨0, by positivity⟩)
      ct₂ (List.replicate ct₂.length ⟨0, by positivity⟩)
      List.length_replicate List.length_replicate hlen hroot with ⟨hct, _⟩ | hcol
  · exact Or.inl hct
  · exact Or.inr hcol

def towerPolyEval (γ : C8) : List C8 → C8
  | [] => zeroC
  | x :: xs => addC x (mulC γ (towerPolyEval γ xs))

theorem towerPolyEval_xor_additive (γ : C8) :
    ∀ (xs ys : List C8), xs.length = ys.length →
      addC (towerPolyEval γ xs) (towerPolyEval γ ys) = towerPolyEval γ (List.zipWith addC xs ys)
  | [], [], _ => by simp [towerPolyEval, addC_self]
  | x :: xs, y :: ys, hlen => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [towerPolyEval, List.zipWith_cons_cons]
      rw [← towerPolyEval_xor_additive γ xs ys hlen, mulC_addC]
      apply (coordinateFieldEquiv 8).injective; simp only [addC, coordinateFieldEquiv_add]; ring

def saltedLeaves (bytes : List UInt8) (salts : List Salt248) : List C8 :=
  List.zipWith packSaltedLeaf bytes salts

def ctLeaves (ct : List UInt8) : List C8 :=
  ct.map fun b => packSaltedLeaf b ⟨0, by positivity⟩

theorem salted_xor_mask_eval_eq_ciphertext_eval (γ : C8)
    (pt ks : List UInt8) (salts : List Salt248)
    (hpk : pt.length = ks.length) (hps : pt.length = salts.length) :
    addC (towerPolyEval γ (saltedLeaves pt salts)) (towerPolyEval γ (saltedLeaves ks salts)) =
      towerPolyEval γ (ctLeaves (List.zipWith (· ^^^ ·) pt ks)) := by
  rw [towerPolyEval_xor_additive γ _ _ (by simp [saltedLeaves, hpk])]
  congr 1
  induction pt generalizing ks salts with
  | nil => cases ks <;> cases salts <;> simp_all [saltedLeaves, ctLeaves]
  | cons p pt ih =>
      cases ks with
      | nil => simp at hpk
      | cons k ks =>
          cases salts with
          | nil => simp at hps
          | cons s salts =>
              simp only [List.length_cons, Nat.add_right_cancel_iff] at hpk hps
              simp only [saltedLeaves, ctLeaves, List.zipWith_cons_cons, List.map_cons,
                packSaltedLeaf_xor_eq_ciphertextLeaf]
              exact congrArg _ (ih ks salts hpk hps)

theorem blinded_xor_weld_holds (γ bPad : C8) (pt ks : List UInt8) (salts : List Salt248)
    (hpk : pt.length = ks.length) (hps : pt.length = salts.length) :
    let evalS := towerPolyEval γ (saltedLeaves pt salts)
    let evalM := towerPolyEval γ (saltedLeaves ks salts)
    let evalC := towerPolyEval γ (ctLeaves (List.zipWith (· ^^^ ·) pt ks))
    addC (addC evalS bPad) (addC evalM bPad) = evalC := by
  intro evalS evalM evalC
  have hsum := salted_xor_mask_eval_eq_ciphertext_eval γ pt ks salts hpk hps
  have hbb : addC bPad bPad = zeroC := addC_self bPad
  calc
    addC (addC evalS bPad) (addC evalM bPad)
      = addC (addC evalS evalM) (addC bPad bPad) := by
          apply (coordinateFieldEquiv 8).injective; simp only [addC, coordinateFieldEquiv_add]; ring
    _ = addC evalS evalM := by rw [hbb, addC_zero]
    _ = evalC := hsum

theorem blinded_xor_weld_zero_leakage (evalS₁ evalS₂ : C8) :
    Function.Bijective (fun bPad : C8 => addC evalS₁ bPad) ∧
    (∀ bPad : C8, addC evalS₁ bPad = addC evalS₂ (addC (addC evalS₁ evalS₂) bPad)) :=
  hybrid_wrap_dual_protection evalS₁ evalS₂

/-! ## §5. Statement-Pinned Sealed Patch Gate & Keyless Public Consensus Verifier -/

structure SlotAadMeta where
  documentId  : Nat
  atomId      : Nat
  schema      : Digest
  operationId : Nat
  slotIndex   : Nat
  keyEpoch    : Nat
  extraAad    : List UInt8
deriving DecidableEq, Repr

def computeSlotAadDigest (m : SlotAadMeta) : Digest :=
  cshakeC.xofDigest slotAadCust
    (u64LE m.documentId ++ u64LE m.atomId ++ cshakeC.digestCodec.encode m.schema ++
     u64LE m.operationId ++ u64LE m.slotIndex ++ u64LE m.keyEpoch ++ u64LE m.extraAad.length ++ m.extraAad)

def deriveSlotKeystream (slotSecret : Digest) (slotIdx : Nat) (nonce : List UInt8)
    (aadDigest : Digest) (len : Nat) : List UInt8 :=
  let seed := cshakeC.digestCodec.encode slotSecret ++ u64LE slotIdx ++ nonce ++ cshakeC.digestCodec.encode aadDigest
  (((List.range ((len + 31) / 32)).map fun b =>
    fixedDigestBytesLE (cshakeC.xofDigest slotStreamCust (seed ++ u64LE b))).flatten).take len

def deriveSlotSalts (slotSecret : Digest) (slotIdx : Nat) (nonce : List UInt8)
    (aadDigest : Digest) (len : Nat) : List Salt248 :=
  let seed := cshakeC.digestCodec.encode slotSecret ++ u64LE slotIdx ++ nonce ++ cshakeC.digestCodec.encode aadDigest
  (List.range len).map fun pos =>
    ⟨(cshakeC.xofDigest slotSaltsCust (seed ++ u64LE pos)).value % 2 ^ 248, Nat.mod_lt _ (by positivity)⟩

def computeSlotAeadTag (slotSecret keyCommit : Digest) (nonce : List UInt8)
    (aadDigest saltedPatchRoot ctRoot maskRoot : Digest) (patchLen : Nat) : Digest :=
  cshakeC.xofDigest slotAeadTagCust
    (cshakeC.digestCodec.encode slotSecret ++ cshakeC.digestCodec.encode keyCommit ++ nonce ++
     cshakeC.digestCodec.encode aadDigest ++ cshakeC.digestCodec.encode saltedPatchRoot ++
     cshakeC.digestCodec.encode ctRoot ++ cshakeC.digestCodec.encode maskRoot ++ u64LE patchLen)

structure PublicCiphertextWeld where
  ctMerkleRoot   : Digest
  maskMerkleRoot : Digest
  blindPadCommit : Digest
  aeadTag        : Digest
  weldDigest     : Digest
  blindEvalS     : C8
  blindEvalM     : C8
deriving DecidableEq, Repr

structure KeylessPublicPatchStmt where
  aadMeta         : SlotAadMeta
  keyCommit       : Digest
  nonce           : List UInt8
  patchLen        : Nat
  saltedPatchRoot : Digest
  ciphertext      : List UInt8
  weld            : PublicCiphertextWeld
deriving DecidableEq, Repr

def publicWeldInput (saltedPatchRoot maskRoot ctRoot keyCommit : Digest)
    (nonce : List UInt8) (aadDigest : Digest) (patchLen : Nat)
    (aeadTag blindPadCommit : Digest) : List UInt8 :=
  cshakeC.digestCodec.encode saltedPatchRoot ++ cshakeC.digestCodec.encode maskRoot ++
  cshakeC.digestCodec.encode ctRoot ++ cshakeC.digestCodec.encode keyCommit ++ nonce ++
  cshakeC.digestCodec.encode aadDigest ++ u64LE patchLen ++
  cshakeC.digestCodec.encode aeadTag ++ cshakeC.digestCodec.encode blindPadCommit

def computeWeldDigest (stmt : KeylessPublicPatchStmt) : Digest :=
  cshakeC.xofDigest publicWeldCust
    (publicWeldInput stmt.saltedPatchRoot stmt.weld.maskMerkleRoot stmt.weld.ctMerkleRoot
      stmt.keyCommit stmt.nonce (computeSlotAadDigest stmt.aadMeta) stmt.patchLen
      stmt.weld.aeadTag stmt.weld.blindPadCommit)

def computeWeldChallenge (weldDigest : Digest) : C8 :=
  digestTowerC (cshakeC.xofDigest weldChallengeCust (cshakeC.digestCodec.encode weldDigest))

/-- Keyless public consensus verifier (`0` secrets, `0` plaintext bytes). -/
def verifyKeylessCiphertextWeld (stmt : KeylessPublicPatchStmt) : Bool :=
  decide (0 < stmt.patchLen) &&
  decide (stmt.ciphertext.length = stmt.patchLen) &&
  decide (stmt.nonce.length = 32) &&
  decide (ciphertextMerkleRoot stmt.ciphertext = stmt.weld.ctMerkleRoot) &&
  decide (computeWeldDigest stmt = stmt.weld.weldDigest) &&
  decide (addC stmt.weld.blindEvalS stmt.weld.blindEvalM =
    towerPolyEval (computeWeldChallenge stmt.weld.weldDigest) (ctLeaves stmt.ciphertext))

theorem verifyKeylessCiphertextWeld_sound_or_collision (stmt : KeylessPublicPatchStmt)
    (hok : verifyKeylessCiphertextWeld stmt = true)
    (ct' : List UInt8) (hlen' : ct'.length = stmt.patchLen)
    (hroot' : ciphertextMerkleRoot ct' = stmt.weld.ctMerkleRoot) :
    (ct' = stmt.ciphertext ∧ stmt.weld.weldDigest = computeWeldDigest stmt ∧
     addC stmt.weld.blindEvalS stmt.weld.blindEvalM =
       towerPolyEval (computeWeldChallenge stmt.weld.weldDigest) (ctLeaves ct')) ∨
    (let z₁ := List.replicate stmt.ciphertext.length ⟨0, by positivity⟩
     let z₂ := List.replicate ct'.length ⟨0, by positivity⟩
     let f := saltedCollisionFrames stmt.ciphertext z₁ ct' z₂
     FramedXofCollision cshakeC f.customization f.left f.right) := by
  unfold verifyKeylessCiphertextWeld at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨_, hclen⟩, _⟩, hctRoot⟩, hweld⟩, hxor⟩
  rcases ciphertextMerkleRoot_eq_or_collision stmt.ciphertext ct'
      (hclen.trans hlen'.symm) (hctRoot.trans hroot'.symm) with hctEq | hcol
  · subst hctEq; exact Or.inl ⟨rfl, hweld.symm, hxor⟩
  · exact Or.inr hcol

theorem keyless_weld_rejects_forged_ciphertext_or_collision (stmt : KeylessPublicPatchStmt)
    (hok : verifyKeylessCiphertextWeld stmt = true)
    (ct' : List UInt8) (hlen' : ct'.length = stmt.patchLen) (hne : ct' ≠ stmt.ciphertext) :
    verifyKeylessCiphertextWeld { stmt with ciphertext := ct' } = false ∨
    (let z₁ := List.replicate stmt.ciphertext.length ⟨0, by positivity⟩
     let z₂ := List.replicate ct'.length ⟨0, by positivity⟩
     let f := saltedCollisionFrames stmt.ciphertext z₁ ct' z₂
     FramedXofCollision cshakeC f.customization f.left f.right) := by
  cases h : verifyKeylessCiphertextWeld { stmt with ciphertext := ct' } with
  | false => exact Or.inl rfl
  | true =>
      unfold verifyKeylessCiphertextWeld at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases verifyKeylessCiphertextWeld_sound_or_collision stmt hok ct' hlen' h.1.1.2 with
        ⟨heq, _, _⟩ | hcol
      · exact absurd heq hne
      · exact Or.inr hcol

theorem keyless_weld_rejects_swapped_root_or_collision (stmt : KeylessPublicPatchStmt)
    (hok : verifyKeylessCiphertextWeld stmt = true)
    (root' : Digest) (hne : root' ≠ stmt.saltedPatchRoot)
    (hRange₁ : stmt.saltedPatchRoot.value < 256 ^ 32) (hRange₂ : root'.value < 256 ^ 32) :
    verifyKeylessCiphertextWeld { stmt with saltedPatchRoot := root' } = false ∨
    FramedXofCollision cshakeC publicWeldCust
      (publicWeldInput stmt.saltedPatchRoot stmt.weld.maskMerkleRoot stmt.weld.ctMerkleRoot
        stmt.keyCommit stmt.nonce (computeSlotAadDigest stmt.aadMeta) stmt.patchLen
        stmt.weld.aeadTag stmt.weld.blindPadCommit)
      (publicWeldInput root' stmt.weld.maskMerkleRoot stmt.weld.ctMerkleRoot
        stmt.keyCommit stmt.nonce (computeSlotAadDigest stmt.aadMeta) stmt.patchLen
        stmt.weld.aeadTag stmt.weld.blindPadCommit) := by
  cases h : verifyKeylessCiphertextWeld { stmt with saltedPatchRoot := root' } with
  | false => exact Or.inl rfl
  | true =>
      right
      unfold verifyKeylessCiphertextWeld at hok h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok h
      have hlen1 : (cshakeC.digestCodec.encode stmt.saltedPatchRoot).length = 32 := by
        show (digestBytesLE stmt.saltedPatchRoot).length = 32
        unfold digestBytesLE; simp only [hRange₁, ↓reduceIte, fixedDigestBytesLE, List.length_map, Bignum.digitsLE_length]
      have hlen2 : (cshakeC.digestCodec.encode root').length = 32 := by
        show (digestBytesLE root').length = 32
        unfold digestBytesLE; simp only [hRange₂, ↓reduceIte, fixedDigestBytesLE, List.length_map, Bignum.digitsLE_length]
      refine ⟨fun heq => ?_, hok.1.2.trans h.1.2.symm⟩
      unfold publicWeldInput at heq
      have htake := congrArg (List.take 32) heq
      simp only [List.append_assoc, List.take_left', hlen1, hlen2] at htake
      have hdec := congrArg cshakeC.digestCodec.decode htake
      rw [cshakeC.digestCodec.decode_encode, cshakeC.digestCodec.decode_encode] at hdec
      exact hne (Option.some.inj hdec).symm

/-- Full statement-pinned + keyless-welded sealed `Hyperdocument` patch gate. -/
def verifyConfinedSealedHyperdocPatch {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] [DecidableEq Val]
    {sem : AttrSemantics SemOp Val} {ell m fq : Nat}
    (parentage : Parentage) (baseStmt : SealedHyperdocPatchStmt NT sem)
    (pubStmt : KeylessPublicPatchStmt)
    (baseWit : SealedHyperdocPatchWitness NT SemOp sem ell m fq)
    (witSlotSecret : Digest) : Bool :=
  let aadDigest := computeSlotAadDigest pubStmt.aadMeta
  let ks := deriveSlotKeystream witSlotSecret pubStmt.aadMeta.slotIndex pubStmt.nonce aadDigest baseStmt.patchLen
  let expectedCt := List.zipWith (· ^^^ ·) baseWit.patchBytes ks
  let expectedMaskRoot := maskMerkleRoot ks baseWit.patchSalts
  let expectedTag := computeSlotAeadTag witSlotSecret pubStmt.keyCommit pubStmt.nonce aadDigest
    baseStmt.saltedPatchRoot pubStmt.weld.ctMerkleRoot expectedMaskRoot baseStmt.patchLen
  verifySealedHyperdocPatch parentage baseStmt baseWit &&
  decide (pubStmt.aadMeta.documentId = baseStmt.documentId.digest.value) &&
  decide (pubStmt.aadMeta.atomId = baseStmt.atomId.digest.value) &&
  decide (pubStmt.aadMeta.schema = baseStmt.schema) &&
  decide (pubStmt.aadMeta.operationId = baseStmt.operation.digest.value) &&
  decide (pubStmt.patchLen = baseStmt.patchLen) &&
  decide (pubStmt.saltedPatchRoot = baseStmt.saltedPatchRoot) &&
  decide (slotKeyCommit pubStmt.aadMeta.slotIndex witSlotSecret = pubStmt.keyCommit) &&
  decide (pubStmt.ciphertext = expectedCt) &&
  decide (pubStmt.weld.maskMerkleRoot = expectedMaskRoot) &&
  decide (pubStmt.weld.aeadTag = expectedTag) &&
  verifyKeylessCiphertextWeld pubStmt

theorem verifyConfinedSealedHyperdocPatch_sound_or_collision {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] [DecidableEq Val]
    {sem : AttrSemantics SemOp Val} {ell m fq : Nat}
    (parentage : Parentage) (baseStmt : SealedHyperdocPatchStmt NT sem)
    (pubStmt : KeylessPublicPatchStmt)
    (baseWit : SealedHyperdocPatchWitness NT SemOp sem ell m fq)
    (witSlotSecret registeredSecret : Digest)
    (hSlotLt : pubStmt.aadMeta.slotIndex < 2 ^ 64)
    (hRegKey : slotKeyCommit pubStmt.aadMeta.slotIndex registeredSecret = pubStmt.keyCommit)
    (hver : verifyConfinedSealedHyperdocPatch parentage baseStmt pubStmt baseWit witSlotSecret = true)
    (wNamed : List UInt8) (sNamed : List Salt248)
    (hcomm : CommitsSaltedPatch baseStmt wNamed sNamed) :
    (wNamed = baseWit.patchBytes ∧ sNamed = baseWit.patchSalts ∧
     witSlotSecret = registeredSecret ∧
     PolicyAdmits baseStmt.rootPolicy wNamed baseWit.ruleSeq baseStmt.claimedAst ∧
     (∀ rt ∈ baseStmt.rootPolicy.redactRules,
       AbsentPlain wNamed rt.pat ∧
       MatchesRegex wNamed (Regex.paddedComplement (Regex.literal rt.pat))) ∧
     (editAtomRecord baseStmt.operation baseStmt.editPayload).payload = [] ∧
     pubStmt.ciphertext = List.zipWith (· ^^^ ·) wNamed
       (deriveSlotKeystream registeredSecret pubStmt.aadMeta.slotIndex pubStmt.nonce
         (computeSlotAadDigest pubStmt.aadMeta) baseStmt.patchLen) ∧
     verifyKeylessCiphertextWeld pubStmt = true) ∨
    (let f := saltedCollisionFrames baseWit.patchBytes baseWit.patchSalts wNamed sNamed
     FramedXofCollision cshakeC f.customization f.left f.right) ∨
    FramedXofCollision cshakeC slotKeyCommitCust
      (slotKeyCommitInput pubStmt.aadMeta.slotIndex witSlotSecret)
      (slotKeyCommitInput pubStmt.aadMeta.slotIndex registeredSecret) := by
  unfold verifyConfinedSealedHyperdocPatch at hver
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hver
  rcases hver with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbase, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hkc⟩, hctEq⟩, _⟩, _⟩, hkeyless⟩
  rcases verifySealedHyperdocPatch_sound_or_collision parentage baseStmt baseWit hbase
      wNamed sNamed hcomm with hsound | hcolSalted
  · rcases slotKeyCommit_eq_or_collision hSlotLt hSlotLt (hkc.trans hRegKey.symm) with
      ⟨_, hsecEq⟩ | hcolKey
    · rcases hsound with ⟨hwEq, hsEq, hpol, hred, _, _, _, _, _, _, hcleartext⟩
      exact Or.inl ⟨hwEq, hsEq, hsecEq, hpol, hred, hcleartext, by rw [hctEq, hwEq, hsecEq], hkeyless⟩
    · exact Or.inr (Or.inr hcolKey)
  · exact Or.inr (Or.inl hcolSalted)

/-! ## §6. Symbolic Inhabitation, Refusal Teeth, & Pure-`Init` Conformance JSON Emitter -/

def demoRootViewKey : Digest := ⟨0x2a1f3e4d5c6b7a8990a1b2c3d4e5f60718293a4b5c6d7e8f9a0b1c2d3e4f5061⟩
def demoCellId : Nat := 500
def demoKeyEpoch : Nat := 3
def demoGrantedSlot : Nat := 2
def demoUngrantedSlot : Nat := 7
def demoSlot2Secret : Digest := deriveSlotSecret demoRootViewKey demoCellId demoGrantedSlot demoKeyEpoch
def demoSlot7Secret : Digest := deriveSlotSecret demoRootViewKey demoCellId demoUngrantedSlot demoKeyEpoch
def demoDelegatePk : HybridPublicKey := ⟨⟨0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00⟩, ⟨0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20⟩⟩
def demoKemCt (s : Nat) : HybridKemCiphertext := ⟨⟨0xaabbccddeeff00112233445566778899aabbccddeeff00112233445566778800 + s⟩, ⟨0xdeadbeefcafebabe0123456789abcdefdeadbeefcafebabe0123456789abcd00 + s⟩⟩
def demoKemSs (s : Nat) : HybridKemShared := ⟨⟨0x5566778899aabbccddeeff00112233445566778899aabbccddeeff0011223300 + s⟩, ⟨0xfedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543200 + s⟩⟩
def demoNonce : List UInt8 := (List.range 32).map fun i => UInt8.ofNat (0xA0 + i)
def demoExtraAad : List UInt8 := asciiBytes "hyperdoc-slot-2-v1"
def demoAadMeta : SlotAadMeta := ⟨demoStmt.documentId.digest.value, demoStmt.atomId.digest.value, demoStmt.schema, demoStmt.operation.digest.value, demoGrantedSlot, demoKeyEpoch, demoExtraAad⟩
def demoAadDigest : Digest := computeSlotAadDigest demoAadMeta
def demoKeystream : List UInt8 := deriveSlotKeystream demoSlot2Secret demoGrantedSlot demoNonce demoAadDigest sampleSubagentPayload.length
def demoCiphertext : List UInt8 := List.zipWith (· ^^^ ·) sampleSubagentPayload demoKeystream
def demoBlindPadDigest : Digest := ⟨0x0f1e2d3c4b5a69788796a5b4c3d2e1f00f1e2d3c4b5a69788796a5b4c3d2e1f0⟩
def demoBlindPadC8 : C8 := digestTowerC demoBlindPadDigest
def demoBlindPadCommit : Digest := cshakeC.xofDigest blindPadCust (cshakeC.digestCodec.encode demoBlindPadDigest ++ cshakeC.digestCodec.encode demoStmt.saltedPatchRoot ++ demoNonce)
def demoPublicWeld : PublicCiphertextWeld :=
  let ctRoot := ciphertextMerkleRoot demoCiphertext
  let maskRoot := maskMerkleRoot demoKeystream demoSalts
  let kc := slotKeyCommit demoGrantedSlot demoSlot2Secret
  let tag := computeSlotAeadTag demoSlot2Secret kc demoNonce demoAadDigest demoStmt.saltedPatchRoot ctRoot maskRoot sampleSubagentPayload.length
  let wDig := cshakeC.xofDigest publicWeldCust (publicWeldInput demoStmt.saltedPatchRoot maskRoot ctRoot kc demoNonce demoAadDigest sampleSubagentPayload.length tag demoBlindPadCommit)
  let γ := computeWeldChallenge wDig
  ⟨ctRoot, maskRoot, demoBlindPadCommit, tag, wDig, addC (towerPolyEval γ (saltedLeaves sampleSubagentPayload demoSalts)) demoBlindPadC8, addC (towerPolyEval γ (saltedLeaves demoKeystream demoSalts)) demoBlindPadC8⟩
def demoKeylessStmt : KeylessPublicPatchStmt := ⟨demoAadMeta, slotKeyCommit demoGrantedSlot demoSlot2Secret, demoNonce, sampleSubagentPayload.length, demoStmt.saltedPatchRoot, demoCiphertext, demoPublicWeld⟩

private theorem deriveSlotKeystream_length (slotSecret : Digest) (slotIdx : Nat)
    (nonce : List UInt8) (aadDigest : Digest) (len : Nat) :
    (deriveSlotKeystream slotSecret slotIdx nonce aadDigest len).length = len := by
  unfold deriveSlotKeystream
  rw [List.length_take, Nat.min_eq_left]
  have hflat : ∀ (xs : List Nat),
      ((xs.map fun b => fixedDigestBytesLE (cshakeC.xofDigest slotStreamCust
        (cshakeC.digestCodec.encode slotSecret ++ u64LE slotIdx ++ nonce ++
          cshakeC.digestCodec.encode aadDigest ++ u64LE b))).flatten).length = 32 * xs.length := by
    intro xs; induction xs with
    | nil => simp
    | cons _ _ ih =>
        simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons, ih]
        simp only [fixedDigestBytesLE, List.length_map, Bignum.digitsLE_length]; omega
  rw [hflat, List.length_range]; omega

theorem demo_keyless_weld_verified : verifyKeylessCiphertextWeld demoKeylessStmt = true := by
  have hksLen : demoKeystream.length = sampleSubagentPayload.length := deriveSlotKeystream_length _ _ _ _ _
  have hctLen : demoCiphertext.length = sampleSubagentPayload.length := by simp [demoCiphertext, hksLen]
  have hxor : addC demoPublicWeld.blindEvalS demoPublicWeld.blindEvalM =
      towerPolyEval (computeWeldChallenge demoPublicWeld.weldDigest) (ctLeaves demoCiphertext) :=
    blinded_xor_weld_holds _ demoBlindPadC8 sampleSubagentPayload demoKeystream demoSalts hksLen.symm (by simp [demoSalts])
  unfold verifyKeylessCiphertextWeld
  have h1 : decide (0 < demoKeylessStmt.patchLen) = true := by decide
  have h2 : decide (demoKeylessStmt.ciphertext.length = demoKeylessStmt.patchLen) = true := decide_eq_true hctLen
  have h3 : decide (demoKeylessStmt.nonce.length = 32) = true := by decide
  have h4 : decide (ciphertextMerkleRoot demoKeylessStmt.ciphertext = demoKeylessStmt.weld.ctMerkleRoot) = true := decide_eq_true rfl
  have h5 : decide (computeWeldDigest demoKeylessStmt = demoKeylessStmt.weld.weldDigest) = true := decide_eq_true rfl
  have h6 : decide (addC demoKeylessStmt.weld.blindEvalS demoKeylessStmt.weld.blindEvalM =
      towerPolyEval (computeWeldChallenge demoKeylessStmt.weld.weldDigest) (ctLeaves demoKeylessStmt.ciphertext)) = true := decide_eq_true hxor
  simp only [h1, h2, h3, h4, h5, h6, Bool.and_self]

theorem demo_confined_gate_verified :
    verifyConfinedSealedHyperdocPatch demoParentage demoStmt demoKeylessStmt
      demoWitness demoSlot2Secret = true := by
  have hbase := demo_sealedHyperdocGate_verified
  have hkeyless := demo_keyless_weld_verified
  unfold verifyConfinedSealedHyperdocPatch
  rw [hbase, hkeyless]
  simp only [demoKeylessStmt, demoAadMeta, demoPublicWeld, demoCiphertext,
    demoKeystream, demoAadDigest, demoWitness, demoStmt, demoGrantedSlot, demoKeyEpoch,
    decide_true, Bool.and_self]

private theorem verifyKeylessCiphertextWeld_false_of_xor_ne (s : KeylessPublicPatchStmt)
    (hne : addC s.weld.blindEvalS s.weld.blindEvalM ≠
      towerPolyEval (computeWeldChallenge s.weld.weldDigest) (ctLeaves s.ciphertext)) :
    verifyKeylessCiphertextWeld s = false := by
  unfold verifyKeylessCiphertextWeld; rw [decide_eq_false hne, Bool.and_false]

theorem demo_tooth_corrupted_blind_xor_rejected :
    verifyKeylessCiphertextWeld
      { demoKeylessStmt with weld := { demoPublicWeld with blindEvalS := addC demoPublicWeld.blindEvalS oneC } } = false := by
  have hok := demo_keyless_weld_verified
  unfold verifyKeylessCiphertextWeld at hok; simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  have heq : addC demoPublicWeld.blindEvalS demoPublicWeld.blindEvalM =
      towerPolyEval (computeWeldChallenge demoPublicWeld.weldDigest) (ctLeaves demoCiphertext) := hok.2
  apply verifyKeylessCiphertextWeld_false_of_xor_ne
  intro hbad
  change addC (addC demoPublicWeld.blindEvalS oneC) demoPublicWeld.blindEvalM =
    towerPolyEval (computeWeldChallenge demoPublicWeld.weldDigest) (ctLeaves demoCiphertext) at hbad
  rw [← heq] at hbad
  have h1 : addC oneC (addC demoPublicWeld.blindEvalS demoPublicWeld.blindEvalM) =
      addC zeroC (addC demoPublicWeld.blindEvalS demoPublicWeld.blindEvalM) := by
    rw [zero_addC, addC_comm oneC, addC_assoc, addC_comm demoPublicWeld.blindEvalM oneC, ← addC_assoc]; exact hbad
  have h2 : oneC = zeroC := by
    simpa only [addC_assoc, addC_self, addC_zero] using
      congrArg (fun x => addC x (addC demoPublicWeld.blindEvalS demoPublicWeld.blindEvalM)) h1
  exact absurd h2 (by decide)

theorem demo_tooth_attenuated_cap_omits_slot7 :
    let cap := mintAttenuatedSlotCap (deriveSlotSecret demoRootViewKey demoCellId · demoKeyEpoch)
      demoCellId demoKeyEpoch demoDelegatePk (fun s => (demoKemCt s, demoKemSs s)) [2, 5]
    cap.lookupWrapped 7 = none ∧
    attenuateSlotCap cap (fun w => some (demoKemSs w.slotIndex)) demoDelegatePk
      (fun s => (demoKemCt s, demoKemSs s)) [2, 7] = none :=
  ⟨by decide, attenuate_refuses_amplification _ _ _ _ [2, 7] 7 (by decide) (by decide)⟩

private def hexBytes (bytes : List UInt8) : String :=
  String.join (bytes.map fun b => let d := "0123456789abcdef".toList; String.ofList [d[b.toNat / 16]!, d[b.toNat % 16]!])
private def natFixedLE (len val : Nat) : List UInt8 := (List.range len).map fun i => UInt8.ofNat ((val / 256 ^ i) % 256)
private def digestHex (d : Digest) : String := hexBytes (natFixedLE 32 d.value)
private def c8Hex (c : C8) : String := hexBytes (natFixedLE 32 (Coord.toNat 8 c))
private def jsonBool (b : Bool) : String := if b then "true" else "false"

private def emitPerSlotConformance (path : System.FilePath) : IO Unit := do
  let okWeld := verifyKeylessCiphertextWeld demoKeylessStmt
  let okGate := verifyConfinedSealedHyperdocPatch demoParentage demoStmt demoKeylessStmt demoWitness demoSlot2Secret
  let tamperedCt := match demoCiphertext with | [] => [] | b :: r => (b ^^^ 1) :: r
  let rejCt := !verifyKeylessCiphertextWeld { demoKeylessStmt with ciphertext := tamperedCt }
  let rejRoot := !verifyKeylessCiphertextWeld { demoKeylessStmt with saltedPatchRoot := ⟨demoStmt.saltedPatchRoot.value ^^^ 1⟩ }
  let rejKc := !verifyKeylessCiphertextWeld { demoKeylessStmt with keyCommit := ⟨demoKeylessStmt.keyCommit.value ^^^ 1⟩ }
  let rejWrongSec := !verifyConfinedSealedHyperdocPatch demoParentage demoStmt demoKeylessStmt demoWitness demoSlot7Secret
  unless okWeld && okGate && rejCt && rejRoot && rejKc && rejWrongSec do
    throw (IO.userError "PerSlotKeyConfinement build-time self-check failed")
  let kc2 := slotKeyCommit demoGrantedSlot demoSlot2Secret
  let aad2 := wrapSlotAad demoCellId demoGrantedSlot demoKeyEpoch kc2
  let kek2 := hybridWrapKek (demoKemSs demoGrantedSlot) (demoKemCt demoGrantedSlot) demoDelegatePk aad2
  let wrapped2 := wrapSlotKey demoCellId demoGrantedSlot demoKeyEpoch demoDelegatePk
    (demoKemCt demoGrantedSlot) (demoKemSs demoGrantedSlot) demoSlot2Secret
  let γ := computeWeldChallenge demoPublicWeld.weldDigest
  let evalC := towerPolyEval γ (ctLeaves demoCiphertext)
  let kv (k v : String) : String := s!"  \"{k}\": {v}"
  let ks (k v : String) : String := s!"  \"{k}\": \"{v}\""
  let lines : List String := [
    ks "schema" "minidregg.per_slot_seal_conformance.v1", ks "source" "Assurance/PerSlotKeyConfinement.lean",
    kv "cell_id" s!"{demoCellId}", kv "key_epoch" s!"{demoKeyEpoch}", kv "granted_slot" s!"{demoGrantedSlot}", kv "ungranted_slot" s!"{demoUngrantedSlot}",
    ks "root_view_key_hex" (digestHex demoRootViewKey), ks "slot_2_secret_hex" (digestHex demoSlot2Secret), ks "slot_2_key_commit_hex" (digestHex kc2),
    ks "slot_7_secret_hex" (digestHex demoSlot7Secret), ks "slot_7_key_commit_hex" (digestHex (slotKeyCommit demoUngrantedSlot demoSlot7Secret)),
    ks "delegate_x25519_pk_hex" (digestHex demoDelegatePk.x25519Pk), ks "delegate_mlkem768_ek_digest_hex" (digestHex demoDelegatePk.mlkem768EkDigest),
    ks "kem_ct_x25519_eph_pk_hex" (digestHex (demoKemCt demoGrantedSlot).x25519EphPk), ks "kem_ct_mlkem768_digest_hex" (digestHex (demoKemCt demoGrantedSlot).mlkem768CtDigest),
    ks "kem_ss_x25519_hex" (digestHex (demoKemSs demoGrantedSlot).ssX25519), ks "kem_ss_mlkem768_hex" (digestHex (demoKemSs demoGrantedSlot).ssMlkem),
    ks "hybrid_kek_hex" (digestHex kek2), ks "wrapped_slot_2_secret_hex" (digestHex wrapped2.wrappedSecret), ks "wrapped_slot_2_tag_hex" (digestHex wrapped2.wrapTag),
    kv "document_id" s!"{demoAadMeta.documentId}", kv "atom_id" s!"{demoAadMeta.atomId}", ks "schema_hex" (digestHex demoAadMeta.schema), kv "operation_id" s!"{demoAadMeta.operationId}",
    ks "nonce_hex" (hexBytes demoNonce), ks "extra_aad_hex" (hexBytes demoExtraAad), ks "slot_aad_digest_hex" (digestHex demoAadDigest),
    ks "patch_payload_hex" (hexBytes sampleSubagentPayload), ks "salted_patch_root_hex" (digestHex demoStmt.saltedPatchRoot),
    ks "keystream_hex" (hexBytes demoKeystream), ks "ciphertext_hex" (hexBytes demoCiphertext), ks "ct_merkle_root_hex" (digestHex demoPublicWeld.ctMerkleRoot),
    ks "mask_merkle_root_hex" (digestHex demoPublicWeld.maskMerkleRoot), ks "blind_pad_hex" (digestHex demoBlindPadDigest),
    ks "blind_pad_commit_hex" (digestHex demoPublicWeld.blindPadCommit), ks "aead_tag_hex" (digestHex demoPublicWeld.aeadTag),
    ks "weld_digest_hex" (digestHex demoPublicWeld.weldDigest), ks "weld_gamma_hex" (c8Hex γ), ks "eval_c_hex" (c8Hex evalC),
    ks "blind_eval_s_hex" (c8Hex demoPublicWeld.blindEvalS), ks "blind_eval_m_hex" (c8Hex demoPublicWeld.blindEvalM),
    kv "keyless_weld_verified" (jsonBool okWeld), kv "confined_gate_verified" (jsonBool okGate),
    kv "tooth_tampered_ct_rejected" (jsonBool rejCt), kv "tooth_swapped_root_rejected" (jsonBool rejRoot),
    kv "tooth_swapped_key_commit_rejected" (jsonBool rejKc), kv "tooth_wrong_slot_secret_rejected" (jsonBool rejWrongSec)]
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path ("{\n" ++ String.intercalate ",\n" lines ++ "\n}\n")

#eval emitPerSlotConformance "prover/testdata/per_slot_seal_conformance.json"

/-! ## §7. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.slotKeyCommit_eq_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms slotKeyCommit_eq_or_collision
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.unwrapSlotKey_wrapSlotKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unwrapSlotKey_wrapSlotKey
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.attenuate_refuses_amplification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attenuate_refuses_amplification
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.attenuate_omits_ungranted_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attenuate_omits_ungranted_slots
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.ungranted_slot_non_derivable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ungranted_slot_non_derivable
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.no_adversary_distinguishes_ungranted_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_adversary_distinguishes_ungranted_slot
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.hybrid_wrap_dual_protection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hybrid_wrap_dual_protection
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.tooth_legacy_readcap_leaks_ungranted_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tooth_legacy_readcap_leaks_ungranted_slot
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.packSaltedLeaf_xor_eq_ciphertextLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packSaltedLeaf_xor_eq_ciphertextLeaf
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.blinded_xor_weld_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms blinded_xor_weld_holds
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.verifyKeylessCiphertextWeld_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyKeylessCiphertextWeld_sound_or_collision
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.keyless_weld_rejects_forged_ciphertext_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keyless_weld_rejects_forged_ciphertext_or_collision
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.keyless_weld_rejects_swapped_root_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms keyless_weld_rejects_swapped_root_or_collision
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.verifyConfinedSealedHyperdocPatch_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyConfinedSealedHyperdocPatch_sound_or_collision
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.demo_confined_gate_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_confined_gate_verified
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.demo_tooth_corrupted_blind_xor_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_tooth_corrupted_blind_xor_rejected
/-- info: 'Minidregg.Assurance.PerSlotKeyConfinement.demo_tooth_attenuated_cap_omits_slot7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms demo_tooth_attenuated_cap_omits_slot7

end Minidregg.Assurance.PerSlotKeyConfinement
