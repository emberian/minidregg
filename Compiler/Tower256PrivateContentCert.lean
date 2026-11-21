/-
# Compiler.Tower256PrivateContentCert -- Private-Witness Succinct Content-Bound Certificates

Closes both gaps documented in `Compiler/Tower256ContentCert.lean` (`:18`, `:43-45`, `:484-490`)
for `zkml-research/docs/LEAF-PROVER-DECISION.md` §§4–6:

1. **Salted Private Content Commitment (`saltedContentCommit`) & Hiding:**
   Each byte `w[i]` is packed with a 248-bit per-position random salt `s[i] : Salt248` (`lane 0`
   low byte = `w[i]`, upper 31 bytes / lanes `1..7` = `s[i]`) as a `C8` (`Coordinate 8` /
   `GF(2^256)`) leaf via the exact bijection `saltedLeafEquiv : UInt8 × Salt248 ≃ C8`, committed
   under `cubeRoot merkleDomainsC codecC` alongside public `recordLength`.
   - `saltedRoot_eq_or_collision`: two salted columns of equal length sharing one root agree on
     every byte and every salt, or collide at the explicit `Frames` computed by `denseCollision`.
   - Per-leaf salt-uniformity & hiding at unopened positions:
     * `unopened_salted_leaf_oracle_hiding` & `unopened_salted_leaf_rom_prob_eq`: swapping `b₀`
       and `b₁` at an unopened leaf `idx` with fresh salt `s₀` induces an explicit involutive
       leaf-oracle bijection (`Equiv.swap`) preserving all other leaf digests and producing
       identical root distributions over finite leaf-hash oracles.
     * `unopened_keyed_salt_prob_eq`: for any salt-bijective keyed leaf hash, uniform random
       `Salt248` yields identical root distributions for `b₀` and `b₁` at unopened `idx`.
     * `maskedCubeRootPreimageEquiv` & `maskedCubeRoot_prob_eq`: under concrete `cshakeC`,
       XOR-masking a `C8` leaf (`addC payload mask`) induces an exact bijection on masks `C8 ≃ C8`
       preserving `cubeRoot merkleDomainsC codecC` preimage sets and uniform mask probabilities for
       every digest `rt : Digest`.

2. **All Three `ClaimData` Modes (`.accept b`, `.count n`, `.bound lo hi`):**
   `Dfaops.runCount` counts positions reaching `accepting` states along the run (proved equal to
   `(t.traceFrom t.initial w).countP ...` in `Dfaops.runCount_eq_traceFrom_countP`), and
   `Dfaops.satisfiesClaim` decides `.accept b`, `.count n`, and `.bound lo hi`.

3. **Succinct Root-Only `PrivateReceipt` Tied to `Tower256SuccinctCheck` (`SuccinctAccepts`):**
   - Commits the masked execution trace `traceRoot` (`TraceRow`: `(byte_i, state_i, next_i,
     cumCount_i, mask_i)` with 184-bit per-row random mask `RowMask`),
   - Welds `cSHAKE256`-masked trace evaluations `blindTraceEval` into a Reed–Solomon codeword
     verified by `Tower256SuccinctCheck.check` (`friReceipt`), and
   - Verifies full initial + terminal `BoundaryOpenings` and Fiat–Shamir sampled `StepOpening`s
     against `contentRoot`, `traceRoot`, `deltaRoot`, and `friReceipt.roots 0` without carrying the
     document or dense transition table in the clear.
   - `checkPrivate_sound_or_collision`: an accepted `PrivateReceipt` either satisfies `PrivateHolds`
     (across `.accept`, `.count`, `.bound`) together with Selvage's `IdealAccept` and exact FRI
     level-0 boundary/query welds on `T`, or hits `StepSamplingMiss` bounded by
     `((L - 1) / L) ^ stepQueries` (`step_sampling_miss_prob_eq`), or exposes an explicit
     tree/path-pinned `PrivateCertCollision`. `checkPrivate_premises_inhabited` proves joint
     non-vacuity of the soundness hypotheses on any well-formed table and non-empty word.

Emits Lean-authored conformance vectors to `prover/testdata/tower256_private_cert_conformance.json`.
-/

import Compiler.Tower256ContentCert
import Compiler.Tower256SuccinctCheck
import Compiler.Tower256SuccinctProver
import Compiler.Tower256SuccinctReceiptCodec
import Selvage.BindingGame

namespace Minidregg.Compiler.Tower256PrivateContentCert

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate coordinateFinEquiv capacity)
open Minidregg.Theory.BinaryCubeAddress (binaryAddressBits binaryCubeIndexEquiv)
open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256CshakeMerkleBinding
open Minidregg.Compiler.Tower256CoordinateMerkle
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8 toField evalCoeffs)
open Minidregg.Compiler.Tower256ContentCert
open Minidregg.Compiler.Tower256AdditiveFriController (TranscriptPins Tower256)
open Minidregg.Compiler.Tower256AdditiveFriRawController
  (RawTranscript IdealAccept ReceiptCollision)
open Minidregg.Compiler.Tower256AdditiveFriSuccinctController
  (Consistent toRawStatement FinalCollision succinct_accepts_ideal_or_collision)
open Minidregg.Compiler.Tower256AdditiveFriRawDeployment (rawPcs bootstrapPins)
open Minidregg.Compiler.Tower256SuccinctCheck
open Minidregg.Compiler.Tower256SuccinctProver (unitBasis unitBasis_independent)
open Minidregg.Compiler.Tower256SuccinctReceiptCodec (receiptCodec)
open Minidregg.Selvage

set_option autoImplicit false

/-! ## §1. Constructive Path-Pinned Merkle Collision Extraction -/

/-- **Constructive path-vs-column collision finder (`pathCollision`)**: given a claimed leaf value
`v`, address `addr`, and sibling path `path` accepted against `cubeRoot domains codec col` where
`v ≠ col addr`, walks top-down to return the exact `Frames` that collide in `cshake`. -/
def pathCollision {cshake : Cshake256} (domains : MerkleDomains cshake)
    {R : Type} [DecidableEq R] (codec : LawfulCodec R) :
    {k : Nat} → R → (Fin k → Bool) → List Digest → ((Fin k → Bool) → R) → Frames
  | 0, v, addr, _, col =>
      ⟨domains.leafCustomization, leafInput codec v, leafInput codec (col addr)⟩
  | _ + 1, v, addr, [], col =>
      ⟨domains.leafCustomization, leafInput codec v, leafInput codec (col addr)⟩
  | _ + 1, v, addr, sib :: rest, col =>
      let lCol := fun t => col (Fin.cases false t)
      let rCol := fun t => col (Fin.cases true t)
      let tailAddr := fun i => addr i.succ
      match recompute domains (domains.hashLeaf codec v) tailAddr rest with
      | none =>
          ⟨domains.leafCustomization, leafInput codec v, leafInput codec (col addr)⟩
      | some child =>
          let (claimedL, claimedR) := if addr 0 then (sib, child) else (child, sib)
          let honestL := cubeRoot domains codec lCol
          let honestR := cubeRoot domains codec rCol
          if nodeInput cshake claimedL claimedR = nodeInput cshake honestL honestR then
            if addr 0 then
              pathCollision domains codec v tailAddr rest rCol
            else
              pathCollision domains codec v tailAddr rest lCol
          else
            ⟨domains.nodeCustomization,
              nodeInput cshake claimedL claimedR,
              nodeInput cshake honestL honestR⟩

/-- **An accepted Merkle path either opens the true column value at `addr`, or collides at the
exact `Frames` computed by `pathCollision`.** -/
theorem recompute_eq_or_pathCollision {cshake : Cshake256} (domains : MerkleDomains cshake)
    {R : Type} [DecidableEq R] (codec : LawfulCodec R) :
    ∀ {k : Nat} (v : R) (addr : Fin k → Bool) (path : List Digest) (col : (Fin k → Bool) → R),
      recompute domains (domains.hashLeaf codec v) addr path = some (cubeRoot domains codec col) →
        v = col addr ∨
          let w := pathCollision domains codec v addr path col
          FramedXofCollision cshake w.customization w.left w.right
  | 0, v, addr, path, col, hrec => by
      cases path with
      | cons _ _ => simp [recompute] at hrec
      | nil =>
          simp only [recompute, cubeRoot, ↓reduceIte, Option.some.injEq] at hrec
          have haddr : col (fun i => i.elim0) = col addr :=
            congrArg col (funext fun i => i.elim0)
          rw [haddr] at hrec
          by_cases hv : v = col addr
          · exact Or.inl hv
          · exact Or.inr ⟨fun e => hv (leafInput_injective codec e), hrec⟩
  | _ + 1, _, _, [], _, hrec => by
      simp [recompute] at hrec
  | _ + 1, v, addr, sib :: rest, col, hrec => by
      obtain ⟨child, hchild, hroot⟩ :=
        (recompute_cons_some_iff domains (domains.hashLeaf codec v) sib addr rest
          (cubeRoot domains codec col)).mp hrec
      simp only [pathCollision, hchild]
      let lCol := fun t => col (Fin.cases false t)
      let rCol := fun t => col (Fin.cases true t)
      cases hb : addr 0
      · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hroot ⊢
        split
        · rename_i heq
          have hp := nodeInput_injective cshake
            (show (fun p : Digest × Digest => nodeInput cshake p.1 p.2) (child, sib) =
              (fun p : Digest × Digest => nodeInput cshake p.1 p.2)
                (cubeRoot domains codec lCol, cubeRoot domains codec rCol) from heq)
          have hL : child = cubeRoot domains codec lCol := congrArg Prod.fst hp
          subst hL
          rcases recompute_eq_or_pathCollision domains codec v (fun i => addr i.succ) rest lCol hchild with hv | hc
          · left
            rw [hv]
            show col (Fin.cases false (fun i => addr i.succ)) = col addr
            congr 1
            funext j
            cases j using Fin.cases with
            | zero => exact hb.symm
            | succ _ => rfl
          · exact Or.inr hc
        · rename_i hne
          exact Or.inr ⟨hne, hroot⟩
      · simp only [hb, ↓reduceIte] at hroot ⊢
        split
        · rename_i heq
          have hp := nodeInput_injective cshake
            (show (fun p : Digest × Digest => nodeInput cshake p.1 p.2) (sib, child) =
              (fun p : Digest × Digest => nodeInput cshake p.1 p.2)
                (cubeRoot domains codec lCol, cubeRoot domains codec rCol) from heq)
          have hR : child = cubeRoot domains codec rCol := congrArg Prod.snd hp
          subst hR
          rcases recompute_eq_or_pathCollision domains codec v (fun i => addr i.succ) rest rCol hchild with hv | hc
          · left
            rw [hv]
            show col (Fin.cases true (fun i => addr i.succ)) = col addr
            congr 1
            funext j
            cases j using Fin.cases with
            | zero => exact hb.symm
            | succ _ => rfl
          · exact Or.inr hc
        · rename_i hne
          exact Or.inr ⟨hne, hroot⟩

/-! ## §2. Salted Private Content Commitment (`saltedContentCommit`) & Hiding -/

private theorem add_mul_mod_eq (a b m : Nat) (ha : a < m) :
    (a + m * b) % m = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

private theorem add_mul_div_eq (a b m : Nat) (hm : 0 < m) (ha : a < m) :
    (a + m * b) / m = b := by
  rw [Nat.add_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt ha, Nat.add_zero]

/-- 248-bit per-position random salt (`lanes 1..7` + upper 3 bytes of lane 0; byte 0 holds `w[i]`). -/
abbrev Salt248 := Fin (2 ^ 248)

instance : Inhabited Salt248 := ⟨⟨0, by positivity⟩⟩

/-- Canonical 256-bit integer packing of `(byte, salt)`: low byte is `b`, upper 248 bits are `s`. -/
def saltedLeafNat (b : UInt8) (s : Salt248) : Nat :=
  b.toNat + 256 * s.val

theorem saltedLeafNat_lt (b : UInt8) (s : Salt248) : saltedLeafNat b s < 2 ^ 256 := by
  unfold saltedLeafNat
  have hb := b.toNat_lt
  have hs := s.isLt
  have hpow : (256 : Nat) * 2 ^ 248 = 2 ^ 256 := by norm_num
  omega

/-- Pack `(byte, 248-bit salt)` into a `Coordinate 8` (`C8`) Merkle leaf. -/
def packSaltedLeaf (b : UInt8) (s : Salt248) : C8 :=
  leafOfNat (saltedLeafNat b s)

/-- Extract byte `0` (`lane 0` low byte) of a `C8` coordinate. -/
def unpackByte (c : C8) : UInt8 :=
  UInt8.ofNat (Coord.toNat 8 c % 256)

/-- Extract the 248-bit salt (`bytes 1..31`) of a `C8` coordinate. -/
def unpackSalt (c : C8) : Salt248 :=
  ⟨Coord.toNat 8 c / 256, by
    have hc : Coord.toNat 8 c < 2 ^ 256 := by
      simpa [capacity_eight] using Coord.toNat_lt 8 c
    omega⟩

@[simp] theorem toNat_packSaltedLeaf (b : UInt8) (s : Salt248) :
    Coord.toNat 8 (packSaltedLeaf b s) = saltedLeafNat b s := by
  unfold packSaltedLeaf leafOfNat
  exact Coord.toNat_ofNat 8 _ (by rw [capacity_eight]; exact saltedLeafNat_lt b s)

@[simp] theorem unpackByte_packSaltedLeaf (b : UInt8) (s : Salt248) :
    unpackByte (packSaltedLeaf b s) = b := by
  unfold unpackByte
  rw [toNat_packSaltedLeaf]
  unfold saltedLeafNat
  rw [add_mul_mod_eq b.toNat s.val 256 b.toNat_lt]
  exact UInt8.ofNat_toNat

@[simp] theorem unpackSalt_packSaltedLeaf (b : UInt8) (s : Salt248) :
    unpackSalt (packSaltedLeaf b s) = s := by
  apply Fin.ext
  simp only [unpackSalt, toNat_packSaltedLeaf, saltedLeafNat]
  exact add_mul_div_eq b.toNat s.val 256 (by norm_num) b.toNat_lt

@[simp] theorem packSaltedLeaf_unpack (c : C8) :
    packSaltedLeaf (unpackByte c) (unpackSalt c) = c := by
  apply (coordinateFinEquiv 8).injective
  apply Fin.ext
  rw [Coord.coordinateFinEquiv_val, Coord.coordinateFinEquiv_val, toNat_packSaltedLeaf]
  unfold saltedLeafNat unpackByte unpackSalt
  simp only [UInt8.toNat_ofNat', Nat.mod_mod]
  exact Nat.mod_add_div (Coord.toNat 8 c) 256

/-- **Exact bijection `(byte, 248-bit salt) ≃ C8`**: every 256-bit leaf splits into 1 byte + 248-bit salt. -/
def saltedLeafEquiv : UInt8 × Salt248 ≃ C8 where
  toFun p := packSaltedLeaf p.1 p.2
  invFun c := (unpackByte c, unpackSalt c)
  left_inv p := by simp
  right_inv c := packSaltedLeaf_unpack c

theorem saltedLeafNat_injective {b₁ b₂ : UInt8} {s₁ s₂ : Salt248}
    (h : saltedLeafNat b₁ s₁ = saltedLeafNat b₂ s₂) : b₁ = b₂ ∧ s₁ = s₂ := by
  have hb₁ := b₁.toNat_lt
  have hb₂ := b₂.toNat_lt
  unfold saltedLeafNat at h
  have hmod : b₁.toNat = b₂.toNat := by omega
  have hdiv : s₁.val = s₂.val := by omega
  exact ⟨UInt8.toNat_inj.mp hmod, Fin.ext hdiv⟩

theorem packSaltedLeaf_injective {b₁ b₂ : UInt8} {s₁ s₂ : Salt248} :
    packSaltedLeaf b₁ s₁ = packSaltedLeaf b₂ s₂ ↔ b₁ = b₂ ∧ s₁ = s₂ := by
  constructor
  · intro h
    have hp := congrArg saltedLeafEquiv.symm h
    simpa [saltedLeafEquiv] using hp
  · rintro ⟨rfl, rfl⟩; rfl

/-- Dense integer list of salted leaves for a byte record `w` and per-position `salts`. -/
def saltedEntries (w : List UInt8) (salts : List Salt248) : List Nat :=
  List.zipWith saltedLeafNat w salts

/-- **Salted private content commitment (`saltedContentCommit`)**: the `cSHAKE256` `cubeRoot` over
`packSaltedLeaf w[i] salts[i]`, zero-padded above `w.length` to `2 ^ depthOf w.length`. -/
def saltedContentCommit (w : List UInt8) (salts : List Salt248) : Digest :=
  denseRoot (saltedEntries w salts)

/-- Explicit tree-pinned collision frames between two salted records. -/
def saltedCollisionFrames (w₁ : List UInt8) (s₁ : List Salt248)
    (w₂ : List UInt8) (s₂ : List Salt248) : Frames :=
  denseCollision (saltedEntries w₁ s₁) (saltedEntries w₂ s₂)

/-- The concrete `FramedXofCollision` event exposed by two colliding salted trees. -/
def SaltedCollision (w₁ : List UInt8) (s₁ : List Salt248)
    (w₂ : List UInt8) (s₂ : List Salt248) : Prop :=
  DenseCollision (saltedEntries w₁ s₁) (saltedEntries w₂ s₂)

theorem saltedEntries_lt (w : List UInt8) (salts : List Salt248) :
    ∀ x ∈ saltedEntries w salts, x < 2 ^ 256 := by
  induction w generalizing salts with
  | nil => simp [saltedEntries]
  | cons b ws ih =>
      cases salts with
      | nil => simp [saltedEntries]
      | cons s ss =>
          intro x hx
          simp only [saltedEntries, List.zipWith_cons_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact saltedLeafNat_lt b s
          · exact ih ss x hx

theorem saltedEntries_injective :
    ∀ (w₁ : List UInt8) (s₁ : List Salt248) (w₂ : List UInt8) (s₂ : List Salt248),
      s₁.length = w₁.length → s₂.length = w₂.length → w₁.length = w₂.length →
      saltedEntries w₁ s₁ = saltedEntries w₂ s₂ → w₁ = w₂ ∧ s₁ = s₂
  | [], [], [], [], _, _, _, _ => ⟨rfl, rfl⟩
  | b₁ :: w₁, x₁ :: s₁, b₂ :: w₂, x₂ :: s₂, hs₁, hs₂, hw, heq => by
      simp only [saltedEntries, List.zipWith_cons_cons, List.cons.injEq] at heq
      obtain ⟨hb, hx⟩ := saltedLeafNat_injective heq.1
      obtain ⟨hws, hss⟩ := saltedEntries_injective w₁ s₁ w₂ s₂
        (by simp at hs₁; omega) (by simp at hs₂; omega) (by simp at hw; omega) heq.2
      exact ⟨congrArg₂ List.cons hb hws, congrArg₂ List.cons hx hss⟩
  | [], _ :: _, _, _, hs₁, _, _, _ => by simp at hs₁
  | _ :: _, [], _, _, hs₁, _, _, _ => by simp at hs₁
  | _, _, [], _ :: _, _, hs₂, _, _ => by simp at hs₂
  | _, _, _ :: _, [], _, hs₂, _, _ => by simp at hs₂
  | [], [], _ :: _, _ :: _, _, _, hw, _ => by simp at hw
  | _ :: _, _ :: _, [], [], _, _, hw, _ => by simp at hw

/-- **`saltedRoot_eq_or_collision`**: two salted columns of equal length under one `saltedContentCommit`
root agree on **every byte and every salt**, or expose an explicit `FramedXofCollision` at the exact
frames `saltedCollisionFrames` computes from the two trees. -/
theorem saltedRoot_eq_or_collision
    (w₁ : List UInt8) (s₁ : List Salt248) (w₂ : List UInt8) (s₂ : List Salt248)
    (hs₁ : s₁.length = w₁.length) (hs₂ : s₂.length = w₂.length) (hw : w₁.length = w₂.length)
    (hroot : saltedContentCommit w₁ s₁ = saltedContentCommit w₂ s₂) :
    (w₁ = w₂ ∧ s₁ = s₂) ∨ SaltedCollision w₁ s₁ w₂ s₂ := by
  have hlen : (saltedEntries w₁ s₁).length = (saltedEntries w₂ s₂).length := by
    simp [saltedEntries, hs₁, hs₂, hw]
  rcases denseRoot_eq_or_collision (saltedEntries w₁ s₁) (saltedEntries w₂ s₂) hlen
      (saltedEntries_lt w₁ s₁) (saltedEntries_lt w₂ s₂) hroot with heq | col
  · exact Or.inl (saltedEntries_injective w₁ s₁ w₂ s₂ hs₁ hs₂ hw heq)
  · exact Or.inr col

/-! ### Per-Leaf Salt-Uniformity & Hiding at Unopened Positions -/

/-- Salt-shift bijection on `Salt248`: uniform random salts stay uniform under any shift `δ`. -/
def saltShiftEquiv (δ : Salt248) : Salt248 ≃ Salt248 :=
  Equiv.addRight δ

/-- Characteristic-two mask-shift involution on `C8` (`Coordinate 8`). -/
def c8MaskEquiv (δ : C8) : C8 ≃ C8 where
  toFun x := addC x δ
  invFun x := addC x δ
  left_inv x := toField.injective (by simp [add_assoc, CharTwo.add_self_eq_zero])
  right_inv x := toField.injective (by simp [add_assoc, CharTwo.add_self_eq_zero])

/-- Parameterized binary cube-Merkle root over an arbitrary leaf carrier `α`, leaf-hash map
`leafHash : α → D`, and internal node combiner `nodeHash` (specializing by `rfl` to `cubeRoot`). -/
def cubeRootWith {α D : Type} (nodeHash : D → D → D) (leafHash : α → D) :
    {k : Nat} → ((Fin k → Bool) → α) → D
  | 0, col => leafHash (col fun i => i.elim0)
  | _ + 1, col =>
      nodeHash
        (cubeRootWith nodeHash leafHash fun t => col (Fin.cases false t))
        (cubeRootWith nodeHash leafHash fun t => col (Fin.cases true t))

theorem cubeRootWith_eq_cubeRoot :
    ∀ {k : Nat} (col : (Fin k → Bool) → C8),
      cubeRootWith merkleDomainsC.hashNode (merkleDomainsC.hashLeaf codecC) col =
        cubeRoot merkleDomainsC codecC col
  | 0, _ => rfl
  | _ + 1, _ => by
      simp only [cubeRootWith, cubeRoot]
      rw [cubeRootWith_eq_cubeRoot, cubeRootWith_eq_cubeRoot]

theorem cubeRootWith_congr {α D : Type} (nodeHash : D → D → D)
    {L₁ L₂ : α → D} :
    ∀ {k : Nat} {col₁ col₂ : (Fin k → Bool) → α},
      (∀ a, L₁ (col₁ a) = L₂ (col₂ a)) →
      cubeRootWith nodeHash L₁ col₁ = cubeRootWith nodeHash L₂ col₂
  | 0, _, _, h => h (fun i => i.elim0)
  | _ + 1, _, _, h => by
      simp only [cubeRootWith]
      rw [cubeRootWith_congr nodeHash (fun t => h (Fin.cases false t)),
          cubeRootWith_congr nodeHash (fun t => h (Fin.cases true t))]

/-- **Per-leaf ROM / Leaf-Oracle Perfect Hiding (`unopened_salted_leaf_oracle_hiding`)**:
for any two bytes `b₀, b₁`, any fresh salt `s₀` at unopened address `idx` (not reused at `a ≠ idx`,
e.g. `s₀ ≠ 0` and distinct from other leaf salts), precomposing the leaf oracle `L` with the
involutive transposition `Equiv.swap (packSaltedLeaf b₀ s₀) (packSaltedLeaf b₁ s₀)` produces the
**exact same Merkle root** with `b₁` at `idx` as `L` produces with `b₀` at `idx`, while leaving
**every other leaf digest** at `a ≠ idx` identical. -/
theorem unopened_salted_leaf_oracle_hiding {D : Type} (nodeHash : D → D → D)
    {k : Nat} (col : (Fin k → Bool) → C8) (idx : Fin k → Bool)
    (b₀ b₁ : UInt8) (s₀ : Salt248)
    (hfresh : ∀ a, a ≠ idx → unpackSalt (col a) ≠ s₀)
    (L : C8 → D) :
    let perm : Equiv.Perm C8 := Equiv.swap (packSaltedLeaf b₀ s₀) (packSaltedLeaf b₁ s₀)
    cubeRootWith nodeHash (L ∘ perm) (Function.update col idx (packSaltedLeaf b₁ s₀)) =
      cubeRootWith nodeHash L (Function.update col idx (packSaltedLeaf b₀ s₀)) ∧
    (∀ a, a ≠ idx → (L ∘ perm) (col a) = L (col a)) := by
  intro perm
  have hother : ∀ a, a ≠ idx → perm (col a) = col a := by
    intro a hne
    have h0 : col a ≠ packSaltedLeaf b₀ s₀ := by
      intro heq; apply hfresh a hne; rw [heq, unpackSalt_packSaltedLeaf]
    have h1 : col a ≠ packSaltedLeaf b₁ s₀ := by
      intro heq; apply hfresh a hne; rw [heq, unpackSalt_packSaltedLeaf]
    exact Equiv.swap_apply_of_ne_of_ne h0 h1
  refine ⟨cubeRootWith_congr nodeHash fun a => ?_, fun a hne => congrArg L (hother a hne)⟩
  by_cases ha : a = idx
  · subst ha
    simp only [Function.update_self, Function.comp_apply, perm, Equiv.swap_apply_right]
  · simp only [Function.update_of_ne ha, Function.comp_apply, hother a ha]

noncomputable instance : Fintype C8 :=
  Fintype.ofEquiv (Fin (capacity 8)) (coordinateFinEquiv 8).symm

/-- Generic measure-preserving bijection law for `BindingGame.prob` (uses `prob_eq_mean` so tactic
terms inside `BindingGame.prob` are never unfolded). -/
theorem prob_eq_of_equiv {S T : Type} [Fintype S] [Fintype T]
    (e : S ≃ T) (p : S → Prop) (q : T → Prop)
    (hpq : ∀ s, p s ↔ q (e s)) :
    BindingGame.prob p = BindingGame.prob q := by
  let _ : DecidablePred p := Classical.decPred p
  let _ : DecidablePred q := Classical.decPred q
  rw [BindingGame.prob_eq_mean p, BindingGame.prob_eq_mean q]
  unfold BindingGame.mean
  rw [Fintype.card_congr e]
  congr 1
  rw [← Equiv.sum_comp e (fun t => if q t then (1 : ℝ) else 0)]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : p s
  · have ht : q (e s) := (hpq s).mp hs
    simp [hs, ht]
  · have ht : ¬ q (e s) := fun hq => hs ((hpq s).mpr hq)
    simp [hs, ht]

/-- **Exact ROM Root-Distribution Equality (`unopened_salted_leaf_rom_prob_eq`)**:
over a uniform random leaf-hash oracle `L : C8 → D` (for any finite digest carrier `[Fintype D]`),
changing `b₀` to `b₁` at an unopened leaf `idx` with fresh salt `s₀` yields **identically
distributed** Merkle roots (`BindingGame.prob` equal for every target `rt : D`). -/
theorem unopened_salted_leaf_rom_prob_eq {D : Type} [Fintype D] [DecidableEq D]
    (nodeHash : D → D → D) {k : Nat} (col : (Fin k → Bool) → C8) (idx : Fin k → Bool)
    (b₀ b₁ : UInt8) (s₀ : Salt248)
    (hfresh : ∀ a, a ≠ idx → unpackSalt (col a) ≠ s₀)
    (rt : D) :
    BindingGame.prob (fun L : C8 → D =>
      cubeRootWith nodeHash L (Function.update col idx (packSaltedLeaf b₀ s₀)) = rt) =
    BindingGame.prob (fun L : C8 → D =>
      cubeRootWith nodeHash L (Function.update col idx (packSaltedLeaf b₁ s₀)) = rt) := by
  let perm : Equiv.Perm C8 := Equiv.swap (packSaltedLeaf b₀ s₀) (packSaltedLeaf b₁ s₀)
  let oracleEquiv : (C8 → D) ≃ (C8 → D) := Equiv.arrowCongr perm (Equiv.refl D)
  refine prob_eq_of_equiv oracleEquiv _ _ fun L => ?_
  have hperm : oracleEquiv L = L ∘ perm := by
    funext x
    change L (perm.symm x) = L (perm x)
    rw [Equiv.symm_swap]
  rw [hperm, (unopened_salted_leaf_oracle_hiding nodeHash col idx b₀ b₁ s₀ hfresh L).1]

/-- **Per-leaf Keyed-Salt Distribution Identity (`unopened_keyed_salt_prob_eq`)**:
for any keyed leaf-digest family `leafDigest : UInt8 → Salt248 → D` where changing `b₀` to `b₁` is
absorbed by a bijection on salts (`∃ σ : Salt248 ≃ Salt248, ∀ s, leafDigest b₀ s = leafDigest b₁ (σ s)`),
changing `b₀` to `b₁` at `idx` (fixing all other leaf digests) produces **identical root probability**
over uniform random `s : Salt248` for every target digest `rt : D`. -/
theorem unopened_keyed_salt_prob_eq {D : Type} [DecidableEq D] {k : Nat}
    (nodeHash : D → D → D) (otherDigest : (Fin k → Bool) → D)
    (leafDigest : UInt8 → Salt248 → D)
    (idx : Fin k → Bool) (b₀ b₁ : UInt8)
    (hbij : ∃ σ : Salt248 ≃ Salt248, ∀ s, leafDigest b₀ s = leafDigest b₁ (σ s))
    (rt : D) :
    BindingGame.prob (fun s : Salt248 =>
      cubeRootWith nodeHash id (Function.update otherDigest idx (leafDigest b₀ s)) = rt) =
    BindingGame.prob (fun s : Salt248 =>
      cubeRootWith nodeHash id (Function.update otherDigest idx (leafDigest b₁ s)) = rt) := by
  obtain ⟨σ, hσ⟩ := hbij
  refine prob_eq_of_equiv σ _ _ fun s => ?_
  rw [← hσ s]

/-- **Concrete `cshakeC` Mask-Uniformity (`maskedCubeRootPreimageEquiv` & `maskedCubeRoot_prob_eq`)**:
under the **actual concrete `cshakeC` Merkle tree** (`cubeRoot merkleDomainsC codecC`, zero ROM
assumption!), XOR-masking leaf `idx` as `addC payload mask` (`mask : C8`, as in `blindTraceEval`)
induces an explicit involutive bijection `m ↦ addC m (addC p₀ p₁)` on `C8` masks preserving the
exact root and uniform root probability for **every** `p₀, p₁` and **every** `rt : Digest`. -/
def maskedLeafShiftEquiv (p₀ p₁ : C8) : C8 ≃ C8 :=
  c8MaskEquiv (addC p₀ p₁)

theorem addC_maskedLeafShift (p₀ p₁ m : C8) :
    addC p₁ (maskedLeafShiftEquiv p₀ p₁ m) = addC p₀ m := by
  apply toField.injective
  simp only [maskedLeafShiftEquiv, c8MaskEquiv, Equiv.coe_fn_mk, toField_addC]
  have hchar : toField p₁ + (toField m + (toField p₀ + toField p₁)) =
      (toField p₁ + toField p₁) + (toField p₀ + toField m) := by ring
  rw [hchar, CharTwo.add_self_eq_zero, zero_add]

theorem maskedCubeRoot_eq_under_shift {k : Nat}
    (col : (Fin k → Bool) → C8) (idx : Fin k → Bool) (p₀ p₁ m : C8) :
    cubeRoot merkleDomainsC codecC
        (Function.update col idx (addC p₁ (maskedLeafShiftEquiv p₀ p₁ m))) =
      cubeRoot merkleDomainsC codecC (Function.update col idx (addC p₀ m)) := by
  rw [addC_maskedLeafShift]

def maskedCubeRootPreimageEquiv {k : Nat}
    (col : (Fin k → Bool) → C8) (idx : Fin k → Bool) (p₀ p₁ : C8) (rt : Digest) :
    {m : C8 // cubeRoot merkleDomainsC codecC (Function.update col idx (addC p₀ m)) = rt} ≃
    {m : C8 // cubeRoot merkleDomainsC codecC (Function.update col idx (addC p₁ m)) = rt} where
  toFun x := ⟨maskedLeafShiftEquiv p₀ p₁ x.1, by rw [maskedCubeRoot_eq_under_shift, x.2]⟩
  invFun y := ⟨maskedLeafShiftEquiv p₁ p₀ y.1, by rw [maskedCubeRoot_eq_under_shift, y.2]⟩
  left_inv x := by
    apply Subtype.ext
    apply toField.injective
    simp only [maskedLeafShiftEquiv, c8MaskEquiv, Equiv.coe_fn_mk, toField_addC]
    have h : toField x.1 + (toField p₀ + toField p₁) + (toField p₁ + toField p₀) =
        toField x.1 + ((toField p₀ + toField p₀) + (toField p₁ + toField p₁)) := by ring
    rw [h]
    simp [CharTwo.add_self_eq_zero]
  right_inv y := by
    apply Subtype.ext
    apply toField.injective
    simp only [maskedLeafShiftEquiv, c8MaskEquiv, Equiv.coe_fn_mk, toField_addC]
    have h : toField y.1 + (toField p₁ + toField p₀) + (toField p₀ + toField p₁) =
        toField y.1 + ((toField p₁ + toField p₁) + (toField p₀ + toField p₀)) := by ring
    rw [h]
    simp [CharTwo.add_self_eq_zero]

theorem maskedCubeRoot_prob_eq {k : Nat}
    (col : (Fin k → Bool) → C8) (idx : Fin k → Bool) (p₀ p₁ : C8) (rt : Digest) :
    BindingGame.prob (fun m : C8 =>
      cubeRoot merkleDomainsC codecC (Function.update col idx (addC p₀ m)) = rt) =
    BindingGame.prob (fun m : C8 =>
      cubeRoot merkleDomainsC codecC (Function.update col idx (addC p₁ m)) = rt) := by
  refine prob_eq_of_equiv (maskedLeafShiftEquiv p₀ p₁) _ _ fun m => ?_
  rw [maskedCubeRoot_eq_under_shift]

/-! ## §3. All Three `ClaimData` Modes (`.accept b`, `.count n`, `.bound lo hi`) -/

namespace Dfaops

/-- Indicator `1` if `next` is an accepting state of `t`, `0` otherwise. -/
def stepHit (t : DfaTable) (next : Nat) : Nat :=
  if t.accepting.getD next false then 1 else 0

/-- Joint `(state, cumulativeAcceptVisits)` fold from `(s, c)` over `w`. -/
def runStateCountFrom (t : DfaTable) : Nat → Nat → List UInt8 → Nat × Nat
  | s, c, [] => (s, c)
  | s, c, b :: rest =>
      let next := t.step s b
      runStateCountFrom t next (c + stepHit t next) rest

/-- **Canonical accepting-state visit counter (`runCount`)**: total number of byte positions in `w`
whose transition lands in an `accepting` state of `t`. -/
def runCount (t : DfaTable) (w : List UInt8) : Nat :=
  (runStateCountFrom t t.initial 0 w).2

theorem runStateCountFrom_fst (t : DfaTable) :
    ∀ (s c : Nat) (w : List UInt8), (runStateCountFrom t s c w).1 = w.foldl t.step s
  | _, _, [] => rfl
  | s, c, b :: rest => runStateCountFrom_fst t (t.step s b) (c + stepHit t (t.step s b)) rest

theorem runStateCountFrom_fst_initial (t : DfaTable) (w : List UInt8) :
    (runStateCountFrom t t.initial 0 w).1 = t.run w :=
  runStateCountFrom_fst t t.initial 0 w

theorem runStateCountFrom_snd_add (t : DfaTable) :
    ∀ (s c : Nat) (w : List UInt8),
      (runStateCountFrom t s c w).2 = c + (runStateCountFrom t s 0 w).2
  | _, c, [] => by simp [runStateCountFrom]
  | s, c, b :: rest => by
      simp only [runStateCountFrom]
      rw [runStateCountFrom_snd_add t (t.step s b) (c + stepHit t (t.step s b)) rest,
          runStateCountFrom_snd_add t (t.step s b) (0 + stepHit t (t.step s b)) rest]
      omega

theorem runStateCountFrom_append_singleton (t : DfaTable) :
    ∀ (s c : Nat) (w : List UInt8) (b : UInt8),
      runStateCountFrom t s c (w ++ [b]) =
        let cur := runStateCountFrom t s c w
        let next := t.step cur.1 b
        (next, cur.2 + stepHit t next)
  | s, c, [], b => by simp [runStateCountFrom]
  | s, c, x :: rest, b => runStateCountFrom_append_singleton t (t.step s x) (c + stepHit t (t.step s x)) rest b

/-- **`runCount` equals `countP` of accepting steps along `t.traceFrom` (`Bread.Step` trace).** -/
theorem runCount_eq_traceFrom_countP (t : DfaTable) (w : List UInt8) :
    runCount t w = (t.traceFrom t.initial w).countP (fun step => t.accepting.getD step.next false) := by
  unfold runCount
  have haux : ∀ (s : Nat) (u : List UInt8),
      (runStateCountFrom t s 0 u).2 =
        (t.traceFrom s u).countP (fun step => t.accepting.getD step.next false) := by
    intro s u
    induction u generalizing s with
    | nil => rfl
    | cons b rest ih =>
        simp only [runStateCountFrom, DfaTable.traceFrom, List.countP_cons]
        rw [runStateCountFrom_snd_add t (t.step s b) (0 + stepHit t (t.step s b)) rest, ih]
        unfold stepHit
        cases t.accepting.getD (t.step s b) false
        · simp
        · simp; omega
  exact haux t.initial w

/-- Executable claim evaluator covering **all three `ClaimData` modes**. -/
def claimDecide (claim : ClaimData) (finalAccepted : Bool) (totalCount : Nat) : Bool :=
  match claim with
  | .accept b => finalAccepted == b
  | .count n => totalCount == n
  | .bound lo hi => decide (lo ≤ totalCount ∧ totalCount ≤ hi)

/-- Whether word `w` satisfies `claim` under `t`. -/
def satisfiesClaim (t : DfaTable) (claim : ClaimData) (w : List UInt8) : Bool :=
  claimDecide claim (t.accepts w) (runCount t w)

@[simp] theorem satisfiesClaim_accept_iff (t : DfaTable) (b : Bool) (w : List UInt8) :
    satisfiesClaim t (.accept b) w = true ↔ t.accepts w = b := by
  simp [satisfiesClaim, claimDecide]

@[simp] theorem satisfiesClaim_count_iff (t : DfaTable) (n : Nat) (w : List UInt8) :
    satisfiesClaim t (.count n) w = true ↔ runCount t w = n := by
  simp [satisfiesClaim, claimDecide]

@[simp] theorem satisfiesClaim_bound_iff (t : DfaTable) (lo hi : Nat) (w : List UInt8) :
    satisfiesClaim t (.bound lo hi) w = true ↔ lo ≤ runCount t w ∧ runCount t w ≤ hi := by
  simp [satisfiesClaim, claimDecide]

end Dfaops

/-! ## §4. Masked Execution Trace, `Tower256SuccinctCheck` Weld, & `PrivateReceipt` -/

/-- 184-bit per-row random mask (`23` bytes; `8 + 16 + 16 + 32 + 184 = 256` bits = `C8`). -/
abbrev RowMask := Fin (2 ^ 184)

instance : Inhabited RowMask := ⟨⟨0, by positivity⟩⟩

/-- One masked DFA + counter step row committed in `traceRoot`. -/
structure TraceRow where
  byte : UInt8
  state : Nat
  next : Nat
  cumCount : Nat
  mask : RowMask
  deriving DecidableEq, Repr

def defaultRow : TraceRow := ⟨0, 0, 0, 0, ⟨0, by positivity⟩⟩

instance : Inhabited TraceRow := ⟨defaultRow⟩

def TraceRow.WellBounded (r : TraceRow) : Prop :=
  r.state < 2 ^ 16 ∧ r.next < 2 ^ 16 ∧ r.cumCount < 2 ^ 32

instance (r : TraceRow) : Decidable r.WellBounded := by
  unfold TraceRow.WellBounded; infer_instance

/-- Canonical 256-bit integer packing of `TraceRow` (`byte | state16 | next16 | cumCount32 | mask184`). -/
def packTraceRowNat (r : TraceRow) : Nat :=
  r.byte.toNat +
    256 * (r.state +
      65536 * (r.next +
        65536 * (r.cumCount +
          4294967296 * r.mask.val)))

theorem packTraceRowNat_lt (r : TraceRow) (hr : r.WellBounded) :
    packTraceRowNat r < 2 ^ 256 := by
  obtain ⟨hs, hn, hc⟩ := hr
  have hb := r.byte.toNat_lt
  have hm := r.mask.isLt
  unfold packTraceRowNat
  have hpow : (256 : Nat) * (65536 * (65536 * (4294967296 * 2 ^ 184))) = 2 ^ 256 := by norm_num
  omega

def packTraceRow (r : TraceRow) : C8 :=
  leafOfNat (packTraceRowNat r)

def unpackTraceRow (c : C8) : TraceRow :=
  let n0 := Coord.toNat 8 c
  let b := UInt8.ofNat (n0 % 256)
  let n1 := n0 / 256
  let s := n1 % 65536
  let n2 := n1 / 65536
  let nx := n2 % 65536
  let n3 := n2 / 65536
  let cc := n3 % 4294967296
  let m := n3 / 4294967296
  ⟨b, s, nx, cc, ⟨m, by
    have hc : Coord.toNat 8 c < 2 ^ 256 := by
      simpa [capacity_eight] using Coord.toNat_lt 8 c
    omega⟩⟩

theorem unpackTraceRow_packTraceRow (r : TraceRow) (hr : r.WellBounded) :
    unpackTraceRow (packTraceRow r) = r := by
  have htn : Coord.toNat 8 (packTraceRow r) = packTraceRowNat r := by
    unfold packTraceRow leafOfNat
    exact Coord.toNat_ofNat 8 _ (by rw [capacity_eight]; exact packTraceRowNat_lt r hr)
  have ⟨hs, hn, hc⟩ := hr
  cases r with
  | mk rb rstate rnext rcc rmask =>
      simp only at hs hn hc
      simp only [unpackTraceRow, htn, packTraceRowNat]
      have hd0 := add_mul_div_eq rb.toNat (rstate + 65536 * (rnext + 65536 * (rcc + 4294967296 * rmask.val)))
        256 (by norm_num) rb.toNat_lt
      have hm0 := add_mul_mod_eq rb.toNat (rstate + 65536 * (rnext + 65536 * (rcc + 4294967296 * rmask.val)))
        256 rb.toNat_lt
      have hd1 := add_mul_div_eq rstate (rnext + 65536 * (rcc + 4294967296 * rmask.val))
        65536 (by norm_num) hs
      have hm1 := add_mul_mod_eq rstate (rnext + 65536 * (rcc + 4294967296 * rmask.val))
        65536 hs
      have hd2 := add_mul_div_eq rnext (rcc + 4294967296 * rmask.val)
        65536 (by norm_num) hn
      have hm2 := add_mul_mod_eq rnext (rcc + 4294967296 * rmask.val)
        65536 hn
      have hd3 := add_mul_div_eq rcc rmask.val 4294967296 (by norm_num) hc
      have hm3 := add_mul_mod_eq rcc rmask.val 4294967296 hc
      simp only [hm0, hd0, hm1, hd1, hm2, hd2, hm3, hd3, UInt8.ofNat_toNat]

theorem packTraceRow_injective {r₁ r₂ : TraceRow} (h₁ : r₁.WellBounded) (h₂ : r₂.WellBounded)
    (heq : packTraceRow r₁ = packTraceRow r₂) : r₁ = r₂ := by
  have := congrArg unpackTraceRow heq
  rwa [unpackTraceRow_packTraceRow r₁ h₁, unpackTraceRow_packTraceRow r₂ h₂] at this

def traceEntries (rows : List TraceRow) : List Nat :=
  rows.map packTraceRowNat

/-- `cSHAKE256` Merkle commitment to the masked execution trace. -/
def traceCommit (rows : List TraceRow) : Digest :=
  denseRoot (traceEntries rows)

/-- Customization string for the 256-bit one-time row pad masking FRI level-0 evaluations. -/
def rowMaskCustomization : List UInt8 :=
  0x06 :: Tower256ConcreteBackend.utf8 "MINIDREGG/TOWER256/PRIVATECERT/ROWMASK/V1"

/-- Unmasked 72-bit row payload (`byte | state16 | next16 | cumCount32`) as `C8`. -/
def rowPayloadC (r : TraceRow) : C8 :=
  leafOfNat (r.byte.toNat + 256 * (r.state + 65536 * (r.next + 65536 * r.cumCount)))

/-- Full-width 256-bit pseudorandom mask derived from `r.mask` under `rowMaskCustomization`. -/
def rowMaskPadC (m : RowMask) : C8 :=
  digestTowerC (cshakeC.xofDigest rowMaskCustomization (codecC.encode (leafOfNat m.val)))

/-- **Blinded FRI level-0 evaluation (`blindTraceEval`)**: XORs all 256 bits of `rowPayloadC r` with
`rowMaskPadC r.mask`, so unopened FRI pair evaluations reveal zero bits of `r.byte`, `r.state`,
`r.next`, or `r.cumCount`. -/
def blindTraceEval (r : TraceRow) : C8 :=
  addC (rowPayloadC r) (rowMaskPadC r.mask)

/-- **Public statement for a private content-bound certificate.** -/
structure PrivateContentCert where
  contentRoot   : Digest
  recordLength  : Nat
  automatonRoot : Digest
  claim         : ClaimData
  friEll        : Nat
  friRounds     : Nat
  friQueries    : Nat
  stepQueries   : Nat
  deriving DecidableEq, Repr

/-- Compact automaton metadata carried in the receipt (dense `delta` stays behind `deltaRoot`). -/
structure AutomatonHeader where
  states    : Nat
  initial   : Nat
  accepting : List Bool
  deltaRoot : Digest
  deriving DecidableEq, Repr

def AutomatonHeader.WellFormed (h : AutomatonHeader) : Prop :=
  0 < h.states ∧ h.states ≤ 2 ^ 16 ∧ h.initial < h.states ∧ h.accepting.length = h.states

instance (h : AutomatonHeader) : Decidable h.WellFormed := by
  unfold AutomatonHeader.WellFormed; infer_instance

def automatonHeaderInput (h : AutomatonHeader) : List UInt8 :=
  envelope (envelope (codecC.encode (leafOfNat h.states)) ++
      envelope (codecC.encode (leafOfNat h.initial))) ++
    envelope (envelope (acceptBytes h.accepting) ++
      envelope (cshakeC.digestCodec.encode h.deltaRoot))

def automatonHeaderCommit (h : AutomatonHeader) : Digest :=
  cshakeC.xofDigest automatonCustomization (automatonHeaderInput h)

def headerOfTable (t : DfaTable) : AutomatonHeader where
  states := t.states
  initial := t.initial
  accepting := t.accepting
  deltaRoot := deltaCommit t

theorem automatonHeaderCommit_table (t : DfaTable) :
    automatonHeaderCommit (headerOfTable t) = automatonCommit t := rfl

theorem automatonHeaderInput_injective (h : AutomatonHeader) (t : DfaTable)
    (hh : h.WellFormed) (ht : t.WellFormed)
    (heq : automatonHeaderInput h = automatonInput t) :
    h = headerOfTable t := by
  have hs₁ : h.states < 2 ^ 256 := lt_of_le_of_lt hh.2.1 (by norm_num)
  have hs₂ : t.states < 2 ^ 256 := lt_of_le_of_lt ht.1 (by norm_num)
  obtain ⟨hm, ha⟩ := pair_eq heq
  obtain ⟨hs, hi⟩ := pair_eq hm
  obtain ⟨hacc, hd⟩ := pair_eq ha
  have eS := leafOfNat_injective hs₁ hs₂ (lawfulCodec_encode_injective codecC hs)
  have eI := leafOfNat_injective (lt_trans hh.2.2.1 hs₁) (lt_trans ht.2.1 hs₂)
    (lawfulCodec_encode_injective codecC hi)
  have eA := acceptBytes_injective hacc
  have eD := lawfulCodec_encode_injective cshakeC.digestCodec hd
  cases h
  simp only [headerOfTable] at eS eI eA eD ⊢
  subst eS eI eA eD
  rfl

/-- Boundary openings at step `0` and step `recordLength - 1`, welding `contentRoot`, `traceRoot`,
`deltaRoot`, and `friReceipt.roots 0` at both endpoints. -/
structure BoundaryOpenings where
  firstRow         : TraceRow
  firstTracePath   : List Digest
  firstSalt        : Salt248
  firstContentPath : List Digest
  firstDeltaPath   : List Digest
  firstFriPath     : List Digest
  lastRow          : TraceRow
  lastTracePath    : List Digest
  lastSalt         : Salt248
  lastContentPath  : List Digest
  lastDeltaPath    : List Digest
  lastFriPath      : List Digest
  deriving DecidableEq, Repr

/-- One Fiat–Shamir sampled step opening at `idx = derivedStepIndex stmt r u`. -/
structure StepOpening where
  salt          : Salt248
  contentPath   : List Digest
  row           : TraceRow
  tracePath     : List Digest
  deltaPath     : List Digest
  friPath       : List Digest
  nextRow       : TraceRow
  nextTracePath : List Digest
  deriving DecidableEq, Repr

/-- **Succinct private-witness receipt (`PrivateReceipt`).** -/
structure PrivateReceipt (ell m friQueries : Nat) where
  header         : AutomatonHeader
  traceRoot      : Digest
  friInitialRoot : Digest
  friReceipt     : CReceipt ell m friQueries
  boundary       : BoundaryOpenings
  stepOpenings   : List StepOpening

/-! ### Constant-Width Statement Framing & Fiat–Shamir Challenge Derivation -/

/-- Constant-width 32-byte coordinate framing for natural parameters (`O(1)` bytes, no unary OOM). -/
def natCoordBytes (n : Nat) : List UInt8 :=
  codecC.encode (leafOfNat n)

def claimBytes : ClaimData → List UInt8
  | .accept b => [0, if b then 1 else 0]
  | .count n => 1 :: natCoordBytes n
  | .bound lo hi => 2 :: (natCoordBytes lo ++ natCoordBytes hi)

/-- Framed statement + `traceRoot` bytes bound into `Tower256SuccinctCheck`'s `TranscriptPins`:
binds **every** field of `PrivateContentCert` plus `traceRoot` in constant width. -/
def privateStatementBytes (stmt : PrivateContentCert) (traceRoot : Digest) : List UInt8 :=
  envelope (cshakeC.digestCodec.encode stmt.contentRoot) ++
    envelope (natCoordBytes stmt.recordLength) ++
    envelope (cshakeC.digestCodec.encode stmt.automatonRoot) ++
    envelope (claimBytes stmt.claim) ++
    envelope (natCoordBytes stmt.friEll) ++
    envelope (natCoordBytes stmt.friRounds) ++
    envelope (natCoordBytes stmt.friQueries) ++
    envelope (natCoordBytes stmt.stepQueries) ++
    envelope (cshakeC.digestCodec.encode traceRoot)

def privateFriPins (stmt : PrivateContentCert) (traceRoot : Digest) : TranscriptPins :=
  { bootstrapPins with statementBytes := privateStatementBytes stmt traceRoot }

/-- Degree schedule `j ↦ max 1 (2 ^ (td - j))` where `td = max 1 (depthOf recordLength)`. -/
def privateDegreeSchedule (recordLength : Nat) (j : Nat) : Nat :=
  let td := Nat.max 1 (depthOf recordLength)
  Nat.max 1 (2 ^ (td - j))

def friStatementOf {ell m : Nat} (stmt : PrivateContentCert) (friInitialRoot : Digest)
    (hm : m ≤ ell) (hell : ell ≤ 256) : CStatement ell m where
  beta := unitBasis ell
  offset := Coordinate.zero 8
  degree := privateDegreeSchedule stmt.recordLength
  queryCount := stmt.friQueries
  initialRoot := friInitialRoot
  independent := unitBasis_independent ell hell
  rounds_le := hm

def stepQueryCustomization : List UInt8 :=
  0x07 :: Tower256ConcreteBackend.utf8 "MINIDREGG/TOWER256/PRIVATECERT/STEPQ/V1"

/-- Domain-separated Fiat–Shamir prefix for step query sampling: wraps `roots` and `challenges` in
separate outer `envelope` frames and omits `finalCoeffs` (already bound by `roots[m]`, preventing
trailing-zero grinding). -/
def stepTranscriptPrefix {ell m fq : Nat}
    (stmt : PrivateContentCert) (r : PrivateReceipt ell m fq) : List UInt8 :=
  envelope (privateStatementBytes stmt r.traceRoot) ++
    envelope ((List.ofFn fun n : Fin (m + 1) =>
      envelope (cshakeC.digestCodec.encode (r.friReceipt.roots n))).flatten) ++
    envelope ((List.ofFn r.friReceipt.challenges).flatMap (fun c => envelope (encodeC c)))

/-- Deterministic Fiat–Shamir step index `u ↦ idx ∈ [0, recordLength)`. -/
def derivedStepIndex {ell m fq : Nat}
    (stmt : PrivateContentCert) (r : PrivateReceipt ell m fq) (u : Nat) : Nat :=
  if stmt.recordLength = 0 then 0
  else
    let d := cshakeC.xofDigest stepQueryCustomization
      (stepTranscriptPrefix stmt r ++ envelope (natCoordBytes u))
    d.value % stmt.recordLength

/-! ### Executable Merkle Verification Helpers -/

def verifyDenseLeaf (depth : Nat) (root : Digest) (idx : Nat) (leaf : C8) (path : List Digest) : Bool :=
  if h : idx < 2 ^ depth then
    decide (recompute merkleDomainsC (merkleDomainsC.hashLeaf codecC leaf)
      (binaryAddressBits depth ⟨idx, h⟩) path = some root)
  else
    false

def headerStepHit (h : AutomatonHeader) (next : Nat) : Nat :=
  if h.accepting.getD next false then 1 else 0

/-- Check one sampled step opening at `idx` against `contentRoot`, `traceRoot`, `deltaRoot`, and `friInitialRoot`. -/
def checkStepOpening (ell : Nat) (stmt : PrivateContentCert) (hdr : AutomatonHeader)
    (traceRoot friRoot0 : Digest) (idx : Nat) (o : StepOpening) : Bool :=
  let dRec := depthOf stmt.recordLength
  let dDelta := depthOf (hdr.states * 256)
  let deltaIdx := 256 * o.row.state + o.row.byte.toNat
  decide o.row.WellBounded &&
  decide (o.row.state < hdr.states ∧ o.row.next < hdr.states) &&
  verifyDenseLeaf dRec stmt.contentRoot idx (packSaltedLeaf o.row.byte o.salt) o.contentPath &&
  verifyDenseLeaf dRec traceRoot idx (packTraceRow o.row) o.tracePath &&
  verifyDenseLeaf dDelta hdr.deltaRoot deltaIdx (leafOfNat o.row.next) o.deltaPath &&
  verifyDenseLeaf ell friRoot0 idx (blindTraceEval o.row) o.friPath &&
  (if idx + 1 < stmt.recordLength then
    decide o.nextRow.WellBounded &&
    verifyDenseLeaf dRec traceRoot (idx + 1) (packTraceRow o.nextRow) o.nextTracePath &&
    decide (o.nextRow.state = o.row.next ∧
            o.nextRow.cumCount = o.row.cumCount + headerStepHit hdr o.row.next)
   else
    decide (o.nextRow = defaultRow ∧ o.nextTracePath = []))

/-- Check initial (`idx = 0`) and terminal (`idx = recordLength - 1`) boundaries + `ClaimData`. -/
def checkBoundary (ell : Nat) (stmt : PrivateContentCert) (hdr : AutomatonHeader)
    (traceRoot friRoot0 : Digest) (b : BoundaryOpenings) : Bool :=
  let dRec := depthOf stmt.recordLength
  let dDelta := depthOf (hdr.states * 256)
  let firstDeltaIdx := 256 * b.firstRow.state + b.firstRow.byte.toNat
  let lastIdx := stmt.recordLength - 1
  let lastDeltaIdx := 256 * b.lastRow.state + b.lastRow.byte.toNat
  let finalAcc := hdr.accepting.getD b.lastRow.next false
  let finalCount := b.lastRow.cumCount + headerStepHit hdr b.lastRow.next
  decide b.firstRow.WellBounded &&
  decide b.lastRow.WellBounded &&
  decide (b.firstRow.state = hdr.initial ∧ b.firstRow.cumCount = 0 ∧ b.firstRow.next < hdr.states) &&
  verifyDenseLeaf dRec stmt.contentRoot 0 (packSaltedLeaf b.firstRow.byte b.firstSalt) b.firstContentPath &&
  verifyDenseLeaf dRec traceRoot 0 (packTraceRow b.firstRow) b.firstTracePath &&
  verifyDenseLeaf dDelta hdr.deltaRoot firstDeltaIdx (leafOfNat b.firstRow.next) b.firstDeltaPath &&
  verifyDenseLeaf ell friRoot0 0 (blindTraceEval b.firstRow) b.firstFriPath &&
  decide (b.lastRow.state < hdr.states ∧ b.lastRow.next < hdr.states) &&
  verifyDenseLeaf dRec stmt.contentRoot lastIdx (packSaltedLeaf b.lastRow.byte b.lastSalt) b.lastContentPath &&
  verifyDenseLeaf dRec traceRoot lastIdx (packTraceRow b.lastRow) b.lastTracePath &&
  verifyDenseLeaf dDelta hdr.deltaRoot lastDeltaIdx (leafOfNat b.lastRow.next) b.lastDeltaPath &&
  verifyDenseLeaf ell friRoot0 lastIdx (blindTraceEval b.lastRow) b.lastFriPath &&
  Dfaops.claimDecide stmt.claim finalAcc finalCount

/-- **Executable root-only private certificate verifier (`checkPrivate`)**:
enforces `1 ≤ recordLength ≤ 2^32`, strict rate `≤ 1/2` LDE (`max 1 (depthOf recordLength) < friEll ≤ 24`),
authenticates `AutomatonHeader` against `stmt.automatonRoot`, runs `Tower256SuccinctCheck.check` on
`r.friReceipt`, verifies `BoundaryOpenings`, and checks all `stmt.stepQueries` Fiat–Shamir openings. -/
def checkPrivate {ell m fq : Nat} (stmt : PrivateContentCert)
    (r : PrivateReceipt ell m fq) : Bool :=
  if hm : m ≤ ell then
    if hell : ell ≤ 24 then
      let hell256 : ell ≤ 256 := le_trans hell (by norm_num)
      decide (ell = stmt.friEll ∧ m = stmt.friRounds ∧ fq = stmt.friQueries) &&
      decide (0 < stmt.recordLength ∧ stmt.recordLength ≤ 2 ^ 32) &&
      decide (Nat.max 1 (depthOf stmt.recordLength) < ell) &&
      decide (stmt.friQueries ≤ 4096 ∧ stmt.stepQueries ≤ 4096) &&
      decide r.header.WellFormed &&
      decide (automatonHeaderCommit r.header = stmt.automatonRoot) &&
      decide (r.stepOpenings.length = stmt.stepQueries) &&
      Tower256SuccinctCheck.check
        (friStatementOf stmt r.friInitialRoot hm hell256)
        (privateFriPins stmt r.traceRoot)
        r.friReceipt &&
      checkBoundary ell stmt r.header r.traceRoot r.friInitialRoot r.boundary &&
      (List.range stmt.stepQueries).all fun u =>
        match r.stepOpenings[u]? with
        | none => false
        | some op =>
            checkStepOpening ell stmt r.header r.traceRoot r.friInitialRoot
              (derivedStepIndex stmt r u) op
    else false
  else false

/-! ## §5. Soundness Reduction (`checkPrivate_sound_or_collision`), Premise Inhabitation & Bound -/

/-- Named commitment relation for a private record `(w, salts)` and `DfaTable`. -/
def CommitsPrivate (stmt : PrivateContentCert) (t : DfaTable)
    (w : List UInt8) (salts : List Salt248) : Prop :=
  t.WellFormed ∧
  automatonCommit t = stmt.automatonRoot ∧
  w.length = stmt.recordLength ∧
  salts.length = stmt.recordLength ∧
  saltedContentCommit w salts = stmt.contentRoot

/-- Full semantic truth of `PrivateContentCert` on `(t, w, salts)` across `.accept`, `.count`, `.bound`. -/
def PrivateHolds (stmt : PrivateContentCert) (t : DfaTable)
    (w : List UInt8) (salts : List Salt248) : Prop :=
  CommitsPrivate stmt t w salts ∧ w ≠ [] ∧ Dfaops.satisfiesClaim t stmt.claim w = true

/-- Step validity of `rows` at position `i < w.length` against `t` and `w`. -/
def StepValidAt (t : DfaTable) (w : List UInt8) (rows : List TraceRow) (i : Nat) : Prop :=
  let r := rows.getD i defaultRow
  r.byte = w.getD i 0 ∧
  r.next = t.step r.state r.byte ∧
  (i + 1 < w.length →
    let rNext := rows.getD (i + 1) defaultRow
    rNext.state = r.next ∧ rNext.cumCount = r.cumCount + Dfaops.stepHit t r.next)

theorem allStepsValid_prefix_eq (t : DfaTable) (w : List UInt8) (rows : List TraceRow)
    (hinit : (rows.getD 0 defaultRow).state = t.initial ∧ (rows.getD 0 defaultRow).cumCount = 0)
    (hall : ∀ j, j < w.length → StepValidAt t w rows j) :
    ∀ i, i < w.length →
      (rows.getD i defaultRow).state = (Dfaops.runStateCountFrom t t.initial 0 (w.take i)).1 ∧
      (rows.getD i defaultRow).cumCount = (Dfaops.runStateCountFrom t t.initial 0 (w.take i)).2
  | 0, _ => by
      simp only [List.take_zero, Dfaops.runStateCountFrom]
      exact hinit
  | i + 1, hi => by
      have hi0 : i < w.length := by omega
      obtain ⟨ihS, ihC⟩ := allStepsValid_prefix_eq t w rows hinit hall i hi0
      obtain ⟨hb, hnx, hchain⟩ := hall i hi0
      obtain ⟨hns, hnc⟩ := hchain hi
      have htake : w.take (i + 1) = w.take i ++ [w[i]] := List.take_succ_eq_append_getElem hi0
      have hgetD : w.getD i 0 = w[i] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi0]
      rw [htake, Dfaops.runStateCountFrom_append_singleton]
      dsimp only
      rw [← ihS, ← ihC, ← hgetD, ← hb, ← hnx]
      exact ⟨hns, hnc⟩

/-- **Inductive Trace Completeness-to-Soundness Bridge (`allStepsValid_implies_satisfiesClaim`)**:
if step `0` initializes `(t.initial, 0)`, step `w.length - 1` passes `claimDecide`, and every step
`i < w.length` satisfies `StepValidAt`, then `w` genuinely satisfies `claim` on `t`. -/
theorem allStepsValid_implies_satisfiesClaim (t : DfaTable) (claim : ClaimData)
    (w : List UInt8) (rows : List TraceRow) (hne : 0 < w.length)
    (hinit : (rows.getD 0 defaultRow).state = t.initial ∧ (rows.getD 0 defaultRow).cumCount = 0)
    (hlast : Dfaops.claimDecide claim
      (t.accepting.getD (rows.getD (w.length - 1) defaultRow).next false)
      ((rows.getD (w.length - 1) defaultRow).cumCount +
        Dfaops.stepHit t (rows.getD (w.length - 1) defaultRow).next) = true)
    (hall : ∀ j, j < w.length → StepValidAt t w rows j) :
    Dfaops.satisfiesClaim t claim w = true := by
  let lastIdx := w.length - 1
  have hlt : lastIdx < w.length := by omega
  obtain ⟨hS, hC⟩ := allStepsValid_prefix_eq t w rows hinit hall lastIdx hlt
  obtain ⟨hb, hnx, -⟩ := hall lastIdx hlt
  have hgetD : w.getD lastIdx 0 = w[lastIdx] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  have hw_eq : w = w.take lastIdx ++ [w[lastIdx]] := by
    have h1 := List.take_succ_eq_append_getElem hlt
    have h2 : lastIdx + 1 = w.length := by omega
    rw [h2, List.take_length] at h1
    exact h1
  have hfull := Dfaops.runStateCountFrom_append_singleton t t.initial 0 (w.take lastIdx) w[lastIdx]
  rw [← hw_eq] at hfull
  dsimp only at hfull
  rw [← hS, ← hC, ← hgetD, ← hb, ← hnx] at hfull
  have hrun : (rows.getD lastIdx defaultRow).next = t.run w := by
    have hfst := congrArg Prod.fst hfull
    rw [Dfaops.runStateCountFrom_fst_initial] at hfst
    exact hfst.symm
  have hcnt : (rows.getD lastIdx defaultRow).cumCount +
      Dfaops.stepHit t (rows.getD lastIdx defaultRow).next = Dfaops.runCount t w := by
    have hsnd := congrArg Prod.snd hfull
    exact hsnd.symm
  unfold Dfaops.satisfiesClaim DfaTable.accepts
  rw [← hrun, ← hcnt]
  exact hlast

/-- **Contrapositive Discrepancy Lemma (`invalid_claim_forces_bad_step`)**:
whenever a record `w` fails `satisfiesClaim t claim w` while boundary rows hold, there **must**
exist at least one step `i < w.length` violating `StepValidAt t w rows i`. -/
theorem invalid_claim_forces_bad_step (t : DfaTable) (claim : ClaimData)
    (w : List UInt8) (rows : List TraceRow) (hne : 0 < w.length)
    (hinit : (rows.getD 0 defaultRow).state = t.initial ∧ (rows.getD 0 defaultRow).cumCount = 0)
    (hlast : Dfaops.claimDecide claim
      (t.accepting.getD (rows.getD (w.length - 1) defaultRow).next false)
      ((rows.getD (w.length - 1) defaultRow).cumCount +
        Dfaops.stepHit t (rows.getD (w.length - 1) defaultRow).next) = true)
    (hbad : Dfaops.satisfiesClaim t claim w = false) :
    ∃ i, i < w.length ∧ ¬ StepValidAt t w rows i := by
  by_contra hno
  push Not at hno
  have hok := allStepsValid_implies_satisfiesClaim t claim w rows hne hinit hlast hno
  rw [hok] at hbad
  exact Bool.noConfusion hbad

/-- The explicit sampled-query miss event: some step `i < recordLength` violates `StepValidAt`,
and every Fiat–Shamir step query `u < stepQueries` landed outside `i`. -/
def StepSamplingMiss {ell m fq : Nat} (stmt : PrivateContentCert)
    (t : DfaTable) (w : List UInt8) (rows : List TraceRow)
    (r : PrivateReceipt ell m fq) : Prop :=
  ∃ i, i < stmt.recordLength ∧ ¬ StepValidAt t w rows i ∧
    ∀ u, u < stmt.stepQueries → derivedStepIndex stmt r u ≠ i

theorem verifyDenseLeaf_eq_or_pathCollision
    (entries : List Nat) (idx : Nat) (hidx : idx < entries.length)
    (hent : entries.getD idx 0 < 2 ^ 256)
    (leafVal : Nat) (hleaf : leafVal < 2 ^ 256)
    (path : List Digest)
    (hver : verifyDenseLeaf (depthOf entries.length) (denseRoot entries) idx (leafOfNat leafVal) path = true) :
    leafVal = entries.getD idx 0 ∨
      let f := pathCollision merkleDomainsC codecC (leafOfNat leafVal)
        (binaryAddressBits (depthOf entries.length)
          ⟨idx, lt_of_lt_of_le hidx (le_two_pow_depthOf entries.length)⟩)
        path (denseColumn (depthOf entries.length) entries)
      FramedXofCollision cshakeC f.customization f.left f.right := by
  have hlt : idx < 2 ^ depthOf entries.length :=
    lt_of_lt_of_le hidx (le_two_pow_depthOf entries.length)
  unfold verifyDenseLeaf at hver
  rw [dite_eq_left hlt, decide_eq_true_eq] at hver
  rcases recompute_eq_or_pathCollision merkleDomainsC codecC (leafOfNat leafVal)
      (binaryAddressBits (depthOf entries.length) ⟨idx, hlt⟩) path
      (denseColumn (depthOf entries.length) entries) hver with heq | hcol
  · left
    have hcol_val : denseColumn (depthOf entries.length) entries
        (binaryAddressBits (depthOf entries.length) ⟨idx, hlt⟩) =
        leafOfNat (entries.getD idx 0) := by
      simp [denseColumn, binaryAddressBits]
    rw [hcol_val] at heq
    exact leafOfNat_injective hleaf hent heq
  · exact Or.inr hcol

theorem verifyDenseLeaf_eq_or_pathCollision_at
    (d : Nat) (entries : List Nat) (hd : d = depthOf entries.length)
    (idx : Nat) (hidx : idx < entries.length)
    (hent : entries.getD idx 0 < 2 ^ 256)
    (leafVal : Nat) (hleaf : leafVal < 2 ^ 256)
    (path : List Digest)
    (hver : verifyDenseLeaf d (denseRoot entries) idx (leafOfNat leafVal) path = true) :
    leafVal = entries.getD idx 0 ∨
      ∃ hlt : idx < 2 ^ d,
        FramedXofCollision cshakeC
          (pathCollision merkleDomainsC codecC (leafOfNat leafVal)
            (binaryAddressBits d ⟨idx, hlt⟩) path (denseColumn d entries)).customization
          (pathCollision merkleDomainsC codecC (leafOfNat leafVal)
            (binaryAddressBits d ⟨idx, hlt⟩) path (denseColumn d entries)).left
          (pathCollision merkleDomainsC codecC (leafOfNat leafVal)
            (binaryAddressBits d ⟨idx, hlt⟩) path (denseColumn d entries)).right := by
  subst hd
  rcases verifyDenseLeaf_eq_or_pathCollision entries idx hidx hent leafVal hleaf path hver with heq | hcol
  · exact Or.inl heq
  · exact Or.inr ⟨lt_of_lt_of_le hidx (le_two_pow_depthOf entries.length), hcol⟩

/-- Level-0 FRI coordinate of a natural index `idx < 2 ^ ell`. -/
noncomputable def friCoord0 {ell : Nat} (idx : Nat) (h : idx < 2 ^ ell) : AdditiveFriLevels ell 0 :=
  (additiveFriLevelEquivPowerTwo ell 0).symm ⟨idx, by simpa using h⟩

theorem verifyDenseLeaf_friWeld_or_collision {ell m : Nat}
    (T : RawTranscript (rawPcs ell)) (challenges : Fin m → Tower256)
    (friRoot0 : Digest) (hroot : T.rootAt challenges 0 (Nat.zero_le m) = friRoot0)
    (idx : Nat) (hidx : idx < 2 ^ ell) (val : C8) (path : List Digest)
    (hver : verifyDenseLeaf ell friRoot0 idx val path = true) :
    toField val = T.wordAt challenges 0 (Nat.zero_le m) (friCoord0 idx hidx) ∨
      ExtractedCollision (rawPcs ell).backend.merkle ((rawPcs ell).level 0).port
        ((rawPcs ell).attemptAgainstWord 0 (T.wordAt challenges 0 (Nat.zero_le m))
          friRoot0 (friCoord0 idx hidx) (toField val)
          (merkleDomainsC.proofCodec.encode path)) := by
  unfold verifyDenseLeaf at hver
  rw [dite_eq_left hidx, decide_eq_true_eq] at hver
  have hrec : recomputesC (ell := ell) 0 friRoot0 (friCoord0 idx hidx) val path = true := by
    unfold recomputesC friCoord0
    simp only [Nat.sub_zero, Equiv.apply_symm_apply, decide_eq_true_eq]
    exact hver
  have hopen : ((rawPcs ell).opening 0).verifyOpen friRoot0 (friCoord0 idx hidx) (toField val)
      (merkleDomainsC.proofCodec.encode path) := by
    rw [verifyOpen_iff, verifyOpenC_encode]
    exact hrec
  exact (rawPcs ell).accepted_value_eq_or_extractedCollision 0
    (T.wordAt challenges 0 (Nat.zero_le m)) friRoot0 (friCoord0 idx hidx) (toField val)
    (merkleDomainsC.proofCodec.encode path)
    (by rw [← hroot]; exact T.rootAt_eq_commit challenges 0 (Nat.zero_le m)) hopen

/-- Explicit frame collision predicate. -/
def ExplicitFrameCollision (f : Frames) : Prop :=
  FramedXofCollision cshakeC f.customization f.left f.right

/-- Bundle of all concrete, input-pinned collision events for `checkPrivate_sound_or_collision`
(including `pathCollision` against `contentRoot`, `traceRoot`, `deltaRoot`, and level-0 FRI weld
`ExtractedCollision` against `T`). -/
def PrivateCertCollision {ell m fq : Nat} (stmt : PrivateContentCert)
    (r : PrivateReceipt ell m fq) (hm : m ≤ ell) (hell : ell ≤ 256)
    (t : DfaTable) (w : List UInt8) (salts : List Salt248) (rows : List TraceRow)
    (T : RawTranscript (rawPcs ell)) : Prop :=
  let sFri := friStatementOf stmt r.friInitialRoot hm hell
  let chals := (r.friReceipt.denote sFri).challenges
  let w0 := T.wordAt chals 0 (Nat.zero_le m)
  let dRec := depthOf stmt.recordLength
  let dDelta := depthOf (t.states * 256)
  let cCol := denseColumn dRec (saltedEntries w salts)
  let tCol := denseColumn dRec (traceEntries rows)
  let δCol := denseColumn dDelta t.delta
  FramedXofCollision cshakeC automatonCustomization (automatonHeaderInput r.header) (automatonInput t) ∨
  FinalCollision (rawPcs ell) sFri.denote (r.friReceipt.denote sFri) T ∨
  ReceiptCollision (rawPcs ell) (toRawStatement sFri.denote T) (r.friReceipt.denote sFri).toRaw ∨
  (∃ h0f : 0 < 2 ^ ell,
    ExtractedCollision (rawPcs ell).backend.merkle ((rawPcs ell).level 0).port
      ((rawPcs ell).attemptAgainstWord 0 w0 r.friInitialRoot (friCoord0 0 h0f)
        (toField (blindTraceEval r.boundary.firstRow))
        (merkleDomainsC.proofCodec.encode r.boundary.firstFriPath))) ∨
  (∃ hlf : stmt.recordLength - 1 < 2 ^ ell,
    ExtractedCollision (rawPcs ell).backend.merkle ((rawPcs ell).level 0).port
      ((rawPcs ell).attemptAgainstWord 0 w0 r.friInitialRoot (friCoord0 (stmt.recordLength - 1) hlf)
        (toField (blindTraceEval r.boundary.lastRow))
        (merkleDomainsC.proofCodec.encode r.boundary.lastFriPath))) ∨
  (∃ h0 : 0 < 2 ^ dRec,
    ExplicitFrameCollision (pathCollision merkleDomainsC codecC (packTraceRow r.boundary.firstRow)
      (binaryAddressBits dRec ⟨0, h0⟩) r.boundary.firstTracePath tCol)) ∨
  (∃ hl : stmt.recordLength - 1 < 2 ^ dRec,
    ExplicitFrameCollision (pathCollision merkleDomainsC codecC (packTraceRow r.boundary.lastRow)
      (binaryAddressBits dRec ⟨stmt.recordLength - 1, hl⟩) r.boundary.lastTracePath tCol)) ∨
  (∃ u : Fin stmt.stepQueries, ∃ op : StepOpening,
    r.stepOpenings[u.val]? = some op ∧
    let idx := derivedStepIndex stmt r u.val
    (∃ hi : idx < 2 ^ dRec,
      ExplicitFrameCollision (pathCollision merkleDomainsC codecC (packSaltedLeaf op.row.byte op.salt)
        (binaryAddressBits dRec ⟨idx, hi⟩) op.contentPath cCol)) ∨
    (∃ hi : idx < 2 ^ dRec,
      ExplicitFrameCollision (pathCollision merkleDomainsC codecC (packTraceRow op.row)
        (binaryAddressBits dRec ⟨idx, hi⟩) op.tracePath tCol)) ∨
    (∃ hd : 256 * op.row.state + op.row.byte.toNat < 2 ^ dDelta,
      ExplicitFrameCollision (pathCollision merkleDomainsC codecC (leafOfNat op.row.next)
        (binaryAddressBits dDelta ⟨256 * op.row.state + op.row.byte.toNat, hd⟩) op.deltaPath δCol)) ∨
    (∃ hn : idx + 1 < 2 ^ dRec,
      idx + 1 < stmt.recordLength ∧
      ExplicitFrameCollision (pathCollision merkleDomainsC codecC (packTraceRow op.nextRow)
        (binaryAddressBits dRec ⟨idx + 1, hn⟩) op.nextTracePath tCol)))

theorem traceEntries_getD_eq (rows : List TraceRow) (idx : Nat) (hidx : idx < rows.length) :
    (traceEntries rows).getD idx 0 = packTraceRowNat (rows.getD idx defaultRow) := by
  simp [traceEntries, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]

theorem saltedEntries_getD_eq (w : List UInt8) (salts : List Salt248)
    (hs : salts.length = w.length) (idx : Nat) (hidx : idx < w.length) :
    (saltedEntries w salts).getD idx 0 = saltedLeafNat (w.getD idx 0) (salts.getD idx default) := by
  have hsi : idx < salts.length := hs ▸ hidx
  simp [saltedEntries, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem hsi]

/-- **Main Soundness Theorem (`checkPrivate_sound_or_collision`)**:
for any accepted `PrivateReceipt` (`checkPrivate stmt r = true`), any named `(t, w, salts)`
committed by `stmt`, any well-bounded `rows` committed by `r.traceRoot`, and any FRI strategy `T`
consistent with `r.friReceipt`:
1. **Exact claim + FRI proximity + boundary level-0 weld hold:**
   `PrivateHolds stmt t w salts` (`.accept b`, `.count n`, or `.bound lo hi`), `IdealAccept` holds
   for `T`, AND `T`'s level-0 word equals `toField (blindTraceEval ...)` at both endpoints `0` and
   `recordLength - 1`, **OR**
2. **Sampled step miss:** an explicit bad step `i < recordLength` was missed by all `stepQueries`
   Fiat–Shamir draws (`StepSamplingMiss`), **OR**
3. **Explicit `cSHAKE256` collision:** an input-pinned `PrivateCertCollision` holds. -/
theorem checkPrivate_sound_or_collision {ell m fq : Nat}
    (stmt : PrivateContentCert)
    (r : PrivateReceipt ell m fq)
    (accepted : checkPrivate stmt r = true)
    (t : DfaTable) (w : List UInt8) (salts : List Salt248)
    (named : CommitsPrivate stmt t w salts)
    (rows : List TraceRow) (hrowsLen : rows.length = stmt.recordLength)
    (hrowsWb : ∀ row ∈ rows, row.WellBounded)
    (hrowsRoot : traceCommit rows = r.traceRoot)
    (T : RawTranscript (rawPcs ell))
    (hcons : ∀ (hm : m ≤ ell) (hell : ell ≤ 256),
      let sFri := friStatementOf stmt r.friInitialRoot hm hell
      Consistent sFri.denote (r.friReceipt.denote sFri) T) :
    ∃ (hm : m ≤ ell) (hell : ell ≤ 256) (h0f : 0 < 2 ^ ell) (hlf : stmt.recordLength - 1 < 2 ^ ell),
      let sFri := friStatementOf stmt r.friInitialRoot hm hell
      let chals := (r.friReceipt.denote sFri).challenges
      (PrivateHolds stmt t w salts ∧
        toField (blindTraceEval (rows.getD 0 defaultRow)) =
          T.wordAt chals 0 (Nat.zero_le m) (friCoord0 0 h0f) ∧
        toField (blindTraceEval (rows.getD (stmt.recordLength - 1) defaultRow)) =
          T.wordAt chals 0 (Nat.zero_le m) (friCoord0 (stmt.recordLength - 1) hlf) ∧
        ∃ seeds, IdealAccept (toRawStatement sFri.denote T) chals seeds) ∨
      StepSamplingMiss stmt t w rows r ∨
      PrivateCertCollision stmt r hm hell t w salts rows T := by
  unfold checkPrivate at accepted
  split at accepted
  · rename_i hm
    split at accepted
    · rename_i hell24
      have hell : ell ≤ 256 := le_trans hell24 (by norm_num)
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at accepted
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, ⟨hpos, _⟩⟩, htdLt⟩, _⟩, hhdrWf⟩, hhdrRoot⟩, hstepLen⟩, hfriCheck⟩, hbnd⟩, hsteps⟩ := accepted
      have h0f : 0 < 2 ^ ell := by positivity
      have hdRecLt : depthOf stmt.recordLength < ell := lt_of_le_of_lt (Nat.le_max_right _ _) htdLt
      have hlf : stmt.recordLength - 1 < 2 ^ ell := by
        have h1 : stmt.recordLength - 1 < stmt.recordLength := by omega
        have h2 : stmt.recordLength ≤ 2 ^ depthOf stmt.recordLength := le_two_pow_depthOf _
        have h3 : 2 ^ depthOf stmt.recordLength ≤ 2 ^ ell :=
          Nat.pow_le_pow_right (by norm_num) (le_of_lt hdRecLt)
        omega
      refine ⟨hm, hell, h0f, hlf, ?_⟩
      obtain ⟨htWf, htRoot, hwLen, hsLen, hcRoot⟩ := named
      by_cases hhdrIn : automatonHeaderInput r.header = automatonInput t
      · have hhdrEq : r.header = headerOfTable t :=
          automatonHeaderInput_injective r.header t hhdrWf htWf hhdrIn
        let sFri := friStatementOf stmt r.friInitialRoot hm hell
        have hSucc := (Tower256SuccinctCheck.check_iff sFri (privateFriPins stmt r.traceRoot) r.friReceipt).mp hfriCheck
        have hRoot0Eq : T.rootAt (r.friReceipt.denote sFri).challenges 0 (Nat.zero_le m) = r.friInitialRoot := by
          rw [hcons hm hell 0 (Nat.zero_le m)]
          exact hSucc.2.1
        rcases succinct_accepts_ideal_or_collision (rawPcs ell) sFri.denote
            (privateFriPins stmt r.traceRoot) (r.friReceipt.denote sFri) T (hcons hm hell) hSucc with
          friFinalCol | friRecCol | hIdeal
        · exact Or.inr (Or.inr (Or.inr (Or.inl friFinalCol)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl friRecCol))))
        · unfold checkBoundary at hbnd
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hbnd
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hbFirstWb, hbLastWb⟩, hbInit⟩, _⟩, hbFirstTr⟩, _⟩, hbFirstFri⟩, _⟩, _⟩, hbLastTr⟩, _⟩, hbLastFri⟩, hbClaim⟩ := hbnd
          have htrLen : (traceEntries rows).length = stmt.recordLength := by
            simp [traceEntries, hrowsLen]
          have h0_lt_rows : 0 < rows.length := by omega
          have hlast_lt_rows : stmt.recordLength - 1 < rows.length := by omega
          have hrow0_wb : (rows.getD 0 defaultRow).WellBounded := by
            apply hrowsWb
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0_lt_rows]
          have hrowL_wb : (rows.getD (stmt.recordLength - 1) defaultRow).WellBounded := by
            apply hrowsWb
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlast_lt_rows]
          -- Weld firstRow to `T.wordAt ... 0`
          rcases verifyDenseLeaf_friWeld_or_collision T (r.friReceipt.denote sFri).challenges
              r.friInitialRoot hRoot0Eq 0 h0f (blindTraceEval r.boundary.firstRow)
              r.boundary.firstFriPath hbFirstFri with hWeld0 | hWeld0Col
          · -- Weld lastRow to `T.wordAt ... (recordLength - 1)`
            rcases verifyDenseLeaf_friWeld_or_collision T (r.friReceipt.denote sFri).challenges
                r.friInitialRoot hRoot0Eq (stmt.recordLength - 1) hlf (blindTraceEval r.boundary.lastRow)
                r.boundary.lastFriPath hbLastFri with hWeldL | hWeldLCol
            · -- Check `firstRow` against `rows[0]`
              have hbFirstTr' : verifyDenseLeaf (depthOf stmt.recordLength) (denseRoot (traceEntries rows))
                  0 (leafOfNat (packTraceRowNat r.boundary.firstRow)) r.boundary.firstTracePath = true := by
                simpa [traceCommit, ← hrowsRoot, packTraceRow] using hbFirstTr
              rcases verifyDenseLeaf_eq_or_pathCollision_at (depthOf stmt.recordLength)
                  (traceEntries rows) (by rw [htrLen]) 0 (by omega)
                  (by rw [traceEntries_getD_eq rows 0 h0_lt_rows]; exact packTraceRowNat_lt _ hrow0_wb)
                  (packTraceRowNat r.boundary.firstRow) (packTraceRowNat_lt _ hbFirstWb)
                  r.boundary.firstTracePath hbFirstTr' with hFirstNat | ⟨h0d, hFirstCol⟩
              · have hFirstRowEq : r.boundary.firstRow = rows.getD 0 defaultRow := by
                  apply packTraceRow_injective hbFirstWb hrow0_wb
                  unfold packTraceRow
                  rw [hFirstNat, traceEntries_getD_eq rows 0 h0_lt_rows]
                -- Check `lastRow` against `rows[recordLength - 1]`
                have hbLastTr' : verifyDenseLeaf (depthOf stmt.recordLength) (denseRoot (traceEntries rows))
                    (stmt.recordLength - 1) (leafOfNat (packTraceRowNat r.boundary.lastRow)) r.boundary.lastTracePath = true := by
                  simpa [traceCommit, ← hrowsRoot, packTraceRow] using hbLastTr
                rcases verifyDenseLeaf_eq_or_pathCollision_at (depthOf stmt.recordLength)
                    (traceEntries rows) (by rw [htrLen]) (stmt.recordLength - 1) (by omega)
                    (by rw [traceEntries_getD_eq rows _ hlast_lt_rows]; exact packTraceRowNat_lt _ hrowL_wb)
                    (packTraceRowNat r.boundary.lastRow) (packTraceRowNat_lt _ hbLastWb)
                    r.boundary.lastTracePath hbLastTr' with hLastNat | ⟨hld, hLastCol⟩
                · have hLastRowEq : r.boundary.lastRow = rows.getD (stmt.recordLength - 1) defaultRow := by
                    apply packTraceRow_injective hbLastWb hrowL_wb
                    unfold packTraceRow
                    rw [hLastNat, traceEntries_getD_eq rows _ hlast_lt_rows]
                  by_cases hSat : Dfaops.satisfiesClaim t stmt.claim w = true
                  · left
                    have hwNe : w ≠ [] := by
                      intro hnil; rw [hnil] at hwLen; simp at hwLen; omega
                    exact ⟨⟨⟨htWf, htRoot, hwLen, hsLen, hcRoot⟩, hwNe, hSat⟩,
                      hFirstRowEq ▸ hWeld0, hLastRowEq ▸ hWeldL, hIdeal⟩
                  · have hSatFalse : Dfaops.satisfiesClaim t stmt.claim w = false :=
                      Bool.eq_false_iff.mpr hSat
                    have hInitRows : (rows.getD 0 defaultRow).state = t.initial ∧
                        (rows.getD 0 defaultRow).cumCount = 0 := by
                      rw [← hFirstRowEq]
                      exact ⟨by simpa [hhdrEq, headerOfTable] using hbInit.1, hbInit.2.1⟩
                    have hLastRows : Dfaops.claimDecide stmt.claim
                        (t.accepting.getD (rows.getD (w.length - 1) defaultRow).next false)
                        ((rows.getD (w.length - 1) defaultRow).cumCount +
                          Dfaops.stepHit t (rows.getD (w.length - 1) defaultRow).next) = true := by
                      rw [hwLen, ← hLastRowEq]
                      simpa [hhdrEq, headerOfTable, headerStepHit, Dfaops.stepHit] using hbClaim
                    obtain ⟨badIdx, hbadLt, hbadNotValid⟩ :=
                      invalid_claim_forces_bad_step t stmt.claim w rows (by omega) hInitRows hLastRows hSatFalse
                    have hbadLtStmt : badIdx < stmt.recordLength := hwLen ▸ hbadLt
                    by_cases hHit : ∃ u : Fin stmt.stepQueries, derivedStepIndex stmt r u.val = badIdx
                    · obtain ⟨u, huIdx⟩ := hHit
                      have huMem : u.val ∈ List.range stmt.stepQueries := List.mem_range.mpr u.isLt
                      have huCheck := hsteps u.val huMem
                      have huSome : ∃ op, r.stepOpenings[u.val]? = some op := by
                        have hltOp : u.val < r.stepOpenings.length := by rw [hstepLen]; exact u.isLt
                        exact ⟨r.stepOpenings[u.val], List.getElem?_eq_getElem hltOp⟩
                      obtain ⟨op, hopEq⟩ := huSome
                      rw [hopEq] at huCheck
                      let qIdx := derivedStepIndex stmt r u.val
                      have hqLtW : qIdx < w.length := by show derivedStepIndex stmt r u.val < w.length; rw [huIdx]; exact hbadLt
                      have hqLtStmt : qIdx < stmt.recordLength := hwLen ▸ hqLtW
                      have hqRows : qIdx < rows.length := by omega
                      unfold checkStepOpening at huCheck
                      simp only [Bool.and_eq_true, decide_eq_true_eq] at huCheck
                      obtain ⟨⟨⟨⟨⟨⟨hopWb, hopSt⟩, hopCont⟩, hopTr⟩, hopDel⟩, _⟩, hopNext⟩ := huCheck
                      have hsaltedLen : (saltedEntries w salts).length = stmt.recordLength := by
                        simp [saltedEntries, hsLen, hwLen]
                      have hrowBadWb : (rows.getD qIdx defaultRow).WellBounded := by
                        apply hrowsWb
                        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqRows]
                      have hopCont' : verifyDenseLeaf (depthOf stmt.recordLength)
                          (denseRoot (saltedEntries w salts)) qIdx
                          (leafOfNat (saltedLeafNat op.row.byte op.salt)) op.contentPath = true := by
                        simpa [saltedContentCommit, ← hcRoot, packSaltedLeaf] using hopCont
                      rcases verifyDenseLeaf_eq_or_pathCollision_at (depthOf stmt.recordLength)
                          (saltedEntries w salts) (by rw [hsaltedLen]) qIdx (by omega)
                          (by rw [saltedEntries_getD_eq w salts (by omega) qIdx hqLtW]; exact saltedLeafNat_lt _ _)
                          (saltedLeafNat op.row.byte op.salt) (saltedLeafNat_lt _ _)
                          op.contentPath hopCont' with hContEq | ⟨hiC, hContCol⟩
                      · have hByteEq : op.row.byte = w.getD qIdx 0 := by
                          rw [saltedEntries_getD_eq w salts (by omega) qIdx hqLtW] at hContEq
                          exact (saltedLeafNat_injective hContEq).1
                        have hopTr' : verifyDenseLeaf (depthOf stmt.recordLength)
                            (denseRoot (traceEntries rows)) qIdx
                            (leafOfNat (packTraceRowNat op.row)) op.tracePath = true := by
                          simpa [traceCommit, ← hrowsRoot, packTraceRow] using hopTr
                        rcases verifyDenseLeaf_eq_or_pathCollision_at (depthOf stmt.recordLength)
                            (traceEntries rows) (by rw [htrLen]) qIdx (by omega)
                            (by rw [traceEntries_getD_eq rows qIdx hqRows]; exact packTraceRowNat_lt _ hrowBadWb)
                            (packTraceRowNat op.row) (packTraceRowNat_lt _ hopWb)
                            op.tracePath hopTr' with hTrEq | ⟨hiT, hTrCol⟩
                        · have hOpRowEq : op.row = rows.getD qIdx defaultRow := by
                            apply packTraceRow_injective hopWb hrowBadWb
                            unfold packTraceRow
                            rw [hTrEq, traceEntries_getD_eq rows qIdx hqRows]
                          have hdeltaLen : t.delta.length = t.states * 256 := htWf.2.2.2.1
                          have hdIdxLt : 256 * op.row.state + op.row.byte.toNat < t.delta.length := by
                            have hstLt : op.row.state < t.states := by simpa [hhdrEq, headerOfTable] using hopSt.1
                            have hbLt := op.row.byte.toNat_lt
                            omega
                          have hopDel' : verifyDenseLeaf (depthOf (t.states * 256)) (denseRoot t.delta)
                              (256 * op.row.state + op.row.byte.toNat) (leafOfNat op.row.next) op.deltaPath = true := by
                            simpa [hhdrEq, headerOfTable, deltaCommit] using hopDel
                          have hnxLt256 : op.row.next < 2 ^ 256 := by
                            have hnxLt : op.row.next < t.states := by simpa [hhdrEq, headerOfTable] using hopSt.2
                            exact lt_of_lt_of_le hnxLt (le_trans htWf.1 (by norm_num))
                          have hdelEntLt : t.delta.getD (256 * op.row.state + op.row.byte.toNat) 0 < 2 ^ 256 := by
                            have hmem : t.delta[256 * op.row.state + op.row.byte.toNat] ∈ t.delta :=
                              List.getElem_mem hdIdxLt
                            simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hdIdxLt] using
                              delta_lt t htWf _ hmem
                          rcases verifyDenseLeaf_eq_or_pathCollision_at (depthOf (t.states * 256))
                              t.delta (by rw [hdeltaLen])
                              (256 * op.row.state + op.row.byte.toNat) hdIdxLt hdelEntLt
                              op.row.next hnxLt256 op.deltaPath hopDel' with hDelEq | ⟨hiD, hDelCol⟩
                          · by_cases hNextIn : qIdx + 1 < stmt.recordLength
                            · have hNextIn' : derivedStepIndex stmt r u.val + 1 < stmt.recordLength := hNextIn
                              rw [ite_eq_left hNextIn'] at hopNext
                              simp only [Bool.and_eq_true, decide_eq_true_eq] at hopNext
                              obtain ⟨⟨hopNextWb, hopNextTr⟩, hopChain⟩ := hopNext
                              have hnextRows : qIdx + 1 < rows.length := by omega
                              have hrowNextWb : (rows.getD (qIdx + 1) defaultRow).WellBounded := by
                                apply hrowsWb
                                simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnextRows]
                              have hopNextTr' : verifyDenseLeaf (depthOf stmt.recordLength)
                                  (denseRoot (traceEntries rows)) (qIdx + 1)
                                  (leafOfNat (packTraceRowNat op.nextRow)) op.nextTracePath = true := by
                                simpa [traceCommit, ← hrowsRoot, packTraceRow] using hopNextTr
                              rcases verifyDenseLeaf_eq_or_pathCollision_at (depthOf stmt.recordLength)
                                  (traceEntries rows) (by rw [htrLen]) (qIdx + 1) (by omega)
                                  (by rw [traceEntries_getD_eq rows _ hnextRows]; exact packTraceRowNat_lt _ hrowNextWb)
                                  (packTraceRowNat op.nextRow) (packTraceRowNat_lt _ hopNextWb)
                                  op.nextTracePath hopNextTr' with hNextTrEq | ⟨hiN, hNextTrCol⟩
                              · have hOpNextEq : op.nextRow = rows.getD (qIdx + 1) defaultRow := by
                                  apply packTraceRow_injective hopNextWb hrowNextWb
                                  unfold packTraceRow
                                  rw [hNextTrEq, traceEntries_getD_eq rows _ hnextRows]
                                exfalso
                                apply hbadNotValid
                                have hValQ : StepValidAt t w rows qIdx := by
                                  refine ⟨by rw [← hOpRowEq]; exact hByteEq,
                                          by rw [← hOpRowEq]; exact hDelEq,
                                          fun _ => ?_⟩
                                  rw [← hOpNextEq, ← hOpRowEq]
                                  simpa [hhdrEq, headerOfTable, headerStepHit, Dfaops.stepHit] using hopChain
                                change StepValidAt t w rows (derivedStepIndex stmt r u.val) at hValQ
                                rwa [huIdx] at hValQ
                              · right; right; right; right; right; right; right; right; right
                                exact ⟨u, op, hopEq, Or.inr (Or.inr (Or.inr ⟨hiN, hNextIn, hNextTrCol⟩))⟩
                            · exfalso
                              apply hbadNotValid
                              have hValQ : StepValidAt t w rows qIdx :=
                                ⟨by rw [← hOpRowEq]; exact hByteEq,
                                 by rw [← hOpRowEq]; exact hDelEq,
                                 fun hltNext => absurd (hwLen ▸ hltNext) hNextIn⟩
                              change StepValidAt t w rows (derivedStepIndex stmt r u.val) at hValQ
                              rwa [huIdx] at hValQ
                          · right; right; right; right; right; right; right; right; right
                            exact ⟨u, op, hopEq, Or.inr (Or.inr (Or.inl ⟨hiD, hDelCol⟩))⟩
                        · right; right; right; right; right; right; right; right; right
                          exact ⟨u, op, hopEq, Or.inr (Or.inl ⟨hiT, hTrCol⟩)⟩
                      · right; right; right; right; right; right; right; right; right
                        exact ⟨u, op, hopEq, Or.inl ⟨hiC, hContCol⟩⟩
                    · right; left
                      push Not at hHit
                      exact ⟨badIdx, hbadLtStmt, hbadNotValid, fun u hu => hHit ⟨u, hu⟩⟩
                · right; right; right; right; right; right; right; right; left
                  exact ⟨hld, hLastCol⟩
              · right; right; right; right; right; right; right; left
                exact ⟨h0d, hFirstCol⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hlf, hWeldLCol⟩))))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h0f, hWeld0Col⟩)))))
      · right; right; left
        exact ⟨hhdrIn, by rw [← automatonHeaderCommit, hhdrRoot, ← htRoot]; rfl⟩
    · simp at accepted
  · simp at accepted

/-! ### Premise Inhabitation & Quantitative Soundness Bound -/

/-- **Non-vacuity / Premise Inhabitation (`checkPrivate_premises_inhabited`)**:
for any well-formed non-empty `DfaTable`, any non-empty word `w` with `w.length ≤ 2^31`, any salts,
and any FRI transcript `T`, there exist concrete `stmt`, `rows`, and root-consistent receipt fields
simultaneously inhabiting `CommitsPrivate`, `rows.length = stmt.recordLength`, `WellBounded`,
`traceCommit rows = traceRoot`, and `Consistent` (via `consistent_of_roots`). -/
theorem checkPrivate_premises_inhabited {ell m fq : Nat} (hm : m ≤ ell) (hell : ell ≤ 256)
    (t : DfaTable) (ht : t.WellFormed) (htPos : 0 < t.states)
    (w : List UInt8) (hwNe : w ≠ []) (hwBound : w.length ≤ 2 ^ 31)
    (salts : List Salt248) (hsLen : salts.length = w.length)
    (T : RawTranscript (rawPcs ell)) (chals : Fin m → C8)
    (seeds : Fin fq → PowerTwoFriLevels ell 1)
    (ops : (j : Fin m) → Fin fq → CPairOpening) :
    let stmt : PrivateContentCert :=
      { contentRoot := saltedContentCommit w salts
        recordLength := w.length
        automatonRoot := automatonCommit t
        claim := .accept (t.accepts w)
        friEll := ell
        friRounds := m
        friQueries := fq
        stepQueries := 1 }
    let rows : List TraceRow := w.map fun b => ⟨b, 0, 0, 0, default⟩
    let chalsF : Fin m → Tower256 := fun j => toField (chals j)
    let root0 := T.rootAt chalsF 0 (Nat.zero_le m)
    let sFri := friStatementOf stmt root0 hm hell
    let crecp : CReceipt ell m fq :=
      { roots := fun n => T.rootAt chalsF n (Nat.le_of_lt_succ n.isLt)
        challenges := chals
        querySeed := seeds
        opening := ops
        finalCoeffs := [] }
    CommitsPrivate stmt t w salts ∧
    rows.length = stmt.recordLength ∧
    (∀ row ∈ rows, row.WellBounded) ∧
    Consistent sFri.denote (crecp.denote sFri) T := by
  have _ := htPos
  have _ := hwNe
  have _ := hwBound
  intro stmt rows chalsF root0 sFri crecp
  refine ⟨⟨ht, rfl, rfl, hsLen, rfl⟩, by simp [rows, stmt], ?_, ?_⟩
  · intro row hrow
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hrow
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  · intro n hn
    rfl

/-- **Exact Query-Miss Soundness Law (`step_sampling_miss_prob_eq`)**:
over `q` independent uniform step draws `draws : Fin q → Fin L` (`0 < L`), the probability of
missing a faulty step `badIdx : Fin L` equals `((L - 1 : ℝ) / L) ^ q`. -/
theorem step_sampling_miss_prob_eq (L q : Nat) (hL : 0 < L) (badIdx : Fin L) :
    have : Nonempty (Fin L) := ⟨badIdx⟩
    BindingGame.prob (fun draws : Fin q → Fin L => ∀ u : Fin q, draws u ≠ badIdx) =
      (((L : ℝ) - 1) / (L : ℝ)) ^ q := by
  have : Nonempty (Fin L) := ⟨badIdx⟩
  rw [BindingGame.prob_eq_mean]
  unfold BindingGame.mean
  have hcard_all : Fintype.card (Fin q → Fin L) = L ^ q := by simp
  have hsum : (∑ draws : Fin q → Fin L, if (∀ u : Fin q, draws u ≠ badIdx) then (1 : ℝ) else 0) =
      ((L - 1 : Nat) : ℝ) ^ q := by
    let S : Finset (Fin L) := Finset.univ.erase badIdx
    have hScard : S.card = L - 1 := by simp [S, Finset.card_erase_of_mem]
    have hpow : (Fintype.piFinset fun _ : Fin q => S).card = (L - 1) ^ q := by
      simp [Fintype.card_piFinset, hScard]
    have hfilter : (Finset.univ.filter fun draws : Fin q → Fin L => ∀ u : Fin q, draws u ≠ badIdx) =
        Fintype.piFinset fun _ : Fin q => S := by
      ext draws
      simp [S, Fintype.mem_piFinset]
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul, mul_one, hpow]
    norm_cast
  rw [hsum, hcard_all, Nat.cast_pow]
  have hLcast : ((L - 1 : Nat) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub hL]
    simp
  rw [hLcast, div_pow]

/-! ## §6. Fast Array-Backed Honest Private Prover (`provePrivate`), DFAs & Kernel Teeth -/

local instance : Inhabited Digest := ⟨⟨0⟩⟩

/-- Build the canonical execution trace rows for `(t, w, rowMasks)` using `Array` lookup on `t.delta`. -/
def buildTraceRows (t : DfaTable) (w : List UInt8) (rowMasks : List RowMask) : List TraceRow :=
  let deltaArr := t.delta.toArray
  let accArr := t.accepting.toArray
  let stepFast (s : Nat) (b : UInt8) : Nat := deltaArr.getD (256 * s + b.toNat) 0
  let hitFast (nx : Nat) : Nat := if accArr.getD nx false then 1 else 0
  let rec go (s c : Nat) : List UInt8 → List RowMask → List TraceRow
    | [], _ => []
    | b :: bs, m :: ms =>
        let nx := stepFast s b
        ⟨b, s, nx, c, m⟩ :: go nx (c + hitFast nx) bs ms
    | b :: bs, [] =>
        let nx := stepFast s b
        ⟨b, s, nx, c, default⟩ :: go nx (c + hitFast nx) bs []
  go t.initial 0 w rowMasks

/-- Precomputed strided cube-Merkle tree over `2 ^ depth` leaves: computes `2^(depth+1) - 1` hashes
once and answers `root` in `O(1)` and `path` in `O(depth)` array reads (`0` extra hashes). -/
structure FastCubeTree where
  depth : Nat
  levels : Array (Array Digest)

def buildFastCubeTree (depth : Nat) (leaves : Array C8) : FastCubeTree := Id.run do
  let size := 2 ^ depth
  let leafDigests := Array.ofFn fun i : Fin size =>
    merkleDomainsC.hashLeaf codecC (leaves.getD i.val (Coordinate.zero 8))
  let mut revLevels : Array (Array Digest) := #[leafDigests]
  let mut cur := leafDigests
  for k in [0:depth] do
    let lvl := depth - 1 - k
    let stride := 2 ^ lvl
    let prev := cur
    cur := Array.ofFn fun off : Fin stride =>
      merkleDomainsC.hashNode prev[off.val]! prev[off.val + stride]!
    revLevels := revLevels.push cur
  ⟨depth, revLevels.reverse⟩

def buildFastDenseTree (entries : List Nat) : FastCubeTree :=
  let d := depthOf entries.length
  buildFastCubeTree d (entries.toArray.map leafOfNat)

def FastCubeTree.root (tree : FastCubeTree) : Digest :=
  (tree.levels[0]!)[0]!

def FastCubeTree.path (tree : FastCubeTree) (idx : Nat) : List Digest := Id.run do
  let mut out : Array Digest := #[]
  let mut offset := 0
  for lvl in [0:tree.depth] do
    let stride := 2 ^ lvl
    let child := tree.levels[lvl + 1]!
    if (idx / stride) % 2 == 0 then
      out := out.push child[offset + stride]!
    else
      out := out.push child[offset]!
      offset := offset + stride
  return out.toList

/-- Precomputed automaton commitment bundle `(automatonRoot, header, deltaTree)` reusable across runs. -/
structure PreparedAutomaton where
  automatonRoot : Digest
  header        : AutomatonHeader
  deltaTree     : FastCubeTree

def prepareAutomaton (t : DfaTable) : PreparedAutomaton :=
  let dTree := buildFastDenseTree t.delta
  let hdr : AutomatonHeader :=
    { states := t.states
      initial := t.initial
      accepting := t.accepting
      deltaRoot := dTree.root }
  { automatonRoot := automatonHeaderCommit hdr
    header := hdr
    deltaTree := dTree }

/-- **Executable honest prover (`provePrivatePrepared`)** using a precomputed `PreparedAutomaton`
and `FastCubeTree` layers (`O(N)` hashes, `O(depth)` path extraction). -/
def provePrivatePrepared (pa : PreparedAutomaton) (t : DfaTable) (w : List UInt8)
    (salts : List Salt248) (rowMasks : List RowMask) (claim : ClaimData)
    (friEll friRounds friQueries stepQueries : Nat) :
    Option (PrivateContentCert × PrivateReceipt friEll friRounds friQueries) := do
  if hm : friRounds ≤ friEll then
    if hell24 : friEll ≤ 24 then
      let hell : friEll ≤ 256 := le_trans hell24 (by norm_num)
      let td := Nat.max 1 (depthOf w.length)
      if w.isEmpty || w.length > 2 ^ 32 || !(td < friEll) ||
          salts.length != w.length || rowMasks.length != w.length then
        none
      else
        let rows := buildTraceRows t w rowMasks
        let rowsArr := rows.toArray
        let saltsArr := salts.toArray
        let cTree := buildFastDenseTree (saltedEntries w salts)
        let tTree := buildFastDenseTree (traceEntries rows)
        let cRoot := cTree.root
        let trRoot := tTree.root
        let domainBase := 2 ^ td
        let pts : Array (C8 × C8) := (List.range domainBase).toArray.map fun idx =>
          let x := domC (unitBasis friEll) (Coordinate.zero 8) 0
            ((additiveFriLevelEquivPowerTwo friEll 0).symm
              ⟨idx % 2 ^ friEll, Nat.mod_lt _ (by positivity)⟩)
          let y := if h : idx < rowsArr.size then blindTraceEval rowsArr[idx] else Coordinate.zero 8
          (x, y)
        let poly ← Tower256SuccinctProver.interpolate pts
        let stmt0 : PrivateContentCert :=
          { contentRoot := cRoot
            recordLength := w.length
            automatonRoot := pa.automatonRoot
            claim := claim
            friEll := friEll
            friRounds := friRounds
            friQueries := friQueries
            stepQueries := stepQueries }
        let pins := privateFriPins stmt0 trRoot
        let degList := (List.range (friRounds + 1)).map (privateDegreeSchedule w.length)
        let friRun ← Tower256SuccinctProver.prove friEll friRounds friQueries hm hell
          (Coordinate.zero 8) degList pins poly none
        let w0Tree := buildFastCubeTree friEll friRun.words[0]!
        let friRoot0 := friRun.receipt.roots 0
        let lastIdx := w.length - 1
        let firstRow := rowsArr.getD 0 defaultRow
        let firstSalt := saltsArr.getD 0 default
        let lastRow := rowsArr.getD lastIdx defaultRow
        let lastSalt := saltsArr.getD lastIdx default
        let bnd : BoundaryOpenings :=
          { firstRow := firstRow
            firstTracePath := tTree.path 0
            firstSalt := firstSalt
            firstContentPath := cTree.path 0
            firstDeltaPath := pa.deltaTree.path (256 * firstRow.state + firstRow.byte.toNat)
            firstFriPath := w0Tree.path 0
            lastRow := lastRow
            lastTracePath := tTree.path lastIdx
            lastSalt := lastSalt
            lastContentPath := cTree.path lastIdx
            lastDeltaPath := pa.deltaTree.path (256 * lastRow.state + lastRow.byte.toNat)
            lastFriPath := w0Tree.path lastIdx }
        let rStub : PrivateReceipt friEll friRounds friQueries :=
          { header := pa.header
            traceRoot := trRoot
            friInitialRoot := friRoot0
            friReceipt := friRun.receipt
            boundary := bnd
            stepOpenings := [] }
        let stepOps : List StepOpening := (List.range stepQueries).map fun u =>
          let idx := derivedStepIndex stmt0 rStub u
          let row := rowsArr.getD idx defaultRow
          let s := saltsArr.getD idx default
          let hasNext := decide (idx + 1 < w.length)
          let nxRow := if hasNext then rowsArr.getD (idx + 1) defaultRow else defaultRow
          { salt := s
            contentPath := cTree.path idx
            row := row
            tracePath := tTree.path idx
            deltaPath := pa.deltaTree.path (256 * row.state + row.byte.toNat)
            friPath := w0Tree.path idx
            nextRow := nxRow
            nextTracePath := if hasNext then tTree.path (idx + 1) else [] }
        some (stmt0, { rStub with stepOpenings := stepOps })
    else none
  else none

/-- **Executable honest prover (`provePrivate`)**. -/
def provePrivate (t : DfaTable) (w : List UInt8) (salts : List Salt248) (rowMasks : List RowMask)
    (claim : ClaimData) (friEll friRounds friQueries stepQueries : Nat) :
    Option (PrivateContentCert × PrivateReceipt friEll friRounds friQueries) :=
  provePrivatePrepared (prepareAutomaton t) t w salts rowMasks claim friEll friRounds friQueries stepQueries

/-! ### Concrete Policy DFAs (`noSkDash` & `countTodo`) & Kernel-Checked Teeth (`by decide`) -/

/-- **4-state padded-complement DFA `noSkDash` (`neg(any* · "sk-" · any*)`)**:
states `0` (clean), `1` (saw `'s'`=115), `2` (saw `"sk"`, `'k'`=107), `3` (dead: saw `"sk-"`, `'-'`=45). -/
def noSkDash : DfaTable where
  states := 4
  initial := 0
  accepting := [true, true, true, false]
  delta := (List.range (4 * 256)).map fun key =>
    let s := key / 256
    let b := key % 256
    if s = 3 then 3
    else if s = 2 ∧ b = 45 then 3
    else if s = 1 ∧ b = 107 then 2
    else if b = 115 then 1
    else 0

/-- **5-state non-overlapping `"TODO"` counter DFA (`countTodo`)**:
`T`=84, `O`=79, `D`=68, `O`=79. State `4` is the sole accepting state and transitions like state `0`. -/
def countTodo : DfaTable where
  states := 5
  initial := 0
  accepting := [false, false, false, false, true]
  delta := (List.range (5 * 256)).map fun key =>
    let s0 := key / 256
    let s := if s0 = 4 then 0 else s0
    let b := key % 256
    if s = 3 ∧ b = 79 then 4
    else if s = 2 ∧ b = 68 then 3
    else if s = 1 ∧ b = 79 then 2
    else if b = 84 then 1
    else 0

/-- **3-state non-overlapping `"ab"` counter DFA (`countAB`)**:
`'a'`=97, `'b'`=98. State `2` is the sole accepting state and transitions like state `0`. -/
def countAB : DfaTable where
  states := 3
  initial := 0
  accepting := [false, false, true]
  delta := (List.range (3 * 256)).map fun key =>
    let s0 := key / 256
    let s := if s0 = 2 then 0 else s0
    let b := key % 256
    if s = 1 ∧ b = 98 then 2
    else if b = 97 then 1
    else 0

theorem noSkDash_wellFormed : noSkDash.WellFormed := by
  unfold DfaTable.WellFormed noSkDash
  refine ⟨by norm_num, by norm_num, rfl, by simp, ?_⟩
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  split_ifs <;> norm_num

theorem countTodo_wellFormed : countTodo.WellFormed := by
  unfold DfaTable.WellFormed countTodo
  refine ⟨by norm_num, by norm_num, rfl, by simp, ?_⟩
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  dsimp only
  split_ifs <;> norm_num

theorem countAB_wellFormed : countAB.WellFormed := by
  unfold DfaTable.WellFormed countAB
  refine ⟨by norm_num, by norm_num, rfl, by simp, ?_⟩
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨k, -, rfl⟩ := hx
  dsimp only
  split_ifs <;> norm_num

theorem step_noSkDash (s : Nat) (hs : s < 4) (b : UInt8) :
    noSkDash.step s b =
      if s = 3 then 3
      else if s = 2 ∧ b.toNat = 45 then 3
      else if s = 1 ∧ b.toNat = 107 then 2
      else if b.toNat = 115 then 1
      else 0 := by
  have hb := b.toNat_lt
  have hkey : 256 * s + b.toNat < 4 * 256 := by omega
  have hdiv : (256 * s + b.toNat) / 256 = s := by omega
  have hmod : (256 * s + b.toNat) % 256 = b.toNat := by omega
  simp [DfaTable.step, noSkDash, List.getD_eq_getElem?_getD, hkey, hdiv, hmod]

theorem step_countAB (s : Nat) (hs : s < 3) (b : UInt8) :
    countAB.step s b =
      let s' := if s = 2 then 0 else s
      if s' = 1 ∧ b.toNat = 98 then 2
      else if b.toNat = 97 then 1
      else 0 := by
  have hb := b.toNat_lt
  have hkey : 256 * s + b.toNat < 3 * 256 := by omega
  have hdiv : (256 * s + b.toNat) / 256 = s := by omega
  have hmod : (256 * s + b.toNat) % 256 = b.toNat := by omega
  simp [DfaTable.step, countAB, List.getD_eq_getElem?_getD, hkey, hdiv, hmod]

/-- Closed-form witness & falsifier across all three `ClaimData` modes (`.accept`, `.count`, `.bound`)
on `noSkDash` and `countAB`. -/
theorem claimModes_kernel_teeth :
    Dfaops.satisfiesClaim noSkDash (.accept true) [111, 107] = true ∧
    Dfaops.satisfiesClaim noSkDash (.accept true) [115, 107, 45] = false ∧
    Dfaops.satisfiesClaim noSkDash (.accept false) [115, 107, 45] = true ∧
    Dfaops.satisfiesClaim countAB (.count 2) [97, 98, 97, 98] = true ∧
    Dfaops.satisfiesClaim countAB (.count 3) [97, 98, 97, 98] = false ∧
    Dfaops.satisfiesClaim countAB (.bound 1 3) [97, 98, 97, 98] = true ∧
    Dfaops.satisfiesClaim countAB (.bound 3 5) [97, 98, 97, 98] = false ∧
    Dfaops.satisfiesClaim countAB (.bound 2 1) [97, 98, 97, 98] = false := by
  have hOk : (Dfaops.runStateCountFrom noSkDash noSkDash.initial 0 [111, 107]).1 = 0 := by
    change (Dfaops.runStateCountFrom noSkDash 0 0 [111, 107]).1 = 0
    simp only [Dfaops.runStateCountFrom, Dfaops.stepHit]
    rw [step_noSkDash 0 (by norm_num)]; norm_num
    rw [step_noSkDash 0 (by norm_num)]; norm_num
  have hSk : (Dfaops.runStateCountFrom noSkDash noSkDash.initial 0 [115, 107, 45]).1 = 3 := by
    change (Dfaops.runStateCountFrom noSkDash 0 0 [115, 107, 45]).1 = 3
    simp only [Dfaops.runStateCountFrom, Dfaops.stepHit]
    rw [step_noSkDash 0 (by norm_num)]; norm_num
    rw [step_noSkDash 1 (by norm_num)]; norm_num
    rw [step_noSkDash 2 (by norm_num)]; norm_num
  have hHit1 : Dfaops.stepHit countAB 1 = 0 := by decide
  have hHit2 : Dfaops.stepHit countAB 2 = 1 := by decide
  have hAb : Dfaops.runCount countAB [97, 98, 97, 98] = 2 := by
    change (Dfaops.runStateCountFrom countAB 0 0 [97, 98, 97, 98]).2 = 2
    simp only [Dfaops.runStateCountFrom]
    rw [step_countAB 0 (by norm_num)]; norm_num; rw [hHit1]
    rw [step_countAB 1 (by norm_num)]; norm_num; rw [hHit2]
    rw [step_countAB 2 (by norm_num)]; norm_num; rw [hHit1]
    rw [step_countAB 1 (by norm_num)]; norm_num; rw [hHit2]
  have hOkRun : noSkDash.run [111, 107] = 0 := by
    rw [← Dfaops.runStateCountFrom_fst_initial]; exact hOk
  have hSkRun : noSkDash.run [115, 107, 45] = 3 := by
    rw [← Dfaops.runStateCountFrom_fst_initial]; exact hSk
  have hAcc0 : noSkDash.accepting.getD 0 false = true := by decide
  have hAcc3 : noSkDash.accepting.getD 3 false = false := by decide
  simp only [Dfaops.satisfiesClaim, Dfaops.claimDecide, DfaTable.accepts,
    hOkRun, hSkRun, hAb, hAcc0, hAcc3]
  decide

/-- Kernel-decided round-trip & disequality teeth on `packSaltedLeaf` and `packTraceRow`. -/
theorem leafPacking_kernel_teeth :
    let s₁ : Salt248 := ⟨0x1122334455667788, by decide⟩
    let s₂ : Salt248 := ⟨0x99aabbccddeeff00, by decide⟩
    let r : TraceRow := ⟨115, 2, 3, 17, ⟨0xdeadbeefcafebabe, by decide⟩⟩
    unpackByte (packSaltedLeaf 115 s₁) == 115 &&
    unpackSalt (packSaltedLeaf 115 s₁) == s₁ &&
    (packSaltedLeaf 115 s₁ != packSaltedLeaf 115 s₂) &&
    (packSaltedLeaf 115 s₁ != packSaltedLeaf 116 s₁) &&
    unpackTraceRow (packTraceRow r) == r := by
  decide

/-! ## §7. Axiom Pins (`#guard_msgs` + `#print axioms`) -/

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.recompute_eq_or_pathCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recompute_eq_or_pathCollision

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.saltedRoot_eq_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms saltedRoot_eq_or_collision

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.unopened_salted_leaf_oracle_hiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unopened_salted_leaf_oracle_hiding

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.unopened_salted_leaf_rom_prob_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unopened_salted_leaf_rom_prob_eq

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.unopened_keyed_salt_prob_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unopened_keyed_salt_prob_eq

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.maskedCubeRootPreimageEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskedCubeRootPreimageEquiv

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.maskedCubeRoot_prob_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms maskedCubeRoot_prob_eq

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.Dfaops.runCount_eq_traceFrom_countP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Dfaops.runCount_eq_traceFrom_countP

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.allStepsValid_implies_satisfiesClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms allStepsValid_implies_satisfiesClaim

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.checkPrivate_sound_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkPrivate_sound_or_collision

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.checkPrivate_premises_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkPrivate_premises_inhabited

/-- info: 'Minidregg.Compiler.Tower256PrivateContentCert.step_sampling_miss_prob_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_sampling_miss_prob_eq

end Minidregg.Compiler.Tower256PrivateContentCert
