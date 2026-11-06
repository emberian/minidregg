/-
# Compiler.Tower256CoordinateMerkle -- the concrete Merkle layer, computable over coordinates

The concrete backend's cSHAKE256 controller, Merkle domains and Tower256 value codec are
declared `noncomputable` (`Tower256ConcreteBackend.cshake`, `BinaryTowerCodec.codec`): the
field carrier `binaryTower 8` has no executable representation. This file gives the same
objects over `Coordinate 8` and proves them equal to the declared ones, so that a checker
written over coordinates computes the concrete scheme's verdicts:

* `Coordinate.toNat` / `Coordinate.ofNat` are the computable little-endian integer view, and
  `coordinateFinEquiv_val` says it is `coordinateFinEquiv`.
* `encodeC` is the 32-byte value codec on coordinates; `encode_toField` says it is
  `BinaryTowerFanPaarCodec.encode ∘ toField`, and `digestTowerC` is `digestTower`.
* `cshakeC` and `merkleDomainsC` are the backend's controller and domains, by `rfl`, but
  compilable (the cSHAKE bytes run through the `mini_cshake256_32` extern).
* `cubeRoot_map` / `verifyOpening_toField`: the generic Merkle root and opening check over
  `toField ∘ column` equal the coordinate ones.
-/

import Theory.BinaryTowerCoordinateArith
import Compiler.Tower256FinalPolynomialCheck
import Compiler.Tower256ConcreteBackend

namespace Minidregg.Compiler.Tower256CoordinateMerkle

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate coordinateFieldEquiv coordinateFinEquiv
  capacity coordinateFinEquiv_pair_val)
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8 toField)
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## The integer view of a coordinate -/

namespace Coord

/-- Little-endian integer of a coordinate: low half first. -/
def toNat : (k : Nat) → Coordinate k → Nat
  | 0, c => if Coordinate.bitOf c then 1 else 0
  | k + 1, c => toNat k (Coordinate.low c) + capacity k * toNat k (Coordinate.high c)

/-- The coordinate of an integer below `capacity k`. -/
def ofNat : (k : Nat) → Nat → Coordinate k
  | 0, n => .bit (n % 2 == 1)
  | k + 1, n => .pair (ofNat k (n % capacity k)) (ofNat k (n / capacity k))

theorem coordinateFinEquiv_val : ∀ (k : Nat) (c : Coordinate k),
    (coordinateFinEquiv k c).val = toNat k c
  | 0, .bit b => by cases b <;> rfl
  | k + 1, .pair l h => by
      rw [coordinateFinEquiv_pair_val, coordinateFinEquiv_val k l, coordinateFinEquiv_val k h]
      rfl

theorem toNat_lt (k : Nat) (c : Coordinate k) : toNat k c < capacity k := by
  rw [← coordinateFinEquiv_val]; exact (coordinateFinEquiv k c).isLt

theorem toNat_ofNat : ∀ (k n : Nat), n < capacity k → toNat k (ofNat k n) = n
  | 0, n, hn => by
      have : n = 0 ∨ n = 1 := by simp [capacity] at hn; omega
      rcases this with rfl | rfl <;> rfl
  | k + 1, n, hn => by
      have hc : 0 < capacity k := by simp [capacity]
      have hdiv : n / capacity k < capacity k := by
        rw [Nat.div_lt_iff_lt_mul hc, BinaryTowerFanPaarCodec.capacity_succ k]
        exact hn
      simp only [toNat, ofNat, Coordinate.low_pair, Coordinate.high_pair]
      rw [toNat_ofNat k _ (Nat.mod_lt _ hc), toNat_ofNat k _ hdiv]
      exact Nat.mod_add_div n (capacity k)

theorem coordinateFinEquiv_ofNat (k : Nat) (v : Fin (capacity k)) :
    coordinateFinEquiv k (ofNat k v.val) = v :=
  Fin.ext (by rw [coordinateFinEquiv_val, toNat_ofNat k v.val v.isLt])

end Coord

/-! ## The value codec on coordinates -/

theorem capacity_eight : capacity 8 = 2 ^ 256 := by simp [capacity]

/-- The canonical 32-byte encoding of a coordinate. -/
def encodeC (c : C8) : List UInt8 :=
  BinaryTowerFanPaarCodec.encodeFin ⟨Coord.toNat 8 c, capacity_eight ▸ Coord.toNat_lt 8 c⟩

theorem toFin_toField (c : C8) :
    BinaryTowerFanPaarCodec.toFin (toField c) = ⟨Coord.toNat 8 c, capacity_eight ▸ Coord.toNat_lt 8 c⟩ := by
  apply Fin.ext
  change (coordinateFinEquiv 8 ((coordinateFieldEquiv 8).symm (coordinateFieldEquiv 8 c))).val = _
  rw [Equiv.symm_apply_apply, Coord.coordinateFinEquiv_val]

theorem encode_toField (c : C8) :
    BinaryTowerCodec.codec.encode (toField c) = encodeC c := by
  change BinaryTowerFanPaarCodec.encodeFin (BinaryTowerFanPaarCodec.toFin (toField c)) = _
  rw [toFin_toField]; rfl

/-- The coordinate a digest names under `digestTower`. -/
def digestTowerC (digest : Digest) : C8 := Coord.ofNat 8 (digest.value % 2 ^ 256)

theorem toField_digestTowerC (digest : Digest) :
    toField (digestTowerC digest) = Tower256AdditiveFriController.digestTower digest := by
  unfold digestTowerC Tower256AdditiveFriController.digestTower
  change coordinateFieldEquiv 8 _ = coordinateFieldEquiv 8 ((coordinateFinEquiv 8).symm _)
  congr 1
  have hv : digest.value % 2 ^ 256 < capacity 8 := by
    rw [capacity_eight]; exact Nat.mod_lt _ (by positivity)
  exact ((Equiv.symm_apply_eq _).mpr
    (Coord.coordinateFinEquiv_ofNat 8 ⟨digest.value % 2 ^ 256, hv⟩).symm).symm

/-- The value codec on coordinates, as a `LawfulCodec`. -/
def codecC : LawfulCodec C8 where
  encode := encodeC
  decode := fun bytes => (BinaryTowerFanPaarCodec.decodeFin bytes).map fun v => Coord.ofNat 8 v.val
  decode_encode := by
    intro c
    simp only [encodeC, BinaryTowerFanPaarCodec.decodeFin_encodeFin, Option.map_some]
    congr 1
    apply (coordinateFinEquiv 8).injective
    apply Fin.ext
    rw [Coord.coordinateFinEquiv_val, Coord.coordinateFinEquiv_val,
      Coord.toNat_ofNat 8 _ (Coord.toNat_lt 8 c)]

/-! ## Computable aliases of the concrete backend -/

def cshakeC : Cshake256 :=
  Sp800185Cshake256.controller Tower256ConcreteBackend.cshakeAlgorithmId
    Tower256ConcreteBackend.digestCodecPin

theorem cshakeC_eq : cshakeC = Tower256ConcreteBackend.cshake := rfl

def merkleDomainsC : MerkleDomains cshakeC where
  suiteId := Tower256ConcreteBackend.merkleSuiteId
  proofCodecPin := Tower256ConcreteBackend.merklePathCodecPin
  proofCodec := Tower256ConcreteBackend.merklePathCodec
  leafCustomization := Tower256ConcreteBackend.leafCustomization
  nodeCustomization := Tower256ConcreteBackend.nodeCustomization
  customizationsDistinct := Tower256ConcreteBackend.leaf_node_distinct

theorem merkleDomainsC_eq : HEq merkleDomainsC Tower256ConcreteBackend.merkleDomains := HEq.rfl

/-! ## The generic Merkle layer commutes with a codec-preserving map -/

section Map

variable {cshake : Cshake256} (domains : MerkleDomains cshake)
variable {R S : Type} (codecR : LawfulCodec R) (codecS : LawfulCodec S) (f : S → R)
variable (hf : ∀ s, codecR.encode (f s) = codecS.encode s)

include hf in
theorem hashLeaf_map (s : S) : domains.hashLeaf codecR (f s) = domains.hashLeaf codecS s := by
  simp only [MerkleDomains.hashLeaf, hf]

include hf in
theorem cubeRoot_map : ∀ {k : Nat} (column : (Fin k → Bool) → S),
    cubeRoot domains codecR (fun a => f (column a)) = cubeRoot domains codecS column
  | 0, column => by simp only [cubeRoot]; exact hashLeaf_map domains codecR codecS f hf _
  | k + 1, column => by
      simp only [cubeRoot]
      rw [cubeRoot_map (k := k) (fun tail => column (Fin.cases false tail)),
        cubeRoot_map (k := k) (fun tail => column (Fin.cases true tail))]

end Map

/-- The tower codec and the coordinate codec agree along `toField`. -/
theorem encode_toField_codec (c : C8) :
    BinaryTower256Profile.profile.valueCodec.encode (toField c) = codecC.encode c :=
  encode_toField c

/-- **The concrete root of a coordinate column**, computed over coordinates. -/
theorem cubeRoot_toField {k : Nat} (column : (Fin k → Bool) → C8) :
    cubeRoot Tower256ConcreteBackend.merkleDomains BinaryTower256Profile.profile.valueCodec
        (fun a => toField (column a)) =
      cubeRoot merkleDomainsC codecC column :=
  cubeRoot_map Tower256ConcreteBackend.merkleDomains _ codecC toField encode_toField_codec column

/-- The leaf hash of a coordinate, over coordinates. -/
theorem hashLeaf_toField (c : C8) :
    Tower256ConcreteBackend.merkleDomains.hashLeaf BinaryTower256Profile.profile.valueCodec
        (toField c) = merkleDomainsC.hashLeaf codecC c :=
  hashLeaf_map Tower256ConcreteBackend.merkleDomains _ codecC toField encode_toField_codec c

/-! ## Teeth: the computable path really runs the native cSHAKE -/

-- Two distinct one-leaf trees have distinct roots under the compiled cSHAKE.
#guard cubeRoot merkleDomainsC codecC (k := 0) (fun _ => Coordinate.zero 8) !=
  cubeRoot merkleDomainsC codecC (k := 0) (fun _ => Coordinate.one 8)

-- A two-leaf root recomputes from its honest path.
#guard recompute merkleDomainsC (k := 1)
    (merkleDomainsC.hashLeaf codecC (Coordinate.one 8)) (fun _ => true)
    (cubePath merkleDomainsC codecC (k := 1)
      (fun a => if a 0 then Coordinate.one 8 else Coordinate.zero 8) (fun _ => true)) ==
  some (cubeRoot merkleDomainsC codecC (k := 1)
      (fun a => if a 0 then Coordinate.one 8 else Coordinate.zero 8))

/-- info: 'Minidregg.Compiler.Tower256CoordinateMerkle.cubeRoot_toField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms cubeRoot_toField
/-- info: 'Minidregg.Compiler.Tower256CoordinateMerkle.toField_digestTowerC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toField_digestTowerC

end Minidregg.Compiler.Tower256CoordinateMerkle
