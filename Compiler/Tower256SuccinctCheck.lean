/-
# Compiler.Tower256SuccinctCheck -- succinct additive-FRI acceptance as a `Bool`

`Tower256AdditiveFriSuccinctController.SuccinctAccepts` is a proposition over `Tower256`, whose
carrier has no executable representation. This file states the same verifier over
`Coordinate 8` data and proves the two agree at the concrete deployment PCS:

    check_iff : check s pins r = true ↔ SuccinctAccepts (rawPcs ell) s.denote pins r.denote

Field side. Every tower quantity the verifier reads is recomputed from the basis coordinates:
the quotient map after `r` folds iterates `foldMap p x = x² + p·x` with the per-round pivots,
and each pivot is that map applied to the reversed basis element (`toField_applyPivots`,
`toField_pivotC`). No pivot table or inverse is carried: the fold equation is checked in the
multiplied-out form `(next + left)·pivot = (x + α)·(left + right)`, which is equivalent to the
division form because the pivot is nonzero for an independent basis (`fold_iff`).

Byte side. Transcript bytes use `encodeC` (`basisPrefix_eq`, `challengeInput_eq`,
`queryPrefix_eq`); openings and the last root use the coordinate Merkle layer of
`Tower256CoordinateMerkle` (`verifyOpen_iff`, `lastRoot_eq`).
-/

import Compiler.Tower256AdditiveFriSuccinctController
import Compiler.Tower256AdditiveFriRawDeployment
import Compiler.Tower256CoordinateMerkle

namespace Minidregg.Compiler.Tower256SuccinctCheck

open Polynomial
open Minidregg.Theory
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Compiler.Tower256AdditiveFriSuccinctController
open Minidregg.Compiler.Tower256AdditiveFriRawDeployment (rawPcs bootstrapPins)
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256CoordinateMerkle
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8 toField evalCoeffs toField_evalCoeffs)
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate coordinateFieldEquiv
  coordinateFieldEquiv_add coordinateFieldEquiv_mul coordinateFieldEquiv_zero)
open Minidregg.Selvage
open Minidregg.Theory.BinaryCubeAddress (binaryAddressBits binaryCubeIndexEquiv)
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

variable {ell m queryCount : Nat}

/-! ## Coordinate arithmetic -/

def addC (a b : C8) : C8 := Coordinate.add 8 a b
def mulC (a b : C8) : C8 := Coordinate.mul 8 a b

@[simp] theorem toField_addC (a b : C8) : toField (addC a b) = toField a + toField b :=
  coordinateFieldEquiv_add 8 a b
@[simp] theorem toField_mulC (a b : C8) : toField (mulC a b) = toField a * toField b :=
  coordinateFieldEquiv_mul 8 a b
@[simp] theorem toField_zeroC : toField (Coordinate.zero 8) = 0 := coordinateFieldEquiv_zero 8

/-! ## The tower over coordinates -/

section Tower

variable (beta : Fin ell → C8) (offset : C8)

/-- The basis as a `Nat`-indexed family, zero past `ell`. -/
def betaN (n : Nat) : C8 := if h : n < ell then beta ⟨n, h⟩ else Coordinate.zero 8

/-- Its denotation: the `beta` field of the denoted tower. -/
noncomputable def betaF (n : Nat) : Tower256 := if h : n < ell then toField (beta ⟨n, h⟩) else 0

theorem toField_betaN (n : Nat) : toField (betaN beta n) = betaF beta n := by
  unfold betaN betaF
  split <;> simp

/-- One additive fold `y ↦ y² + p·y`. -/
def foldStep (p y : C8) : C8 := addC (mulC y y) (mulC p y)

def applyPivots (ps : List C8) (x : C8) : C8 := ps.foldl (fun y p => foldStep p y) x

theorem applyPivots_append_single (ps : List C8) (p x : C8) :
    applyPivots (ps ++ [p]) x = foldStep p (applyPivots ps x) := by
  simp [applyPivots, List.foldl_append]

/-- The first `r` pivots: pivot `i` is the quotient map after `i` folds at the reversed basis
element `beta (ell - 1 - i)`. -/
def pivots : Nat → List C8
  | 0 => []
  | r + 1 =>
      let ps := pivots r
      ps ++ [applyPivots ps (betaN beta (ell - 1 - r))]

theorem pivots_succ (r : Nat) :
    pivots beta (r + 1) = pivots beta r ++ [applyPivots (pivots beta r) (betaN beta (ell - 1 - r))] :=
  rfl

/-- **The quotient map over coordinates.** -/
theorem toField_applyPivots : ∀ (r : Nat) (x : C8),
    toField (applyPivots (pivots beta r) x) = additiveTowerMap ell (betaF beta) r (toField x)
  | 0, x => by simp [pivots, applyPivots]
  | r + 1, x => by
      rw [additiveTowerMap_succ, pivots_succ, applyPivots_append_single]
      simp only [foldStep, toField_addC, toField_mulC, toField_applyPivots r, toField_betaN]
      simp only [foldMap, additiveTowerPivot, additiveReverseBasis]
      ring

/-- The round-`r` pivot over coordinates. -/
def pivotC (r : Nat) : C8 := applyPivots (pivots beta r) (betaN beta (ell - 1 - r))

theorem toField_pivotC (r : Nat) :
    toField (pivotC beta r) = additiveTowerPivot ell (betaF beta) r := by
  unfold pivotC additiveTowerPivot additiveReverseBasis
  rw [toField_applyPivots, toField_betaN]

theorem zmod2_smul (a : ZMod 2) (x : Tower256) : a • x = if a = 1 then x else 0 := by
  fin_cases a
  · show (0 : ZMod 2) • x = if (0 : ZMod 2) = 1 then x else 0
    rw [ite_eq_right (by decide), zero_smul]
  · show (1 : ZMod 2) • x = if (1 : ZMod 2) = 1 then x else 0
    rw [ite_eq_left rfl, one_smul]

/-- The unquotiented affine point `offset + ∑ cᵢ·βᵢ`. -/
def rawC : (k : Nat) → (Fin k → ZMod 2) → C8
  | 0, _ => offset
  | k + 1, c =>
      addC (rawC k (Fin.init c)) (if c (Fin.last k) = 1 then betaN beta k else Coordinate.zero 8)

theorem toField_rawC : ∀ (k : Nat) (c : Fin k → ZMod 2),
    toField (rawC beta offset k c) = additiveTowerRawPoint (betaF beta) (toField offset) k c
  | 0, c => by simp [rawC, additiveTowerRawPoint, domainPoint]
  | k + 1, c => by
      have ih := toField_rawC k (Fin.init c)
      have hlast : toField (if c (Fin.last k) = 1 then betaN beta k else Coordinate.zero 8) =
          c (Fin.last k) • betaF beta k := by
        rw [zmod2_smul]
        split <;> simp [toField_betaN]
      show toField (addC _ _) = _
      rw [toField_addC, ih, hlast]
      simp only [additiveTowerRawPoint, domainPoint, Fin.sum_univ_castSucc, add_assoc,
        Fin.val_castSucc, Fin.val_last]
      rfl

/-- The level-`j` domain point of `c`. -/
def domC (j : Nat) (c : Fin (ell - j) → ZMod 2) : C8 :=
  applyPivots (pivots beta j) (rawC beta offset (ell - j) c)

end Tower

/-! ## Statement and receipt over coordinates -/

/-- The public statement, as coordinate data. The basis independence is a proof field: it is
what makes every pivot nonzero, so the multiplied-out fold check is faithful. -/
structure CStatement (ell m : Nat) where
  beta : Fin ell → C8
  offset : C8
  degree : Nat → Nat
  queryCount : Nat
  initialRoot : Digest
  independent : LinearIndependent (ZMod 2) (fun j : Fin ell => betaF beta j)
  rounds_le : m ≤ ell

structure CReceipt (ell m queryCount : Nat) where
  roots : Fin (m + 1) → Digest
  challenges : Fin m → C8
  querySeed : Fin queryCount → PowerTwoFriLevels ell 1
  opening : (j : Fin m) → Fin queryCount → FriQueryOpening C8 (List UInt8) (List UInt8)
  finalCoeffs : List C8

namespace CStatement

variable (s : CStatement ell m)

noncomputable def tower : AdditiveFriTower Tower256 ell m where
  beta := betaF s.beta
  offset := toField s.offset
  independent := s.independent
  rounds_le := s.rounds_le

noncomputable def denote : SuccinctStatement ell m where
  tower := s.tower
  degree := s.degree
  queryCount := s.queryCount
  initialRoot := s.initialRoot

theorem toField_domC (j : Nat) (hj : j ≤ ell) (c : AdditiveFriLevels ell j) :
    toField (domC s.beta s.offset j c) = s.tower.dom j c := by
  rw [AdditiveFriTower.dom, dite_eq_left hj]
  show _ = additiveTowerPoint ell (betaF s.beta) (toField s.offset) j (ell - j) c
  unfold domC additiveTowerPoint
  rw [toField_applyPivots, toField_rawC]

end CStatement

noncomputable def openingDenote (o : FriQueryOpening C8 (List UInt8) (List UInt8)) :
    FriQueryOpening Tower256 (List UInt8) (List UInt8) where
  left := toField o.left
  right := toField o.right
  next := toField o.next
  leftPath := o.leftPath
  rightPath := o.rightPath
  nextPath := o.nextPath

noncomputable def CReceipt.denote (r : CReceipt ell m queryCount) :
    SuccinctReceipt ell m queryCount where
  roots := r.roots
  challenges := fun j => toField (r.challenges j)
  querySeed := r.querySeed
  opening := fun j a => openingDenote (r.opening j a)
  finalCoeffs := r.finalCoeffs

/-! ## Transcript bytes -/

def basisPrefixC (ell m : Nat) (beta : Fin ell → C8) (offset : C8) : List UInt8 :=
  envelope (encodeLength ell) ++
    envelope (encodeLength m) ++
      envelope (encodeC offset) ++
        (List.ofFn fun index : Fin ell =>
          envelope (envelope (encodeLength index) ++ envelope (encodeC (beta index)))).flatten

theorem basisPrefix_eq (beta : Fin ell → C8) (offset : C8) :
    basisPrefix ell m (betaF beta) (toField offset) = basisPrefixC ell m beta offset := by
  unfold basisPrefix basisPrefixC basisFrame
  have h1 : transcriptValueCodec.encode (toField offset) = encodeC offset := encode_toField offset
  have h2 : ∀ index : Fin ell,
      transcriptValueCodec.encode (betaF beta index) = encodeC (beta index) := by
    intro index
    rw [betaF, dite_eq_left index.isLt]
    exact encode_toField _
  simp only [h1, h2]

def challengeInputC (s : CStatement ell m) (pins : TranscriptPins)
    (r : CReceipt ell m queryCount) (j : Fin m) : List UInt8 :=
  envelope pins.statementBytes ++
    envelope (basisPrefixC ell m s.beta s.offset) ++
    (List.ofFn fun n : Fin ((j : Nat) + 1) =>
      have hn : (n : Nat) <= m := by omega
      envelope (encodeLength n) ++
        envelope (cshakeC.digestCodec.encode (r.roots ⟨n, Nat.lt_succ_of_le hn⟩))).flatten

theorem challengeInput_eq (s : CStatement ell m) (pins : TranscriptPins)
    (r : CReceipt ell m queryCount) (j : Fin m) :
    Tower256AdditiveFriSuccinctController.challengeInput (rawPcs ell) s.denote pins r.denote j = challengeInputC s pins r j := by
  unfold Tower256AdditiveFriSuccinctController.challengeInput challengeInputC
  rw [← basisPrefix_eq]
  rfl

def challengeC (s : CStatement ell m) (pins : TranscriptPins)
    (r : CReceipt ell m queryCount) (j : Fin m) : C8 :=
  digestTowerC (cshakeC.xofDigest pins.challengeCustomization (challengeInputC s pins r j))

theorem toField_challengeC (s : CStatement ell m) (pins : TranscriptPins)
    (r : CReceipt ell m queryCount) (j : Fin m) :
    toField (challengeC s pins r j) = Tower256AdditiveFriSuccinctController.derivedChallenge (rawPcs ell) s.denote pins r.denote j := by
  rw [challengeC, toField_digestTowerC, Tower256AdditiveFriSuccinctController.derivedChallenge, challengeInput_eq]
  rfl

def queryPrefixC (s : CStatement ell m) (pins : TranscriptPins)
    (r : CReceipt ell m queryCount) : List UInt8 :=
  envelope pins.statementBytes ++
    envelope (basisPrefixC ell m s.beta s.offset) ++
    (List.ofFn fun n : Fin (m + 1) =>
      have hn : (n : Nat) <= m := by omega
      envelope (encodeLength n) ++ envelope
        (cshakeC.digestCodec.encode (r.roots ⟨n, Nat.lt_succ_of_le hn⟩))).flatten ++
    (List.ofFn r.challenges).flatMap fun challenge => envelope (encodeC challenge)

theorem flatMap_map_toField (l : List C8) :
    (l.map toField).flatMap
        (fun c => envelope (BinaryTower256Profile.profile.valueCodec.encode c)) =
      l.flatMap fun c => envelope (encodeC c) := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      simp only [List.map_cons, List.flatMap_cons, ih]
      rw [encode_toField_codec]
      rfl

theorem queryPrefix_eq (s : CStatement ell m) (pins : TranscriptPins)
    (r : CReceipt ell m queryCount) :
    Tower256AdditiveFriSuccinctController.queryPrefix (rawPcs ell) s.denote pins r.denote = queryPrefixC s pins r := by
  unfold Tower256AdditiveFriSuccinctController.queryPrefix queryPrefixC
  rw [← basisPrefix_eq, ← flatMap_map_toField, List.map_ofFn]
  rfl

def seedC (s : CStatement ell m) (pins : TranscriptPins)
    (r : CReceipt ell m queryCount) (a : Fin queryCount) : PowerTwoFriLevels ell 1 :=
  let digest := cshakeC.xofDigest pins.queryCustomization
    (queryPrefixC s pins r ++ envelope (encodeLength a))
  ⟨digest.value % (2 ^ (ell - 1)), Nat.mod_lt _ (by positivity)⟩

theorem seedC_eq (s : CStatement ell m) (pins : TranscriptPins)
    (r : CReceipt ell m queryCount) (a : Fin queryCount) :
    seedC s pins r a = Tower256AdditiveFriSuccinctController.derivedQuerySeed (rawPcs ell) s.denote pins r.denote a := by
  have hc : (rawPcs ell).backend.cshake = cshakeC := rfl
  unfold seedC Tower256AdditiveFriSuccinctController.derivedQuerySeed
  simp only [hc, queryPrefix_eq]

/-! ## Openings and the fold equation -/

/-- The concrete level-`n` opening check over coordinates. -/
def verifyOpenC (n : Nat) (root : Digest) (coordinate : AdditiveFriLevels ell n)
    (value : C8) (proof : List UInt8) : Bool :=
  match merkleDomainsC.proofCodec.decode proof with
  | none => false
  | some path =>
      decide (recompute merkleDomainsC (merkleDomainsC.hashLeaf codecC value)
        (binaryAddressBits (ell - n) (additiveFriLevelEquivPowerTwo ell n coordinate)) path =
          some root)

theorem verifyOpen_iff (n : Nat) (root : Digest) (coordinate : AdditiveFriLevels ell n)
    (value : C8) (proof : List UInt8) :
    ((rawPcs ell).opening n).verifyOpen root coordinate (toField value) proof ↔
      verifyOpenC n root coordinate value proof = true := by
  have hleaf : Tower256ConcreteBackend.merkleDomains.hashLeaf
      BinaryTower256Profile.profile.valueCodec (toField value) =
        merkleDomainsC.hashLeaf codecC value := hashLeaf_toField value
  change (merkleCommitmentScheme Tower256ConcreteBackend.merkleDomains
      (((rawPcs ell).level n).port)).verifyOpening root
        (additiveFriLevelEquivPowerTwo ell n coordinate) (toField value) proof = true ↔ _
  unfold merkleCommitmentScheme verifyOpenC
  change (match merkleDomainsC.proofCodec.decode proof with
    | none => false
    | some path =>
        decide (recompute merkleDomainsC (Tower256ConcreteBackend.merkleDomains.hashLeaf
          BinaryTower256Profile.profile.valueCodec (toField value))
          (binaryAddressBits (ell - n) (additiveFriLevelEquivPowerTwo ell n coordinate)) path =
            some root)) = true ↔ _
  rw [hleaf]

/-- `liftBit` over coordinates; it reads the tower only for a dimension proof. -/
def liftBitC (s : CStatement ell m) (j : Fin m) (bit : ZMod 2)
    (c : AdditiveFriLevels ell ((j : Nat) + 1)) : AdditiveFriLevels ell j :=
  fun i => (Fin.snoc c bit : Fin ((ell - ((j : Nat) + 1)) + 1) → ZMod 2)
    (Fin.cast (by have := s.rounds_le; have := j.isLt; omega) i)

theorem liftBitC_eq (s : CStatement ell m) (j : Fin m) (bit : ZMod 2)
    (c : AdditiveFriLevels ell ((j : Nat) + 1)) :
    liftBitC s j bit c = s.tower.liftBit j j.isLt bit c := rfl

/-- The fold equation in multiplied-out form is the division form when the pivot is nonzero. -/
theorem fold_iff (n l r d α p : C8) (hp : toField p ≠ 0) :
    mulC (addC n l) p = mulC (addC d α) (addC l r) ↔
      toField n = toField l + (toField d + toField α) * ((toField l + toField r) / toField p) := by
  rw [← Equiv.apply_eq_iff_eq toField, toField_mulC, toField_mulC, toField_addC, toField_addC,
    toField_addC, mul_div_assoc', ← sub_eq_iff_eq_add', eq_div_iff hp, CharTwo.sub_eq_add]

def openedC (s : CStatement ell m) (r : CReceipt ell m queryCount) (j : Fin m)
    (k : AdditiveFriLevels ell ((j : Nat) + 1))
    (o : FriQueryOpening C8 (List UInt8) (List UInt8)) : Bool :=
  verifyOpenC j (r.roots ⟨j, by omega⟩) (liftBitC s j 0 k) o.left o.leftPath &&
  (verifyOpenC ((j : Nat) + 1) (r.roots ⟨(j : Nat) + 1, by omega⟩) k o.next o.nextPath &&
  (verifyOpenC j (r.roots ⟨j, by omega⟩) (liftBitC s j 1 k) o.right o.rightPath &&
  decide (mulC (addC o.next o.left) (pivotC s.beta j) =
    mulC (addC (domC s.beta s.offset j (liftBitC s j 0 k)) (r.challenges j))
      (addC o.left o.right))))

theorem openedC_iff (s : CStatement ell m) (r : CReceipt ell m queryCount) (j : Fin m)
    (k : AdditiveFriLevels ell ((j : Nat) + 1))
    (o : FriQueryOpening C8 (List UInt8) (List UInt8)) :
    openedC s r j k o = true ↔ OpenedQuery (rawPcs ell) s.denote j r.denote k (openingDenote o) := by
  have hj : (j : Nat) < ell := lt_of_lt_of_le j.isLt s.rounds_le
  have hp : toField (pivotC s.beta j) ≠ 0 := by
    rw [toField_pivotC]
    exact additiveTowerPivot_ne_zero ell (betaF s.beta) (toField s.offset) s.independent j
      (ell - j - 1) (by omega)
  unfold openedC OpenedQuery
  simp only [Bool.and_eq_true, decide_eq_true_eq, ← verifyOpen_iff]
  rw [fold_iff _ _ _ _ _ _ hp, toField_pivotC, s.toField_domC j hj.le]
  rfl

/-! ## The last root -/

/-- The root of the final polynomial's evaluations on the last domain, over coordinates. -/
def lastRootC (beta : Fin ell → C8) (offset : C8) (m : Nat) (coeffs : List C8) : Digest :=
  cubeRoot merkleDomainsC codecC (k := ell - m) fun address =>
    evalCoeffs coeffs (domC beta offset m
      ((additiveFriLevelEquivPowerTwo ell m).symm (binaryCubeIndexEquiv (ell - m) address)))

theorem lastRoot_eq (s : CStatement ell m) (r : CReceipt ell m queryCount) :
    ((rawPcs ell).opening m).commit (r.denote.finalWord s.denote) =
      lastRootC s.beta s.offset m r.finalCoeffs := by
  have hword : ∀ p, r.denote.finalWord s.denote p =
      toField (evalCoeffs r.finalCoeffs (domC s.beta s.offset m p)) := by
    intro p
    rw [toField_evalCoeffs, s.toField_domC m s.rounds_le]
    rfl
  change cubeRoot Tower256ConcreteBackend.merkleDomains BinaryTower256Profile.profile.valueCodec
      (fun address => r.denote.finalWord s.denote
        ((additiveFriLevelEquivPowerTwo ell m).symm (binaryCubeIndexEquiv (ell - m) address))) = _
  simp only [hword]
  exact cubeRoot_toField _

/-! ## The checker -/

/-- **Succinct acceptance, decided.** -/
def check (s : CStatement ell m) (pins : TranscriptPins) (r : CReceipt ell m queryCount) : Bool :=
  decide (queryCount = s.queryCount) &&
  (decide (r.roots 0 = s.initialRoot) &&
  (decide (∀ j, r.challenges j = challengeC s pins r j) &&
  (decide (∀ a, r.querySeed a = seedC s pins r a) &&
  (decide (∀ (j : Fin m) (a : Fin queryCount),
      openedC s r j (additiveCoherentRound s.rounds_le j r.querySeed a) (r.opening j a) = true) &&
  (decide (r.finalCoeffs.length ≤ s.degree m) &&
   decide (r.roots (Fin.last m) = lastRootC s.beta s.offset m r.finalCoeffs))))))

theorem check_iff (s : CStatement ell m) (pins : TranscriptPins) (r : CReceipt ell m queryCount) :
    check s pins r = true ↔ SuccinctAccepts (rawPcs ell) s.denote pins r.denote := by
  have hch : (∀ j, r.challenges j = challengeC s pins r j) ↔
      ∀ j, r.denote.challenges j = Tower256AdditiveFriSuccinctController.derivedChallenge (rawPcs ell) s.denote pins r.denote j :=
    forall_congr' fun j => by
      rw [← toField_challengeC]
      exact (Equiv.apply_eq_iff_eq toField).symm
  have hseed : (∀ a, r.querySeed a = seedC s pins r a) ↔
      ∀ a, r.denote.querySeed a = Tower256AdditiveFriSuccinctController.derivedQuerySeed (rawPcs ell) s.denote pins r.denote a :=
    forall_congr' fun a => by rw [seedC_eq]; rfl
  have hop : (∀ (j : Fin m) (a : Fin queryCount),
      openedC s r j (additiveCoherentRound s.rounds_le j r.querySeed a) (r.opening j a) = true) ↔
      ∀ (j : Fin m) (a : Fin queryCount), OpenedQuery (rawPcs ell) s.denote j r.denote
        (additiveCoherentRound s.rounds_le j r.querySeed a) (openingDenote (r.opening j a)) :=
    forall_congr' fun j => forall_congr' fun a => openedC_iff s r j _ _
  have hlast : r.roots (Fin.last m) = lastRootC s.beta s.offset m r.finalCoeffs ↔
      r.denote.roots (Fin.last m) = ((rawPcs ell).opening m).commit (r.denote.finalWord s.denote) := by
    rw [lastRoot_eq]; rfl
  unfold check SuccinctAccepts
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hch, hseed, hop, hlast]
  exact Iff.rfl

/-! ## Teeth -/

/-- The bootstrap shape: `ell = 1`, no folds, no queries, basis `[1]`, one final coefficient. -/
def bootBeta : Fin 1 → C8 := fun _ => Coordinate.one 8

theorem bootIndependent : LinearIndependent (ZMod 2) (fun j : Fin 1 => betaF bootBeta j) := by
  rw [linearIndependent_unique_iff]
  show betaF bootBeta 0 ≠ 0
  rw [betaF, dite_eq_left (by norm_num)]
  show coordinateFieldEquiv 8 (Coordinate.one 8) ≠ 0
  rw [Minidregg.Theory.BinaryTowerFanPaarCodec.coordinateFieldEquiv_one]
  exact one_ne_zero

def bootCoeffs : List C8 := [Coordinate.one 8]

def bootStatement : CStatement 1 0 where
  beta := bootBeta
  offset := Coordinate.zero 8
  degree := fun _ => 1
  queryCount := 0
  initialRoot := lastRootC bootBeta (Coordinate.zero 8) 0 bootCoeffs
  independent := bootIndependent
  rounds_le := Nat.zero_le 1

def bootReceipt (coeffs : List C8) : CReceipt 1 0 0 where
  roots := fun _ => lastRootC bootBeta (Coordinate.zero 8) 0 bootCoeffs
  challenges := fun j => j.elim0
  querySeed := fun a => a.elim0
  opening := fun j => j.elim0
  finalCoeffs := coeffs

-- The honest bootstrap receipt is accepted (compiled, through the native cSHAKE).
#guard check bootStatement bootstrapPins (bootReceipt bootCoeffs)
-- A different final polynomial under the same roots is rejected by the last-root clause.
#guard !check bootStatement bootstrapPins (bootReceipt [Coordinate.zero 8])
-- A final polynomial over the degree bound is rejected.
#guard !check bootStatement bootstrapPins (bootReceipt [Coordinate.one 8, Coordinate.zero 8])

/-- info: 'Minidregg.Compiler.Tower256SuccinctCheck.check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms check_iff

end Minidregg.Compiler.Tower256SuccinctCheck
