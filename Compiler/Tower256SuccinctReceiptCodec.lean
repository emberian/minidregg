/-
# Compiler.Tower256SuccinctReceiptCodec -- the wire format of a succinct additive-FRI receipt

A `StreamCodec` for `Tower256SuccinctCheck.CReceipt`, assembled from `Theory/StreamCodec`
combinators, and its `LawfulCodec` by `toLawful`. Every function-typed field travels as a
length-prefixed list whose decoder refuses any other length (`finFun`), so the wire is
list-shaped while `check` and `check_iff` keep the function-shaped receipt unchanged:

* roots: `m + 1` digests (`digestStream`);
* challenges: `m` coordinates (`c8Stream`, the 32-byte little-endian integer of the coordinate);
* query seeds: `queryCount` values of `Fin (2^(ell-1))`;
* openings: `m × queryCount` pair openings: the pair's two coordinates and the Merkle siblings
  above the pair (shared by both leaves; each leaf's last sibling is the other leaf's hash). No
  next-level leaf travels: it is round `j+1`'s pair leaf, or the final polynomial's
  (`CReceipt.nextOf`);
* final coefficients: a list of coordinates.

`decode_encode` and canonicity (`toLawful_canonical`: a decoded receipt re-encodes to the very
bytes) come from the combinators. The teeth run the codec on the accepting one-fold receipt of
`Tower256SuccinctHonestRun`.
-/

import Compiler.Tower256SuccinctCheck

namespace Minidregg.Compiler.Tower256SuccinctReceiptCodec

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend (StreamCodec fixedStream digestStream merklePathStream)
open Minidregg.Compiler.Tower256CoordinateMerkle
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8)
open Minidregg.Compiler.Tower256SuccinctCheck
open Minidregg.Compiler.Tower256AdditiveFriRawDeployment (bootstrapPins)
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate coordinateFinEquiv capacity)
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Vectors as length-checked lists -/

/-- `Fin n → α` on the wire: the list `List.ofFn f`, whose decoder refuses every other length. -/
def finFun {α : Type} (n : Nat) (codec : StreamCodec α) : StreamCodec (Fin n → α) :=
  StreamCodec.xmap (StreamCodec.refine (StreamCodec.list codec) (fun l => l.length = n))
    (fun f => ⟨List.ofFn f, List.length_ofFn⟩)
    (fun l i => l.1.get (i.cast l.2.symm))
    (by intro f; funext i; simp)
    (by
      intro l
      apply Subtype.ext
      apply List.ext_get (by simp [l.2])
      intro k h1 h2
      simp)

/-! ## Coordinates -/

theorem capacity_eight_bytes : capacity 8 = 256 ^ 32 := by simp [capacity]

theorem ofNat_toNat (c : C8) : Coord.ofNat 8 (Coord.toNat 8 c) = c := by
  apply (coordinateFinEquiv 8).injective
  apply Fin.ext
  rw [Coord.coordinateFinEquiv_val, Coord.coordinateFinEquiv_val,
    Coord.toNat_ofNat 8 _ (Coord.toNat_lt 8 c)]

/-- A coordinate as the 32-byte little-endian integer `Coord.toNat`. -/
def c8Stream : StreamCodec C8 :=
  StreamCodec.xmap (fixedStream 32)
    (fun c => ⟨Coord.toNat 8 c, by
      have h := Coord.toNat_lt 8 c
      rw [capacity_eight_bytes] at h
      exact h⟩)
    (fun v => Coord.ofNat 8 v.val)
    (fun c => ofNat_toNat c)
    (by
      intro v
      apply Fin.ext
      exact Coord.toNat_ofNat 8 v.val (by rw [capacity_eight_bytes]; exact v.isLt))

/-! ## Openings and the receipt -/

/-- A pair opening: two coordinates and the shared path above the leaf pair, as a
`merklePathStream` digest list. -/
def openingStream : StreamCodec CPairOpening :=
  StreamCodec.xmap
    (StreamCodec.product c8Stream (StreamCodec.product c8Stream merklePathStream))
    (fun o => (o.left, o.right, o.pairPath))
    (fun w => ⟨w.1, w.2.1, w.2.2⟩)
    (by intro o; rfl)
    (by intro w; rfl)

variable {ell m queryCount : Nat}

def receiptStream (ell m queryCount : Nat) : StreamCodec (CReceipt ell m queryCount) :=
  StreamCodec.xmap
    (StreamCodec.product (finFun (m + 1) digestStream)
      (StreamCodec.product (finFun m c8Stream)
        (StreamCodec.product (finFun queryCount (StreamCodec.fin (2 ^ (ell - 1))))
          (StreamCodec.product (finFun m (finFun queryCount openingStream))
            (StreamCodec.list c8Stream)))))
    (fun r => (r.roots, r.challenges, r.querySeed, r.opening, r.finalCoeffs))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2⟩)
    (by intro r; rfl)
    (by intro w; rfl)

/-- **The receipt codec.** -/
def receiptCodec (ell m queryCount : Nat) : LawfulCodec (CReceipt ell m queryCount) :=
  (receiptStream ell m queryCount).toLawful

theorem receipt_decode_encode (r : CReceipt ell m queryCount) :
    (receiptCodec ell m queryCount).decode ((receiptCodec ell m queryCount).encode r) = some r :=
  (receiptCodec ell m queryCount).decode_encode r

/-- Canonical: anything that decodes is the encoding of what it decodes to. -/
theorem receipt_canonical (bytes : List UInt8) (r : CReceipt ell m queryCount)
    (decoded : (receiptCodec ell m queryCount).decode bytes = some r) :
    (receiptCodec ell m queryCount).encode r = bytes :=
  StreamCodec.toLawful_canonical _ bytes r decoded

/-- Decode, then decide. -/
def checkBytes (s : CStatement ell m) (pins : Tower256AdditiveFriController.TranscriptPins)
    (bytes : List UInt8) : Bool :=
  match (receiptCodec ell m queryCount).decode bytes with
  | none => false
  | some r => check s pins r

theorem checkBytes_iff (s : CStatement ell m) (pins : Tower256AdditiveFriController.TranscriptPins)
    (bytes : List UInt8) :
    checkBytes (queryCount := queryCount) s pins bytes = true ↔
      ∃ r, (receiptCodec ell m queryCount).decode bytes = some r ∧
        Tower256AdditiveFriSuccinctController.SuccinctAccepts
          (Tower256AdditiveFriRawDeployment.rawPcs ell) s.denote pins (r.denote s) := by
  unfold checkBytes
  cases h : (receiptCodec ell m queryCount).decode bytes with
  | none => simp
  | some r => simp [check_iff]

/-! ## Teeth

On the bootstrap receipt here (cheap); on the accepting ell = 2 receipt (round trip, refusals,
the 375-byte pin and the per-part sizes) compiled, in `lake exe tower256-prover-run`
(`Tower256SuccinctProverRun.shapeTwo`). -/

#guard
  let bytes := (receiptCodec 1 0 0).encode (bootReceipt bootCoeffs)
  ((receiptCodec 1 0 0).decode bytes).map (receiptCodec 1 0 0).encode == some bytes &&
  checkBytes (queryCount := 0) bootStatement bootstrapPins bytes &&
  !checkBytes (queryCount := 0) bootStatement bootstrapPins (bytes ++ [0]) &&
  !checkBytes (queryCount := 0) bootStatement bootstrapPins bytes.dropLast

/-- info: 'Minidregg.Compiler.Tower256SuccinctReceiptCodec.checkBytes_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkBytes_iff

end Minidregg.Compiler.Tower256SuccinctReceiptCodec
