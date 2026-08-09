/-
# `Compiler.NextgenLightClientPublicInputs` — canonical next-generation join inputs

This file models the first-order public-input schema emitted by
`prover/src/nextgen_light_client.rs`. It deliberately stops at the generated-artifact
boundary: Rust has no semantics to refine; the handwritten encoder must be replaced by an
emitted artifact/API, and the succinct verifier
must be shown to bind the descriptor's public prefix.  No Rust semantics, binary-append
soundness, hash collision resistance, or recursive composition is claimed here.

The codec is injective for structural reasons made executable below: every `u64` has four
little-endian radix-2^16 cells, byte strings carry a `u64` byte length and use two bytes per
cell (with a zero high byte in the odd tail), tower values carry their level, bases carry
their element count, and the complete body carries its cell count.
-/
import Compiler.EmitSerialize
import Theory.Bignum

namespace Minidregg.Compiler.NextgenLightClientPublicInputs

open Minidregg.Compiler
open Minidregg.Theory

set_option autoImplicit false

abbrev Byte := Fin 256
abbrev U64 := Fin (2 ^ 64)

/-- A byte vector whose length can be represented by the runtime's `u64` framing. -/
structure Bytes where
  data : List Byte
  length_lt : data.length < 2 ^ 64
deriving DecidableEq

/-- A fixed-size byte vector (used for 48-byte roots and channel identifiers). -/
abbrev FixedBytes (n : Nat) := { data : List Byte // data.length = n }
abbrev FixedCells (n : Nat) := { data : List Nat // data.length = n }
abbrev Root48 := FixedBytes 48
abbrev Channel48 := FixedBytes 48

/-- The serialized part of a tower element. Canonical-bit masking is a generated-code
obligation of `TowerElem::new`; the public schema itself serializes exactly level plus u64. -/
structure TowerElem where
  level : Fin 7
  bits : U64
  canonical : bits.val < 2 ^ (2 ^ level.val)
deriving DecidableEq

structure Claim where
  root : Root48
  coefficientBound : U64
  channelId : Channel48
  target : TowerElem
deriving DecidableEq

/-- A list whose length is encodable by the runtime's `push_len`. -/
structure BoundedList (α : Type) where
  data : List α
  length_lt : data.length < 2 ^ 64
deriving DecidableEq

structure EvaluationStatement where
  claim : Claim
  basis : BoundedList TowerElem
  offset : TowerElem
  evaluationPoint : TowerElem
  numQueries : U64
deriving DecidableEq

/-- The binary append statement (left/right evaluations) and its derived output claim. -/
structure Join where
  left : EvaluationStatement
  right : EvaluationStatement
  output : Claim
  bodyLength_lt : 335 + 5 * (left.basis.data.length + right.basis.data.length) < 2 ^ 64
deriving DecidableEq

def u16Base : Nat := 2 ^ 16

theorem u16Base_eq : u16Base = 65536 := by norm_num [u16Base]

def encodeU64 (x : U64) : List Nat := Bignum.digitsLE u16Base 4 x.val

@[simp] theorem encodeU64_length (x : U64) : (encodeU64 x).length = 4 := by
  simp [encodeU64]

theorem encodeU64_ranged (x : U64) : Bignum.Ranged u16Base (encodeU64 x) := by
  exact Bignum.digitsLE_ranged (by norm_num [u16Base]) 4 x.val

theorem encodeU64_denote (x : U64) : Bignum.denoteNat u16Base (encodeU64 x) = x.val := by
  apply Bignum.denoteNat_digitsLE (by norm_num [u16Base])
  simp [u16Base]

/-- Pack byte pairs little-endian.  A final odd byte is represented by its low byte alone,
so its implicit high byte is definitionally zero. -/
def packBytes : List Byte → List Nat
  | [] => []
  | [a] => [a.val]
  | a :: b :: rest => (a.val + 256 * b.val) :: packBytes rest

@[simp] theorem packBytes_length : ∀ xs : List Byte,
    (packBytes xs).length = (xs.length + 1) / 2 := by
  intro xs
  induction xs using List.twoStepInduction with
  | nil => simp [packBytes]
  | singleton a => simp [packBytes]
  | cons_cons a b xs ih => simp [packBytes, ih]; omega

theorem packBytes_lt : ∀ xs : List Byte, ∀ cell ∈ packBytes xs, cell < u16Base := by
  intro xs
  induction xs using List.twoStepInduction with
  | nil => simp [packBytes]
  | singleton a =>
      intro cell h
      simp only [packBytes, List.mem_singleton] at h
      subst cell
      norm_num [u16Base]
      exact a.isLt.trans (by omega)
  | cons_cons a b xs ih =>
      intro cell h
      simp only [packBytes, List.mem_cons] at h
      rcases h with rfl | h
      · norm_num [u16Base]
        omega
      · exact ih cell h

def encodeBytes (xs : Bytes) : List Nat :=
  encodeU64 ⟨xs.data.length, xs.length_lt⟩ ++ packBytes xs.data

def fixedAsBytes {n : Nat} (h : n < 2 ^ 64) (xs : FixedBytes n) : Bytes :=
  ⟨xs.1, by simpa [xs.2] using h⟩

def encodeFixed48 (xs : FixedBytes 48) : List Nat :=
  encodeBytes (fixedAsBytes (by norm_num) xs)

def encodeTower (x : TowerElem) : List Nat := x.level.val :: encodeU64 x.bits

@[simp] theorem encodeTower_length (x : TowerElem) : (encodeTower x).length = 5 := by
  simp [encodeTower]

def encodeClaim (x : Claim) : List Nat :=
  [5] ++ encodeFixed48 x.root ++ encodeU64 x.coefficientBound ++
    encodeFixed48 x.channelId ++ encodeTower x.target

def encodeBasis (xs : BoundedList TowerElem) : List Nat :=
  encodeU64 ⟨xs.data.length, xs.length_lt⟩ ++ xs.data.flatMap encodeTower

@[simp] theorem encodeBasis_length (xs : BoundedList TowerElem) :
    (encodeBasis xs).length = 4 + 5 * xs.data.length := by
  simp [encodeBasis, List.length_flatMap]
  omega

def encodeEvaluation (sectionId : Nat) (x : EvaluationStatement) : List Nat :=
  [sectionId] ++ encodeClaim x.claim ++ [6] ++ encodeBasis x.basis ++ [7] ++
    encodeTower x.offset ++ [8] ++ encodeTower x.evaluationPoint ++ [9] ++
    encodeU64 x.numQueries

/- These are the exact `push_bytes` outputs for the four runtime schema tags, including
their four-cell u64 byte lengths. Keeping them first-order makes the generated-code
obligation byte-for-byte explicit and avoids importing a text encoding into the AIR layer. -/
def encodingTag : List Nat :=
  [47, 0, 0, 0, 26989, 26990, 29284, 26469, 12135, 25966, 29816, 25959,
   11630, 26988, 26727, 11636, 27747, 25961, 29806, 28719, 25205, 26988,
   11619, 28265, 30064, 29556, 30255, 49]

def binarySuiteTag : List Nat :=
  [16, 0, 0, 0, 26946, 24942, 31090, 26707, 27489, 12901, 13877, 12630]

def binaryProtocolTag : List Nat :=
  [45, 0, 0, 0, 26989, 26990, 29284, 26469, 12135, 26978, 24942, 31090,
   25901, 24950, 30060, 29793, 28521, 11630, 26984, 29811, 29295, 11641,
   28769, 25968, 25710, 30255, 49]

def towerSuiteTag : List Nat :=
  [35, 0, 0, 0, 24902, 20590, 24929, 17010, 28265, 29281, 21625, 30575,
   29285, 18223, 12870, 13918, 12084, 25964, 25974, 13932, 30255, 49]

def encodeBody (x : Join) : List Nat :=
  [1] ++ encodingTag ++ binarySuiteTag ++ binaryProtocolTag ++ towerSuiteTag ++
    encodeEvaluation 2 x.left ++ encodeEvaluation 3 x.right ++ [4] ++ encodeClaim x.output

@[simp] theorem encodeFixed48_length (xs : FixedBytes 48) :
    (encodeFixed48 xs).length = 28 := by
  simp [encodeFixed48, encodeBytes, fixedAsBytes, xs.2]

@[simp] theorem encodeClaim_length (x : Claim) : (encodeClaim x).length = 66 := by
  simp [encodeClaim, encodeTower]

@[simp] theorem encodeEvaluation_length (sectionId : Nat) (x : EvaluationStatement) :
    (encodeEvaluation sectionId x).length = 89 + 5 * x.basis.data.length := by
  simp [encodeEvaluation]
  omega

@[simp] theorem encodeBody_length (x : Join) :
    (encodeBody x).length =
      335 + 5 * (x.left.basis.data.length + x.right.basis.data.length) := by
  simp [encodeBody, encodingTag, binarySuiteTag, binaryProtocolTag, towerSuiteTag]
  omega

/-- The exact version-one public-input vector. -/
def encode (x : Join) : List Nat :=
  [1] ++ encodeU64 ⟨(encodeBody x).length, by
    simpa using x.bodyLength_lt⟩ ++ encodeBody x

/-! ## A consuming decoder -/

abbrev Parser (α : Type) := List Nat → Option (α × List Nat)

def expectCell (wanted : Nat) : Parser Unit
  | got :: rest => if got = wanted then some ((), rest) else none
  | [] => none

def expectPrefix : List Nat → Parser Unit
  | [], input => some ((), input)
  | wanted :: ws, got :: rest =>
      if got = wanted then expectPrefix ws rest else none
  | _ :: _, [] => none

@[simp] theorem expectCell_cons (wanted : Nat) (rest : List Nat) :
    expectCell wanted (wanted :: rest) = some ((), rest) := by simp [expectCell]

@[simp] theorem expectPrefix_append (tag rest : List Nat) :
    expectPrefix tag (tag ++ rest) = some ((), rest) := by
  induction tag with
  | nil => simp [expectPrefix]
  | cons a tail ih => simp [expectPrefix, ih]

def parseU64 : Parser U64
  | a :: b :: c :: d :: rest =>
      if h : Bignum.Ranged u16Base [a, b, c, d] then
        some (⟨Bignum.denoteNat u16Base [a, b, c, d], by
          have := Bignum.denoteNat_lt_pow (by norm_num [u16Base]) [a, b, c, d] h
          simpa [u16Base] using this⟩, rest)
      else none
  | _ => none

@[simp] theorem parseU64_encode (x : U64) (rest : List Nat) :
    parseU64 (encodeU64 x ++ rest) = some (x, rest) := by
  have hr := encodeU64_ranged x
  have hd := encodeU64_denote x
  unfold encodeU64 at hr hd ⊢
  simp only [Bignum.digitsLE] at hr hd ⊢
  simp only [List.cons_append, List.nil_append, parseU64]
  rw [dif_pos hr]
  congr 2
  apply Fin.ext
  exact hd

/-- Decode exactly `n` bytes.  The `n=1` branch requires `<256`, hence rejects a nonzero
implicit high byte in the last packed cell. -/
def parsePacked : (n : Nat) → Parser (List Byte)
  | 0, input => some ([], input)
  | 1, cell :: rest =>
      if h : cell < 256 then some ([⟨cell, h⟩], rest) else none
  | 1, [] => none
  | n + 2, cell :: rest =>
      if h : cell < 65536 then
        match parsePacked n rest with
        | some (tail, rest') =>
            some (⟨cell % 256, Nat.mod_lt _ (by omega)⟩ ::
              ⟨cell / 256, by omega⟩ :: tail, rest')
        | none => none
      else none
  | _ + 2, [] => none

@[simp] theorem parsePacked_packBytes (xs : List Byte) (rest : List Nat) :
    parsePacked xs.length (packBytes xs ++ rest) = some (xs, rest) := by
  induction xs using List.twoStepInduction with
  | nil => simp [packBytes, parsePacked]
  | singleton a =>
      simp only [packBytes, List.singleton_append, List.length_cons, List.length_nil,
        Nat.zero_add, parsePacked]
      rw [dif_pos a.isLt]
  | cons_cons a b xs ih =>
      simp only [packBytes, List.cons_append, List.length_cons, parsePacked]
      have hcell : a.val + 256 * b.val < 65536 := by omega
      rw [dif_pos hcell]
      simp only [ih]
      have hlo : (a.val + 256 * b.val) % 256 = a.val := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]
      have hhi : (a.val + 256 * b.val) / 256 = b.val := by
        rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt a.isLt, Nat.zero_add]
      apply congrArg (fun data : List Byte => some (data, rest))
      exact congrArg₂ List.cons (Fin.ext hlo)
        (congrArg₂ List.cons (Fin.ext hhi) rfl)

def parseFixed48 : Parser (FixedBytes 48) := fun input =>
  match parseU64 input with
  | some (n, rest) =>
      if n.val = 48 then
        match parsePacked 48 rest with
        | some (xs, rest') =>
            if h : xs.length = 48 then some (⟨xs, h⟩, rest') else none
        | none => none
      else none
  | none => none

@[simp] theorem parseFixed48_encode (xs : FixedBytes 48) (rest : List Nat) :
    parseFixed48 (encodeFixed48 xs ++ rest) = some (xs, rest) := by
  rcases xs with ⟨data, hdata⟩
  unfold parseFixed48 encodeFixed48 encodeBytes
  rw [List.append_assoc, parseU64_encode]
  change (if data.length = 48 then
    match parsePacked 48 (packBytes data ++ rest) with
    | some (ys, rest') =>
        if h : ys.length = 48 then some ((⟨ys, h⟩ : FixedBytes 48), rest') else none
    | none => none
    else none) = some ((⟨data, hdata⟩ : FixedBytes 48), rest)
  rw [if_pos hdata]
  have hparse : parsePacked 48 (packBytes data ++ rest) = some (data, rest) := by
    rw [← hdata]
    exact parsePacked_packBytes data rest
  rw [hparse]
  dsimp only
  rw [dif_pos hdata]

def parseTower : Parser TowerElem
  | level :: rest =>
      if h : level < 7 then
        match parseU64 rest with
        | some (bits, rest') =>
            if hc : bits.val < 2 ^ (2 ^ level) then
              some (⟨⟨level, h⟩, bits, hc⟩, rest')
            else none
        | none => none
      else none
  | [] => none

@[simp] theorem parseTower_encode (x : TowerElem) (rest : List Nat) :
    parseTower (encodeTower x ++ rest) = some (x, rest) := by
  simp [parseTower, encodeTower, x.level.isLt, parseU64_encode, x.canonical]

def parseTowerList : (n : Nat) → Parser { xs : List TowerElem // xs.length = n }
  | 0, input => some (⟨[], rfl⟩, input)
  | n + 1, input =>
      match parseTower input with
      | some (x, rest) =>
          match parseTowerList n rest with
          | some (xs, rest') => some (⟨x :: xs.1, by simp [xs.2]⟩, rest')
          | none => none
      | none => none

@[simp] theorem parseTowerList_encode (xs : List TowerElem) (rest : List Nat) :
    parseTowerList xs.length (xs.flatMap encodeTower ++ rest) =
      some (⟨xs, rfl⟩, rest) := by
  induction xs with
  | nil => simp [parseTowerList]
  | cons x xs ih =>
      simp [parseTowerList, parseTower_encode, ih]

def parseBasis : Parser (BoundedList TowerElem) := fun input =>
  match parseU64 input with
  | some (n, rest) =>
      match parseTowerList n.val rest with
      | some (xs, rest') =>
          some (⟨xs.1, by simp [xs.2]⟩, rest')
      | none => none
  | none => none

@[simp] theorem parseBasis_encode (xs : BoundedList TowerElem) (rest : List Nat) :
    parseBasis (encodeBasis xs ++ rest) = some (xs, rest) := by
  unfold parseBasis encodeBasis
  rw [List.append_assoc, parseU64_encode]
  dsimp only
  have hp := parseTowerList_encode xs.data rest
  rw [hp]

def parseClaim : Parser Claim := fun input =>
  match expectCell 5 input with
  | none => none
  | some (_, r1) =>
      match parseFixed48 r1 with
      | none => none
      | some (root, r2) =>
          match parseU64 r2 with
          | none => none
          | some (bound, r3) =>
              match parseFixed48 r3 with
              | none => none
              | some (channel, r4) =>
                  match parseTower r4 with
                  | none => none
                  | some (target, r5) => some (⟨root, bound, channel, target⟩, r5)

@[simp] theorem parseClaim_encode (x : Claim) (rest : List Nat) :
    parseClaim (encodeClaim x ++ rest) = some (x, rest) := by
  simp [parseClaim, encodeClaim, parseFixed48_encode, parseU64_encode,
    parseTower_encode]

def parseEvaluation (sectionId : Nat) : Parser EvaluationStatement := fun input =>
  match expectCell sectionId input with
  | none => none
  | some (_, r1) =>
      match parseClaim r1 with
      | none => none
      | some (claim, r2) =>
          match expectCell 6 r2 with
          | none => none
          | some (_, r3) =>
              match parseBasis r3 with
              | none => none
              | some (basis, r4) =>
                  match expectCell 7 r4 with
                  | none => none
                  | some (_, r5) =>
                      match parseTower r5 with
                      | none => none
                      | some (offset, r6) =>
                          match expectCell 8 r6 with
                          | none => none
                          | some (_, r7) =>
                              match parseTower r7 with
                              | none => none
                              | some (point, r8) =>
                                  match expectCell 9 r8 with
                                  | none => none
                                  | some (_, r9) =>
                                      match parseU64 r9 with
                                      | none => none
                                      | some (queries, r10) =>
                                          some (⟨claim, basis, offset, point, queries⟩, r10)

@[simp] theorem parseEvaluation_encode (sectionId : Nat) (x : EvaluationStatement)
    (rest : List Nat) :
    parseEvaluation sectionId (encodeEvaluation sectionId x ++ rest) = some (x, rest) := by
  simp [parseEvaluation, encodeEvaluation, parseClaim_encode, parseBasis_encode,
    parseTower_encode, parseU64_encode]

def parseBody : Parser Join := fun input =>
  match expectCell 1 input with
  | none => none
  | some (_, r1) =>
      match expectPrefix encodingTag r1 with
      | none => none
      | some (_, r2) =>
          match expectPrefix binarySuiteTag r2 with
          | none => none
          | some (_, r3) =>
              match expectPrefix binaryProtocolTag r3 with
              | none => none
              | some (_, r4) =>
                  match expectPrefix towerSuiteTag r4 with
                  | none => none
                  | some (_, r5) =>
                      match parseEvaluation 2 r5 with
                      | none => none
                      | some (left, r6) =>
                          match parseEvaluation 3 r6 with
                          | none => none
                          | some (right, r7) =>
                              match expectCell 4 r7 with
                              | none => none
                              | some (_, r8) =>
                                  match parseClaim r8 with
                                  | none => none
                                  | some (output, r9) =>
                                      if h : 335 + 5 *
                                          (left.basis.data.length + right.basis.data.length) <
                                          2 ^ 64 then
                                        some (⟨left, right, output, h⟩, r9)
                                      else none

@[simp] theorem parseBody_encode (x : Join) (rest : List Nat) :
    parseBody (encodeBody x ++ rest) = some (x, rest) := by
  have hbody : 335 + 5 *
      (x.left.basis.data.length + x.right.basis.data.length) < 2 ^ 64 :=
    x.bodyLength_lt
  have hbody' : 335 + 5 *
      (x.left.basis.data.length + x.right.basis.data.length) <
      18446744073709551616 := by simpa using hbody
  simp [parseBody, encodeBody, parseEvaluation_encode, parseClaim_encode, hbody']

/-- Split exactly `n` cells from an input. -/
def takeCells (n : Nat) : Parser (List Nat)
  | input =>
      if _h : n ≤ input.length then
        some (input.take n, input.drop n)
      else none

@[simp] theorem takeCells_append {n : Nat} (xs : FixedCells n) (rest : List Nat) :
    takeCells n (xs.1 ++ rest) = some (xs.1, rest) := by
  have hlen : n ≤ (xs.1 ++ rest).length := by simp [xs.2]
  simp only [takeCells]
  rw [dif_pos hlen]
  simp [xs.2]

@[simp] theorem takeCells_self (xs : List Nat) :
    takeCells xs.length xs = some (xs, []) := by
  simpa using (takeCells_append (xs := (⟨xs, rfl⟩ : FixedCells xs.length))
    (rest := []))

/-- Decode one complete version-one vector, rejecting trailing cells and a dishonest body
length. -/
def decode (input : List Nat) : Option Join :=
  match expectCell 1 input with
  | none => none
  | some (_, r1) =>
      match parseU64 r1 with
      | none => none
      | some (bodyLen, r2) =>
          match takeCells bodyLen.val r2 with
          | none => none
          | some (body, rest) =>
              if rest.isEmpty then
                match parseBody body with
                | some (x, []) => some x
                | _ => none
              else none

set_option maxHeartbeats 600000 in
theorem decode_encode (x : Join) : decode (encode x) = some x := by
  simp [decode, encode, expectCell, parseU64_encode]
  rw [← encodeBody_length x, takeCells_self]
  have hp := parseBody_encode x []
  simp only [List.append_nil] at hp
  dsimp only
  rw [hp]
  simp

theorem encode_injective : Function.Injective encode := by
  intro x y h
  have := congrArg decode h
  simpa [decode_encode] using this

/-! Small codec teeth. -/

/-- The last cell of an odd byte string really is one byte: a nonzero high byte is rejected. -/
theorem parsePacked_one_rejects_nonzero_high (cell : Nat) (rest : List Nat)
    (h : 256 ≤ cell) : parsePacked 1 (cell :: rest) = none := by
  simp [parsePacked, Nat.not_lt.mpr h]

/-- Version zero cannot alias version one, independently of its tail. -/
theorem decode_rejects_version_zero (tail : List Nat) : decode (0 :: tail) = none := by
  simp [decode, expectCell]

/-! ## Canonical BabyBear cells and exact size -/

/-- Every natural cell has a canonical, non-reducing BabyBear representative. -/
def CellsBelow : List Nat → Prop
  | [] => True
  | cell :: xs => cell < babyBearP ∧ CellsBelow xs

instance (xs : List Nat) : Decidable (CellsBelow xs) := by
  induction xs with
  | nil => exact isTrue trivial
  | cons x xs ih =>
      letI : Decidable (CellsBelow xs) := ih
      change Decidable (_ < babyBearP ∧ CellsBelow xs)
      infer_instance

@[simp] theorem cellsBelow_nil : CellsBelow [] := by trivial

@[simp] theorem cellsBelow_cons (cell : Nat) (xs : List Nat) :
    CellsBelow (cell :: xs) ↔ cell < babyBearP ∧ CellsBelow xs := by
  rfl

@[simp] theorem cellsBelow_append (xs ys : List Nat) :
    CellsBelow (xs ++ ys) ↔ CellsBelow xs ∧ CellsBelow ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, and_assoc]

theorem cellsBelow_iff (xs : List Nat) :
    CellsBelow xs ↔ ∀ cell ∈ xs, cell < babyBearP := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, CellsBelow]

@[simp] theorem cellsBelow_flatMap {α : Type} (f : α → List Nat) (xs : List α) :
    CellsBelow (xs.flatMap f) ↔ ∀ x ∈ xs, CellsBelow (f x) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

@[simp] theorem encodeU64_cellsBelow (x : U64) : CellsBelow (encodeU64 x) := by
  have hr := encodeU64_ranged x
  unfold encodeU64 at hr ⊢
  simp only [Bignum.digitsLE] at hr ⊢
  constructor
  · exact (hr _ (by simp)).trans (by norm_num [u16Base, babyBearP])
  constructor
  · exact (hr _ (by simp)).trans (by norm_num [u16Base, babyBearP])
  constructor
  · exact (hr _ (by simp)).trans (by norm_num [u16Base, babyBearP])
  constructor
  · exact (hr _ (by simp)).trans (by norm_num [u16Base, babyBearP])
  trivial

@[simp] theorem packBytes_cellsBelow (xs : List Byte) : CellsBelow (packBytes xs) := by
  induction xs using List.twoStepInduction with
  | nil => simp [packBytes]
  | singleton a =>
      simp [packBytes, CellsBelow, babyBearP]
      omega
  | cons_cons a b xs ih =>
      simp [packBytes, ih, babyBearP]
      omega

@[simp] theorem encodeFixed48_cellsBelow (xs : FixedBytes 48) :
    CellsBelow (encodeFixed48 xs) := by
  simp [encodeFixed48, encodeBytes]

@[simp] theorem encodeTower_cellsBelow (x : TowerElem) : CellsBelow (encodeTower x) := by
  constructor
  · exact x.level.isLt.trans (by norm_num [babyBearP])
  exact encodeU64_cellsBelow x.bits

@[simp] theorem encodeClaim_cellsBelow (x : Claim) : CellsBelow (encodeClaim x) := by
  simp [encodeClaim, babyBearP]

@[simp] theorem encodeBasis_cellsBelow (xs : BoundedList TowerElem) :
    CellsBelow (encodeBasis xs) := by
  simp [encodeBasis]

@[simp] theorem encodeEvaluation_cellsBelow (sectionId : Nat) (hsection : sectionId < babyBearP)
    (x : EvaluationStatement) : CellsBelow (encodeEvaluation sectionId x) := by
  have hs : sectionId < 2013265921 := by simpa [babyBearP] using hsection
  simp [encodeEvaluation, babyBearP, hs]

theorem encodingTag_cellsBelow : CellsBelow encodingTag := by decide
theorem binarySuiteTag_cellsBelow : CellsBelow binarySuiteTag := by decide
theorem binaryProtocolTag_cellsBelow : CellsBelow binaryProtocolTag := by decide
theorem towerSuiteTag_cellsBelow : CellsBelow towerSuiteTag := by decide

@[simp] theorem encodeBody_cellsBelow (x : Join) : CellsBelow (encodeBody x) := by
  simp [encodeBody, encodingTag_cellsBelow, binarySuiteTag_cellsBelow,
    binaryProtocolTag_cellsBelow, towerSuiteTag_cellsBelow, babyBearP]

/-- **Canonical public inputs.** No encoded cell reduces modulo BabyBear. -/
theorem encode_cell_lt_babyBearP (x : Join) :
    ∀ cell ∈ encode x, cell < babyBearP := by
  have hbelow : CellsBelow (encode x) := by simp [encode, babyBearP]
  exact (cellsBelow_iff (encode x)).mp hbelow

/-- The runtime's exact size equation: 340 fixed cells plus five per basis element. -/
theorem encode_length (x : Join) :
    (encode x).length =
      340 + 5 * (x.left.basis.data.length + x.right.basis.data.length) := by
  simp [encode]
  omega

/-- Cast the canonical natural cells into the deployed prover field. -/
def encodeField (x : Join) : List BabyBear := (encode x).map fun cell => (cell : BabyBear)

@[simp] theorem encodeField_length (x : Join) : (encodeField x).length = (encode x).length := by
  simp [encodeField]

/-! ## The descriptor/public-prefix seam -/

/-- The exact seam established by `require_public_length` plus
`require_public_prefix`: the descriptor declares precisely this many public wires and those
wires equal the canonical encoding of the binary append statement and derived output claim.

`descriptorHolds` is intentionally absent: emitted gate satisfaction does not by itself
choose public values.  The succinct verifier's public-input aggregation must establish this
predicate as a separate generated-code obligation. -/
def PublicPrefixBound (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    (x : Join) : Prop :=
  d.nPublic = (encode x).length ∧
    ∀ (i : Nat), (hi : i < (encode x).length) →
      (wv i).val = (encode x)[i]

/-- A single descriptor/wire prefix cannot bind two different append statements or output
claims.  This is the formal metadata-binding consequence of the codec's injectivity. -/
theorem publicPrefixBound_injective (d : ConstraintDescriptor BabyBear) (wv : Nat → BabyBear)
    {x y : Join} (hx : PublicPrefixBound d wv x) (hy : PublicPrefixBound d wv y) : x = y := by
  apply encode_injective
  have hlen : (encode x).length = (encode y).length := hx.1.symm.trans hy.1
  apply List.ext_getElem hlen
  intro i hix hiy
  exact (hx.2 i hix).symm.trans (hy.2 i hiy)

/-- Machine-state the two remaining runtime obligations without pretending to prove them:
Rust's encoder must return `encode`, and the verifier must establish `PublicPrefixBound` for
the descriptor/wire vector it authenticates. -/
def RuntimeRefinementSeam
    (rustEncode : Join → List Nat)
    (verifierBinds : ConstraintDescriptor BabyBear → (Nat → BabyBear) → Join → Prop) : Prop :=
  (∀ x, rustEncode x = encode x) ∧
  (∀ d wv x, verifierBinds d wv x → PublicPrefixBound d wv x)

end Minidregg.Compiler.NextgenLightClientPublicInputs
