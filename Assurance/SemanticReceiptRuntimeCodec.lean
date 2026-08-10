/-
# Assurance.SemanticReceiptRuntimeCodec — exact key-major runtime layout

The executable receipt relation stores one flat vector in the order

  `[pre[0], post[0], touched[0], pre[1], post[1], touched[1], ...]`.

This file proves that layout is an injective reindexing of the formal
`ReceiptWitness.encode` word, and that the two runtime residual lanes are
exactly the formal Boolean-mask and frame constraints.  It is a Lean-owned
codec theorem, not a Rust refinement: no Rust semantics exists. Rust must
consume an emitted artifact/API. The larger heterogeneous envelope/request
codec remains a separate Lean theorem.
-/
import Assurance.SemanticTurnReceipt
import Compiler.NextgenLightClientPublicInputs

namespace Minidregg.Assurance.SemanticReceiptRuntimeCodec

open Minidregg.Assurance.SemanticReceiptRelation

variable {F : Type*} [Field F] [DecidableEq F]

/-- Runtime slot tags in their literal on-wire order. -/
def slotEquivFin : ReceiptSlot ≃ Fin 3 where
  toFun
    | .pre => 0
    | .post => 1
    | .touched => 2
  invFun
    | ⟨0, _⟩ => .pre
    | ⟨1, _⟩ => .post
    | ⟨2, _⟩ => .touched
  left_inv slot := by cases slot <;> rfl
  right_inv index := by fin_cases index <;> rfl

/-- `(key,slot)` becomes the flat key-major index `3*key+slot`. -/
def receiptIxEquivRuntime (n : Nat) : ReceiptIx (Fin n) ≃ Fin (n * 3) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) slotEquivFin).trans finProdFinEquiv

@[simp] theorem receiptIxEquivRuntime_pre_val (n : Nat) (key : Fin n) :
    (receiptIxEquivRuntime n (key, .pre)).val = 3 * key.val := by
  simp [receiptIxEquivRuntime, slotEquivFin, finProdFinEquiv]

@[simp] theorem receiptIxEquivRuntime_post_val (n : Nat) (key : Fin n) :
    (receiptIxEquivRuntime n (key, .post)).val = 3 * key.val + 1 := by
  simp [receiptIxEquivRuntime, slotEquivFin, finProdFinEquiv]
  omega

@[simp] theorem receiptIxEquivRuntime_touched_val (n : Nat) (key : Fin n) :
    (receiptIxEquivRuntime n (key, .touched)).val = 3 * key.val + 2 := by
  simp [receiptIxEquivRuntime, slotEquivFin, finProdFinEquiv]
  omega

/-- The literal flat runtime word, defined by the proved index equivalence. -/
def runtimeEncode {n : Nat} (witness : ReceiptWitness (Fin n) F) :
    Fin (n * 3) → F :=
  fun index => witness.encode ((receiptIxEquivRuntime n).symm index)

@[simp] theorem runtimeEncode_pre {n : Nat}
    (witness : ReceiptWitness (Fin n) F) (key : Fin n) :
    runtimeEncode witness (receiptIxEquivRuntime n (key, .pre)) = witness.pre key := by
  simp [runtimeEncode, ReceiptWitness.encode]

@[simp] theorem runtimeEncode_post {n : Nat}
    (witness : ReceiptWitness (Fin n) F) (key : Fin n) :
    runtimeEncode witness (receiptIxEquivRuntime n (key, .post)) = witness.post key := by
  simp [runtimeEncode, ReceiptWitness.encode]

@[simp] theorem runtimeEncode_touched {n : Nat}
    (witness : ReceiptWitness (Fin n) F) (key : Fin n) :
    runtimeEncode witness (receiptIxEquivRuntime n (key, .touched)) =
      witness.touched key := by
  simp [runtimeEncode, ReceiptWitness.encode]

/-- Flattening loses no semantic receipt information. -/
theorem runtimeEncode_injective {n : Nat} :
    Function.Injective (runtimeEncode (F := F) (n := n)) := by
  intro left right hword
  apply ReceiptWitness.encode_injective
  funext index
  have h := congrFun hword (receiptIxEquivRuntime n index)
  simpa [runtimeEncode] using h

/-- Literal runtime order of the two residual lanes per key. -/
def runtimeResiduals {n : Nat} (witness : ReceiptWitness (Fin n) F)
    (key : Fin n) : Fin 2 → F
  | 0 => witness.touched key * (witness.touched key - 1)
  | 1 => (1 - witness.touched key) * (witness.post key - witness.pre key)

@[simp] theorem runtimeResiduals_boolean {n : Nat}
    (witness : ReceiptWitness (Fin n) F) (key : Fin n) :
    runtimeResiduals witness key 0 = witness.residual (key, .boolean) :=
  rfl

@[simp] theorem runtimeResiduals_frame {n : Nat}
    (witness : ReceiptWitness (Fin n) F) (key : Fin n) :
    runtimeResiduals witness key 1 = witness.residual (key, .frame) :=
  rfl

/-- Runtime zero residuals are exactly the formal semantic relation. -/
theorem runtimeResiduals_zero_iff {n : Nat}
    (witness : ReceiptWitness (Fin n) F) :
    (∀ key lane, runtimeResiduals witness key lane = 0) ↔ witness.Satisfies := by
  constructor
  · intro h index
    rcases index with ⟨key, kind⟩
    cases kind with
    | boolean => exact h key 0
    | frame => exact h key 1
  · intro h key lane
    fin_cases lane
    · exact h (key, .boolean)
    · exact h (key, .frame)

/-- Reindexing the runtime vector back through the declared codec is literally
the formal receipt word used by `SemanticReceiptRelation`. -/
theorem runtimeEncode_refines_formal {n : Nat}
    (witness : ReceiptWitness (Fin n) F) :
    (fun index => runtimeEncode witness (receiptIxEquivRuntime n index)) =
      witness.encode := by
  funext index
  simp [runtimeEncode]

/-! ## The public typed-header binding carried by the accumulator word -/

/-- A 32-byte digest is represented injectively as sixteen little-endian u16
cells.  Byte-to-cell refinement is the responsibility of the concrete header
codec; this type fixes the accumulator width and order. -/
abbrev BindingIx := Fin 16

namespace HeaderBytes

open Minidregg.Compiler.NextgenLightClientPublicInputs

abbrev FixedBytes32 := FixedBytes 32

/-- The Rust header digest codec: adjacent bytes become one little-endian u16
cell, with no length prefix because the digest width is fixed. -/
def bindingNatCells (bytes : FixedBytes32) : { cells : List Nat // cells.length = 16 } :=
  ⟨packBytes bytes.1, by simp [bytes.2]⟩

theorem bindingNatCells_ranged (bytes : FixedBytes32) :
    ∀ cell ∈ (bindingNatCells bytes).1, cell < u16Base :=
  packBytes_lt bytes.1

/-- Pair packing is injective at fixed width.  This rules out a header-digest
alias before the cells are embedded in BabyBear/Ext6. -/
theorem bindingNatCells_injective : Function.Injective bindingNatCells := by
  intro left right hcells
  apply Subtype.ext
  have hpack : packBytes left.1 = packBytes right.1 :=
    congrArg Subtype.val hcells
  have happend : packBytes left.1 ++ ([] : List Nat) =
      packBytes right.1 ++ [] := congrArg (fun cells => cells ++ []) hpack
  have hparse := congrArg (parsePacked 32) happend
  have hleft : parsePacked 32 (packBytes left.1 ++ []) =
      some (left.1, []) := by
    simpa [left.2] using parsePacked_packBytes left.1 ([] : List Nat)
  have hright : parsePacked 32 (packBytes right.1 ++ []) =
      some (right.1, []) := by
    simpa [right.2] using parsePacked_packBytes right.1 ([] : List Nat)
  rw [hleft, hright] at hparse
  exact congrArg Prod.fst (Option.some.inj hparse)

end HeaderBytes

abbrev BoundReceiptIx (n : Nat) := BindingIx ⊕ ReceiptIx (Fin n)

/-- Exact runtime index equivalence: binding cells first, then key-major core. -/
def boundReceiptIxEquivRuntime (n : Nat) :
    BoundReceiptIx n ≃ Fin (16 + n * 3) :=
  (Equiv.sumCongr (Equiv.refl BindingIx) (receiptIxEquivRuntime n)).trans
    finSumFinEquiv

structure BoundReceiptWitness (n : Nat) (F : Type*) where
  binding : BindingIx → F
  core : ReceiptWitness (Fin n) F

def BoundReceiptWitness.encode {n : Nat} (witness : BoundReceiptWitness n F) :
    BoundReceiptIx n → F
  | .inl index => witness.binding index
  | .inr index => witness.core.encode index

/-- Literal runtime vector with sixteen binding cells followed by the flat
core relation word. -/
def boundRuntimeEncode {n : Nat} (witness : BoundReceiptWitness n F) :
    Fin (16 + n * 3) → F :=
  fun index => witness.encode ((boundReceiptIxEquivRuntime n).symm index)

@[simp] theorem boundRuntimeEncode_binding {n : Nat}
    (witness : BoundReceiptWitness n F) (index : BindingIx) :
    boundRuntimeEncode witness (boundReceiptIxEquivRuntime n (.inl index)) =
      witness.binding index := by
  simp [boundRuntimeEncode, BoundReceiptWitness.encode]

@[simp] theorem boundRuntimeEncode_core {n : Nat}
    (witness : BoundReceiptWitness n F) (index : ReceiptIx (Fin n)) :
    boundRuntimeEncode witness (boundReceiptIxEquivRuntime n (.inr index)) =
      witness.core.encode index := by
  simp [boundRuntimeEncode, BoundReceiptWitness.encode]

theorem boundRuntimeEncode_injective {n : Nat} :
    Function.Injective (boundRuntimeEncode (F := F) (n := n)) := by
  intro left right hword
  have hencode : left.encode = right.encode := by
    funext index
    have h := congrFun hword (boundReceiptIxEquivRuntime n index)
    simpa [boundRuntimeEncode] using h
  cases left with
  | mk leftBinding leftCore =>
    cases right with
    | mk rightBinding rightCore =>
      have hbinding : leftBinding = rightBinding := by
        funext index
        exact congrFun hencode (.inl index)
      have hcore : leftCore = rightCore := by
        apply ReceiptWitness.encode_injective
        funext index
        exact congrFun hencode (.inr index)
      cases hbinding
      cases hcore
      rfl

/-- The accumulated bound language: arbitrary public binding cells plus a
genuine semantic receipt core.  The typed-header codec supplies those cells;
the core relation supplies the nonlinear constraints. -/
def BoundSemanticReceiptRelation {n : Nat}
    (word : BoundReceiptIx n → F) : Prop :=
  ∃ witness : BoundReceiptWitness n F,
    witness.core.Satisfies ∧ word = witness.encode

structure BoundSemanticReceiptClaim (n : Nat) (F : Type*) [Field F]
    [DecidableEq F] where
  witness : BoundReceiptWitness n F
  valid : witness.core.Satisfies

def boundEvalAt {n : Nat} (ix : BoundReceiptIx n) :
    (BoundReceiptIx n → F) →ₗ[F] F where
  toFun word := word ix
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def boundReceiptCoord {n : Nat}
    (k : Fin (Fintype.card (BoundReceiptIx n))) : BoundReceiptIx n :=
  (Fintype.equivFin (BoundReceiptIx n)).symm k

theorem boundReceiptCoord_surjective {n : Nat} (ix : BoundReceiptIx n) :
    ∃ k, boundReceiptCoord k = ix := by
  exact ⟨Fintype.equivFin (BoundReceiptIx n) ix, by simp [boundReceiptCoord]⟩

noncomputable def BoundSemanticReceiptClaim.acc {n : Nat} {Root : Type*}
    (claim : BoundSemanticReceiptClaim n F) (root : Root) :
    Minidregg.Loom.AccClaim Root F (BoundReceiptIx n)
      (Fintype.card (BoundReceiptIx n)) :=
  ⟨root, fun k =>
    (boundEvalAt (boundReceiptCoord k), claim.witness.encode (boundReceiptCoord k))⟩

theorem BoundSemanticReceiptClaim.acc_weights_shared
    {n : Nat} {Root : Type*}
    (left right : BoundSemanticReceiptClaim n F) (leftRoot rightRoot : Root) :
    ∀ k, (right.acc rightRoot).weights k = (left.acc leftRoot).weights k :=
  fun _ => rfl

theorem BoundSemanticReceiptClaim.acc_satisfies_iff
    {n : Nat} {Root : Type*}
    {C : Submodule F (BoundReceiptIx n → F)}
    (claim : BoundSemanticReceiptClaim n F) (root : Root)
    (word : BoundReceiptIx n → F) :
    Minidregg.Loom.AccClaim.Satisfies C (claim.acc root) word ↔
      word ∈ C ∧ word = claim.witness.encode := by
  unfold Minidregg.Loom.AccClaim.Satisfies
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    funext ix
    obtain ⟨k, rfl⟩ := boundReceiptCoord_surjective ix
    simpa [BoundSemanticReceiptClaim.acc, Minidregg.Loom.AccClaim.weights,
      Minidregg.Loom.AccClaim.targets, boundEvalAt] using h k
  · rintro rfl k
    simp [BoundSemanticReceiptClaim.acc, Minidregg.Loom.AccClaim.weights,
      Minidregg.Loom.AccClaim.targets, boundEvalAt]

/-- Bound words fold through the real Loom claim while retaining the typed
header binding as ordinary authenticated coordinates. -/
theorem boundSemanticReceiptClaims_fold
    {n : Nat} {Root : Type*}
    {C : Submodule F (BoundReceiptIx n → F)}
    (foldRoot : Root → F → Root → Root)
    (left right : BoundSemanticReceiptClaim n F)
    (leftRoot rightRoot : Root) (gamma : F)
    (hleft : left.witness.encode ∈ C)
    (hright : right.witness.encode ∈ C) :
    Minidregg.Loom.AccClaim.Satisfies C
      (Minidregg.Loom.foldClaims foldRoot (left.acc leftRoot)
        (right.acc rightRoot) gamma)
      (left.witness.encode + gamma • right.witness.encode) := by
  apply Minidregg.Loom.foldClaims_satisfies foldRoot gamma
    (left.acc_weights_shared right leftRoot rightRoot)
  · exact (left.acc_satisfies_iff leftRoot _).mpr ⟨hleft, rfl⟩
  · exact (right.acc_satisfies_iff rightRoot _).mpr ⟨hright, rfl⟩

/-- info: 'Minidregg.Assurance.SemanticReceiptRuntimeCodec.boundRuntimeEncode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundRuntimeEncode_injective
/-- info: 'Minidregg.Assurance.SemanticReceiptRuntimeCodec.boundSemanticReceiptClaims_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boundSemanticReceiptClaims_fold
/-- info: 'Minidregg.Assurance.SemanticReceiptRuntimeCodec.HeaderBytes.bindingNatCells_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HeaderBytes.bindingNatCells_injective

end Minidregg.Assurance.SemanticReceiptRuntimeCodec
