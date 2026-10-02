/-
# Kernel.DeclaredFields -- a small fixed record as a declared-effect store

Several source-owned resources (an agent task, an application, an application
session) are four integer fields of one declared object.  They are stored as
entries of the one declared-effect store (`Compiler.DeclaredEffectCell`), not
as a page.  This module gives the store of such a record, the canonical order
of its fields, and the exact policy projection the generic declared receiver
computes from two such stores.

The canonical order is the byte order of the field keys' encodings.  Field `n`
of object `o` encodes as `0 :: nat o ++ nat n`, and `nat 0 = [255]` sorts after
`nat n = [n, 255]` for `0 < n < 255`: the order is fields 1, 2, 3, 0.
-/
import Kernel.DeclaredResourceProjection
import Kernel.FieldClosure

namespace Minidregg.Kernel.DeclaredFields

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.Store (Store Address)

set_option autoImplicit false

def key (object field : Nat) : StateKey := .objectField ⟨object⟩ ⟨field⟩

/-- Four field values in the store's canonical order (1, 2, 3, 0). -/
def four (v0 v1 v2 v3 : Int) : DeclaredResourceProjection.Values :=
  [(1, v1), (2, v2), (3, v3), (0, v0)]

def entries (object : Nat) (values : DeclaredResourceProjection.Values) :
    List (Minidregg.Theory.Store.Entry effectLayout) :=
  values.map fun pair => ⟨(key object pair.1).address, pair.2⟩

/-- The record's store: exactly its fields, nothing else. -/
def store (object : Nat) (values : DeclaredResourceProjection.Values) : Store effectLayout :=
  StoreCodec.fromEntries (entries object values)

/-- A four-field record's declaration (K-FIELD-CLOSURE): it holds fields 0–3
and may create no other. -/
def recordFields : FieldClosure.FieldSet := .closed [0, 1, 2, 3]

/-- The record's cell at birth: its fields and its declaration. -/
def birthStore (object : Nat) (values : DeclaredResourceProjection.Values) : Store effectLayout :=
  FieldClosure.declare object recordFields (store object values)

/-- Read field `field` of `object`. -/
def read (object field : Nat) (logical : Store effectLayout) : Option Int :=
  logical (key object field).address

/-- The kernel's blinding ratchet (K-HIDE-ROTATE) writes no field. -/
@[simp] theorem read_ratchet (object field : Nat) (store pre : Store effectLayout) (height : Nat) :
    read object field (Minidregg.Theory.Store.Patch.run store
      (DeclaredEffectCell.blinding.patch pre height)) = read object field store :=
  StoreCodec.Blinding.run_patch_frame _ _ _ _ _ (by
    simp [StoreCodec.Blinding.address, DeclaredEffectCell.blinding, key, StateKey.address])

private theorem key_addressKey (object field : Nat) :
    StoreCodec.addressKey DeclaredEffectCell.wire (key object field).address =
      ((0 :: StreamCodec.nat.encode object).map UInt8.toNat) ++
        (digestStream.encode ⟨field⟩).map UInt8.toNat := by
  simp [StoreCodec.addressKey, StoreCodec.addressStream, FiniteDependentMapCodec.entryStream,
    DeclaredEffectCell.wire, key, StateKey.address, DeclaredEffectCell.stateKeyStream,
    StoreCodec.unitStream, List.map_append]

private theorem field_lt (object i j : Nat)
    (ordered : (digestStream.encode ⟨i⟩).map UInt8.toNat <
      (digestStream.encode ⟨j⟩).map UInt8.toNat) :
    StoreCodec.addressKey DeclaredEffectCell.wire (key object i).address <
      StoreCodec.addressKey DeclaredEffectCell.wire (key object j).address := by
  rw [key_addressKey, key_addressKey]
  exact List.append_left_lt ordered

/-- The four entries are already in the wire's canonical order. -/
theorem four_ordered (object : Nat) (v0 v1 v2 v3 : Int) :
    (entries object (four v0 v1 v2 v3)).Pairwise (StoreCodec.AddressLT DeclaredEffectCell.wire) := by
  simp only [entries, four, List.map_cons, List.map_nil]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ List.Pairwise.nil)))
  all_goals
    intro other member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    try (rcases member with rfl | rfl | rfl <;> (apply field_lt; decide))

/-- The receiver's projection of two four-field records is exactly the scalar
slots of their canonical coordinates. -/
theorem project_four (object : Nat) (v0 v1 v2 v3 w0 w1 w2 w3 : Int) :
    DeclaredResourceProjection.project object
        (store object (four v0 v1 v2 v3)) (store object (four w0 w1 w2 w3)) =
      DeclaredResourceProjection.scalarSlots (four v0 v1 v2 v3) (four w0 w1 w2 w3) := by
  unfold DeclaredResourceProjection.project DeclaredResourceProjection.values store
  rw [StoreCodec.entries_fromEntries_of_pairwise _ _ (four_ordered object v0 v1 v2 v3),
    StoreCodec.entries_fromEntries_of_pairwise _ _ (four_ordered object w0 w1 w2 w3)]
  simp [entries, four, key, StateKey.address]

/-- Each field of a four-field record reads back exactly. -/
theorem read_four (object : Nat) (v0 v1 v2 v3 : Int) :
    read object 0 (store object (four v0 v1 v2 v3)) = some v0 ∧
      read object 1 (store object (four v0 v1 v2 v3)) = some v1 ∧
      read object 2 (store object (four v0 v1 v2 v3)) = some v2 ∧
      read object 3 (store object (four v0 v1 v2 v3)) = some v3 := by
  have distinct : ((entries object (four v0 v1 v2 v3)).map Sigma.fst).Nodup := by
    refine List.pairwise_map.mpr ((four_ordered object v0 v1 v2 v3).imp ?_)
    intro left right less same
    unfold StoreCodec.AddressLT at less
    rw [same] at less
    exact List.lt_irrefl _ less
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact StoreCodec.fromEntries_apply_of_mem _ distinct
      (entry := ⟨(key object 0).address, v0⟩) (by simp [entries, four])
  · exact StoreCodec.fromEntries_apply_of_mem _ distinct
      (entry := ⟨(key object 1).address, v1⟩) (by simp [entries, four])
  · exact StoreCodec.fromEntries_apply_of_mem _ distinct
      (entry := ⟨(key object 2).address, v2⟩) (by simp [entries, four])
  · exact StoreCodec.fromEntries_apply_of_mem _ distinct
      (entry := ⟨(key object 3).address, v3⟩) (by simp [entries, four])

/-- info: 'Minidregg.Kernel.DeclaredFields.project_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms project_four
/-- info: 'Minidregg.Kernel.DeclaredFields.read_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms read_four

end Minidregg.Kernel.DeclaredFields
