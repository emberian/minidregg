/-
# Theory.SparseLogicalState -- the finitely-supported cell state

`Theory.MaterializerCardinality` proves that the former total-function field
carrier made four deployed schemas unmaterializable.  `CellState.FieldStore`
is now the repaired canonical carrier: **a dependent finite map with an
Option-valued read and no implicit default**.  This module gives that landed
carrier its sparse-state vocabulary and records the counting theorem which
shows why the repair is sufficient.

The two useful total views are policies above the one carrier, not rival cores:

* a schema-side default is `readD (S.default ·)`;
* a state-side default is `readD` applied to a default the caller carries.

Both are `readD` below.  Canonical bytes encode only the primitive finite map;
zero epochs, false membership, and semantic store defaults are named at their
respective readers.  Hyperdocument and event-log values are stored directly,
with absence represented once by the carrier rather than by a second nested
`Option`.
-/
import Theory.CellState
import Theory.MaterializerCardinality

namespace Minidregg.Theory.SparseLogicalState

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

universe u v w x

/-! ## The carrier -/

/-- A canonical finitely-supported dependent map.  The stored value at a field
is optional, so `none` is the primitive absence value and is omitted from the
finite support.  `DFinsupp` equality is extensional: insertion order and stale
duplicate writes are not part of logical identity and therefore cannot create
different canonical roots for the same sparse map. -/
abbrev SparseState (S : Schema.{u, v, w, x}) :=
  CellState.FieldStore S

namespace SparseState

variable {S : Schema.{u, v, w, x}}

/-- **The primitive read.**  Option-valued, because absence is a real answer
and inventing one is the caller's decision, not the carrier's. -/
def read (state : SparseState S) (field : S.Field) : Option (S.FieldType field) :=
  state field

/-- The empty state reads absent everywhere. -/
@[simp] theorem read_empty (field : S.Field) :
    (0 : SparseState S).read field = none := rfl

/-- **The total view.**  Supply a default and reads become total.  Passing the
schema's own default gives the schema-side design; passing one the state
carries gives the state-side design; both are this function. -/
def readD (state : SparseState S) (default : (field : S.Field) → S.FieldType field)
    (field : S.Field) : S.FieldType field :=
  (state.read field).getD (default field)

/-- With an empty state, the total view is exactly the default -- so "no
default" and "default everywhere" are the same object seen two ways. -/
@[simp] theorem readD_empty
    (default : (field : S.Field) → S.FieldType field) (field : S.Field) :
    (0 : SparseState S).readD default field = default field := rfl

variable [DecidableEq S.Field]

/-- Assign one primitive sparse slot.  `none` is deletion. -/
def assign (state : SparseState S) (field : S.Field)
    (value : Option (S.FieldType field)) : SparseState S :=
  CellState.FieldStore.assign state field value

/-- Write one present field value.  `DFinsupp.update` replaces any prior value,
so a sequence of writes has one extensional result rather than an
order-dependent association-list representation. -/
def write (state : SparseState S) (field : S.Field)
    (value : S.FieldType field) : SparseState S :=
  CellState.FieldStore.write state field value

/-- Remove one address from the structural finite support. -/
def erase (state : SparseState S) (field : S.Field) : SparseState S :=
  CellState.FieldStore.erase state field

/-- A written entry is read back. -/
@[simp] theorem read_write_self (state : SparseState S) (field : S.Field)
    (value : S.FieldType field) :
    (state.write field value).read field = some value := by
  simp [read, write]

/-- A write frames every other field. -/
theorem read_write_other (state : SparseState S) {field other : S.Field}
    (different : other ≠ field)
    (value : S.FieldType other) :
    (state.write other value).read field = state.read field := by
  change Function.update (⇑state) other (some value) field = state field
  rw [Function.update_of_ne (Ne.symm different)]

/-- Erasure reads back as primitive absence. -/
@[simp] theorem read_erase_self (state : SparseState S) (field : S.Field) :
    (state.erase field).read field = none := by
  simpa [read, erase, CellState.FieldStore.read] using
    (CellState.FieldStore.read_erase_self state field)

end SparseState

/-! ## Why this fixes the obstruction

The counting argument dies here: a dependent finitely-supported map over
countable indices and fibers is countable, so
`materializer_nonempty_iff_countable` supplies a codec. -/

/-- A sparse state space is countable whenever its index and every typed fiber
are countable. -/
instance countable_sparseState {S : Schema.{0, 0, 0, 0}}
    [Countable S.Field] [∀ field, Countable (S.FieldType field)] :
    Countable (SparseState S) := by infer_instance

/-- **The obstruction is gone**, for any schema whose typed entries are
countable: the sparse state space is countable, and
`MaterializerCardinality.nonempty_lawfulCodec_of_countable` then gives a codec.
Contrast the regression theorem for the deleted total-function carrier, where
the same construction was impossible. -/
theorem nonempty_lawfulCodec_sparse {S : Schema.{0, 0, 0, 0}}
    [Countable S.Field] [∀ field, Countable (S.FieldType field)] :
    Nonempty (LawfulCodec (SparseState S)) :=
  haveI : Nonempty (SparseState S) := ⟨0⟩
  MaterializerCardinality.nonempty_lawfulCodec_of_countable

/-! ## The fix on a deployed schema

`DeclaredTurn.effectSchema` is the state schema used by
`Kernel.DeclaredHyperedge`.  The instances below carry the repaired state all
the way to a lawful codec existence theorem. -/

open Minidregg.Theory.EffectDeclaration in
/-- A first-order code for the three state-key constructors.  Nothing subtle:
the point is that `StateKey` is countable, and Lean does not derive that. -/
def stateKeyCode : StateKey -> Nat × Nat × Nat
  | .objectField object field => (0, object.value, field.value)
  | .accountBalance account resource => (1, account.value, resource.value)
  | .programCode program => (2, program.value, 0)

open Minidregg.Theory.EffectDeclaration in
theorem stateKeyCode_injective : Function.Injective stateKeyCode := by
  rintro (⟨⟨o⟩, ⟨f⟩⟩ | ⟨⟨a⟩, ⟨r⟩⟩ | ⟨⟨p⟩⟩) (⟨⟨o'⟩, ⟨f'⟩⟩ | ⟨⟨a'⟩, ⟨r'⟩⟩ | ⟨⟨p'⟩⟩) same <;>
    simp_all [stateKeyCode]

open Minidregg.Theory.EffectDeclaration in
instance : Countable StateKey :=
  Function.Injective.countable stateKeyCode_injective

instance : Countable DeclaredTurn.effectSchema.Field :=
  inferInstanceAs (Countable EffectDeclaration.StateKey)

instance : ∀ field : DeclaredTurn.effectSchema.Field,
    Countable (DeclaredTurn.effectSchema.FieldType field) :=
  fun _ => inferInstanceAs (Countable Int)

open Minidregg.Theory.EffectDeclaration in
instance : Countable (Sigma DeclaredTurn.effectSchema.FieldType) :=
  Function.Injective.countable
    (f := fun entry => (entry.1, show Int from entry.2))
    (by
      rintro ⟨key, value⟩ ⟨key', value'⟩ same
      simp only [Prod.mk.injEq] at same
      obtain ⟨sameKey, sameValue⟩ := same
      subst sameKey
      simp_all)

/-- **A codec exists for the canonical effect state.**  The corresponding
deleted total-function carrier is unmaterializable; the finite-map state used
by the kernel is materializable. -/
theorem nonempty_lawfulCodec_sparse_effect :
    Nonempty (LawfulCodec (SparseState DeclaredTurn.effectSchema.{0, 0})) :=
  nonempty_lawfulCodec_sparse

/-! ## Representation boundary

The four formerly impossible schemas now use this carrier directly:
`DeclaredTurn.effectSchema`, `CredentialAuthorityState.schema`,
`Hyperdocument.cellSchema`, and `HyperdocumentEventLog.cellSchema`.  The total
`EffectDeclaration.Store` remains a semantic evaluator only.  Declared turns
reify the exact finite footprint over their canonical pre-state and prove a
frame law for every coordinate outside it; they do not attempt to serialize an
arbitrary total function.

`LogicalState.resources` remains total.  Every migrated schema has
`Resource := Empty`, so that function has one inhabitant and causes no counting
obstruction.  A future schema with an infinite nonempty resource index must
make its resource representation finite or otherwise encodable explicitly.
-/

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.read_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.read_empty
/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.read_write_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.read_write_self
/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.read_write_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.read_write_other
/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.read_erase_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.read_erase_self
/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.readD_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.readD_empty
/-- info: 'Minidregg.Theory.SparseLogicalState.countable_sparseState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms countable_sparseState
/-- info: 'Minidregg.Theory.SparseLogicalState.nonempty_lawfulCodec_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_lawfulCodec_sparse
/-- info: 'Minidregg.Theory.SparseLogicalState.stateKeyCode_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms stateKeyCode_injective
/-- info: 'Minidregg.Theory.SparseLogicalState.nonempty_lawfulCodec_sparse_effect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_lawfulCodec_sparse_effect

end Minidregg.Theory.SparseLogicalState
