/-
# Theory.SparseLogicalState -- the finitely-supported cell state

`Theory.MaterializerCardinality` proves that all four schemas in this tree admit
no `CellState.Materializer`, because `LogicalState.fields` is a TOTAL function
over an infinite field index and a `LawfulCodec` cannot inject an uncountable
state space into `List UInt8`.

This is the replacement, and it is deliberately the most primitive of the three
shapes considered: **a canonical dependent finite map with an Option-valued
read, and no default at all**.  The other two candidate designs are then VIEWS
on this one rather than
rival cores:

* a schema-side default is `readD (S.default ·)`;
* a state-side default is `readD` applied to a default the caller carries.

Both are `readD` below.  Nothing has to choose, which is the point -- the
encoding is primitive and the totality conventions live above it.  It is also
what `Hyperdocument.cellSchema` and `HyperdocumentEventLog.cellSchema` already
do in their own value types (`FieldType := fun a => Option (Value a.1)`), so
for those two the Option-valued read is the shape the schema already wanted.

**Status: this is a staged migration, and the endpoint is deletion of the
total-function field.**  `CellState.LogicalState` is unchanged so far; each
schema moves across separately, and the old shape goes when the last one has.
The migration order and the reason each step is separable are at the bottom of
this file.  A twin with a named endpoint is the only way to make a change this
wide reviewable; a twin without one is what the first law forbids.
-/
import Theory.CellState
import Theory.MaterializerCardinality
import Mathlib.Data.DFinsupp.Encodable

namespace Minidregg.Theory.SparseLogicalState

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

universe u v w x

/-! ## The carrier -/

/-- `none` is the distinguished absent value stored as DFinsupp zero.  This is
representation structure only; it does not choose a default *field value* for
the total view. -/
instance optionZero (alpha : Type v) : Zero (Option alpha) := ⟨none⟩

/-- A canonical finitely-supported dependent map.  The stored value at a field
is optional, so `none` is the primitive absence value and is omitted from the
finite support.  `DFinsupp` equality is extensional: insertion order and stale
duplicate writes are not part of logical identity and therefore cannot create
different canonical roots for the same sparse map. -/
abbrev SparseState (S : Schema.{u, v, w, x}) :=
  Π₀ field : S.Field, Option (S.FieldType field)

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

/-- Write one present field value.  `DFinsupp.update` replaces any prior value,
so a sequence of writes has one extensional result rather than an
order-dependent association-list representation. -/
def write (state : SparseState S) (field : S.Field)
    (value : S.FieldType field) : SparseState S :=
  state.update field (some value)

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
Contrast `MaterializerCardinality.authorityMaterializer_isEmpty`, where the
total-function state space made this impossible. -/
theorem nonempty_lawfulCodec_sparse {S : Schema.{0, 0, 0, 0}}
    [Countable S.Field] [∀ field, Countable (S.FieldType field)] :
    Nonempty (LawfulCodec (SparseState S)) :=
  haveI : Nonempty (SparseState S) := ⟨0⟩
  MaterializerCardinality.nonempty_lawfulCodec_of_countable

/-! ## The fix, demonstrated on a real schema

Existence in the abstract is cheap.  This is `DeclaredTurn.effectSchema` -- the
first migration step, and the schema `Kernel.DeclaredHyperedge` sits on --
carried all the way to a codec, so the fix is shown to work on something the
tree actually uses rather than on a hypothetical countable schema. -/

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

/-- **A codec exists for the sparse effect state.**  The schema
`MaterializerCardinality.effectMaterializer_isEmpty` proves unmaterializable as
a total function is materializable the moment its state is finitely supported.
That is the fix, on a schema the kernel actually uses. -/
theorem nonempty_lawfulCodec_sparse_effect :
    Nonempty (LawfulCodec (SparseState DeclaredTurn.effectSchema.{0, 0})) :=
  nonempty_lawfulCodec_sparse

/-! ## Migration order, and why each step is separable

Each schema moves independently because nothing reads another schema's cells.

1. `DeclaredTurn.effectSchema` — the smallest, and the one whose readers are
   most concentrated. Its `EffectDeclaration.Store` is itself a total function
   and has to move with it, which is the only place the two changes are
   coupled.
2. `CredentialAuthorityState.schema` — mixed value types (`Option
   StoredCapability`, `Epoch`, `Bool`), so its readers become `readD` with a
   schema-side default naming zero epochs and unrevoked keys. That default is
   worth writing out: it is the "empty authority" the model has always assumed
   and never stated.
3. `Hyperdocument.cellSchema` and 4. `HyperdocumentEventLog.cellSchema` — both
   already have `Option`-shaped value types, so their readers want `read`
   composed with `Option.join`, or equivalently `readD (fun _ => none)`.

The `Countable (Sigma S.FieldType)` instance each step needs does not exist for
any of them yet — `Countable AuthorityField` alone wants a `deriving instance`,
and the capability value types want `Countable` through `Finset`. That plumbing
is part of the step, not a precondition someone else supplies.

`LogicalState.resources` is left alone deliberately: it is also a total
function, but every schema in the tree has `Resource := Empty`, so it
contributes a single inhabitant and no obstruction. If a schema ever uses a
nonempty infinite `Resource`, it needs this same treatment.
-/

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.read_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.read_empty
/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.read_write_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.read_write_self
/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.read_write_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.read_write_other
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
