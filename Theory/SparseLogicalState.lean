/-
# Theory.SparseLogicalState -- the finitely-supported cell state

`Theory.MaterializerCardinality` proves that all four schemas in this tree admit
no `CellState.Materializer`, because `LogicalState.fields` is a TOTAL function
over an infinite field index and a `LawfulCodec` cannot inject an uncountable
state space into `List UInt8`.

This is the replacement, and it is deliberately the most primitive of the three
shapes considered: **entries plus an Option-valued read, and no default at
all**.  The other two candidate designs are then VIEWS on this one rather than
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

namespace Minidregg.Theory.SparseLogicalState

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

universe u v w x

/-! ## The carrier -/

/-- A finitely-supported logical state: an association list of typed entries.
Absence is `none`; there is no default here, by design. -/
structure SparseState (S : Schema.{u, v, w, x}) where
  entries : List (Sigma S.FieldType)

namespace SparseState

variable {S : Schema.{u, v, w, x}} [DecidableEq S.Field]

/-- **The primitive read.**  Option-valued, because absence is a real answer
and inventing one is the caller's decision, not the carrier's. -/
def read (state : SparseState S) (field : S.Field) : Option (S.FieldType field) :=
  state.entries.findSome? fun entry =>
    if same : entry.1 = field then some (same ▸ entry.2) else none

/-- **The total view.**  Supply a default and reads become total.  Passing the
schema's own default gives the schema-side design; passing one the state
carries gives the state-side design; both are this function. -/
def readD (state : SparseState S) (default : (field : S.Field) → S.FieldType field)
    (field : S.Field) : S.FieldType field :=
  (state.read field).getD (default field)

/-- The empty state reads absent everywhere. -/
@[simp] theorem read_empty (field : S.Field) :
    (⟨[]⟩ : SparseState S).read field = none := rfl

/-- A written entry is read back.  This is the law that makes `read` a lookup
rather than an arbitrary function. -/
@[simp] theorem read_cons_self (field : S.Field) (value : S.FieldType field)
    (rest : List (Sigma S.FieldType)) :
    (⟨⟨field, value⟩ :: rest⟩ : SparseState S).read field = some value := by
  simp [read]

/-- Entries for other fields are skipped. -/
theorem read_cons_other {field other : S.Field}
    (different : other ≠ field)
    (value : S.FieldType other) (rest : List (Sigma S.FieldType)) :
    (⟨⟨other, value⟩ :: rest⟩ : SparseState S).read field =
      (⟨rest⟩ : SparseState S).read field := by
  simp [read, different]

/-- With an empty state, the total view is exactly the default -- so "no
default" and "default everywhere" are the same object seen two ways. -/
@[simp] theorem readD_empty
    (default : (field : S.Field) → S.FieldType field) (field : S.Field) :
    (⟨[]⟩ : SparseState S).readD default field = default field := rfl

end SparseState

/-! ## Why this fixes the obstruction

The counting argument dies here: an association list over a countable entry
type is countable, so the state space is countable, so
`materializer_nonempty_iff_countable` supplies a codec. -/

/-- A sparse state space is countable whenever its typed entries are. -/
instance countable_sparseState {S : Schema.{0, 0, 0, 0}}
    [Countable (Sigma S.FieldType)] : Countable (SparseState S) := by
  apply Function.Injective.countable (f := SparseState.entries)
  intro left right same
  cases left
  cases right
  simpa using same

/-- **The obstruction is gone**, for any schema whose typed entries are
countable: the sparse state space is countable, and
`MaterializerCardinality.nonempty_lawfulCodec_of_countable` then gives a codec.
Contrast `MaterializerCardinality.authorityMaterializer_isEmpty`, where the
total-function state space made this impossible. -/
theorem nonempty_lawfulCodec_sparse {S : Schema.{0, 0, 0, 0}}
    [Countable (Sigma S.FieldType)] : Nonempty (LawfulCodec (SparseState S)) :=
  haveI : Nonempty (SparseState S) := ⟨⟨[]⟩⟩
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

/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.read_empty' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.read_empty
/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.read_cons_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.read_cons_self
/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.read_cons_other' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms SparseState.read_cons_other
/-- info: 'Minidregg.Theory.SparseLogicalState.SparseState.readD_empty' does not depend on any axioms -/
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
