/-
# Theory.MaterializerCardinality -- a schema can be too wide to materialize

`CellState.Materializer S Root` carries `codec : LawfulCodec (LogicalState S)`,
and `LawfulCodec.decode_encode` makes `encode` injective.  So a materializer is,
among other things, an injection from the schema's entire logical state space
into `List UInt8`.

`List UInt8` is countable.  A schema with infinitely many independent two-valued
fields has an uncountable state space.  Such a schema therefore admits **no
materializer at all**, and every theorem quantified over one of its cells is
vacuous.

This is not hypothetical.  `CredentialAuthorityState.schema` has
`AuthorityField.nullifier : Nat -> AuthorityField` with value type `Bool`, so
its state space contains `Nat -> Bool`.  `authorityMaterializer_isEmpty` below
proves that `CredentialAuthorityState.Materializer` is empty.

**What that means, stated carefully.**  It does not mean the credential
authority model is wrong; it means the *materializer interface* asks for
something no encoding can supply at an infinite field index.  The fix is the
one the rest of the tree already uses in its own vocabulary: canonicalize
finitely-supported states.  A `LogicalState` for a sparse schema should be a
finite map with a default, not a total function, and then the codec is the
finite map's codec.  Until that lands, `Cell`-quantified theorems over these
schemas are conditional on a premise that is provably unsatisfiable.

The witness schemas in `Theory.CellStateWitness` are finite and are unaffected.
-/
import Theory.CellState
import Theory.CredentialAuthorityState
import Theory.Hyperdocument

namespace Minidregg.Theory.MaterializerCardinality

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## The counting lemma -/

instance : Countable UInt8 :=
  Function.Injective.countable (f := UInt8.toNat)
    (by intro left right same; exact UInt8.toNat.inj same)

/-- No countable type admits an injection from `Nat -> Bool`.  Proved by
diagonalization rather than cardinal arithmetic, so the statement stays
elementary. -/
theorem not_injective_natBool {beta : Type} [Countable beta]
    (encode : (Nat -> Bool) -> beta) : ¬Function.Injective encode := by
  intro injective
  have countable : Countable (Nat -> Bool) := injective.countable
  obtain ⟨enumerate, surjective⟩ := exists_surjective_nat (Nat -> Bool)
  let diagonal : Nat -> Bool := fun index => !(enumerate index index)
  obtain ⟨index, hit⟩ := surjective diagonal
  have point := congrFun hit index
  simp [diagonal] at point

/-- A lawful codec is an injection into a countable type, so its domain is
countable.  This is the whole content of the argument; everything below is
finding a schema whose state space is not. -/
theorem lawfulCodec_injective {alpha : Type} (codec : LawfulCodec alpha) :
    Function.Injective codec.encode := by
  intro left right same
  have decoded : codec.decode (codec.encode left) =
      codec.decode (codec.encode right) := by rw [same]
  rw [codec.decode_encode, codec.decode_encode] at decoded
  exact Option.some.inj decoded

/-- **The general obstruction.**  If a schema's logical state space contains an
injective copy of `Nat -> Bool`, it has no materializer, for any root type. -/
theorem materializer_isEmpty_of_natBool_embedding
    {S : Schema.{0, 0, 0, 0}} {Root : Type}
    (embed : (Nat -> Bool) -> LogicalState S)
    (embed_injective : Function.Injective embed) :
    IsEmpty (Materializer S Root) :=
  ⟨fun materializer =>
    not_injective_natBool (fun value => materializer.codec.encode (embed value))
      ((lawfulCodec_injective materializer.codec).comp embed_injective)⟩

/-! ## The credential authority schema is one such schema -/

open Minidregg.Theory.CredentialAuthorityState in
/-- Nullifier fields carry `Bool` and are indexed by `Nat`, so an arbitrary
predicate on naturals is a logical state.  Every other field takes its default. -/
def authorityStateOf (marked : Nat -> Bool) : LogicalState schema where
  fields := fun field =>
    match field with
    | .capability _ _ => none
    | .issuerEpoch _ => (0 : Nat)
    | .policyEpoch _ => (0 : Nat)
    | .subjectKeyEpoch _ => (0 : Nat)
    | .revoked _ => false
    | .nullifier index => marked index
  resources := fun resource => resource.elim

open Minidregg.Theory.CredentialAuthorityState in
theorem authorityStateOf_injective : Function.Injective authorityStateOf := by
  intro left right same
  funext index
  have fields := congrArg LogicalState.fields same
  exact congrFun fields (.nullifier index)

open Minidregg.Theory.CredentialAuthorityState in
/-- **`CredentialAuthorityState.Materializer` is empty.**  So
`CredentialAuthorityState.Cell M` cannot be formed, `AuthenticatedPrincipal`
cannot be formed, and every theorem quantified over an authority cell is
vacuously true. -/
theorem authorityMaterializer_isEmpty : IsEmpty Materializer.{0, 0} :=
  materializer_isEmpty_of_natBool_embedding (Root := Digest) authorityStateOf
    authorityStateOf_injective

open Minidregg.Theory.CredentialAuthorityState in
/-- Stated the way an audit wants it: there is no authority cell, for any
materializer, because there is no materializer. -/
theorem no_authority_cell :
    ¬∃ (M : CredentialAuthorityState.Materializer.{0, 0})
      (_ : CredentialAuthorityState.Cell M), True := by
  rintro ⟨materializer, _, _⟩
  exact authorityMaterializer_isEmpty.false materializer

/-! ## And the Hyperdocument schema is another

Same shape, different namespace: `cellSchema.Field` is `Address = Sigma Key`,
the document keys are digest wrappers indexed by `Nat`, and the value type is
`Option DocumentRecord`, which has at least two inhabitants.  So the obstruction
is not a quirk of one schema; it is what happens whenever a sparse namespace is
typed as a total function. -/

open Minidregg.Theory.Hyperdocument in
/-- A document record built from zeros, used only to make `Option` two-valued. -/
def sampleDocument : DocumentRecord where
  rootElement := ⟨⟨0⟩⟩
  schema := ⟨0⟩
  createdBy := { subject := ⟨0⟩, capabilityKind := .object, capabilityId := ⟨0⟩ }
  createdAt := ⟨⟨0⟩⟩

open Minidregg.Theory.Hyperdocument in
/-- Mark document `n` present or absent according to `marked n`. -/
def documentStateOf (marked : Nat -> Bool) : LogicalState cellSchema where
  fields := fun address =>
    match address with
    | ⟨.documents, key⟩ =>
        if marked key.digest.value then some sampleDocument else none
    | _ => none
  resources := fun resource => resource.elim

open Minidregg.Theory.Hyperdocument in
theorem documentStateOf_injective : Function.Injective documentStateOf := by
  intro left right same
  funext index
  have fields := congrArg LogicalState.fields same
  have point := congrFun fields ⟨.documents, ⟨⟨index⟩⟩⟩
  simp only [documentStateOf] at point
  by_cases hleft : left index = true
  · by_cases hright : right index = true
    · rw [hleft, hright]
    · simp [hleft, hright] at point
  · by_cases hright : right index = true
    · simp [hleft, hright] at point
    · simp only [Bool.not_eq_true] at hleft hright
      rw [hleft, hright]

open Minidregg.Theory.Hyperdocument in
/-- **`Hyperdocument.Materializer Digest` is empty too.**  So there is no
document cell either, and `ValidOperation` joins the vacuous list. -/
theorem hyperdocumentMaterializer_isEmpty :
    IsEmpty (CellState.Materializer Hyperdocument.cellSchema.{0, 0} Digest) :=
  materializer_isEmpty_of_natBool_embedding (Root := Digest) documentStateOf
    documentStateOf_injective

/-! ## What the fix looks like

The obstruction is the TOTAL function in `LogicalState`, not the schema's
semantics.  A finitely-supported state -- an association list or `Finsupp` over
the field index, read through a default -- is countable whenever the field
index and value types are, and its codec is the underlying finite map's codec.
That is also what the surrounding vocabulary already says these cells are:
`Kernel.SparseAuthenticatedState` calls them sparse namespaces, and
`CredentialAuthorityState`'s own comment calls its cell "one canonical typed
sparse CellState".  The type does not currently say sparse.

The theorem below is the shape that becomes provable once it does: a finite
field index has no obstruction, which is why `Theory.CellStateWitness` works. -/

/-- Finite schemas are unobstructed: their field space is a `Fintype`, hence
countable, so nothing in this file applies to them -- which is why
`Theory.CellStateWitness` works. -/
theorem finite_schema_state_countable {S : Schema.{0, 0, 0, 0}}
    [Fintype S.Field] [DecidableEq S.Field]
    (fieldFinite : ∀ field, Fintype (S.FieldType field))
    (resourceEmpty : IsEmpty S.Resource) :
    Countable (LogicalState S) := by
  have : Fintype ((field : S.Field) → S.FieldType field) :=
    @Pi.instFintype _ _ _ _ fieldFinite
  apply Function.Injective.countable (f := fun state => state.fields)
  intro left right same
  cases left with
  | mk leftFields leftResources =>
      cases right with
      | mk rightFields rightResources =>
          congr 1
          funext resource
          exact resourceEmpty.elim resource

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.MaterializerCardinality.not_injective_natBool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_injective_natBool
/-- info: 'Minidregg.Theory.MaterializerCardinality.lawfulCodec_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms lawfulCodec_injective
/-- info: 'Minidregg.Theory.MaterializerCardinality.materializer_isEmpty_of_natBool_embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materializer_isEmpty_of_natBool_embedding
/-- info: 'Minidregg.Theory.MaterializerCardinality.authorityStateOf_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorityStateOf_injective
/-- info: 'Minidregg.Theory.MaterializerCardinality.authorityMaterializer_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authorityMaterializer_isEmpty
/-- info: 'Minidregg.Theory.MaterializerCardinality.documentStateOf_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms documentStateOf_injective
/-- info: 'Minidregg.Theory.MaterializerCardinality.hyperdocumentMaterializer_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hyperdocumentMaterializer_isEmpty
/-- info: 'Minidregg.Theory.MaterializerCardinality.no_authority_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_authority_cell
/-- info: 'Minidregg.Theory.MaterializerCardinality.finite_schema_state_countable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finite_schema_state_countable

end Minidregg.Theory.MaterializerCardinality
