/-
# Theory.MaterializerCardinality -- why canonical cells must be sparse

The former cell carrier (`CellState.LogicalState.fields`, and the declared
effects' `EffectDeclaration.Store := StateKey → Int`) was a total dependent
function.  At an infinite key index it could contain an injective copy of
`Nat → Bool`, but every `LawfulCodec` injects into the countable type
`List UInt8`.  Consequently the deployed authority, Hyperdocument, event-log,
and declared-effect schemas had no materializer at all.

The one carrier is now `Store.Store L`, a canonical dependent finite map.  This
module keeps the counting argument against the *deleted total carrier* as a
regression tooth, and characterizes the materializer honestly: it is inhabited
exactly when the store type is countable, which it is whenever namespaces, keys
and values are.
-/
import Mathlib.Data.DFinsupp.Encodable
import Theory.CellState
import Theory.EffectDeclaration

namespace Minidregg.Theory.MaterializerCardinality

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

universe u v w y

instance : Countable UInt8 :=
  Function.Injective.countable (f := UInt8.toNat)
    (by intro left right same; exact UInt8.toNat.inj same)

/-- No countable type admits an injection from `Nat → Bool`. -/
theorem not_injective_natBool {beta : Type} [Countable beta]
    (encode : (Nat → Bool) → beta) : ¬Function.Injective encode := by
  intro injective
  have countable : Countable (Nat → Bool) := injective.countable
  obtain ⟨enumerate, surjective⟩ := exists_surjective_nat (Nat → Bool)
  let diagonal : Nat → Bool := fun index => !(enumerate index index)
  obtain ⟨index, hit⟩ := surjective diagonal
  have point := congrFun hit index
  simp [diagonal] at point

/-- Round-trip decoding makes every lawful encoding injective. -/
theorem lawfulCodec_injective {alpha : Type u} (codec : LawfulCodec alpha) :
    Function.Injective codec.encode := by
  intro left right same
  have decoded : codec.decode (codec.encode left) =
      codec.decode (codec.encode right) := by rw [same]
  rw [codec.decode_encode, codec.decode_encode] at decoded
  exact Option.some.inj decoded

/-! ## Regression model: the deleted total-function carrier -/

/-- The old carrier shape: one value at every address, retained only so the
vacuity cannot silently return. -/
def TotalStore (L : Layout.{u, v, w}) : Type (max u v w) :=
  (address : Address L) → L.Value address.1

/-- The materializer interface over that old carrier. -/
structure TotalMaterializer (L : Layout.{u, v, w}) (Root : Type y) where
  codec : LawfulCodec (TotalStore L)
  rootBytes : List UInt8 → Root

/-- Any total carrier containing `Nat → Bool` has no lawful materializer. -/
theorem totalMaterializer_isEmpty_of_natBool_embedding
    {L : Layout.{0, 0, 0}} {Root : Type}
    (embed : (Nat → Bool) → TotalStore L)
    (embed_injective : Function.Injective embed) :
    IsEmpty (TotalMaterializer L Root) :=
  ⟨fun materializer =>
    not_injective_natBool (fun value => materializer.codec.encode (embed value))
      ((lawfulCodec_injective materializer.codec).comp embed_injective)⟩

open Minidregg.Theory.EffectDeclaration in
/-- The former declared-effect carrier really did contain every Boolean stream. -/
def totalEffectStateOf (marked : Nat → Bool) : TotalStore effectLayout :=
  fun address =>
    match address.2 with
    | .programCode program =>
        show Int from if marked program.value then 1 else 0
    | _ => show Int from 0

open Minidregg.Theory.EffectDeclaration in
theorem totalEffectStateOf_injective : Function.Injective totalEffectStateOf := by
  intro left right same
  funext index
  have point := congrFun same (StateKey.programCode ⟨index⟩).address
  simp only [totalEffectStateOf, StateKey.address] at point
  by_cases hleft : left index = true
  · by_cases hright : right index = true
    · rw [hleft, hright]
    · simp [hleft, hright] at point
  · by_cases hright : right index = true
    · simp [hleft, hright] at point
    · simp only [Bool.not_eq_true] at hleft hright
      rw [hleft, hright]

open Minidregg.Theory.EffectDeclaration in
/-- Load-bearing negative tooth: restoring the old total effect carrier makes
the kernel materializer empty again. -/
theorem totalEffectMaterializer_isEmpty :
    IsEmpty (TotalMaterializer effectLayout Digest) :=
  totalMaterializer_isEmpty_of_natBool_embedding totalEffectStateOf
    totalEffectStateOf_injective

/-! ## The sparse carrier -/

/-- Any nonempty countable type has a lawful codec.  The unary wire format is
an existence witness, not a deployment recommendation. -/
theorem nonempty_lawfulCodec_of_countable {alpha : Type} [Countable alpha]
    [Nonempty alpha] : Nonempty (LawfulCodec alpha) := by
  obtain ⟨encodable⟩ := nonempty_encodable alpha
  refine ⟨{ encode := fun value => List.replicate (encodable.encode value) 0
            decode := fun bytes => encodable.decode bytes.length
            decode_encode := ?_ }⟩
  intro value
  simp [encodable.encodek]

/-- A materializer exists exactly when its store type is countable (assuming
the root carrier is inhabited). -/
theorem materializer_nonempty_iff_countable {L : Layout.{0, 0, 0}}
    {Root : Type} [Nonempty Root] :
    Nonempty (Materializer L Root) ↔ Countable (Store L) := by
  constructor
  · intro ⟨materializer⟩
    exact (lawfulCodec_injective materializer.codec).countable
  · intro countable
    obtain ⟨codec⟩ := nonempty_lawfulCodec_of_countable (alpha := Store L)
    exact ⟨{ codec := codec, rootBytes := fun _ => Classical.arbitrary Root }⟩

/-- With countable namespaces, keys and values, the store is countable even
when the key index is infinite. -/
theorem sparse_store_countable {L : Layout.{0, 0, 0}}
    [Countable L.Namespace] [∀ space, Countable (L.Key space)]
    [∀ space, Countable (L.Value space)] : Countable (Store L) :=
  inferInstance

open Minidregg.Theory.EffectDeclaration in
/-- A first-order code for the state-key constructors: `StateKey` is
countable, and Lean does not derive that. -/
def stateKeyCode : StateKey → Nat × Nat × Nat
  | .objectField object field => (0, object.value, field.value)
  | .accountBalance account resource => (1, account.value, resource.value)
  | .programCode program => (2, program.value, 0)
  | .fieldDeclared object field => (3, object.value, field.value)
  | .fieldsOpen object => (4, object.value, 0)

open Minidregg.Theory.EffectDeclaration in
theorem stateKeyCode_injective : Function.Injective stateKeyCode := by
  rintro (⟨⟨_⟩, ⟨_⟩⟩ | ⟨⟨_⟩, ⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩, ⟨_⟩⟩ | ⟨⟨_⟩⟩)
    (⟨⟨_⟩, ⟨_⟩⟩ | ⟨⟨_⟩, ⟨_⟩⟩ | ⟨⟨_⟩⟩ | ⟨⟨_⟩, ⟨_⟩⟩ | ⟨⟨_⟩⟩) same <;>
    simp_all [stateKeyCode]

open Minidregg.Theory.EffectDeclaration in
instance stateKey_countable : Countable StateKey :=
  Function.Injective.countable stateKeyCode_injective

open Minidregg.Theory.EffectDeclaration in
/-- The positive pole: the declared-effect layout, whose total carrier had no
materializer, has one over the sparse store. -/
theorem effectMaterializer_nonempty : Nonempty (Materializer effectLayout Digest) := by
  haveI : Nonempty Digest := ⟨⟨0⟩⟩
  exact materializer_nonempty_iff_countable.mpr sparse_store_countable

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.MaterializerCardinality.not_injective_natBool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_injective_natBool
/-- info: 'Minidregg.Theory.MaterializerCardinality.lawfulCodec_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms lawfulCodec_injective
/-- info: 'Minidregg.Theory.MaterializerCardinality.totalEffectMaterializer_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms totalEffectMaterializer_isEmpty
/-- info: 'Minidregg.Theory.MaterializerCardinality.nonempty_lawfulCodec_of_countable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_lawfulCodec_of_countable
/-- info: 'Minidregg.Theory.MaterializerCardinality.materializer_nonempty_iff_countable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materializer_nonempty_iff_countable
/-- info: 'Minidregg.Theory.MaterializerCardinality.effectMaterializer_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms effectMaterializer_nonempty
/-- info: 'Minidregg.Theory.MaterializerCardinality.stateKeyCode_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms stateKeyCode_injective

end Minidregg.Theory.MaterializerCardinality
