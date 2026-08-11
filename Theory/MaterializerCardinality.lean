/-
# Theory.MaterializerCardinality -- why canonical cells must be sparse

The former `CellState.LogicalState.fields` was a total dependent function.  At
an infinite field index it could contain an injective copy of `Nat → Bool`, but
every `LawfulCodec` injects into the countable type `List UInt8`.  Consequently
the deployed authority, Hyperdocument, event-log, and declared-effect schemas
had no materializer at all.

`CellState.LogicalState.fields` is now a canonical dependent finite map.  This
module keeps the counting argument against the *deleted total carrier* as a
regression tooth, and characterizes the repaired materializer honestly: it is
inhabited exactly when the complete sparse logical-state type is countable.
-/
import Theory.CellState
import Theory.DeclaredTurn

namespace Minidregg.Theory.MaterializerCardinality

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

universe u v w x y

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

/-- The old field shape, retained only so the vacuity cannot silently return. -/
structure TotalLogicalState (S : Schema.{u, v, w, x}) where
  fields : (field : S.Field) → S.FieldType field
  resources : (resource : S.Resource) → ResourceCell S resource

/-- The materializer interface over that old carrier. -/
structure TotalMaterializer (S : Schema.{u, v, w, x}) (Root : Type y) where
  codec : LawfulCodec (TotalLogicalState S)
  rootBytes : List UInt8 → Root

/-- Any total carrier containing `Nat → Bool` has no lawful materializer. -/
theorem totalMaterializer_isEmpty_of_natBool_embedding
    {S : Schema.{0, 0, 0, 0}} {Root : Type}
    (embed : (Nat → Bool) → TotalLogicalState S)
    (embed_injective : Function.Injective embed) :
    IsEmpty (TotalMaterializer S Root) :=
  ⟨fun materializer =>
    not_injective_natBool (fun value => materializer.codec.encode (embed value))
      ((lawfulCodec_injective materializer.codec).comp embed_injective)⟩

open Minidregg.Theory.DeclaredTurn in
/-- The former declared-effect carrier really did contain every Boolean stream. -/
def totalEffectStateOf (marked : Nat → Bool) :
    TotalLogicalState effectSchema where
  fields := fun key =>
    match key with
    | .programCode program =>
        show Int from if marked program.value then 1 else 0
    | _ => show Int from 0
  resources := fun resource => nomatch resource

open Minidregg.Theory.DeclaredTurn in
theorem totalEffectStateOf_injective : Function.Injective totalEffectStateOf := by
  intro left right same
  funext index
  have fields := congrArg TotalLogicalState.fields same
  have point := congrFun fields (.programCode ⟨index⟩)
  simp only [totalEffectStateOf] at point
  by_cases hleft : left index = true
  · by_cases hright : right index = true
    · rw [hleft, hright]
    · simp [hleft, hright] at point
      exact absurd point (show (1 : Int) ≠ 0 by decide)
  · by_cases hright : right index = true
    · simp [hleft, hright] at point
      exact absurd point (show (0 : Int) ≠ 1 by decide)
    · simp only [Bool.not_eq_true] at hleft hright
      rw [hleft, hright]

open Minidregg.Theory.DeclaredTurn in
/-- Load-bearing negative tooth: restoring the old total effect carrier makes
the kernel materializer empty again. -/
theorem totalEffectMaterializer_isEmpty :
    IsEmpty (TotalMaterializer effectSchema.{0, 0} Digest) :=
  totalMaterializer_isEmpty_of_natBool_embedding totalEffectStateOf
    totalEffectStateOf_injective

/-! ## The repaired sparse carrier -/

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

/-- A repaired materializer exists exactly when its complete sparse logical
state is countable (assuming the root carrier and state are inhabited). -/
theorem materializer_nonempty_iff_countable {S : Schema.{0, 0, 0, 0}}
    {Root : Type} [Nonempty (LogicalState S)] [Nonempty Root] :
    Nonempty (Materializer S Root) ↔ Countable (LogicalState S) := by
  constructor
  · intro ⟨materializer⟩
    exact (lawfulCodec_injective materializer.codec).countable
  · intro countable
    obtain ⟨codec⟩ := nonempty_lawfulCodec_of_countable (alpha := LogicalState S)
    exact ⟨{ codec := codec, rootBytes := fun _ => Classical.arbitrary Root }⟩

/-- With countable typed fields and no resource lane, the repaired complete
logical state is countable even when the field index is infinite. -/
theorem sparse_schema_state_countable {S : Schema.{0, 0, 0, 0}}
    [Countable S.Field] [∀ field, Countable (S.FieldType field)]
    (resourceEmpty : IsEmpty S.Resource) : Countable (LogicalState S) := by
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
/-- info: 'Minidregg.Theory.MaterializerCardinality.totalEffectMaterializer_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms totalEffectMaterializer_isEmpty
/-- info: 'Minidregg.Theory.MaterializerCardinality.nonempty_lawfulCodec_of_countable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nonempty_lawfulCodec_of_countable
/-- info: 'Minidregg.Theory.MaterializerCardinality.materializer_nonempty_iff_countable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materializer_nonempty_iff_countable
/-- info: 'Minidregg.Theory.MaterializerCardinality.sparse_schema_state_countable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sparse_schema_state_countable

end Minidregg.Theory.MaterializerCardinality
