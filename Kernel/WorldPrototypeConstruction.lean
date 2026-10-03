/- Authenticated prototype inputs and exact constructor effects.
This is an adapter for the existing evaluator, not a second evaluator. Ordered
self/super code stays in immutable Nock libraries; restrictive law composition
continues through the ordinary controller. -/
import Kernel.WorldKindProjection
import Kernel.NockProgramCell.Sample
import Theory.Eval
import Theory.AssertAxioms

namespace Minidregg.Kernel.WorldPrototypeConstruction

open Minidregg.Compiler
open Minidregg.Compiler.WorldKindCell
open Minidregg.Theory
open Minidregg.Theory.Store

set_option autoImplicit false

/-- A length-preserving byte list. A terminal zero byte is data. -/
def byteNoun : List UInt8 → Noun
  | [] => .atom 0
  | byte :: rest => .cell (.atom byte.toNat) (byteNoun rest)

theorem byteNoun_injective : Function.Injective byteNoun := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | cons byte rest => simp [byteNoun] at same
  | cons byte rest ih =>
      intro right same
      cases right with
      | nil => simp [byteNoun] at same
      | cons other more =>
          simp only [byteNoun, Noun.cell.injEq, Noun.atom.injEq] at same
          have first : byte = other := UInt8.toNat_inj.mp same.1
          exact congrArg₂ List.cons first (ih same.2)

/-- Improper lists and out-of-range atoms refuse instead of truncating. -/
def bytesOfNoun : Noun → Option (List UInt8)
  | .atom 0 => some []
  | .cell (.atom byte) rest =>
      if byte < 256 then (bytesOfNoun rest).map (byte.toUInt8 :: ·) else none
  | _ => none

def bytesValue (bytes : List UInt8) : Int :=
  Int.ofNat (NockProgramCell.jamAtom (byteNoun bytes))

def definitionNoun (definition : Definition) : Noun :=
  byteNoun (definitionStream.encode definition)

def definitionValue (definition : Definition) : Int :=
  bytesValue (definitionStream.encode definition)

/-- Only an explicitly authorized full-definition observer exposes this slot.
The ordinary kind law projection remains the existing structural metadata. -/
def observeProject (store : Store definitionLayout) : List (String × Int) :=
  (WorldKindProjection.definitionProject store store) ++
    (match store definitionAddress with
     | none => []
     | some definition => [("kind/definition/noun", definitionValue definition)])

theorem observeProject_unjoint (store : Store definitionLayout) :
    ∀ pair ∈ observeProject store, pair.1.toList.head? ≠ some 'j' := by
  intro pair member
  rcases List.mem_append.mp member with ordinary | whole
  · exact WorldKindProjection.definitionProject_unjoint _ _ pair ordinary
  · cases present : store definitionAddress with
    | none => simp [present] at whole
    | some definition =>
        simp only [present, List.mem_cons, List.not_mem_nil, or_false] at whole
        subst pair
        change ("kind/definition/noun" : String).toList.head? ≠ some 'j'
        decide

/-- Coordinate zero denotes the complete canonical definition result. This
never bypasses prepareDefinition or target mutation authority. -/
def constructorWrite (target : Nat) (definition : Definition) : Eval.FieldWrite :=
  ⟨target, 0, definitionValue definition⟩

theorem definition_sample_decodes (definition : Definition) :
    NockProgramCell.encodeValue .noun (definitionValue definition) =
      some (definitionNoun definition) := by
  exact NockProgramCell.ofJamAtom_jamAtom _

theorem definitionNoun_injective : Function.Injective definitionNoun := by
  intro left right same
  have encoded := byteNoun_injective same
  have decoded := congrArg definitionStream.toLawful.decode encoded
  change definitionStream.toLawful.decode (definitionStream.toLawful.encode left) =
    definitionStream.toLawful.decode (definitionStream.toLawful.encode right) at decoded
  rw [definitionStream.toLawful.decode_encode, definitionStream.toLawful.decode_encode] at decoded
  exact Option.some.inj decoded

#assert_axioms byteNoun_injective
#assert_axioms definition_sample_decodes
#assert_axioms definitionNoun_injective
#assert_axioms observeProject_unjoint

end Minidregg.Kernel.WorldPrototypeConstruction
