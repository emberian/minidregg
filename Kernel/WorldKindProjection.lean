/- Source-owned policy/authority views of descriptor-interpreted stores. -/
import Compiler.WorldKindCell
import Compiler.ResourceAuthorityProjection
import Theory.StoreFootprint

namespace Minidregg.Kernel.WorldKindProjection

open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.WorldKindDescriptor
open Minidregg.Compiler.WorldKindCell

set_option autoImplicit false

def amount : (codec : ScalarCodec) → codec.Value → Int
  | .natural, value => Int.ofNat value
  | .integer, value => value
  | .bytes, _ => 0

def fieldOf (descriptor : Descriptor) (address : Address (layout descriptor)) : CellField :=
  .slot (descriptor.fields.get address.1).id

def amountOf (descriptor : Descriptor) (address : Address (layout descriptor))
    (value : (layout descriptor).Value address.1) : Int :=
  amount (descriptor.fields.get address.1).codec value

def innerFootprint (descriptor : Descriptor) (before after : Store (layout descriptor)) : Footprint :=
  Minidregg.Theory.StoreFootprint.footprint (fieldOf descriptor) (amountOf descriptor) before after

theorem inner_touched_exact (descriptor : Descriptor)
    (before after : Store (layout descriptor)) (field : CellField) :
    field ∈ (innerFootprint descriptor before after).touched ↔
      ∃ address, before address ≠ after address ∧ fieldOf descriptor address = field :=
  Minidregg.Theory.StoreFootprint.footprint_touched_exact _ _ _ _ _

/-- A changed descriptor is not a successful empty footprint. Callers must
refuse absence; no capability check may interpret it as an authority incidence. -/
def footprint (before after : Store instanceLayout) : Option Footprint := do
  let old ← instanceAt before
  let next ← instanceAt after
  if same : next.descriptor = old.descriptor then
    some (innerFootprint old.descriptor old.store (same ▸ next.store))
  else none

/-- Successful decoding uses the exact old descriptor's typed address space;
there is no outer-blob permission standing in for these semantic fields. -/
theorem footprint_exact {before after : Store instanceLayout}
    {old next : WorldKindInstance.Instance}
    (oldExact : instanceAt before = some old) (nextExact : instanceAt after = some next)
    (same : next.descriptor = old.descriptor) :
    footprint before after =
      some (innerFootprint old.descriptor old.store (same ▸ next.store)) := by
  simp [footprint, oldExact, nextExact, same]

def scalarSlots (stem : String) : (codec : ScalarCodec) → codec.Value → List (String × Int)
  | .natural, value => [(stem, Int.ofNat value)]
  | .integer, value => [(stem, value)]
  | .bytes, value => (stem ++ "/length", Int.ofNat value.length) ::
      ResourceAuthorityProjection.bytesSlots (stem ++ "/bytes") 0 value

def stateSlots (view : String) (value : WorldKindInstance.Instance) : List (String × Int) :=
  let entries := StoreCodec.entries (wire value.descriptor) value.store
  (value.descriptor.fields.map fun field =>
    (s!"resource/field/{field.id}/count/{view}",
      Int.ofNat (entries.filter fun entry =>
        (value.descriptor.fields.get entry.1.1).id == field.id).length)) ++
  entries.flatMap fun entry =>
    let field := value.descriptor.fields.get entry.1.1
    scalarSlots s!"resource/field/{field.id}/{(entry.1.2 : Nat)}/{view}" field.codec entry.2

def changes (subject : SubjectId) (descriptor : Descriptor)
    (before after : Store (layout descriptor)) : List (String × Int) :=
  let addresses := Minidregg.Theory.StoreFootprint.changed before after
  let footprint := innerFootprint descriptor before after
  [("changed/count", Int.ofNat addresses.card),
   ("changed/subject-keys-only", if ∀ address ∈ addresses, address.2 = subject.value then 1 else 0)] ++
  descriptor.fields.flatMap fun field =>
    [(s!"resource/field/{field.id}/delta", footprint.delta (.slot field.id)),
     (s!"resource/field/{field.id}/changed", if .slot field.id ∈ footprint.touched then 1 else 0)]

/-- Definitions and meanings are source data, not caller-authored policy slots.
Old and new entry views preserve absence; no absent field is silently zeroed. -/
def rawProject (subject : SubjectId) (before after : Store instanceLayout) : List (String × Int) :=
  match instanceAt before, instanceAt after with
  | some old, some next =>
      if same : next.descriptor = old.descriptor then
        [("target/kind", Int.ofNat old.descriptor.kind),
         ("target/layout-revision", Int.ofNat old.descriptor.revision)] ++
          ResourceAuthorityProjection.bytesSlots "target/layout-digest/bytes" 0
            (Tower256ConcreteBackend.digestStream.encode old.descriptor.identity) ++
          stateSlots "before" old ++ stateSlots "after" next ++
          changes subject old.descriptor old.store (same ▸ next.store)
      else []
  | _, _ => []

/-- A structural local namespace keeps member field labels from becoming
cross-participant `joint/` keys. The labels themselves are displayed separately. -/
def project (subject : SubjectId) (before after : Store instanceLayout) : List (String × Int) :=
  ("world/request/birth", 0) ::
    (rawProject subject before after).map fun pair => ("world/" ++ pair.1, pair.2)

theorem project_unjoint (subject : SubjectId) (before after : Store instanceLayout) :
    ∀ pair ∈ project subject before after, pair.1.toList.head? ≠ some 'j' := by
  intro pair member
  rcases List.mem_cons.mp member with rfl | member
  · decide
  · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    simp [String.toList_append]

/-- A birth's actual effect starts from an empty inner store under its signed
immutable descriptor, not from an invalid absent outer carrier. This source-owned
marker distinguishes allocation from ordinary mutation without rewriting the
request's actual verb. Export laws still judge every birth. -/
def birthProject (subject : SubjectId) (initial : Store instanceLayout) : List (String × Int) :=
  match initial descriptorAddress, instanceAt initial with
  | some binding, some value =>
      let empty := instanceOf binding.kindRoot { value with store := 0 }
      ("world/request/birth", 1) ::
        (rawProject subject empty initial).map fun pair => ("world/" ++ pair.1, pair.2)
  | _, _ => []

def rawDefinitionProject (before after : Store definitionLayout) : List (String × Int) :=
  match before definitionAddress, after definitionAddress with
  | some old, some next =>
      [("target/kind", Int.ofNat old.descriptor.kind),
       ("kind/revision/before", Int.ofNat old.descriptor.revision),
       ("kind/revision/after", Int.ofNat next.descriptor.revision),
       ("kind/fields/before", Int.ofNat old.descriptor.fields.length),
       ("kind/fields/after", Int.ofNat next.descriptor.fields.length)]
  | _, _ => []

def definitionProject (before after : Store definitionLayout) : List (String × Int) :=
  (rawDefinitionProject before after).map fun pair => ("kind/" ++ pair.1, pair.2)

theorem definitionProject_unjoint (before after : Store definitionLayout) :
    ∀ pair ∈ definitionProject before after, pair.1.toList.head? ≠ some 'j' := by
  intro pair member
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
  simp [String.toList_append]

end Minidregg.Kernel.WorldKindProjection
