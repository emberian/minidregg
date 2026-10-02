/- Enrollment/resume authentication of a retained canonical roster preimage and
its actual separate device catalog. This is semantic image verification, never
query authority. Catalog bytes/rows may be exported only through separately
admitted signed observation of that catalog. No guessed registry lookup exists:
its identifier is committed inside every roster entry. -/
import Kernel.ResourceObservationAdmission
import Compiler.ObjectAudienceRoster
namespace Minidregg.Kernel.AudienceRosterBinding
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false
abbrev State := Minidregg.Theory.ObjectAudience.State
abbrev Entry := Minidregg.Theory.ObjectAudienceRoster.Entry
abbrev Roster := Minidregg.Theory.ObjectAudienceRoster.Roster
abbrev Deployment := ResourceObservationAdmission.Deployment
abbrev Durable := ResourceObservationAdmission.Durable
abbrev Context := ResourceObservationAdmission.Context
variable {deployment : Deployment} {durable : Durable}
/-- The initial catalog profile uses canonical atom zero in a content resource.
The exact full entry list includes subject/capability/device generation/key
commitments. It is an audience-scoped catalog; an unrelated global JSON roster
cannot be substituted. Tombstoned or noncanonical images fail closed. -/
def catalogPayload (context : Context deployment durable) (source : Nat) : Option (Digest × List UInt8) := do
  let .present packed := context.directory.directory.slots source | none
  if !decide (CanonicalCellRegistry.CellLaw deployment source packed) then none else
   match packed with
   | ⟨.content, materialized⟩ =>
     let atom : Hyperdocument.AtomId := ⟨⟨0⟩⟩
     let record ← Hyperdocument.lookup materialized.logical .atoms atom
     if record.tombstonedAt.isNone then some (materialized.root, record.payload) else none
   | _ => none

structure Checked (context : Context deployment durable) (state : State) (roster : Roster) where
  private mk ::
  bound : ObjectAudienceRoster.Bound state roster roster.entries
  source : Nat
  separate : source ≠ state.object
  sourceExact : ∀ entry ∈ roster.entries, entry.deviceSource = source
  payload : Digest × List UInt8
  catalogExact : catalogPayload context source = some payload
  entriesExact : payload.2 = (StreamCodec.list ObjectAudienceRoster.entryStream).encode roster.entries
  snapshotExact : state.deviceSnapshot = (durable.snapshot.model.roots ⟨source⟩).value

def Checked.deviceRoot {context : Context deployment durable} {state : State} {roster : Roster}
    (checked : Checked context state roster) : Nat :=
  (durable.snapshot.model.roots ⟨checked.source⟩).value

def Checked.deviceGuard {context : Context deployment durable} {state : State} {roster : Roster}
    (checked : Checked context state roster) : ReadGuard :=
  ⟨⟨checked.source⟩, durable.snapshot.model.roots ⟨checked.source⟩⟩

theorem Checked.deviceGuard_exact {context : Context deployment durable} {state : State} {roster : Roster}
    (checked : Checked context state roster) :
    checked.deviceGuard.expectedRoot = durable.snapshot.model.roots checked.deviceGuard.cellId := rfl

def check (context : Context deployment durable) (state : State) (roster : Roster) :
    Option (Checked context state roster) := do
  if bound : ObjectAudienceRoster.Bound state roster roster.entries then
   let first ← roster.entries.head?
   let source := first.deviceSource
   if separate : source ≠ state.object then
    if sourceExact : ∀ entry ∈ roster.entries, entry.deviceSource = source then
     match catalogExact : catalogPayload context source with
     | none => none
     | some payload =>
      if entriesExact : payload.2 = (StreamCodec.list ObjectAudienceRoster.entryStream).encode roster.entries then
       if snapshotExact : state.deviceSnapshot = (durable.snapshot.model.roots ⟨source⟩).value then
        some ⟨bound, source, separate, sourceExact, payload, catalogExact, entriesExact, snapshotExact⟩
       else none
      else none
    else none
   else none
  else none

/-- Exact canonical preimage and its admitted bindings are retained together. -/
structure CheckedBytes (context : Context deployment durable) (state : State) (bytes : List UInt8) where
  private mk ::
  roster : Roster
  decoded : ObjectAudienceRoster.decode bytes = some roster
  checked : Checked context state roster

def checkBytes (context : Context deployment durable) (state : State) (bytes : List UInt8) :
    Option (CheckedBytes context state bytes) := do
  match decoded : ObjectAudienceRoster.decode bytes with
  | none => none
  | some roster =>
    let checked ← check context state roster
    pure ⟨roster, decoded, checked⟩

theorem CheckedBytes.canonical {context : Context deployment durable} {state : State} {bytes : List UInt8}
    (checked : CheckedBytes context state bytes) : ObjectAudienceRoster.encode checked.roster = bytes :=
  ObjectAudienceRoster.decode_canonical checked.decoded

theorem Checked.deviceRoot_exact {context : Context deployment durable} {state : State} {roster : Roster}
    (checked : Checked context state roster) : state.deviceSnapshot = checked.deviceRoot :=
  checked.snapshotExact
end Minidregg.Kernel.AudienceRosterBinding
