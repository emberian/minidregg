/-
# Kernel.EventLogMaterializerLimit -- the third schema, same obstruction

`Theory.MaterializerCardinality` proves `CredentialAuthorityState.Materializer`
and `Hyperdocument.Materializer Digest` are empty, because a materializer's
codec must inject a total function over an infinite field index into
`List UInt8`.

`HyperdocumentEventLog.cellSchema` is the third cell the Hyperdocument
publication path needs, and it has the same shape: `Sparse.Address` is
infinite, its value type is `Option VersionEventRecord`, and
`VersionEventRecord` is inhabited.  So the joint publication commit demands
three materializers and none of the three exists.

The proof is three lines, because
`materializer_isEmpty_of_natBool_embedding` already carries the argument.  That
is the point of having stated it generically: a suspected schema costs an
embedding and an injectivity proof, not a rederivation.
-/
import Kernel.HyperdocumentEventLog
import Theory.MaterializerCardinality

namespace Minidregg.Kernel.EventLogMaterializerLimit

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.MaterializerCardinality
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- A version-event record built from zeros, used only to make `Option`
two-valued. -/
def sampleEvent : Hyperdocument.VersionEventRecord where
  historyDomain := ⟨0⟩
  document := ⟨⟨0⟩⟩
  schema := { schemaId := ⟨0⟩, version := 0 }
  semanticVersion := 0
  operation := ⟨⟨0⟩⟩
  parents := []
  preStateRoot := ⟨0⟩
  postStateRoot := ⟨0⟩
  requestId := ⟨0⟩
  effectId := ⟨0⟩
  author := { subject := ⟨0⟩, capabilityKind := .object, capabilityId := ⟨0⟩ }

/-- Mark event `index` present or absent according to `marked index`. -/
def eventStateOf (marked : Nat -> Bool) :
    LogicalState HyperdocumentEventLog.cellSchema where
  fields := fun address =>
    if marked address.2.digest.value then some sampleEvent else none
  resources := fun resource => resource.elim

theorem eventStateOf_injective : Function.Injective eventStateOf := by
  intro left right same
  funext index
  have fields := congrArg LogicalState.fields same
  have point := congrFun fields ⟨.events, ⟨⟨index⟩⟩⟩
  simp only [eventStateOf] at point
  by_cases hleft : left index = true
  · by_cases hright : right index = true
    · rw [hleft, hright]
    · simp [hleft, hright] at point
  · by_cases hright : right index = true
    · simp [hleft, hright] at point
    · simp only [Bool.not_eq_true] at hleft hright
      rw [hleft, hright]

/-- **The event-log cell has no materializer either.**  So all three cells the
Hyperdocument publication commit requires are uninhabitable, and the commit
itself is vacuous at that instantiation. -/
theorem eventLogMaterializer_isEmpty :
    IsEmpty (Materializer HyperdocumentEventLog.cellSchema.{0, 0} Digest) :=
  materializer_isEmpty_of_natBool_embedding (Root := Digest) eventStateOf
    eventStateOf_injective

/-- info: 'Minidregg.Kernel.EventLogMaterializerLimit.eventStateOf_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eventStateOf_injective
/-- info: 'Minidregg.Kernel.EventLogMaterializerLimit.eventLogMaterializer_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eventLogMaterializer_isEmpty

end Minidregg.Kernel.EventLogMaterializerLimit
