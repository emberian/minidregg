/-
# Kernel.EventLogMaterializerLimit -- regression tooth for total event logs

The live Hyperdocument event log is a structurally finite `Store` over
`HyperdocumentEventLog.Sparse.layout`.  This module retains the former
cardinality failure against `MaterializerCardinality.TotalStore`: if the cell
regresses to a total function, the event-log materializer becomes empty again.
-/
import Kernel.HyperdocumentEventLog
import Theory.MaterializerCardinality

namespace Minidregg.Kernel.EventLogMaterializerLimit

open Minidregg.Theory
open Minidregg.Theory.MaterializerCardinality
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- A version-event record whose semantic version makes two distinct values. -/
def sampleEvent (semanticVersion : Nat) : Hyperdocument.VersionEventRecord where
  historyDomain := ⟨0⟩
  document := ⟨⟨0⟩⟩
  schema := { schemaId := ⟨0⟩, version := 0 }
  semanticVersion := semanticVersion
  operation := ⟨⟨0⟩⟩
  parents := []
  preStateRoot := ⟨0⟩
  postStateRoot := ⟨0⟩
  requestId := ⟨0⟩
  effectId := ⟨0⟩
  author := { subject := ⟨0⟩, capabilityKind := .object, capabilityId := ⟨0⟩ }

/-- The deleted total carrier can encode every Boolean stream in event values. -/
def totalEventStateOf (marked : Nat → Bool) :
    TotalStore HyperdocumentEventLog.Sparse.layout :=
  fun address =>
    show Hyperdocument.VersionEventRecord from
      if marked address.2.digest.value then sampleEvent 1 else sampleEvent 0

theorem totalEventStateOf_injective : Function.Injective totalEventStateOf := by
  intro left right same
  funext index
  have point := congrFun same ⟨.events, ⟨⟨index⟩⟩⟩
  have version := congrArg Hyperdocument.VersionEventRecord.semanticVersion point
  simp only [totalEventStateOf, sampleEvent] at version
  by_cases hleft : left index = true
  · by_cases hright : right index = true
    · rw [hleft, hright]
    · simp [hleft, hright] at version
  · by_cases hright : right index = true
    · simp [hleft, hright] at version
    · simp only [Bool.not_eq_true] at hleft hright
      rw [hleft, hright]

/-- Restoring a total event-log field function would make materialization
impossible again.  This theorem is about the regression model, not the live
sparse cell. -/
theorem totalEventLogMaterializer_isEmpty :
    IsEmpty (TotalMaterializer HyperdocumentEventLog.Sparse.layout Digest) :=
  totalMaterializer_isEmpty_of_natBool_embedding totalEventStateOf
    totalEventStateOf_injective

/-- info: 'Minidregg.Kernel.EventLogMaterializerLimit.totalEventStateOf_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms totalEventStateOf_injective
/-- info: 'Minidregg.Kernel.EventLogMaterializerLimit.totalEventLogMaterializer_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms totalEventLogMaterializer_isEmpty

end Minidregg.Kernel.EventLogMaterializerLimit
