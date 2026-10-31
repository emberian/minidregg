/-
# `Kernel/EffectsRevival/ActivityProofs.lean` — the two refusal levels, PROVED of today's kernel

`Kernel/EffectsRevival/ActivityStatements.lean` (audited, pass 28): today's `commitYield` keeps the
two levels (`twoLevelsSatisfiable`), an effect-level refusal exists (`twoLevelsPremise`: a
transfer to the activity's own purse, refused `reserved`), and the collapsed judgment does not
keep them (`twoLevelsTeeth`).
-/
module

public import Kernel.EffectsRevival.ActivityStatements
public import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Effects.Revival

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Theory.CanonicalResourceKernel (AccountId Book)

set_option autoImplicit false

theorem twoLevelsSatisfiable : TwoLevelsSatisfiable where
  verdict i reason refused := by
    obtain ⟨patience, narrow, effects, recipient, amount, written, source, wrote, decided⟩ := refused
    unfold YieldInput.reference commitYield
    rw [if_neg patience, if_neg narrow, wrote]
    simp only [source, effects, Bool.not_true, Bool.false_eq_true, if_false]
    simp only [YieldInput.performedAwait] at decided ⊢
    rw [decided]
  ok _ _ found := found
  turn _ _ found := found

/-! ## An effect-level refusal: a transfer to the activity's own purse. -/

/-- A deployment's activity parameters (patience up to 16). -/
def sampleConfig : Config where
  deployment := ⟨⟨1⟩, 2, 3, 4⟩
  asset := 0
  collector := 0
  limits := ⟨100000, 100000⟩
  planBudget := ⟨10000, 100000, 1048576⟩
  maxTicks := 200000
  maxExtractTicks := 1600000
  maxPatience := 16
  typeFuel := 16384
  maxArtifactBytes := 4194304
  tariff := ⟨Minidregg.Kernel.ObjectiveTariff.tariffVersion, 10, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩
  abandonGrace := 16
  storageRate := 1

/-- An empty store, every root the zero digest. -/
def sampleSnapshot : ObjectiveActivity.Snapshot (fun _ => ⟨0⟩) where
  model := ⟨fun _ => ⟨0⟩, fun _ => false, fun _ => 0, [], []⟩
  canonicalBytes := fun _ => []
  coherent := fun _ => rfl

def sampleRecord : Record :=
  ⟨⟨0⟩, ⟨0⟩, ⟨0⟩, [], 0, [], ⟨0⟩,
    ⟨⟨0⟩, 0, ObjectiveTariff.zeroCapacity, ObjectiveTariff.zeroCapacity, 0, 0⟩, 0, .faulted ""⟩

/-- The activity's purse. -/
def samplePurse : AccountId := 1001

/-- A yield of present state `{}` (kept) asking for a transfer of 1 to its own purse. -/
def sampleInput : YieldInput where
  rootBytes := fun _ => ⟨0⟩
  config := sampleConfig
  snapshot := sampleSnapshot
  height := 0
  transaction := ⟨0⟩
  cell := ⟨0⟩
  object := ⟨0⟩
  generation := 0
  checkpoint := ⟨0⟩
  current := some ⟨0, .record []⟩
  viewed := true
  plan := ⟨.record [], .performed (.transfer samplePurse 1), 1⟩
  funds := ⟨true, samplePurse, fun _ => Book.empty, sampleRecord⟩
  reserve := fun _ => 0

theorem sample_refused : sampleInput.TransferRefused .reserved := by
  refine ⟨by decide, by decide, rfl, samplePurse, 1, none, rfl, ?_, ?_⟩
  · simp [sampleInput, stateWrite, decodeWrite, applyWrite, bind, Except.bind, pure, Except.pure]
  · simp [sampleInput, transferVerdict]

theorem twoLevelsPremise : TwoLevelsPremise := ⟨sampleInput, .reserved, sample_refused⟩

theorem twoLevelsTeeth : TwoLevelsTeeth := by
  intro two
  have collapsed := two.verdict sampleInput .reserved sample_refused
  have reference := twoLevelsSatisfiable.verdict sampleInput .reserved sample_refused
  simp [collapsedJudgment, reference, YieldInput.performedAwait] at collapsed

#assert_axioms twoLevelsSatisfiable
#assert_axioms twoLevelsPremise
#assert_axioms twoLevelsTeeth

end Minidregg.Effects.Revival
