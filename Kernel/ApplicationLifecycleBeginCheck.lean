/-
Focused, named executable instances of the general lifecycle BEGIN laws. The
native receiver is deliberately not exercised here: no physical launch or
completion authority is represented by these values.
-/
import Kernel.ApplicationLifecycleBeginReceiver

namespace Minidregg.Kernel.ApplicationLifecycleBeginCheck

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ApplicationLifecycleBegin
open Minidregg.Kernel.ApplicationLifecycleBeginIngress

private def initial : Source where
  kind := .install
  app := 101
  packageManifest := 102
  snapshotManifest := 103
  operationId := 104
  subject := ⟨7⟩
  managementSubject := ⟨7⟩
  capability := ⟨11⟩
  packageObserveCapability := ⟨12⟩
  before := ⟨0, 0, 0, 0⟩
  appRoot := ⟨0⟩
  packageRoot := ⟨0⟩
  packageDigest := ⟨0⟩
  imageIdentity := [1]
  processGeneration := 1
  processIdentity := [2]

theorem initial_valid : initial.valid = true := by decide

theorem initial_source_roundtrip :
    sourceCodec.decode initial.canonicalBytes = some initial :=
  source_decode_encode initial

private def changedImage : Source := { initial with imageIdentity := [3] }

theorem changed_image_distinct : initial ≠ changedImage := by decide

theorem changed_image_same_operation_key (domain semantics : Digest) :
    key domain semantics initial = key domain semantics changedImage := rfl

theorem changed_image_same_nullifier (domain semantics : Digest) :
    stableNullifier domain semantics initial =
      stableNullifier domain semantics changedImage :=
  stableNullifier_same_key domain semantics initial changedImage
    (changed_image_same_operation_key domain semantics)

end Minidregg.Kernel.ApplicationLifecycleBeginCheck
