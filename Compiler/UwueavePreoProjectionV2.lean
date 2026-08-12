/-
# Compiler.UwueavePreoProjectionV2 -- checked Preoscript data for Rust

This is the deliberately narrow dependency edge from minidregg into
Preoscript.  The imported export crosses Uwueave's private
`ValidatedProjectionV2` boundary.  We retain its exact first-order identities,
render its deterministic Rust representation, and write that representation
as a committed generated source file.

The resulting Rust value is coordination *data*.  Reading it does not produce
a Minidregg authorization, verified receipt, semantic verdict, scheduling
permit, or native-work continuation.  Those remain owned by the existing Lean
controllers and kernel admission paths.
-/
import Uwueave.Preo.ProjectionV2

namespace Minidregg.Compiler.UwueavePreoProjectionV2

set_option autoImplicit false

abbrev Projection := Uwueave.Preo.ProjectionV2.Projection
abbrev ValidatedProjection := Uwueave.Preo.ProjectionV2.ValidatedProjectionV2

/-- The only consumed projection is Uwueave's proof-originated, fully nonempty
export example from the content-pinned dependency. -/
def projection : Projection :=
  Uwueave.Preo.ProjectionV2.Examples.fullExport

def validation : Uwueave.Preo.ProjectionV2.ValidationResult ValidatedProjection :=
  Uwueave.Preo.ProjectionV2.validate
    Uwueave.Preo.ProjectionV2.Examples.config projection

/-- This private-boundary value is extracted only from Uwueave's successful
validator result.  The impossible branch is discharged by the upstream
acceptance theorem; minidregg does not reconstruct the value from bytes. -/
def validated : ValidatedProjection :=
  match h : validation with
  | .ok value => value
  | .error _ => False.elim (by
      have accepted := Uwueave.Preo.ProjectionV2.Examples.full_export_validates
      change validation.isOk = true at accepted
      rw [h] at accepted
      cases accepted)

/-- Deterministic data-only Rust source from that validated value. -/
def rustSource : String :=
  Uwueave.Preo.ProjectionV2.renderRustSource validated

def targetPath : System.FilePath :=
  "prover/generated/uwueave_preo_projection_v2.rs"

/-- Materialize only the deterministic renderer output.  Defining this writer
does not grant the output any semantic authority. -/
def writeGenerated : IO Unit := do
  if let some directory := targetPath.parent then
    IO.FS.createDirAll directory
  IO.FS.writeFile targetPath rustSource

/- The checked export's actual cross-system contract: one declaration, stable
row identifiers, one session/plan pair, and one exact-plan budget. -/
theorem exact_manifest_ids_and_lengths :
    projection.encoding.declaration.id = 400
      ∧ projection.encoding.fields.map (fun row => row.id) = [402]
      ∧ projection.encoding.invariants.map (fun row => row.id) = [403]
      ∧ projection.encoding.futures.map (fun row => row.id) = [404]
      ∧ projection.encoding.sessions.map (fun row => row.id) = [407]
      ∧ projection.encoding.plans.map (fun row => row.id) = [408]
      ∧ projection.encoding.budgets.map (fun row => row.id) = [411] := by
  decide

theorem exact_session_plan_budget_references :
    projection.encoding.sessions.map (fun row =>
        (row.id, row.declarationId)) = [(407, 400)]
      ∧ projection.encoding.plans.map (fun row =>
        (row.id, row.sessionId)) = [(408, 407)]
      ∧ projection.encoding.budgets.map (fun row =>
        (row.id, row.sessionId, row.planId)) = [(411, 407, 408)] := by
  decide

theorem exact_plan_profiles :
    projection.encoding.plans.map (fun row => row.profile) =
      [[(.peerBarrier, 2), (.arbiterCut, 0), (.networkRound, 0),
        (.userPrompt, 0), (.rollback, 0)]] := by
  rfl

theorem exact_budget_limits_and_realized_profile :
    projection.encoding.budgets.map
        (fun row => (row.limits, row.realizedProfile)) =
      [([(.peerBarrier, 2), (.arbiterCut, 0), (.networkRound, 0),
          (.userPrompt, 0), (.rollback, 0)],
        [(.peerBarrier, 2), (.arbiterCut, 0), (.networkRound, 0),
          (.userPrompt, 0), (.rollback, 0)])] := by
  rfl

/- Regeneration is part of building this module.  The generated file is
checked into the Rust crate so its review and consumer tests do not need a Lean
runtime. -/
#eval writeGenerated

/-- info: 'Minidregg.Compiler.UwueavePreoProjectionV2.exact_manifest_ids_and_lengths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exact_manifest_ids_and_lengths
/-- info: 'Minidregg.Compiler.UwueavePreoProjectionV2.exact_session_plan_budget_references' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exact_session_plan_budget_references
/-- info: 'Minidregg.Compiler.UwueavePreoProjectionV2.exact_plan_profiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exact_plan_profiles
/-- info: 'Minidregg.Compiler.UwueavePreoProjectionV2.exact_budget_limits_and_realized_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exact_budget_limits_and_realized_profile

end Minidregg.Compiler.UwueavePreoProjectionV2
