/-
# scripts/ObjectiveSnapshotMathlib.lean -- the statement and axiom snapshot of the rest of ObjectiveProofs

`lake build ObjectiveProofs` gates the proofs of every module in its import closure; the
Mathlib-free run (scripts/ObjectiveSnapshot.lean) can pin only the `Theory.ObjectiveBend*` ones.
This run pins the others: it covers every module of the closure of `ObjectiveProofs` whose
source is in this repository (`<Module/Path>.lean` exists under the working directory: Kernel,
Compiler, Pred, Selvage, the rest of Theory; never Mathlib, Batteries, Std, Lean, Init), except
the `Theory.ObjectiveBend*` modules the Mathlib-free run already covers (read from that file's
import header, so the two runs partition the closure). Its environment imports `ObjectiveProofs`
and therefore Mathlib: these rows are rendered with Mathlib's delaborators, which is why they
live in their own pair of files, scripts/gates/objective-statements-mathlib.snapshot and
scripts/gates/objective-axioms-mathlib.pin. A Mathlib bump may re-render rows here; that is an
announced `--update`, never the Mathlib-free pair.

Measured before this run existed (W20-GATE-MUTATION, 2026-10-04): an unused `(_vacuous : False)`
premise on `Kernel.ObjectiveBendAdmissionSemantics.admitted_source_semantics` left the whole
`proofs` gate green. The gate now plants exactly that premise every run and requires this
instrument's row for it to change.

Run: `lake env lean scripts/ObjectiveSnapshotMathlib.lean` (from the repository root)
-/
import ObjectiveProofs
import Theory.ObjectiveBendExtensions
import Theory.ObjectiveBendDemandCapacity
import Verify.ObjectiveSnapshot

open Lean

namespace Minidregg.ObjectiveSnapshot.MathlibRun

/-- Self-test switch (scripts/check-objective-proofs.sh flips it in a scratch copy). -/
def includeLocal : Bool := false

/-- The file whose import header says what the Mathlib-free run covers. -/
def theoryRunFile : System.FilePath := "scripts/ObjectiveSnapshot.lean"

/-- Modules this run must cover: the ones the measured defect left unpinned. -/
def mustCover : List Name :=
  [`Kernel.ObjectiveBendAdmissionSemantics, `Kernel.ObjectiveResumeContract,
   `Compiler.ObjectiveBendFrontEndAdequacy]

/-- 258 modules and 18840 declarations measured 2026-10-04; the floors sit under both. -/
def moduleFloor : Nat := 200

def config : MetaM Minidregg.ObjectiveSnapshot.Config := do
  let env ← getEnv
  let mut pre : Array String := #[]
  let header ← Lean.parseImports' (← IO.FS.readFile theoryRunFile) theoryRunFile.toString
  let theoryImports := header.imports.map (·.module) |>.filter (· != `Verify.ObjectiveSnapshot)
  for m in theoryImports do
    unless env.header.moduleNames.contains m do
      pre := pre.push s!"instrument: {m} (imported by {theoryRunFile}) is not imported here; the partition would be guessed"
  if theoryImports.isEmpty then
    pre := pre.push s!"instrument: no imports read from {theoryRunFile}"
  let theoryCovered := (importClosure env theoryImports).toList.filter
    (·.toString.startsWith "Theory.ObjectiveBend")
  let mut covered : NameSet := {}
  for m in (importClosure env #[`ObjectiveProofs]).toList do
    if theoryCovered.contains m then continue
    let file := System.mkFilePath (m.components.map toString) |>.addExtension "lean"
    if ← file.pathExists then covered := covered.insert m
  for m in mustCover do
    unless covered.contains m do pre := pre.push s!"instrument: module {m} not covered"
  if covered.size < moduleFloor then
    pre := pre.push s!"instrument: only {covered.size} modules covered (floor {moduleFloor})"
  IO.eprintln s!"objective-snapshot-mathlib: {covered.size} modules covered, {theoryCovered.length} left to the Mathlib-free run"
  return {
    label := "objective-snapshot-mathlib"
    covers := covered.contains
    includeLocal := includeLocal
    refuseMathlib := false
    scanFloor := 15000
    mustFind :=
      [`Minidregg.Kernel.ObjectiveBendAdmissionSemantics.admitted_source_semantics,
       `Minidregg.Kernel.ObjectiveBendAdmissionSemantics.admitted_front_end]
    preFailures := pre }

end Minidregg.ObjectiveSnapshot.MathlibRun

set_option maxHeartbeats 0 in
run_meta do Minidregg.ObjectiveSnapshot.main (← Minidregg.ObjectiveSnapshot.MathlibRun.config)
