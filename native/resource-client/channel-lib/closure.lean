/-
`closure.lean` — the import closure of the given modules, as olean paths, dependencies first.
`lake env lean --run native/resource-client/channel-lib/closure.lean Kernel.DomainEpochExport`
`build.sh` maps each package olean to its compiled object (`.c.o.export`) and links them.
-/
import Lean

open Lean

/-- Each module's imports, read from its olean. The olean stays mapped (read-only) until exit: freeing
the compacted region while the interpreter still holds its names crashes, and this runs once. -/
def importsOf (olean : System.FilePath) : IO (Array String) := do
  let (md, _) ← readModuleData olean
  return md.imports.map fun i => i.module.toString

partial def visit (m : String) : StateT (Std.HashSet String × Array System.FilePath) IO Unit := do
  if (← get).1.contains m then return
  modify fun (s, a) => (s.insert m, a)
  let olean ← findOLean m.toName
  for i in ← importsOf olean do visit i
  modify fun (s, a) => (s, a.push olean)

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (_, (_, paths)) ← (args.forM fun a => visit a).run ({}, #[])
  for p in paths do IO.println p
  return 0
